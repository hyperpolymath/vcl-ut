// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! E2E tests for the VCL-total query pipeline.
//!
//! Exercises the full format → lint pipeline for realistic VCL-total queries.
//! Focuses on scenarios not covered by the existing integration tests:
//! - Multi-keyword queries with complex WHERE predicates
//! - Error handling for invalid VCL-total (missing semicolons, wrong case)
//! - Consecutive round-trip consistency
//! - Formatter and linter agreement on canonical output

use vcl_total::fmt::format_vqlut;
use vcl_total::lint::lint_vqlut;

// ============================================================================
// Full VCL type-checking pipeline: parse → format → lint → verify
// ============================================================================

#[test]
fn e2e_full_pipeline_simple_select_clean() {
    // A fully correct VCL-total query should pass the full pipeline cleanly.
    let query = "SELECT id;\n";
    let formatted = format_vqlut(query);
    let issues = lint_vqlut(&formatted);

    assert!(
        formatted.contains("SELECT"),
        "formatted output must retain SELECT keyword"
    );
    let semicolon_issues: Vec<_> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(
        semicolon_issues.is_empty(),
        "clean query with semicolon must pass lint: {:?}",
        semicolon_issues
    );
}

#[test]
fn e2e_full_pipeline_complex_multiclause_query() {
    // A multi-clause query exercises the formatter on every recognised keyword.
    let query = concat!(
        "SELECT id, name, amount\n",
        "FROM transactions\n",
        "WHERE amount > 100\n",
        "GROUP BY currency\n",
        "HAVING count > 5\n",
        "ORDER BY amount\n",
        "LIMIT 50;"
    );
    let formatted = format_vqlut(query);
    let lines: Vec<&str> = formatted.lines().collect();

    // All recognised keyword lines must be indented by exactly two spaces.
    let keywords = ["SELECT", "FROM", "WHERE", "GROUP", "HAVING", "ORDER", "LIMIT"];
    for line in &lines {
        let trimmed = line.trim();
        if keywords.iter().any(|&kw| trimmed.starts_with(kw)) {
            assert!(
                line.starts_with("  "),
                "keyword line must have two-space indent, got: {:?}", line
            );
        }
    }

    // The final line ends with ';' so the linter must not flag a missing semicolon on it.
    let issues = lint_vqlut(&formatted);
    let flagged_lines: Vec<usize> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .map(|i| i.line)
        .collect();
    // The last line has a semicolon; only the first 6 lines should be flagged.
    assert_eq!(
        flagged_lines.len(), 6,
        "6 of the 7 lines lack semicolons (LIMIT line has one). Got: {:?}", flagged_lines
    );
}

// ============================================================================
// Error handling for invalid VCL-total
// ============================================================================

#[test]
fn e2e_error_missing_semicolons_throughout() {
    // None of these lines end with semicolons — every line must be flagged.
    let query = "SELECT id\nFROM users\nWHERE id = 1";
    let issues = lint_vqlut(query);
    let semicolon_flags: Vec<_> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert_eq!(
        semicolon_flags.len(), 3,
        "all 3 lines must be flagged for missing semicolon, got {}", semicolon_flags.len()
    );
}

#[test]
fn e2e_error_lowercase_keywords_all_flagged() {
    // All SQL keywords in lowercase surrounded by spaces.
    let query = "a select b from c where d;";
    let issues = lint_vqlut(query);
    let kw_issues: Vec<_> = issues
        .iter()
        .filter(|i| i.message.contains("should be uppercase"))
        .collect();
    // "select", "from", "where" should all be detected.
    assert!(
        kw_issues.len() >= 3,
        "at least 3 keyword issues expected, got {}: {:?}",
        kw_issues.len(),
        kw_issues.iter().map(|i| &i.message).collect::<Vec<_>>()
    );
}

#[test]
fn e2e_error_does_not_panic_on_unicode_input() {
    // Unicode content must not panic the formatter or linter.
    let query = "SELECT 'héllo wörld' FROM üsers WHERE naïve = true;";
    let formatted = format_vqlut(query);
    let issues = lint_vqlut(&formatted);
    // No assertion about issue count — just that neither function panics.
    let _ = (formatted, issues);
}

#[test]
fn e2e_error_does_not_panic_on_binary_like_input() {
    // Null bytes and control chars must not panic.
    let query = "SELECT\0 id FROM\t users;";
    let formatted = format_vqlut(query);
    let issues = lint_vqlut(&formatted);
    let _ = (formatted, issues);
}

// ============================================================================
// Round-trip parsing consistency
// ============================================================================

#[test]
fn e2e_round_trip_consistent_after_two_passes() {
    // The formatter must be idempotent: applying it twice gives the same result.
    let raw = "  SELECT id, name\n  FROM users\n  WHERE active = 1;";
    let pass_one = format_vqlut(raw);
    let pass_two = format_vqlut(&pass_one);
    assert_eq!(
        pass_one, pass_two,
        "formatter must be idempotent after first application"
    );
}

#[test]
fn e2e_round_trip_lint_issues_stable_after_reformatting() {
    // Re-formatting must not change lint issue count.
    let query = "SELECT id\nFROM users";
    let first_fmt  = format_vqlut(query);
    let second_fmt = format_vqlut(&first_fmt);

    let issues_first  = lint_vqlut(&first_fmt);
    let issues_second = lint_vqlut(&second_fmt);

    assert_eq!(
        issues_first.len(), issues_second.len(),
        "lint issue count must be stable across format passes"
    );
}

#[test]
fn e2e_round_trip_keyword_indentation_preserved() {
    // After round-trip, keyword lines must still have the two-space indent.
    let query = "SELECT id FROM users;";
    let formatted = format_vqlut(query);
    let reformatted = format_vqlut(&formatted);
    let first_line = reformatted.lines().next()
        .expect("reformatted output must have at least one line");
    assert!(
        first_line.starts_with("  SELECT"),
        "SELECT must remain indented after round-trip, got: {:?}", first_line
    );
}

// ============================================================================
// Formatter and linter agreement on canonical output
// ============================================================================

#[test]
fn e2e_formatter_does_not_introduce_semicolon_issues() {
    // The formatter must not strip semicolons from the input.
    // A single-line query with a semicolon, once formatted, must not acquire
    // a 'missing semicolon' lint issue.
    // Note: the linter uses a space-delimited, case-insensitive keyword check,
    // so even well-formatted queries may trigger keyword-case issues — that is
    // documented linter behaviour, not a bug introduced by the formatter.
    let query = "SELECT id;";
    let formatted = format_vqlut(query);
    let issues = lint_vqlut(&formatted);
    let semicolon_issues: Vec<_> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(
        semicolon_issues.is_empty(),
        "formatter must not strip semicolons: {:?}", semicolon_issues
    );
}

#[test]
fn e2e_formatter_preserves_query_content_after_trimming() {
    // Formatting must not drop content — only adjust leading whitespace.
    let query = "SELECT   id,   name   FROM   users;";
    let formatted = format_vqlut(query);
    assert!(
        formatted.contains("id,   name"),
        "formatter must preserve content between keywords, got: {:?}", formatted
    );
}

#[test]
fn e2e_all_keywords_indented_in_formatted_output() {
    let lines_with_keywords = [
        ("SELECT *;",        "SELECT"),
        ("FROM t;",          "FROM"),
        ("WHERE x = 1;",     "WHERE"),
        ("GROUP BY y;",      "GROUP"),
        ("ORDER BY z;",      "ORDER"),
        ("HAVING n > 0;",    "HAVING"),
        ("LIMIT 5;",         "LIMIT"),
    ];
    for (input, kw) in &lines_with_keywords {
        let formatted = format_vqlut(input);
        let first_line = formatted.lines().next()
            .expect("must produce at least one line");
        assert!(
            first_line.starts_with("  "),
            "keyword '{}' line must be indented, got: {:?}", kw, first_line
        );
        assert!(
            first_line.contains(kw),
            "formatted output must contain keyword '{}', got: {:?}", kw, first_line
        );
    }
}

// ============================================================================
// Lint line-number accuracy on multi-line queries
// ============================================================================

#[test]
fn e2e_lint_line_numbers_accurate_on_6_line_query() {
    let query = "SELECT id\nFROM users\nWHERE id > 0\nGROUP BY dept\nORDER BY name\nLIMIT 10;";
    let issues = lint_vqlut(query);
    let flagged: Vec<usize> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .map(|i| i.line)
        .collect();
    // Lines 1-5 lack semicolons; line 6 has one.
    assert_eq!(
        flagged, vec![1, 2, 3, 4, 5],
        "lines 1-5 must be flagged for missing semicolons, got: {:?}", flagged
    );
}
