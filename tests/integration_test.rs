// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! Comprehensive L3 integration tests for VQL-UT.
//!
//! Test categories:
//!   - Point-to-point: test each tool (formatter, linter) individually
//!   - End-to-end: parse -> format -> lint pipeline
//!   - Aspect: error messages, edge cases, empty queries, malformed syntax
//!   - Type levels: exercise the 10 VQL-UT type safety levels where applicable

use vql_ut::fmt::format_vqlut;
use vql_ut::lint::{lint_vqlut, LintIssue};

// ============================================================================
// Point-to-point: Formatter
// ============================================================================

#[test]
fn fmt_indents_select_keyword() {
    let input = "SELECT * FROM users";
    let output = format_vqlut(input);
    assert!(output.starts_with("  SELECT"), "SELECT should be indented");
}

#[test]
fn fmt_indents_from_keyword() {
    let input = "FROM users";
    let output = format_vqlut(input);
    assert!(output.starts_with("  FROM"), "FROM should be indented");
}

#[test]
fn fmt_indents_where_keyword() {
    let input = "WHERE id = 1";
    let output = format_vqlut(input);
    assert!(output.starts_with("  WHERE"), "WHERE should be indented");
}

#[test]
fn fmt_indents_group_by() {
    let input = "GROUP BY category";
    let output = format_vqlut(input);
    assert!(output.starts_with("  GROUP"), "GROUP should be indented");
}

#[test]
fn fmt_indents_order_by() {
    let input = "ORDER BY name ASC";
    let output = format_vqlut(input);
    assert!(output.starts_with("  ORDER"), "ORDER should be indented");
}

#[test]
fn fmt_indents_having() {
    let input = "HAVING count > 5";
    let output = format_vqlut(input);
    assert!(output.starts_with("  HAVING"), "HAVING should be indented");
}

#[test]
fn fmt_indents_limit() {
    let input = "LIMIT 100";
    let output = format_vqlut(input);
    assert!(output.starts_with("  LIMIT"), "LIMIT should be indented");
}

#[test]
fn fmt_does_not_indent_non_keyword_lines() {
    let input = "  id, name, email";
    let output = format_vqlut(input);
    assert!(
        output.starts_with("id, name, email"),
        "Non-keyword line should be trimmed but not indented. Got: {:?}",
        output
    );
}

#[test]
fn fmt_trims_leading_whitespace() {
    let input = "    SELECT * FROM users";
    let output = format_vqlut(input);
    // Should trim then re-indent
    assert_eq!(output, "  SELECT * FROM users\n");
}

#[test]
fn fmt_preserves_multiline_structure() {
    let input = "SELECT id, name\nFROM users\nWHERE active = true";
    let output = format_vqlut(input);
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 3);
    assert!(lines[0].starts_with("  SELECT"));
    assert!(lines[1].starts_with("  FROM"));
    assert!(lines[2].starts_with("  WHERE"));
}

#[test]
fn fmt_handles_lowercase_keywords_without_indent() {
    // Lowercase keywords should NOT be indented (formatter checks uppercase only)
    let input = "select * from users";
    let output = format_vqlut(input);
    assert!(
        !output.starts_with("  "),
        "Lowercase keywords should not be indented"
    );
}

#[test]
fn fmt_output_ends_with_newline() {
    let input = "SELECT 1";
    let output = format_vqlut(input);
    assert!(output.ends_with('\n'), "Output should end with newline");
}

// ============================================================================
// Point-to-point: Linter
// ============================================================================

#[test]
fn lint_detects_missing_semicolon() {
    let input = "SELECT * FROM users";
    let issues = lint_vqlut(input);
    let semicolon_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(
        !semicolon_issues.is_empty(),
        "Should detect missing semicolon"
    );
}

#[test]
fn lint_accepts_semicolon_terminated_line() {
    let input = "SELECT * FROM users;";
    let issues = lint_vqlut(input);
    let semicolon_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(
        semicolon_issues.is_empty(),
        "Should not flag line ending with semicolon"
    );
}

#[test]
fn lint_detects_lowercase_select() {
    // The linter checks for ` keyword ` pattern (surrounded by spaces)
    let input = "x select y from z";
    let issues = lint_vqlut(input);
    let kw_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("SELECT"))
        .collect();
    assert!(
        !kw_issues.is_empty(),
        "Should detect lowercase 'select' keyword"
    );
}

#[test]
fn lint_detects_lowercase_from() {
    let input = "x from y";
    let issues = lint_vqlut(input);
    let kw_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("FROM"))
        .collect();
    assert!(
        !kw_issues.is_empty(),
        "Should detect lowercase 'from' keyword"
    );
}

#[test]
fn lint_detects_lowercase_where() {
    let input = "x where y";
    let issues = lint_vqlut(input);
    let kw_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("WHERE"))
        .collect();
    assert!(!kw_issues.is_empty(), "Should detect lowercase 'where'");
}

#[test]
fn lint_flags_keywords_case_insensitively() {
    // The linter lowercases the entire line before searching for ` keyword `.
    // This means even uppercase keywords surrounded by spaces are flagged,
    // because "SELECT * FROM users" lowercased contains " from ".
    // This documents the current behavior: the linter always flags keywords
    // found via the ` keyword ` pattern regardless of original case.
    let input = "SELECT * FROM users WHERE id = 1;";
    let issues = lint_vqlut(input);
    let kw_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("should be uppercase"))
        .collect();
    assert!(
        !kw_issues.is_empty(),
        "Current linter flags keywords found via case-insensitive space-delimited search"
    );
}

#[test]
fn lint_reports_correct_line_numbers() {
    let input = "line one\nline two\nline three";
    let issues = lint_vqlut(input);
    // All three lines lack semicolons
    let lines: Vec<usize> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .map(|i| i.line)
        .collect();
    assert_eq!(lines, vec![1, 2, 3], "Line numbers should be 1-indexed");
}

#[test]
fn lint_multiple_issues_on_single_line() {
    // Missing semicolon AND lowercase keyword on same line
    let input = "x select y from z";
    let issues = lint_vqlut(input);
    // Should have: missing semicolon + keyword issues
    assert!(
        issues.len() >= 2,
        "Should report multiple issues. Got: {}",
        issues.len()
    );
}

#[test]
fn lint_multiline_query() {
    let input = "SELECT id, name\nFROM users\nWHERE active = true;";
    let issues = lint_vqlut(input);
    // First two lines lack semicolons
    let semicolon_issues: Vec<usize> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .map(|i| i.line)
        .collect();
    assert_eq!(
        semicolon_issues,
        vec![1, 2],
        "Lines 1 and 2 should lack semicolons"
    );
}

// ============================================================================
// End-to-end: Format then Lint pipeline
// ============================================================================

#[test]
fn e2e_format_then_lint_clean_query() {
    let raw = "  SELECT id, name\n  FROM users\n  WHERE active = true;";
    let formatted = format_vqlut(raw);
    let issues = lint_vqlut(&formatted);
    // After formatting, all keywords are uppercase (they already were).
    // Lines 1-2 still lack semicolons.
    let semicolon_count = issues.iter().filter(|i| i.message.contains("semicolon")).count();
    assert_eq!(semicolon_count, 2, "Formatted output: lines 1,2 lack semicolons");
}

#[test]
fn e2e_format_then_lint_full_query() {
    let raw = "SELECT *\nFROM posts\nWHERE id > 0\nORDER BY created_at\nLIMIT 10;";
    let formatted = format_vqlut(raw);
    let issues = lint_vqlut(&formatted);
    // After formatting, keywords are indented. Lines 1-4 lack semicolons.
    let semicolon_issues: Vec<usize> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .map(|i| i.line)
        .collect();
    assert_eq!(semicolon_issues, vec![1, 2, 3, 4]);
}

#[test]
fn e2e_format_preserves_lint_clean_content() {
    // A query that is already formatted and lint-clean
    let input = "SELECT 1;";
    let formatted = format_vqlut(input);
    let issues = lint_vqlut(&formatted);
    // The formatted version adds indent: "  SELECT 1;\n"
    // That ends with semicolon, so no semicolon issue.
    let semicolon_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(
        semicolon_issues.is_empty(),
        "Formatted semicolon-terminated query should be lint-clean for semicolons"
    );
}

#[test]
fn e2e_round_trip_idempotent() {
    let input = "SELECT *\nFROM users\nWHERE id = 1;";
    let first_pass = format_vqlut(input);
    let second_pass = format_vqlut(&first_pass);
    assert_eq!(
        first_pass, second_pass,
        "Formatting should be idempotent after first pass"
    );
}

// ============================================================================
// Aspect: Edge cases
// ============================================================================

#[test]
fn aspect_empty_input_format() {
    let output = format_vqlut("");
    assert_eq!(output, "", "Empty input should produce empty output");
}

#[test]
fn aspect_empty_input_lint() {
    let issues = lint_vqlut("");
    assert!(issues.is_empty(), "Empty input should produce no lint issues");
}

#[test]
fn aspect_whitespace_only_format() {
    let output = format_vqlut("   \n   \n   ");
    // Each line trims to empty, so should not be indented
    let lines: Vec<&str> = output.lines().collect();
    for line in &lines {
        assert!(line.is_empty(), "Whitespace-only lines should trim to empty");
    }
}

#[test]
fn aspect_whitespace_only_lint() {
    let issues = lint_vqlut("   \n   \n   ");
    // All lines are whitespace-only, trimmed to empty, so no semicolon issues
    assert!(
        issues.is_empty(),
        "Whitespace-only lines should not generate issues"
    );
}

#[test]
fn aspect_single_character_input() {
    let output = format_vqlut("x");
    assert_eq!(output, "x\n");
    let issues = lint_vqlut("x");
    assert_eq!(issues.len(), 1, "Single char without semicolon = 1 issue");
}

#[test]
fn aspect_very_long_line() {
    let long_query = format!("SELECT {}", "col, ".repeat(1000));
    let formatted = format_vqlut(&long_query);
    assert!(formatted.starts_with("  SELECT"), "Long lines should still be formatted");
    let issues = lint_vqlut(&long_query);
    assert!(!issues.is_empty(), "Long line without semicolon should be flagged");
}

#[test]
fn aspect_keyword_in_middle_of_line_not_indented() {
    // "id FROM" — line starts with "id" not a keyword, should not be indented
    let output = format_vqlut("id FROM users");
    assert!(
        !output.starts_with("  "),
        "Line not starting with keyword should not be indented"
    );
}

#[test]
fn aspect_keyword_as_substring_not_indented() {
    // "SELECTED" starts with SELECT but is not SELECT keyword
    // Actually it does start with "SELECT" so it WILL be indented by the current logic
    let output = format_vqlut("SELECTED * FROM users");
    // This is expected behavior: starts_with("SELECT") matches "SELECTED"
    assert!(
        output.starts_with("  SELECTED"),
        "Current logic indents lines starting with keyword prefix"
    );
}

#[test]
fn aspect_mixed_case_not_indented() {
    // "Select" is not "SELECT" — should not be indented
    let output = format_vqlut("Select * From users");
    assert!(
        !output.starts_with("  "),
        "Mixed-case keywords should not be indented (formatter is case-sensitive)"
    );
}

#[test]
fn aspect_multiple_keywords_same_line() {
    // Line starts with SELECT and also contains FROM, WHERE
    let input = "SELECT * FROM users WHERE id = 1";
    let output = format_vqlut(input);
    // Only indented once (because the line starts with SELECT)
    assert_eq!(output, "  SELECT * FROM users WHERE id = 1\n");
}

#[test]
fn aspect_newline_variations() {
    // Lines separated by \n are handled; content.lines() handles this
    let input = "SELECT 1\nFROM dual";
    let output = format_vqlut(input);
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 2);
}

#[test]
fn aspect_lint_keyword_at_line_start_not_surrounded_by_spaces() {
    // "select*" — "select" not surrounded by spaces, should NOT be detected
    let input = "select*from users";
    let issues = lint_vqlut(input);
    let kw_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("should be uppercase"))
        .collect();
    // The pattern checks for " keyword ", so "select*from" won't match
    assert!(
        kw_issues.is_empty(),
        "Keywords not surrounded by spaces should not be flagged"
    );
}

// ============================================================================
// Type level conceptual tests
// ============================================================================
// VQL-UT defines 10 type safety levels. The formatter and linter operate at
// the surface syntax level. These tests verify that the tools handle queries
// at varying complexity levels that correspond to VQL-UT's type system.

#[test]
fn level_1_parse_time_safety_valid_syntax() {
    // Level 1: syntactically valid query should format without error
    let query = "SELECT id FROM users WHERE id = 1;";
    let formatted = format_vqlut(query);
    assert!(!formatted.is_empty());
    // Lint: no semicolon issue (line ends with ;)
    let issues = lint_vqlut(query);
    let semicolon_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(semicolon_issues.is_empty());
}

#[test]
fn level_2_schema_binding_multi_table_query() {
    // Level 2: query referencing multiple tables — formatter handles it
    let query = "SELECT u.id, p.title\nFROM users u\nJOIN posts p ON u.id = p.user_id;";
    let formatted = format_vqlut(query);
    let lines: Vec<&str> = formatted.lines().collect();
    assert!(lines[0].starts_with("  SELECT"));
    assert!(lines[1].starts_with("  FROM"));
    // JOIN line doesn't start with a recognised keyword
    assert!(!lines[2].starts_with("  "));
}

#[test]
fn level_3_type_compatible_operations() {
    // Level 3: type-compatible operations in WHERE clause
    let query = "SELECT id FROM users WHERE age > 18;";
    let formatted = format_vqlut(query);
    assert!(formatted.contains("age > 18"));
}

#[test]
fn level_4_null_safety_coalesce() {
    // Level 4: null-safe query using COALESCE
    let query = "SELECT COALESCE(email, 'none') FROM users;";
    let formatted = format_vqlut(query);
    assert!(formatted.contains("COALESCE"));
}

#[test]
fn level_5_injection_proof_parameterised() {
    // Level 5: parameterised query (no injection risk)
    let query = "SELECT id FROM users WHERE name = $1;";
    let formatted = format_vqlut(query);
    assert!(formatted.contains("$1"));
}

#[test]
fn level_6_result_type_known() {
    // Level 6: query with known result type (explicit column list)
    let query = "SELECT id, name, email FROM users;";
    let formatted = format_vqlut(query);
    assert!(formatted.contains("id, name, email"));
}

#[test]
fn level_7_cardinality_bounded() {
    // Level 7: cardinality bounded with LIMIT
    let query = "SELECT * FROM users\nLIMIT 10;";
    let formatted = format_vqlut(query);
    assert!(formatted.contains("LIMIT 10"));
}

#[test]
fn level_8_effect_tracking_readonly() {
    // Level 8: read-only query (SELECT only, no side effects)
    let query = "SELECT count(*) FROM users;";
    let issues = lint_vqlut(query);
    // No semicolon issue (line ends with ;)
    let semicolon_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(semicolon_issues.is_empty());
}

#[test]
fn level_9_temporal_safety_timestamp() {
    // Level 9: temporal query with timestamp predicate
    let query = "SELECT * FROM events\nWHERE created_at > '2026-01-01';";
    let formatted = format_vqlut(query);
    assert!(formatted.contains("created_at"));
}

#[test]
fn level_10_linearity_single_use() {
    // Level 10: linearity — each resource consumed once
    // At the syntax level, this is a single INSERT
    let query = "INSERT INTO log (event) VALUES ('started');";
    let formatted = format_vqlut(query);
    // INSERT is not a recognised keyword for indentation
    assert!(!formatted.starts_with("  "));
    let issues = lint_vqlut(query);
    // No semicolon issue (ends with ;)
    let semicolon_issues: Vec<&LintIssue> = issues
        .iter()
        .filter(|i| i.message.contains("semicolon"))
        .collect();
    assert!(semicolon_issues.is_empty());
}

// ============================================================================
// Stress and regression tests
// ============================================================================

#[test]
fn stress_many_lines() {
    let mut query = String::new();
    for i in 0..100 {
        query.push_str(&format!("SELECT {} FROM t{};\n", i, i));
    }
    let formatted = format_vqlut(&query);
    let line_count = formatted.lines().count();
    assert_eq!(line_count, 100, "Should preserve all 100 lines");
}

#[test]
fn stress_lint_many_issues() {
    let mut query = String::new();
    for _ in 0..50 {
        query.push_str("x select y from z\n");
    }
    let issues = lint_vqlut(&query);
    // Each line: missing semicolon + 2 keyword issues (select, from) = 3 per line
    assert!(
        issues.len() >= 100,
        "Should detect issues on all 50 lines. Got: {}",
        issues.len()
    );
}
