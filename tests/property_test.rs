// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Property-based tests for VCL-total using proptest.
//!
//! Verifies algebraic invariants that must hold for all VCL-total input strings:
//! - Formatting idempotence: format(format(x)) == format(x)
//! - Type inference determinism: lint(x) always produces the same count
//! - Valid queries (correct case, with semicolons) never panic

use proptest::prelude::*;
use vcl_total::fmt::format_vqlut;
use vcl_total::lint::lint_vqlut;

// ============================================================================
// Arbitrary input generators
// ============================================================================

/// Generate a random ASCII string that could plausibly appear in a VCL query.
fn arb_query_fragment() -> impl Strategy<Value = String> {
    // Use printable ASCII range to avoid encoding-related panics.
    prop::string::string_regex("[a-zA-Z0-9 _,.*=><;()'\"\\-\n]{1,200}")
        .expect("regex must compile")
}

/// Generate a string starting with a recognised VCL-total keyword (uppercase).
fn arb_keyword_line() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("SELECT id;".to_string()),
        Just("FROM users;".to_string()),
        Just("WHERE id = 1;".to_string()),
        Just("GROUP BY dept;".to_string()),
        Just("ORDER BY name;".to_string()),
        Just("HAVING count > 0;".to_string()),
        Just("LIMIT 100;".to_string()),
    ]
}

/// Generate a multi-line query by joining keyword lines.
fn arb_multiline_query() -> impl Strategy<Value = String> {
    prop::collection::vec(arb_keyword_line(), 1..=5)
        .prop_map(|lines| lines.join("\n"))
}

// ============================================================================
// Property: formatting is idempotent
// ============================================================================

proptest! {
    #[test]
    fn prop_formatting_idempotent(query in arb_query_fragment()) {
        let first  = format_vqlut(&query);
        let second = format_vqlut(&first);
        prop_assert_eq!(
            first, second,
            "format must be idempotent after first application"
        );
    }
}

proptest! {
    #[test]
    fn prop_formatting_idempotent_keyword_lines(query in arb_multiline_query()) {
        let first  = format_vqlut(&query);
        let second = format_vqlut(&first);
        prop_assert_eq!(
            first, second,
            "format must be idempotent on keyword-line queries"
        );
    }
}

// ============================================================================
// Property: lint issue count is deterministic (same input → same count)
// ============================================================================

proptest! {
    #[test]
    fn prop_lint_count_deterministic(query in arb_query_fragment()) {
        let issues_a = lint_vqlut(&query);
        let issues_b = lint_vqlut(&query);
        prop_assert_eq!(
            issues_a.len(), issues_b.len(),
            "lint must be deterministic: same input must give same issue count"
        );
    }
}

// ============================================================================
// Property: valid queries (uppercase keywords, trailing semicolons) never panic
// ============================================================================

proptest! {
    #[test]
    fn prop_valid_queries_never_panic(query in arb_multiline_query()) {
        // Both functions must return without panicking.
        let formatted = format_vqlut(&query);
        let _issues   = lint_vqlut(&formatted);
        // If we reach here, no panic occurred.
        prop_assert!(!formatted.is_empty() || query.is_empty());
    }
}

// ============================================================================
// Property: arbitrary inputs never panic (robustness / no unwrap panics)
// ============================================================================

proptest! {
    #[test]
    fn prop_arbitrary_input_never_panics_formatter(query in arb_query_fragment()) {
        // Must not panic regardless of input content.
        let _ = format_vqlut(&query);
    }
}

proptest! {
    #[test]
    fn prop_arbitrary_input_never_panics_linter(query in arb_query_fragment()) {
        // Must not panic regardless of input content.
        let _ = lint_vqlut(&query);
    }
}

// ============================================================================
// Property: formatter does not increase line count
// ============================================================================

proptest! {
    #[test]
    fn prop_formatter_preserves_line_count(query in arb_query_fragment()) {
        // count() on lines() handles trailing newlines consistently.
        let input_line_count  = query.lines().count();
        let formatted         = format_vqlut(&query);
        let output_line_count = formatted.lines().count();
        prop_assert_eq!(
            input_line_count, output_line_count,
            "formatter must not add or remove lines"
        );
    }
}

// ============================================================================
// Property: lines ending with ';' are never flagged for missing semicolon
// ============================================================================

proptest! {
    #[test]
    fn prop_semicolon_terminated_lines_not_flagged(
        prefix in "[a-zA-Z0-9 _,*=><()]{1,50}",
    ) {
        let query = format!("{prefix};");
        let issues = lint_vqlut(&query);
        let semicolon_issues: Vec<_> = issues
            .iter()
            .filter(|i| i.message.contains("semicolon"))
            .collect();
        prop_assert!(
            semicolon_issues.is_empty(),
            "line ending with ';' must not be flagged for missing semicolon. Issues: {:?}",
            semicolon_issues.iter().map(|i| &i.message).collect::<Vec<_>>()
        );
    }
}

// ============================================================================
// Property: lines without ';' are always flagged for missing semicolon
// ============================================================================

proptest! {
    #[test]
    fn prop_non_semicolon_lines_always_flagged(
        content in "[a-zA-Z][a-zA-Z0-9 _,*=><()]{1,50}",
    ) {
        // Ensure content neither ends with ';' nor is empty after trim.
        prop_assume!(!content.trim().is_empty());
        prop_assume!(!content.trim().ends_with(';'));

        let issues = lint_vqlut(&content);
        let semicolon_issues: Vec<_> = issues
            .iter()
            .filter(|i| i.message.contains("semicolon"))
            .collect();
        prop_assert!(
            !semicolon_issues.is_empty(),
            "non-empty line without ';' must be flagged. content: {:?}", content
        );
    }
}

// ============================================================================
// Property: formatting is a pure function (no observable side effects)
// ============================================================================

proptest! {
    #[test]
    fn prop_formatter_is_pure(query in arb_query_fragment()) {
        let result_a = format_vqlut(&query);
        let result_b = format_vqlut(&query);
        prop_assert_eq!(result_a, result_b, "formatter must be a pure function");
    }
}
