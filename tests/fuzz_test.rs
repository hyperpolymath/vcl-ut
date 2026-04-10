// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Fuzz-style exhaustive property tests for VCL-total.
//!
//! These tests use proptest with high case counts to approximate fuzzing
//! without requiring nightly Rust or cargo-fuzz. They target the same
//! invariants a real fuzzer would: no panics, no infinite loops, no
//! memory corruption on arbitrary (including adversarial) input.
//!
//! Run with: cargo test --test fuzz_test
//!
//! For deeper fuzzing with cargo-fuzz (nightly):
//!   cargo +nightly fuzz run fuzz_format
//!   cargo +nightly fuzz run fuzz_lint

use proptest::prelude::*;
use vcl_total::fmt::format_vqlut;
use vcl_total::lint::lint_vqlut;

// ============================================================================
// Generators for adversarial input
// ============================================================================

/// Fully arbitrary bytes interpreted as UTF-8 (lossy).
fn arb_raw_bytes() -> impl Strategy<Value = String> {
    prop::collection::vec(any::<u8>(), 0..512)
        .prop_map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
}

/// Strings containing SQL injection payloads.
fn arb_injection_payload() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("' OR '1'='1".to_string()),
        Just("'; DROP TABLE users; --".to_string()),
        Just("1; EXEC xp_cmdshell('whoami')".to_string()),
        Just("' UNION SELECT password FROM credentials --".to_string()),
        Just(
            "1' AND 1=CONVERT(int,(SELECT TOP 1 table_name FROM information_schema.tables))--"
                .to_string()
        ),
        Just("admin'--".to_string()),
        Just("' OR ''='".to_string()),
        Just("'; SHUTDOWN; --".to_string()),
        Just("1; WAITFOR DELAY '0:0:5'; --".to_string()),
        Just("SELECT CHAR(0x41)".to_string()),
    ]
}

/// Strings with unusual Unicode: RTL overrides, zero-width chars, surrogates.
fn arb_unicode_edge_cases() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("SELECT \u{200B}id FROM users;".to_string()), // zero-width space
        Just("SELECT \u{202E}di FROM users;".to_string()), // RTL override
        Just("SELECT \u{FEFF}id FROM users;".to_string()), // BOM
        Just("\u{0000}SELECT id;\u{0000}".to_string()),    // null bytes
        Just("SELECT '🦀' FROM t;".to_string()),           // emoji
        Just("SELECT '\u{10FFFF}' FROM t;".to_string()),   // max codepoint
        Just("SELECT id FROM \u{200D}users;".to_string()), // zero-width joiner
        Just("SÉLECT ïd FRÖM üsers;".to_string()),         // accented chars
    ]
}

/// Extremely long or repetitive input.
fn arb_stress_input() -> impl Strategy<Value = String> {
    prop_oneof![
        // Very long single line
        Just("SELECT ".to_string() + &"a,".repeat(5000) + "z FROM t;"),
        // Many short lines
        Just(
            (0..500)
                .map(|i| format!("SELECT col{i};"))
                .collect::<Vec<_>>()
                .join("\n")
        ),
        // Deep nesting
        Just("SELECT ".to_string() + &"(".repeat(200) + "1" + &")".repeat(200) + ";"),
        // Repeated keywords
        Just("SELECT ".repeat(500) + ";"),
        // Only whitespace
        Just(" \t\n\r ".repeat(1000)),
    ]
}

// ============================================================================
// Fuzz: formatter never panics on arbitrary input
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn fuzz_format_raw_bytes(input in arb_raw_bytes()) {
        let _ = format_vqlut(&input);
    }

    #[test]
    fn fuzz_format_injection_payloads(input in arb_injection_payload()) {
        let result = format_vqlut(&input);
        // Injection content must be preserved (not silently stripped).
        prop_assert!(!result.is_empty() || input.is_empty());
    }

    #[test]
    fn fuzz_format_unicode_edge_cases(input in arb_unicode_edge_cases()) {
        let _ = format_vqlut(&input);
    }
}

// ============================================================================
// Fuzz: linter never panics on arbitrary input
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn fuzz_lint_raw_bytes(input in arb_raw_bytes()) {
        let _ = lint_vqlut(&input);
    }

    #[test]
    fn fuzz_lint_injection_payloads(input in arb_injection_payload()) {
        let _ = lint_vqlut(&input);
    }

    #[test]
    fn fuzz_lint_unicode_edge_cases(input in arb_unicode_edge_cases()) {
        let _ = lint_vqlut(&input);
    }
}

// ============================================================================
// Fuzz: full pipeline (format → lint) never panics
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn fuzz_pipeline_raw_bytes(input in arb_raw_bytes()) {
        let formatted = format_vqlut(&input);
        let _ = lint_vqlut(&formatted);
    }

    #[test]
    fn fuzz_pipeline_injection(input in arb_injection_payload()) {
        let formatted = format_vqlut(&input);
        let _ = lint_vqlut(&formatted);
    }
}

// ============================================================================
// Stress tests: large/adversarial inputs
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    #[test]
    fn fuzz_stress_formatter(input in arb_stress_input()) {
        let _ = format_vqlut(&input);
    }

    #[test]
    fn fuzz_stress_linter(input in arb_stress_input()) {
        let _ = lint_vqlut(&input);
    }

    #[test]
    fn fuzz_stress_pipeline(input in arb_stress_input()) {
        let formatted = format_vqlut(&input);
        let _ = lint_vqlut(&formatted);
    }
}

// ============================================================================
// Invariant: format(format(x)) == format(x) even on adversarial input
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn fuzz_idempotence_raw_bytes(input in arb_raw_bytes()) {
        let first = format_vqlut(&input);
        let second = format_vqlut(&first);
        prop_assert_eq!(first, second, "idempotence must hold on arbitrary input");
    }
}

// ============================================================================
// Invariant: lint count is deterministic even on adversarial input
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn fuzz_lint_deterministic_raw_bytes(input in arb_raw_bytes()) {
        let a = lint_vqlut(&input).len();
        let b = lint_vqlut(&input).len();
        prop_assert_eq!(a, b, "lint must be deterministic on arbitrary input");
    }
}
