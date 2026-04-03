// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! QuickCheck fuzz harness for VQL-UT.
//!
//! This keeps the fuzz submission small and focused: it exercises the public
//! formatter and linter on arbitrary input and checks simple invariants.

use quickcheck::{QuickCheck, TestResult};
use vql_ut::fmt::format_vqlut;
use vql_ut::lint::lint_vqlut;

fn prop_format_is_idempotent(input: String) -> TestResult {
    let once = format_vqlut(&input);
    let twice = format_vqlut(&once);
    TestResult::from_bool(once == twice)
}

fn prop_lint_is_deterministic(input: String) -> TestResult {
    let first = lint_vqlut(&input);
    let second = lint_vqlut(&input);

    let normalize = |issues: Vec<vql_ut::lint::LintIssue>| {
        issues
            .into_iter()
            .map(|issue| (issue.line, issue.message))
            .collect::<Vec<_>>()
    };

    TestResult::from_bool(normalize(first) == normalize(second))
}

#[test]
fn fuzz_formatter_idempotence() {
    QuickCheck::new()
        .tests(256)
        .quickcheck(prop_format_is_idempotent as fn(String) -> TestResult);
}

#[test]
fn fuzz_linter_determinism() {
    QuickCheck::new()
        .tests(256)
        .quickcheck(prop_lint_is_deterministic as fn(String) -> TestResult);
}
