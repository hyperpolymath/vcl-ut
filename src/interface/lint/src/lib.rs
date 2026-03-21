// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! VQL-UT Linting Library
//!
//! Provides linting capabilities for VQL-UT query files.
//! Checks for missing semicolons and lowercase keywords.

/// A single lint issue found in VQL-UT content.
#[derive(Debug)]
pub struct LintIssue {
    /// 1-indexed line number where the issue was found.
    pub line: usize,
    /// Human-readable description of the issue.
    pub message: String,
}

/// Lint VQL-UT content and return a list of issues.
///
/// Current checks:
/// - Missing semicolons at the end of non-empty lines
/// - Lowercase keywords (select, from, where, group, order, having, limit)
///   when surrounded by spaces (` keyword `)
pub fn lint_vqlut(content: &str) -> Vec<LintIssue> {
    let mut issues = Vec::new();

    // Check for missing semicolons
    for (i, line) in content.lines().enumerate() {
        let line_num = i + 1;
        let trimmed = line.trim();
        if !trimmed.is_empty() && !trimmed.ends_with(';') {
            issues.push(LintIssue {
                line: line_num,
                message: "Missing semicolon".to_string(),
            });
        }
    }

    // Check for uppercase keywords
    for (i, line) in content.lines().enumerate() {
        let line_num = i + 1;
        let keywords = ["select", "from", "where", "group", "order", "having", "limit"];
        for keyword in keywords {
            if line.to_lowercase().contains(&format!(" {} ", keyword)) {
                issues.push(LintIssue {
                    line: line_num,
                    message: format!("Keyword '{}' should be uppercase", keyword.to_uppercase()),
                });
            }
        }
    }

    issues
}
