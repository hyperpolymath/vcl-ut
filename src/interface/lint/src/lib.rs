#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! VCL-total Linting Library
//!
//! Provides linting capabilities for VCL-total query files.
//! Checks for missing semicolons, lowercase keywords, SELECT *, and OFFSET without LIMIT.

/// A single lint issue found in VCL-total content.
#[derive(Debug)]
pub struct LintIssue {
    /// 1-indexed line number where the issue was found.
    pub line: usize,
    /// Human-readable description of the issue.
    pub message: String,
}

/// Lint VCL-total content and return a list of issues.
///
/// Current checks:
/// - Missing semicolons at the end of non-empty lines
/// - Lowercase keywords (SQL and VCL-total extension keywords)
///   when surrounded by spaces (` keyword `)
/// - `SELECT *` usage (prefer explicit columns for Level 5 result typing)
/// - `OFFSET` without `LIMIT` (likely a mistake)
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

    // Check for lowercase keywords: flag keywords that appear (case-insensitive)
    // but are not already uppercase in the original text.
    let keywords = [
        "select", "from", "where", "group", "order", "having", "limit",
        "offset", "effects", "proof", "consume", "usage",
    ];
    for (i, line) in content.lines().enumerate() {
        let line_num = i + 1;
        for keyword in keywords {
            let lower_pattern = format!(" {} ", keyword);
            if line.to_lowercase().contains(&lower_pattern) {
                let upper_pattern = format!(" {} ", keyword.to_uppercase());
                if !line.contains(&upper_pattern) {
                    issues.push(LintIssue {
                        line: line_num,
                        message: format!(
                            "Keyword '{}' should be uppercase",
                            keyword.to_uppercase()
                        ),
                    });
                }
            }
        }
    }

    // Check for SELECT * (prefer explicit columns for Level 5 result typing)
    let upper_content = content.to_uppercase();
    for (i, line) in upper_content.lines().enumerate() {
        let line_num = i + 1;
        let trimmed = line.trim();
        if trimmed.starts_with("SELECT") && trimmed.contains("SELECT *") {
            issues.push(LintIssue {
                line: line_num,
                message: "Prefer explicit column list over SELECT * for result-type safety (Level 5)".to_string(),
            });
        }
    }

    // Check for OFFSET without LIMIT (likely a mistake — OFFSET is meaningless without LIMIT)
    let has_offset = upper_content.lines().any(|l| {
        let t = l.trim();
        t.starts_with("OFFSET") || t.contains(" OFFSET ")
    });
    let has_limit = upper_content.lines().any(|l| {
        let t = l.trim();
        t.starts_with("LIMIT") || t.contains(" LIMIT ")
    });
    if has_offset && !has_limit {
        // Report on the line containing OFFSET
        for (i, line) in upper_content.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with("OFFSET") || trimmed.contains(" OFFSET ") {
                issues.push(LintIssue {
                    line: i + 1,
                    message: "OFFSET without LIMIT has no effect".to_string(),
                });
                break;
            }
        }
    }

    issues
}
