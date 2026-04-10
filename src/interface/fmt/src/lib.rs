#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! VCL-total Formatting Library
//!
//! Provides formatting capabilities for VCL-total query files.
//! Keywords are indented with two spaces for readability.

/// Format VCL-total content by indenting lines that start with recognised keywords.
///
/// Keywords recognised: SELECT, FROM, WHERE, GROUP, ORDER, HAVING, LIMIT.
/// Each keyword-leading line is prefixed with two spaces of indentation.
/// All lines are trimmed of leading/trailing whitespace before processing.
pub fn format_vqlut(content: &str) -> String {
    let mut formatted = String::new();
    let keywords = [
        "SELECT", "FROM", "WHERE", "GROUP", "ORDER", "HAVING", "LIMIT",
        "OFFSET", "EFFECTS", "PROOF", "CONSUME",
    ];

    for line in content.lines() {
        let trimmed = line.trim();
        if keywords.iter().any(|&kw| {
            trimmed.starts_with(kw)
                && trimmed
                    .as_bytes()
                    .get(kw.len())
                    .map_or(true, |&b| !b.is_ascii_alphanumeric() && b != b'_')
        }) {
            formatted.push_str("  ");
        }
        formatted.push_str(trimmed);
        formatted.push('\n');
    }

    formatted
}
