// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//! VCL-total: 10-level type-safe query language for VeriSimDB
//!
//! This top-level crate re-exports the formatter and linter libraries
//! for use in integration tests and downstream consumers.

/// Re-export the VCL-total formatter.
pub use vcltotal_fmt as fmt;

/// Re-export the VCL-total linter.
pub use vcltotal_lint as lint;
