// SPDX-License-Identifier: PMPL-1.0-or-later

//! vcl-ut interface crate.
//!
//! Holds the seam between vcl-ut's query surface (owned locally in
//! `src/core/` Idris2 + this crate's Rust wrappers) and echidna's proof
//! surface (owned in the `echidna-core` crate).
//!
//! Downstream consumers (fmt, lint, lsp, dap, and the forthcoming
//! echidna-client) use this crate as their single import point for both
//! sides of the vcl-ut ↔ echidna interface.

/// Re-export echidna's canonical proof-surface types so callers don't need
/// a direct dep on `echidna-core`. Covers Term, Goal, ProofState, Tactic,
/// Hypothesis, Context, Theorem, Definition, Variable, Pattern,
/// TacticResult, and the TypeInfo decoration family.
pub use echidna_core::{core, types};
