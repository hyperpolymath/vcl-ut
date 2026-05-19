// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! `vcltotal-parse` — P5a of issue #25 (reinforce the verified-corpus
//! boundary). A *trusted* `String -> Statement` parser for VCL-total,
//! held to a SPARK-grade posture so it can sit on the doubly-trusted
//! hypatia<->verisim path:
//!
//! * `#![forbid(unsafe_code)]` — no UB surface.
//! * No `unwrap`/`expect`/`panic`/`unreachable`/`todo`/`unimplemented`,
//!   no slice indexing, no unchecked arithmetic (`clippy::
//!   arithmetic_side_effects` denied; the only arithmetic is cursor
//!   `saturating_add`) — every failure is a typed
//!   [`parser::ParseError`]; the parser is **total**.
//! * The `proptest` panic-free invariant (tests/parse.rs, 4096 cases x
//!   3 strategies) is the runtime witness that no input reaches a panic.
//!
//! Its [`ast`] is a one-to-one mirror of `src/core/Grammar.idr` (the
//! type the proof corpus certifies) so the P5b C-ABI marshaller is a
//! structural map. The parser establishes *syntax only*; type
//! resolution and the L0–L10 safety decision remain the Idris2
//! certifier's job.

#![forbid(unsafe_code)]
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::unreachable,
    clippy::todo,
    clippy::unimplemented,
    clippy::exit
)]

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod schema;
pub mod wire;

pub use ast::Statement;
pub use parser::{parse, ParseError};
pub use schema::OctadSchema;
pub use wire::{from_wire, from_wire_schema, to_wire, to_wire_schema, WireError};

#[cfg(test)]
mod tests {
    // Test code may use the assertion/panic helpers the production
    // lint-set forbids; the SPARK-grade posture binds the library only.
    #![allow(
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::panic,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects
    )]
    use super::ast::*;
    use super::parse;

    #[test]
    fn minimal_select_from() {
        let s = parse("SELECT * FROM STORE main").expect("valid");
        assert_eq!(s.select_items, vec![SelectItem::Star]);
        assert_eq!(s.source, Source::Store("main".to_string()));
        assert_eq!(s.requested_level, SafetyLevel::SchemaBound);
    }

    #[test]
    fn field_where_param_is_injection_safe_level() {
        let s = parse("SELECT GRAPH.name FROM OCTAD x WHERE GRAPH.age > $1").expect("valid");
        assert_eq!(
            s.select_items,
            vec![SelectItem::Field(FieldRef {
                modality: Modality::Graph,
                field_name: "name".to_string(),
            })]
        );
        match s.where_clause {
            Some(Expr::Compare(CompOp::Gt, _, _)) => {}
            other => panic!("unexpected where: {other:?}"),
        }
        assert_eq!(s.requested_level, SafetyLevel::InjectionProof);
    }

    #[test]
    fn aggregate_and_clauses() {
        let s = parse(
            "SELECT COUNT(*) FROM HEXAD h \
             WHERE VECTOR.score >= 0.5 AND NOT DOCUMENT.deleted = TRUE \
             GROUP BY GRAPH.kind HAVING COUNT(*) > 3 \
             ORDER BY GRAPH.kind DESC LIMIT 10 OFFSET 5;",
        )
        .expect("valid");
        assert_eq!(s.limit, Some(10));
        assert_eq!(s.offset, Some(5));
        assert_eq!(s.group_by.len(), 1);
        assert!(s.having.is_some());
        assert_eq!(s.order_by.first().map(|(_, asc)| *asc), Some(false));
        // limit present, no higher feature -> CardinalitySafe.
        assert_eq!(s.requested_level, SafetyLevel::CardinalitySafe);
    }

    #[test]
    fn subquery_in_where() {
        let s = parse("SELECT * FROM STORE a WHERE GRAPH.id IN (SELECT GRAPH.id FROM STORE b)")
            .expect("valid");
        match s.where_clause {
            Some(Expr::Compare(CompOp::In, _, ref rhs)) => {
                assert!(matches!(**rhs, Expr::Subquery(_)));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn extension_clause_is_fail_closed_not_wrong() {
        let e = parse("SELECT * FROM STORE a EFFECTS { Read }").unwrap_err();
        assert!(e.msg.contains("EFFECTS"), "got: {e}");
        assert!(e.msg.contains("fail-closed"), "got: {e}");
    }

    #[test]
    fn garbage_is_an_error_never_a_panic() {
        assert!(parse("").is_err());
        assert!(parse("SELECT").is_err());
        assert!(parse("SELECT * FROM").is_err());
        assert!(parse("')) DROP everything --").is_err());
    }
}
