// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! P5b cross-language conformance: the **regeneration oracle** for the
//! Idris-side `VclTotal.Interface.WireConformance` `Refl` proofs.
//!
//! These are the exact, byte-for-byte `to_wire` outputs the Idris total
//! decoder must reproduce structurally. Run:
//!
//! ```text
//! cargo test --manifest-path src/interface/parse/Cargo.toml --locked \
//!   --test conformance_emit -- --nocapture emit
//! ```
//!
//! and transcribe each `Fn = [..]` line into the corresponding
//! `goldenN` byte list in `src/interface/WireConformance.idr`. The
//! fixtures are deliberately chosen so the Idris equality is
//! *definitional* (`Refl`): no arbitrary `f64` (F3 uses 2.5, exactly
//! representable — bit-exact reconstruction is the Rust proptest's job,
//! `wire.rs::golden_bit_exact_floats`).

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use vcltotal_parse::ast::*;
use vcltotal_parse::to_wire;

fn line(name: &str, s: &Statement) {
    let b = to_wire(s);
    let body = b.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
    println!("{name} = [{body}]");
}

fn f1() -> Statement {
    Statement {
        select_items: vec![SelectItem::Star],
        source: Source::Store("main".to_string()),
        where_clause: None,
        group_by: vec![],
        having: None,
        order_by: vec![],
        limit: None,
        offset: None,
        proof_clause: None,
        effect_decl: None,
        version_const: None,
        linear_annot: None,
        epistemic_clause: None,
        requested_level: SafetyLevel::SchemaBound,
    }
}

fn f2() -> Statement {
    Statement {
        select_items: vec![
            SelectItem::Field(FieldRef {
                modality: Modality::Graph,
                field_name: "id".to_string(),
            }),
            SelectItem::Star,
        ],
        source: Source::Octad("uuid-1".to_string()),
        where_clause: Some(Expr::Compare(
            CompOp::Eq,
            Box::new(Expr::Field(FieldRef {
                modality: Modality::Vector,
                field_name: "x".to_string(),
            })),
            Box::new(Expr::Literal(Literal::Int(7))),
        )),
        group_by: vec![],
        having: None,
        order_by: vec![(
            FieldRef {
                modality: Modality::Temporal,
                field_name: "t".to_string(),
            },
            true,
        )],
        limit: Some(10),
        offset: None,
        proof_clause: Some(ProofClause::Witness("w".to_string())),
        effect_decl: Some(EffectDecl::ReadWrite),
        version_const: Some(VersionConstraint::AtLeast(3)),
        linear_annot: Some(LinearAnnotation::UseOnce),
        epistemic_clause: Some(EpistemicClause {
            agents: vec![Agent::Engine, Agent::Prover("lean4".to_string())],
            requirements: vec![EpistemicRequirement::Knows(
                Agent::Engine,
                Expr::Literal(Literal::Bool(true)),
            )],
        }),
        requested_level: SafetyLevel::EpistemicSafe,
    }
}

fn f3() -> Statement {
    Statement {
        select_items: vec![SelectItem::Star],
        source: Source::Store("s".to_string()),
        where_clause: Some(Expr::Literal(Literal::Float(2.5))),
        group_by: vec![],
        having: None,
        order_by: vec![],
        limit: None,
        offset: None,
        proof_clause: None,
        effect_decl: None,
        version_const: None,
        linear_annot: None,
        epistemic_clause: None,
        requested_level: SafetyLevel::ParseSafe,
    }
}

#[test]
fn emit() {
    line("golden1", &f1());
    line("golden2", &f2());
    line("golden3", &f3());
}

/// Self-check: every fixture round-trips through the Rust codec, so the
/// emitted bytes are a faithful `to_wire` image (the Idris decoder is
/// then proven to agree on the same bytes).
#[test]
fn fixtures_roundtrip() {
    for s in [f1(), f2(), f3()] {
        assert_eq!(vcltotal_parse::from_wire(&to_wire(&s)).unwrap(), s);
    }
}
