// SPDX-License-Identifier: MPL-2.0
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
use vcltotal_parse::schema::*;
use vcltotal_parse::{certified_transition_level, to_wire, to_wire_op, to_wire_schema};

fn line(name: &str, s: &Statement) {
    let b = to_wire(s);
    let body = b.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
    println!("{name} = [{body}]");
}

fn line_op(name: &str, op: &VclOp) {
    let b = to_wire_op(op);
    let body = b.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
    println!("{name} = [{body}]");
}

// ── S2 VclOp fixtures (the regeneration oracle for WireConformance's
//    `goldenOp*`/`goldenT*` Refl proofs) ───────────────────────────────

/// `MERGE 'a' 'b' INTO 'c'` — distinct inputs, no evidence ⇒ admissible.
fn t_merge() -> Transition {
    Transition::Merge(
        SubjectRef("a".to_string()),
        SubjectRef("b".to_string()),
        SubjectRef("c".to_string()),
        None,
        SafetyLevel::InjectionProof,
    )
}

/// `NORMALISE 's-1' USER RESOLVE` — single subject, justified ⇒ admissible.
fn t_normalise() -> Transition {
    Transition::Normalise(
        SubjectRef("s-1".to_string()),
        RepairJustification::UserResolve,
        SafetyLevel::InjectionProof,
    )
}

fn line_schema(name: &str, s: &OctadSchema) {
    let b = to_wire_schema(s);
    let body = b.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
    println!("{name} = [{body}]");
}

/// Minimal P5c schema fixture: exercises empty + non-empty field
/// lists, all 8 modality slots in record order, bools, and a recursive
/// `VqlType` (`TList`) plus `TVector(Nat)`.
fn sch1() -> OctadSchema {
    let m = |modality, fields| ModalitySchema { modality, fields };
    OctadSchema {
        graph: m(
            Modality::Graph,
            vec![FieldDef {
                name: "id".to_string(),
                ty: VqlType::TString,
                nullable: true,
                indexed: false,
            }],
        ),
        vector: m(
            Modality::Vector,
            vec![FieldDef {
                name: "emb".to_string(),
                ty: VqlType::TVector(4),
                nullable: false,
                indexed: true,
            }],
        ),
        tensor: m(Modality::Tensor, vec![]),
        semantic: m(Modality::Semantic, vec![]),
        document: m(
            Modality::Document,
            vec![FieldDef {
                name: "tags".to_string(),
                ty: VqlType::TList(Box::new(VqlType::TString)),
                nullable: false,
                indexed: false,
            }],
        ),
        temporal: m(Modality::Temporal, vec![]),
        provenance: m(Modality::Provenance, vec![]),
        spatial: m(Modality::Spatial, vec![]),
    }
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
        verb: Verb::Select,
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
        verb: Verb::Select,
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
        verb: Verb::Select,
    }
}

#[test]
fn emit() {
    line("golden1", &f1());
    line("golden2", &f2());
    line("golden3", &f3());
    line_schema("goldenS1", &sch1());
    // P5c recompute-tier verdicts: the Rust decider's certified level
    // for each statement fixture against the S1 schema. The Idris
    // `WireConformance` Refl-proves the corpus `certifiedLevel` equals
    // these same ints on the same bytes — the runtime-TCB pin.
    println!("cl1 = {}", vcltotal_parse::certified_level(&f1(), &sch1()));
    println!("cl2 = {}", vcltotal_parse::certified_level(&f2(), &sch1()));
    println!("cl3 = {}", vcltotal_parse::certified_level(&f3(), &sch1()));
    // S2 VclOp golden bytes (magic VCLT) + transition verdict oracle.
    // `goldenOpQ1` = Query-wrapped f1 (the op stream around a statement);
    // `goldenT1` = the MERGE transition; `goldenT2` = the NORMALISE.
    line_op("goldenOpQ1", &VclOp::Query(Box::new(f1())));
    line_op("goldenT1", &VclOp::Transit(t_merge()));
    line_op("goldenT2", &VclOp::Transit(t_normalise()));
    // Transition recompute-tier verdicts (schema-independent for these
    // evidence-free fixtures): both admissible ⇒ InjectionProof = 4.
    println!("ctl1 = {}", certified_transition_level(&t_merge(), &sch1()));
    println!("ctl2 = {}", certified_transition_level(&t_normalise(), &sch1()));
}

/// Self-check: every fixture round-trips through the Rust codec, so the
/// emitted bytes are a faithful `to_wire` image (the Idris decoder is
/// then proven to agree on the same bytes).
#[test]
fn fixtures_roundtrip() {
    for s in [f1(), f2(), f3()] {
        assert_eq!(vcltotal_parse::from_wire(&to_wire(&s)).unwrap(), s);
    }
    assert_eq!(
        vcltotal_parse::from_wire_schema(&to_wire_schema(&sch1())).unwrap(),
        sch1()
    );
    // Recompute-tier verdicts must hold on the *decoded* bytes (the
    // exact domain the consumer runs), not just the in-memory value.
    let sc = vcltotal_parse::from_wire_schema(&to_wire_schema(&sch1())).unwrap();
    for (s, want) in [(f1(), 1_i64), (f2(), -1_i64), (f3(), 0_i64)] {
        let decoded = vcltotal_parse::from_wire(&to_wire(&s)).unwrap();
        assert_eq!(vcltotal_parse::certified_level(&decoded, &sc), want);
    }
    // S2: VclOp streams round-trip through the VCLT codec, and the
    // transition verdict holds on the *decoded* op (the gate's domain).
    for op in [
        VclOp::Query(Box::new(f1())),
        VclOp::Transit(t_merge()),
        VclOp::Transit(t_normalise()),
    ] {
        let decoded = vcltotal_parse::from_wire_op(&to_wire_op(&op)).unwrap();
        assert_eq!(decoded, op);
        if let VclOp::Transit(t) = decoded {
            assert_eq!(certified_transition_level(&t, &sc), 4);
        }
    }
}
