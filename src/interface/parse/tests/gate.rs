// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! vclt-gate conformance tests (contract §"Worked examples", v1).
//!
//! These tests drive the `decider::certified_level` path directly (no
//! subprocess) to verify the two worked fixtures in `docs/vclt-gate-contract.adoc`
//! and the gate-error / version-check paths.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects
)]

use vcltotal_parse::{
    ast::{Modality, Verb},
    certified_level, parse,
    schema::{FieldDef, ModalitySchema, OctadSchema, VqlType},
};

fn empty_schema() -> OctadSchema {
    let ms = |m: Modality| ModalitySchema {
        modality: m,
        fields: vec![],
    };
    OctadSchema {
        graph: ms(Modality::Graph),
        vector: ms(Modality::Vector),
        tensor: ms(Modality::Tensor),
        semantic: ms(Modality::Semantic),
        document: ms(Modality::Document),
        temporal: ms(Modality::Temporal),
        provenance: ms(Modality::Provenance),
        spatial: ms(Modality::Spatial),
    }
}

fn schema_with_graph_fields(fields: Vec<FieldDef>) -> OctadSchema {
    let mut s = empty_schema();
    s.graph = ModalitySchema {
        modality: Modality::Graph,
        fields,
    };
    s
}

// ── Fixture 1: Admitted ────────────────────────────────────────────────────
//
// Contract §"Worked examples" — Admitted (vclt-gate-contract.adoc:86):
//   ASSERT GRAPH.knows FROM HEXAD 'e-1' WHERE depth < 3 LIMIT 10
//   schema: graph.depth TInt non-null, graph.knows TOctad non-null
//   expected: admissible=true, certified_level=6, levels 1-6 all pass, exit 0.

#[test]
fn fixture_admitted_assert_with_limit() {
    let schema = schema_with_graph_fields(vec![
        FieldDef {
            name: "depth".to_string(),
            ty: VqlType::TInt,
            nullable: false,
            indexed: true,
        },
        FieldDef {
            name: "knows".to_string(),
            ty: VqlType::TOctad,
            nullable: false,
            indexed: true,
        },
    ]);
    // S1: the contract's worked example uses the ASSERT consonance verb, which
    // now parses as a verb tag over the relational body (previously this fixture
    // had to rewrite ASSERT->INSPECT because the parser could not parse ASSERT).
    // Field refs need MODALITY.name qualification; bare `depth` parses as
    // Expr::Param (schema-unresolved) — passes L1 vacuously.
    let stmt = parse("ASSERT GRAPH.knows FROM HEXAD 'e-1' WHERE depth < 3 LIMIT 10")
        .expect("fixture 1 must parse");
    assert_eq!(stmt.verb, Verb::Assert, "the ASSERT verb tag must be captured");
    let cert = certified_level(&stmt, &schema);
    assert_eq!(
        cert, 6,
        "fixture 1: certified_level must be 6 (CardinalitySafe)"
    );
    // admissible = cert == requested_level
    assert_eq!(stmt.requested_level as i64, 6);
}

// ── Fixture 2: Rejected (injection) ───────────────────────────────────────
//
// Contract §"Worked examples" — Rejected:
//   statement contains a raw string literal in WHERE ⟹ L4 InjectionProof fails.
//   expected: admissible=false, certified_level=-1, L4 status=fail, exit 1.

#[test]
fn fixture_injection_reject() {
    let schema = schema_with_graph_fields(vec![FieldDef {
        name: "name".to_string(),
        ty: VqlType::TString,
        nullable: false,
        indexed: true,
    }]);
    // Parameterised queries use $name; a raw string literal in WHERE fails L4.
    let stmt = parse("SELECT GRAPH.name FROM STORE main WHERE GRAPH.name = 'Robert'")
        .expect("fixture 2 must parse");
    let cert = certified_level(&stmt, &schema);
    assert_eq!(
        cert, -1,
        "fixture 2: certified_level must be -1 (InjectionProof fails)"
    );
}

// ── Gate-error path: unsupported schema_version ────────────────────────────

#[test]
fn reject_string_literal_in_where() {
    // Any string literal in WHERE must fail L4 regardless of schema.
    let s = parse("SELECT * FROM STORE s WHERE GRAPH.x = 'literal'").expect("parses");
    let cert = certified_level(&s, &empty_schema());
    assert_eq!(cert, -1);
}

// ── L1 SchemaBound: unknown field fails ───────────────────────────────────

#[test]
fn l1_fails_on_unknown_field() {
    // No schema — GRAPH.missing cannot resolve.
    let s = parse("SELECT GRAPH.missing FROM STORE s").expect("parses");
    let cert = certified_level(&s, &empty_schema());
    assert_eq!(
        cert, -1,
        "GRAPH.missing should fail SchemaBound against empty schema"
    );
}

// ── L6 CardinalitySafe: no LIMIT → fails at L6 ───────────────────────────

#[test]
fn l6_fails_without_limit() {
    let schema = schema_with_graph_fields(vec![FieldDef {
        name: "name".to_string(),
        ty: VqlType::TString,
        nullable: false,
        indexed: true,
    }]);
    // Use GRAPH.name which is in the schema (non-nullable TString).
    // $1 is a parameter (TAny), compatible with TString via TAny rule.
    let s = parse("SELECT GRAPH.name FROM STORE s WHERE GRAPH.name > $1").expect("parses");
    let cert = certified_level(&s, &schema);
    // InjectionProof (L4) is the requested level (WHERE present, no LIMIT).
    // L1-L4 should all pass. certified_level == 4 (not -1).
    assert_eq!(cert, 4, "without LIMIT, level stops at InjectionProof (4)");
}

// ── Parse error → certified_level irrelevant; parse itself must err ────────

#[test]
fn parse_error_on_empty_input() {
    assert!(parse("").is_err());
}

#[test]
fn parse_error_on_garbage() {
    assert!(parse("'); DROP TABLE --").is_err());
}

// ── S1: consonance-verb discriminant ────────────────────────────────────────
// The read verbs (SELECT/INSPECT/VERIFY) and the promoted mutating verbs
// (ASSERT/DECLARE/RETRACT) parse as a verb tag over the same relational body;
// MERGE/SPLIT/NORMALISE are deliberately fail-closed until their semantics (S2).
#[test]
fn s1_verb_tags_and_fail_closed() {
    let body = "GRAPH.knows FROM STORE main";
    for (kw, want) in [
        ("SELECT", Verb::Select),
        ("INSPECT", Verb::Inspect),
        ("VERIFY", Verb::Verify),
        ("ASSERT", Verb::Assert),
        ("DECLARE", Verb::Declare),
        ("RETRACT", Verb::Retract),
    ] {
        let stmt = parse(&format!("{kw} {body}"))
            .unwrap_or_else(|e| panic!("{kw} should parse: {e:?}"));
        assert_eq!(stmt.verb, want, "{kw} must carry the {want:?} tag");
    }
    for kw in ["MERGE", "SPLIT", "NORMALISE"] {
        assert!(
            parse(&format!("{kw} {body}")).is_err(),
            "{kw} must fail-closed (S2, multi-subject / result-less semantics)"
        );
    }
}
