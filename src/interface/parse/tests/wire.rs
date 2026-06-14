// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! P5b (#25) wire-codec properties: the machine witnesses for
//! `WIRE-FORMAT.adoc`'s totality + bijection contract.
//!
//! * `roundtrip`: `from_wire(to_wire(s)) == s` over arbitrary
//!   `Statement`s (the codec is a bijection on the Rust AST mirror).
//! * `decoder_total_on_garbage`: `from_wire` never panics on arbitrary
//!   bytes — only `Ok`/`Err` (the trusted-boundary totality contract).
//! * `encoder_deterministic`: one canonical byte string per value.
//! * golden vectors incl. bit-exact non-finite float preservation.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use proptest::prelude::*;
use vcltotal_parse::ast::*;
use vcltotal_parse::{from_wire, from_wire_op, to_wire, to_wire_op};

fn modality() -> impl Strategy<Value = Modality> {
    prop_oneof![
        Just(Modality::Graph),
        Just(Modality::Vector),
        Just(Modality::Tensor),
        Just(Modality::Semantic),
        Just(Modality::Document),
        Just(Modality::Temporal),
        Just(Modality::Provenance),
        Just(Modality::Spatial),
    ]
}

fn agent() -> impl Strategy<Value = Agent> {
    prop_oneof![
        Just(Agent::Engine),
        ".*".prop_map(Agent::Prover),
        Just(Agent::Validator),
        ".*".prop_map(Agent::User),
        Just(Agent::Federation),
    ]
}

fn fieldref() -> impl Strategy<Value = FieldRef> {
    (modality(), ".*").prop_map(|(modality, field_name)| FieldRef {
        modality,
        field_name,
    })
}

// Finite floats only: the round-trip oracle is `PartialEq`, and
// `NaN != NaN`. Bit-exact preservation of non-finite values (incl. inf)
// is pinned separately by `golden_bit_exact_floats`.
fn finite_f64() -> impl Strategy<Value = f64> {
    prop_oneof![
        Just(0.0_f64),
        Just(-0.0_f64),
        (-1e9_f64..1e9_f64),
        Just(f64::MIN),
        Just(f64::MAX),
    ]
}

fn literal() -> impl Strategy<Value = Literal> {
    prop_oneof![
        ".*".prop_map(Literal::Str),
        any::<i64>().prop_map(Literal::Int),
        finite_f64().prop_map(Literal::Float),
        any::<bool>().prop_map(Literal::Bool),
        Just(Literal::Null),
        proptest::collection::vec(finite_f64(), 0..4).prop_map(Literal::Vector),
    ]
}

fn compop() -> impl Strategy<Value = CompOp> {
    prop_oneof![
        Just(CompOp::Eq),
        Just(CompOp::NotEq),
        Just(CompOp::Lt),
        Just(CompOp::Gt),
        Just(CompOp::LtEq),
        Just(CompOp::GtEq),
        Just(CompOp::Like),
        Just(CompOp::In),
    ]
}
fn aggfunc() -> impl Strategy<Value = AggFunc> {
    prop_oneof![
        Just(AggFunc::Count),
        Just(AggFunc::Sum),
        Just(AggFunc::Avg),
        Just(AggFunc::Min),
        Just(AggFunc::Max),
    ]
}
fn epiop() -> impl Strategy<Value = EpistemicOp> {
    prop_oneof![
        Just(EpistemicOp::Knows),
        Just(EpistemicOp::Believes),
        Just(EpistemicOp::CommonKnowledge),
    ]
}

/// A bounded, non-recursive statement for embedding inside `Subquery`
/// (no WHERE/HAVING/subquery) — keeps the generated tree finite.
fn leaf_stmt() -> impl Strategy<Value = Statement> {
    (
        proptest::collection::vec(
            prop_oneof![
                fieldref().prop_map(SelectItem::Field),
                modality().prop_map(SelectItem::Modality),
                Just(SelectItem::Star),
            ],
            1..3,
        ),
        prop_oneof![".*".prop_map(Source::Octad), ".*".prop_map(Source::Store)],
    )
        .prop_map(|(select_items, source)| Statement {
            select_items,
            source,
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
            requested_level: SafetyLevel::ParseSafe,
            verb: Verb::Select,
        })
}

fn expr() -> impl Strategy<Value = Expr> {
    let leaf = prop_oneof![
        fieldref().prop_map(Expr::Field),
        literal().prop_map(Expr::Literal),
        ".*".prop_map(Expr::Param),
        Just(Expr::Star),
        leaf_stmt().prop_map(|s| Expr::Subquery(Box::new(s))),
        (epiop(), agent(), literal()).prop_map(|(o, a, l)| Expr::Epistemic(
            o,
            a,
            Box::new(Expr::Literal(l))
        )),
    ];
    leaf.prop_recursive(4, 32, 3, |inner| {
        prop_oneof![
            (compop(), inner.clone(), inner.clone()).prop_map(|(c, a, b)| Expr::Compare(
                c,
                Box::new(a),
                Box::new(b)
            )),
            (
                prop_oneof![Just(LogicOp::And), Just(LogicOp::Or), Just(LogicOp::Not)],
                inner.clone(),
                proptest::option::of(inner.clone()),
            )
                .prop_map(|(l, a, b)| Expr::Logic(l, Box::new(a), b.map(Box::new))),
            (aggfunc(), inner.clone()).prop_map(|(a, e)| Expr::Aggregate(a, Box::new(e))),
            (agent(), inner.clone(), inner).prop_map(|(ag, p, b)| Expr::Announce(
                ag,
                Box::new(p),
                Box::new(b)
            )),
        ]
    })
}

fn statement() -> impl Strategy<Value = Statement> {
    let select = proptest::collection::vec(
        prop_oneof![
            fieldref().prop_map(SelectItem::Field),
            modality().prop_map(SelectItem::Modality),
            (aggfunc(), expr()).prop_map(|(a, e)| SelectItem::Aggregate(a, e)),
            Just(SelectItem::Star),
        ],
        1..4,
    );
    let source = prop_oneof![
        ".*".prop_map(Source::Octad),
        ".*".prop_map(Source::Federation),
        ".*".prop_map(Source::Store),
    ];
    let safety = prop_oneof![
        Just(SafetyLevel::ParseSafe),
        Just(SafetyLevel::InjectionProof),
        Just(SafetyLevel::EpistemicSafe),
    ];
    // Group into <=12-tuples for prop_map, then assemble.
    let core = (
        select,
        source,
        proptest::option::of(expr()),
        proptest::collection::vec(fieldref(), 0..3),
        proptest::option::of(expr()),
        proptest::collection::vec((fieldref(), any::<bool>()), 0..3),
        proptest::option::of(any::<u64>()),
        proptest::option::of(any::<u64>()),
    );
    let ext = (
        proptest::option::of(prop_oneof![
            Just(ProofClause::Attached),
            ".*".prop_map(ProofClause::Witness),
        ]),
        proptest::option::of(prop_oneof![
            Just(EffectDecl::Read),
            Just(EffectDecl::Write),
            Just(EffectDecl::ReadWrite),
            Just(EffectDecl::Consume),
        ]),
        proptest::option::of(prop_oneof![
            Just(VersionConstraint::Latest),
            any::<u64>().prop_map(VersionConstraint::AtLeast),
            (any::<u64>(), any::<u64>()).prop_map(|(a, b)| VersionConstraint::Range(a, b)),
        ]),
        proptest::option::of(prop_oneof![
            Just(LinearAnnotation::Unlimited),
            Just(LinearAnnotation::UseOnce),
            any::<u64>().prop_map(LinearAnnotation::Bounded),
        ]),
        proptest::option::of(
            (
                proptest::collection::vec(agent(), 0..3),
                proptest::collection::vec(
                    prop_oneof![
                        (agent(), literal())
                            .prop_map(|(a, l)| EpistemicRequirement::Knows(a, Expr::Literal(l))),
                        literal().prop_map(|l| EpistemicRequirement::Common(Expr::Literal(l))),
                    ],
                    0..3,
                ),
            )
                .prop_map(|(agents, requirements)| EpistemicClause {
                    agents,
                    requirements,
                }),
        ),
        safety,
    );
    (core, ext).prop_map(|(c, e)| Statement {
        select_items: c.0,
        source: c.1,
        where_clause: c.2,
        group_by: c.3,
        having: c.4,
        order_by: c.5,
        limit: c.6,
        offset: c.7,
        proof_clause: e.0,
        effect_decl: e.1,
        version_const: e.2,
        linear_annot: e.3,
        epistemic_clause: e.4,
        requested_level: e.5,
        verb: Verb::Select,
    })
}

// ── S2: VclOp (Query | Transit) strategies ───────────────────────────

fn subject() -> impl Strategy<Value = SubjectRef> {
    ".*".prop_map(SubjectRef)
}

fn repair() -> impl Strategy<Value = RepairJustification> {
    prop_oneof![
        modality().prop_map(RepairJustification::FromAuthoritative),
        Just(RepairJustification::MergeModalities),
        Just(RepairJustification::UserResolve),
    ]
}

fn transition() -> impl Strategy<Value = Transition> {
    let lvl = prop_oneof![
        Just(SafetyLevel::ParseSafe),
        Just(SafetyLevel::InjectionProof),
    ];
    prop_oneof![
        (
            subject(),
            subject(),
            subject(),
            proptest::option::of(expr()),
            lvl.clone()
        )
            .prop_map(|(a, b, c, ev, l)| Transition::Merge(a, b, c, ev, l)),
        (
            subject(),
            subject(),
            subject(),
            proptest::option::of(expr()),
            lvl.clone()
        )
            .prop_map(|(a, b, c, ev, l)| Transition::Split(a, b, c, ev, l)),
        (subject(), repair(), lvl).prop_map(|(s, r, l)| Transition::Normalise(s, r, l)),
    ]
}

fn vclop() -> impl Strategy<Value = VclOp> {
    prop_oneof![
        statement().prop_map(|s| VclOp::Query(Box::new(s))),
        transition().prop_map(VclOp::Transit),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2048))]

    /// The codec is a bijection on the Rust AST mirror.
    #[test]
    fn roundtrip(s in statement()) {
        let bytes = to_wire(&s);
        let back = from_wire(&bytes).expect("decode of own encoding must succeed");
        prop_assert_eq!(back, s);
    }

    /// The VCLT op codec is a bijection on the `VclOp` mirror.
    #[test]
    fn op_roundtrip(op in vclop()) {
        let bytes = to_wire_op(&op);
        let back = from_wire_op(&bytes).expect("decode of own op encoding must succeed");
        prop_assert_eq!(back, op);
    }

    /// Totality: arbitrary bytes never panic the op decoder.
    #[test]
    fn op_decoder_total_on_garbage(bytes in proptest::collection::vec(any::<u8>(), 0..2048)) {
        let _ = from_wire_op(&bytes);
    }

    /// Totality even with a valid VCLT header followed by garbage.
    #[test]
    fn op_decoder_total_with_valid_header(tail in proptest::collection::vec(any::<u8>(), 0..512)) {
        let mut v = b"VCLT".to_vec();
        v.extend_from_slice(&1u16.to_le_bytes());
        v.extend_from_slice(&tail);
        let _ = from_wire_op(&v);
    }

    /// Encoding is canonical/deterministic.
    #[test]
    fn encoder_deterministic(s in statement()) {
        prop_assert_eq!(to_wire(&s), to_wire(&s));
    }

    /// Totality: arbitrary bytes never panic the decoder.
    #[test]
    fn decoder_total_on_garbage(bytes in proptest::collection::vec(any::<u8>(), 0..2048)) {
        let _ = from_wire(&bytes);
    }

    /// Totality even with a valid header followed by garbage.
    #[test]
    fn decoder_total_with_valid_header(tail in proptest::collection::vec(any::<u8>(), 0..512)) {
        let mut v = b"VCLW".to_vec();
        v.extend_from_slice(&1u16.to_le_bytes());
        v.extend_from_slice(&tail);
        let _ = from_wire(&v);
    }
}

#[test]
fn golden_minimal() {
    let s = Statement {
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
    };
    let b = to_wire(&s);
    assert_eq!(&b[0..4], b"VCLW");
    assert_eq!(from_wire(&b).unwrap(), s);
}

#[test]
fn golden_op_transitions() {
    // MERGE 'a' 'b' INTO 'c', no evidence, InjectionProof — the exact bytes
    // the Idris `WireConformance.goldenT1` Refl decodes (magic VCLT).
    let merge = VclOp::Transit(Transition::Merge(
        SubjectRef("a".to_string()),
        SubjectRef("b".to_string()),
        SubjectRef("c".to_string()),
        None,
        SafetyLevel::InjectionProof,
    ));
    let b = to_wire_op(&merge);
    assert_eq!(&b[0..4], b"VCLT");
    assert_eq!(
        b,
        vec![86, 67, 76, 84, 1, 0, 1, 0, 1, 0, 0, 0, 97, 1, 0, 0, 0, 98, 1, 0, 0, 0, 99, 0, 4]
    );
    assert_eq!(from_wire_op(&b).unwrap(), merge);

    // NORMALISE 's-1' USER RESOLVE — `WireConformance.goldenT2`.
    let norm = VclOp::Transit(Transition::Normalise(
        SubjectRef("s-1".to_string()),
        RepairJustification::UserResolve,
        SafetyLevel::InjectionProof,
    ));
    let nb = to_wire_op(&norm);
    assert_eq!(
        nb,
        vec![86, 67, 76, 84, 1, 0, 1, 2, 3, 0, 0, 0, 115, 45, 49, 2, 4]
    );
    assert_eq!(from_wire_op(&nb).unwrap(), norm);

    // A VCLW (statement) stream must NOT decode as a VCLT op — hard BadMagic.
    let stmt_bytes = to_wire(&mk_float_stmt(1.0));
    assert!(from_wire_op(&stmt_bytes).is_err());
}

#[test]
fn golden_bit_exact_floats() {
    // Non-finite floats round-trip bit-exactly (codec encodes
    // f64::to_bits). inf compares equal under PartialEq; NaN does not,
    // so assert NaN by bits, others structurally.
    for f in [f64::INFINITY, f64::NEG_INFINITY, 12_345.678_901_f64] {
        let s = mk_float_stmt(f);
        assert_eq!(from_wire(&to_wire(&s)).unwrap(), s);
    }
    let nan = mk_float_stmt(f64::NAN);
    let back = from_wire(&to_wire(&nan)).unwrap();
    match (&back.where_clause, &nan.where_clause) {
        (Some(Expr::Literal(Literal::Float(a))), Some(Expr::Literal(Literal::Float(b)))) => {
            assert_eq!(a.to_bits(), b.to_bits(), "NaN must round-trip bit-exactly");
        }
        _ => panic!("shape changed"),
    }
}

fn mk_float_stmt(f: f64) -> Statement {
    Statement {
        select_items: vec![SelectItem::Star],
        source: Source::Store("s".to_string()),
        where_clause: Some(Expr::Literal(Literal::Float(f))),
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
