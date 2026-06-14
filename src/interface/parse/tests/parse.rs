// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Totality / panic-freedom property for the trusted parser (P5a, #25).
//! The SPARK-grade claim is "no input panics; every failure is a typed
//! `ParseError`". `proptest` fails the run if any input panics, so a
//! green run over these strategies is machine evidence of that.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use proptest::prelude::*;
use vcltotal_parse::{parse, parse_op};

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4096))]

    /// Arbitrary UTF-8: parsing must terminate with Ok/Err, never panic.
    #[test]
    fn never_panics_on_arbitrary_text(s in ".*") {
        let _ = parse(&s);
    }

    /// Arbitrary bytes interpreted lossily — still no panic.
    #[test]
    fn never_panics_on_arbitrary_bytes(bytes in proptest::collection::vec(any::<u8>(), 0..512)) {
        let s = String::from_utf8_lossy(&bytes);
        let _ = parse(&s);
    }

    /// Token-salad from the real lexical alphabet: stresses the
    /// recursive-descent paths without panicking.
    #[test]
    fn never_panics_on_token_salad(
        toks in proptest::collection::vec(
            prop_oneof![
                Just("SELECT"), Just("FROM"), Just("WHERE"), Just("STORE"),
                Just("OCTAD"), Just("GRAPH.x"), Just("VECTOR.y"), Just("AND"),
                Just("OR"), Just("NOT"), Just("COUNT"), Just("("), Just(")"),
                Just("*"), Just(","), Just("="), Just(">="), Just("$1"),
                Just("'lit'"), Just("42"), Just("3.14"), Just(";"),
                Just("LIMIT"), Just("GROUP"), Just("BY"), Just("EFFECTS"),
            ],
            0..40,
        )
    ) {
        let s = toks.join(" ");
        let _ = parse(&s);
    }
}

#[test]
fn known_good_queries_parse() {
    let oks = [
        "SELECT * FROM STORE main",
        "SELECT GRAPH.a, VECTOR.b FROM OCTAD u WHERE GRAPH.a = $1",
        "SELECT COUNT(*) FROM HEXAD h GROUP BY GRAPH.k HAVING COUNT(*) > 2",
        "SELECT * FROM STORE s WHERE GRAPH.id IN (SELECT GRAPH.id FROM STORE t);",
        "SELECT SEMANTIC FROM FEDERATION 'pat-*' ORDER BY SEMANTIC.score DESC LIMIT 7",
    ];
    for q in oks {
        assert!(parse(q).is_ok(), "should parse: {q}");
    }
}

// ── Deep nesting must fail-closed (typed error), NOT overflow the stack ──
// Regression for the adversarial-review finding: the recursive-descent
// expression grammar (parens, NOT chains, sub-queries) is depth-guarded so
// an adversarial deeply-nested input returns a typed `ParseError`, never a
// SIGABRT process abort. The depth cap (256) is comfortably within the gate
// binary's main-thread stack; these witnesses run the parse on an
// 8-MiB-stack thread (representative of the deployed gate) because libtest's
// default *spawned* test threads are only ~2 MiB — too small to even reach
// the cap in an unoptimised build, which would mask the real contract.
fn parse_on_gate_stack<R: Send + 'static>(f: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the parse must not abort the thread")
}

#[test]
fn deep_parens_are_typed_error_not_overflow() {
    let msg = parse_on_gate_stack(|| {
        let depth = 100_000;
        let q = format!(
            "SELECT * FROM STORE s WHERE {}GRAPH.x = 1{}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        parse(&q).err().map(|e| e.msg)
    });
    assert_eq!(
        msg.as_deref().map(|m| m.contains("too deep")),
        Some(true),
        "deep parens must fail-closed with a typed error; got: {msg:?}"
    );
}

#[test]
fn deep_not_chain_is_typed_error_not_overflow() {
    let msg = parse_on_gate_stack(|| {
        let q = format!("SELECT * FROM STORE s WHERE {}GRAPH.x", "NOT ".repeat(100_000));
        parse(&q).err().map(|e| e.msg)
    });
    assert_eq!(
        msg.as_deref().map(|m| m.contains("too deep")),
        Some(true),
        "deep NOT chain must fail-closed; got: {msg:?}"
    );
}

#[test]
fn deep_transition_evidence_is_typed_error_not_overflow() {
    // The S2 transition WHERE-evidence path flows through the same grammar.
    let msg = parse_on_gate_stack(|| {
        let depth = 100_000;
        let q = format!(
            "MERGE 'a' 'b' INTO 'c' WHERE {}GRAPH.x = 1{}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        parse_op(&q).err().map(|e| e.msg)
    });
    assert_eq!(
        msg.as_deref().map(|m| m.contains("too deep")),
        Some(true),
        "deep transition evidence must fail-closed; got: {msg:?}"
    );
}

#[test]
fn fail_closed_on_unsupported_extensions() {
    // Honest: a typed error, never a silently-wrong AST.
    for q in [
        "SELECT * FROM STORE s PROOF ATTACHED",
        "SELECT * FROM STORE s AT VERSION = 3",
        "SELECT * FROM STORE s EPISTEMIC { AGENTS ENGINE }",
        "SELECT KNOWS ENGINE GRAPH.x FROM STORE s",
    ] {
        let err = parse(q).expect_err("must fail-closed");
        assert!(
            err.msg.contains("not yet supported") || err.msg.contains("fail-closed"),
            "expected fail-closed error for {q:?}, got {err}"
        );
    }
}
