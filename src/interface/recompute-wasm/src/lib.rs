// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! P5c (#25) — the recompute-PCC tier's `wasm32` entry point.
//!
//! ROLE (see `VERIFICATION-STANCE.adoc`'s two-tier boundary model).
//! Under the locked recompute design, the consumer is shipped this
//! wasm module + the wire bytes of a `(Statement, OctadSchema)` + the
//! producer's claimed safety level. The consumer **re-runs the
//! certified decision** here and compares. The guarantee is NOT the
//! wasm's type system: it is (a) the corpus proof `checkLevelNSound`
//! (machine-checked once, offline-re-checkable with idris2), and (b)
//! the cross-language conformance pin (`tests/conformance_emit.rs` ⇄
//! `WireConformance`) that `vcltotal_parse::certified_level` is a
//! faithful image of the corpus decision. This crate adds only the
//! host/guest memory ABI; it introduces no decision logic.
//!
//! Plain `wasm32-unknown-unknown` is *sufficient* for this argument:
//! nothing structured crosses the boundary that needs type-preservation
//! — opaque wire bytes go in, an `i64` verdict comes out, and the
//! decoder+decider run *inside* the module on those bytes. AffineScript
//! dependent/affine typing was load-bearing only for the *rejected*
//! proof-term-transport tier.
//!
//! Why NOT `affinescriptiser` here (disclosed, not an oversight). The
//! estate's Rust→typed-wasm wrapper is resource-oriented: it
//! *structurally requires* at least one `[[resources]]` entry
//! (allocator/deallocator/affinity) and exists to prove at-most-once
//! resource use. This entry is a **pure total verdict function** — it
//! owns no file descriptors, sockets, GPU buffers or linear handles,
//! so there is nothing for the affine checker to track; declaring a
//! fake resource purely to satisfy the tool would be exactly the kind
//! of cargo-culting the estate verification-honesty doctrine forbids.
//! (Independently, affinescriptiser's own wasm backend is
//! Phase-2-pending.) The recompute security argument does not need it:
//! soundness is the corpus proof, faithfulness is the conformance pin,
//! and the wasm is a deterministic `cargo build` of the pinned source.
//! See `src/interface/recompute-wasm/AFFINESCRIPTISER-NA.adoc`.
//!
//! UNSAFE POLICY. All decision/decoding logic lives in the
//! `#![forbid(unsafe_code)]` `vcltotal-parse` crate. The ONLY `unsafe`
//! in the entire recompute path is the small, audited host/guest
//! memory-ABI block below — which *is* the declared trust boundary
//! (the host is trusted to pass valid `(ptr, len)` into linear
//! memory). Every byte of judgement remains in the verified-posture
//! crate.
//!
//! FAIL-CLOSED. Any malformed wire input (`WireError`) yields `-1`
//! (Reject) — never a fabricated level. `certified_level` itself
//! returns `-1` when any required level is not established. So the
//! only non-negative result is a genuinely recomputed certified level.

#![deny(clippy::undocumented_unsafe_blocks)]

use core::slice;
use vcltotal_parse::{certified_level, from_wire, from_wire_schema};

/// Allocate `len` bytes of guest linear memory and return a pointer the
/// host can write wire bytes into. Pair with [`vcl_dealloc`].
///
/// # Safety
/// Caller (the host) must later pass the returned pointer and the same
/// `len` to [`vcl_dealloc`] exactly once, and must not retain it after.
#[no_mangle]
pub extern "C" fn vcl_alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len);
    let ptr = buf.as_mut_ptr();
    core::mem::forget(buf);
    ptr
}

/// Free a buffer previously returned by [`vcl_alloc`].
///
/// # Safety
/// `ptr`/`len` must be exactly a pair returned by one prior
/// [`vcl_alloc`] call, not yet freed.
#[no_mangle]
pub unsafe extern "C" fn vcl_dealloc(ptr: *mut u8, len: usize) {
    if !ptr.is_null() && len != 0 {
        // SAFETY: by this function's documented contract `ptr`/`len`
        // are exactly a prior `vcl_alloc` pair (capacity == len, never
        // freed). Reconstituting and dropping the `Vec` frees it.
        unsafe {
            drop(Vec::from_raw_parts(ptr, 0, len));
        }
    }
}

/// Recompute the certified safety level of a wire-encoded
/// `(Statement, OctadSchema)`.
///
/// Returns the certified level (`0..=10`) iff every required level is
/// re-established by the faithful in-corpus-image decider; `-1`
/// (Reject) on any decode failure or any unmet level — fail-closed,
/// never a fabricated level.
///
/// # Safety
/// `stmt_ptr`/`stmt_len` and `schema_ptr`/`schema_len` must each
/// describe an initialised, readable byte range in guest linear memory
/// (typically buffers from [`vcl_alloc`] the host filled). This is the
/// declared host↔guest trust boundary.
#[no_mangle]
pub unsafe extern "C" fn vcl_recompute(
    stmt_ptr: *const u8,
    stmt_len: usize,
    schema_ptr: *const u8,
    schema_len: usize,
) -> i64 {
    if stmt_ptr.is_null() || schema_ptr.is_null() {
        return -1;
    }
    // SAFETY: the *only* unsafe in the recompute path. By this
    // function's documented ABI contract the two (ptr, len) pairs are
    // valid initialised ranges in guest linear memory. We immediately
    // narrow to shared slices and hand them to the
    // `#![forbid(unsafe_code)]` decoder; no raw pointer escapes.
    let (stmt_bytes, schema_bytes) = unsafe {
        (
            slice::from_raw_parts(stmt_ptr, stmt_len),
            slice::from_raw_parts(schema_ptr, schema_len),
        )
    };
    match (from_wire(stmt_bytes), from_wire_schema(schema_bytes)) {
        (Ok(stmt), Ok(schema)) => certified_level(&stmt, &schema),
        _ => -1,
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use super::*;
    use vcltotal_parse::{to_wire, to_wire_schema};

    // The native-target faithfulness pin is in
    // `vcltotal-parse`'s conformance harness (Rust `certified_level`
    // == corpus on shared bytes). The wasm artefact is `cargo build`
    // of that *same* source, so the verdict is identical by
    // construction (pure, total, deterministic integer logic — no
    // platform-dependent behaviour). This test re-asserts the
    // fail-closed boundary contract through the actual entry on the
    // host target.
    fn rt(stmt: &[u8], schema: &[u8]) -> i64 {
        // SAFETY: valid slices from owned Vecs (test only).
        unsafe { vcl_recompute(stmt.as_ptr(), stmt.len(), schema.as_ptr(), schema.len()) }
    }

    #[test]
    fn garbage_is_fail_closed_not_a_level() {
        assert_eq!(rt(b"", b""), -1);
        assert_eq!(rt(b"not-vclw", b"not-vcls"), -1);
        assert_eq!(rt(&[0xff; 64], &[0xff; 64]), -1);
    }

    #[test]
    fn null_pointers_reject() {
        // SAFETY: deliberately passing null — the entry checks for it.
        let r = unsafe { vcl_recompute(core::ptr::null(), 0, core::ptr::null(), 0) };
        assert_eq!(r, -1);
    }

    #[test]
    fn well_formed_roundtrips_through_the_boundary() {
        // Minimal valid Statement (SELECT * FROM STORE "s",
        // requestedLevel ParseSafe) + empty-ish schema ⇒ level 0
        // (ParseSafe gate is unconditional).
        use vcltotal_parse::ast::*;
        use vcltotal_parse::schema::*;
        let s = Statement {
            select_items: vec![SelectItem::Star],
            source: Source::Store("s".to_string()),
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
        };
        let m = |modality, fields| ModalitySchema { modality, fields };
        let sc = OctadSchema {
            graph: m(Modality::Graph, vec![]),
            vector: m(Modality::Vector, vec![]),
            tensor: m(Modality::Tensor, vec![]),
            semantic: m(Modality::Semantic, vec![]),
            document: m(Modality::Document, vec![]),
            temporal: m(Modality::Temporal, vec![]),
            provenance: m(Modality::Provenance, vec![]),
            spatial: m(Modality::Spatial, vec![]),
        };
        assert_eq!(rt(&to_wire(&s), &to_wire_schema(&sc)), 0);
    }
}
