// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! P5d (#25) — **Tier-2: C-ABI trusted-certifier attestation
//! (FALLBACK).**
//!
//! See `verification/proofs/VERIFICATION-STANCE.adoc`'s canonical
//! two-tier boundary model. Tier-1 (recompute-PCC over `wasm32`,
//! `src/interface/recompute-wasm`) is the achieved tier: the consumer
//! re-validates. Tier-2 — *this crate* — is the explicit **weaker
//! fallback** for consumers that cannot run the Tier-1 wasm. A C ABI
//! erases types to machine words, so it cannot carry a re-checkable
//! dependent proof; the honest ceiling there is *trusted-certifier
//! attestation*: the consumer **trusts the certifier that minted the
//! token**, but the token is *unforgeable* and *bound* to the exact
//! `(query, schema, level)` it attests, so it cannot be forged,
//! transplanted onto a different query/schema, or have its level
//! escalated.
//!
//! TRUST MODEL (stated, not hidden). The consumer trusts: (a) the
//! certifier's Ed25519 private key is held only by a genuine
//! certifier; (b) that certifier ran the conformance-pinned
//! `vcltotal_parse::certified_level` (the same faithful image of the
//! corpus decision Tier-1 uses) before signing. This is strictly
//! weaker than Tier-1 (which needs neither (a) nor (b) — it
//! recomputes). It is *not* a re-checkable proof and does not pretend
//! to be one.
//!
//! TOKEN. Ed25519 signature over
//! `DOMAIN ‖ sha256(stmt_wire) ‖ sha256(schema_wire) ‖ level`
//! (`DOMAIN` is a fixed protocol/version tag — domain separation, so a
//! signature here can never be replayed as any other protocol's). The
//! level is `vcltotal_parse::certified_level` over the *decoded* wire;
//! it is signed iff it is `>= 0`. **Fail-closed:** a Reject (`-1`) or
//! any decode failure yields *no token* — never a signed level the
//! certifier did not establish.
//!
//! UNSAFE POLICY. All decode/decision logic is in the
//! `#![forbid(unsafe_code)]` `vcltotal-parse` crate; signing is the
//! audited `ed25519-dalek`. The only `unsafe` is one documented
//! host/guest C-ABI memory block in [`vclut_rs_verify`] — the declared
//! trust boundary the Zig shim links against.

#![deny(clippy::undocumented_unsafe_blocks)]

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use sha2::{Digest, Sha256};
use vcltotal_parse::{certified_level, from_wire, from_wire_schema};

/// Protocol + version domain-separation tag. Bump on any wire/format
/// change so old signatures cannot be reinterpreted.
pub const DOMAIN: &[u8; 16] = b"VCLT-ATTEST-v1\0\0";

/// A minted attestation: the certified level and the detached Ed25519
/// signature over `DOMAIN ‖ sha256(stmt) ‖ sha256(schema) ‖ level`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Attestation {
    pub level: u8,
    pub sig: [u8; 64],
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().into()
}

/// The exact bytes signed/verified. `level` is `0..=10`.
fn signed_message(stmt_wire: &[u8], schema_wire: &[u8], level: u8) -> [u8; 81] {
    let mut m = [0u8; 81];
    m[..16].copy_from_slice(DOMAIN);
    m[16..48].copy_from_slice(&sha256(stmt_wire));
    m[48..80].copy_from_slice(&sha256(schema_wire));
    m[80] = level;
    m
}

/// Mint an attestation for a wire-encoded `(Statement, OctadSchema)`.
///
/// Decodes both, runs the conformance-pinned
/// `vcltotal_parse::certified_level`, and signs **iff** the level is
/// `>= 0`. Returns `None` (fail-closed) on any decode failure or a
/// Reject — never a token for a level the certifier did not establish.
pub fn mint(stmt_wire: &[u8], schema_wire: &[u8], sk: &SigningKey) -> Option<Attestation> {
    let stmt = from_wire(stmt_wire).ok()?;
    let schema = from_wire_schema(schema_wire).ok()?;
    let lvl = certified_level(&stmt, &schema);
    if !(0..=10).contains(&lvl) {
        return None;
    }
    let level = u8::try_from(lvl).ok()?;
    let sig = sk.sign(&signed_message(stmt_wire, schema_wire, level));
    Some(Attestation {
        level,
        sig: sig.to_bytes(),
    })
}

/// Verify an attestation against the certifier's public key.
///
/// Recomputes the bound message from the wire bytes the consumer holds
/// together with the attested level, and checks the signature. Returns
/// `Some(level)` iff the token is a genuine certifier signature bound
/// to *these exact* `(stmt_wire, schema_wire, level)` — so a tampered
/// query, schema, level, or signature, or a wrong key, all reject.
/// Does **not** re-run the decider (that is Tier-1's job; Tier-2 trusts
/// the certifier — by construction of a C ABI).
pub fn verify(
    stmt_wire: &[u8],
    schema_wire: &[u8],
    att: &Attestation,
    vk: &VerifyingKey,
) -> Option<u8> {
    if att.level > 10 {
        return None;
    }
    let sig = Signature::from_bytes(&att.sig);
    let msg = signed_message(stmt_wire, schema_wire, att.level);
    vk.verify(&msg, &sig).ok().map(|()| att.level)
}

// ── C-ABI: the `vclut_rs_verify` backend the Zig shim links ──────────

/// `vclut_rs_verify` — the real backend declared (OWED) by
/// `ffi/zig/src/lib.zig`. Decodes the wire `(Statement, OctadSchema)`,
/// mints an attestation, and on success writes `[level:1][sig:64]` (65
/// bytes) into `out` and returns the level (`0..=10`). Returns `-1`
/// (Reject) — writing nothing — on any decode failure, a Reject level,
/// a null pointer, or `out_cap < 65`. Fail-closed: never a token for an
/// unestablished level.
///
/// # Safety
/// `stmt_ptr/stmt_len`, `schema_ptr/schema_len`, `sk_ptr` (32 bytes),
/// and `out_ptr/out_cap` must each describe valid, readable/writable
/// ranges. This is the declared host↔guest trust boundary the Zig shim
/// owns.
#[no_mangle]
pub unsafe extern "C" fn vclut_rs_verify(
    stmt_ptr: *const u8,
    stmt_len: usize,
    schema_ptr: *const u8,
    schema_len: usize,
    sk_ptr: *const u8,
    out_ptr: *mut u8,
    out_cap: usize,
) -> i64 {
    if stmt_ptr.is_null()
        || schema_ptr.is_null()
        || sk_ptr.is_null()
        || out_ptr.is_null()
        || out_cap < 65
    {
        return -1;
    }
    // SAFETY: the only unsafe in the path. By this function's
    // documented ABI contract the four ranges are valid; we narrow to
    // slices immediately and hand the data to the
    // `#![forbid(unsafe_code)]` decoder + audited ed25519-dalek. No raw
    // pointer escapes; `out` is written only on the success path.
    let (stmt_bytes, schema_bytes, sk_bytes) = unsafe {
        (
            core::slice::from_raw_parts(stmt_ptr, stmt_len),
            core::slice::from_raw_parts(schema_ptr, schema_len),
            core::slice::from_raw_parts(sk_ptr, 32),
        )
    };
    let sk_arr = match <[u8; 32]>::try_from(sk_bytes) {
        Ok(a) => a,
        Err(_) => return -1,
    };
    let sk = SigningKey::from_bytes(&sk_arr);
    match mint(stmt_bytes, schema_bytes, &sk) {
        Some(att) => {
            // SAFETY: out_cap >= 65 checked above; out_ptr non-null.
            // Write exactly [level:1][sig:64].
            let out = unsafe { core::slice::from_raw_parts_mut(out_ptr, 65) };
            out[0] = att.level;
            out[1..65].copy_from_slice(&att.sig);
            i64::from(att.level)
        }
        None => -1,
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
    use super::*;
    use vcltotal_parse::ast::*;
    use vcltotal_parse::schema::*;
    use vcltotal_parse::{to_wire, to_wire_schema};

    fn key() -> SigningKey {
        // Deterministic test key (NOT a real certifier key — real key
        // provisioning is deployment, via the estate token vault).
        SigningKey::from_bytes(&[7u8; 32])
    }

    fn empty_schema() -> OctadSchema {
        let m = |modality, fields| ModalitySchema { modality, fields };
        OctadSchema {
            graph: m(Modality::Graph, vec![]),
            vector: m(Modality::Vector, vec![]),
            tensor: m(Modality::Tensor, vec![]),
            semantic: m(Modality::Semantic, vec![]),
            document: m(Modality::Document, vec![]),
            temporal: m(Modality::Temporal, vec![]),
            provenance: m(Modality::Provenance, vec![]),
            spatial: m(Modality::Spatial, vec![]),
        }
    }

    fn parse_safe_stmt() -> Statement {
        Statement {
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
        }
    }

    #[test]
    fn roundtrip_mint_then_verify() {
        let sk = key();
        let vk = sk.verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let att = mint(&sw, &cw, &sk).expect("ParseSafe ⇒ level 0, mintable");
        assert_eq!(att.level, 0);
        assert_eq!(verify(&sw, &cw, &att, &vk), Some(0));
    }

    #[test]
    fn tampered_query_rejects() {
        let sk = key();
        let vk = sk.verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let att = mint(&sw, &cw, &sk).unwrap();
        let mut bad = sw.clone();
        *bad.last_mut().unwrap() ^= 0x01; // flip the requested-level byte
        assert_eq!(verify(&bad, &cw, &att, &vk), None);
    }

    #[test]
    fn tampered_schema_rejects() {
        let sk = key();
        let vk = sk.verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let att = mint(&sw, &cw, &sk).unwrap();
        let mut badc = cw.clone();
        badc[6] ^= 0x01;
        assert_eq!(verify(&sw, &badc, &att, &vk), None);
    }

    #[test]
    fn escalated_level_rejects() {
        let sk = key();
        let vk = sk.verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let mut att = mint(&sw, &cw, &sk).unwrap();
        att.level = 10; // attacker bumps the claimed level
        assert_eq!(verify(&sw, &cw, &att, &vk), None);
    }

    #[test]
    fn wrong_key_rejects() {
        let sk = key();
        let other = SigningKey::from_bytes(&[9u8; 32]).verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let att = mint(&sw, &cw, &sk).unwrap();
        assert_eq!(verify(&sw, &cw, &att, &other), None);
    }

    #[test]
    fn flipped_signature_rejects() {
        let sk = key();
        let vk = sk.verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let mut att = mint(&sw, &cw, &sk).unwrap();
        att.sig[0] ^= 0x01;
        assert_eq!(verify(&sw, &cw, &att, &vk), None);
    }

    #[test]
    fn fail_closed_on_garbage_no_token() {
        let sk = key();
        assert!(mint(b"", b"", &sk).is_none());
        assert!(mint(b"not-vclw", b"not-vcls", &sk).is_none());
        assert!(mint(&[0xff; 64], &[0xff; 64], &sk).is_none());
    }

    #[test]
    fn cabi_roundtrips_and_is_fail_closed() {
        let sk = key();
        let vk = sk.verifying_key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let skb = sk.to_bytes();
        let mut out = [0u8; 65];
        // SAFETY: valid owned slices (test).
        let rc = unsafe {
            vclut_rs_verify(
                sw.as_ptr(),
                sw.len(),
                cw.as_ptr(),
                cw.len(),
                skb.as_ptr(),
                out.as_mut_ptr(),
                out.len(),
            )
        };
        assert_eq!(rc, 0);
        let att = Attestation {
            level: out[0],
            sig: <[u8; 64]>::try_from(&out[1..65]).unwrap(),
        };
        assert_eq!(verify(&sw, &cw, &att, &vk), Some(0));

        // Fail-closed: garbage ⇒ -1, out untouched.
        let mut out2 = [0xAAu8; 65];
        // SAFETY: valid owned slices (test).
        let rc2 = unsafe {
            vclut_rs_verify(
                [1u8, 2, 3].as_ptr(),
                3,
                cw.as_ptr(),
                cw.len(),
                skb.as_ptr(),
                out2.as_mut_ptr(),
                out2.len(),
            )
        };
        assert_eq!(rc2, -1);
        assert!(out2.iter().all(|&b| b == 0xAA));
    }

    #[test]
    fn cabi_rejects_small_out_and_nulls() {
        let sk = key();
        let sw = to_wire(&parse_safe_stmt());
        let cw = to_wire_schema(&empty_schema());
        let skb = sk.to_bytes();
        let mut tiny = [0u8; 64];
        // SAFETY: valid slices; deliberately out_cap < 65.
        let rc = unsafe {
            vclut_rs_verify(
                sw.as_ptr(),
                sw.len(),
                cw.as_ptr(),
                cw.len(),
                skb.as_ptr(),
                tiny.as_mut_ptr(),
                tiny.len(),
            )
        };
        assert_eq!(rc, -1);
        // SAFETY: deliberately null stmt pointer.
        let rc2 = unsafe {
            vclut_rs_verify(
                core::ptr::null(),
                0,
                cw.as_ptr(),
                cw.len(),
                skb.as_ptr(),
                tiny.as_mut_ptr(),
                tiny.len(),
            )
        };
        assert_eq!(rc2, -1);
    }
}
