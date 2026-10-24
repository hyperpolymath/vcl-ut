/* SPDX-License-Identifier: MPL-2.0 */
/* Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> */
/*
 * vclut_ffi.h — normative C declarations for the VCL-total FFI surface.
 *
 * This header is the published half of the contract; the exported
 * definitions live in `ffi/zig/src/lib.zig` and the Tier-2 backend behind
 * `vclut_verify_wire` in `ffi/rust/attest/src/lib.rs`. `zig build`
 * installs this file, and `.github/workflows/zig-shim-gate.yml` fails if an
 * exported symbol is missing here or the two disagree on arity.
 *
 * RETURN-CODE ALIASING: `vclut_verify_query` uses 0 for *Pending* (no
 * verdict yet); `vclut_verify_wire` uses 0 for *Verified at level 0
 * (ParseSafe) with a token written*. Do not share one rc->verdict mapping
 * between the two entry points.
 */
#ifndef VCLUT_FFI_H
#define VCLUT_FFI_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Attestation token width: [level:1][sig:64]. */
#define VCLUT_ATTESTATION_TOKEN_SIZE 65
/* Ed25519 seed width, checked against `sk_len`. */
#define VCLUT_ED25519_SEED_SIZE 32
/* Highest certifiable level (EpistemicSafe). */
#define VCLUT_MAX_LEVEL 10
/* Every entry point returns this for "Rejected, fail-closed". */
#define VCLUT_REJECTED (-1)

/*
 * Initialise the FFI session. Returns 0 on success. Call once at process
 * start, before any other entry point.
 */
int vclut_init(void);

/*
 * Verify a VCL query string against a registered schema id.
 *
 * Returns 1..10  Verified at that level
 *         0      Pending (async checker still running)
 *         -1     Rejected — see vclut_last_error()
 *
 * Currently always -1: no verifier backend is linked to this entry point
 * (NAMED OWED — see verification/proofs/VERIFICATION-STANCE.adoc). This
 * is fail-closed by design; it must never report a level it did not
 * establish.
 */
int vclut_verify_query(const char *query, uint64_t schema_id);

/*
 * Verify wire-marshalled (Statement, OctadSchema) bytes and, on a genuine
 * certified level, write a signed attestation token.
 *
 *   stmt, stmt_len      v1 statement-wire bytes
 *   schema, schema_len  v1 schema-wire bytes
 *   sk, sk_len          certifier's Ed25519 seed; sk_len MUST be 32
 *   out, out_cap        token destination; out_cap MUST be >= 65
 *
 * Returns 0..10 — the certified level, with 65 bytes written to `out`.
 *   NOTE: 0 here is Verified/ParseSafe with a token, NOT Pending.
 * Returns -1 — Rejected, nothing written, reason in vclut_last_error() —
 *   on a NULL pointer, sk_len != 32, out_cap < 65, a decode failure, a
 *   Reject level, or a backend result outside 0..10.
 *
 * Preconditions: each (pointer, length) pair must describe a valid,
 * readable span (writable for `out`); the seed is never read past index
 * 31. NULL pointers are rejected, never dereferenced.
 */
int vclut_verify_wire(const uint8_t *stmt, size_t stmt_len,
                      const uint8_t *schema, size_t schema_len,
                      const uint8_t *sk, size_t sk_len,
                      uint8_t *out, size_t out_cap);

/*
 * Reason for the most recent Rejected (-1) result, or "" when none is
 * pending. The buffer is thread-local, owned by this library: copy the
 * bytes before the next FFI call and never free the pointer.
 */
const char *vclut_last_error(void);

#ifdef __cplusplus
}
#endif

#endif /* VCLUT_FFI_H */
