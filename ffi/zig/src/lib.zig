// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// VCL-ut Zig FFI shim.
//
// Exports a minimal C-ABI surface that wraps the Rust vcl-ut crate's
// query-verification path. Callers (Idris2 ABI module, OCaml/AffineScript
// host, future SPARK satellites) link against libvclut_ffi.{so,a} and
// call these symbols directly — no Rust runtime, no JSON marshalling.
//
// Status: scaffold, FAIL-CLOSED (standards#124, Phase 3d). The real
// verification authority is the Idris2 certifier
// (`VclTotal.Core.Checker.certifyRequested` / `certifiedLevel`), which
// only yields a non-negative level when a genuine dependent
// `SafetyCertificate` exists. No verifier backend is linked into this
// shim yet, and there is deliberately NO fabricated result: a previous
// version returned a fake "Verified L2" for any string containing
// "SELECT" — that was a lie and has been deleted. Until the real
// backend is linked AND the string→AST parser + C-ABI Statement
// marshalling exist (NAMED OWED in
// verification/proofs/VERIFICATION-STANCE.adoc), this shim returns
// Rejected (-1). A fail-closed FFI is correct; a fabricated level is
// not.

const std = @import("std");

/// Per-thread last-error buffer. The Idris2 wrapper reads this via
/// vclut_last_error after a Rejected result.
threadlocal var last_error_buf: [4096]u8 = undefined;
threadlocal var last_error_len: usize = 0;

fn setLastError(msg: []const u8) void {
    const n = @min(msg.len, last_error_buf.len - 1);
    @memcpy(last_error_buf[0..n], msg[0..n]);
    last_error_buf[n] = 0;
    last_error_len = n;
}

fn clearLastError() void {
    last_error_buf[0] = 0;
    last_error_len = 0;
}

// ──────────────────────────────────────────────────────────────────────
// Tier-2 backend (P5d, vcl-ut#25) — the real `vclut_rs_verify`.
//
// Previously NAMED OWED ("declared in intent but not linked"). Now
// implemented by the Rust `vcltotal-attest` crate
// (`src/interface/attest`) and linked by build.zig. It decodes the
// wire `(Statement, OctadSchema)`, runs the conformance-pinned
// `vcltotal_parse::certified_level` (the same faithful image of the
// Idris corpus decision Tier-1 uses), and on a genuine level mints an
// Ed25519 attestation bound to `(sha256(stmt_wire), sha256(schema_wire),
// level)`. Fail-closed: a Reject / decode failure yields -1 and NO
// token. This is the Tier-2 *fallback* (trusted-certifier attestation)
// — explicitly weaker than Tier-1 recompute-PCC; see
// verification/proofs/VERIFICATION-STANCE.adoc.
// ──────────────────────────────────────────────────────────────────────

extern fn vclut_rs_verify(
    stmt_ptr: [*]const u8,
    stmt_len: usize,
    schema_ptr: [*]const u8,
    schema_len: usize,
    sk_ptr: [*]const u8,
    out_ptr: [*]u8,
    out_cap: usize,
) callconv(.c) i64;

// ──────────────────────────────────────────────────────────────────────
// C-ABI exports
// ──────────────────────────────────────────────────────────────────────

/// Initialise the FFI session. Returns 0 on success, non-zero on
/// failure (with the reason in last_error_buf).
pub export fn vclut_init() callconv(.c) c_int {
    clearLastError();
    return 0;
}

/// Verify a VCL query string against a registered schema.
/// Returns 1..10 on Verified, 0 on Pending, -1 on Rejected.
/// On Rejected, vclut_last_error has the reason.
pub export fn vclut_verify_query(
    query_ptr: [*:0]const u8,
    schema_id: u64,
) callconv(.c) c_int {
    _ = schema_id; // unused until a real backend is linked
    const query = std.mem.span(query_ptr);

    if (query.len == 0) {
        setLastError("empty query");
        return -1;
    }

    // FAIL-CLOSED (standards#124, Phase 3d). There is intentionally NO
    // shape-based "optimistic" verdict here any more: returning a
    // positive safety level this shim did not establish is a lie. The
    // real verification authority is the Idris2 certifier
    // (`certifyRequested`/`certifiedLevel`), which only yields a level
    // behind a genuine dependent `SafetyCertificate`. Wiring is OWED:
    //   1. extern fn vclut_rs_verify(query_ptr, len, schema_id) -> i32
    //      (a real backend that marshals a `Statement`+`OctadSchema`
    //       and calls the Idris certifier) — NOT linked.
    //   2. a string→`Statement` parser — does not exist anywhere in the
    //      repo (the corpus certifies an already-built AST).
    // Until (1) and (2) exist, every query is Rejected. This keeps the
    // symbol table populated and the build green WITHOUT asserting an
    // unestablished safety level.
    setLastError("no verifier backend linked: vcl-ut verification " ++
        "authority is the Idris2 certifier (certifyRequested); FFI " ++
        "marshalling + string->AST parser are OWED — see " ++
        "verification/proofs/VERIFICATION-STANCE.adoc");
    return -1;
}

/// Get the last error message. Returns an empty string when no error
/// is pending. Caller does not own the pointer; copy before the next
/// FFI call.
/// Tier-2 (P5d): verify a wire-marshalled `(Statement, OctadSchema)`
/// and, on a genuine certified level, emit a signed attestation.
///
/// `stmt`/`schema` are the v1 wire bytes (the C-ABI marshalling, same
/// shape as the Tier-1 recompute module). `sk` is the certifier's
/// 32-byte Ed25519 seed (real provisioning is deployment, via the
/// estate token vault). On success returns the level `0..10` and
/// writes a 65-byte token `[level:1][sig:64]` into `out` (needs
/// `out_cap >= 65`). Returns -1 (Rejected) — writing nothing,
/// `vclut_last_error` set — on any decode failure, a Reject level, a
/// null pointer, or insufficient `out_cap`. **Fail-closed:** never a
/// token for a level the certifier did not establish.
pub export fn vclut_verify_wire(
    stmt_ptr: [*]const u8,
    stmt_len: usize,
    schema_ptr: [*]const u8,
    schema_len: usize,
    sk_ptr: [*]const u8,
    out_ptr: [*]u8,
    out_cap: usize,
) callconv(.c) c_int {
    clearLastError();
    const rc = vclut_rs_verify(
        stmt_ptr,
        stmt_len,
        schema_ptr,
        schema_len,
        sk_ptr,
        out_ptr,
        out_cap,
    );
    if (rc < 0) {
        setLastError("Rejected (fail-closed): no genuine certified " ++
            "level — Tier-2 attestation NOT minted. The verification " ++
            "authority is the conformance-pinned certified_level; see " ++
            "verification/proofs/VERIFICATION-STANCE.adoc");
        return -1;
    }
    // 0..10 fits c_int; rc is bounded by the Rust backend.
    return @intCast(rc);
}

pub export fn vclut_last_error() callconv(.c) [*:0]const u8 {
    if (last_error_len == 0) return "";
    return @ptrCast(&last_error_buf[0]);
}

// ──────────────────────────────────────────────────────────────────────
// Tests
// ──────────────────────────────────────────────────────────────────────

test "init clears error" {
    setLastError("stale");
    _ = vclut_init();
    try std.testing.expectEqual(@as(usize, 0), last_error_len);
}

test "verify rejects empty query" {
    _ = vclut_init();
    const rc = vclut_verify_query("", 0);
    try std.testing.expectEqual(@as(c_int, -1), rc);
}

// FAIL-CLOSED contract (standards#124, Phase 3d): with no verifier
// backend linked, a well-formed query must NOT receive a fabricated
// positive level. It is Rejected (-1) — the honest result. (The old
// test asserted `== 2`, enshrining the deleted lie.)
test "verify is fail-closed: no fabricated level without a backend" {
    _ = vclut_init();
    const rc = vclut_verify_query("SELECT * FROM t", 0);
    try std.testing.expectEqual(@as(c_int, -1), rc);
    // and it never returns a "verified" (>=1) level here
    try std.testing.expect(rc < 1);
}

// P5d integration: the REAL Rust Tier-2 backend is linked
// (libvcltotal_attest.a via build.zig). Garbage wire bytes must
// decode-fail in the conformance-pinned decoder ⇒ no attestation ⇒
// -1, end-to-end across the Zig↔Rust boundary. (A positive path needs
// a valid wire (Statement,OctadSchema), exhaustively covered by the
// Rust crate's own roundtrip/tamper suite; this asserts the
// fail-closed contract through the actual linked symbol.)
test "vclut_verify_wire fail-closed on garbage via the linked Rust backend" {
    _ = vclut_init();
    var out: [65]u8 = [_]u8{0xAA} ** 65;
    const sk = [_]u8{7} ** 32;
    const bad = [_]u8{0xFF} ** 8;
    const rc = vclut_verify_wire(&bad, bad.len, &bad, bad.len, &sk, &out, out.len);
    try std.testing.expectEqual(@as(c_int, -1), rc);
    // out untouched on the fail-closed path
    for (out) |byte| try std.testing.expectEqual(@as(u8, 0xAA), byte);
}
