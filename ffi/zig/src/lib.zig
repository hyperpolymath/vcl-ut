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
