// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// VCL-ut Zig FFI shim.
//
// Exports a minimal C-ABI surface that wraps the Rust vcl-total crates'
// verification paths. Callers (Idris2 ABI module, OCaml/AffineScript
// host, future SPARK satellites) link against libvclut_ffi.{so,a} and
// call these symbols directly — no Rust runtime, no JSON marshalling.
//
// Normative C declarations for this surface: `include/vclut_ffi.h`
// (installed by `zig build`). That header and the `pub export fn`s below
// are the two halves of one contract; change them together.
//
// RETURN-CODE ALIASING (read this before combining the two entry
// points). `vclut_verify_query` uses 0 to mean *Pending* (no verdict
// yet), while `vclut_verify_wire` uses 0 to mean *Verified at level 0
// (ParseSafe) with a token written*. The two APIs are not interchangeable
// and must not share one rc→verdict mapping.
//
// Status: `vclut_verify_query` is scaffold, FAIL-CLOSED
// (standards#124, Phase 3d). The real verification authority is the
// Idris2 certifier (`VclTotal.Core.Checker.certifyRequested` /
// `certifiedLevel`), which only yields a non-negative level when a
// genuine dependent `SafetyCertificate` exists. No verifier backend is
// linked into this entry point yet, and there is deliberately NO
// fabricated result: a previous version returned a fake "Verified L2"
// for any string containing "SELECT" — that was a lie and has been
// deleted. Until the real backend is linked AND the string→AST parser +
// C-ABI Statement marshalling exist (NAMED OWED in
// verification/proofs/VERIFICATION-STANCE.adoc), this shim returns
// Rejected (-1). A fail-closed FFI is correct; a fabricated level is
// not.

const std = @import("std");

/// Per-thread last-error buffer. Read via `vclut_last_error` after a
/// Rejected (-1) result.
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
// ABI constants. These are published in `include/vclut_ffi.h`; the Idris2
// binding (`src/interface/abi/Tier2.idr`) restates the same two widths.
// ──────────────────────────────────────────────────────────────────────

/// Attestation token width: `[level:1][sig:64]`.
const token_size: usize = 65;
/// Ed25519 seed width. Transmitted explicitly as `sk_len` — never assumed.
const seed_size: usize = 32;
/// Highest level the certifier can establish (`EpistemicSafe`).
const max_level: i64 = 10;

// ──────────────────────────────────────────────────────────────────────
// Tier-2 backend (P5d, vcl-ut#25) — the real `vclut_rs_verify`.
//
// Implemented by the Rust `vcltotal-attest` crate (`ffi/rust/attest`) and
// linked by build.zig. It decodes the wire `(Statement, OctadSchema)`,
// runs the conformance-pinned `vcltotal_parse::certified_level` (the same
// faithful image of the Idris corpus decision Tier-1 uses), and on a
// genuine level mints an Ed25519 attestation bound to
// `(sha256(stmt_wire), sha256(schema_wire), level)`.
//
// This is a NATIVE Rust static library linked into this shim, not a wasm
// guest: the decode/sign code runs in the caller's address space. The
// Rust crate is `panic = "abort"`, so a (by-construction unreachable)
// panic aborts the process rather than unwinding across the boundary.
// Fail-closed: a Reject / decode failure yields -1 and NO token. This is
// the Tier-2 *fallback* (trusted-certifier attestation) — explicitly
// weaker than Tier-1 recompute-PCC; see
// verification/proofs/VERIFICATION-STANCE.adoc.
//
// Every pointer is optional (`?[*]`) because C callers can pass NULL; the
// Rust side rejects NULL, and `vclut_verify_wire` rejects it before the
// call so a NULL never reaches `from_raw_parts`.
// ──────────────────────────────────────────────────────────────────────

extern fn vclut_rs_verify(
    stmt_ptr: ?[*]const u8,
    stmt_len: usize,
    schema_ptr: ?[*]const u8,
    schema_len: usize,
    sk_ptr: ?[*]const u8,
    sk_len: usize,
    out_ptr: ?[*]u8,
    out_cap: usize,
) callconv(.c) i64;

/// Narrow the backend's `i64` verdict to the `c_int` this ABI promises.
///
/// Returns null for any value outside `0..=10`, so an out-of-contract
/// backend result is rejected rather than silently truncated by
/// `@intCast` (which would panic in Debug/ReleaseSafe and is UB in
/// ReleaseFast).
fn levelFromRc(rc: i64) ?c_int {
    if (rc < 0 or rc > max_level) return null;
    return @intCast(rc);
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
    query_ptr: ?[*:0]const u8,
    schema_id: u64,
) callconv(.c) c_int {
    _ = schema_id; // unused until a real backend is linked
    const query_c = query_ptr orelse {
        setLastError("null query pointer");
        return -1;
    };
    const query = std.mem.span(query_c);

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
    //   1. a real backend that marshals a `Statement`+`OctadSchema` and
    //      calls the Idris certifier — NOT linked to this entry point.
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

/// Verify a wire-marshalled `(Statement, OctadSchema)` and, on a genuine
/// certified level, emit a signed attestation.
///
/// `stmt`/`schema` are the v1 wire bytes (the C-ABI marshalling, same
/// shape as the Tier-1 recompute module). `sk`/`sk_len` is the
/// certifier's Ed25519 *seed*; `sk_len` must be exactly 32 and is
/// checked here, before the pointer is ever narrowed to a slice. `out`/
/// `out_cap` receives a 65-byte token `[level:1][sig:64]`.
///
/// Returns the level `0..=10` on success. Note that 0 is a *success*
/// here (`ParseSafe`, token written) — unlike `vclut_verify_query`, where
/// 0 means Pending. Returns -1 (Rejected) — writing nothing,
/// `vclut_last_error` set — on a null pointer, `sk_len != 32`,
/// `out_cap < 65`, any decode failure, a Reject level, or a backend
/// result outside `0..=10`. **Fail-closed:** never a token for a level
/// the certifier did not establish.
pub export fn vclut_verify_wire(
    stmt_ptr: ?[*]const u8,
    stmt_len: usize,
    schema_ptr: ?[*]const u8,
    schema_len: usize,
    sk_ptr: ?[*]const u8,
    sk_len: usize,
    out_ptr: ?[*]u8,
    out_cap: usize,
) callconv(.c) c_int {
    clearLastError();

    // Preconditions of the published C contract. Each is checked here so
    // that no NULL or out-of-range span can reach `from_raw_parts`.
    if (stmt_ptr == null or schema_ptr == null or
        sk_ptr == null or out_ptr == null)
    {
        setLastError("null pointer argument");
        return -1;
    }
    if (sk_len != seed_size) {
        setLastError("Ed25519 seed must be exactly 32 bytes (sk_len)");
        return -1;
    }
    if (out_cap < token_size) {
        setLastError("out_cap must be at least 65 bytes");
        return -1;
    }

    const rc = vclut_rs_verify(
        stmt_ptr,
        stmt_len,
        schema_ptr,
        schema_len,
        sk_ptr,
        sk_len,
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
    return levelFromRc(rc) orelse {
        setLastError("backend returned an out-of-range level — " ++
            "fail-closed");
        return -1;
    };
}

/// Get the last error message. Returns an empty string when no error
/// is pending. The pointer is thread-local and owned by this library;
/// copy the bytes before the next FFI call, and never free it.
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

test "verify rejects a null query pointer" {
    _ = vclut_init();
    const rc = vclut_verify_query(null, 0);
    try std.testing.expectEqual(@as(c_int, -1), rc);
    try std.testing.expect(std.mem.span(vclut_last_error()).len > 0);
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

test "levelFromRc accepts 0..=10 and rejects everything else" {
    // 0 is a genuine level (ParseSafe) on the wire path, not "Pending".
    try std.testing.expectEqual(@as(?c_int, 0), levelFromRc(0));
    try std.testing.expectEqual(@as(?c_int, 10), levelFromRc(10));
    try std.testing.expectEqual(@as(?c_int, null), levelFromRc(-1));
    try std.testing.expectEqual(@as(?c_int, null), levelFromRc(11));
    try std.testing.expectEqual(@as(?c_int, null), levelFromRc(1 << 40));
}

// The Zig-side preconditions are checked before the backend is called, so
// these hold with or without a linked backend.
test "verify_wire rejects null pointers, bad sk_len and small out_cap" {
    _ = vclut_init();
    var out: [65]u8 = [_]u8{0xAA} ** 65;
    const sk31 = [_]u8{7} ** 31;
    const bad = [_]u8{0xFF} ** 8;

    try std.testing.expectEqual(@as(c_int, -1), vclut_verify_wire(
        null,
        bad.len,
        &bad,
        bad.len,
        &sk31,
        sk31.len,
        &out,
        out.len,
    ));
    try std.testing.expectEqual(@as(c_int, -1), vclut_verify_wire(
        &bad,
        bad.len,
        &bad,
        bad.len,
        &sk31,
        sk31.len, // 31, not 32
        &out,
        out.len,
    ));
    const sk32 = [_]u8{7} ** 32;
    try std.testing.expectEqual(@as(c_int, -1), vclut_verify_wire(
        &bad,
        bad.len,
        &bad,
        bad.len,
        &sk32,
        sk32.len,
        &out,
        out.len - 1, // 64 < 65
    ));
    // out is untouched on every fail-closed path
    for (out) |byte| try std.testing.expectEqual(@as(u8, 0xAA), byte);
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
    const rc = vclut_verify_wire(
        &bad,
        bad.len,
        &bad,
        bad.len,
        &sk,
        sk.len,
        &out,
        out.len,
    );
    try std.testing.expectEqual(@as(c_int, -1), rc);
    // out untouched on the fail-closed path
    for (out) |byte| try std.testing.expectEqual(@as(u8, 0xAA), byte);
}
