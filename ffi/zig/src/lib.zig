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
// Status: scaffold. The Rust-side `extern "C"` entry points that this
// shim is supposed to wrap don't exist yet; the functions below stub
// out the behaviour so the build is green and the symbol table is
// populated. When the Rust crate exposes its `vclut_verify_query`
// FFI counterpart, swap the stub calls for `extern fn` declarations.

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
    _ = schema_id; // unused until Rust side ships
    const query = std.mem.span(query_ptr);

    // Stub validation — until the Rust crate exposes its extern "C"
    // counterpart, we do a minimal shape check so the FFI is testable
    // end-to-end. Real verification will route through:
    //   extern fn vclut_rs_verify(*const u8, usize, u64) -> i32;
    if (query.len == 0) {
        setLastError("empty query");
        return -1;
    }
    if (std.mem.indexOf(u8, query, "SELECT") == null) {
        setLastError("query missing SELECT keyword");
        return -1;
    }

    // Optimistic: declare L2Typed when the query passes the shape gate.
    // Higher levels require Rust-side type resolution.
    return 2;
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

test "verify accepts well-formed select" {
    _ = vclut_init();
    const rc = vclut_verify_query("SELECT * FROM t", 0);
    try std.testing.expectEqual(@as(c_int, 2), rc);
}
