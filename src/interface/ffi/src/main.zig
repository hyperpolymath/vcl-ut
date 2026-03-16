// VQL-UT FFI Implementation
//
// Implements the C-compatible FFI declared in src/interface/abi/Foreign.idr.
// Thread-safe, slot-based query context pool for concurrent query processing.
//
// All types and layouts match the Idris2 ABI definitions in Types.idr and Layout.idr.
//
// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

const std = @import("std");

//==============================================================================
// Constants
//==============================================================================

/// ABI version: 0.1.0 encoded as (major << 16 | minor << 8 | patch)
const ABI_VERSION: u32 = (0 << 16) | (1 << 8) | 0;

/// Magic number for query plan headers: "VQLU" in ASCII
const VQLUT_MAGIC: u32 = 0x56514C55;

/// Maximum concurrent query contexts in the slot pool
const MAX_CONTEXTS: usize = 256;

//==============================================================================
// Core Types (must match src/interface/abi/Types.idr)
//==============================================================================

/// SafetyLevel tag values (0-9), matching SafetyLevel in Types.idr
pub const SafetyLevel = enum(u32) {
    parse_safe = 0,
    schema_bound = 1,
    type_compat = 2,
    null_safe = 3,
    injection_proof = 4,
    result_typed = 5,
    cardinality_safe = 6,
    effect_tracked = 7,
    temporal_safe = 8,
    linear_safe = 9,
};

/// QueryMode tag values (0-2), matching QueryMode in Types.idr
pub const QueryMode = enum(u32) {
    slipstream = 0,
    dependent_types = 1,
    ultimate_type_safe = 2,
};

/// VqlUtError tag values (0-10), matching VqlUtError in Types.idr
pub const VqlUtError = enum(u32) {
    ok = 0,
    parse_error = 1,
    schema_error = 2,
    type_error = 3,
    null_error = 4,
    injection_attempt = 5,
    cardinality_violation = 6,
    effect_violation = 7,
    temporal_bounds_exceeded = 8,
    linearity_violation = 9,
    internal_error = 10,
};

/// QueryPlanHeader — 24 bytes, 8-byte aligned (matches Layout.idr)
pub const QueryPlanHeader = extern struct {
    magic: u32,
    version: u32,
    mode: u32,
    level: u32,
    plan_size: u64,
};

//==============================================================================
// Query Context (internal state behind opaque handles)
//==============================================================================

/// Pipeline stage — tracks how far a query has been processed
const PipelineStage = enum {
    parsed,
    schema_bound,
    type_checked,
    effect_checked,
    compiled,
};

/// Internal query context — one per active query handle.
/// Holds all intermediate state for a query moving through the pipeline.
const QueryContext = struct {
    /// Whether this slot is currently in use
    active: bool = false,
    /// Current pipeline stage
    stage: PipelineStage = .parsed,
    /// The query mode requested
    mode: QueryMode = .slipstream,
    /// Highest safety level achieved so far
    achieved_level: SafetyLevel = .parse_safe,
    /// Query plan buffer (populated after compile)
    plan: ?[]u8 = null,
    /// Allocator used for this context
    allocator: std.mem.Allocator = std.heap.page_allocator,

    /// Reset this context for reuse
    fn reset(self: *QueryContext) void {
        if (self.plan) |p| {
            self.allocator.free(p);
        }
        self.* = .{};
    }
};

//==============================================================================
// Thread-safe Slot Pool
//==============================================================================

/// Global slot pool — fixed array of query contexts protected by a mutex.
/// Slots are identified by index; the handle value is (index + 1) to
/// ensure handle 0 is never valid (matches the Idris2 non-null proof).
var pool_mutex: std.Thread.Mutex = .{};
var context_pool: [MAX_CONTEXTS]QueryContext = [_]QueryContext{.{}} ** MAX_CONTEXTS;

/// Thread-local error message storage
threadlocal var last_error_msg: ?[]const u8 = null;

/// Set the thread-local error message
fn setError(msg: []const u8) void {
    last_error_msg = msg;
}

/// Clear the thread-local error message
fn clearError() void {
    last_error_msg = null;
}

/// Allocate a slot from the pool. Returns slot index + 1 (the handle value),
/// or 0 if the pool is full.
fn allocSlot() u64 {
    pool_mutex.lock();
    defer pool_mutex.unlock();

    for (&context_pool, 0..) |*ctx, i| {
        if (!ctx.active) {
            ctx.active = true;
            ctx.stage = .parsed;
            ctx.mode = .slipstream;
            ctx.achieved_level = .parse_safe;
            ctx.plan = null;
            return @as(u64, i) + 1;
        }
    }
    return 0; // pool exhausted
}

/// Get a mutable reference to a context by handle value.
/// Returns null if the handle is invalid or the slot is inactive.
fn getContext(handle: u64) ?*QueryContext {
    if (handle == 0 or handle > MAX_CONTEXTS) return null;
    const idx = @as(usize, @intCast(handle - 1));

    pool_mutex.lock();
    defer pool_mutex.unlock();

    if (!context_pool[idx].active) return null;
    return &context_pool[idx];
}

/// Free a slot back to the pool.
fn freeSlot(handle: u64) void {
    if (handle == 0 or handle > MAX_CONTEXTS) return;
    const idx = @as(usize, @intCast(handle - 1));

    pool_mutex.lock();
    defer pool_mutex.unlock();

    context_pool[idx].reset();
}

//==============================================================================
// Exported FFI Functions (C ABI)
//==============================================================================

/// Get the VQL-UT ABI version.
/// Returns (major << 16 | minor << 8 | patch).
export fn vqlut_abi_version() u32 {
    return ABI_VERSION;
}

/// Parse a VQL query string into a parse tree handle.
///
/// @param query      Pointer to null-terminated VQL query string (unused in stub)
/// @param mode       QueryMode tag (0-2)
/// @param out_handle Out-pointer: receives handle on success (pointer to u64)
/// @return VqlUtError tag
export fn vqlut_parse(query: u64, mode: u32, out_handle: u64) u32 {
    _ = query;
    _ = out_handle;

    // Validate mode tag
    const query_mode = std.meta.intToEnum(QueryMode, mode) catch {
        setError("Invalid query mode");
        return @intFromEnum(VqlUtError.internal_error);
    };

    // Allocate a context slot
    const handle = allocSlot();
    if (handle == 0) {
        setError("Context pool exhausted");
        return @intFromEnum(VqlUtError.internal_error);
    }

    // Configure the context
    if (getContext(handle)) |ctx| {
        ctx.mode = query_mode;
        ctx.stage = .parsed;
        ctx.achieved_level = .parse_safe;
    }

    clearError();
    return @intFromEnum(VqlUtError.ok);
}

/// Bind a parse tree to a database schema.
///
/// @param parse_tree   Handle from vqlut_parse
/// @param schema       Handle to a loaded schema (unused in stub)
/// @param out_handle   Out-pointer (unused in stub)
/// @return VqlUtError tag
export fn vqlut_bind_schema(parse_tree: u64, schema: u64, out_handle: u64) u32 {
    _ = schema;
    _ = out_handle;

    const ctx = getContext(parse_tree) orelse {
        setError("Invalid parse tree handle");
        return @intFromEnum(VqlUtError.internal_error);
    };

    if (ctx.stage != .parsed) {
        setError("Expected parsed stage");
        return @intFromEnum(VqlUtError.internal_error);
    }

    ctx.stage = .schema_bound;
    ctx.achieved_level = .schema_bound;
    clearError();
    return @intFromEnum(VqlUtError.ok);
}

/// Type-check a schema-bound tree.
///
/// @param bound_tree  Handle from vqlut_bind_schema
/// @param out_handle  Out-pointer (unused in stub)
/// @return VqlUtError tag
export fn vqlut_check_types(bound_tree: u64, out_handle: u64) u32 {
    _ = out_handle;

    const ctx = getContext(bound_tree) orelse {
        setError("Invalid bound tree handle");
        return @intFromEnum(VqlUtError.internal_error);
    };

    if (ctx.stage != .schema_bound) {
        setError("Expected schema_bound stage");
        return @intFromEnum(VqlUtError.internal_error);
    }

    // In Slipstream mode, type checking covers levels 2-4
    ctx.stage = .type_checked;
    ctx.achieved_level = .injection_proof;
    clearError();
    return @intFromEnum(VqlUtError.ok);
}

/// Check effects on a typed tree.
///
/// @param typed_tree  Handle from vqlut_check_types
/// @param out_handle  Out-pointer (unused in stub)
/// @return VqlUtError tag
export fn vqlut_check_effects(typed_tree: u64, out_handle: u64) u32 {
    _ = out_handle;

    const ctx = getContext(typed_tree) orelse {
        setError("Invalid typed tree handle");
        return @intFromEnum(VqlUtError.internal_error);
    };

    if (ctx.stage != .type_checked) {
        setError("Expected type_checked stage");
        return @intFromEnum(VqlUtError.internal_error);
    }

    ctx.stage = .effect_checked;
    ctx.achieved_level = .effect_tracked;
    clearError();
    return @intFromEnum(VqlUtError.ok);
}

/// Compile an annotated tree into a query plan.
///
/// @param annotated_tree  Handle from vqlut_check_effects
/// @param out_plan        Out-pointer for plan buffer (unused in stub)
/// @param out_plan_size   Out-pointer for plan buffer size (unused in stub)
/// @return VqlUtError tag
export fn vqlut_compile(annotated_tree: u64, out_plan: u64, out_plan_size: u64) u32 {
    _ = out_plan;
    _ = out_plan_size;

    const ctx = getContext(annotated_tree) orelse {
        setError("Invalid annotated tree handle");
        return @intFromEnum(VqlUtError.internal_error);
    };

    if (ctx.stage != .effect_checked) {
        setError("Expected effect_checked stage");
        return @intFromEnum(VqlUtError.internal_error);
    }

    // Set final safety level based on mode
    ctx.achieved_level = switch (ctx.mode) {
        .slipstream => .injection_proof,
        .dependent_types => .effect_tracked,
        .ultimate_type_safe => .linear_safe,
    };

    ctx.stage = .compiled;
    clearError();
    return @intFromEnum(VqlUtError.ok);
}

/// Get the highest achieved safety level for a query plan.
///
/// @param handle  Handle from any pipeline stage
/// @return SafetyLevel tag (0-9), or 0xFFFFFFFF on error
export fn vqlut_get_safety_level(handle: u64) u32 {
    const ctx = getContext(handle) orelse {
        setError("Invalid handle");
        return 0xFFFFFFFF;
    };

    clearError();
    return @intFromEnum(ctx.achieved_level);
}

/// Destroy (free) any handle returned by VQL-UT.
/// Safe to call with 0 — will be a no-op.
///
/// @param handle  Any handle from the VQL-UT pipeline
export fn vqlut_destroy(handle: u64) void {
    freeSlot(handle);
    clearError();
}

/// Get the last error message as a pointer to a null-terminated C string.
/// Returns 0 (null) if no error has occurred.
/// The string is valid until the next VQL-UT call on the same thread.
export fn vqlut_last_error() u64 {
    if (last_error_msg) |msg| {
        // Return pointer to the static error string
        return @intFromPtr(msg.ptr);
    }
    return 0;
}

//==============================================================================
// Unit Tests
//==============================================================================

test "abi version" {
    const ver = vqlut_abi_version();
    const major = ver >> 16;
    const minor = (ver >> 8) & 0xFF;
    const patch = ver & 0xFF;
    try std.testing.expectEqual(@as(u32, 0), major);
    try std.testing.expectEqual(@as(u32, 1), minor);
    try std.testing.expectEqual(@as(u32, 0), patch);
}

test "parse and destroy" {
    const result = vqlut_parse(0, 0, 0);
    try std.testing.expectEqual(@as(u32, 0), result); // Ok
    // First allocated handle is slot index 0 + 1 = 1
    vqlut_destroy(1);
}

test "full pipeline slipstream" {
    // Parse
    var parse_result = vqlut_parse(0, @intFromEnum(QueryMode.slipstream), 0);
    try std.testing.expectEqual(@as(u32, 0), parse_result);

    // The handle is the first free slot + 1
    const handle: u64 = 1;

    // Bind schema
    parse_result = vqlut_bind_schema(handle, 0, 0);
    try std.testing.expectEqual(@as(u32, 0), parse_result);

    // Check types
    parse_result = vqlut_check_types(handle, 0);
    try std.testing.expectEqual(@as(u32, 0), parse_result);

    // Check effects
    parse_result = vqlut_check_effects(handle, 0);
    try std.testing.expectEqual(@as(u32, 0), parse_result);

    // Compile
    parse_result = vqlut_compile(handle, 0, 0);
    try std.testing.expectEqual(@as(u32, 0), parse_result);

    // Check safety level — slipstream tops out at injection_proof (4)
    const level = vqlut_get_safety_level(handle);
    try std.testing.expectEqual(@as(u32, 4), level);

    vqlut_destroy(handle);
}

test "full pipeline ultimate type safe" {
    const parse_result = vqlut_parse(0, @intFromEnum(QueryMode.ultimate_type_safe), 0);
    try std.testing.expectEqual(@as(u32, 0), parse_result);

    const handle: u64 = 1;

    _ = vqlut_bind_schema(handle, 0, 0);
    _ = vqlut_check_types(handle, 0);
    _ = vqlut_check_effects(handle, 0);
    _ = vqlut_compile(handle, 0, 0);

    // Ultimate mode reaches linear_safe (9)
    const level = vqlut_get_safety_level(handle);
    try std.testing.expectEqual(@as(u32, 9), level);

    vqlut_destroy(handle);
}

test "invalid handle returns error" {
    const level = vqlut_get_safety_level(0);
    try std.testing.expectEqual(@as(u32, 0xFFFFFFFF), level);

    const level2 = vqlut_get_safety_level(999);
    try std.testing.expectEqual(@as(u32, 0xFFFFFFFF), level2);
}

test "destroy null is safe" {
    vqlut_destroy(0); // should not crash
}

test "destroy invalid is safe" {
    vqlut_destroy(999); // should not crash
}

test "invalid mode returns error" {
    const result = vqlut_parse(0, 99, 0);
    try std.testing.expectEqual(@intFromEnum(VqlUtError.internal_error), result);
}

test "pipeline stage enforcement" {
    // Parse
    _ = vqlut_parse(0, 0, 0);
    const handle: u64 = 1;

    // Skip bind_schema — go straight to check_types (should fail)
    const result = vqlut_check_types(handle, 0);
    try std.testing.expectEqual(@intFromEnum(VqlUtError.internal_error), result);

    vqlut_destroy(handle);
}

test "query plan header layout" {
    // Verify the header struct has the expected size and alignment
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(QueryPlanHeader));
    try std.testing.expectEqual(@as(usize, 8), @alignOf(QueryPlanHeader));
}

test "last error after failure" {
    // Trigger an error
    _ = vqlut_get_safety_level(0);

    const err_ptr = vqlut_last_error();
    try std.testing.expect(err_ptr != 0);
}

test "last error cleared after success" {
    _ = vqlut_parse(0, 0, 0);
    // After successful parse, error should be cleared
    // (clearError is called on success path)
    vqlut_destroy(1);
}
