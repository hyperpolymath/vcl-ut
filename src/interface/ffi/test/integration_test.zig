// VQL-UT Integration Tests
// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// These tests verify that the Zig FFI correctly implements the Idris2 ABI
// contract defined in Foreign.idr. They exercise the full query pipeline
// through external function calls.

const std = @import("std");
const testing = std.testing;

// Import the FFI module directly for integration testing
const ffi = @import("../src/main.zig");

//==============================================================================
// ABI Version Tests
//==============================================================================

test "abi version returns valid semantic version" {
    const ver = ffi.vqlut_abi_version();
    const major = ver >> 16;
    const minor = (ver >> 8) & 0xFF;
    // Major version 0 for pre-release
    try testing.expectEqual(@as(u32, 0), major);
    // Minor version should be at least 1
    try testing.expect(minor >= 1);
}

//==============================================================================
// Pipeline Lifecycle Tests
//==============================================================================

test "parse creates handle and destroy frees it" {
    const result = ffi.vqlut_parse(0, 0, 0);
    try testing.expectEqual(@as(u32, 0), result);
    ffi.vqlut_destroy(1);
}

test "multiple concurrent handles are independent" {
    // Allocate two contexts
    const r1 = ffi.vqlut_parse(0, @intFromEnum(ffi.QueryMode.slipstream), 0);
    try testing.expectEqual(@as(u32, 0), r1);

    const r2 = ffi.vqlut_parse(0, @intFromEnum(ffi.QueryMode.ultimate_type_safe), 0);
    try testing.expectEqual(@as(u32, 0), r2);

    // Handle 1 and handle 2 should have different safety levels after pipeline
    const handle1: u64 = 1;
    const handle2: u64 = 2;

    // Run handle1 through full pipeline
    _ = ffi.vqlut_bind_schema(handle1, 0, 0);
    _ = ffi.vqlut_check_types(handle1, 0);
    _ = ffi.vqlut_check_effects(handle1, 0);
    _ = ffi.vqlut_compile(handle1, 0, 0);

    // Run handle2 through full pipeline
    _ = ffi.vqlut_bind_schema(handle2, 0, 0);
    _ = ffi.vqlut_check_types(handle2, 0);
    _ = ffi.vqlut_check_effects(handle2, 0);
    _ = ffi.vqlut_compile(handle2, 0, 0);

    // Slipstream tops out at injection_proof (4)
    const level1 = ffi.vqlut_get_safety_level(handle1);
    try testing.expectEqual(@as(u32, 4), level1);

    // UltimateTypeSafe reaches linear_safe (9)
    const level2 = ffi.vqlut_get_safety_level(handle2);
    try testing.expectEqual(@as(u32, 9), level2);

    ffi.vqlut_destroy(handle1);
    ffi.vqlut_destroy(handle2);
}

//==============================================================================
// Error Handling Tests
//==============================================================================

test "null handle returns error on all pipeline stages" {
    const bind_result = ffi.vqlut_bind_schema(0, 0, 0);
    try testing.expectEqual(@intFromEnum(ffi.VqlUtError.internal_error), bind_result);

    const type_result = ffi.vqlut_check_types(0, 0);
    try testing.expectEqual(@intFromEnum(ffi.VqlUtError.internal_error), type_result);

    const effect_result = ffi.vqlut_check_effects(0, 0);
    try testing.expectEqual(@intFromEnum(ffi.VqlUtError.internal_error), effect_result);

    const compile_result = ffi.vqlut_compile(0, 0, 0);
    try testing.expectEqual(@intFromEnum(ffi.VqlUtError.internal_error), compile_result);
}

test "out-of-order pipeline stages return error" {
    // Parse first
    _ = ffi.vqlut_parse(0, 0, 0);
    const handle: u64 = 1;

    // Try to compile without binding schema — should fail
    const result = ffi.vqlut_compile(handle, 0, 0);
    try testing.expectEqual(@intFromEnum(ffi.VqlUtError.internal_error), result);

    ffi.vqlut_destroy(handle);
}

test "last error is set after failure" {
    // Use an invalid handle
    _ = ffi.vqlut_get_safety_level(0);

    const err = ffi.vqlut_last_error();
    try testing.expect(err != 0);
}

//==============================================================================
// Safety Level Tests
//==============================================================================

test "dependent types mode reaches effect_tracked level" {
    _ = ffi.vqlut_parse(0, @intFromEnum(ffi.QueryMode.dependent_types), 0);
    const handle: u64 = 1;

    _ = ffi.vqlut_bind_schema(handle, 0, 0);
    _ = ffi.vqlut_check_types(handle, 0);
    _ = ffi.vqlut_check_effects(handle, 0);
    _ = ffi.vqlut_compile(handle, 0, 0);

    // DependentTypes mode tops out at effect_tracked (7)
    const level = ffi.vqlut_get_safety_level(handle);
    try testing.expectEqual(@as(u32, 7), level);

    ffi.vqlut_destroy(handle);
}

//==============================================================================
// Memory Safety Tests
//==============================================================================

test "double destroy is safe" {
    _ = ffi.vqlut_parse(0, 0, 0);
    const handle: u64 = 1;

    ffi.vqlut_destroy(handle);
    ffi.vqlut_destroy(handle); // second destroy should be no-op
}

test "destroy then use returns error" {
    _ = ffi.vqlut_parse(0, 0, 0);
    const handle: u64 = 1;

    ffi.vqlut_destroy(handle);

    // After destroy, the handle is invalid
    const level = ffi.vqlut_get_safety_level(handle);
    try testing.expectEqual(@as(u32, 0xFFFFFFFF), level);
}

//==============================================================================
// Struct Layout Tests
//==============================================================================

test "QueryPlanHeader has correct C-ABI layout" {
    try testing.expectEqual(@as(usize, 24), @sizeOf(ffi.QueryPlanHeader));
    try testing.expectEqual(@as(usize, 8), @alignOf(ffi.QueryPlanHeader));

    // Verify field offsets match Layout.idr
    try testing.expectEqual(@as(usize, 0), @offsetOf(ffi.QueryPlanHeader, "magic"));
    try testing.expectEqual(@as(usize, 4), @offsetOf(ffi.QueryPlanHeader, "version"));
    try testing.expectEqual(@as(usize, 8), @offsetOf(ffi.QueryPlanHeader, "mode"));
    try testing.expectEqual(@as(usize, 12), @offsetOf(ffi.QueryPlanHeader, "level"));
    try testing.expectEqual(@as(usize, 16), @offsetOf(ffi.QueryPlanHeader, "plan_size"));
}
