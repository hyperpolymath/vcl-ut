// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// VCL-ut FFI Build Configuration (Zig 0.15.2+).
//
// Builds:
//   - libvclut_ffi.so       shared library for Idris2 / OCaml / SPARK consumers
//   - libvclut_ffi.a        static library variant
//   - test runner           `zig build test`

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });

    // Shared library variant
    const shared = b.addLibrary(.{
        .name = "vclut_ffi",
        .root_module = lib_mod,
        .linkage = .dynamic,
    });
    b.installArtifact(shared);

    // Static library variant
    const static = b.addLibrary(.{
        .name = "vclut_ffi",
        .root_module = lib_mod,
        .linkage = .static,
    });
    b.installArtifact(static);

    // Tests
    const tests = b.addTest(.{
        .root_module = lib_mod,
    });
    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run vcl-ut FFI tests");
    test_step.dependOn(&run_tests.step);
}
