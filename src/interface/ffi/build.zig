// VQL-UT FFI Build Configuration
// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Create the root module for the library source
    const root_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Shared library (.so, .dylib, .dll)
    const lib = b.addLibrary(.{
        .linkage = .dynamic,
        .name = "vqlut",
        .root_module = root_module,
        .version = .{ .major = 0, .minor = 1, .patch = 0 },
    });

    // Static library (.a)
    const lib_static = b.addLibrary(.{
        .linkage = .static,
        .name = "vqlut",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    // Install artifacts
    b.installArtifact(lib);
    b.installArtifact(lib_static);

    // Unit tests
    const lib_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });

    const run_lib_tests = b.addRunArtifact(lib_tests);

    const test_step = b.step("test", "Run VQL-UT FFI unit tests");
    test_step.dependOn(&run_lib_tests.step);
}
