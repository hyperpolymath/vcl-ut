// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// VCL-ut FFI Build Configuration (Zig 0.15.2+).
//
// Builds:
//   - libvclut_ffi.so       shared library for Idris2 / OCaml / SPARK consumers
//   - libvclut_ffi.a        static library variant
//   - test runner           `zig build test`
//
// P5d (vcl-ut#25): the Tier-2 attestation backend `vclut_rs_verify`
// (previously declared-but-unlinked, NAMED OWED) is now the Rust
// `vcltotal-attest` crate (`src/interface/attest`). build.zig compiles
// that staticlib via cargo and links it into every artefact (incl. the
// test runner), so the shim's `vclut_verify_wire` calls a real,
// conformance-pinned, fail-closed backend — not a stub.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Build the Rust Tier-2 backend staticlib (libvcltotal_attest.a).
    const cargo = b.addSystemCommand(&.{
        "cargo",                "build",
        "--release",            "--manifest-path",
        "../../src/interface/attest/Cargo.toml",
    });

    const attest_a = b.path("../../src/interface/attest/target/release/libvcltotal_attest.a");

    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    // Link the Rust Tier-2 staticlib. glibc (link_libc) covers
    // pthread/dl/m/rt; `gcc_s` provides the `_Unwind_*` personality
    // symbols Rust `std` references (backtrace/personality) even under
    // `panic = "abort"`. This is the standard Rust-staticlib companion.
    lib_mod.addObjectFile(attest_a);
    lib_mod.linkSystemLibrary("gcc_s", .{});

    // Shared library variant
    const shared = b.addLibrary(.{
        .name = "vclut_ffi",
        .root_module = lib_mod,
        .linkage = .dynamic,
    });
    shared.step.dependOn(&cargo.step);
    b.installArtifact(shared);

    // Static library variant
    const static = b.addLibrary(.{
        .name = "vclut_ffi",
        .root_module = lib_mod,
        .linkage = .static,
    });
    static.step.dependOn(&cargo.step);
    b.installArtifact(static);

    // Tests (linked against the real Rust backend)
    const tests = b.addTest(.{
        .root_module = lib_mod,
    });
    tests.step.dependOn(&cargo.step);
    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run vcl-ut FFI tests");
    test_step.dependOn(&run_tests.step);
}
