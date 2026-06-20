#!/bin/bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# SessionStart hook for Claude Code on the web (cloud sessions).
#
# Prefetches workspace dependencies and warms the Rust build cache so that
# `cargo test`, `cargo clippy`, and `cargo fmt` are ready immediately when a
# cloud session starts. Local sessions are skipped — your own machine already
# has the toolchain and dependencies, and this hook runs everywhere by design.
#
# Only the Rust toolchain (cargo) is exercised here: it is pre-installed in
# cloud sessions and drives the canonical `cargo test` suite. The optional
# Idris2/Zig pieces (idris-check, zig-build) are not pre-installed and are not
# required for the Rust test/lint path, so they are intentionally left out.
#
# Docs: https://code.claude.com/docs/en/claude-code-on-the-web
set -euo pipefail

# Cloud-only: do nothing on local checkouts.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

ROOT="${CLAUDE_PROJECT_DIR:-$PWD}"
cd "$ROOT" || exit 0

# Keep verbose cargo output out of the session context; log to a temp file.
LOG="${TMPDIR:-/tmp}/vcl-ut-session-start.log"
echo "[vcl-ut] Warming Rust workspace (cargo fetch + build --all-targets). Log: $LOG"

# 1. Fetch all workspace dependencies. Cargo.lock is authoritative; fall back to
#    an unlocked fetch if the lockfile is ever out of date. Idempotent and fast
#    once the registry cache is populated.
cargo fetch --locked >"$LOG" 2>&1 || cargo fetch >>"$LOG" 2>&1 || true

# 2. Warm the build cache for every target (lib + bins + tests + benches) so the
#    first `cargo test` / `cargo clippy` the agent runs is near-instant. Best
#    effort: a transient failure here must not block the session from starting.
cargo build --workspace --all-targets >>"$LOG" 2>&1 || true

echo "[vcl-ut] Workspace ready."
exit 0
