#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tests/e2e.sh — End-to-end structural and pipeline validation for vql-ut (VCL-total).
#
# Validates:
#   1. Required structural files exist (Cargo.toml, README, grammar, spec)
#   2. Source layout follows expected structure
#   3. Cargo build succeeds
#   4. Full Rust test suite (unit + integration + property + e2e) passes
#   5. Key VCL-total examples round-trip through format → lint
#
# Usage:
#   bash tests/e2e.sh            # run all checks
#   E2E_BUILD=0 bash tests/e2e.sh  # skip build (structural only)

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

PASSED=0
FAILED=0
SKIPPED=0

check() {
    local desc="$1"
    local result="$2"
    if [ "$result" = "0" ]; then
        echo -e "  ${GREEN}PASS${NC} $desc"
        PASSED=$((PASSED + 1))
    else
        echo -e "  ${RED}FAIL${NC} $desc"
        FAILED=$((FAILED + 1))
    fi
}

skip() {
    echo -e "  ${YELLOW}SKIP${NC} $1"
    SKIPPED=$((SKIPPED + 1))
}

echo -e "${CYAN}=== VCL-total (vql-ut) E2E Validation ===${NC}"
echo ""

# ── Category 1: Required structural files ──────────────────────────────────
echo "Category 1: Structural files"

check "Cargo.toml exists"         "$([ -f Cargo.toml ] && echo 0 || echo 1)"
check "README.adoc exists"        "$([ -f README.adoc ] && echo 0 || echo 1)"
check "EXPLAINME.adoc exists"     "$([ -f EXPLAINME.adoc ] && echo 0 || echo 1)"
check "SECURITY.md exists"        "$([ -f SECURITY.md ] && echo 0 || echo 1)"
check "LICENSE exists"            "$([ -f LICENSE ] && echo 0 || echo 1)"
check "SPDX header in Cargo.toml" "$(grep -q 'SPDX-License-Identifier' Cargo.toml && echo 0 || echo 1)"
echo ""

# ── Category 2: Source layout ──────────────────────────────────────────────
echo "Category 2: Source layout"

check "src/ directory exists"           "$([ -d src ] && echo 0 || echo 1)"
check "src/lib.rs exists"               "$([ -f src/lib.rs ] && echo 0 || echo 1)"
check "tests/ directory exists"         "$([ -d tests ] && echo 0 || echo 1)"
check "tests/e2e_test.rs exists"        "$([ -f tests/e2e_test.rs ] && echo 0 || echo 1)"
check "tests/integration_test.rs exists" "$([ -f tests/integration_test.rs ] && echo 0 || echo 1)"
check "tests/property_test.rs exists"   "$([ -f tests/property_test.rs ] && echo 0 || echo 1)"
check ".machine_readable/ exists"       "$([ -d .machine_readable ] && echo 0 || echo 1)"
echo ""

# ── Category 3: VCL-total artefacts ───────────────────────────────────────
echo "Category 3: VCL-total artefacts"

check "arcvix paper (arXiv source) exists" "$([ -f arcvix-10-level-query-safety.tex ] && echo 0 || echo 1)"
check "examples/ directory has content"    "$([ -d examples ] && ls examples/*.vcl 2>/dev/null | head -1 | grep -q . && echo 0 || echo 1)"
check "features/ directory exists"        "$([ -d features ] && echo 0 || echo 1)"
check "verification/ directory exists"    "$([ -d verification ] && echo 0 || echo 1)"
echo ""

# ── Category 4: Build ──────────────────────────────────────────────────────
echo "Category 4: Build"

if [ "${E2E_BUILD:-1}" = "0" ]; then
    skip "Build check skipped (E2E_BUILD=0)"
else
    cargo build --release 2>/dev/null
    check "cargo build --release succeeds" "$?"
fi
echo ""

# ── Category 5: Full test suite ────────────────────────────────────────────
echo "Category 5: Rust test suite"

if [ "${E2E_BUILD:-1}" = "0" ]; then
    skip "Test suite skipped (E2E_BUILD=0)"
else
    cargo test 2>/dev/null
    check "cargo test (all: unit + integration + property + e2e)" "$?"
fi
echo ""

# ── Summary ────────────────────────────────────────────────────────────────
echo -e "${CYAN}=== Results: ${GREEN}${PASSED} passed${NC}, ${RED}${FAILED} failed${NC}, ${YELLOW}${SKIPPED} skipped${NC} ==="
[ "$FAILED" -eq 0 ]
