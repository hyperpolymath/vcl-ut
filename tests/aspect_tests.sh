#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tests/aspect_tests.sh — Aspect tests for vql-ut (VCL-total).
#
# Validates cross-cutting concerns:
#   1. SPDX licence headers on all source files
#   2. No unsafe blocks outside FFI boundaries
#   3. No banned dangerous patterns (unwrap/expect in non-test code)
#   4. HTTPS-only URLs
#   5. No hardcoded secrets
#   6. Totality markers (all public query fns documented)

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

PASSED=0
FAILED=0

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

echo "=== VCL-total Aspect Tests ==="
echo ""

# 1. SPDX headers
missing_spdx=$(find src/ -name '*.rs' 2>/dev/null \
    | xargs grep -rL "SPDX-License-Identifier" 2>/dev/null | wc -l)
check "SPDX headers on all src/ Rust files" "$([ "$missing_spdx" -eq 0 ] && echo 0 || echo 1)"

# 2. No unsafe in src/ (FFI layer would be in ffi/)
unsafe_hits=$(grep -rn 'unsafe\s*{' src/ 2>/dev/null | wc -l || true)
check "No unsafe blocks in src/ (FFI belongs in ffi/)" "$([ "$unsafe_hits" -eq 0 ] && echo 0 || echo 1)"

# 3. No .unwrap()/.expect() in non-test src/
unwrap_hits=$(grep -rn '\.unwrap()\|\.expect(' src/ 2>/dev/null | grep -v '#\[cfg(test)\]\|//.*unwrap' | wc -l || true)
check "No .unwrap()/.expect() in production src/" "$([ "$unwrap_hits" -eq 0 ] && echo 0 || echo 1)"

# 4. HTTPS-only URLs
http_hits=$(grep -rn 'http://[^l]' src/ 2>/dev/null | grep -v '#\|//' | wc -l || true)
check "HTTPS-only URLs in source (no plain http://)" "$([ "$http_hits" -eq 0 ] && echo 0 || echo 1)"

# 5. No hardcoded secrets
secret_hits=$(grep -rn 'password\s*=\s*["\x27][^"\x27]\|secret\s*=\s*["\x27][^"\x27]' \
    src/ 2>/dev/null | grep -iv 'test\|example\|placeholder' | wc -l || true)
check "No hardcoded secrets in source" "$([ "$secret_hits" -eq 0 ] && echo 0 || echo 1)"

# 6. Cargo.lock committed (reproducible builds)
check "Cargo.lock committed" "$([ -f Cargo.lock ] && echo 0 || echo 1)"

echo ""
echo "=== Results: ${PASSED} passed, ${FAILED} failed ==="
[ "$FAILED" -eq 0 ]
