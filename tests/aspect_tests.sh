#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tests/aspect_tests.sh — Aspect tests for vql-ut (VCL-total).
#
# Validates cross-cutting concerns over PRODUCTION source. The gate's
# remit is *non-test* code: idiomatic test code legitimately uses
# unwrap/expect (and a test harness' own `testing.expect`-style helpers),
# so those are out of scope by design — see checks 2 and 3.
#
#   1. SPDX licence headers on all src/ Rust files
#   2. No UNDOCUMENTED unsafe in production src/. Audited FFI/WASM trust
#      boundaries are permitted to contain `unsafe` (a cdylib's
#      `#[no_mangle] extern "C"` entry *cannot* be written without it),
#      but every `unsafe {` must carry a contiguous `// SAFETY:`
#      justification — mirroring `clippy::undocumented_unsafe_blocks`.
#   3. No .unwrap()/.expect() in production (non-test) Rust src/
#   4. HTTPS-only URLs
#   5. No hardcoded secrets
#   6. Totality marker: Cargo.lock committed (reproducible builds)
#
# "Production source" = *.rs under src/, EXCLUDING integration tests
# (any path under a tests/ directory) and EXCLUDING #[cfg(test)] modules
# (stripped below by brace depth). Non-Rust files (e.g. the Zig FFI shim)
# are out of scope for the Rust-pattern checks 2 and 3.

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

# Print only the production (non-#[cfg(test)]-module) lines of a Rust file
# read on stdin. Tracks the brace depth of the #[cfg(test)]-guarded module
# so it is correct regardless of where the module sits in the file.
strip_cfg_test() {
    awk '
        BEGIN { intest=0; depth=0; pend=0 }
        {
            tt=$0; opens=gsub(/[{]/,"&",tt)
            tt=$0; closes=gsub(/[}]/,"&",tt)
            if (intest) { depth+=opens-closes; if (depth<=0) intest=0; next }
            if (pend)   { depth+=opens-closes; if (opens>0){ intest=1; pend=0; if(depth<=0) intest=0 } ; next }
            if ($0 ~ /#\[cfg\(test\)\]/) {
                if (opens>0) { depth=opens-closes; intest=1; if(depth<=0) intest=0 }
                else { pend=1; depth=0 }
                next
            }
            print
        }'
}

# Production Rust sources: *.rs under src/, excluding integration tests.
prod_rs_files() { find src/ -name '*.rs' 2>/dev/null | grep -v '/tests/' | sort; }

echo "=== VCL-total Aspect Tests ==="
echo ""

# 1. SPDX headers
missing_spdx=$(find src/ -name '*.rs' 2>/dev/null \
    | xargs grep -rL "SPDX-License-Identifier" 2>/dev/null | wc -l)
check "SPDX headers on all src/ Rust files" "$([ "$missing_spdx" -eq 0 ] && echo 0 || echo 1)"

# 2. No UNDOCUMENTED unsafe in production src/. Every `unsafe {` must be
#    immediately preceded by a contiguous `// SAFETY:` justification.
undoc_unsafe=0
while IFS= read -r f; do
    n=$(strip_cfg_test < "$f" | awk '
        /\/\/[[:space:]]*SAFETY/ { armed=1 }
        /unsafe[[:space:]]*\{/   { if (!armed) bad++; armed=0; next }
        ($0 !~ /^[[:space:]]*\/\//) && ($0 !~ /^[[:space:]]*$/) { armed=0 }
        END { print bad+0 }')
    undoc_unsafe=$((undoc_unsafe + n))
done < <(prod_rs_files)
check "No undocumented unsafe in production src/ (// SAFETY: required)" \
    "$([ "$undoc_unsafe" -eq 0 ] && echo 0 || echo 1)"

# 3. No .unwrap()/.expect() in production (non-test) Rust src/.
unwrap_hits=0
while IFS= read -r f; do
    n=$(strip_cfg_test < "$f" | grep -c '\.unwrap()\|\.expect(' || true)
    unwrap_hits=$((unwrap_hits + n))
done < <(prod_rs_files)
check "No .unwrap()/.expect() in production src/" \
    "$([ "$unwrap_hits" -eq 0 ] && echo 0 || echo 1)"

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
