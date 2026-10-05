#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# tests/aspect_tests.sh — Aspect tests for vql-ut (VCL-total).
#
# Validates cross-cutting concerns and the safe-source boundary
# (vcl-ut#49). Rust code under src/ is safe Rust: the unsafe host/guest
# (wasm) and C-ABI boundary crates live under ffi/rust/, never under src/.
#
#   1. SPDX licence header on the FIRST line of every src/ Rust file
#   2. No unsafe Rust constructs anywhere under src/ (tests included):
#      `unsafe {`, `unsafe fn|impl|trait|extern`, `#[unsafe(...)]`,
#      `static mut`. FFI is isolated under ffi/rust/.
#   3. Every Rust crate root under src/ (lib.rs, main.rs, bin/*.rs)
#      carries `#![forbid(unsafe_code)]` — the compiler-level guard
#      behind the lexical check 2.
#   4. No .unwrap()/.expect()/panic!/unreachable!/todo!/unimplemented!
#      in production (non-test) Rust src/ — the SPARK-grade fail-closed
#      posture (cf. vcltotal-parse's deny lint-set, the estate pattern).
#   5. HTTPS-only URLs
#   6. No hardcoded secrets
#   7. Totality marker: Cargo.lock committed (reproducible builds)
#
# "Production source" (check 4 only) = *.rs under src/, EXCLUDING
# integration tests (any path under a tests/ directory) and EXCLUDING
# #[cfg(test)] modules (stripped below by brace depth): idiomatic test code
# legitimately uses unwrap/expect. Checks 1-3 cover test code too. Cargo
# target/ directories are pruned everywhere. Non-Rust files (e.g. the Zig
# FFI shim under ffi/zig) are out of scope for the Rust-pattern checks.

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

# List every Rust source file under src/, tests included, skipping Cargo
# target/ build output (which holds generated Rust).
all_src_rs_files() {
    find src/ -type d -name target -prune -o -type f -name '*.rs' -print | sort
}

# List the production Rust source files under src/: all_src_rs_files
# minus integration tests (any path under a tests/ directory).
prod_rs_files() { all_src_rs_files | grep -v '/tests/' || true; }

# List the Rust crate roots under src/ (lib.rs, main.rs, src/bin/*.rs),
# skipping Cargo target/ build output.
crate_root_files() {
    find src/ -type d -name target -prune -o -type f \
        \( -name lib.rs -o -name main.rs -o -path '*/src/bin/*.rs' \) -print | sort
}

echo "=== VCL-total Aspect Tests ==="
echo ""

# 1. SPDX header must be the first line, not merely present somewhere in
#    the file (which let misplaced headers silently pass this gate). The
#    expected string is split so REUSE does not read it as this file's own
#    licence declaration.
expected_spdx='// SPDX-License-'
expected_spdx+='Identifier: MPL-2.0'
missing_spdx=0
while IFS= read -r f; do
    if [ "$(head -n 1 "$f")" != "$expected_spdx" ]; then
        echo "    missing/misplaced SPDX: $f"
        missing_spdx=$((missing_spdx + 1))
    fi
done < <(all_src_rs_files)
check "SPDX header on the first line of all src/ Rust files" \
    "$([ "$missing_spdx" -eq 0 ] && echo 0 || echo 1)"

# 2. No unsafe Rust constructs anywhere under src/, tests included. The
#    unsafe host/guest and C-ABI boundaries live under ffi/rust/.
unsafe_hits=0
while IFS= read -r f; do
    n=$(awk -v f="$f" '
        /^[[:space:]]*\/\// { next }
        /(^|[^[:alnum:]_])unsafe[[:space:]]*(\{|fn([^[:alnum:]_]|$)|extern([^[:alnum:]_]|$)|impl([^[:alnum:]_]|$)|trait([^[:alnum:]_]|$))/ \
            { print "    unsafe: " f ":" FNR > "/dev/stderr"; bad++; next }
        /#!?\[[[:space:]]*unsafe[[:space:]]*\(/ \
            { print "    unsafe attribute: " f ":" FNR > "/dev/stderr"; bad++; next }
        /(^|[^[:alnum:]_])static[[:space:]]+mut([^[:alnum:]_]|$)/ \
            { print "    static mut: " f ":" FNR > "/dev/stderr"; bad++; next }
        END { print bad+0 }' "$f")
    unsafe_hits=$((unsafe_hits + n))
done < <(all_src_rs_files)
check "No unsafe Rust in src/ (FFI isolated under ffi/rust/)" \
    "$([ "$unsafe_hits" -eq 0 ] && echo 0 || echo 1)"

# 3. Every crate root under src/ forbids unsafe code at compile time, in
#    addition to the lexical check above.
missing_forbid=0
while IFS= read -r f; do
    if ! grep -q '^#!\[forbid(unsafe_code)\]' "$f"; then
        echo "    missing #![forbid(unsafe_code)]: $f"
        missing_forbid=$((missing_forbid + 1))
    fi
done < <(crate_root_files)
check "All src/ Rust crate roots #![forbid(unsafe_code)]" \
    "$([ "$missing_forbid" -eq 0 ] && echo 0 || echo 1)"

# 4. No fail-open helpers in production (non-test) Rust src/: neither
#    .unwrap()/.expect() nor the panic family (`panic!`, `unreachable!`,
#    `todo!`, `unimplemented!`). Mirrors the vcltotal-parse deny
#    lint-set (the estate's SPARK-grade pattern).
failopen_hits=0
while IFS= read -r f; do
    n=$(strip_cfg_test < "$f" | grep -c '\.unwrap()\|\.expect(\|panic!\|unreachable!\|todo!\|unimplemented!' || true)
    failopen_hits=$((failopen_hits + n))
done < <(prod_rs_files)
check "No .unwrap()/.expect()/panic! in production src/" \
    "$([ "$failopen_hits" -eq 0 ] && echo 0 || echo 1)"

# 5. HTTPS-only URLs
http_hits=$(grep -rn 'http://[^l]' src/ 2>/dev/null | grep -v '#\|//' | wc -l || true)
check "HTTPS-only URLs in source (no plain http://)" "$([ "$http_hits" -eq 0 ] && echo 0 || echo 1)"

# 6. No hardcoded secrets
secret_hits=$(grep -rn 'password\s*=\s*["\x27][^"\x27]\|secret\s*=\s*["\x27][^"\x27]' \
    src/ 2>/dev/null | grep -iv 'test\|example\|placeholder' | wc -l || true)
check "No hardcoded secrets in source" "$([ "$secret_hits" -eq 0 ] && echo 0 || echo 1)"

# 7. Cargo.lock committed (reproducible builds)
check "Cargo.lock committed" "$([ -f Cargo.lock ] && echo 0 || echo 1)"

echo ""
echo "=== Results: ${PASSED} passed, ${FAILED} failed ==="
[ "$FAILED" -eq 0 ]
