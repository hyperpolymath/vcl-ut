#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# check-ffi-header.sh — keep the C ABI declaration and its exports in step.
#
# `ffi/zig/include/vclut_ffi.h` is the published half of the VCL-total C
# contract; `ffi/zig/src/lib.zig` holds the definitions. Nothing else checks
# that the two agree, so a new export could ship undocumented (or a header
# declaration could outlive its definition) and only a downstream consumer
# would find out at link time.
#
# This gate fails when:
#
#   * an `pub export fn` in lib.zig has no prototype in the header;
#   * a function prototype in the header has no `pub export fn` in lib.zig;
#   * the two disagree on parameter count.
#
# It is deliberately a SHAPE check, not a TYPE check. It catches a symbol that
# exists on one side only, and parameter-count drift. It does NOT catch a type
# change (`uint64_t` -> `uint32_t` on an unchanged parameter list): that is
# caught by compiling, which the Zig shim gate does, and by the Idris binding
# in `src/interface/abi/Tier2.idr`, which restates the widths. Do not read a
# pass here as "the ABI types agree".
#
# Shell, not Python: the estate's `governance / Language / package
# anti-pattern policy` gate fails any PR that ships a .py file (see the
# reasoning in `.github/scripts/classify-issue.jq`).
#
# Exit status: 0 when consistent, 1 otherwise.

set -eu

root=$(unset CDPATH; cd -- "$(dirname -- "$0")/.." && pwd)
lib="$root/ffi/zig/src/lib.zig"
header="$root/ffi/zig/include/vclut_ffi.h"

for f in "$lib" "$header"; do
    if [ ! -f "$f" ]; then
        echo "FAIL missing ${f#"$root"/}" >&2
        exit 1
    fi
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

# ── Zig side ──────────────────────────────────────────────────────────────
# Strip `//` comments first: lib.zig's own prose mentions "`pub export fn`s",
# which must not count as a definition. Then join to one line so a signature
# that wraps is read as a whole.
sed 's|//.*||' "$lib" | tr '\n' ' ' | awk '
    function args_of(s,   depth, i, c, out) {
        depth = 1; out = ""
        for (i = 1; i <= length(s); i++) {
            c = substr(s, i, 1)
            if (c == "(") depth++
            else if (c == ")") { depth--; if (depth == 0) break }
            if (depth >= 1) out = out c
        }
        return out
    }
    {
        s = $0
        while (match(s, /pub[ \t]+export[ \t]+fn[ \t]+[A-Za-z_][A-Za-z0-9_]*[ \t]*\(/)) {
            head = substr(s, 1, RSTART + RLENGTH - 1)
            name = head
            sub(/.*fn[ \t]+/, "", name)
            sub(/[ \t]*\($/, "", name)
            rest = substr(s, RSTART + RLENGTH)
            print name "\t" args_of(rest)
            s = rest
        }
    }' > "$tmp/zig"

# ── Header side ───────────────────────────────────────────────────────────
# Strip block comments (multi-line aware) and `//` comments, drop preprocessor
# lines and the extern "C" braces, then split into `;`-terminated prototypes.
awk '
    BEGIN { inblock = 0 }
    {
        line = $0; out = ""; i = 1
        while (i <= length(line)) {
            if (!inblock) {
                p = index(substr(line, i), "/*")
                if (p == 0) { out = out substr(line, i); break }
                out = out substr(line, i, p - 1)
                i = i + p + 1
                inblock = 1
            } else {
                p = index(substr(line, i), "*/")
                if (p == 0) { break }
                i = i + p + 1
                inblock = 0
            }
        }
        print out
    }' "$header" |
    sed -e 's|//.*||' -e 's|extern "C"[[:space:]]*{||' |
    grep -v '^[[:space:]]*#' |
    grep -v '^[[:space:]]*[{}][[:space:]]*$' |
    tr '\n' ' ' | tr ';' '\n' | awk '
    function args_of(s,   depth, i, c, out) {
        depth = 1; out = ""
        for (i = 1; i <= length(s); i++) {
            c = substr(s, i, 1)
            if (c == "(") depth++
            else if (c == ")") { depth--; if (depth == 0) break }
            if (depth >= 1) out = out c
        }
        return out
    }
    {
        if (!match($0, /[A-Za-z_][A-Za-z0-9_ \t*]*[ \t*]([A-Za-z_][A-Za-z0-9_]*)[ \t]*\(/)) next
        name = substr($0, RSTART, RLENGTH)
        sub(/.*[ \t*]/, "", name)
        sub(/[ \t]*\($/, "", name)
        rest = substr($0, RSTART + RLENGTH)
        print name "\t" args_of(rest)
    }' > "$tmp/hdr"

if [ ! -s "$tmp/zig" ]; then
    echo "FAIL no 'pub export fn' found in ffi/zig/src/lib.zig — the scan is broken" >&2
    exit 1
fi

# ── Compare ───────────────────────────────────────────────────────────────
# Parameter count: top-level commas + 1, minus a trailing comma (Zig style);
# an empty list or C `(void)` is zero.
status=0
awk -F'\t' '
    function count(args,   depth, n, i, c, body) {
        depth = 0; n = 0
        for (i = 1; i <= length(args); i++) {
            c = substr(args, i, 1)
            if (c == "(") depth++
            else if (c == ")") depth--
            else if (c == "," && depth == 0) n++
        }
        body = args
        gsub(/[ \t]/, "", body)
        if (body == "" || body == "void") return 0
        if (body ~ /,$/) n--
        return n + 1
    }
    NR == FNR { arity[$1] = count($2); order[++n] = $1; next }
    { hdr[$1] = count($2) }
    END {
        bad = 0
        for (i = 1; i <= n; i++) {
            name = order[i]
            if (!(name in hdr)) {
                printf "FAIL exported but not declared in the header: %s\n", name > "/dev/stderr"
                bad++
            } else if (hdr[name] != arity[name]) {
                printf "FAIL arity mismatch for %s: lib.zig has %d parameter(s), header declares %d\n",
                       name, arity[name], hdr[name] > "/dev/stderr"
                bad++
            }
        }
        for (name in hdr) {
            if (!(name in arity)) {
                printf "FAIL declared in the header but not exported: %s\n", name > "/dev/stderr"
                bad++
            }
        }
        if (bad > 0) {
            printf "%d problem(s) between ffi/zig/src/lib.zig and ffi/zig/include/vclut_ffi.h\n", bad > "/dev/stderr"
            exit 1
        }
        exit 0
    }' "$tmp/zig" "$tmp/hdr" || status=$?

if [ "$status" -ne 0 ]; then
    exit 1
fi

symbols=$(cut -f1 "$tmp/zig" | sort | tr '\n' ' ')
echo "OK $(cut -f1 "$tmp/zig" | wc -l | tr -d ' ') exported symbol(s) match ffi/zig/include/vclut_ffi.h (name + arity): ${symbols% }"
exit 0
