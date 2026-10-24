#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
"""check-ffi-header.py — keep the C ABI declaration and its exports in step.

`ffi/zig/include/vclut_ffi.h` is the published half of the VCL-total C
contract; `ffi/zig/src/lib.zig` holds the definitions. Nothing else checks
that the two agree, so a new export could ship undocumented (or a header
declaration could outlive its definition) and only a downstream consumer
would find out at link time.

This gate fails when:

  * an `pub export fn` in lib.zig has no prototype in the header;
  * a function prototype in the header has no `pub export fn` in lib.zig;
  * the two disagree on parameter count.

It is deliberately a shape check, not a type check. It catches a symbol
that exists on one side only, and parameter-count drift. It does NOT catch
a *type* change (e.g. `uint64_t` -> `uint32_t` on an unchanged parameter
list): that is caught by compiling, which the Zig shim gate does, and by
the Idris binding in `src/interface/abi/Tier2.idr`, which restates the
widths. Do not read a pass here as "the ABI types agree".

Exit status: 0 when consistent, 1 otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "ffi" / "zig" / "src" / "lib.zig"
HEADER = ROOT / "ffi" / "zig" / "include" / "vclut_ffi.h"

EXPORT_RE = re.compile(r"\bpub\s+export\s+fn\s+([A-Za-z_][A-Za-z0-9_]*)")
# A declaration we care about: starts a line, has a name followed by "(",
# and is not a macro/typedef/comment.
DECL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_ \t*]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*\(", re.MULTILINE)


def strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//[^\n]*", "", text)


def split_params(prototype: str) -> list[str]:
    """Split the outermost parenthesis pair on top-level commas.

    Zig parameter lists carry a trailing comma, so empty segments are
    dropped; `(void)` is the C spelling of "no parameters".
    """
    depth = 0
    segments: list[str] = []
    current: list[str] = []
    for ch in prototype:
        if ch == "(":
            depth += 1
            if depth == 1:
                continue
        elif ch == ")":
            depth -= 1
            if depth == 0:
                segments.append("".join(current))
                break
        elif depth == 1 and ch == ",":
            segments.append("".join(current))
            current = []
            continue
        if depth >= 1:
            current.append(ch)
    params = [seg.strip() for seg in segments]
    params = [seg for seg in params if seg and seg != "void"]
    return params


def count_params(prototype: str) -> int:
    return len(split_params(prototype))


def flatten(text: str, start: int) -> str:
    """Return text from `start` up to the closing paren of the first call."""
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    return text[start:]


def zig_exports(text: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for m in EXPORT_RE.finditer(text):
        name = m.group(1)
        paren = text.index("(", m.end())
        out[name] = count_params(flatten(text, paren))
    return out


def header_decls(text: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for m in DECL_RE.finditer(text):
        name = m.group(1)
        if name in {"if", "while", "for", "sizeof", "return", "defined"}:
            continue
        paren = text.index("(", m.end() - 1)
        proto = flatten(text, paren)
        if proto.strip() in {"()", "(void)"}:
            out[name] = 0
        else:
            out[name] = count_params(proto)
    return out


def main() -> int:
    for path in (LIB, HEADER):
        if not path.is_file():
            print(f"FAIL missing {path.relative_to(ROOT)}", file=sys.stderr)
            return 1

    exports = zig_exports(LIB.read_text(encoding="utf-8"))
    decls = header_decls(strip_c_comments(HEADER.read_text(encoding="utf-8")))

    problems: list[str] = []
    for name in sorted(exports):
        if name not in decls:
            problems.append(f"exported but not declared in the header: {name}")
        elif decls[name] != exports[name]:
            problems.append(
                f"arity mismatch for {name}: lib.zig has {exports[name]} "
                f"parameter(s), header declares {decls[name]}"
            )
    for name in sorted(decls):
        if name not in exports:
            problems.append(f"declared in the header but not exported: {name}")

    if not exports:
        problems.append("no `pub export fn` found in lib.zig — the scan is broken")

    if problems:
        for p in problems:
            print(f"FAIL {p}", file=sys.stderr)
        print(
            f"{len(problems)} problem(s) between "
            f"{LIB.relative_to(ROOT)} and {HEADER.relative_to(ROOT)}",
            file=sys.stderr,
        )
        return 1

    print(
        f"OK {len(exports)} exported symbol(s) match "
        f"{HEADER.relative_to(ROOT)} (name + arity): "
        + ", ".join(sorted(exports))
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
