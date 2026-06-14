#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# honesty-guard.sh — advisory scan for fake-success "proof-escape" smells in
# the Idris2 corpus. These symbols let a broken proof typecheck and claim a
# green that it has not earned:
#
#   believe_me / really_believe_me   assert any type with zero proof content
#   postulate                        axiom with no proof
#   assert_total                     suppress the totality (coverage) checker
#   assert_smaller                   suppress the termination checker
#   idris_crash                      runtime abort masquerading as a value
#   sorry                            unfilled placeholder (Idris2 accepts it)
#   ?name                            unsolved metavariable / open hole
#   partial / %default partial       disable coverage+termination checking
#
# The scan STRIPS Idris comments first — line (`--`), doc (`|||`), and nested
# block (`{- -}`) — so a file that merely *names* one of these tokens in prose
# (as src/interface/abi/LayoutProofs.idr does in its module docstring) is not a
# false positive. String literals are comment-marker-aware so an in-string
# `--` cannot hide following code. Line numbers are preserved for reporting.
#
# Usage:   scripts/honesty-guard.sh [PATH ...]      (PATH = file or dir; default: src)
# Exit:    0 + "Clean."                      when no smell is found
#          1 + "N smell(s) in M file(s)"      and a file:line list otherwise
#
# Advisory by design: it is a diagnostic, not a substitute for the
# totality-checked `idris2 --build` of verification/proofs/vclut-core.ipkg.

set -u

PATTERN='\b(believe_me|really_believe_me|assert_total|assert_smaller|idris_crash|postulate|sorry|partial)\b|\?[A-Za-z_]'

# ---- Idris comment stripper (preserves one output line per input line) ------
awkprog=$(mktemp)
filelist=$(mktemp)
hits=$(mktemp)
trap 'rm -f "$awkprog" "$filelist" "$hits"' EXIT INT TERM

cat > "$awkprog" <<'AWK'
# Blank out Idris2 comments while keeping line count stable.
#   depth : nesting depth of {- -} block comments (persists across lines)
#   instr : inside a "..." string literal (reset per line; Idris strings
#           do not span lines except rare triple-quoted forms)
BEGIN { depth = 0 }
{
  line = $0; n = length(line); out = ""; i = 1; instr = 0
  while (i <= n) {
    c   = substr(line, i, 1)
    two = substr(line, i, 2)
    if (depth > 0) {                       # inside a block comment
      if (two == "-}") { depth--; i += 2; continue }
      if (two == "{-") { depth++; i += 2; continue }
      i++; continue
    }
    if (instr) {                           # inside a string literal
      out = out c
      if (c == "\\") { i++; if (i <= n) out = out substr(line, i, 1); i++; continue }
      if (c == "\"") { instr = 0 }
      i++; continue
    }
    if (two == "{-") { depth++; i += 2; continue }   # open block comment
    if (two == "--") { break }                       # line comment to EOL
    if (substr(line, i, 3) == "|||") { break }       # doc comment to EOL
    if (c == "\"") { instr = 1; out = out c; i++; continue }
    out = out c
    i++
  }
  print out
}
AWK

# ---- collect target files ---------------------------------------------------
[ "$#" -eq 0 ] && set -- src
for arg in "$@"; do
  if [ -d "$arg" ]; then
    find "$arg" -type f -name '*.idr'
  elif [ -f "$arg" ]; then
    printf '%s\n' "$arg"
  else
    echo "honesty-guard: no such path: $arg" >&2
  fi
done | sort -u > "$filelist"

# ---- scan -------------------------------------------------------------------
while IFS= read -r f; do
  [ -n "$f" ] || continue
  awk -f "$awkprog" "$f" | grep -nE "$PATTERN" | sed "s|^|$f:|" >> "$hits"
done < "$filelist"

# ---- report -----------------------------------------------------------------
if [ -s "$hits" ]; then
  cat "$hits"
  n=$(wc -l < "$hits" | tr -d ' ')
  m=$(cut -d: -f1 "$hits" | sort -u | wc -l | tr -d ' ')
  echo "honesty-guard: $n smell(s) in $m file(s)"
  exit 1
fi
echo "honesty-guard: Clean."
exit 0
