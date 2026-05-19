# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

## Current State

- **LOC**: ~8,000
- **Languages**: Rust, ReScript, Idris2, Zig
- **Existing ABI proofs**: `src/interface/abi/*.idr` + domain-specific Idris2: `src/core/Checker.idr`, `Grammar.idr`, `Levels.idr`, `Schema.idr`, `Composition.idr`
- **Machine-verified**: `verification/proofs/SafetyL4Model.idr` only (idris2 0.8.0 `--check`, exit 0, zero proof escapes) — the Level-4 SQL-injection remediation
- **Dangerous patterns**: ⚠️ The `src/core/**` Idris2 corpus **does not compile** on `origin/main` and has **never been machine-checked** (no `.ipkg`/CI). `ABI.Types` has ≥4 type errors; `Grammar.idr` forward-references types with no `mutual` block. L2/L3/L5 safety predicates are **vacuous** (inhabited for any input, incl. injection); `SafetyCertificate` is never constructed by `checkQuery`; the Zig FFI is a `SELECT`-substring stub. See `verification/proofs/VERIFICATION-STANCE.adoc` for the authoritative, proof-backed catalogue. The earlier "None detected" line was wrong.

## What Needs Proving

### Query Type Checker (src/core/Checker.idr)
- Already in Idris2 — verify it type-checks and that the checking algorithm is total
- Prove: well-typed VCL-total queries produce well-typed results against a schema

### Grammar Specification (src/core/Grammar.idr)
- VCL-total grammar defined in Idris2 — prove the grammar is unambiguous
- Prove: parser (ReScript side) accepts exactly the Idris2-specified grammar

### Level System (src/core/Levels.idr)
- ✅ L4 `NoRawUserInput` de-vacuized + `checkLevel4Sound` + `noRawUserInputCompose` (verified in `verification/proofs/SafetyL4Model.idr`)
- ⚠️ L2/L3/L5 predicates still vacuous — de-vacuize with evidence-carrying constructors and prove each `checkLevelN` sound (as done for L4)
- 10-level type safety hierarchy — prove level ordering is a lattice
- Prove: level promotion/demotion preserves query safety

### Schema Validation (src/core/Schema.idr)
- Prove: schema-validated queries cannot produce runtime type errors
- Prove: schema evolution preserves backward compatibility for existing queries

### Rust DAP/Formatter (src/interface/dap/, src/interface/fmt/)
- Debug adapter and formatter — lower priority but should preserve query semantics

### ReScript Bridge (src/bridges/)
- `VclTotalParser.res`, `VclTotalBridge.res` — a **standalone ReScript
  frontend** (a working recursive-descent parser producing a *ReScript*
  AST). It is **not** on the verified path: it does not connect to, or
  marshal into, the Idris2 `Statement` the proof corpus certifies, nor
  the Rust core. (`VERIFICATION-STANCE.adoc` "no string→`Statement`
  parser exists" is precise — it means no parser whose output is the
  *certified* Idris2 `Statement`.)
- The *trusted* boundary parser is the Rust/SPARK-grade
  `src/interface/parse` crate (`vcltotal-parse`, P5a of vcl-ut#25),
  which mirrors `Grammar.idr` and feeds the certifier across the C-ABI.
- Optional future work: prove the ReScript frontend faithfully tracks
  the Idris2 grammar (low priority; it is a convenience frontend, not a
  trust anchor).

## Recommended Prover

- **Idris2** (already in use for core — complete the proofs in Checker.idr, Grammar.idr, Levels.idr, Schema.idr)

## Priority

**HIGH** — VCL-total is the query language for VeriSimDB. Incorrect type checking could allow queries that corrupt data or return wrong results. The Idris2 core is already in place — completing the proofs is high value for low effort.
