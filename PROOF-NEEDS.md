# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

## Current State

- **LOC**: ~8,000
- **Languages**: Rust, ReScript, Idris2, Zig
- **Existing ABI proofs**: `src/interface/abi/*.idr` + domain-specific Idris2: `src/core/Checker.idr`, `Grammar.idr`, `Levels.idr`, `Schema.idr`, `Composition.idr`
- **Machine-verified**: the full `VclTotal` proof corpus — `verification/proofs/vclut-core.ipkg` builds clean under idris2 0.8.0 (`idris2 --build`, exit 0, `%default total`, **zero proof-escape symbols**, CI-gated by `.github/workflows/proof-corpus.yml`) as **10 modules** (`ABI.{Types,Layout,LayoutProofs}` + `Core.{Grammar,Schema,Decide,Levels,Checker,Composition,Epistemic}`), plus the self-contained `verification/proofs/SafetyL4Model.idr` (`--check`, exit 0). Phases 1–3 are on `origin/main` (PRs #21/#22/#23); Phase 4 (`LayoutProofs` + L6–L10 `composeJoin` closure) is **PR #24**, pending merge.
- **Status (Phase 0 → 4 RESOLVED, honestly)**: the Phase-0 blockers are fixed, not faked — the corpus compiles and is machine-checked; `ABI.Types`/`Grammar` errors repaired; **L2/L3/L5 de-vacuized** (Phase 2, evidence-carrying predicates over `Core.Decide`); all ten levels carry `checkLevelNSound` and `Checker.certifyAt`/`certifyRequested` assemble a genuine dependent `SafetyCertificate` (Phase 3); the Zig FFI is no longer a fabricating stub — it is **fail-closed** with a proof-gated `Checker.certifiedLevel` mint (Phase 3d). Remaining honest gaps are precisely scoped (FFI proof-transport, string→`Statement` parser, L3 subquery/heuristic scoping, L9/L10 predicate depth, the additive↔ceil `alignUp` sliver). `verification/proofs/VERIFICATION-STANCE.adoc` is the authoritative, proof-backed catalogue and takes precedence over this file.

## What Needs Proving

### Query Type Checker (src/core/Checker.idr)
- Already in Idris2 — verify it type-checks and that the checking algorithm is total
- Prove: well-typed VCL-total queries produce well-typed results against a schema

### Grammar Specification (src/core/Grammar.idr)
- VCL-total grammar defined in Idris2 — prove the grammar is unambiguous
- Prove: parser (ReScript side) accepts exactly the Idris2-specified grammar

### Level System (src/core/Levels.idr)
- ✅ L4 `NoRawUserInput` de-vacuized + `checkLevel4Sound` + `noRawUserInputCompose` (verified in `verification/proofs/SafetyL4Model.idr` and in situ in the corpus)
- ✅ L2/L3/L5 de-vacuized (Phase 2) — evidence-carrying predicates over `Core.Decide`, with `checkLevel2/3/5Sound` and genuine `composeJoin` closure
- ✅ L1 + L6–L10 sound (Phase 3) + genuine L6–L10 `composeJoin` closure (Phase 4: `l6..l9Compose`, `epiStructJoin`); L10 acyclicity carried by the explicit `JoinSideCondition` (provably non-closed, not faked)
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
