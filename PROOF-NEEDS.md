# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

## Current State

- **LOC**: ~8,000
- **Languages**: Rust, ReScript, Idris2, Zig
- **Existing ABI proofs**: `src/interface/abi/*.idr` + domain-specific Idris2: `src/core/Checker.idr`, `Grammar.idr`, `Levels.idr`, `Schema.idr`, `Composition.idr`
- **Machine-verified**: the full `VclTotal` proof corpus — `verification/proofs/vclut-core.ipkg` builds clean under idris2 0.8.0 (`idris2 --build`, exit 0, `%default total`, **zero proof-escape symbols**, CI-gated by `.github/workflows/proof-corpus.yml`) as **12 modules** (`ABI.{Types,Layout,LayoutProofs}` + `Core.{Grammar,Schema,Decide,Levels,Checker,Composition,Epistemic}` + `Interface.{WireDecode,WireConformance}`), plus the self-contained `verification/proofs/SafetyL4Model.idr` (`--check`, exit 0). Phases 1–4 are on `origin/main` (PRs #21/#22/#23/#24); Phase 5 / vcl-ut#25 (trusted Rust parser P5a #26, wire codec P5b-step-1 #28, **certified Idris wire decoder + cross-language `Refl` conformance** P5b-step-2) reinforces the FFI boundary.
- **Status (Phase 0 → 4 RESOLVED, honestly; Phase 5 boundary reinforcement in progress)**: the Phase-0 blockers are fixed, not faked — the corpus compiles and is machine-checked; `ABI.Types`/`Grammar` errors repaired; **L2/L3/L5 de-vacuized** (Phase 2, evidence-carrying predicates over `Core.Decide`); all ten levels carry `checkLevelNSound` and `Checker.certifyAt`/`certifyRequested` assemble a genuine dependent `SafetyCertificate` (Phase 3); the Zig FFI is no longer a fabricating stub — it is **fail-closed** with a proof-gated `Checker.certifiedLevel` mint (Phase 3d). **Phase 5 (vcl-ut#25)**: a trusted Rust/SPARK-grade parser + a deterministic versioned wire codec exist, and the *decode* side of the C-ABI `Statement` marshalling is now **certified** — `VclTotal.Interface.WireDecode` is a total (zero-escape) decoder proven byte-for-byte conformant with the Rust encoder by `Refl` (`WireConformance`). Remaining honest gaps are precisely scoped (P5c = typed-wasm PCC proof-transport — proof term + checker kernel the consumer re-runs, *re-checkable*, the estate-aligned objective; the C-ABI/Zig shim retained only as the fail-closed attestation fallback; P5d = signed-attestation *fallback* contract for C-only consumers; plus L3 subquery/heuristic scoping; L9/L10 predicate depth; the additive↔ceil `alignUp` sliver; the disclosed NaN-payload limitation of the Idris `Double` boundary). Re-checkable transport is impossible *only* over a C ABI, not over the estate's typed-wasm target. `verification/proofs/VERIFICATION-STANCE.adoc` is the authoritative, proof-backed catalogue and takes precedence over this file.

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
  Its `wire.rs` codec (P5b step 1) serialises the parsed `Statement`
  to a deterministic versioned binary format
  (`src/interface/parse/WIRE-FORMAT.adoc`).
- The *certified* receiver of that format is
  `VclTotal.Interface.WireDecode` (P5b step 2): a total, zero-escape
  Idris decoder into the certified `Statement`, proven byte-for-byte
  conformant with the Rust encoder by `Refl` in
  `VclTotal.Interface.WireConformance`. The marshalling seam's *decode*
  side is therefore now machine-verified. **P5c** (the estate-aligned
  objective): transport the certificate over the **typed-wasm** target
  as a proof term + a small checker kernel the consumer re-runs —
  proof-carrying code, *re-checkable*, TCB = checker kernel + typed-wasm
  verifier (re-checkable transport is impossible only over a C ABI; the
  `ffi/zig` fail-closed shim is retained only as the C-ABI attestation
  fallback). **P5d** (fallback tier): the signed-attestation contract
  for consumers reachable only over C. Both OWED; see the two-tier
  boundary model in `verification/proofs/VERIFICATION-STANCE.adoc`.
- Optional future work: prove the ReScript frontend faithfully tracks
  the Idris2 grammar (low priority; it is a convenience frontend, not a
  trust anchor).

## Recommended Prover

- **Idris2** (already in use for core — complete the proofs in Checker.idr, Grammar.idr, Levels.idr, Schema.idr)

## Priority

**HIGH** — VCL-total is the query language for VeriSimDB. Incorrect type checking could allow queries that corrupt data or return wrong results. The Idris2 core is already in place — completing the proofs is high value for low effort.
