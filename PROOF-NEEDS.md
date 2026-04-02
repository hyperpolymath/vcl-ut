# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

## Current State

- **LOC**: ~8,000
- **Languages**: Rust, ReScript, Idris2, Zig
- **Existing ABI proofs**: `src/interface/abi/*.idr` (template-level) + domain-specific Idris2: `src/core/Checker.idr`, `Grammar.idr`, `Levels.idr`, `Schema.idr`
- **Dangerous patterns**: None detected

## What Needs Proving

### Query Type Checker (src/core/Checker.idr)
- Already in Idris2 — verify it type-checks and that the checking algorithm is total
- Prove: well-typed VQL-UT queries produce well-typed results against a schema

### Grammar Specification (src/core/Grammar.idr)
- VQL-UT grammar defined in Idris2 — prove the grammar is unambiguous
- Prove: parser (ReScript side) accepts exactly the Idris2-specified grammar

### Level System (src/core/Levels.idr)
- 10-level type safety hierarchy — prove level ordering is a lattice
- Prove: level promotion/demotion preserves query safety

### Schema Validation (src/core/Schema.idr)
- Prove: schema-validated queries cannot produce runtime type errors
- Prove: schema evolution preserves backward compatibility for existing queries

### Rust DAP/Formatter (src/interface/dap/, src/interface/fmt/)
- Debug adapter and formatter — lower priority but should preserve query semantics

### ReScript Bridge (src/bridges/)
- `VqlUtParser.res`, `VqlUtBridge.res` — bridge between ReScript frontend and Idris2/Rust core
- Prove: bridge faithfully translates between ReScript and core representations

## Recommended Prover

- **Idris2** (already in use for core — complete the proofs in Checker.idr, Grammar.idr, Levels.idr, Schema.idr)

## Priority

**HIGH** — VQL-UT is the query language for VeriSimDB. Incorrect type checking could allow queries that corrupt data or return wrong results. The Idris2 core is already in place — completing the proofs is high value for low effort.
