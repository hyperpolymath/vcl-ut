# TEST-NEEDS: vql-ut

## CRG Grade: C — ACHIEVED 2026-04-04

## Current State

| Category | Count | Details |
|----------|-------|---------|
| **Source modules** | 27 | Idris2 core (4: Checker, Grammar, Levels, Schema), ReScript bridges (3: Ast, Bridge, Parser), ReScript definitions/errors (2), Rust interfaces (LSP 2, DAP 2, fmt 2, lint 2, lib), 3 Idris2 interface ABI, Zig FFI |
| **Unit tests** | 1 file | integration_test.rs (49 #[test]) |
| **Integration tests** | 0 | Despite the filename, these are unit tests |
| **E2E tests** | 0 | None |
| **Benchmarks** | 0 | None |
| **Fuzz tests** | 0 | None |

## What's Missing

### P2P Tests (CRITICAL)
- [ ] No tests for ReScript parser -> Idris2 checker pipeline
- [ ] No tests for LSP server handling real editor requests
- [ ] No tests for DAP server with real debugger
- [ ] No tests for fmt/lint tools on actual VQL-UT code

### E2E Tests (CRITICAL)
- [ ] No test that parses VQL-UT, type-checks it through all 10 levels, and executes it
- [ ] No test for LSP completion/hover/diagnostics
- [ ] No test for DAP breakpoints/stepping

### Aspect Tests
- [ ] **Security**: Query language with no injection tests
- [ ] **Performance**: No benchmarks for type checking, parsing throughput
- [ ] **Concurrency**: No concurrent query compilation tests
- [ ] **Error handling**: No tests for malformed VQL-UT, type errors at each level

### Build & Execution
- [ ] 4 Idris2 core modules with 0 Idris2-level tests -- are proofs checked?
- [ ] 4 Rust tool interfaces (LSP, DAP, fmt, lint) with 0 tests each
- [ ] Zig FFI integration_test.zig likely template placeholder

### Benchmarks Needed
- [ ] VQL-UT parsing throughput
- [ ] Type checking per level (L1-L10)
- [ ] LSP response latency
- [ ] Query compilation time

### Self-Tests
- [ ] No VQL-UT self-consistency check

## FLAGGED ISSUES
- **49 tests for 27 source modules** = thin coverage
- **4 developer tools (LSP, DAP, fmt, lint) with 0 tests** -- tools that developers will use are untested
- **10-level type system with 0 level-specific tests** -- can't verify any level works
- **Idris2 formal core is unverified** -- the proofs exist but nobody tests that they check

## Priority: P0 (CRITICAL)

## FAKE-FUZZ ALERT

- `tests/fuzz/placeholder.txt` is a scorecard placeholder inherited from rsr-template-repo — it does NOT provide real fuzz testing
- Replace with an actual fuzz harness (see rsr-template-repo/tests/fuzz/README.adoc) or remove the file
- Priority: P2 — creates false impression of fuzz coverage
