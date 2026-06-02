-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Interface — Cross-language Wire + Decision Conformance
||| (P5b/P5c). Machine-checked agreement between the certified Idris
||| corpus and the trusted Rust crate on shared golden fixtures:
|||
|||   * `conform{1,2,3,S1}` — `from{Wire,WireSchema} goldenN =
|||     Right expectedN` by `Refl`: the certified Idris decoder, run at
|||     compile time on the EXACT bytes the Rust `to_wire*` encoder
|||     emits (regeneration oracle `tests/conformance_emit.rs`),
|||     reduces to the expected certified value.
|||   * `clVerdict{1,2,3}` (P5c recompute tier) — the decisive corpus
|||     fact behind each Rust `certified_level` verdict, pinned with
|||     the `VclTotal.Core.Decide` deciders (fully `public export`,
|||     only import Grammar/Schema, so they reduce under `Refl`
|||     cross-module — unlike `Checker.checkLevelN`, whose helpers are
|||     `export`/Levels-coupled and do not reduce here). The Rust
|||     `decider.rs` is a line-by-line port of these same `Decide`
|||     functions; the conformance is: same `Decide` fact ⇒ same Rust
|||     verdict (oracle `cl{1,2,3}`: golden1→1, golden2→-1, golden3→0).
|||     Each fact is THE reason for its fixture's verdict:
|||       - golden1 (k=SchemaBound): its only ref-bearing clause is
|||         `SelStar` ⇒ statement field-ref set is `[]`;
|||         `allFieldRefsResolve [] = True` ⇒ L1 accepts ⇒ cl=1.
|||       - golden2 (k=EpistemicSafe): `vector.x` does NOT resolve in
|||         S1 ⇒ `fieldRefResolves = False` ⇒ L1 rejects ⇒ cl=-1.
|||       - golden3 (k=ParseSafe): no decider runs;
|||         `safetyLevelToInt ParseSafe = 0` ⇒ cl=0.
|||
||| No proof-escape, %default total.

module VclTotal.Interface.WireConformance

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import VclTotal.Core.Decide
import VclTotal.Interface.WireDecode

%default total

-- ── F1: minimal — SELECT * FROM STORE "main", level SchemaBound ──────

golden1 : List Bits8
golden1 = [86,67,76,87,1,0,1,0,0,0,3,2,4,0,0,0,109,97,105,110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]

expected1 : Statement
expected1 =
  MkStatement [SelStar] (SrcStore "main")
    Nothing [] Nothing [] Nothing Nothing
    Nothing Nothing Nothing Nothing Nothing
    SchemaBound

conform1 : fromWire WireConformance.golden1 = Right WireConformance.expected1
conform1 = Refl

-- ── F2: strings/ints/bools/agents/options/lists/nested expr + every
--       extension clause; level EpistemicSafe ─────────────────────────

golden2 : List Bits8
golden2 = [86,67,76,87,1,0,2,0,0,0,0,0,2,0,0,0,105,100,3,0,6,0,0,0,117,117,105,100,45,49,1,2,0,0,1,1,0,0,0,120,1,1,7,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,5,1,0,0,0,116,1,1,10,0,0,0,0,0,0,0,0,1,1,1,0,0,0,119,1,2,1,1,3,0,0,0,0,0,0,0,1,1,1,2,0,0,0,0,1,5,0,0,0,108,101,97,110,52,1,0,0,0,0,0,1,3,1,10]

expected2 : Statement
expected2 =
  MkStatement
    [SelField (MkFieldRef Graph "id"), SelStar]
    (SrcOctad "uuid-1")
    (Just (ECompare Eq
             (EField (MkFieldRef Vector "x") TAny)
             (ELiteral (LitInt 7) TAny)
             TAny))
    []
    Nothing
    [(MkFieldRef Temporal "t", True)]
    (Just 10)
    Nothing
    (Just (ProofWitness "w"))
    (Just EffReadWrite)
    (Just (VerAtLeast 3))
    (Just LinUseOnce)
    (Just (EpClause
             [AgEngine, AgProver "lean4"]
             [EpReqKnows AgEngine (ELiteral (LitBool True) TAny)]))
    EpistemicSafe

conform2 : fromWire WireConformance.golden2 = Right WireConformance.expected2
conform2 = Refl

-- ── F3: float path — WHERE 2.5 (exactly representable) ───────────────

golden3 : List Bits8
golden3 = [86,67,76,87,1,0,1,0,0,0,3,2,1,0,0,0,115,1,1,2,0,0,0,0,0,0,4,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

expected3 : Statement
expected3 =
  MkStatement [SelStar] (SrcStore "s")
    (Just (ELiteral (LitFloat 2.5) TAny))
    [] Nothing [] Nothing Nothing
    Nothing Nothing Nothing Nothing Nothing
    ParseSafe

conform3 : fromWire WireConformance.golden3 = Right WireConformance.expected3
conform3 = Refl

-- ── S1 (P5c): OctadSchema path ───────────────────────────────────────

goldenS1 : List Bits8
goldenS1 = [86,67,76,83,1,0,0,1,0,0,0,2,0,0,0,105,100,0,1,0,1,1,0,0,0,3,0,0,0,101,109,98,5,4,0,0,0,0,0,0,0,0,1,2,0,0,0,0,3,0,0,0,0,4,1,0,0,0,4,0,0,0,116,97,103,115,8,0,0,0,5,0,0,0,0,6,0,0,0,0,7,0,0,0,0]

expectedS1 : OctadSchema
expectedS1 =
  MkOctadSchema
    (MkModalitySchema Graph      [MkFieldDef "id" TString True False])
    (MkModalitySchema Vector     [MkFieldDef "emb" (TVector 4) False True])
    (MkModalitySchema Tensor     [])
    (MkModalitySchema Semantic   [])
    (MkModalitySchema Document   [MkFieldDef "tags" (TList TString) False False])
    (MkModalitySchema Temporal   [])
    (MkModalitySchema Provenance [])
    (MkModalitySchema Spatial    [])

conformS1 : fromWireSchema WireConformance.goldenS1 = Right WireConformance.expectedS1
conformS1 = Refl

-- ── P5c recompute-tier verdict pins (corpus PUBLIC deciders == the
--    Rust certified_level port, on the SAME decoded bytes) ────────────

||| golden1 ⇒ Rust cl=1. golden1's statement (`conform1`) has only
||| `SelStar` and no WHERE/GROUP/HAVING/ORDER, so its field-ref set is
||| empty; `Decide.allFieldRefsResolve [] schema = True` is the L1
||| accept, and `safetyLevelToInt SchemaBound = 1` is the level int —
||| together exactly the Rust `certified_level` value 1.
clVerdict1a : allFieldRefsResolve [] WireConformance.expectedS1 = True
clVerdict1a = Refl

clVerdict1b : safetyLevelToInt SchemaBound = 1
clVerdict1b = Refl

clVerdict1c : requestedLevel WireConformance.expected1 = SchemaBound
clVerdict1c = Refl

||| golden2 ⇒ Rust cl=-1, because L1 rejects: `vector.x` does not
||| resolve in S1. DISCLOSURE (not a fake): that fact forces
||| `resolveFieldRef` → `Schema.lookupField` → `Data.List.find`,
||| and `find` does NOT reduce under the idris2 0.8.0 evaluator (the
||| same limitation the corpus documents for `Data.List.elemBy`, for
||| which it hand-rolled `Decide.refElem`). So the negative-resolution
||| fact is NOT `Refl`-pinnable cross-module here. It is instead
||| machine-pinned on the Rust side — `conformance_emit.rs`'s
||| `fixtures_roundtrip` asserts `certified_level` over the DECODED
||| golden2 bytes `== -1` — and the input value the Rust decider runs
||| on is itself `Refl`-proven identical to the corpus's (`conform2`:
||| `fromWire golden2 = Right expected2`). What IS Refl-pinned here:
||| golden2 requests EpistemicSafe and its int would be 10 had every
||| level passed — so the observed -1 is a genuine rejection, not a
||| level-int mismatch.
clVerdict2a : requestedLevel WireConformance.expected2 = EpistemicSafe
clVerdict2a = Refl

clVerdict2b : safetyLevelToInt EpistemicSafe = 10
clVerdict2b = Refl

||| golden3 ⇒ Rust cl=0. requestedLevel = ParseSafe (k=0): no decider
||| runs, the level int is `safetyLevelToInt ParseSafe = 0`.
clVerdict3a : requestedLevel WireConformance.expected3 = ParseSafe
clVerdict3a = Refl

clVerdict3b : safetyLevelToInt ParseSafe = 0
clVerdict3b = Refl
