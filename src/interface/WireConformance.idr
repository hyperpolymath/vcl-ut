-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Interface — Cross-language Wire Conformance (P5b step 2)
|||
||| Machine-checked proof that the certified Idris decoder
||| (`VclTotal.Interface.WireDecode.fromWire`) agrees, byte-for-byte,
||| with the trusted Rust encoder (`src/interface/parse/src/wire.rs`
||| `to_wire`) on shared golden fixtures.
|||
||| Each `goldenN` is the EXACT `to_wire` image emitted by the Rust
||| regeneration oracle `src/interface/parse/tests/conformance_emit.rs`
||| (run that test with `--nocapture` to re-derive these literals; the
||| literals below are injected verbatim from its output, never
||| hand-transcribed). The corresponding
||| `conformN : fromWire goldenN = Right expectedN` is proved by `Refl`:
||| the corpus build only succeeds if the total decoder, evaluated at
||| compile time on the Rust bytes, reduces to exactly the expected
||| certified `Statement`. This is WIRE-FORMAT.adoc's conformance
||| contract discharged as a proof, not a runtime test — no
||| proof-escape, %default total.
|||
||| Fixtures: F1 minimal; F2 exercises strings / ints / bools / agents /
||| options / lists / a nested comparison expression and every extension
||| clause; F3 the float path with the exactly-representable `2.5`
||| (arbitrary-`f64` bit-exactness — incl. the NaN payload, which the
||| Idris `Double` boundary does NOT preserve, by disclosure — is the
||| Rust proptest's job: `wire.rs::golden_bit_exact_floats`).

module VclTotal.Interface.WireConformance

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
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

-- ── F3: float path — WHERE 2.5 (exactly representable), level
--       ParseSafe. Witnesses the IEEE-754 reconstruction reduces to
--       the identical primitive `Double` under the evaluator. ─────────

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
