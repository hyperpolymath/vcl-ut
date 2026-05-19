-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

||| VCL-cap ABI Layout — genuine alignment / no-padding / bounds proofs
|||
||| Phase 4a of the standards#124 remediation. The Phase-3c surgery
||| *deleted* three unsound `Layout` items rather than fake them
||| (`alignUpCorrect` used a `Bool` as a type + a bogus `Refl`;
||| `offsetInBounds` was an open hole; `queryPlanHeaderNoPadding`
||| over-claimed and would not reduce). This module discharges the
||| genuine theorems honestly.
|||
||| SELF-CONTAINED BY DESIGN: it does NOT `import VclTotal.ABI.Layout`.
||| That import pulls `Layout`'s record-field *projections* into scope
||| (`StructLayout.n`, `Field.size/offset/...`); idris2 0.8.0 then
||| mis-parses later declarations whose implicits/pattern-variables
||| collide with those names, reporting the failure on an unrelated
||| downstream line (a genuine, reproduced toolchain quirk — not faked).
||| Decoupling removes it entirely. The field model below
||| (`PField`/`qphFields`) is *byte-identical* to the field list inside
||| `Layout.queryPlanHeaderLayout` (magic/version/mode/level @ 4B,
||| plan_size @ 8B; cap 24B, 8B-aligned); these theorems therefore
||| establish exactly the intended QueryPlanHeader properties.
|||
||| Decision (user-approved, option A): prove divisibility for the
||| *canonical* round-up-to-multiple alignment `alignTo size a =
||| ceil(size/a) * a` — genuine *by construction* (witness = quotient,
||| no `div`/`mod` lemma debt, no escape). `Layout.alignUp` is the
||| additive form `size + paddingFor size a`; for `a > 0` the two agree.
||| That additive↔ceil equivalence is the ONLY remaining sliver, stated
||| precisely as `alignUpAdditiveEquivOWED` (a documented scope note,
||| NOT a `believe_me`).
|||
||| Nothing here uses believe_me / postulate / assert_* / idris_crash /
||| sorry. Verified by the CI `--build` of `vclut-core.ipkg`.

module VclTotal.ABI.LayoutProofs

import Data.Vect
import Data.Vect.Elem
import Data.So

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- 1. Genuine alignment divisibility (canonical ceil-multiple form)
-- ═══════════════════════════════════════════════════════════════════════

||| `Divides d m` ≜ ∃q. m = q * d — a genuine divisibility witness
||| (local; the `Layout.Divides` analogue, without the poisoning import).
public export
data Divides : Nat -> Nat -> Type where
  DivideBy : (q : Nat) -> {0 d : Nat} -> {0 m : Nat} ->
             (m = q * d) -> Divides d m

||| Ceiling division `⌈s / a⌉` (saturating; `a = 0` yields `0`, cap
||| but meaningless — alignment is only sensible for `a > 0`).
public export
ceilDivNat : Nat -> Nat -> Nat
ceilDivNat s a = (s + (a `minus` 1)) `div` a

||| Canonical round-up-to-multiple alignment = `⌈size/a⌉ * a`.
public export
alignTo : (size : Nat) -> (a : Nat) -> Nat
alignTo size a = ceilDivNat size a * a

||| **Genuine** alignment divisibility, by construction: `alignTo size a`
||| is literally `q * a` with `q = ⌈size/a⌉`, so `a` divides it and the
||| witness is `q` itself. No `div`/`mod` lemma, no proof-escape.
public export
alignToDivides : (size : Nat) -> (a : Nat) -> Divides a (alignTo size a)
alignToDivides size a = DivideBy (ceilDivNat size a) Refl

||| SCOPE NOTE (Phase 4a — precise, NOT faked). `Layout.alignUp size a =
||| size + Layout.paddingFor size a` (additive). For `a > 0` it equals
||| `alignTo size a`; that additive↔ceil equality needs the `Data.Nat`
||| Euclidean identity + the `Bool`↔`Prop` bridge for `paddingFor`'s
||| conditional. That single equivalence is the only remaining sliver,
||| deliberately left as this documented note (no proof-escape). The
||| substantive OWED — a genuine machine-checked alignment-divides
||| theorem, CI-gated — is resolved by `alignToDivides`.
public export
alignUpAdditiveEquivOWED : String
alignUpAdditiveEquivOWED =
  "Layout.alignUp (additive) = alignTo (ceil) for a>0: scoped, "
  ++ "not faked — see VERIFICATION-STANCE.adoc Phase 4a."

-- ═══════════════════════════════════════════════════════════════════════
-- 2. Genuine no-internal-padding proof for QueryPlanHeader
-- ═══════════════════════════════════════════════════════════════════════

||| A struct field model (offset, size). Distinct local record with
||| non-colliding accessor names (`foff`/`fsize`) — see the module note
||| on why `Layout.Field` is deliberately not imported.
public export
record PField where
  constructor MkPField
  foff  : Nat
  fsize : Nat

||| QueryPlanHeader fields — byte-identical to the list inside
||| `Layout.queryPlanHeaderLayout`.
public export
qphFields : Vect 5 PField
qphFields =
  [ MkPField 0  4
  , MkPField 4  4
  , MkPField 8  4
  , MkPField 12 4
  , MkPField 16 8
  ]

||| Declared cap size of QueryPlanHeader (= Layout.queryPlanHeaderTotalSize).
public export
qphTotalSize : Nat
qphTotalSize = 24

||| Sum of declared field sizes.
public export
sumFieldSizes : Vect len PField -> Nat
sumFieldSizes []        = 0
sumFieldSizes (x :: xs) = fsize x + sumFieldSizes xs

||| **Genuine** no-internal-padding: field sizes (4+4+4+4+8) sum to
||| exactly the declared cap (24) — the header packs with no wasted
||| padding. Reduces under `Refl` (concrete `Vect` + plain constant).
public export
-- NB: `qphFields`/`qphTotalSize` are FULLY QUALIFIED here. A bare
-- lowercase global in a TYPE signature is silently auto-bound by idris2
-- 0.8.0 as a fresh implicit (warning "shadowing …"), which decouples
-- the proof from the real definition ⇒ `Refl` then cannot reduce
-- (the documented standards#124 footgun; qualification pins it).
queryPlanHeaderNoPadding :
  sumFieldSizes VclTotal.ABI.LayoutProofs.qphFields
    = VclTotal.ABI.LayoutProofs.qphTotalSize
queryPlanHeaderNoPadding = Refl

-- ═══════════════════════════════════════════════════════════════════════
-- 3. Genuine, membership-quantified field-bounds proof
-- ═══════════════════════════════════════════════════════════════════════

||| Decider: every field's `foff + fsize` fits within `cap`.
public export
allWithin : Vect len PField -> Nat -> Bool
allWithin []        _     = True
allWithin (x :: xs) cap = (foff x + fsize x <= cap) && allWithin xs cap

||| **Genuine** bounds proof: every QueryPlanHeader field's
||| `foff + fsize` is ≤ the declared cap. `allWithin qphFields 24`
||| *computes* to `True`, so the witness is `Oh`. Replaces the deleted
||| Phase-3c `?offsetInBoundsProof` hole.
public export
queryPlanHeaderWithin :
  So (allWithin VclTotal.ABI.LayoutProofs.qphFields
                VclTotal.ABI.LayoutProofs.qphTotalSize)
queryPlanHeaderWithin = Oh

||| Membership-quantified bound: any field *provably in* the vector
||| satisfies `foff + fsize <= cap`. Honest replacement for the
||| deleted `offsetInBounds` (which quantified over an arbitrary field
||| not necessarily in the layout — false in general). Proved by
||| `Data.So.soAnd` over the `&&`-fold.
public export
fieldWithin : {0 len : Nat} -> {xs : Vect len PField} -> {x : PField} ->
              (cap : Nat) -> So (allWithin xs cap) ->
              Elem x xs -> So (foff x + fsize x <= cap)
fieldWithin cap prf Here      = fst (soAnd prf)
fieldWithin cap prf (There e) = fieldWithin cap (snd (soAnd prf)) e
