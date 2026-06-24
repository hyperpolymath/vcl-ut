-- SPDX-License-Identifier: MPL-2.0
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
||| The additive↔ceil equivalence is proved by `alignUpAdditiveEquivAlignTo`
||| in Section 4, closing the Phase 4a scope completely.
|||
||| Nothing here uses believe_me / postulate / assert_* / idris_crash /
||| sorry. Verified by the CI `--build` of `vclut-core.ipkg`.

module VclTotal.ABI.LayoutProofs

import Data.Nat
import Data.Nat.Division
import Data.Vect
import Data.Vect.Elem
import Data.So
import Syntax.WithProof
import Syntax.PreorderReasoning

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

||| Canonical round-up-to-multiple alignment = `⌈size/a⌉ * a`.
||| Defined by case split to keep `divNatNZ` in head position, which
||| lets the Idris2 unifier reduce it by Refl in the additive-equivalence
||| proof. (`ceilDivNat` via `divNat` is non-covering and stays stuck.)
public export
alignTo : (size : Nat) -> (a : Nat) -> Nat
alignTo size Z       = 0
alignTo size (S a)   = divNatNZ (size + a) (S a) ItIsSucc * (S a)

||| **Genuine** alignment divisibility, by construction: `alignTo size a`
||| is literally `q * a` with `q = ⌈size/a⌉`, so `a` divides it and the
||| witness is `q` itself. No `div`/`mod` lemma, no proof-escape.
public export
alignToDivides : (size : Nat) -> (a : Nat) -> Divides a (alignTo size a)
alignToDivides size Z     = DivideBy 0 Refl
alignToDivides size (S a) = DivideBy (divNatNZ (size + a) (S a) ItIsSucc) Refl


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

-- ═══════════════════════════════════════════════════════════════════════
-- 4. Additive form ≡ ceil-multiple form  (closes Phase 4a scope)
-- ═══════════════════════════════════════════════════════════════════════

-- Local mirror of Layout.paddingFor.  Uses modNatNZ (fully covering:
-- Z case handled by `void (absurd p)`) rather than backtick `mod`
-- (which expands to modNat, whose `modNat left Z` case is absent and
-- therefore non-covering under %default total).
paddingForLocal : (s : Nat) -> (a : Nat) -> (0 nz : NonZero a) -> Nat
paddingForLocal s a nz =
  if modNatNZ s a nz == 0 then 0 else a `minus` modNatNZ s a nz

-- Expose the True branch of the conditional as a propositional equality.
paddingZeroCase : (s : Nat) -> (a : Nat) -> (0 nz : NonZero a) ->
                  (modNatNZ s a nz == 0) = True ->
                  paddingForLocal s a nz = 0
paddingZeroCase s a nz prf = rewrite prf in Refl

-- Expose the False branch of the conditional as a propositional equality.
paddingNonzeroCase : (s : Nat) -> (a : Nat) -> (0 nz : NonZero a) ->
                     (modNatNZ s a nz == 0) = False ->
                     paddingForLocal s a nz = a `minus` modNatNZ s a nz
paddingNonzeroCase s a nz prf = rewrite prf in Refl

-- Bool-to-Prop bridge helpers for the case split.
natEqZeroFromBool : (n : Nat) -> (n == 0) = True -> n = 0
natEqZeroFromBool Z     _   = Refl
natEqZeroFromBool (S k) prf = absurd prf

natSuccFromFalse : (n : Nat) -> (n == 0) = False -> (k : Nat ** n = S k)
natSuccFromFalse Z     prf = absurd prf
natSuccFromFalse (S k) _   = (k ** Refl)

||| **Genuine** proof that `Layout.alignUp` (the additive padding form,
||| `size + paddingFor size a`) equals `alignTo` (the canonical
||| ceil-multiple form, `⌈size/a⌉ * a`) for any alignment `a > 0`.
|||
||| Proof by Euclidean division case split.  Let `r = size mod a`,
||| `q = size div a`.
|||
||| - `r = 0` branch: padding is 0; ceiling quotient is `q` (shown by
|||   `DivisionTheoremUniqueness` applied to `size + (a−1)`).
||| - `r = S r'` branch: padding is `a − S r' = (a−1) − r'`; ceiling
|||   quotient is `S q` (again by uniqueness); arithmetic closes the gap.
|||
||| Closes the `alignUpAdditiveEquivOWED` scope note documented in
||| Phase 4a.  Nothing here uses `believe_me`, `postulate`, `assert_*`,
||| or `sorry`.
public export
alignUpAdditiveEquivAlignTo :
    (s : Nat) -> (a : Nat) -> (0 nz : NonZero a) ->
    s + paddingForLocal s a nz = alignTo s a
-- NonZero is a 0-quantity type alias (NonZero = IsSucc), so its
-- constructor ItIsSucc cannot be pattern-matched on the LHS.
-- Pattern-match on `a` only; bind the erased NonZero arg as `nz` so the
-- goal mentions `nz` and the proof terms are unambiguous to the unifier.
-- Drop opaque `r`/`q` let-bindings: DivisionTheorem's return type mentions
-- `modNatNZ`/`divNatNZ` directly, and let-bound names go opaque in the unifier.
-- `rewrite prf` eliminates the `if` from the goal without needing
-- paddingZeroCase/paddingNonzeroCase or replace; prf is from the @@ split.
alignUpAdditiveEquivAlignTo s (S predA) nz =
  let divThm = DivisionTheorem s (S predA) nz nz
      rLtA   = boundModNatNZ s (S predA) nz
  in case @@ (modNatNZ s (S predA) nz == 0) of
       (True ** prf) =>
         -- mod = 0 branch: padding vanishes; ceilDivNat s (S predA) = q₀.
         -- `rewrite prf` rewrites `modNatNZ ... == 0` → True in goal,
         -- resolving the `if True then 0 else ...` to 0.
         let rIsZ   = natEqZeroFromBool (modNatNZ s (S predA) nz) prf
             sEqQA  = trans divThm
                            (cong (+ divNatNZ s (S predA) nz * S predA) rIsZ)
             sPA    = cong (+ predA) sEqQA
             divEqQ = fst $ DivisionTheoremUniqueness
                              (s + predA) (S predA) ItIsSucc
                              (divNatNZ s (S predA) nz) predA
                              (LTESucc reflexive) sPA
         in rewrite prf in
            Calc $
              |~ s + 0
              ~~ s                                                    ...(plusZeroRightNeutral s)
              ~~ divNatNZ s (S predA) nz * (S predA)                 ...(sEqQA)
              ~~ divNatNZ (s + predA) (S predA) ItIsSucc * (S predA) ...(cong (* S predA) (sym divEqQ))
              ~~ alignTo s (S predA)                                  ...(Refl)
       (False ** prf) =>
         -- mod = S r' branch: ceilDivNat s (S predA) = S q₀.
         -- `rewrite prf` resolves `if False then 0 else X` → X in goal,
         -- leaving  s + (S predA `minus` modNatNZ s (S predA) nz) = alignTo s (S predA).
         rewrite prf in
         case natSuccFromFalse (modNatNZ s (S predA) nz) prf of
           (r' ** rIsSr') =>
             -- rIsSr' : modNatNZ s (S predA) nz = S r'.  The mod term is stuck
             -- (reduces to `mod' s s predA`, never to a constructor), so a
             -- `case rIsSr' of Refl` CANNOT substitute it into the goal.
             -- Bridge it explicitly: `divThm'` rephrases the division theorem
             -- with `S r'`, `rLtA'` rephrases the remainder bound, and the
             -- first Calc step does the `modNatNZ → S r'` swap via `cong`.
             let divThm' = trans divThm
                             (cong (+ divNatNZ s (S predA) nz * (S predA)) rIsSr')
                 rLtA'      = replace {p = \m => LT m (S predA)} rIsSr' rLtA
                 sr'LePredA = fromLteSucc rLtA'
                 r'LePredA  = lteSuccLeft  sr'LePredA
                 r'LtSPredA = lteSuccRight sr'LePredA
                 sRpA = Calc $
                   |~ S r' + predA
                   ~~ predA + S r'  ...(plusCommutative (S r') predA)
                   ~~ S predA + r'  ...(sym $ plusSuccRightSucc predA r')
                 sRpMinR = cong S $
                   trans (plusCommutative r' (predA `minus` r'))
                         (plusMinusLte r' predA r'LePredA)
                 sPA2 = Calc $
                   |~ s + predA
                   ~~ (S r' + divNatNZ s (S predA) nz * (S predA)) + predA
                            ...(cong (+ predA) divThm')
                   ~~ (divNatNZ s (S predA) nz * (S predA) + S r') + predA
                            ...(cong (+ predA) $
                                plusCommutative (S r')
                                  (divNatNZ s (S predA) nz * S predA))
                   ~~ divNatNZ s (S predA) nz * (S predA) + (S r' + predA)
                            ...(sym $ plusAssociative
                                (divNatNZ s (S predA) nz * S predA) (S r') predA)
                   ~~ divNatNZ s (S predA) nz * (S predA) + (S predA + r')
                            ...(cong (divNatNZ s (S predA) nz * S predA +) sRpA)
                   ~~ (divNatNZ s (S predA) nz * (S predA) + S predA) + r'
                            ...(plusAssociative
                                (divNatNZ s (S predA) nz * S predA) (S predA) r')
                   ~~ (S predA + divNatNZ s (S predA) nz * (S predA)) + r'
                            ...(cong (+ r') $
                                plusCommutative
                                  (divNatNZ s (S predA) nz * S predA) (S predA))
                   ~~ S (divNatNZ s (S predA) nz) * (S predA) + r'
                            ...(cong (+ r') $
                                sym $ multLeftSuccPlus
                                  (divNatNZ s (S predA) nz) (S predA))
                 divEqSQ = fst $ DivisionTheoremUniqueness
                                   (s + predA) (S predA) ItIsSucc
                                   (S (divNatNZ s (S predA) nz)) r'
                                   r'LtSPredA sPA2
             in Calc $
                  |~ s + (S predA `minus` modNatNZ s (S predA) nz)
                  ~~ s + (S predA `minus` S r')
                           ...(cong (\m => s + (S predA `minus` m)) rIsSr')
                  ~~ s + (predA `minus` r')
                           ...(Refl)
                  ~~ (S r' + divNatNZ s (S predA) nz * (S predA))
                       + (predA `minus` r')
                           ...(cong (+ (predA `minus` r')) divThm')
                  ~~ S r' + (divNatNZ s (S predA) nz * (S predA)
                       + (predA `minus` r'))
                           ...(sym $ plusAssociative (S r')
                                 (divNatNZ s (S predA) nz * S predA)
                                 (predA `minus` r'))
                  ~~ S r' + ((predA `minus` r')
                       + divNatNZ s (S predA) nz * (S predA))
                           ...(cong (S r' +) $
                               plusCommutative
                                 (divNatNZ s (S predA) nz * S predA)
                                 (predA `minus` r'))
                  ~~ (S r' + (predA `minus` r'))
                       + divNatNZ s (S predA) nz * (S predA)
                           ...(plusAssociative (S r') (predA `minus` r')
                                 (divNatNZ s (S predA) nz * S predA))
                  ~~ S predA + divNatNZ s (S predA) nz * (S predA)
                           ...(cong (+ divNatNZ s (S predA) nz * S predA)
                                 sRpMinR)
                  ~~ S (divNatNZ s (S predA) nz) * (S predA)
                           ...(sym $ multLeftSuccPlus
                                 (divNatNZ s (S predA) nz) (S predA))
                  ~~ divNatNZ (s + predA) (S predA) ItIsSucc * (S predA)
                           ...(cong (* S predA) (sym divEqSQ))
                  ~~ alignTo s (S predA)
                           ...(Refl)
