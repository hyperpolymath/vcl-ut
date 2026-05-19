-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Composition.idr — Proof of Theorem [Composition Preservation]
--
-- Proves that the 10-level VCL-ut safety hierarchy is closed under
-- relational query composition (join):
--
--   Theorem (Composition Preservation):
--     For all k in {0..10} and queries q1, q2 over the same schema:
--       SafetyCertificate q1 schema k
--         -> SafetyCertificate q2 schema k
--         -> SafetyCertificate (composeJoin q1 q2) schema k
--
-- HONESTY NOTE (standards#124, vcl-ut HOLE remediation, Phase 1).
-- This module never compiled on origin/main (forward references, `cong`
-- sections with un-inferrable holes, references to the deleted vacuous
-- `AllParameterised` constructor, wrong `CertL6+` arities, and `rewrite`s
-- whose redex never appeared in the goal). It has been re-derived so that
-- it typechecks under idris2 0.8.0 with `%default total` and ZERO
-- believe_me / really_believe_me / postulate / assert_total / idris_crash
-- / sorry.
--
-- The L4 (injection-freedom) composition is GENUINE: `noRawUserInputCompose`
-- proves the joined WHERE introduces no string literal absent from either
-- input, matching verification/proofs/SafetyL4Model.idr. The L1 (schema
-- binding) composition is GENUINE: a real list-membership subset proof.
-- L2/L3/L5 are constructed at the correct *indexed* type but remain
-- evidentially weak because the L2/L3/L5 predicates themselves are still
-- vacuous (NOT yet de-vacuized — that is Phase 2). This weakness is real,
-- carries no proof-escape symbol, and is scoped OWED in
-- verification/proofs/VERIFICATION-STANCE.adoc. L6..L10 are GENUINE
-- equational proofs about the join* combiners.

module VclTotal.Core.Composition

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import VclTotal.Core.Decide
import VclTotal.Core.Levels
import Data.List
import Data.List.Elem

%default total

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 1: list / membership helper lemmas
-- ══════════════════════════════════════════════════════════════════════

||| `selectFieldRefs` distributes over list append.
export
selectFieldRefsAppend :
  (items1, items2 : List SelectItem) ->
  selectFieldRefs (items1 ++ items2)
    = selectFieldRefs items1 ++ selectFieldRefs items2
selectFieldRefsAppend []                         _      = Refl
selectFieldRefsAppend (SelField ref :: rest)     items2 =
  cong (ref ::) (selectFieldRefsAppend rest items2)
selectFieldRefsAppend (SelModality _ :: rest)    items2 =
  selectFieldRefsAppend rest items2
selectFieldRefsAppend (SelAggregate _ _ :: rest) items2 =
  selectFieldRefsAppend rest items2
selectFieldRefsAppend (SelStar :: rest)          items2 =
  selectFieldRefsAppend rest items2

||| `map fst` distributes over list append.
mapFstAppend :
  (xs, ys : List (a, b)) ->
  map Builtin.fst (xs ++ ys) = map Builtin.fst xs ++ map Builtin.fst ys
mapFstAppend []              _  = Refl
mapFstAppend ((x, _) :: xs)  ys = cong (x ::) (mapFstAppend xs ys)

||| An element of `xs` is an element of `xs ++ ys`.
elemAppendLeft : Elem x xs -> Elem x (xs ++ ys)
elemAppendLeft Here      = Here
elemAppendLeft (There e) = There (elemAppendLeft e)

||| An element of `ys` is an element of `xs ++ ys`.
elemAppendRight : (xs : List a) -> Elem x ys -> Elem x (xs ++ ys)
elemAppendRight []        e = e
elemAppendRight (_ :: xs) e = There (elemAppendRight xs e)

||| Split membership in an append into membership in one side.
||| `xs` is an ordinary (unrestricted) implicit so it can be matched on.
elemAppendSplit :
  {xs : List a} -> Elem x (xs ++ ys) -> Either (Elem x xs) (Elem x ys)
elemAppendSplit {xs = []}        e         = Right e
elemAppendSplit {xs = _ :: _}    Here      = Left Here
elemAppendSplit {xs = _ :: xs'} (There e)  =
  case elemAppendSplit {xs = xs'} e of
    Left  l => Left (There l)
    Right r => Right r

||| Transport an `Elem` proof along a list equality.
elemCast : (0 _ : as = bs) -> Elem x as -> Elem x bs
elemCast prf e = replace {p = \l => Elem x l} prf e

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 2: the composition operation
-- ══════════════════════════════════════════════════════════════════════

||| Combine WHERE clauses with AND conjunction.
export
joinWhere : Maybe Expr -> Maybe Expr -> Maybe Expr
joinWhere Nothing   Nothing   = Nothing
joinWhere (Just w)  Nothing   = Just w
joinWhere Nothing   (Just w)  = Just w
joinWhere (Just w1) (Just w2) = Just (ELogic And w1 (Just w2) TBool)

||| Combine effect declarations: union of effects.
joinEffects : Maybe EffectDecl -> Maybe EffectDecl -> Maybe EffectDecl
joinEffects Nothing             e                  = e
joinEffects e                   Nothing             = e
joinEffects (Just EffRead)      (Just EffWrite)     = Just EffReadWrite
joinEffects (Just EffWrite)     (Just EffRead)      = Just EffReadWrite
joinEffects (Just EffReadWrite) _                   = Just EffReadWrite
joinEffects _                   (Just EffReadWrite) = Just EffReadWrite
joinEffects (Just e1)           _                   = Just e1

||| Combine version constraints: tighten to latest.
joinVersion : Maybe VersionConstraint -> Maybe VersionConstraint
           -> Maybe VersionConstraint
joinVersion Nothing                 v                         = v
joinVersion v                       Nothing                   = v
joinVersion (Just VerLatest)        _                         = Just VerLatest
joinVersion _                       (Just VerLatest)          = Just VerLatest
joinVersion (Just (VerAtLeast n1))  (Just (VerAtLeast n2))    =
  Just (VerAtLeast (max n1 n2))
joinVersion (Just (VerExact n))     _                         = Just (VerExact n)
joinVersion _                       (Just (VerExact n))       = Just (VerExact n)
joinVersion (Just (VerRange l1 h1)) (Just (VerRange l2 h2))   =
  Just (VerRange (max l1 l2) (min h1 h2))
joinVersion v                       _                         = v

||| Combine linearity annotations: stricter wins.
joinLinear : Maybe LinearAnnotation -> Maybe LinearAnnotation
          -> Maybe LinearAnnotation
-- Explicit, exhaustive clauses: unlike joinEffects/joinVersion this
-- combiner has no final catch-all variable clause, so Idris's coverage
-- checker needs every Just/Just constructor pairing spelled out.
joinLinear Nothing                Nothing                = Nothing
joinLinear (Just a)               Nothing                = Just a
joinLinear Nothing                (Just b)               = Just b
joinLinear (Just LinUnlimited)    (Just LinUnlimited)    = Just LinUnlimited
joinLinear (Just LinUnlimited)    (Just LinUseOnce)      = Just LinUseOnce
joinLinear (Just LinUnlimited)    (Just (LinBounded n))  = Just (LinBounded n)
joinLinear (Just LinUseOnce)      (Just LinUnlimited)    = Just LinUseOnce
joinLinear (Just LinUseOnce)      (Just LinUseOnce)      = Just LinUseOnce
joinLinear (Just LinUseOnce)      (Just (LinBounded _))  = Just LinUseOnce
joinLinear (Just (LinBounded n))  (Just LinUnlimited)    = Just (LinBounded n)
joinLinear (Just (LinBounded _))  (Just LinUseOnce)      = Just LinUseOnce
joinLinear (Just (LinBounded n1)) (Just (LinBounded n2)) =
  Just (LinBounded (min n1 n2))

||| Combine epistemic clauses: union of agents and requirements.
joinEpistemic : Maybe EpistemicClause -> Maybe EpistemicClause
             -> Maybe EpistemicClause
joinEpistemic Nothing                     ec                       = ec
joinEpistemic ec                          Nothing                  = ec
joinEpistemic (Just (EpClause as1 rs1))   (Just (EpClause as2 rs2)) =
  Just (EpClause (as1 ++ as2) (rs1 ++ rs2))

||| Combine LIMIT clauses: take the minimum (stricter bound).
joinLimit : Maybe Nat -> Maybe Nat -> Maybe Nat
joinLimit Nothing   n         = n
joinLimit n         Nothing   = n
joinLimit (Just n1) (Just n2) = Just (min n1 n2)

||| Relational join of two queries.
||| Both queries are assumed to target the same source octad
||| (the `Composable` precondition).
export
composeJoin : Statement -> Statement -> Statement
composeJoin q1 q2 = MkStatement
  (selectItems q1 ++ selectItems q2)
  (source q1)
  (joinWhere (whereClause q1) (whereClause q2))
  (groupBy q1 ++ groupBy q2)
  Nothing                                        -- HAVING dropped in join
  (orderBy q1 ++ orderBy q2)
  (joinLimit (limit q1) (limit q2))
  (offset q1)
  Nothing                                        -- PROOF clause dropped
  (joinEffects (effectDecl q1) (effectDecl q2))
  (joinVersion (versionConst q1) (versionConst q2))
  (joinLinear (linearAnnot q1) (linearAnnot q2))
  (joinEpistemic (epistemicClause q1) (epistemicClause q2))
  (requestedLevel q1)

||| Two queries are composable if they target the same source octad.
public export
data Composable : Statement -> Statement -> Type where
  MkComposable : source q1 = source q2 -> Composable q1 q2

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 3: L1 (schema binding) is GENUINELY preserved
-- ══════════════════════════════════════════════════════════════════════

||| AllFieldsBound is closed under list append.
export
allFieldsBoundAppend :
  AllFieldsBound refs1 schema ->
  AllFieldsBound refs2 schema ->
  AllFieldsBound (refs1 ++ refs2) schema
allFieldsBoundAppend NilBound         ys = ys
allFieldsBoundAppend (ConsBound x xs) ys = ConsBound x (allFieldsBoundAppend xs ys)

||| Look up the binding witness for one ref via membership evidence.
boundLookup :
  AllFieldsBound refs schema -> Elem ref refs -> FieldBound ref schema
boundLookup (ConsBound fb _)   Here      = fb
boundLookup (ConsBound _ rest) (There e) = boundLookup rest e

||| Build AllFieldsBound from an element-wise lookup.
allFieldsBoundFromElem :
  (refs : List FieldRef) ->
  (schema : OctadSchema) ->
  ((ref : FieldRef) -> Elem ref refs -> FieldBound ref schema) ->
  AllFieldsBound refs schema
allFieldsBoundFromElem []            _      _ = NilBound
allFieldsBoundFromElem (ref :: rest) schema f =
  ConsBound (f ref Here)
            (allFieldsBoundFromElem rest schema (\r, prf => f r (There prf)))

||| AllFieldsBound respects list subset (every member of xs is a member of ys).
allFieldsBoundSubset :
  {xs : List FieldRef} ->
  {schema : OctadSchema} ->
  AllFieldsBound ys schema ->
  ((ref : FieldRef) -> Elem ref xs -> Elem ref ys) ->
  AllFieldsBound xs schema
allFieldsBoundSubset {xs} {schema} bound f =
  allFieldsBoundFromElem xs schema (\ref, prf => boundLookup bound (f ref prf))

||| The single field-ref of one statement landing in `extractFieldRefs`.
||| `extractFieldRefs q` definitionally unfolds to
|||   selectFieldRefs (selectItems q)
|||   ++ exprFieldRefs (whereClause q)
|||   ++ groupBy q
|||   ++ exprFieldRefs (having q)
|||   ++ map fst (orderBy q)
||| so each clause is a tower of `elemAppendLeft/Right`.
inExtractSel : (q : Statement) ->
  Elem ref (selectFieldRefs (selectItems q)) -> Elem ref (extractFieldRefs q)
inExtractSel _ e = elemAppendLeft e

inExtractWhere : (q : Statement) ->
  Elem ref (exprFieldRefs (whereClause q)) -> Elem ref (extractFieldRefs q)
inExtractWhere q e =
  elemAppendRight (selectFieldRefs (selectItems q)) (elemAppendLeft e)

inExtractGroup : (q : Statement) ->
  Elem ref (groupBy q) -> Elem ref (extractFieldRefs q)
inExtractGroup q e =
  elemAppendRight (selectFieldRefs (selectItems q))
    (elemAppendRight (exprFieldRefs (whereClause q)) (elemAppendLeft e))

inExtractOrder : (q : Statement) ->
  Elem ref (map Builtin.fst (orderBy q)) -> Elem ref (extractFieldRefs q)
inExtractOrder q e =
  elemAppendRight (selectFieldRefs (selectItems q))
    (elemAppendRight (exprFieldRefs (whereClause q))
      (elemAppendRight (groupBy q)
        (elemAppendRight (exprFieldRefs (having q)) e)))

||| The joined WHERE introduces no field-ref absent from both inputs.
whereRefsSubset :
  (w1m, w2m : Maybe Expr) ->
  Elem ref (exprFieldRefs (joinWhere w1m w2m)) ->
  Either (Elem ref (exprFieldRefs w1m)) (Elem ref (exprFieldRefs w2m))
whereRefsSubset Nothing   Nothing   e = absurd e
whereRefsSubset (Just _)  Nothing   e = Left e
whereRefsSubset Nothing   (Just _)  e = Right e
whereRefsSubset (Just a)  (Just b)  e =
  -- joinWhere (Just a) (Just b) = Just (ELogic And a (Just b) TBool), and
  -- exprFieldRefs of that = exprFieldRefs (Just a) ++ exprFieldRefs (Just b)
  elemAppendSplit {xs = exprFieldRefs (Just a)} e

||| **Genuine** subset lemma: every field-ref of the composed query was
||| already a field-ref of `q1` or of `q2`. This is the engine of L1
||| composition; the original file's attempt did not typecheck.
export
composeJoinFieldsSubset :
  (q1, q2 : Statement) -> (ref : FieldRef) ->
  Elem ref (extractFieldRefs (composeJoin q1 q2)) ->
  Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
composeJoinFieldsSubset q1 q2 ref e =
  let inL : Elem ref (extractFieldRefs q1)
         -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
      inL = elemAppendLeft
      inR : Elem ref (extractFieldRefs q2)
         -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
      inR = elemAppendRight (extractFieldRefs q1)
  in
  -- extractFieldRefs (composeJoin q1 q2) unfolds to a 5-way append:
  --   sel(q1++q2) ++ where(join) ++ (g1++g2) ++ [] ++ ord(q1++q2)
  case elemAppendSplit
         {xs = selectFieldRefs (selectItems q1 ++ selectItems q2)} e of
    Left esel =>
      case elemAppendSplit {xs = selectFieldRefs (selectItems q1)}
             (elemCast (selectFieldRefsAppend (selectItems q1)
                                               (selectItems q2)) esel) of
        Left  l => inL (inExtractSel q1 l)
        Right r => inR (inExtractSel q2 r)
    Right rest1 =>
      case elemAppendSplit
             {xs = exprFieldRefs (joinWhere (whereClause q1) (whereClause q2))}
             rest1 of
        Left ewh =>
          case whereRefsSubset (whereClause q1) (whereClause q2) ewh of
            Left  l => inL (inExtractWhere q1 l)
            Right r => inR (inExtractWhere q2 r)
        Right rest2 =>
          case elemAppendSplit {xs = groupBy q1 ++ groupBy q2} rest2 of
            Left egrp =>
              case elemAppendSplit {xs = groupBy q1} egrp of
                Left  l => inL (inExtractGroup q1 l)
                Right r => inR (inExtractGroup q2 r)
            Right rest3 =>
              -- having (composeJoin ..) = Nothing, exprFieldRefs Nothing = []
              case elemAppendSplit
                     {xs = exprFieldRefs (the (Maybe Expr) Nothing)} rest3 of
                Left  eh  => absurd eh
                Right eord =>
                  case elemAppendSplit {xs = map Builtin.fst (orderBy q1)}
                         (elemCast (mapFstAppend (orderBy q1) (orderBy q2))
                                   eord) of
                    Left  l => inL (inExtractOrder q1 l)
                    Right r => inR (inExtractOrder q2 r)

||| L1 schema binding is preserved by `composeJoin`.
l1Compose :
  L1_SchemaBound q1 schema -> L1_SchemaBound q2 schema ->
  L1_SchemaBound (composeJoin q1 q2) schema
l1Compose (MkL1 s1 sch b1) (MkL1 s2 _ b2) =
  MkL1 (composeJoin s1 s2) sch $
    allFieldsBoundSubset (allFieldsBoundAppend b1 b2)
      (composeJoinFieldsSubset s1 s2)

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 4: L4 injection-freedom is GENUINELY preserved
-- ══════════════════════════════════════════════════════════════════════

||| If both disjuncts are `False`, the disjunction is `False`.
||| (Matching `prf : x = False` forces `x = False`, so `x || y`
||| reduces to `y`.)
orBothFalse : {x : Bool} -> {y : Bool} -> x = False -> y = False -> (x || y) = False
orBothFalse Refl py = py

-- `Prelude.maybe`'s `Lazy` first argument wraps the relevant terms in
-- `Delay`, which repeatedly wedged the unifier (identical-looking terms
-- failing to converge). The L4 core is therefore phrased with a plain,
-- non-lazy `wsl` ("where-string-literal"); a one-line `wslEq` bridges
-- back to `whereHasStringLit`'s `maybe`-based definition exactly once.

||| Plain (non-lazy) "does this optional WHERE embed a string literal".
wsl : Maybe Expr -> Bool
wsl Nothing  = False
wsl (Just e) = hasStringLit e

||| Bridge: `wsl` agrees with `whereHasStringLit`'s `maybe` body.
||| `hasStringLit` is fully qualified: a bare lowercase occurrence in a
||| TYPE signature is auto-bound by Idris 2 as a fresh implicit (it warns
||| "shadowing VclTotal.Core.Grammar.hasStringLit"), which silently
||| decoupled this lemma from the real predicate. Qualification pins it.
wslEq : (m : Maybe Expr)
     -> wsl m = maybe False VclTotal.Core.Grammar.hasStringLit m
wslEq Nothing  = Refl
wslEq (Just _) = Refl

||| The AND-conjoined join, in `wsl` form, is the disjunction of sides.
||| Single isolated top-level `Refl` (joinWhere/wsl/hasStringLit on the
||| concrete `ELogic` node all reduce — reliable at top level, as the
||| standalone-module probe confirmed). No `maybe`, no `Delay`.
wslJoinConjoin : (a, b : Expr) ->
  wsl (joinWhere (Just a) (Just b)) = (wsl (Just a) || wsl (Just b))
wslJoinConjoin _ _ = Refl

||| Both-WHERE-present case. `trans` of two already-typed lemmas; the
||| result type is syntactically `wslJoinConjoin`'s LHS, so the final
||| check needs no reduction at all.
wslJoinJJ : (a, b : Expr) ->
  wsl (Just a) = False -> wsl (Just b) = False ->
  wsl (joinWhere (Just a) (Just b)) = False
wslJoinJJ a b p1 p2 = trans (wslJoinConjoin a b) (orBothFalse p1 p2)

||| The joined WHERE embeds a string literal only if one input did.
wslJoin :
  (w1m, w2m : Maybe Expr) ->
  wsl w1m = False -> wsl w2m = False ->
  wsl (joinWhere w1m w2m) = False
wslJoin Nothing   Nothing   _  _  = Refl
wslJoin (Just _)  Nothing   p1 _  = p1
wslJoin Nothing   (Just _)  _  p2 = p2
wslJoin (Just a)  (Just b)  p1 p2 = wslJoinJJ a b p1 p2

||| **Genuine** L4 composition (matches verification/proofs/SafetyL4Model.idr,
||| lemma `noRawUserInputCompose`). Replaces the historical
||| `MkL4 _ AllParameterised`, which only typechecked because the L4
||| predicate was vacuous. See standards#124.
|||
||| `whereHasStringLit s` is `maybe False hasStringLit (whereClause s)`;
||| `wslEq` rewrites that to `wsl (whereClause s)` so the genuine
||| `wslJoin` argument can discharge it.
export
noRawUserInputCompose :
  (q1, q2 : Statement) ->
  NoRawUserInput q1 -> NoRawUserInput q2 ->
  NoRawUserInput (composeJoin q1 q2)
noRawUserInputCompose q1 q2 (MkNoRawUserInput n1) (MkNoRawUserInput n2) =
  let g1 : (wsl (whereClause q1) = False)
      g1 = trans (wslEq (whereClause q1)) n1
      g2 : (wsl (whereClause q2) = False)
      g2 = trans (wslEq (whereClause q2)) n2
  in MkNoRawUserInput
       (trans (sym (wslEq (joinWhere (whereClause q1) (whereClause q2))))
              (wslJoin (whereClause q1) (whereClause q2) g1 g2))

||| L4 certificate composition.
l4Compose :
  L4_InjectionProof q1 -> L4_InjectionProof q2 ->
  L4_InjectionProof (composeJoin q1 q2)
l4Compose (MkL4 s1 n1) (MkL4 s2 n2) =
  MkL4 (composeJoin s1 s2) (noRawUserInputCompose s1 s2 n1 n2)

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 5: L2 / L3 / L5 — correct indexed construction
--            (predicates remain vacuous; OWED, see VERIFICATION-STANCE)
-- ══════════════════════════════════════════════════════════════════════

||| L2: the joined WHERE is Nothing, one verbatim side, or an `ELogic And`.
||| For the verbatim sides we *reuse the input witness* (not a fresh
||| catch-all); the conjoined node uses `LogicSafe`, the (still vacuous)
||| L2 constructor.
joinWhereTypeSafe :
  (w1m, w2m : Maybe Expr) ->
  AllComparisonsTypeSafe w1m sch -> AllComparisonsTypeSafe w2m sch ->
  AllComparisonsTypeSafe (joinWhere w1m w2m) sch
joinWhereTypeSafe Nothing   Nothing   NoWhere            NoWhere            = NoWhere
joinWhereTypeSafe (Just _)  Nothing   (WhereTypeSafe e1) NoWhere            = WhereTypeSafe e1
joinWhereTypeSafe Nothing   (Just _)  NoWhere            (WhereTypeSafe e2) = WhereTypeSafe e2
joinWhereTypeSafe (Just _)  (Just _)  (WhereTypeSafe _)  (WhereTypeSafe _)  = WhereTypeSafe LogicSafe

l2Compose :
  L2_TypeCompat q1 schema -> L2_TypeCompat q2 schema ->
  L2_TypeCompat (composeJoin q1 q2) schema
l2Compose (MkL2 s1 sch a1) (MkL2 s2 _ a2) =
  MkL2 (composeJoin s1 s2) sch
    (joinWhereTypeSafe (whereClause s1) (whereClause s2) a1 a2)

||| L3: `AllNullableFieldsGuarded` only distinguishes `Nothing` from
||| `Just _`; the join is `Just _` whenever either input was.
joinWhereNullGuarded :
  (w1m, w2m : Maybe Expr) ->
  AllNullableFieldsGuarded w1m sch -> AllNullableFieldsGuarded w2m sch ->
  AllNullableFieldsGuarded (joinWhere w1m w2m) sch
joinWhereNullGuarded Nothing  Nothing  NoWhereNull NoWhereNull = NoWhereNull
joinWhereNullGuarded (Just _) Nothing  GuardedNull NoWhereNull = GuardedNull
joinWhereNullGuarded Nothing  (Just _) NoWhereNull GuardedNull = GuardedNull
joinWhereNullGuarded (Just _) (Just _) GuardedNull GuardedNull = GuardedNull

l3Compose :
  L3_NullSafe q1 schema -> L3_NullSafe q2 schema ->
  L3_NullSafe (composeJoin q1 q2) schema
l3Compose (MkL3 s1 sch a1) (MkL3 s2 _ a2) =
  MkL3 (composeJoin s1 s2) sch
    (joinWhereNullGuarded (whereClause s1) (whereClause s2) a1 a2)

||| **Genuine** L5 closure. `AllSelectItemsTyped` now carries
||| `selectItemsTyped items sch = True`; `composeJoin` concatenates the
||| SELECT lists and `selectItemTyped` is per-item / context-free, so the
||| joined list is typed iff both inputs were — discharged by the real
||| `Decide.selectItemsTypedAppend` induction. No vacuous constructor.
selTypedAppend :
  {xs, ys : List SelectItem} -> {sch : OctadSchema} ->
  AllSelectItemsTyped xs sch -> AllSelectItemsTyped ys sch ->
  AllSelectItemsTyped (xs ++ ys) sch
selTypedAppend {xs} {ys} {sch} (MkAllSelTyped p1) (MkAllSelTyped p2) =
  MkAllSelTyped (selectItemsTypedAppend xs ys sch p1 p2)

l5Compose :
  L5_ResultTyped q1 schema -> L5_ResultTyped q2 schema ->
  L5_ResultTyped (composeJoin q1 q2) schema
l5Compose (MkL5 s1 sch t1) (MkL5 s2 _ t2) =
  MkL5 (composeJoin s1 s2) sch (selTypedAppend t1 t2)

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 6: L6..L10 — GENUINE equational proofs about join* combiners
-- ══════════════════════════════════════════════════════════════════════

||| `joinLimit (Just a) (Just b)` is `Just (min a b)` — definitional.
l6Compose : L6_CardinalitySafe q1 -> L6_CardinalitySafe q2 ->
            L6_CardinalitySafe (composeJoin q1 q2)
l6Compose (MkL6 s1 n1 p1) (MkL6 s2 n2 p2) =
  MkL6 (composeJoin s1 s2) (min n1 n2) (rewrite p1 in rewrite p2 in Refl)

||| For any two `EffectDecl`s, `joinEffects (Just a) (Just b)` is `Just _`.
joinEffectsJust : (a, b : EffectDecl)
               -> (c : EffectDecl ** joinEffects (Just a) (Just b) = Just c)
joinEffectsJust EffRead      EffRead      = (_ ** Refl)
joinEffectsJust EffRead      EffWrite     = (_ ** Refl)
joinEffectsJust EffRead      EffReadWrite = (_ ** Refl)
joinEffectsJust EffRead      EffConsume   = (_ ** Refl)
joinEffectsJust EffWrite     EffRead      = (_ ** Refl)
joinEffectsJust EffWrite     EffWrite     = (_ ** Refl)
joinEffectsJust EffWrite     EffReadWrite = (_ ** Refl)
joinEffectsJust EffWrite     EffConsume   = (_ ** Refl)
joinEffectsJust EffReadWrite EffRead      = (_ ** Refl)
joinEffectsJust EffReadWrite EffWrite     = (_ ** Refl)
joinEffectsJust EffReadWrite EffReadWrite = (_ ** Refl)
joinEffectsJust EffReadWrite EffConsume   = (_ ** Refl)
joinEffectsJust EffConsume   EffRead      = (_ ** Refl)
joinEffectsJust EffConsume   EffWrite     = (_ ** Refl)
joinEffectsJust EffConsume   EffReadWrite = (_ ** Refl)
joinEffectsJust EffConsume   EffConsume   = (_ ** Refl)

l7Compose : L7_EffectTracked q1 -> L7_EffectTracked q2 ->
            L7_EffectTracked (composeJoin q1 q2)
l7Compose (MkL7 s1 e1 p1) (MkL7 s2 e2 p2) =
  let (c ** q) = joinEffectsJust e1 e2
  in MkL7 (composeJoin s1 s2) c (rewrite p1 in rewrite p2 in q)

||| For any two `VersionConstraint`s, `joinVersion (Just a) (Just b)` is
||| `Just _` (case split on the four constructor shapes; Nat payloads
||| stay abstract).
joinVersionJust : (a, b : VersionConstraint)
  -> (c : VersionConstraint ** joinVersion (Just a) (Just b) = Just c)
joinVersionJust VerLatest       _               = (_ ** Refl)
joinVersionJust (VerAtLeast _)  VerLatest       = (_ ** Refl)
joinVersionJust (VerAtLeast _)  (VerAtLeast _)  = (_ ** Refl)
joinVersionJust (VerAtLeast _)  (VerExact _)    = (_ ** Refl)
joinVersionJust (VerAtLeast _)  (VerRange _ _)  = (_ ** Refl)
joinVersionJust (VerExact _)    VerLatest       = (_ ** Refl)
joinVersionJust (VerExact _)    (VerAtLeast _)  = (_ ** Refl)
joinVersionJust (VerExact _)    (VerExact _)    = (_ ** Refl)
joinVersionJust (VerExact _)    (VerRange _ _)  = (_ ** Refl)
joinVersionJust (VerRange _ _)  VerLatest       = (_ ** Refl)
joinVersionJust (VerRange _ _)  (VerAtLeast _)  = (_ ** Refl)
joinVersionJust (VerRange _ _)  (VerExact _)    = (_ ** Refl)
joinVersionJust (VerRange _ _)  (VerRange _ _)  = (_ ** Refl)

l8Compose : L8_TemporalSafe q1 -> L8_TemporalSafe q2 ->
            L8_TemporalSafe (composeJoin q1 q2)
l8Compose (MkL8 s1 v1 p1) (MkL8 s2 v2 p2) =
  let (c ** q) = joinVersionJust v1 v2
  in MkL8 (composeJoin s1 s2) c (rewrite p1 in rewrite p2 in q)

||| For any two `LinearAnnotation`s, `joinLinear (Just a) (Just b)` is
||| `Just _`.
joinLinearJust : (a, b : LinearAnnotation)
  -> (c : LinearAnnotation ** joinLinear (Just a) (Just b) = Just c)
joinLinearJust LinUnlimited   LinUnlimited   = (_ ** Refl)
joinLinearJust LinUnlimited   LinUseOnce     = (_ ** Refl)
joinLinearJust LinUnlimited   (LinBounded _) = (_ ** Refl)
joinLinearJust LinUseOnce     LinUnlimited   = (_ ** Refl)
joinLinearJust LinUseOnce     LinUseOnce     = (_ ** Refl)
joinLinearJust LinUseOnce     (LinBounded _) = (_ ** Refl)
joinLinearJust (LinBounded _) LinUnlimited   = (_ ** Refl)
joinLinearJust (LinBounded _) LinUseOnce     = (_ ** Refl)
joinLinearJust (LinBounded _) (LinBounded _) = (_ ** Refl)

l9Compose : L9_LinearSafe q1 -> L9_LinearSafe q2 ->
            L9_LinearSafe (composeJoin q1 q2)
l9Compose (MkL9 s1 a1 p1) (MkL9 s2 a2 p2) =
  let (c ** q) = joinLinearJust a1 a2
  in MkL9 (composeJoin s1 s2) c (rewrite p1 in rewrite p2 in q)

||| `joinEpistemic (Just (EpClause ..)) (Just (EpClause ..))` is `Just _`.
joinEpistemicJust : (a, b : EpistemicClause)
  -> (c : EpistemicClause ** joinEpistemic (Just a) (Just b) = Just c)
joinEpistemicJust (EpClause _ _) (EpClause _ _) = (_ ** Refl)

l10Compose : L10_EpistemicSafe q1 -> L10_EpistemicSafe q2 ->
             L10_EpistemicSafe (composeJoin q1 q2)
l10Compose (MkL10 s1 c1 p1) (MkL10 s2 c2 p2) =
  let (c ** q) = joinEpistemicJust c1 c2
  in MkL10 (composeJoin s1 s2) c (rewrite p1 in rewrite p2 in q)

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 7: the main theorem
-- ══════════════════════════════════════════════════════════════════════

||| Theorem [Composition Preservation]. The 10-level safety hierarchy is
||| closed under relational join: a level-k certificate for q1 and q2
||| yields a level-k certificate for `composeJoin q1 q2`.
|||
||| L0/L1/L4/L6..L10 are genuine. L2/L3/L5 are produced at the correct
||| indexed type by `lN Compose`, but the L2/L3/L5 predicates are still
||| vacuous (Phase 2 work) — disclosed OWED in VERIFICATION-STANCE.adoc.
export
compositionPreservation :
  (q1, q2 : Statement) ->
  (schema : OctadSchema) ->
  (k : SafetyLevel) ->
  Composable q1 q2 ->
  SafetyCertificate q1 schema k ->
  SafetyCertificate q2 schema k ->
  SafetyCertificate (composeJoin q1 q2) schema k
compositionPreservation q1 q2 _ ParseSafe _ _ _ =
  CertL0 (MkL0 (composeJoin q1 q2))
compositionPreservation q1 q2 _ SchemaBound _
    (CertL1 _ l1a) (CertL1 _ l1b) =
  CertL1 (MkL0 (composeJoin q1 q2)) (l1Compose l1a l1b)
compositionPreservation q1 q2 _ TypeCompat _
    (CertL2 _ l1a l2a) (CertL2 _ l1b l2b) =
  CertL2 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b)
compositionPreservation q1 q2 _ NullSafe _
    (CertL3 _ l1a l2a l3a) (CertL3 _ l1b l2b l3b) =
  CertL3 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
compositionPreservation q1 q2 _ InjectionProof _
    (CertL4 _ l1a l2a l3a l4a) (CertL4 _ l1b l2b l3b l4b) =
  CertL4 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
         (l4Compose l4a l4b)
compositionPreservation q1 q2 _ ResultTyped _
    (CertL5 _ l1a l2a l3a l4a l5a) (CertL5 _ l1b l2b l3b l4b l5b) =
  CertL5 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
         (l4Compose l4a l4b) (l5Compose l5a l5b)
compositionPreservation q1 q2 _ CardinalitySafe _
    (CertL6 _ l1a l2a l3a l4a l5a l6a)
    (CertL6 _ l1b l2b l3b l4b l5b l6b) =
  CertL6 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
         (l4Compose l4a l4b) (l5Compose l5a l5b) (l6Compose l6a l6b)
compositionPreservation q1 q2 _ EffectTracked _
    (CertL7 _ l1a l2a l3a l4a l5a l6a l7a)
    (CertL7 _ l1b l2b l3b l4b l5b l6b l7b) =
  CertL7 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
         (l4Compose l4a l4b) (l5Compose l5a l5b) (l6Compose l6a l6b)
         (l7Compose l7a l7b)
compositionPreservation q1 q2 _ TemporalSafe _
    (CertL8 _ l1a l2a l3a l4a l5a l6a l7a l8a)
    (CertL8 _ l1b l2b l3b l4b l5b l6b l7b l8b) =
  CertL8 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
         (l4Compose l4a l4b) (l5Compose l5a l5b) (l6Compose l6a l6b)
         (l7Compose l7a l7b) (l8Compose l8a l8b)
compositionPreservation q1 q2 _ LinearSafe _
    (CertL9 _ l1a l2a l3a l4a l5a l6a l7a l8a l9a)
    (CertL9 _ l1b l2b l3b l4b l5b l6b l7b l8b l9b) =
  CertL9 (MkL0 (composeJoin q1 q2))
         (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
         (l4Compose l4a l4b) (l5Compose l5a l5b) (l6Compose l6a l6b)
         (l7Compose l7a l7b) (l8Compose l8a l8b) (l9Compose l9a l9b)
compositionPreservation q1 q2 _ EpistemicSafe _
    (CertL10 _ l1a l2a l3a l4a l5a l6a l7a l8a l9a l10a)
    (CertL10 _ l1b l2b l3b l4b l5b l6b l7b l8b l9b l10b) =
  CertL10 (MkL0 (composeJoin q1 q2))
          (l1Compose l1a l1b) (l2Compose l2a l2b) (l3Compose l3a l3b)
          (l4Compose l4a l4b) (l5Compose l5a l5b) (l6Compose l6a l6b)
          (l7Compose l7a l7b) (l8Compose l8a l8b) (l9Compose l9a l9b)
          (l10Compose l10a l10b)
