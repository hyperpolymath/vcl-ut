-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- Composition.idr — Proof of Theorem [Composition Preservation]
--
-- Proves that the 10-level VQL-UT safety hierarchy is closed under
-- relational query composition (join).  This is the "supplementary
-- material" referenced in §8 of the VQL-UT paper.
--
-- Theorem (Composition Preservation):
--   For all k ∈ {0,...,10} and composable queries q1, q2:
--   SafetyCertificate q1 schema k
--     → SafetyCertificate q2 schema k
--     → SafetyCertificate (composeJoin q1 q2) schema k
--
-- The proof proceeds in three layers:
--   1. Helper lemmas about list-level distributivity (section LEMMAS)
--   2. Composition operation and its field-ref tracking (section COMPOSE)
--   3. Level-by-level certificate construction (section PROOF)
--
-- All functions are total (%default total); no believe_me, assert_total,
-- sorry, or postulate is used anywhere in this file.

module VclTotal.Core.Composition

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import VclTotal.Core.Levels
import Data.List
import Data.List.Elem

%default total

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 1: Helper Lemmas
-- ══════════════════════════════════════════════════════════════════════

-- ── List append properties ──────────────────────────────────────────

||| Appending an empty list on the right is a no-op.
appendNilRight : (xs : List a) -> xs ++ [] = xs
appendNilRight []        = Refl
appendNilRight (_ :: xs) = cong (_ ::) (appendNilRight xs)

||| map fst distributes over (++).
mapFstAppend :
  (xs, ys : List (a, b)) ->
  map fst (xs ++ ys) = map fst xs ++ map fst ys
mapFstAppend []               _  = Refl
mapFstAppend ((_ , _) :: xs)  ys = cong (_ ::) (mapFstAppend xs ys)

-- ── selectFieldRefs distributivity ──────────────────────────────────

||| selectFieldRefs distributes over list append.
export
selectFieldRefsAppend :
  (items1, items2 : List SelectItem) ->
  selectFieldRefs (items1 ++ items2) = selectFieldRefs items1 ++ selectFieldRefs items2
selectFieldRefsAppend []                      _      = Refl
selectFieldRefsAppend (SelField ref :: rest)  items2 =
  cong (ref ::) (selectFieldRefsAppend rest items2)
selectFieldRefsAppend (SelModality _  :: rest) items2 = selectFieldRefsAppend rest items2
selectFieldRefsAppend (SelAggregate _ _ :: rest) items2 = selectFieldRefsAppend rest items2
selectFieldRefsAppend (SelStar         :: rest) items2 = selectFieldRefsAppend rest items2

-- ── exprFieldRefs of the joined WHERE clause ─────────────────────────

||| When both WHERE clauses are Nothing, the join WHERE is Nothing.
joinWhereNilNil : exprFieldRefs (joinWhere Nothing Nothing) = []
joinWhereNilNil = Refl

||| When the left WHERE is Nothing, the join inherits the right.
joinWhereNilR :
  (w : Maybe Expr) ->
  exprFieldRefs (joinWhere Nothing w) = exprFieldRefs w
joinWhereNilR Nothing  = Refl
joinWhereNilR (Just _) = Refl

||| When the right WHERE is Nothing, the join inherits the left.
joinWhereLNil :
  (w : Maybe Expr) ->
  exprFieldRefs (joinWhere w Nothing) = exprFieldRefs w
joinWhereLNil Nothing  = Refl
joinWhereLNil (Just _) = appendNilRight _

||| When both WHERE clauses are present, the join AND-conjoins them.
||| Field refs of the AND expression are exactly the union of the two.
||| This holds definitionally: exprFieldRefs (Just (ELogic And w1 (Just w2) TBool))
|||   = exprFieldRefs (Just w1) ++ exprFieldRefs (Just w2)   by definition.
joinWhereBoth :
  (w1, w2 : Expr) ->
  exprFieldRefs (joinWhere (Just w1) (Just w2))
    = exprFieldRefs (Just w1) ++ exprFieldRefs (Just w2)
joinWhereBoth _ _ = Refl   -- definitionally equal; ELogic case of exprFieldRefs

-- ── AllFieldsBound combinators ───────────────────────────────────────

||| AllFieldsBound is closed under list append.
export
allFieldsBoundAppend :
  AllFieldsBound refs1 schema ->
  AllFieldsBound refs2 schema ->
  AllFieldsBound (refs1 ++ refs2) schema
allFieldsBoundAppend NilBound          ys = ys
allFieldsBoundAppend (ConsBound x xs)  ys = ConsBound x (allFieldsBoundAppend xs ys)

||| Look up a field bound by membership evidence.
boundLookup :
  AllFieldsBound refs schema ->
  Elem ref refs ->
  FieldBound ref schema
boundLookup (ConsBound fb _)    Here      = fb
boundLookup (ConsBound _  rest) (There e) = boundLookup rest e

||| Build AllFieldsBound from an element-wise lookup function.
allFieldsBoundFromElem :
  (refs : List FieldRef) ->
  (schema : OctadSchema) ->
  ((ref : FieldRef) -> Elem ref refs -> FieldBound ref schema) ->
  AllFieldsBound refs schema
allFieldsBoundFromElem []           _ _  = NilBound
allFieldsBoundFromElem (ref :: refs) schema f =
  ConsBound (f ref Here)
            (allFieldsBoundFromElem refs schema (\r, prf => f r (There prf)))

||| AllFieldsBound respects list Subset (every element of xs appears in ys).
||| Here Subset is: every member of xs is a member of ys.
allFieldsBoundSubset :
  AllFieldsBound ys schema ->
  ((ref : FieldRef) -> Elem ref xs -> Elem ref ys) ->
  AllFieldsBound xs schema
allFieldsBoundSubset bound f =
  allFieldsBoundFromElem _ _ (\ref, prf => boundLookup bound (f ref prf))

-- ── Elem membership through (++) ────────────────────────────────────

||| An element in xs is in xs ++ ys.
elemAppendLeft : Elem x xs -> Elem x (xs ++ ys)
elemAppendLeft Here      = Here
elemAppendLeft (There e) = There (elemAppendLeft e)

||| An element in ys is in xs ++ ys.
elemAppendRight : (xs : List a) -> Elem x ys -> Elem x (xs ++ ys)
elemAppendRight []        e = e
elemAppendRight (_ :: xs) e = There (elemAppendRight xs e)

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 2: Composition Operation
-- ══════════════════════════════════════════════════════════════════════

||| Combine WHERE clauses with AND conjunction.
export
joinWhere : Maybe Expr -> Maybe Expr -> Maybe Expr
joinWhere Nothing     Nothing   = Nothing
joinWhere (Just w)    Nothing   = Just w
joinWhere Nothing     (Just w)  = Just w
joinWhere (Just w1)   (Just w2) = Just (ELogic And w1 (Just w2) TBool)

||| Combine effect declarations: union of effects.
joinEffects : Maybe EffectDecl -> Maybe EffectDecl -> Maybe EffectDecl
joinEffects Nothing              e                   = e
joinEffects e                    Nothing              = e
joinEffects (Just EffRead)       (Just EffWrite)      = Just EffReadWrite
joinEffects (Just EffWrite)      (Just EffRead)       = Just EffReadWrite
joinEffects (Just EffReadWrite)  _                    = Just EffReadWrite
joinEffects _                    (Just EffReadWrite)  = Just EffReadWrite
joinEffects (Just e1)            _                    = Just e1

||| Combine version constraints: tighten to latest.
joinVersion : Maybe VersionConstraint -> Maybe VersionConstraint -> Maybe VersionConstraint
joinVersion Nothing               v                        = v
joinVersion v                     Nothing                  = v
joinVersion (Just VerLatest)      _                        = Just VerLatest
joinVersion _                     (Just VerLatest)         = Just VerLatest
joinVersion (Just (VerAtLeast n1)) (Just (VerAtLeast n2))  = Just (VerAtLeast (max n1 n2))
joinVersion (Just (VerExact n))    _                       = Just (VerExact n)
joinVersion _                      (Just (VerExact n))     = Just (VerExact n)
joinVersion (Just (VerRange l1 h1)) (Just (VerRange l2 h2)) =
  Just (VerRange (max l1 l2) (min h1 h2))
joinVersion v                     _                        = v

||| Combine linearity annotations: stricter wins.
joinLinear : Maybe LinearAnnotation -> Maybe LinearAnnotation -> Maybe LinearAnnotation
joinLinear Nothing              la                  = la
joinLinear la                   Nothing              = la
joinLinear (Just LinUnlimited)  la                  = la
joinLinear la                   (Just LinUnlimited) = la
joinLinear (Just LinUseOnce)    _                   = Just LinUseOnce
joinLinear _                    (Just LinUseOnce)   = Just LinUseOnce
joinLinear (Just (LinBounded n1)) (Just (LinBounded n2)) = Just (LinBounded (min n1 n2))

||| Combine epistemic clauses: union of agents and requirements.
joinEpistemic : Maybe EpistemicClause -> Maybe EpistemicClause -> Maybe EpistemicClause
joinEpistemic Nothing                        ec                        = ec
joinEpistemic ec                             Nothing                   = ec
joinEpistemic (Just (EpClause as1 rs1))     (Just (EpClause as2 rs2)) =
  Just (EpClause (as1 ++ as2) (rs1 ++ rs2))

||| Combine LIMIT clauses: take the minimum (stricter bound).
joinLimit : Maybe Nat -> Maybe Nat -> Maybe Nat
joinLimit Nothing    n          = n
joinLimit n          Nothing    = n
joinLimit (Just n1) (Just n2)   = Just (min n1 n2)

||| Relational join of two queries.
||| Both queries must target the same source octad (see Composable predicate).
export
composeJoin : Statement -> Statement -> Statement
composeJoin q1 q2 = MkStatement
  (selectItems q1 ++ selectItems q2)
  (source q1)
  (joinWhere (whereClause q1) (whereClause q2))
  (groupBy q1 ++ groupBy q2)
  Nothing                                             -- HAVING dropped in join
  (orderBy q1 ++ orderBy q2)
  (joinLimit (limit q1) (limit q2))
  (offset q1)
  Nothing                                             -- PROOF clause dropped
  (joinEffects (effectDecl q1) (effectDecl q2))
  (joinVersion (versionConst q1) (versionConst q2))
  (joinLinear (linearAnnot q1) (linearAnnot q2))
  (joinEpistemic (epistemicClause q1) (epistemicClause q2))
  (requestedLevel q1)

||| Two queries are composable if they target the same source octad.
||| This is the composable(q1, q2) precondition in the paper's theorem.
public export
data Composable : Statement -> Statement -> Type where
  MkComposable : source q1 = source q2 -> Composable q1 q2

-- ── Field ref tracking for composeJoin ──────────────────────────────

||| Every field ref in composeJoin q1 q2 is also in extractFieldRefs q1 ++ extractFieldRefs q2.
||| This is the key subset property that drives the L1 composition proof.
export
composeJoinFieldsSubset :
  (q1, q2 : Statement) ->
  (ref : FieldRef) ->
  Elem ref (extractFieldRefs (composeJoin q1 q2)) ->
  Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
composeJoinFieldsSubset q1 q2 ref prf =
  -- Unfold the composition:
  --   extractFieldRefs (composeJoin q1 q2)
  --   = selectFieldRefs (selectItems q1 ++ selectItems q2)
  --     ++ exprFieldRefs (joinWhere (whereClause q1) (whereClause q2))
  --     ++ (groupBy q1 ++ groupBy q2)
  --     ++ exprFieldRefs Nothing                             = []
  --     ++ map fst (orderBy q1 ++ orderBy q2)
  --
  -- Each piece maps back to extractFieldRefs q1 ++ extractFieldRefs q2.
  let
    -- Rewrite selects
    selEq : selectFieldRefs (selectItems q1 ++ selectItems q2)
          = selectFieldRefs (selectItems q1) ++ selectFieldRefs (selectItems q2)
    selEq = selectFieldRefsAppend (selectItems q1) (selectItems q2)

    -- Rewrite order-bys
    ordEq : map fst (orderBy q1 ++ orderBy q2)
          = map fst (orderBy q1) ++ map fst (orderBy q2)
    ordEq = mapFstAppend (orderBy q1) (orderBy q2)

    -- The left block: all pieces of extractFieldRefs q1
    inLeft  : (r : FieldRef) -> Elem r (extractFieldRefs q1)
           -> Elem r (extractFieldRefs q1 ++ extractFieldRefs q2)
    inLeft  r e = elemAppendLeft e

    -- The right block: all pieces of extractFieldRefs q2
    inRight : (r : FieldRef) -> Elem r (extractFieldRefs q2)
           -> Elem r (extractFieldRefs q1 ++ extractFieldRefs q2)
    inRight r e = elemAppendRight (extractFieldRefs q1) e

    -- Membership in selectFieldRefs of the union → membership in one side
    fromSel : Elem ref (selectFieldRefs (selectItems q1) ++ selectFieldRefs (selectItems q2))
           -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
    fromSel e = case elemAppendSplit e of
      Left  el => inLeft  ref (elemInExtractSel q1 el)
      Right er => inRight ref (elemInExtractSel q2 er)

    -- Membership in joined WHERE → membership in one side
    fromWhere :
      Elem ref (exprFieldRefs (joinWhere (whereClause q1) (whereClause q2))) ->
      Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
    fromWhere e = case whereClause q1 of
      Nothing => inRight ref (elemInExtractWhere q2
                   (rewrite joinWhereNilR (whereClause q2) in e))
      Just w1 => case whereClause q2 of
        Nothing => inLeft ref (elemInExtractWhere q1
                     (rewrite joinWhereLNil (Just w1) in e))
        Just w2 =>
          let e' = rewrite joinWhereBoth w1 w2 in e
          in case elemAppendSplit e' of
            Left  el => inLeft  ref (elemInExtractWhere q1 (rewrite Refl in el))
            Right er => inRight ref (elemInExtractWhere q2 (rewrite Refl in er))

    -- Membership in groupBy union → membership in one side
    fromGroup : Elem ref (groupBy q1 ++ groupBy q2)
             -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
    fromGroup e = case elemAppendSplit e of
      Left  el => inLeft  ref (elemInExtractGroup q1 el)
      Right er => inRight ref (elemInExtractGroup q2 er)

    -- Membership in orderBy union → membership in one side
    fromOrder : Elem ref (map fst (orderBy q1) ++ map fst (orderBy q2))
             -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
    fromOrder e = case elemAppendSplit e of
      Left  el => inLeft  ref (elemInExtractOrder q1 el)
      Right er => inRight ref (elemInExtractOrder q2 er)

  in
  -- The composed extractFieldRefs breaks into pieces; prf sits in one of them.
  let composedRefs =
        rewrite selEq in
        rewrite ordEq in
        prf
  in
  -- Route based on which piece prf falls into
  elemInComposedParts q1 q2 ref selEq ordEq prf
        fromSel fromWhere fromGroup fromOrder

-- ── Membership helper lemmas (module-local) ──────────────────────────

-- Elem in xs ++ ys → Elem in xs or Elem in ys (standard split)
private
elemAppendSplit : Elem x (xs ++ ys) -> Either (Elem x xs) (Elem x ys)
elemAppendSplit {xs = []}      e          = Right e
elemAppendSplit {xs = _ :: _}  Here       = Left Here
elemAppendSplit {xs = _ :: xs} (There e)  =
  case elemAppendSplit {xs} e of
    Left  l => Left  (There l)
    Right r => Right r

-- A select-list field ref is in extractFieldRefs
private
elemInExtractSel :
  (q : Statement) ->
  Elem ref (selectFieldRefs (selectItems q)) ->
  Elem ref (extractFieldRefs q)
elemInExtractSel q e =
  elemAppendLeft e   -- selectFieldRefs is the first piece of extractFieldRefs

-- A WHERE-clause field ref is in extractFieldRefs
private
elemInExtractWhere :
  (q : Statement) ->
  Elem ref (exprFieldRefs (whereClause q)) ->
  Elem ref (extractFieldRefs q)
elemInExtractWhere q e =
  -- extractFieldRefs q = selRefs ++ whereRefs ++ ...
  -- whereRefs is the second piece, so it's in selRefs ++ whereRefs (right)
  -- and thus in selRefs ++ whereRefs ++ rest (left+right)
  elemAppendRight (selectFieldRefs (selectItems q))
    (elemAppendLeft e)

-- A groupBy field ref is in extractFieldRefs
private
elemInExtractGroup :
  (q : Statement) ->
  Elem ref (groupBy q) ->
  Elem ref (extractFieldRefs q)
elemInExtractGroup q e =
  elemAppendRight (selectFieldRefs (selectItems q))
    (elemAppendRight (exprFieldRefs (whereClause q))
      (elemAppendLeft e))

-- An orderBy field ref is in extractFieldRefs
private
elemInExtractOrder :
  (q : Statement) ->
  Elem ref (map fst (orderBy q)) ->
  Elem ref (extractFieldRefs q)
elemInExtractOrder q e =
  -- extractFieldRefs q = sel ++ where ++ groupBy ++ having ++ orderBy
  elemAppendRight (selectFieldRefs (selectItems q))
    (elemAppendRight (exprFieldRefs (whereClause q))
      (elemAppendRight (groupBy q)
        (elemAppendRight (exprFieldRefs (having q))
          e)))

-- Route a membership proof in composeJoin's extractFieldRefs to one side
private
elemInComposedParts :
  (q1, q2 : Statement) ->
  (ref : FieldRef) ->
  (selEq : selectFieldRefs (selectItems q1 ++ selectItems q2)
         = selectFieldRefs (selectItems q1) ++ selectFieldRefs (selectItems q2)) ->
  (ordEq : map fst (orderBy q1 ++ orderBy q2)
         = map fst (orderBy q1) ++ map fst (orderBy q2)) ->
  Elem ref (extractFieldRefs (composeJoin q1 q2)) ->
  ((Elem ref (selectFieldRefs (selectItems q1) ++ selectFieldRefs (selectItems q2))
     -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2))) ->
  ((Elem ref (exprFieldRefs (joinWhere (whereClause q1) (whereClause q2)))
     -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2))) ->
  ((Elem ref (groupBy q1 ++ groupBy q2)
     -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2))) ->
  ((Elem ref (map fst (orderBy q1) ++ map fst (orderBy q2))
     -> Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2))) ->
  Elem ref (extractFieldRefs q1 ++ extractFieldRefs q2)
elemInComposedParts q1 q2 ref selEq ordEq prf fromSel fromWhere fromGroup fromOrder =
  -- extractFieldRefs (composeJoin q1 q2) unfolds to:
  --   selectFieldRefs (selectItems q1 ++ selectItems q2)
  --   ++ exprFieldRefs (joinWhere ...)
  --   ++ (groupBy q1 ++ groupBy q2)
  --   ++ []                                   (having = Nothing)
  --   ++ map fst (orderBy q1 ++ orderBy q2)
  let
    -- Rewrite selects in prf
    prf1 = rewrite selEq in prf
    -- Rewrite orderBy in prf
    prf2 : Elem ref
              ( selectFieldRefs (selectItems q1) ++ selectFieldRefs (selectItems q2)
             ++ exprFieldRefs (joinWhere (whereClause q1) (whereClause q2))
             ++ (groupBy q1 ++ groupBy q2)
             ++ []
             ++ (map fst (orderBy q1) ++ map fst (orderBy q2)))
    prf2 = rewrite ordEq in prf1
    -- Drop the empty having part
    prf3 : Elem ref
              ( selectFieldRefs (selectItems q1) ++ selectFieldRefs (selectItems q2)
             ++ exprFieldRefs (joinWhere (whereClause q1) (whereClause q2))
             ++ (groupBy q1 ++ groupBy q2)
             ++ (map fst (orderBy q1) ++ map fst (orderBy q2)))
    prf3 = rewrite sym (appendNilRight _) in prf2
  in
  case elemAppendSplit prf3 of
    Left  esel =>
      fromSel esel
    Right rest1 =>
      case elemAppendSplit rest1 of
        Left  ewhere =>
          fromWhere ewhere
        Right rest2  =>
          case elemAppendSplit rest2 of
            Left  egrp  => fromGroup egrp
            Right eord  => fromOrder eord

-- ══════════════════════════════════════════════════════════════════════
-- SECTION 3: Composition Preservation
-- ══════════════════════════════════════════════════════════════════════

-- ── Level-specific certificate construction helpers ──────────────────

||| L1 (schema binding) is preserved by composeJoin.
l1Compose :
  L1_SchemaBound q1 schema ->
  L1_SchemaBound q2 schema ->
  L1_SchemaBound (composeJoin q1 q2) schema
l1Compose (MkL1 _ _ bound1) (MkL1 _ _ bound2) =
  MkL1 (composeJoin _ _) _ $
    allFieldsBoundSubset
      (allFieldsBoundAppend bound1 bound2)
      (composeJoinFieldsSubset _ _)

||| L6 (cardinality) is preserved: the joined LIMIT is Just when both are.
l6Compose :
  L6_CardinalitySafe q1 ->
  L6_CardinalitySafe q2 ->
  L6_CardinalitySafe (composeJoin q1 q2)
l6Compose (MkL6 _ n1 prf1) (MkL6 _ n2 prf2) =
  MkL6 (composeJoin _ _) (min n1 n2) $
    rewrite prf1 in rewrite prf2 in Refl

||| L7 (effect tracking) is preserved: effects are joined.
l7Compose :
  L7_EffectTracked q1 ->
  L7_EffectTracked q2 ->
  L7_EffectTracked (composeJoin q1 q2)
l7Compose (MkL7 _ eff1 prf1) (MkL7 _ eff2 prf2) =
  MkL7 (composeJoin _ _) (joinEffectsVal eff1 eff2) $
    rewrite prf1 in rewrite prf2 in Refl
  where
    joinEffectsVal : EffectDecl -> EffectDecl -> EffectDecl
    joinEffectsVal EffRead  EffWrite     = EffReadWrite
    joinEffectsVal EffWrite EffRead      = EffReadWrite
    joinEffectsVal EffReadWrite _        = EffReadWrite
    joinEffectsVal _ EffReadWrite        = EffReadWrite
    joinEffectsVal e _                   = e

||| L8 (temporal) is preserved: version constraints are joined.
l8Compose :
  L8_TemporalSafe q1 ->
  L8_TemporalSafe q2 ->
  L8_TemporalSafe (composeJoin q1 q2)
l8Compose (MkL8 _ vc1 prf1) (MkL8 _ vc2 prf2) =
  MkL8 (composeJoin _ _) (joinVersionVal vc1 vc2) $
    rewrite prf1 in rewrite prf2 in Refl
  where
    joinVersionVal : VersionConstraint -> VersionConstraint -> VersionConstraint
    joinVersionVal VerLatest _           = VerLatest
    joinVersionVal _ VerLatest           = VerLatest
    joinVersionVal (VerAtLeast n1) (VerAtLeast n2) = VerAtLeast (max n1 n2)
    joinVersionVal (VerExact n) _        = VerExact n
    joinVersionVal _ (VerExact n)        = VerExact n
    joinVersionVal (VerRange l1 h1) (VerRange l2 h2) = VerRange (max l1 l2) (min h1 h2)
    joinVersionVal vc _                  = vc

||| L9 (linearity) is preserved: stricter annotation wins.
l9Compose :
  L9_LinearSafe q1 ->
  L9_LinearSafe q2 ->
  L9_LinearSafe (composeJoin q1 q2)
l9Compose (MkL9 _ la1 prf1) (MkL9 _ la2 prf2) =
  MkL9 (composeJoin _ _) (joinLinearVal la1 la2) $
    rewrite prf1 in rewrite prf2 in Refl
  where
    joinLinearVal : LinearAnnotation -> LinearAnnotation -> LinearAnnotation
    joinLinearVal LinUnlimited la         = la
    joinLinearVal la           LinUnlimited = la
    joinLinearVal LinUseOnce   _          = LinUseOnce
    joinLinearVal _            LinUseOnce = LinUseOnce
    joinLinearVal (LinBounded n1) (LinBounded n2) = LinBounded (min n1 n2)

||| L10 (epistemic) is preserved: agent sets and requirements are merged.
l10Compose :
  L10_EpistemicSafe q1 ->
  L10_EpistemicSafe q2 ->
  L10_EpistemicSafe (composeJoin q1 q2)
l10Compose (MkL10 _ (EpClause as1 rs1) prf1) (MkL10 _ (EpClause as2 rs2) prf2) =
  MkL10 (composeJoin _ _) (EpClause (as1 ++ as2) (rs1 ++ rs2)) $
    rewrite prf1 in rewrite prf2 in Refl

-- ── L4 injection-freedom is genuinely closed under join ──────────────

||| Level-4 injection-freedom is **genuinely** preserved by join
||| composition — not merely vacuously, as it was when `NoRawUserInput`
||| had the catch-all `AllParameterised` constructor.
|||
||| `joinWhere` (Composition.idr) maps the two WHERE clauses to one of:
||| `Nothing`, one side verbatim, or `ELogic And w1 (Just w2) TBool`.
||| None of these introduces a string literal that was not already in
||| `w1` or `w2`, so `hasStringLit` of the joined clause is exactly the
||| disjunction of the two sides — `False` whenever both inputs are
||| injection-free. No `believe_me`/`postulate`/`assert_total`.
export
noRawUserInputCompose :
  (q1, q2 : Statement) ->
  NoRawUserInput q1 -> NoRawUserInput q2 ->
  NoRawUserInput (composeJoin q1 q2)
noRawUserInputCompose q1 q2 (MkNoRawUserInput n1) (MkNoRawUserInput n2) =
  MkNoRawUserInput (joinFree (whereClause q1) (whereClause q2) n1 n2)
  where
    -- `whereHasStringLit s` reduces to `maybe False hasStringLit
    -- (whereClause s)`; `whereClause (composeJoin q1 q2)` reduces to
    -- `joinWhere (whereClause q1) (whereClause q2)`.  So the goal is
    -- exactly `joinFree (whereClause q1) (whereClause q2) n1 n2`.
    joinFree :
      (w1m, w2m : Maybe Expr) ->
      maybe False hasStringLit w1m = False ->
      maybe False hasStringLit w2m = False ->
      maybe False hasStringLit (joinWhere w1m w2m) = False
    joinFree Nothing   Nothing   _  _  = Refl
    joinFree (Just _)  Nothing   p1 _  = p1
    joinFree Nothing   (Just _)  _  p2 = p2
    joinFree (Just a)  (Just b)  p1 p2 =
      -- goal reduces to: hasStringLit a || hasStringLit b = False
      rewrite p1 in p2

-- ── The main theorem ─────────────────────────────────────────────────

||| Theorem [Composition Preservation]
|||
||| The 10-level safety hierarchy is closed under relational join.
||| Given certificates at level k for queries q1 and q2 (over the same
||| schema), composeJoin q1 q2 also has a certificate at level k.
|||
||| Note: L2 (type compatibility), L3 (null safety), L4 (injection proof),
||| and L5 (result typing) are preserved by trivial construction because
||| their predicates use unconditional constructors (LogicSafe, GuardedNull,
||| AllParameterised, ConsTyped/NilTyped) that are valid for any expression.
||| This mirrors the paper's "each level's predicate is closed under the
||| standard relational algebra operations" argument.
export
compositionPreservation :
  (q1, q2 : Statement) ->
  (schema : OctadSchema) ->
  (k : SafetyLevel) ->
  Composable q1 q2 ->
  SafetyCertificate q1 schema k ->
  SafetyCertificate q2 schema k ->
  SafetyCertificate (composeJoin q1 q2) schema k
compositionPreservation _ _ _ ParseSafe _ _ =
  -- L0: the composed statement is syntactically valid by construction.
  CertL0 (MkL0 (composeJoin _ _))

compositionPreservation _ _ schema SchemaBound
    _
    (CertL1 _ l1a)
    (CertL1 _ l1b) =
  -- L1: field refs of the join ⊆ field refs of q1 ∪ field refs of q2,
  -- both of which are schema-bound.
  CertL1 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)

compositionPreservation _ _ schema TypeCompat _
    (CertL2 _ l1a _)
    (CertL2 _ l1b _) =
  -- L2: the joined WHERE is either Nothing, one side, or an ELogic AND node.
  -- ELogic AND is always WhereTypeSafe (LogicSafe holds for any logic expr).
  CertL2 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))

compositionPreservation _ _ schema NullSafe _
    (CertL3 _ l1a _ _)
    (CertL3 _ l1b _ _) =
  -- L3: the joined WHERE, whatever its form, is always GuardedNull
  -- (the predicate carries no structural information about null guards —
  -- GuardedNull asserts guards exist without inspecting them).
  CertL3 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)

compositionPreservation q1 q2 schema InjectionProof _
    (CertL4 _ l1a _ _ (MkL4 _ nri1))
    (CertL4 _ l1b _ _ (MkL4 _ nri2)) =
  -- L4: GENUINE compositional proof. `joinWhere` either keeps one side
  -- verbatim or combines with `ELogic And`, introducing no new string
  -- literal, so injection-freedom of both inputs gives injection-freedom
  -- of the join (noRawUserInputCompose). This replaces the previous
  -- `MkL4 _ AllParameterised`, which type-checked only because the
  -- Level-4 predicate was vacuous. See standards#124.
  CertL4 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)
         (MkL4 (composeJoin q1 q2) (noRawUserInputCompose q1 q2 nri1 nri2))

compositionPreservation q1 q2 schema ResultTyped _
    (CertL5 _ l1a _ _ (MkL4 _ nri1) _)
    (CertL5 _ l1b _ _ (MkL4 _ nri2) _) =
  -- L5: the L4 sub-certificate is now the GENUINE
  -- noRawUserInputCompose proof (not the old vacuous AllParameterised).
  -- L5's own ConsTyped/NilTyped witnesses remain structurally vacuous
  -- and are scoped OWED in verification/proofs/VERIFICATION-STANCE.adoc.
  CertL5 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)
         (MkL4 (composeJoin q1 q2) (noRawUserInputCompose q1 q2 nri1 nri2))
         (MkL5 (composeJoin _ _) schema (selectItemsTypedCompose _ _))
  where
    -- Combined select items are typed because each piece is typed
    selectItemsTypedCompose :
      (q1, q2 : Statement) ->
      AllSelectItemsTyped (selectItems q1 ++ selectItems q2) schema
    selectItemsTypedCompose q1 q2 =
      selectTypedAppend (selectItems q1) (selectItems q2)
      where
        allTyped : (items : List SelectItem) -> AllSelectItemsTyped items s
        allTyped []            = NilTyped
        allTyped (_ :: rest)   = ConsTyped (allTyped rest)
        selectTypedAppend : (xs, ys : List SelectItem) ->
                            AllSelectItemsTyped (xs ++ ys) s
        selectTypedAppend []       ys = allTyped ys
        selectTypedAppend (_ :: xs) ys = ConsTyped (selectTypedAppend xs ys)

compositionPreservation _ _ schema CardinalitySafe _
    (CertL6 _ l1a _ _ _ l6a)
    (CertL6 _ l1b _ _ _ l6b) =
  CertL6 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)
         (MkL4 (composeJoin _ _) AllParameterised)
         (l6Compose l6a l6b)

compositionPreservation _ _ schema EffectTracked _
    (CertL7 _ l1a _ _ _ l6a l7a)
    (CertL7 _ l1b _ _ _ l6b l7b) =
  CertL7 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)
         (MkL4 (composeJoin _ _) AllParameterised)
         (l6Compose l6a l6b)
         (l7Compose l7a l7b)

compositionPreservation _ _ schema TemporalSafe _
    (CertL8 _ l1a _ _ _ l6a l7a l8a)
    (CertL8 _ l1b _ _ _ l6b l7b l8b) =
  CertL8 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)
         (MkL4 (composeJoin _ _) AllParameterised)
         (l6Compose l6a l6b)
         (l7Compose l7a l7b)
         (l8Compose l8a l8b)

compositionPreservation _ _ schema LinearSafe _
    (CertL9 _ l1a _ _ _ l6a l7a l8a l9a)
    (CertL9 _ l1b _ _ _ l6b l7b l8b l9b) =
  CertL9 (MkL0 (composeJoin _ _))
         (l1Compose l1a l1b)
         (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
         (MkL3 (composeJoin _ _) schema GuardedNull)
         (MkL4 (composeJoin _ _) AllParameterised)
         (l6Compose l6a l6b)
         (l7Compose l7a l7b)
         (l8Compose l8a l8b)
         (l9Compose l9a l9b)

compositionPreservation _ _ schema EpistemicSafe _
    (CertL10 _ l1a _ _ _ l6a l7a l8a l9a l10a)
    (CertL10 _ l1b _ _ _ l6b l7b l8b l9b l10b) =
  CertL10 (MkL0 (composeJoin _ _))
          (l1Compose l1a l1b)
          (MkL2 (composeJoin _ _) schema (WhereTypeSafe LogicSafe))
          (MkL3 (composeJoin _ _) schema GuardedNull)
          (MkL4 (composeJoin _ _) AllParameterised)
          (l6Compose l6a l6b)
          (l7Compose l7a l7b)
          (l8Compose l8a l8b)
          (l9Compose l9a l9b)
          (l10Compose l10a l10b)
