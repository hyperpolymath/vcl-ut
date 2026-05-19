-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Core Decide — canonical safety deciders (single source of truth)
|||
||| Phase 2 of the standards#124 HOLE remediation de-vacuizes the Level
||| 2 / 3 / 5 proof predicates. Before this, `Levels.AllComparisonsTypeSafe`,
||| `AllNullableFieldsGuarded` and `AllSelectItemsTyped` were inhabited by
||| content-free constructors, so a query that *failed* the corresponding
||| `Checker.checkLevelN` still type-checked at that level — the predicate
||| proved nothing.
|||
||| The fix mirrors the Level-4 architecture (`Grammar.hasStringLit`): a
||| single decidable `Bool` function lives here, BELOW both the proof
||| predicates (`Levels`) and the decision pipeline (`Checker`). The
||| predicate carries `decider … = True` as structural evidence and
||| `Checker.checkLevelN` is *defined through the same function*, so the
||| soundness lemma (`checkLevelNSound`) is a genuine equality, not a
||| check against a parallel re-implementation that could silently drift.
|||
||| Nothing here uses believe_me / postulate / assert_* / idris_crash /
||| sorry: the deciders are ordinary structural recursion and the lemmas
||| are ordinary equational reasoning.

module VclTotal.Core.Decide

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import Data.List

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Boolean glue lemmas (self-contained; no Prelude Uninhabited dependency)
-- ═══════════════════════════════════════════════════════════════════════

||| `False = True` is absurd. Defined locally rather than via a Prelude
||| `Uninhabited` instance, matching the codebase convention
||| (`Checker.falseNotTrue`) of not depending on instance names that
||| have moved across idris2 releases.
public export
notFalseTrue : (False = True) -> Void
notFalseTrue Refl impossible

||| If `a` is `True`, `a && b` is `b`; so two `= True` facts compose.
public export
andTrueIntro : {a, b : Bool} -> a = True -> b = True -> (a && b) = True
andTrueIntro Refl pb = pb

||| Conversely, `a && b = True` splits into both conjuncts.
public export
andTrueSplit : (a, b : Bool) -> (a && b) = True -> (a = True, b = True)
andTrueSplit True  b prf = (Refl, prf)
andTrueSplit False b prf = void (notFalseTrue prf)

||| If either disjunct is `True`'s negation… more precisely: both `False`
||| gives `False` for the disjunction. (Mirrors `Composition.orBothFalse`
||| but kept here so the L2/L3 deciders are self-contained.)
public export
orBothFalse : (a, b : Bool) -> a = False -> b = False -> (a || b) = False
orBothFalse a b pa pb = rewrite pa in pb

-- ═══════════════════════════════════════════════════════════════════════
-- Shared type resolution (was private in Checker; hoisted here so the
-- Level-2 / Level-5 predicate and the checker share ONE definition)
-- ═══════════════════════════════════════════════════════════════════════

||| Resolve the VqlType of an expression using the schema.
||| `EField` is resolved against the schema; every other node carries its
||| own annotation. Context-free: the result depends only on the node and
||| the schema, never on the surrounding expression — this is what makes
||| Level-2 / Level-5 composition genuine (join never rewrites subnodes).
public export
resolveExprType : Expr -> OctadSchema -> VqlType
resolveExprType (EField ref _) schema    = resolveType ref schema
resolveExprType (ELiteral _ ty) _        = ty
resolveExprType (ECompare _ _ _ ty) _    = ty
resolveExprType (ELogic _ _ _ ty) _      = ty
resolveExprType (EAggregate _ _ ty) _    = ty
resolveExprType (EParam _ ty) _          = ty
resolveExprType EStar _                  = TAny
resolveExprType (ESubquery _) _          = TOctad
resolveExprType (EEpistemic _ _ _ ty) _  = ty
resolveExprType (EAnnounce _ _ _ ty) _   = ty

||| Resolve the result type of a single SELECT item.
public export
resolveSelectItemType : SelectItem -> OctadSchema -> VqlType
resolveSelectItemType (SelField ref) schema     = resolveType ref schema
resolveSelectItemType (SelModality _) _          = TOctad
resolveSelectItemType (SelAggregate _ e) schema  = resolveExprType e schema
resolveSelectItemType SelStar _                  = TAny

-- ═══════════════════════════════════════════════════════════════════════
-- Level 5 decider — ResultTyped
-- ═══════════════════════════════════════════════════════════════════════

||| `True` unless the type is the unresolved `TAny` sentinel.
public export
notAnyTy : VqlType -> Bool
notAnyTy TAny = False
notAnyTy _    = True

||| One SELECT item resolves to a known (non-`TAny`) type.
public export
selectItemTyped : SelectItem -> OctadSchema -> Bool
selectItemTyped item schema = notAnyTy (resolveSelectItemType item schema)

||| Level-5 decider: every SELECT item resolves to a known type.
||| Defined by explicit spine recursion (not `all`) so the
||| append-distribution lemma is a one-line structural induction.
public export
selectItemsTyped : List SelectItem -> OctadSchema -> Bool
selectItemsTyped []        _      = True
selectItemsTyped (i :: is) schema =
  selectItemTyped i schema && selectItemsTyped is schema

||| `selectItemsTyped` over an append is provable from each side
||| (the engine of genuine L5 composition: `composeJoin` concatenates
||| the SELECT lists and `selectItemTyped` is per-item / context-free).
public export
selectItemsTypedAppend :
  (xs, ys : List SelectItem) -> (sch : OctadSchema) ->
  selectItemsTyped xs sch = True -> selectItemsTyped ys sch = True ->
  selectItemsTyped (xs ++ ys) sch = True
selectItemsTypedAppend []        ys sch _   py = py
selectItemsTypedAppend (i :: is) ys sch pxs py =
  let (qi, qis) = andTrueSplit (selectItemTyped i sch)
                               (selectItemsTyped is sch) pxs
  in andTrueIntro qi (selectItemsTypedAppend is ys sch qis py)

-- ═══════════════════════════════════════════════════════════════════════
-- Level 2 decider — TypeCompat
-- (was private in Checker; hoisted so the L2 predicate + checkLevel2
--  share ONE definition — single source of truth, no drift)
-- ═══════════════════════════════════════════════════════════════════════

||| Structural equality for Agent (payload-sensitive for the parameterised
||| constructors). Used only to compare epistemic type wrappers.
public export
agentEq : Agent -> Agent -> Bool
agentEq AgEngine        AgEngine        = True
agentEq (AgProver a)    (AgProver b)    = a == b
agentEq AgValidator     AgValidator     = True
agentEq (AgUser a)      (AgUser b)      = a == b
agentEq AgFederation    AgFederation    = True
agentEq _               _              = False

||| Structural equality for VqlType (same constructor + matching args).
public export
vqlTypeEq : VqlType -> VqlType -> Bool
vqlTypeEq TString     TString     = True
vqlTypeEq TInt        TInt        = True
vqlTypeEq TFloat      TFloat      = True
vqlTypeEq TBool       TBool       = True
vqlTypeEq TBytes      TBytes      = True
vqlTypeEq (TVector n) (TVector m) = n == m
vqlTypeEq TTimestamp  TTimestamp  = True
vqlTypeEq THash       THash       = True
vqlTypeEq (TList a)   (TList b)   = vqlTypeEq a b
vqlTypeEq TOctad      TOctad      = True
vqlTypeEq (TNull a)   (TNull b)   = vqlTypeEq a b
vqlTypeEq TAny        TAny        = True
vqlTypeEq (TKnows a1 t1)     (TKnows a2 t2)     = agentEq a1 a2 && vqlTypeEq t1 t2
vqlTypeEq (TBelieves a1 t1)  (TBelieves a2 t2)  = agentEq a1 a2 && vqlTypeEq t1 t2
vqlTypeEq (TCommonKnowledge t1) (TCommonKnowledge t2) = vqlTypeEq t1 t2
vqlTypeEq _           _           = False

||| Two VqlTypes are compatible for comparison: structurally equal, or
||| `TNull t ~ t`, or numeric widening `TInt ~ TFloat`. Decidable mirror
||| of `Grammar.TypeCompatible`.
public export
typesCompatible : VqlType -> VqlType -> Bool
typesCompatible a b =
  if vqlTypeEq a b
    then True
    else case (a, b) of
      (TNull inner, other) => vqlTypeEq inner other
      (other, TNull inner) => vqlTypeEq other inner
      (TInt, TFloat)       => True
      (TFloat, TInt)       => True
      _                    => False

||| All `ECompare` nodes in an expression tree, as
||| (operator, left, right, annotated-type) tuples. Structural recursion
||| on `Expr`; `ESubquery` is opaque here (its own checker pass covers
||| it), so this is total with no fuel/axiom.
public export
extractComparisons : Expr -> List (CompOp, Expr, Expr, VqlType)
extractComparisons (ECompare op l r ty) =
  (op, l, r, ty) :: extractComparisons l ++ extractComparisons r
extractComparisons (ELogic _ l Nothing _)  = extractComparisons l
extractComparisons (ELogic _ l (Just r) _) =
  extractComparisons l ++ extractComparisons r
extractComparisons (EAggregate _ e _)   = extractComparisons e
extractComparisons (EEpistemic _ _ e _) = extractComparisons e
extractComparisons (EAnnounce _ p b _)  =
  extractComparisons p ++ extractComparisons b
extractComparisons _ = []

||| One comparison's operands have compatible resolved types.
public export
comparisonCompatible :
  OctadSchema -> (CompOp, Expr, Expr, VqlType) -> Bool
comparisonCompatible schema (_, l, r, _) =
  typesCompatible (resolveExprType l schema) (resolveExprType r schema)

||| Every comparison in a list is operand-compatible. Explicit spine
||| recursion (not `all`) so the append lemma is one structural step.
public export
allComparisonsCompatible :
  List (CompOp, Expr, Expr, VqlType) -> OctadSchema -> Bool
allComparisonsCompatible []        _      = True
allComparisonsCompatible (c :: cs) schema =
  comparisonCompatible schema c && allComparisonsCompatible cs schema

||| Level-2 decider: every comparison in the (optional) WHERE clause has
||| operands of compatible resolved types. `Nothing` is trivially safe.
public export
whereComparisonsCompatible : Maybe Expr -> OctadSchema -> Bool
whereComparisonsCompatible Nothing  _      = True
whereComparisonsCompatible (Just e) schema =
  allComparisonsCompatible (extractComparisons e) schema

||| `allComparisonsCompatible` over an append follows from each side
||| (engine of genuine L2 composition: `composeJoin` conjoins the two
||| WHEREs under one `ELogic And` node, whose comparison multiset is
||| exactly the union — `extractComparisons` distributes over it — and
||| `comparisonCompatible` is per-node / context-free).
public export
allComparisonsCompatibleAppend :
  (xs, ys : List (CompOp, Expr, Expr, VqlType)) -> (sch : OctadSchema) ->
  allComparisonsCompatible xs sch = True ->
  allComparisonsCompatible ys sch = True ->
  allComparisonsCompatible (xs ++ ys) sch = True
allComparisonsCompatibleAppend []        ys sch _   py = py
allComparisonsCompatibleAppend (c :: cs) ys sch pxs py =
  let (qc, qcs) = andTrueSplit (comparisonCompatible sch c)
                               (allComparisonsCompatible cs sch) pxs
  in andTrueIntro qc (allComparisonsCompatibleAppend cs ys sch qcs py)
