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
