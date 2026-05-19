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

-- ═══════════════════════════════════════════════════════════════════════
-- Level 3 decider — NullSafe
-- (was a `where` block inside Checker.findUnguardedNullableFields;
--  hoisted so the L3 predicate + checkLevel3 share ONE definition.
--  L3 is Statement-indexed: checkLevel3 — and now the predicate — cover
--  BOTH the WHERE and the HAVING clause.)
-- ═══════════════════════════════════════════════════════════════════════

||| `True = False` is absurd (companion of `notFalseTrue`).
public export
notTrueFalse : (True = False) -> Void
notTrueFalse Refl impossible

||| `not b = True` forces `b = False`.
public export
notTrueElim : (b : Bool) -> not b = True -> b = False
notTrueElim False _   = Refl
notTrueElim True  prf = void (notFalseTrue prf)

||| `not b = False` forces `b = True`.
public export
notFalseElim : (b : Bool) -> not b = False -> b = True
notFalseElim True  _   = Refl
notFalseElim False prf = void (notTrueFalse prf)

||| `b || True` is always `True`.
public export
orTrueR : (b : Bool) -> (b || True) = True
orTrueR True  = Refl
orTrueR False = Refl

-- NB: `Data.List.elemBy` in idris2 0.8.0 is `foldl (\a,e => a || Delay
-- (eq x e)) False`, which does NOT reduce structurally on `_::_`, so
-- induction on it stalls. The L3 guard membership therefore uses this
-- purpose-built `refElem` (plain `||` recursion, clean reduction).

||| Field-ref identity used for guard matching (modality tag + name) —
||| the exact relation the original `Checker` heuristic used.
public export
fieldRefEq : FieldRef -> FieldRef -> Bool
fieldRefEq a b =
  modalityToInt (modality a) == modalityToInt (modality b)
    && fieldName a == fieldName b

||| Membership of a field-ref in a guard set, by `fieldRefEq`. Plain
||| `||` spine recursion (cf. the `elemBy`/`foldl` note above) so the
||| monotonicity lemmas are clean structural inductions.
public export
refElem : FieldRef -> List FieldRef -> Bool
refElem _ []        = False
refElem r (g :: gs) = fieldRefEq r g || refElem r gs

||| `refElem` is monotone under appending guards on the left.
public export
refElemAppendL :
  (r : FieldRef) -> (xs, ys : List FieldRef) ->
  refElem r xs = True -> refElem r (xs ++ ys) = True
refElemAppendL r []        ys prf = void (notFalseTrue prf)
refElemAppendL r (g :: gs) ys prf with (fieldRefEq r g)
  refElemAppendL r (g :: gs) ys prf | True  = Refl
  refElemAppendL r (g :: gs) ys prf | False = refElemAppendL r gs ys prf

||| `refElem` is monotone under appending guards on the right.
public export
refElemAppendR :
  (r : FieldRef) -> (xs, ys : List FieldRef) ->
  refElem r ys = True -> refElem r (xs ++ ys) = True
refElemAppendR r []        ys prf = prf
refElemAppendR r (g :: gs) ys prf with (fieldRefEq r g)
  refElemAppendR r (g :: gs) ys prf | True  = Refl
  refElemAppendR r (g :: gs) ys prf | False = refElemAppendR r gs ys prf

||| Every field reference syntactically present in an expression.
||| Structural recursion; `ESubquery` is opaque here — a subquery's
||| null-safety is established by its OWN Level-3 pass, not folded into
||| the enclosing query (disclosed in VERIFICATION-STANCE.adoc).
public export
exprFieldRefsD : Expr -> List FieldRef
exprFieldRefsD (EField ref _)          = [ref]
exprFieldRefsD (ECompare _ l r _)      = exprFieldRefsD l ++ exprFieldRefsD r
exprFieldRefsD (ELogic _ l Nothing _)  = exprFieldRefsD l
exprFieldRefsD (ELogic _ l (Just r) _) = exprFieldRefsD l ++ exprFieldRefsD r
exprFieldRefsD (EAggregate _ e _)      = exprFieldRefsD e
exprFieldRefsD (EEpistemic _ _ e _)    = exprFieldRefsD e
exprFieldRefsD (EAnnounce _ p b _)     = exprFieldRefsD p ++ exprFieldRefsD b
exprFieldRefsD _                       = []

||| Field refs occurring in an explicit NULL-guard position:
||| `fld = NULL` / `NULL = fld` / `fld <> NULL` / `NULL <> fld`,
||| collected through the boolean structure of the expression.
||| (Specific guard clauses precede the general recursive one;
||| Idris's top-down match makes a guard node return its ref and never
||| fall through, exactly as the original checker did.)
public export
nullGuardedRefs : Expr -> List FieldRef
nullGuardedRefs (ECompare Eq (EField ref _) (ELiteral LitNull _) _)    = [ref]
nullGuardedRefs (ECompare Eq (ELiteral LitNull _) (EField ref _) _)    = [ref]
nullGuardedRefs (ECompare NotEq (EField ref _) (ELiteral LitNull _) _) = [ref]
nullGuardedRefs (ECompare NotEq (ELiteral LitNull _) (EField ref _) _) = [ref]
nullGuardedRefs (ECompare _ l r _)      = nullGuardedRefs l ++ nullGuardedRefs r
nullGuardedRefs (ELogic _ l Nothing _)  = nullGuardedRefs l
nullGuardedRefs (ELogic _ l (Just r) _) = nullGuardedRefs l ++ nullGuardedRefs r
nullGuardedRefs (EAggregate _ e _)      = nullGuardedRefs e
nullGuardedRefs (EEpistemic _ _ e _)    = nullGuardedRefs e
nullGuardedRefs (EAnnounce _ p b _)     = nullGuardedRefs p ++ nullGuardedRefs b
nullGuardedRefs _                       = []

-- `&&` algebra, in fully-unfolded form so the L3 monotonicity proofs
-- never have to `rewrite` a goal whose head is a stuck `refUnguarded`
-- application (`with`/`rewrite` only see *syntactic* occurrences; these
-- helpers state their goals with `&&` explicit and rely on the
-- definitional unfolding of `refUnguarded` at the call site).

||| `x && y = False` splits into which conjunct failed.
public export
andEqFalse : (x, y : Bool) -> (x && y) = False ->
             Either (x = False) (y = False)
andEqFalse False y _   = Left Refl
andEqFalse True  y prf = Right prf

||| `x && False` is always `False`.
public export
andFalseR : (x : Bool) -> (x && False) = False
andFalseR True  = Refl
andFalseR False = Refl

||| A `False` left conjunct kills the conjunction.
public export
andFalseFromL : {x : Bool} -> (z : Bool) -> x = False -> (x && z) = False
andFalseFromL z prf = rewrite prf in Refl

||| A `False` right conjunct kills the conjunction.
public export
andFalseFromR : (x : Bool) -> {z : Bool} -> z = False -> (x && z) = False
andFalseFromR x prf = rewrite prf in andFalseR x

||| A ref is "unguarded nullable" when the schema marks it nullable and
||| it does NOT appear in the collected guard set.
public export
refUnguarded : OctadSchema -> List FieldRef -> FieldRef -> Bool
refUnguarded schema guarded ref =
  isNullable ref schema && not (refElem ref guarded)

||| Adding more guards (append-left) cannot turn a guarded ref unguarded:
||| either it was never nullable, or it was already in `ga` (hence in
||| `ga ++ gb`). Conversion-based (no `rewrite` on the stuck head).
public export
refUnguardedWeakenL :
  (sch : OctadSchema) -> (ga, gb : List FieldRef) -> (r : FieldRef) ->
  refUnguarded sch ga r = False -> refUnguarded sch (ga ++ gb) r = False
refUnguardedWeakenL sch ga gb r prf =
  case andEqFalse (isNullable r sch) (not (refElem r ga)) prf of
    Left  xF => andFalseFromL (not (refElem r (ga ++ gb))) xF
    Right yF =>
      andFalseFromR (isNullable r sch)
        (cong not (refElemAppendL r ga gb
                     (notFalseElim (refElem r ga) yF)))

||| Adding more guards (append-right) cannot turn a guarded ref unguarded.
public export
refUnguardedWeakenR :
  (sch : OctadSchema) -> (ga, gb : List FieldRef) -> (r : FieldRef) ->
  refUnguarded sch gb r = False -> refUnguarded sch (ga ++ gb) r = False
refUnguardedWeakenR sch ga gb r prf =
  case andEqFalse (isNullable r sch) (not (refElem r gb)) prf of
    Left  xF => andFalseFromL (not (refElem r (ga ++ gb))) xF
    Right yF =>
      andFalseFromR (isNullable r sch)
        (cong not (refElemAppendR r ga gb
                     (notFalseElim (refElem r gb) yF)))

||| No ref in the list is unguarded-nullable wrt `guarded`. Explicit
||| spine recursion so the lemmas below are one structural step each.
public export
allRefsGuarded :
  OctadSchema -> List FieldRef -> List FieldRef -> Bool
allRefsGuarded _   _       []          = True
allRefsGuarded sch guarded (r :: rs) =
  not (refUnguarded sch guarded r) && allRefsGuarded sch guarded rs

||| `allRefsGuarded` survives appending guards on the left
||| (a strictly larger guard set only ever flags fewer refs).
public export
allRefsGuardedWeakenL :
  (sch : OctadSchema) -> (ga, gb, xs : List FieldRef) ->
  allRefsGuarded sch ga xs = True ->
  allRefsGuarded sch (ga ++ gb) xs = True
allRefsGuardedWeakenL sch ga gb []        _   = Refl
allRefsGuardedWeakenL sch ga gb (r :: rs) prf =
  let (h, t) = andTrueSplit (not (refUnguarded sch ga r))
                            (allRefsGuarded sch ga rs) prf
      ruF    = notTrueElim (refUnguarded sch ga r) h
  in andTrueIntro
       (cong not (refUnguardedWeakenL sch ga gb r ruF))
       (allRefsGuardedWeakenL sch ga gb rs t)

||| `allRefsGuarded` survives appending guards on the right.
public export
allRefsGuardedWeakenR :
  (sch : OctadSchema) -> (ga, gb, xs : List FieldRef) ->
  allRefsGuarded sch gb xs = True ->
  allRefsGuarded sch (ga ++ gb) xs = True
allRefsGuardedWeakenR sch ga gb []        _   = Refl
allRefsGuardedWeakenR sch ga gb (r :: rs) prf =
  let (h, t) = andTrueSplit (not (refUnguarded sch gb r))
                            (allRefsGuarded sch gb rs) prf
      ruF    = notTrueElim (refUnguarded sch gb r) h
  in andTrueIntro
       (cong not (refUnguardedWeakenR sch ga gb r ruF))
       (allRefsGuardedWeakenR sch ga gb rs t)

||| `allRefsGuarded` over a list append (fixed guard set).
public export
allRefsGuardedAppend :
  (sch : OctadSchema) -> (g, xs, ys : List FieldRef) ->
  allRefsGuarded sch g xs = True -> allRefsGuarded sch g ys = True ->
  allRefsGuarded sch g (xs ++ ys) = True
allRefsGuardedAppend sch g []        ys _   py = py
allRefsGuardedAppend sch g (r :: rs) ys pxs py =
  let (h, t) = andTrueSplit (not (refUnguarded sch g r))
                            (allRefsGuarded sch g rs) pxs
  in andTrueIntro h (allRefsGuardedAppend sch g rs ys t py)

||| One expression is null-safe: no schema-nullable field is used
||| without an explicit NULL guard somewhere in the same expression.
public export
exprNullSafe : Expr -> OctadSchema -> Bool
exprNullSafe e schema =
  allRefsGuarded schema (nullGuardedRefs e) (exprFieldRefsD e)

||| **Genuine** null-safety closure under AND-conjunction. `composeJoin`
||| conjoins the two WHEREs as `ELogic And a (Just b) TBool`;
||| `exprFieldRefsD` and `nullGuardedRefs` both distribute over that
||| node, so guards from EITHER side cover uses from EITHER side. Each
||| side's refs stay guarded under the (larger) combined guard set
||| (`allRefsGuardedWeaken{L,R}`), then list-append closes it. This is
||| the real reason L3 is join-closed — not a vacuous constructor.
public export
exprNullSafeConjoin :
  (a, b : Expr) -> (sch : OctadSchema) ->
  exprNullSafe a sch = True -> exprNullSafe b sch = True ->
  exprNullSafe (ELogic And a (Just b) TBool) sch = True
exprNullSafeConjoin a b sch pa pb =
  allRefsGuardedAppend sch (nullGuardedRefs a ++ nullGuardedRefs b)
    (exprFieldRefsD a) (exprFieldRefsD b)
    (allRefsGuardedWeakenL sch (nullGuardedRefs a) (nullGuardedRefs b)
       (exprFieldRefsD a) pa)
    (allRefsGuardedWeakenR sch (nullGuardedRefs a) (nullGuardedRefs b)
       (exprFieldRefsD b) pb)

||| Null-safety of an optional clause (`Nothing` is trivially safe).
public export
maybeExprNullSafe : Maybe Expr -> OctadSchema -> Bool
maybeExprNullSafe Nothing  _      = True
maybeExprNullSafe (Just e) schema = exprNullSafe e schema

||| Level-3 decider: NEITHER the WHERE nor the HAVING clause uses a
||| schema-nullable field without an explicit NULL guard. (Statement-
||| indexed because `checkLevel3` checks both clauses; the old predicate
||| only saw WHERE, so it could not even be the checker's soundness
||| target.)
public export
nullSafeStmt : Statement -> OctadSchema -> Bool
nullSafeStmt stmt schema =
  maybeExprNullSafe (whereClause stmt) schema
    && maybeExprNullSafe (having stmt) schema

-- ═══════════════════════════════════════════════════════════════════════
-- Level 1 decider bridge — SchemaBound (Phase 3a)
-- A `= True` resolution check that *builds* the genuine inductive
-- `AllFieldsBound` evidence (each ref carries its `resolveFieldRef … =
-- Just fd` witness). Lets `checkLevel1Sound` connect the checker to the
-- existing (non-vacuous) L1 predicate without disturbing the genuine
-- `Composition.l1Compose` proof, which stays on `Levels.extractFieldRefs`.
-- ═══════════════════════════════════════════════════════════════════════

||| One field reference resolves in the schema.
public export
fieldRefResolves : FieldRef -> OctadSchema -> Bool
fieldRefResolves ref schema =
  case resolveFieldRef ref schema of
    Just _  => True
    Nothing => False

||| Every field reference in the list resolves. Explicit spine recursion
||| (cf. `selectItemsTyped`) so the builder below is one structural step.
public export
allFieldRefsResolve : List FieldRef -> OctadSchema -> Bool
allFieldRefsResolve []        _      = True
allFieldRefsResolve (r :: rs) schema =
  fieldRefResolves r schema && allFieldRefsResolve rs schema

||| `fieldRefResolves = True` yields the genuine `FieldBound` witness
||| (with the actual `resolveFieldRef ref schema = Just fd` equality).
public export
fieldBoundFromResolve :
  (ref : FieldRef) -> (schema : OctadSchema) ->
  fieldRefResolves ref schema = True -> FieldBound ref schema
fieldBoundFromResolve ref schema prf with (resolveFieldRef ref schema) proof q
  fieldBoundFromResolve ref schema prf | Just fd = MkFieldBound ref schema fd q
  fieldBoundFromResolve ref schema prf | Nothing = void (notFalseTrue prf)

||| `allFieldRefsResolve = True` builds the genuine inductive
||| `AllFieldsBound` (this is what makes L1 soundness real, not a
||| re-assertion).
public export
allFieldsBoundFromResolve :
  (refs : List FieldRef) -> (schema : OctadSchema) ->
  allFieldRefsResolve refs schema = True -> AllFieldsBound refs schema
allFieldsBoundFromResolve []        schema _   = NilBound
allFieldsBoundFromResolve (r :: rs) schema prf =
  let (h, t) = andTrueSplit (fieldRefResolves r schema)
                            (allFieldRefsResolve rs schema) prf
  in ConsBound (fieldBoundFromResolve r schema h)
               (allFieldsBoundFromResolve rs schema t)
