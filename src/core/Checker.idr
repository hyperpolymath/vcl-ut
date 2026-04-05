-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Core Checker — 10-Level Progressive Type Checking Pipeline
|||
||| Takes a Statement (Grammar.idr) and an OctadSchema (Schema.idr),
||| runs 10 sequential safety levels (0 through 9), and produces a
||| CheckResult recording the maximum safety level achieved.
|||
||| Levels are checked in order. If a level fails, all subsequent
||| levels are skipped — the result records the highest level passed.
|||
||| @see Levels.idr for the formal proof predicates
||| @see Grammar.idr for Statement / Expr AST definitions
||| @see Schema.idr for OctadSchema / resolveFieldRef

module VqlUt.Core.Checker

import VqlUt.ABI.Types
import VqlUt.Core.Grammar
import VqlUt.Core.Schema
import Data.List
import Data.Maybe

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Check Result
-- ═══════════════════════════════════════════════════════════════════════

||| The result of running the 10-level type checking pipeline on a query.
|||
||| @maxLevel     The highest SafetyLevel that passed all checks.
||| @levelsPassed All levels that passed (in ascending order).
||| @diagnostics  Human-readable messages for each level checked.
||| @valid        True if at least Level 0 passed.
public export
record CheckResult where
  constructor MkCheckResult
  maxLevel     : SafetyLevel
  levelsPassed : List SafetyLevel
  diagnostics  : List String
  valid        : Bool

-- ═══════════════════════════════════════════════════════════════════════
-- SafetyLevel Utilities
-- ═══════════════════════════════════════════════════════════════════════

||| The ordered list of all 10 safety levels, from 0 to 9.
||| Used to drive the sequential checking pipeline.
public export
allLevels : List SafetyLevel
allLevels =
  [ ParseSafe, SchemaBound, TypeCompat, NullSafe, InjectionProof
  , ResultTyped, CardinalitySafe, EffectTracked, TemporalSafe, LinearSafe
  ]

||| Convert a SafetyLevel to a human-readable label string.
public export
safetyLevelLabel : SafetyLevel -> String
safetyLevelLabel ParseSafe       = "L0:ParseSafe"
safetyLevelLabel SchemaBound     = "L1:SchemaBound"
safetyLevelLabel TypeCompat      = "L2:TypeCompat"
safetyLevelLabel NullSafe        = "L3:NullSafe"
safetyLevelLabel InjectionProof  = "L4:InjectionProof"
safetyLevelLabel ResultTyped     = "L5:ResultTyped"
safetyLevelLabel CardinalitySafe = "L6:CardinalitySafe"
safetyLevelLabel EffectTracked   = "L7:EffectTracked"
safetyLevelLabel TemporalSafe    = "L8:TemporalSafe"
safetyLevelLabel LinearSafe      = "L9:LinearSafe"

-- ═══════════════════════════════════════════════════════════════════════
-- Type Compatibility (decidable boolean check for Level 2)
-- ═══════════════════════════════════════════════════════════════════════

||| Decidable structural equality for VqlType.
||| Returns True when two types are the same constructor with matching
||| arguments — used by Level 2 to verify comparison operand types.
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
vqlTypeEq _           _           = False

||| Check whether two VqlTypes are compatible for comparison.
|||
||| Compatible means:
|||   - Same type (structural equality)
|||   - TNull t is compatible with t (and vice versa)
|||   - TInt is compatible with TFloat (numeric widening)
|||
||| This mirrors the TypeCompatible proof type in Grammar.idr but as
||| a decidable boolean suitable for runtime checking.
public export
typesCompatible : VqlType -> VqlType -> Bool
typesCompatible a b =
  if vqlTypeEq a b
    then True
    else case (a, b) of
      -- Null compatibility: TNull t ~ t and t ~ TNull t
      (TNull inner, other) => vqlTypeEq inner other
      (other, TNull inner) => vqlTypeEq other inner
      -- Numeric widening: Int ~ Float
      (TInt, TFloat)       => True
      (TFloat, TInt)       => True
      _                    => False

-- ═══════════════════════════════════════════════════════════════════════
-- Field Reference Extraction
-- ═══════════════════════════════════════════════════════════════════════

||| Recursively extract all FieldRef nodes from an expression tree.
||| Traverses EField, ECompare, ELogic, EAggregate, and ESubquery nodes.
public export
extractFieldRefs : Expr -> List FieldRef
extractFieldRefs (EField ref _)         = [ref]
extractFieldRefs (ELiteral _ _)         = []
extractFieldRefs (ECompare _ l r _)     = extractFieldRefs l ++ extractFieldRefs r
extractFieldRefs (ELogic _ l Nothing _) = extractFieldRefs l
extractFieldRefs (ELogic _ l (Just r) _) = extractFieldRefs l ++ extractFieldRefs r
extractFieldRefs (EAggregate _ e _)     = extractFieldRefs e
extractFieldRefs (EParam _ _)           = []
extractFieldRefs EStar                  = []
extractFieldRefs (ESubquery sub)        = statementFieldRefs sub
  where
    ||| Collect field references from all clauses of a statement.
    ||| Gathers from: selectItems, whereClause, groupBy, having, orderBy.
    statementFieldRefs : Statement -> List FieldRef
    statementFieldRefs stmt =
      let selRefs : List FieldRef
          selRefs = concatMap selItemRefs (selectItems stmt)
          whereRefs : List FieldRef
          whereRefs = maybe [] extractFieldRefs (whereClause stmt)
          groupRefs : List FieldRef
          groupRefs = groupBy stmt
          havingRefs : List FieldRef
          havingRefs = maybe [] extractFieldRefs (having stmt)
          orderRefs : List FieldRef
          orderRefs = map fst (orderBy stmt)
      in selRefs ++ whereRefs ++ groupRefs ++ havingRefs ++ orderRefs

    ||| Extract field references from a single SELECT item.
    selItemRefs : SelectItem -> List FieldRef
    selItemRefs (SelField ref)       = [ref]
    selItemRefs (SelModality _)      = []
    selItemRefs (SelAggregate _ e)   = extractFieldRefs e
    selItemRefs SelStar              = []

||| Collect all field references from every clause of a statement.
||| Delegates to extractFieldRefs for each expression-bearing clause.
public export
statementFieldRefs : Statement -> List FieldRef
statementFieldRefs stmt =
  let selRefs : List FieldRef
      selRefs = concatMap selItemFieldRefs (selectItems stmt)
      whereRefs : List FieldRef
      whereRefs = maybe [] extractFieldRefs (whereClause stmt)
      groupRefs : List FieldRef
      groupRefs = groupBy stmt
      havingRefs : List FieldRef
      havingRefs = maybe [] extractFieldRefs (having stmt)
      orderRefs : List FieldRef
      orderRefs = map fst (orderBy stmt)
  in selRefs ++ whereRefs ++ groupRefs ++ havingRefs ++ orderRefs
  where
    ||| Extract field references from a single SELECT item.
    selItemFieldRefs : SelectItem -> List FieldRef
    selItemFieldRefs (SelField ref)       = [ref]
    selItemFieldRefs (SelModality _)      = []
    selItemFieldRefs (SelAggregate _ e)   = extractFieldRefs e
    selItemFieldRefs SelStar              = []

-- ═══════════════════════════════════════════════════════════════════════
-- Expression Scanning Helpers
-- ═══════════════════════════════════════════════════════════════════════

||| Extract all ECompare sub-expressions from an expression tree.
||| Returns a list of (operator, left, right, annotatedType) tuples.
extractComparisons : Expr -> List (CompOp, Expr, Expr, VqlType)
extractComparisons (ECompare op l r ty) =
  (op, l, r, ty) :: extractComparisons l ++ extractComparisons r
extractComparisons (ELogic _ l Nothing _) = extractComparisons l
extractComparisons (ELogic _ l (Just r) _) =
  extractComparisons l ++ extractComparisons r
extractComparisons (EAggregate _ e _) = extractComparisons e
extractComparisons _ = []

||| Resolve the VqlType of an expression using the schema.
||| For EField nodes, looks up the field in the schema.
||| For other nodes, returns the annotation type already on the node.
resolveExprType : Expr -> OctadSchema -> VqlType
resolveExprType (EField ref _) schema    = resolveType ref schema
resolveExprType (ELiteral _ ty) _        = ty
resolveExprType (ECompare _ _ _ ty) _    = ty
resolveExprType (ELogic _ _ _ ty) _      = ty
resolveExprType (EAggregate _ _ ty) _    = ty
resolveExprType (EParam _ ty) _          = ty
resolveExprType EStar _                  = TAny
resolveExprType (ESubquery _) _          = TOctad

||| Check whether an expression contains any ELiteral (LitString _) nodes.
||| Used by Level 4 to detect potential injection vectors.
containsLiteralString : Expr -> Bool
containsLiteralString (ELiteral (LitString _) _) = True
containsLiteralString (ECompare _ l r _)          =
  containsLiteralString l || containsLiteralString r
containsLiteralString (ELogic _ l Nothing _)      = containsLiteralString l
containsLiteralString (ELogic _ l (Just r) _)     =
  containsLiteralString l || containsLiteralString r
containsLiteralString (EAggregate _ e _)           = containsLiteralString e
containsLiteralString _                            = False

||| Resolve the type of a SelectItem using the schema.
||| Returns TAny if the item's type cannot be determined.
resolveSelectItemType : SelectItem -> OctadSchema -> VqlType
resolveSelectItemType (SelField ref) schema =
  resolveType ref schema
resolveSelectItemType (SelModality _) _ = TOctad
resolveSelectItemType (SelAggregate _ e) schema =
  resolveExprType e schema
resolveSelectItemType SelStar _ = TAny

||| Check if a nullable field is used without a null guard in an expression.
||| A "null guard" is an ECompare with Eq/NotEq against LitNull.
||| Returns the list of unguarded nullable field references.
findUnguardedNullableFields : Expr -> OctadSchema -> List FieldRef
findUnguardedNullableFields expr schema =
  let refs : List FieldRef
      refs = extractFieldRefs expr
      guarded : List FieldRef
      guarded = findNullGuardedRefs expr
  in filter (\ref => isNullable ref schema && not (elemBy fieldRefEq ref guarded)) refs
  where
    ||| Structural equality for FieldRef (same modality + field name).
    fieldRefEq : FieldRef -> FieldRef -> Bool
    fieldRefEq a b =
      modalityToInt (modality a) == modalityToInt (modality b) &&
      fieldName a == fieldName b

    ||| Find all field refs that appear in a null-check pattern:
    ||| ECompare Eq (EField ref _) (ELiteral LitNull _) or symmetric.
    findNullGuardedRefs : Expr -> List FieldRef
    findNullGuardedRefs (ECompare Eq (EField ref _) (ELiteral LitNull _) _) = [ref]
    findNullGuardedRefs (ECompare Eq (ELiteral LitNull _) (EField ref _) _) = [ref]
    findNullGuardedRefs (ECompare NotEq (EField ref _) (ELiteral LitNull _) _) = [ref]
    findNullGuardedRefs (ECompare NotEq (ELiteral LitNull _) (EField ref _) _) = [ref]
    findNullGuardedRefs (ECompare _ l r _) =
      findNullGuardedRefs l ++ findNullGuardedRefs r
    findNullGuardedRefs (ELogic _ l Nothing _) = findNullGuardedRefs l
    findNullGuardedRefs (ELogic _ l (Just r) _) =
      findNullGuardedRefs l ++ findNullGuardedRefs r
    findNullGuardedRefs _ = []

-- ═══════════════════════════════════════════════════════════════════════
-- Individual Level Checks
-- ═══════════════════════════════════════════════════════════════════════

||| Level 0 — ParseSafe: always passes if we have a Statement.
||| A Statement is proof of successful parsing by construction.
|||
||| @stmt The parsed statement to check.
||| @return (True, diagnostic) unconditionally.
public export
checkLevel0 : Statement -> (Bool, String)
checkLevel0 _ = (True, "L0:ParseSafe — statement parsed successfully")

||| Level 1 — SchemaBound: every field reference in the statement
||| resolves to a known field in the OctadSchema.
|||
||| @stmt   The statement whose field references to validate.
||| @schema The octad schema to resolve against.
||| @return (True, _) if all refs resolve; (False, diagnostic) otherwise.
public export
checkLevel1 : Statement -> OctadSchema -> (Bool, String)
checkLevel1 stmt schema =
  let refs : List FieldRef
      refs = statementFieldRefs stmt
      unresolved : List FieldRef
      unresolved = filter (\ref => isNothing (resolveFieldRef ref schema)) refs
  in case unresolved of
    [] => (True, "L1:SchemaBound — all " ++ show (length refs) ++ " field refs resolve")
    (r :: _) =>
      ( False
      , "L1:SchemaBound FAILED — unresolved field: "
          ++ modalityName (modality r) ++ "." ++ fieldName r
      )

||| Level 2 — TypeCompat: every comparison expression uses operands
||| with compatible types (same type, null compat, or int/float widening).
|||
||| Extracts all ECompare nodes from the WHERE clause and checks that the
||| resolved types of both operands are compatible via typesCompatible.
|||
||| @stmt   The statement to check.
||| @schema The schema for type resolution.
||| @return (True, _) if all comparisons type-check; (False, diagnostic) otherwise.
public export
checkLevel2 : Statement -> OctadSchema -> (Bool, String)
checkLevel2 stmt schema =
  case whereClause stmt of
    Nothing => (True, "L2:TypeCompat — no WHERE clause, trivially compatible")
    Just wExpr =>
      let comps : List (CompOp, Expr, Expr, VqlType)
          comps = extractComparisons wExpr
          incompatible : List (CompOp, Expr, Expr, VqlType)
          incompatible = filter (not . isCompatibleComparison) comps
      in case incompatible of
        [] => (True, "L2:TypeCompat — all " ++ show (length comps) ++ " comparisons type-safe")
        _  => (False, "L2:TypeCompat FAILED — " ++ show (length incompatible) ++ " incompatible comparison(s)")
  where
    ||| Check that a single comparison's operands have compatible types.
    isCompatibleComparison : (CompOp, Expr, Expr, VqlType) -> Bool
    isCompatibleComparison (_, l, r, _) =
      typesCompatible (resolveExprType l schema) (resolveExprType r schema)

||| Level 3 — NullSafe: nullable fields must be guarded with null checks.
||| Any nullable field used in WHERE or HAVING without an IS NULL / IS NOT NULL
||| check causes this level to fail.
|||
||| @stmt   The statement to check.
||| @schema The schema providing nullability information.
||| @return (True, _) if no unguarded nullable fields; (False, diagnostic) otherwise.
public export
checkLevel3 : Statement -> OctadSchema -> (Bool, String)
checkLevel3 stmt schema =
  let whereUnguarded : List FieldRef
      whereUnguarded = maybe [] (\e => findUnguardedNullableFields e schema) (whereClause stmt)
      havingUnguarded : List FieldRef
      havingUnguarded = maybe [] (\e => findUnguardedNullableFields e schema) (having stmt)
      allUnguarded : List FieldRef
      allUnguarded = whereUnguarded ++ havingUnguarded
  in case allUnguarded of
    [] => (True, "L3:NullSafe — all nullable fields are guarded")
    (r :: _) =>
      ( False
      , "L3:NullSafe FAILED — unguarded nullable field: "
          ++ modalityName (modality r) ++ "." ++ fieldName r
      )

||| Level 4 — InjectionProof: no raw string literals in the WHERE clause.
||| All user-controlled values must arrive via EParam nodes (parameterised
||| queries). Any ELiteral (LitString _) in the WHERE tree is treated as
||| a potential injection vector.
|||
||| @stmt The statement to check.
||| @return (True, _) if WHERE contains no literal strings; (False, diagnostic) otherwise.
public export
checkLevel4 : Statement -> (Bool, String)
checkLevel4 stmt =
  case whereClause stmt of
    Nothing => (True, "L4:InjectionProof — no WHERE clause, no injection risk")
    Just wExpr =>
      if containsLiteralString wExpr
        then (False, "L4:InjectionProof FAILED — raw string literal in WHERE clause")
        else (True, "L4:InjectionProof — WHERE uses only parameterised inputs")

||| Level 5 — ResultTyped: every SELECT item resolves to a known type
||| (not TAny). Ensures the result set schema is fully determined.
|||
||| @stmt   The statement to check.
||| @schema The schema for type resolution.
||| @return (True, _) if no TAny in select types; (False, diagnostic) otherwise.
public export
checkLevel5 : Statement -> OctadSchema -> (Bool, String)
checkLevel5 stmt schema =
  let items : List SelectItem
      items = selectItems stmt
      untypedItems : List SelectItem
      untypedItems = filter (\item => isAnyType (resolveSelectItemType item schema)) items
  in case untypedItems of
    [] => (True, "L5:ResultTyped — all " ++ show (length items) ++ " select items have known types")
    _  => (False, "L5:ResultTyped FAILED — " ++ show (length untypedItems) ++ " select item(s) have unresolved types")
  where
    ||| Check if a VqlType is the unresolved TAny sentinel.
    isAnyType : VqlType -> Bool
    isAnyType TAny = True
    isAnyType _    = False

||| Level 6 — CardinalitySafe: the statement includes a LIMIT clause.
||| Queries that could return unbounded results must have an explicit
||| LIMIT to prevent resource exhaustion.
|||
||| @stmt The statement to check.
||| @return (True, _) if LIMIT is present; (False, diagnostic) otherwise.
public export
checkLevel6 : Statement -> (Bool, String)
checkLevel6 stmt =
  case limit stmt of
    Just n  => (True, "L6:CardinalitySafe — LIMIT " ++ show n ++ " present")
    Nothing => (False, "L6:CardinalitySafe FAILED — no LIMIT clause on query")

||| Level 7 — EffectTracked: the statement includes an EFFECTS declaration.
||| Side-effectful operations (INSERT/UPDATE/DELETE) must declare their
||| effects so callers can track and compose them safely.
|||
||| @stmt The statement to check.
||| @return (True, _) if effectDecl is present; (False, diagnostic) otherwise.
public export
checkLevel7 : Statement -> (Bool, String)
checkLevel7 stmt =
  case effectDecl stmt of
    Just _  => (True, "L7:EffectTracked — effect declaration present")
    Nothing => (False, "L7:EffectTracked FAILED — no EFFECTS declaration")

||| Level 8 — TemporalSafe: the statement includes a version constraint.
||| Queries against VeriSimDB's time-travel engine must specify temporal
||| bounds (AT LATEST, AT VERSION >=, etc.) to avoid indeterminate results.
|||
||| @stmt The statement to check.
||| @return (True, _) if versionConst is present; (False, diagnostic) otherwise.
public export
checkLevel8 : Statement -> (Bool, String)
checkLevel8 stmt =
  case versionConst stmt of
    Just _  => (True, "L8:TemporalSafe — version constraint present")
    Nothing => (False, "L8:TemporalSafe FAILED — no version constraint")

||| Level 9 — LinearSafe: the statement includes a linearity annotation
||| with an actual consumption constraint (LinUseOnce or LinBounded).
||| LinUnlimited is not sufficient — it must enforce resource linearity.
|||
||| @stmt The statement to check.
||| @return (True, _) if a consume constraint is present; (False, diagnostic) otherwise.
public export
checkLevel9 : Statement -> (Bool, String)
checkLevel9 stmt =
  case linearAnnot stmt of
    Nothing          => (False, "L9:LinearSafe FAILED — no linearity annotation")
    Just LinUnlimited => (False, "L9:LinearSafe FAILED — LinUnlimited is not a consume constraint")
    Just LinUseOnce  => (True, "L9:LinearSafe — consume-after-1-use constraint present")
    Just (LinBounded _) => (True, "L9:LinearSafe — bounded usage constraint present")

-- ═══════════════════════════════════════════════════════════════════════
-- Pipeline Runner
-- ═══════════════════════════════════════════════════════════════════════

||| Internal accumulator for the pipeline: tracks levels passed so far.
|||
||| @lastPassed  The most recent level that passed.
||| @passed      Levels that passed, in order.
||| @diags       Accumulated diagnostics for every level checked.
record PipelineState where
  constructor MkPipelineState
  lastPassed : SafetyLevel
  passed     : List SafetyLevel
  diags      : List String

||| Dispatch a single level check. Routes to the appropriate checkLevelN
||| function based on the SafetyLevel tag.
|||
||| Levels 0, 4, 6, 7, 8, 9 only need the Statement.
||| Levels 1, 2, 3, 5 also need the OctadSchema.
dispatchLevel : SafetyLevel -> Statement -> OctadSchema -> (Bool, String)
dispatchLevel ParseSafe       stmt _      = checkLevel0 stmt
dispatchLevel SchemaBound     stmt schema = checkLevel1 stmt schema
dispatchLevel TypeCompat      stmt schema = checkLevel2 stmt schema
dispatchLevel NullSafe        stmt schema = checkLevel3 stmt schema
dispatchLevel InjectionProof  stmt _      = checkLevel4 stmt
dispatchLevel ResultTyped     stmt schema = checkLevel5 stmt schema
dispatchLevel CardinalitySafe stmt _      = checkLevel6 stmt
dispatchLevel EffectTracked   stmt _      = checkLevel7 stmt
dispatchLevel TemporalSafe    stmt _      = checkLevel8 stmt
dispatchLevel LinearSafe      stmt _      = checkLevel9 stmt

||| Run the pipeline over a list of remaining levels, stopping at the
||| first failure. Accumulates results into PipelineState.
|||
||| @levels  Remaining levels to check (in ascending order).
||| @stmt    The statement under test.
||| @schema  The octad schema for resolution.
||| @state   Current accumulated pipeline state.
||| @return  Final pipeline state after all levels pass or one fails.
runPipeline : (levels : List SafetyLevel)
           -> Statement
           -> OctadSchema
           -> PipelineState
           -> (PipelineState, Maybe String)
runPipeline []            _    _      state = (state, Nothing)
runPipeline (lvl :: rest) stmt schema state =
  let (ok, diag) = dispatchLevel lvl stmt schema
      newDiags : List String
      newDiags = state.diags ++ [diag]
  in if ok
    then runPipeline rest stmt schema
           (MkPipelineState lvl (state.passed ++ [lvl]) newDiags)
    else (MkPipelineState state.lastPassed state.passed newDiags, Just diag)

-- ═══════════════════════════════════════════════════════════════════════
-- Main Entry Point
-- ═══════════════════════════════════════════════════════════════════════

||| Run the full 10-level VCL-total type checking pipeline.
|||
||| Checks levels 0 through 9 in order. Each level either passes (and
||| the pipeline advances) or fails (and the pipeline stops). The result
||| captures the maximum safety level achieved, the full list of passed
||| levels, and diagnostic messages for every level that was checked.
|||
||| **Example:**
|||   If a query passes levels 0-4 and fails at level 5, the result will
|||   have maxLevel = InjectionProof, levelsPassed = [ParseSafe .. InjectionProof],
|||   and valid = True.
|||
||| @stmt   The parsed VCL-total statement to check.
||| @schema The VeriSimDB octad schema to validate against.
||| @return A CheckResult with the achieved safety level and diagnostics.
public export
checkQuery : Statement -> OctadSchema -> CheckResult
checkQuery stmt schema =
  let initState : PipelineState
      initState = MkPipelineState ParseSafe [] []
      (finalState, mFailure) = runPipeline allLevels stmt schema initState
  in case finalState.passed of
    [] =>
      -- Level 0 itself failed — should not happen (ParseSafe always passes)
      -- but we handle it for totality.
      MkCheckResult ParseSafe [] finalState.diags False
    _  =>
      MkCheckResult
        finalState.lastPassed
        finalState.passed
        finalState.diags
        True
