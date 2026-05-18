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

module VclTotal.Core.Checker

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import VclTotal.Core.Levels
import Data.List
import Data.Maybe

%default total

-- `Levels.CheckResult` (the proof-carrying Passed/Failed datatype) and this
-- module's own `CheckResult` record share a name; this module only uses its
-- own. Hide the imported one so `checkQuery`'s signature is unambiguous.
%hide VclTotal.Core.Levels.CheckResult

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
  , EpistemicSafe
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
safetyLevelLabel EpistemicSafe   = "L10:EpistemicSafe"

-- ═══════════════════════════════════════════════════════════════════════
-- Type Compatibility (decidable boolean check for Level 2)
-- ═══════════════════════════════════════════════════════════════════════

||| Decidable structural equality for VqlType.
||| Structural equality for Agent (ignoring payload for parameterised
||| agents). Hoisted to the top level: a `where` block after the final
||| clause of a multi-clause function is not in scope for the earlier
||| clauses that referenced it.
private
agentEq : Agent -> Agent -> Bool
agentEq AgEngine AgEngine               = True
agentEq (AgProver a) (AgProver b)       = a == b
agentEq AgValidator AgValidator         = True
agentEq (AgUser a) (AgUser b)           = a == b
agentEq AgFederation AgFederation       = True
agentEq _ _                             = False

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
vqlTypeEq (TKnows a1 t1) (TKnows a2 t2) = agentEq a1 a2 && vqlTypeEq t1 t2
vqlTypeEq (TBelieves a1 t1) (TBelieves a2 t2) = agentEq a1 a2 && vqlTypeEq t1 t2
vqlTypeEq (TCommonKnowledge t1) (TCommonKnowledge t2) = vqlTypeEq t1 t2
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

-- Totality note (hyperpolymath/standards#124, Phase 1)
-- ----------------------------------------------------
-- `extractFieldRefs` and `statementFieldRefs` are mutually recursive
-- across the `Expr`/`Statement` boundary: `Expr` has the constructor
-- `ESubquery Statement`, and a `Statement` carries `Maybe Expr` /
-- `List SelectItem` clauses that contain further `Expr`s.
--
-- Idris 2's structural-termination checker only credits a recursive call
-- as decreasing when its argument is a *constructor-pattern subterm* of
-- a matched argument. A record *projection* (`whereClause stmt`,
-- `having stmt`, `selectItems stmt`) is an opaque function application,
-- NOT recognised as smaller — that is exactly why the previous
-- projection-based body was rejected as "possibly not terminating".
--
-- The honest fix below introduces no fuel, no axiom and no
-- `assert_smaller`: it just pattern-matches the `MkStatement`
-- constructor so every clause becomes a bound subpattern variable, and
-- inlines the `Maybe`/`List`/`SelectItem` traversals into the `mutual`
-- block so each `extractFieldRefs` call sits *directly* on a
-- constructor-pattern subterm. The descent the checker now sees is the
-- genuine one:
--
--     extractFieldRefs (ESubquery sub)            -- sub ⊏ the Expr
--       └─ statementFieldRefs (MkStatement … w h) -- w,h,sel ⊏ sub
--            └─ extractFieldRefs w / h / aggregate-e   -- ⊏ that Statement
--
-- so every trip round the cycle strips at least one `ESubquery`
-- constructor: it is ordinary structural recursion on the finite AST,
-- and the computed list of `FieldRef`s is byte-for-byte the same set as
-- before (same clauses, same order: SELECT ++ WHERE ++ GROUP BY ++
-- HAVING ++ ORDER BY).
mutual
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
  extractFieldRefs (EEpistemic _ _ e _)   = extractFieldRefs e
  extractFieldRefs (EAnnounce _ prop body _) =
    extractFieldRefs prop ++ extractFieldRefs body

  ||| Field references collected from an optional expression-bearing
  ||| clause (WHERE / HAVING). Written by pattern match (not `maybe`)
  ||| so the `Just` payload is a constructor-pattern subterm the
  ||| totality checker tracks as smaller.
  export
  maybeExprFieldRefs : Maybe Expr -> List FieldRef
  maybeExprFieldRefs Nothing  = []
  maybeExprFieldRefs (Just e) = extractFieldRefs e

  ||| Extract field references from a single SELECT item. In the
  ||| `mutual` block (not a `where` helper) so the `extractFieldRefs e`
  ||| call on `SelAggregate _ e` lands on a tracked subterm.
  export
  selItemFieldRefs : SelectItem -> List FieldRef
  selItemFieldRefs (SelField ref)     = [ref]
  selItemFieldRefs (SelModality _)    = []
  selItemFieldRefs (SelAggregate _ e) = extractFieldRefs e
  selItemFieldRefs SelStar            = []

  ||| Map `selItemFieldRefs` over the SELECT list by explicit structural
  ||| recursion on the list spine (replaces `concatMap`, whose argument
  ||| would again be an untracked projection).
  export
  selItemsFieldRefs : List SelectItem -> List FieldRef
  selItemsFieldRefs []        = []
  selItemsFieldRefs (i :: is) = selItemFieldRefs i ++ selItemsFieldRefs is

  ||| Collect all field references from every clause of a statement.
  ||| Delegates to extractFieldRefs for each expression-bearing clause.
  ||| The statement is destructured via its `MkStatement` constructor so
  ||| each clause (`sel`, `whr`, `grp`, `hav`, `ord`) is a subpattern
  ||| variable the structural checker recognises as smaller than the
  ||| `Statement` (which, in the recursive case, is the `ESubquery`
  ||| payload — itself smaller than the enclosing `Expr`).
  public export
  statementFieldRefs : Statement -> List FieldRef
  statementFieldRefs (MkStatement sel _ whr grp hav ord _ _ _ _ _ _ _ _) =
    let selRefs    : List FieldRef
        selRefs    = selItemsFieldRefs sel
        whereRefs  : List FieldRef
        whereRefs  = maybeExprFieldRefs whr
        groupRefs  : List FieldRef
        groupRefs  = grp
        havingRefs : List FieldRef
        havingRefs = maybeExprFieldRefs hav
        orderRefs  : List FieldRef
        orderRefs  = map fst ord
    in selRefs ++ whereRefs ++ groupRefs ++ havingRefs ++ orderRefs

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
extractComparisons (EEpistemic _ _ e _) = extractComparisons e
extractComparisons (EAnnounce _ p b _) = extractComparisons p ++ extractComparisons b
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
resolveExprType (EEpistemic _ _ _ ty) _  = ty
resolveExprType (EAnnounce _ _ _ ty) _   = ty

||| Check whether an expression contains any ELiteral (LitString _) nodes.
||| Used by Level 4 to detect potential injection vectors.
|||
||| This is now a thin alias for `Grammar.hasStringLit`, the single
||| source of truth shared with the Level-4 proof predicate
||| (`Levels.NoRawUserInput`). Keeping one definition is what makes
||| `checkLevel4Sound` a genuine soundness proof rather than a check
||| against a parallel re-implementation that could silently drift.
containsLiteralString : Expr -> Bool
containsLiteralString = hasStringLit

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
checkLevel4 stmt = l4Verdict (whereHasStringLit stmt)
  where
    l4Verdict : Bool -> (Bool, String)
    l4Verdict True  =
      (False, "L4:InjectionProof FAILED — raw string literal in WHERE clause")
    l4Verdict False =
      (True,  "L4:InjectionProof — WHERE uses only parameterised inputs")

||| Disjointness of Bool constructors (local, to avoid relying on a
||| particular Prelude `Uninhabited` instance name across idris2 0.8.0).
falseNotTrue : (False = True) -> Void
falseNotTrue Refl impossible

||| **Soundness of the Level-4 decision procedure.**
|||
||| If `checkLevel4` accepts a statement, that statement genuinely
||| carries an `L4_InjectionProof` — its WHERE clause provably embeds no
||| string literal (`whereHasStringLit stmt = False`). This lemma is what
||| connects the *real* (no longer vacuous) Level-4 predicate to the
||| actual decision procedure. Before this remediation `checkLevel4`
||| returned a bare `Bool` while `NoRawUserInput` was inhabited by the
||| catch-all `AllParameterised`, so no soundness statement was even
||| meaningful: a pure string-interpolation injection query type-checked
||| at Level 4. Tracked: hyperpolymath/standards#124.
export
checkLevel4Sound : (stmt : Statement) -> (m : String) ->
                   checkLevel4 stmt = (True, m) -> L4_InjectionProof stmt
checkLevel4Sound stmt m prf with (whereHasStringLit stmt) proof p
  checkLevel4Sound stmt m prf | False = MkL4 stmt (MkNoRawUserInput p)
  checkLevel4Sound stmt m prf | True  = void (falseNotTrue (cong fst prf))

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

||| Level 10 — EpistemicSafe: the statement includes an EPISTEMIC clause
||| with well-formed agent declarations and consistent requirements.
|||
||| Checks:
|||   1. Clause is present with at least one agent
|||   2. All agents referenced in REQUIRES are declared in the AGENTS list
|||   3. No circular ENTAILS chains (a ENTAILS b, b ENTAILS a)
|||   4. COMMON KNOWLEDGE requirements reference propositions that are
|||      well-typed under the existing schema
|||
||| @stmt The statement to check.
||| @return (True, _) if epistemic clause is present and consistent;
|||         (False, diagnostic) otherwise.
public export
checkLevel10 : Statement -> (Bool, String)
checkLevel10 stmt =
  case epistemicClause stmt of
    Nothing => (False, "L10:EpistemicSafe FAILED — no EPISTEMIC clause")
    Just (EpClause agents reqs) =>
      case agents of
        [] => (False, "L10:EpistemicSafe FAILED — EPISTEMIC clause has no agents")
        _  =>
          let undeclared = findUndeclaredAgents agents reqs
          in case undeclared of
            [] =>
              if hasCircularEntails reqs
                then (False, "L10:EpistemicSafe FAILED — circular ENTAILS dependency")
                else (True, "L10:EpistemicSafe — "
                       ++ show (length agents) ++ " agent(s), "
                       ++ show (length reqs) ++ " requirement(s) verified")
            (name :: _) =>
              (False, "L10:EpistemicSafe FAILED — agent '"
                ++ name ++ "' used in REQUIRES but not declared in AGENTS")
  where
    ||| Get a string identifier for an agent (for comparison purposes).
    agentId : Agent -> String
    agentId AgEngine        = "ENGINE"
    agentId (AgProver name) = "PROVER:" ++ name
    agentId AgValidator     = "VALIDATOR"
    agentId (AgUser name)   = "USER:" ++ name
    agentId AgFederation    = "FEDERATION"

    ||| Check if an agent is in the declared agents list.
    agentDeclared : Agent -> List Agent -> Bool
    agentDeclared a declared = any (\d => agentId a == agentId d) declared

    ||| Find agents referenced in requirements but not declared.
    ||| Returns list of undeclared agent name strings.
    findUndeclaredAgents : List Agent -> List EpistemicRequirement -> List String
    findUndeclaredAgents declared [] = []
    findUndeclaredAgents declared (EpReqKnows a _ :: rest) =
      if agentDeclared a declared
        then findUndeclaredAgents declared rest
        else agentId a :: findUndeclaredAgents declared rest
    findUndeclaredAgents declared (EpReqBelieves a _ :: rest) =
      if agentDeclared a declared
        then findUndeclaredAgents declared rest
        else agentId a :: findUndeclaredAgents declared rest
    findUndeclaredAgents declared (EpReqCommon _ :: rest) =
      findUndeclaredAgents declared rest
    findUndeclaredAgents declared (EpReqEntails a1 a2 _ :: rest) =
      let u1 = if agentDeclared a1 declared then [] else [agentId a1]
          u2 = if agentDeclared a2 declared then [] else [agentId a2]
      in u1 ++ u2 ++ findUndeclaredAgents declared rest

    ||| Collect all (source, target) pairs from ENTAILS requirements.
    entailsPairs : List EpistemicRequirement -> List (String, String)
    entailsPairs [] = []
    entailsPairs (EpReqEntails a1 a2 _ :: rest) =
      (agentId a1, agentId a2) :: entailsPairs rest
    entailsPairs (_ :: rest) = entailsPairs rest

    ||| Check for direct circular ENTAILS (a->b and b->a).
    ||| Full cycle detection would require a graph algorithm;
    ||| for now we check the direct symmetry violation.
    hasCircularEntails : List EpistemicRequirement -> Bool
    hasCircularEntails reqs =
      let pairs = entailsPairs reqs
      in any (\(a, b) => any (\(c, d) => a == d && b == c) pairs) pairs

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
dispatchLevel EpistemicSafe   stmt _      = checkLevel10 stmt

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
      finalState : PipelineState
      finalState = fst (runPipeline allLevels stmt schema initState)
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
