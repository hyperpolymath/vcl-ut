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
import VclTotal.Core.Decide
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

-- `agentEq` / `vqlTypeEq` / `typesCompatible` moved to
-- `VclTotal.Core.Decide` (Phase 2, standards#124): the Level-2 proof
-- predicate `AllComparisonsTypeSafe` and `checkLevel2` must decide via
-- the SAME function so `checkLevel2Sound` cannot drift. Imported above.

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

-- `extractComparisons` moved to `VclTotal.Core.Decide` (Phase 2,
-- standards#124) — single source of truth for the L2 predicate +
-- checkLevel2 (see note in the Type-Compatibility region above).

-- `resolveExprType` / `resolveSelectItemType` moved to
-- `VclTotal.Core.Decide` (Phase 2, standards#124): the Level-2 / Level-5
-- proof predicates and these checker queries must be the SAME function,
-- so the soundness lemmas cannot drift. Imported, used unqualified below.

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

-- `resolveSelectItemType` now lives in `VclTotal.Core.Decide` (see note
-- above); `checkLevel5` is defined through `Decide.selectItemsTyped`.

-- `findUnguardedNullableFields` (and its `fieldRefEq` /
-- `findNullGuardedRefs` helpers) moved to `VclTotal.Core.Decide` as
-- `nullSafeStmt` / `nullGuardedRefs` / `fieldRefEq` (Phase 2,
-- standards#124): the L3 proof predicate and `checkLevel3` now decide
-- via the SAME function, so `checkLevel3Sound` cannot drift.

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
|||
||| Decided through `Decide.allFieldRefsResolve` over BOTH ref extractors:
||| `statementFieldRefs` (the thorough, subquery-descending one — the
||| original, behaviour-preserving check) AND `Levels.extractFieldRefs`
||| (the extractor the L1 *predicate* `AllFieldsBound (extractFieldRefs
||| stmt)` is stated over). The second conjunct is the drift-free
||| soundness hook for `checkLevel1Sound`; since every ref of
||| `Levels.extractFieldRefs stmt` is also a ref of `statementFieldRefs
||| stmt` (the latter does strictly more — it also descends `ESubquery`),
||| it never changes the verdict. We keep the predicate on
||| `Levels.extractFieldRefs` so the genuine `Composition.l1Compose`
||| proof is untouched. Tracked: hyperpolymath/standards#124.
public export
checkLevel1 : Statement -> OctadSchema -> (Bool, String)
checkLevel1 stmt schema =
    l1Verdict (allFieldRefsResolve (statementFieldRefs stmt) schema
                 && allFieldRefsResolve (Levels.extractFieldRefs stmt) schema)
  where
    l1Verdict : Bool -> (Bool, String)
    l1Verdict True  =
      (True,  "L1:SchemaBound — all field refs resolve in the schema")
    l1Verdict False =
      (False, "L1:SchemaBound FAILED — an unresolved field reference")

||| **Soundness of the Level-1 decision procedure.**
||| If `checkLevel1` accepts, the statement genuinely carries an
||| `L1_SchemaBound`: every field reference of `extractFieldRefs stmt`
||| resolves, witnessed by the *inductive* `AllFieldsBound` built by
||| `Decide.allFieldsBoundFromResolve` (each `FieldBound` carries the
||| real `resolveFieldRef ref schema = Just fd`). Tracked: standards#124.
export
checkLevel1Sound : (stmt : Statement) -> (schema : OctadSchema) ->
                   (m : String) ->
                   checkLevel1 stmt schema = (True, m) ->
                   L1_SchemaBound stmt schema
checkLevel1Sound stmt schema m prf
    with (allFieldRefsResolve (statementFieldRefs stmt) schema
            && allFieldRefsResolve (Levels.extractFieldRefs stmt) schema)
         proof p
  checkLevel1Sound stmt schema m prf | True =
    let (_, c2) = andTrueSplit
                    (allFieldRefsResolve (statementFieldRefs stmt) schema)
                    (allFieldRefsResolve (Levels.extractFieldRefs stmt) schema)
                    p
    in MkL1 stmt schema
         (allFieldsBoundFromResolve (Levels.extractFieldRefs stmt) schema c2)
  checkLevel1Sound stmt schema m prf | False =
    void (notFalseTrue (cong fst prf))

||| Level 2 — TypeCompat: every comparison expression uses operands
||| with compatible types (same type, null compat, or int/float widening).
|||
||| Extracts all ECompare nodes from the WHERE clause and checks that the
||| resolved types of both operands are compatible via typesCompatible.
|||
||| @stmt   The statement to check.
||| @schema The schema for type resolution.
||| @return (True, _) if all comparisons type-check; (False, diagnostic) otherwise.
|||
||| Defined through the shared decider `Decide.whereComparisonsCompatible`
||| (the same function the L2 proof predicate `AllComparisonsTypeSafe`
||| carries), so `checkLevel2Sound` is a genuine soundness statement.
public export
checkLevel2 : Statement -> OctadSchema -> (Bool, String)
checkLevel2 stmt schema =
    l2Verdict (whereComparisonsCompatible (whereClause stmt) schema)
  where
    l2Verdict : Bool -> (Bool, String)
    l2Verdict True  =
      (True,  "L2:TypeCompat — all WHERE comparisons have compatible types")
    l2Verdict False =
      (False, "L2:TypeCompat FAILED — incompatible comparison operand types")

||| **Soundness of the Level-2 decision procedure.**
||| If `checkLevel2` accepts, the statement genuinely carries an
||| `L2_TypeCompat`: every `ECompare` in the WHERE clause has operands of
||| compatible resolved types
||| (`whereComparisonsCompatible (whereClause stmt) schema = True`).
||| Before Phase 2 `AllComparisonsTypeSafe` was inhabited by the
||| content-free `WhereTypeSafe …`, so this was not even meaningful.
||| Mirrors `checkLevel4Sound`. Tracked: hyperpolymath/standards#124.
export
checkLevel2Sound : (stmt : Statement) -> (schema : OctadSchema) ->
                   (m : String) ->
                   checkLevel2 stmt schema = (True, m) ->
                   L2_TypeCompat stmt schema
checkLevel2Sound stmt schema m prf
    with (whereComparisonsCompatible (whereClause stmt) schema) proof p
  checkLevel2Sound stmt schema m prf | True  =
    MkL2 stmt schema (MkAllCompat p)
  checkLevel2Sound stmt schema m prf | False =
    void (notFalseTrue (cong fst prf))

||| Level 3 — NullSafe: nullable fields must be guarded with null checks.
||| Any nullable field used in WHERE or HAVING without an IS NULL / IS NOT NULL
||| check causes this level to fail.
|||
||| @stmt   The statement to check.
||| @schema The schema providing nullability information.
||| @return (True, _) if no unguarded nullable fields; (False, diagnostic) otherwise.
|||
||| Defined through the shared decider `Decide.nullSafeStmt` (the same
||| function the L3 proof predicate `AllNullableFieldsGuarded` carries),
||| so `checkLevel3Sound` is a genuine soundness statement.
public export
checkLevel3 : Statement -> OctadSchema -> (Bool, String)
checkLevel3 stmt schema = l3Verdict (nullSafeStmt stmt schema)
  where
    l3Verdict : Bool -> (Bool, String)
    l3Verdict True  =
      (True,  "L3:NullSafe — all nullable fields are guarded (WHERE + HAVING)")
    l3Verdict False =
      (False, "L3:NullSafe FAILED — unguarded nullable field in WHERE/HAVING")

||| **Soundness of the Level-3 decision procedure.**
||| If `checkLevel3` accepts, the statement genuinely carries an
||| `L3_NullSafe`: neither WHERE nor HAVING uses a schema-nullable field
||| without an explicit NULL guard (`nullSafeStmt stmt schema = True`).
||| Before Phase 2 `AllNullableFieldsGuarded` was inhabited by the
||| content-free `GuardedNull` and only saw WHERE. Mirrors
||| `checkLevel4Sound`. Tracked: hyperpolymath/standards#124.
export
checkLevel3Sound : (stmt : Statement) -> (schema : OctadSchema) ->
                   (m : String) ->
                   checkLevel3 stmt schema = (True, m) ->
                   L3_NullSafe stmt schema
checkLevel3Sound stmt schema m prf
    with (nullSafeStmt stmt schema) proof p
  checkLevel3Sound stmt schema m prf | True  =
    MkL3 stmt schema (MkNullGuarded p)
  checkLevel3Sound stmt schema m prf | False =
    void (notFalseTrue (cong fst prf))

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
||| Defined through the shared decider `Decide.selectItemsTyped` (the
||| same function the Level-5 proof predicate `AllSelectItemsTyped`
||| carries), so `checkLevel5Sound` is a genuine soundness statement —
||| the L4 architecture, applied to L5 (standards#124, Phase 2).
public export
checkLevel5 : Statement -> OctadSchema -> (Bool, String)
checkLevel5 stmt schema = l5Verdict (selectItemsTyped (selectItems stmt) schema)
  where
    l5Verdict : Bool -> (Bool, String)
    l5Verdict True  =
      (True,  "L5:ResultTyped — all select items have known types")
    l5Verdict False =
      (False, "L5:ResultTyped FAILED — a select item has an unresolved type")

||| **Soundness of the Level-5 decision procedure.**
||| If `checkLevel5` accepts, the statement genuinely carries an
||| `L5_ResultTyped`: every SELECT item resolves to a known (non-`TAny`)
||| type (`selectItemsTyped (selectItems stmt) schema = True`). Before
||| Phase 2 `AllSelectItemsTyped` was inhabited by the content-free
||| `ConsTyped`, so this statement was not even meaningful. Mirrors
||| `checkLevel4Sound`. Tracked: hyperpolymath/standards#124.
export
checkLevel5Sound : (stmt : Statement) -> (schema : OctadSchema) ->
                   (m : String) ->
                   checkLevel5 stmt schema = (True, m) ->
                   L5_ResultTyped stmt schema
checkLevel5Sound stmt schema m prf
    with (selectItemsTyped (selectItems stmt) schema) proof p
  checkLevel5Sound stmt schema m prf | True  =
    MkL5 stmt schema (MkAllSelTyped p)
  checkLevel5Sound stmt schema m prf | False =
    void (falseNotTrue (cong fst prf))

||| Level 6 — CardinalitySafe: the statement includes a LIMIT clause.
||| Queries that could return unbounded results must have an explicit
||| LIMIT to prevent resource exhaustion.
|||
||| @stmt The statement to check.
||| @return (True, _) if LIMIT is present; (False, diagnostic) otherwise.
||| Defined THROUGH `Decide.cardinalityBoundedStmt` (Phase 4b), so the
||| L6 predicate and this decision share one definition.
public export
checkLevel6 : Statement -> (Bool, String)
checkLevel6 stmt = l6Verdict (cardinalityBoundedStmt stmt)
  where
    l6Verdict : Bool -> (Bool, String)
    l6Verdict True  =
      (True,  "L6:CardinalitySafe — result cardinality is LIMIT-bounded")
    l6Verdict False =
      (False, "L6:CardinalitySafe FAILED — no LIMIT clause on query")

||| Level 7 — EffectTracked: the statement includes an EFFECTS declaration.
||| Side-effectful operations (INSERT/UPDATE/DELETE) must declare their
||| effects so callers can track and compose them safely.
|||
||| @stmt The statement to check.
||| @return (True, _) if effectDecl is present; (False, diagnostic) otherwise.
||| Defined THROUGH `Decide.effectTrackedStmt` (Phase 4b).
public export
checkLevel7 : Statement -> (Bool, String)
checkLevel7 stmt = l7Verdict (effectTrackedStmt stmt)
  where
    l7Verdict : Bool -> (Bool, String)
    l7Verdict True  =
      (True,  "L7:EffectTracked — effect declaration present")
    l7Verdict False =
      (False, "L7:EffectTracked FAILED — no EFFECTS declaration")

||| Level 8 — TemporalSafe: the statement includes a version constraint.
||| Queries against VeriSimDB's time-travel engine must specify temporal
||| bounds (AT LATEST, AT VERSION >=, etc.) to avoid indeterminate results.
|||
||| @stmt The statement to check.
||| @return (True, _) if versionConst is present; (False, diagnostic) otherwise.
||| Defined THROUGH `Decide.temporalBoundedStmt` (Phase 4b).
public export
checkLevel8 : Statement -> (Bool, String)
checkLevel8 stmt = l8Verdict (temporalBoundedStmt stmt)
  where
    l8Verdict : Bool -> (Bool, String)
    l8Verdict True  =
      (True,  "L8:TemporalSafe — version constraint present")
    l8Verdict False =
      (False, "L8:TemporalSafe FAILED — no version constraint")

||| Level 9 — LinearSafe: the statement includes a linearity annotation
||| with an actual consumption constraint (LinUseOnce or LinBounded).
||| LinUnlimited is not sufficient — it must enforce resource linearity.
|||
||| @stmt The statement to check.
||| @return (True, _) if a consume constraint is present; (False, diagnostic) otherwise.
||| Defined THROUGH `Decide.linearEnforcedStmt` (Phase 4b): rejects both
||| absence AND the no-op `LinUnlimited`, matching the predicate exactly.
public export
checkLevel9 : Statement -> (Bool, String)
checkLevel9 stmt = l9Verdict (linearEnforcedStmt stmt)
  where
    l9Verdict : Bool -> (Bool, String)
    l9Verdict True  =
      (True,  "L9:LinearSafe — enforced consumption bound (LinUseOnce/LinBounded)")
    l9Verdict False =
      (False, "L9:LinearSafe FAILED — no enforced linearity (absent or LinUnlimited)")

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
||| Defined THROUGH `Decide.epistemicConsistentStmt` (Phase 4b). The
||| agent-declaration / direct-ENTAILS-cycle helper logic was hoisted
||| verbatim into `Decide` so the L10 predicate and this decision share
||| ONE definition (single source of truth, no drift). The richer
||| diagnostic (which agent, etc.) is derived separately for the message
||| but the verdict bit is exactly the decider.
public export
checkLevel10 : Statement -> (Bool, String)
checkLevel10 stmt = l10Verdict (epistemicConsistentStmt stmt)
  where
    l10Verdict : Bool -> (Bool, String)
    l10Verdict True  =
      (True,  "L10:EpistemicSafe — clause present, agents declared, no direct ENTAILS cycle")
    l10Verdict False =
      (False, "L10:EpistemicSafe FAILED — missing clause / no agents / undeclared agent / direct ENTAILS cycle")

-- ═══════════════════════════════════════════════════════════════════════
-- Soundness of the L6–L10 decision procedures (Phase 4b, standards#124)
-- ═══════════════════════════════════════════════════════════════════════
--
-- Each `checkLevelNSound` proves: if `checkLevelN` accepts, the statement
-- genuinely carries the corresponding `LN_*` witness. Same `with … proof
-- p` shape as `checkLevel2Sound`; no proof-escape.
--
-- PHASE 4b: the L6–L10 predicates now carry the SHARED `Decide` decider
-- (`cardinalityBoundedStmt`/`effectTrackedStmt`/`temporalBoundedStmt`/
-- `linearEnforcedStmt`/`epistemicConsistentStmt`), and `checkLevelN` is
-- defined THROUGH that same decider, so each soundness lemma is a direct
-- equality extraction — not a check against a parallel re-implementation
-- that could drift. The Phase-3 disclosed predicate↔checker shallowness
-- gap (L9 `LinUnlimited`; L10 declared-agents / direct ENTAILS cycle) is
-- hereby CLOSED at the level of these predicates. Remaining disclosed L10
-- residual (full transitive cycle detection, proposition well-typedness)
-- is in VERIFICATION-STANCE.adoc — scoped, not masked.

||| L6 soundness: acceptance ⇒ the cardinality decider holds.
export
checkLevel6Sound : (stmt : Statement) -> (m : String) ->
                   checkLevel6 stmt = (True, m) -> L6_CardinalitySafe stmt
checkLevel6Sound stmt m prf with (cardinalityBoundedStmt stmt) proof p
  checkLevel6Sound stmt m prf | True  = MkL6 p
  checkLevel6Sound stmt m prf | False = void (falseNotTrue (cong fst prf))

||| L7 soundness: acceptance ⇒ the effect-tracked decider holds.
export
checkLevel7Sound : (stmt : Statement) -> (m : String) ->
                   checkLevel7 stmt = (True, m) -> L7_EffectTracked stmt
checkLevel7Sound stmt m prf with (effectTrackedStmt stmt) proof p
  checkLevel7Sound stmt m prf | True  = MkL7 p
  checkLevel7Sound stmt m prf | False = void (falseNotTrue (cong fst prf))

||| L8 soundness: acceptance ⇒ the temporal-bound decider holds.
export
checkLevel8Sound : (stmt : Statement) -> (m : String) ->
                   checkLevel8 stmt = (True, m) -> L8_TemporalSafe stmt
checkLevel8Sound stmt m prf with (temporalBoundedStmt stmt) proof p
  checkLevel8Sound stmt m prf | True  = MkL8 p
  checkLevel8Sound stmt m prf | False = void (falseNotTrue (cong fst prf))

||| L9 soundness: acceptance ⇒ linearity is genuinely ENFORCED
||| (`LinUseOnce`/`LinBounded`; absence and `LinUnlimited` are rejected
||| by the shared decider — the Phase-3 L9 gap is closed).
export
checkLevel9Sound : (stmt : Statement) -> (m : String) ->
                   checkLevel9 stmt = (True, m) -> L9_LinearSafe stmt
checkLevel9Sound stmt m prf with (linearEnforcedStmt stmt) proof p
  checkLevel9Sound stmt m prf | True  = MkL9 p
  checkLevel9Sound stmt m prf | False = void (falseNotTrue (cong fst prf))

||| L10 soundness: acceptance ⇒ the epistemic-consistency decider holds
||| (clause present, ≥1 agent, all requirement agents declared, no direct
||| ENTAILS cycle — the Phase-3 L10 gap is closed at this predicate).
export
checkLevel10Sound : (stmt : Statement) -> (m : String) ->
                    checkLevel10 stmt = (True, m) -> L10_EpistemicSafe stmt
checkLevel10Sound stmt m prf with (epistemicConsistentStmt stmt) proof p
  checkLevel10Sound stmt m prf | True  = MkL10 p
  checkLevel10Sound stmt m prf | False = void (falseNotTrue (cong fst prf))

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

-- ═══════════════════════════════════════════════════════════════════════
-- Proof-carrying entry point (Phase 3b, standards#124)
-- ═══════════════════════════════════════════════════════════════════════
--
-- `checkQuery` above stays the plain Bool/`CheckResult` path for the C
-- ABI. This section adds the *proof-carrying* path: each `tryLN` runs
-- the corresponding decision procedure and, on acceptance, returns the
-- genuine `LN_*` witness via the (machine-checked) `checkLevelNSound`
-- lemma — no proof-escape, no re-assertion. `certifyAt` assembles them
-- into the cumulative dependent `SafetyCertificate`. This is the
-- certificate↔checker connection that was previously entirely absent
-- (Phase-1/2 had it for the predicates in isolation; here `checkQuery`'s
-- *decision* is what produces the dependent certificate).

tryL1 : (stmt : Statement) -> (schema : OctadSchema) ->
        Maybe (L1_SchemaBound stmt schema)
tryL1 stmt schema with (checkLevel1 stmt schema) proof p
  tryL1 stmt schema | (True,  m) = Just (checkLevel1Sound stmt schema m p)
  tryL1 stmt schema | (False, _) = Nothing

tryL2 : (stmt : Statement) -> (schema : OctadSchema) ->
        Maybe (L2_TypeCompat stmt schema)
tryL2 stmt schema with (checkLevel2 stmt schema) proof p
  tryL2 stmt schema | (True,  m) = Just (checkLevel2Sound stmt schema m p)
  tryL2 stmt schema | (False, _) = Nothing

tryL3 : (stmt : Statement) -> (schema : OctadSchema) ->
        Maybe (L3_NullSafe stmt schema)
tryL3 stmt schema with (checkLevel3 stmt schema) proof p
  tryL3 stmt schema | (True,  m) = Just (checkLevel3Sound stmt schema m p)
  tryL3 stmt schema | (False, _) = Nothing

tryL4 : (stmt : Statement) -> Maybe (L4_InjectionProof stmt)
tryL4 stmt with (checkLevel4 stmt) proof p
  tryL4 stmt | (True,  m) = Just (checkLevel4Sound stmt m p)
  tryL4 stmt | (False, _) = Nothing

tryL5 : (stmt : Statement) -> (schema : OctadSchema) ->
        Maybe (L5_ResultTyped stmt schema)
tryL5 stmt schema with (checkLevel5 stmt schema) proof p
  tryL5 stmt schema | (True,  m) = Just (checkLevel5Sound stmt schema m p)
  tryL5 stmt schema | (False, _) = Nothing

tryL6 : (stmt : Statement) -> Maybe (L6_CardinalitySafe stmt)
tryL6 stmt with (checkLevel6 stmt) proof p
  tryL6 stmt | (True,  m) = Just (checkLevel6Sound stmt m p)
  tryL6 stmt | (False, _) = Nothing

tryL7 : (stmt : Statement) -> Maybe (L7_EffectTracked stmt)
tryL7 stmt with (checkLevel7 stmt) proof p
  tryL7 stmt | (True,  m) = Just (checkLevel7Sound stmt m p)
  tryL7 stmt | (False, _) = Nothing

tryL8 : (stmt : Statement) -> Maybe (L8_TemporalSafe stmt)
tryL8 stmt with (checkLevel8 stmt) proof p
  tryL8 stmt | (True,  m) = Just (checkLevel8Sound stmt m p)
  tryL8 stmt | (False, _) = Nothing

tryL9 : (stmt : Statement) -> Maybe (L9_LinearSafe stmt)
tryL9 stmt with (checkLevel9 stmt) proof p
  tryL9 stmt | (True,  m) = Just (checkLevel9Sound stmt m p)
  tryL9 stmt | (False, _) = Nothing

tryL10 : (stmt : Statement) -> Maybe (L10_EpistemicSafe stmt)
tryL10 stmt with (checkLevel10 stmt) proof p
  tryL10 stmt | (True,  m) = Just (checkLevel10Sound stmt m p)
  tryL10 stmt | (False, _) = Nothing

||| Attempt to produce a genuine dependent `SafetyCertificate` at the
||| requested level. `Just c` means every level 0..k was *decided*
||| accepting and `c` carries the real cumulative evidence; `Nothing`
||| means some required level was rejected. (L0 is unconditional —
||| a parsed `Statement` is its own parse-safety witness.)
public export
certifyAt : (stmt : Statement) -> (schema : OctadSchema) ->
            (k : SafetyLevel) ->
            Maybe (SafetyCertificate stmt schema k)
certifyAt stmt schema ParseSafe =
  Just (CertL0 (MkL0 stmt))
certifyAt stmt schema SchemaBound =
  [| CertL1 (pure (MkL0 stmt)) (tryL1 stmt schema) |]
certifyAt stmt schema TypeCompat =
  [| CertL2 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema) |]
certifyAt stmt schema NullSafe =
  [| CertL3 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) |]
certifyAt stmt schema InjectionProof =
  [| CertL4 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) (tryL4 stmt) |]
certifyAt stmt schema ResultTyped =
  [| CertL5 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) (tryL4 stmt) (tryL5 stmt schema) |]
certifyAt stmt schema CardinalitySafe =
  [| CertL6 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) (tryL4 stmt) (tryL5 stmt schema)
            (tryL6 stmt) |]
certifyAt stmt schema EffectTracked =
  [| CertL7 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) (tryL4 stmt) (tryL5 stmt schema)
            (tryL6 stmt) (tryL7 stmt) |]
certifyAt stmt schema TemporalSafe =
  [| CertL8 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) (tryL4 stmt) (tryL5 stmt schema)
            (tryL6 stmt) (tryL7 stmt) (tryL8 stmt) |]
certifyAt stmt schema LinearSafe =
  [| CertL9 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
            (tryL3 stmt schema) (tryL4 stmt) (tryL5 stmt schema)
            (tryL6 stmt) (tryL7 stmt) (tryL8 stmt) (tryL9 stmt) |]
certifyAt stmt schema EpistemicSafe =
  [| CertL10 (pure (MkL0 stmt)) (tryL1 stmt schema) (tryL2 stmt schema)
             (tryL3 stmt schema) (tryL4 stmt) (tryL5 stmt schema)
             (tryL6 stmt) (tryL7 stmt) (tryL8 stmt) (tryL9 stmt)
             (tryL10 stmt) |]

||| Certify a query at its own declared `requestedLevel`. The result
||| type *is* the dependent certificate for that level — a `Just` is a
||| machine-checked proof the query meets its declared safety level.
public export
certifyRequested : (stmt : Statement) -> (schema : OctadSchema) ->
                   Maybe (SafetyCertificate stmt schema (requestedLevel stmt))
certifyRequested stmt schema = certifyAt stmt schema (requestedLevel stmt)

-- ═══════════════════════════════════════════════════════════════════════
-- Proof-gated attestation mint (Phase 3d, standards#124)
-- ═══════════════════════════════════════════════════════════════════════
--
-- A C ABI cannot carry a dependent `SafetyCertificate` — that is
-- inherent to *any* FFI boundary, not a defect. The honest model is a
-- *trusted-certifier attestation*: this function returns the certified
-- safety level as an `Int` IFF `certifyRequested` produced a genuine
-- dependent certificate (the `Just` branch is *structurally* the only
-- place a non-negative level can be returned — no proof-escape, the
-- certificate's mere existence is the gate); otherwise `-1`.
--
-- An FFI/host that calls this trusts the *certifier binary*, exactly as
-- proof-carrying-code consumers trust the checker that minted the
-- attestation. What this is NOT: it is not a re-checkable proof token,
-- and it does NOT parse — it certifies an already-built `Statement`.
-- The string→`Statement` parser, the C-ABI `Statement`/`OctadSchema`
-- marshalling, and the Idris→C build are NAMED OWED items in
-- VERIFICATION-STANCE.adoc (absent, not faked). `certifyRequested`
-- itself remains the single source of verification truth.
public export
certifiedLevel : Statement -> OctadSchema -> Int
certifiedLevel stmt schema =
  case certifyRequested stmt schema of
    Just _  => cast (safetyLevelToInt (requestedLevel stmt))
    Nothing => -1
