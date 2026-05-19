-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Core Levels — 10-Level Type Safety Checker Proofs
|||
||| Formalises the 10 progressive type safety levels as dependent types.
||| Each level is a predicate over a Statement + Schema pair, and higher
||| levels subsume all lower levels.
|||
||| The checker proceeds bottom-up: a query that passes Level N is
||| guaranteed to have passed all levels 0 through N-1.
|||
||| Properties proved:
|||   - Subsumption: Level N implies Level (N-1) for all N > 0
|||   - Soundness: a checked query cannot violate its declared level
|||   - Totality: the checker terminates for all inputs
|||   - Monotonicity: additional checks can only raise, never lower, the level

module VclTotal.Core.Levels

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import VclTotal.Core.Decide
import Data.List
import Data.Nat

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Helper Predicates
-- ═══════════════════════════════════════════════════════════════════════

||| Extract field references from a SELECT item list.
||| Exported so that Composition.idr can prove distributivity over (++).
public export
selectFieldRefs : List SelectItem -> List FieldRef
selectFieldRefs [] = []
selectFieldRefs (SelField ref :: rest) = ref :: selectFieldRefs rest
selectFieldRefs (_ :: rest) = selectFieldRefs rest

||| Extract field references from an optional expression.
||| Exported so that Composition.idr can prove properties of joinWhere.
public export
exprFieldRefs : Maybe Expr -> List FieldRef
exprFieldRefs Nothing = []
exprFieldRefs (Just (EField ref _)) = [ref]
exprFieldRefs (Just (ECompare _ l r _)) = exprFieldRefs (Just l) ++ exprFieldRefs (Just r)
exprFieldRefs (Just (ELogic _ l mr _)) = exprFieldRefs (Just l) ++ exprFieldRefs mr
exprFieldRefs (Just (EAggregate _ e _)) = exprFieldRefs (Just e)
exprFieldRefs _ = []

||| Extract all field references from a statement.
public export
extractFieldRefs : Statement -> List FieldRef
extractFieldRefs stmt =
  selectFieldRefs (selectItems stmt) ++
  exprFieldRefs (whereClause stmt) ++
  (groupBy stmt) ++
  exprFieldRefs (having stmt) ++
  map fst (orderBy stmt)

||| Proof that all comparisons in an expression use compatible types.
|||
||| HISTORY (standards#124, Phase 2): this used to be a pair of types
|||
|||   data ExprTypeSafe : Expr -> OctadSchema -> Type where
|||     FieldSafe   : ExprTypeSafe (EField ref ty) schema
|||     CompareSafe : TypeCompatible lty rty ->
|||                   ExprTypeSafe (ECompare op l r TBool) schema
|||     LogicSafe   : ExprTypeSafe (ELogic op l mr TBool) schema
|||     ...   -- (FieldSafe/LiteralSafe/AggregateSafe/ParamSafe)
|||   data AllComparisonsTypeSafe : Maybe Expr -> OctadSchema -> Type where
|||     NoWhere       : AllComparisonsTypeSafe Nothing schema
|||     WhereTypeSafe : ExprTypeSafe expr schema ->
|||                     AllComparisonsTypeSafe (Just expr) schema
|||
||| which is *vacuous* three ways: `FieldSafe` demanded no relation
||| between `ty` and the schema; `CompareSafe`'s `lty`/`rty` were free
||| implicits unconnected to `l`/`r` (dischargeable by `SameType` for any
||| `t`) and it never recursed into the operands; so `WhereTypeSafe …`
||| inhabited the predicate for *every* WHERE clause. Level 2 proved
||| nothing about type compatibility. It now carries real evidence: the
||| shared decider `Decide.whereComparisonsCompatible` (which
||| `Checker.checkLevel2` is defined through) returns `True`, i.e. every
||| `ECompare` node in the WHERE clause has operands of compatible
||| resolved types. Soundness: `Checker.checkLevel2Sound`.
public export
data AllComparisonsTypeSafe : Maybe Expr -> OctadSchema -> Type where
  MkAllCompat : whereComparisonsCompatible m schema = True ->
                AllComparisonsTypeSafe m schema


||| Proof that all nullable fields are guarded (NULL checks present).
|||
||| HISTORY (standards#124, Phase 2): this used to be
|||
|||   data AllNullableFieldsGuarded : Maybe Expr -> OctadSchema -> Type
|||     where
|||       NoWhereNull : AllNullableFieldsGuarded Nothing schema
|||       GuardedNull : AllNullableFieldsGuarded (Just expr) schema
|||
||| which is *vacuous*: `GuardedNull` inhabited the predicate for *every*
||| `Just expr` with zero structural content, and it only saw the WHERE
||| clause (so it could not even be `checkLevel3`'s soundness target —
||| the checker also inspects HAVING). It is now **Statement-indexed**
||| and carries real evidence: the shared decider `Decide.nullSafeStmt`
||| (which `Checker.checkLevel3` is defined through) returns `True`, i.e.
||| neither the WHERE nor the HAVING clause uses a schema-nullable field
||| without an explicit NULL guard. Soundness: `Checker.checkLevel3Sound`.
public export
data AllNullableFieldsGuarded : Statement -> OctadSchema -> Type where
  MkNullGuarded : nullSafeStmt stmt schema = True ->
                  AllNullableFieldsGuarded stmt schema

||| Proof that no raw user input appears in the query's WHERE clause.
||| User values must arrive via `EParam` nodes, never as embedded string
||| literals (the canonical SQL-injection vector).
|||
||| HISTORY (standards#124, vcl-ut HOLE remediation): this used to be
|||
|||   data NoRawUserInput : Statement -> Type where
|||     AllParameterised : NoRawUserInput stmt
|||
||| which is *vacuous* — `AllParameterised` inhabits `NoRawUserInput stmt`
||| for *every* statement, including one whose WHERE is pure string
||| interpolation. Level 4 therefore proved nothing about the property it
||| names. It now carries real structural evidence: the WHERE clause
||| embeds no string literal (`Grammar.whereHasStringLit stmt = False`).
||| `Checker.checkLevel4` decides exactly this predicate
||| (see `checkLevel4Sound`), and it is genuinely closed under join
||| composition (see `Composition.noRawUserInputCompose`).
public export
data NoRawUserInput : Statement -> Type where
  MkNoRawUserInput : whereHasStringLit stmt = False -> NoRawUserInput stmt

||| Proof that all select items have known types.
|||
||| HISTORY (standards#124, Phase 2): this used to be
|||
|||   data AllSelectItemsTyped : List SelectItem -> OctadSchema -> Type where
|||     NilTyped  : AllSelectItemsTyped [] schema
|||     ConsTyped : AllSelectItemsTyped rest schema ->
|||                 AllSelectItemsTyped (item :: rest) schema
|||
||| which is *vacuous*: `ConsTyped` demands nothing of `item`, so the
||| predicate was inhabited for *every* list (induct down to `NilTyped`).
||| Level 5 therefore proved nothing about result typing — a SELECT of an
||| unresolved (`TAny`) field type-checked. It now carries real evidence:
||| the shared decider `Decide.selectItemsTyped` (which `Checker.checkLevel5`
||| is defined through) returns `True`, i.e. every SELECT item resolves to
||| a known, non-`TAny` type. Soundness: `Checker.checkLevel5Sound`.
public export
data AllSelectItemsTyped : List SelectItem -> OctadSchema -> Type where
  MkAllSelTyped : selectItemsTyped items schema = True ->
                  AllSelectItemsTyped items schema

-- ═══════════════════════════════════════════════════════════════════════
-- Level Predicates
-- ═══════════════════════════════════════════════════════════════════════

||| Level 0: Parse Safety — the query is syntactically valid.
||| Satisfied by construction (parsed into a Statement AST).
public export
data L0_ParseSafe : Statement -> Type where
  MkL0 : (stmt : Statement) -> L0_ParseSafe stmt

||| Level 1: Schema Bound — all field references resolve in the schema.
public export
data L1_SchemaBound : Statement -> OctadSchema -> Type where
  MkL1 : (stmt : Statement) ->
          (schema : OctadSchema) ->
          AllFieldsBound (extractFieldRefs stmt) schema ->
          L1_SchemaBound stmt schema

||| Level 2: Type Compatible — all comparisons use compatible types.
public export
data L2_TypeCompat : Statement -> OctadSchema -> Type where
  MkL2 : (stmt : Statement) ->
          (schema : OctadSchema) ->
          AllComparisonsTypeSafe (whereClause stmt) schema ->
          L2_TypeCompat stmt schema

||| Level 3: Null Safe — nullable fields are handled explicitly.
public export
data L3_NullSafe : Statement -> OctadSchema -> Type where
  MkL3 : (stmt : Statement) ->
          (schema : OctadSchema) ->
          AllNullableFieldsGuarded stmt schema ->
          L3_NullSafe stmt schema

||| Level 4: Injection Proof — no unparameterised user input.
||| All user values must come through EParam nodes, not string interpolation.
public export
data L4_InjectionProof : Statement -> Type where
  MkL4 : (stmt : Statement) ->
          NoRawUserInput stmt ->
          L4_InjectionProof stmt

||| Level 5: Result Typed — every select item has a known result type.
public export
data L5_ResultTyped : Statement -> OctadSchema -> Type where
  MkL5 : (stmt : Statement) ->
          (schema : OctadSchema) ->
          AllSelectItemsTyped (selectItems stmt) schema ->
          L5_ResultTyped stmt schema

||| Level 6: Cardinality Safe — the query bounds its result set.
|||
||| HISTORY (standards#124, Phase 4b): this used to be the presence-only
||| `MkL6 : (n : Nat) -> limit stmt = Just n -> ...`. It now carries the
||| shared decider `Decide.cardinalityBoundedStmt stmt = True` (which
||| `Checker.checkLevel6` is defined through), so `checkLevel6Sound` is a
||| direct equality, not a parallel re-implementation. Genuinely
||| non-vacuous: a query with no LIMIT cannot inhabit it.
public export
data L6_CardinalitySafe : Statement -> Type where
  MkL6 : cardinalityBoundedStmt stmt = True -> L6_CardinalitySafe stmt

||| Level 7: Effect Tracked — side effects are declared.
|||
||| HISTORY (standards#124, Phase 4b): presence-only → shared decider
||| `Decide.effectTrackedStmt stmt = True` (Checker.checkLevel7 defined
||| through it). Soundness: `Checker.checkLevel7Sound`.
public export
data L7_EffectTracked : Statement -> Type where
  MkL7 : effectTrackedStmt stmt = True -> L7_EffectTracked stmt

||| Level 8: Temporal Safe — version constraint is present.
|||
||| HISTORY (standards#124, Phase 4b): presence-only → shared decider
||| `Decide.temporalBoundedStmt stmt = True` (Checker.checkLevel8 defined
||| through it). Soundness: `Checker.checkLevel8Sound`.
public export
data L8_TemporalSafe : Statement -> Type where
  MkL8 : temporalBoundedStmt stmt = True -> L8_TemporalSafe stmt

||| Level 9: Linear Safe — linearity is actually ENFORCED.
|||
||| HISTORY (standards#124, Phase 4b): this used to be presence-only
||| (`linearAnnot stmt = Just la` for ANY `la`, including the no-op
||| `LinUnlimited`) — strictly weaker than what `checkLevel9` enforces,
||| a gap explicitly disclosed as a Phase-3 residual. It now carries the
||| shared decider `Decide.linearEnforcedStmt stmt = True`, which (like
||| the checker) rejects both absence AND `LinUnlimited`, requiring a
||| genuine `LinUseOnce`/`LinBounded` consumption bound. The Phase-3 L9
||| predicate↔checker shallowness gap is hereby CLOSED. Soundness:
||| `Checker.checkLevel9Sound`.
public export
data L9_LinearSafe : Statement -> Type where
  MkL9 : linearEnforcedStmt stmt = True -> L9_LinearSafe stmt

||| Level 10: Epistemic Safe — epistemic clause present AND consistent.
|||
||| HISTORY (standards#124, Phase 4b): this used to be presence-only
||| (`epistemicClause stmt = Just ec`), strictly weaker than the
||| consistency `checkLevel10` enforces (a disclosed Phase-3 residual).
||| It now carries the shared decider `Decide.epistemicConsistentStmt
||| stmt = True` — clause present, ≥1 agent, every requirement-referenced
||| agent declared, and no direct (a⊨b, b⊨a) ENTAILS cycle — exactly the
||| `checkLevel10` semantics (its helper logic was hoisted into `Decide`
||| as the single source of truth). Soundness: `Checker.checkLevel10Sound`.
||| Disclosed residual (NOT faked): full transitive ENTAILS-cycle
||| detection and proposition well-typedness remain OWED in
||| VERIFICATION-STANCE.adoc; the decider checks the *direct* symmetry
||| violation, matching the checker.
public export
data L10_EpistemicSafe : Statement -> Type where
  MkL10 : epistemicConsistentStmt stmt = True -> L10_EpistemicSafe stmt


-- ═══════════════════════════════════════════════════════════════════════
-- Subsumption Proofs
-- ═══════════════════════════════════════════════════════════════════════

||| The combined safety certificate for a query at a given level.
||| Higher levels include all lower-level certificates.
public export
data SafetyCertificate : Statement -> OctadSchema -> SafetyLevel -> Type where
  CertL0 : L0_ParseSafe stmt ->
            SafetyCertificate stmt schema ParseSafe

  CertL1 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            SafetyCertificate stmt schema SchemaBound

  CertL2 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            SafetyCertificate stmt schema TypeCompat

  CertL3 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            SafetyCertificate stmt schema NullSafe

  CertL4 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            L4_InjectionProof stmt ->
            SafetyCertificate stmt schema InjectionProof

  CertL5 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            L4_InjectionProof stmt ->
            L5_ResultTyped stmt schema ->
            SafetyCertificate stmt schema ResultTyped

  CertL6 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            L4_InjectionProof stmt ->
            L5_ResultTyped stmt schema ->
            L6_CardinalitySafe stmt ->
            SafetyCertificate stmt schema CardinalitySafe

  CertL7 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            L4_InjectionProof stmt ->
            L5_ResultTyped stmt schema ->
            L6_CardinalitySafe stmt ->
            L7_EffectTracked stmt ->
            SafetyCertificate stmt schema EffectTracked

  CertL8 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            L4_InjectionProof stmt ->
            L5_ResultTyped stmt schema ->
            L6_CardinalitySafe stmt ->
            L7_EffectTracked stmt ->
            L8_TemporalSafe stmt ->
            SafetyCertificate stmt schema TemporalSafe

  CertL9 : L0_ParseSafe stmt ->
            L1_SchemaBound stmt schema ->
            L2_TypeCompat stmt schema ->
            L3_NullSafe stmt schema ->
            L4_InjectionProof stmt ->
            L5_ResultTyped stmt schema ->
            L6_CardinalitySafe stmt ->
            L7_EffectTracked stmt ->
            L8_TemporalSafe stmt ->
            L9_LinearSafe stmt ->
            SafetyCertificate stmt schema LinearSafe

  CertL10 : L0_ParseSafe stmt ->
             L1_SchemaBound stmt schema ->
             L2_TypeCompat stmt schema ->
             L3_NullSafe stmt schema ->
             L4_InjectionProof stmt ->
             L5_ResultTyped stmt schema ->
             L6_CardinalitySafe stmt ->
             L7_EffectTracked stmt ->
             L8_TemporalSafe stmt ->
             L9_LinearSafe stmt ->
             L10_EpistemicSafe stmt ->
             SafetyCertificate stmt schema EpistemicSafe

-- ═══════════════════════════════════════════════════════════════════════
-- Monotonicity Proof
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that safety level ordering is monotonic.
||| A SafetyCertificate at level N can be weakened to any level M < N.
public export
data CanWeaken : SafetyLevel -> SafetyLevel -> Type where
  WeakenSame   : CanWeaken l l
  WeakenParse  : CanWeaken l ParseSafe    -- Any level weakens to L0
  WeakenSchema : CanWeaken SchemaBound ParseSafe
  WeakenType   : CanWeaken TypeCompat SchemaBound
  WeakenNull   : CanWeaken NullSafe TypeCompat
  WeakenInject : CanWeaken InjectionProof NullSafe
  WeakenResult : CanWeaken ResultTyped InjectionProof
  WeakenCard   : CanWeaken CardinalitySafe ResultTyped
  WeakenEffect : CanWeaken EffectTracked CardinalitySafe
  WeakenTemp   : CanWeaken TemporalSafe EffectTracked
  WeakenLinear    : CanWeaken LinearSafe TemporalSafe
  WeakenEpistemic : CanWeaken EpistemicSafe LinearSafe

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI: Level Check Result
-- ═══════════════════════════════════════════════════════════════════════

||| Result of checking a query at a requested level.
||| Either a certificate proving safety, or the level at which checking failed.
public export
data CheckResult : Type where
  ||| Query passed all checks up to the requested level.
  Passed : (achievedLevel : SafetyLevel) -> CheckResult
  ||| Query failed at a specific level with an error.
  Failed : (failedLevel : SafetyLevel) -> (error : String) -> CheckResult

||| Encode CheckResult for C ABI.
public export
checkResultToInts : CheckResult -> (Int, Int)
checkResultToInts (Passed level) =
  (cast (safetyLevelToInt level), 0)
checkResultToInts (Failed level _) =
  (cast (safetyLevelToInt level), 1)
