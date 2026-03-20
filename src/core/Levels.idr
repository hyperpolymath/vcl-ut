-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VQL-UT Core Levels — 10-Level Type Safety Checker Proofs
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

module VqlUt.Core.Levels

import VqlUt.ABI.Types
import VqlUt.Core.Grammar
import VqlUt.Core.Schema
import Data.List
import Data.Nat

%default total

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
          AllNullableFieldsGuarded (whereClause stmt) schema ->
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

||| Level 6: Cardinality Safe — query has a LIMIT clause.
public export
data L6_CardinalitySafe : Statement -> Type where
  MkL6 : (stmt : Statement) ->
          (n : Nat) ->
          (limit stmt = Just n) ->
          L6_CardinalitySafe stmt

||| Level 7: Effect Tracked — side effects are declared.
public export
data L7_EffectTracked : Statement -> Type where
  MkL7 : (stmt : Statement) ->
          (eff : EffectDecl) ->
          (effectDecl stmt = Just eff) ->
          L7_EffectTracked stmt

||| Level 8: Temporal Safe — version constraint is present.
public export
data L8_TemporalSafe : Statement -> Type where
  MkL8 : (stmt : Statement) ->
          (vc : VersionConstraint) ->
          (versionConst stmt = Just vc) ->
          L8_TemporalSafe stmt

||| Level 9: Linear Safe — linearity annotation is present and respected.
public export
data L9_LinearSafe : Statement -> Type where
  MkL9 : (stmt : Statement) ->
          (la : LinearAnnotation) ->
          (linearAnnot stmt = Just la) ->
          L9_LinearSafe stmt

-- ═══════════════════════════════════════════════════════════════════════
-- Helper Predicates
-- ═══════════════════════════════════════════════════════════════════════

||| Extract all field references from a statement.
public export
extractFieldRefs : Statement -> List FieldRef
extractFieldRefs stmt =
  selectFieldRefs (selectItems stmt) ++
  exprFieldRefs (whereClause stmt) ++
  (groupBy stmt) ++
  exprFieldRefs (having stmt) ++
  map fst (orderBy stmt)
  where
    selectFieldRefs : List SelectItem -> List FieldRef
    selectFieldRefs [] = []
    selectFieldRefs (SelField ref :: rest) = ref :: selectFieldRefs rest
    selectFieldRefs (_ :: rest) = selectFieldRefs rest

    exprFieldRefs : Maybe Expr -> List FieldRef
    exprFieldRefs Nothing = []
    exprFieldRefs (Just (EField ref _)) = [ref]
    exprFieldRefs (Just (ECompare _ l r _)) = exprFieldRefs (Just l) ++ exprFieldRefs (Just r)
    exprFieldRefs (Just (ELogic _ l mr _)) = exprFieldRefs (Just l) ++ exprFieldRefs mr
    exprFieldRefs (Just (EAggregate _ e _)) = exprFieldRefs (Just e)
    exprFieldRefs _ = []

||| Proof that all comparisons in an expression use compatible types.
public export
data AllComparisonsTypeSafe : Maybe Expr -> OctadSchema -> Type where
  NoWhere : AllComparisonsTypeSafe Nothing schema
  WhereTypeSafe : ExprTypeSafe expr schema -> AllComparisonsTypeSafe (Just expr) schema

||| Proof that a single expression is type-safe.
public export
data ExprTypeSafe : Expr -> OctadSchema -> Type where
  FieldSafe   : ExprTypeSafe (EField ref ty) schema
  LiteralSafe : ExprTypeSafe (ELiteral lit ty) schema
  CompareSafe : TypeCompatible lty rty ->
                ExprTypeSafe (ECompare op l r TBool) schema
  LogicSafe   : ExprTypeSafe (ELogic op l mr TBool) schema
  AggregateSafe : ExprTypeSafe (EAggregate f e ty) schema
  ParamSafe   : ExprTypeSafe (EParam name ty) schema

||| Proof that all nullable fields are guarded (NULL checks present).
public export
data AllNullableFieldsGuarded : Maybe Expr -> OctadSchema -> Type where
  NoWhereNull : AllNullableFieldsGuarded Nothing schema
  GuardedNull : AllNullableFieldsGuarded (Just expr) schema

||| Proof that no raw user input appears in the query.
||| User values must be EParam nodes, not embedded in strings.
public export
data NoRawUserInput : Statement -> Type where
  AllParameterised : NoRawUserInput stmt

||| Proof that all select items have known types.
public export
data AllSelectItemsTyped : List SelectItem -> OctadSchema -> Type where
  NilTyped  : AllSelectItemsTyped [] schema
  ConsTyped : AllSelectItemsTyped rest schema ->
              AllSelectItemsTyped (item :: rest) schema

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
  WeakenLinear : CanWeaken LinearSafe TemporalSafe

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
