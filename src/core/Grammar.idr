-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Core Grammar — Abstract Syntax Tree
|||
||| Defines the typed AST for VCL-total queries. Every node carries type
||| information sufficient for the 10-level checker to verify safety.
|||
||| The AST extends VCL 3.0 (VeriSimDB's octad query language) with:
|||   - Safety level annotations on every expression
|||   - Effect declarations (read/write/consume)
|||   - Temporal version constraints
|||   - Linearity tracking (use-once resources)
|||   - PROOF clauses for dependent-type verification
|||
||| This module provides:
|||   1. AST node types matching the VCL-total EBNF grammar
|||   2. Well-formedness predicates (structurally valid queries)
|||   3. Type annotations at every expression node

module VqlUt.Core.Grammar

import VqlUt.ABI.Types
import Data.List
import Data.Fin

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Modality References (VeriSimDB octad)
-- ═══════════════════════════════════════════════════════════════════════

||| The 8 VeriSimDB modalities an octad can contain.
public export
data Modality
  = Graph | Vector | Tensor | Semantic
  | Document | Temporal | Provenance | Spatial

||| Convert modality to its string name.
public export
modalityName : Modality -> String
modalityName Graph      = "GRAPH"
modalityName Vector     = "VECTOR"
modalityName Tensor     = "TENSOR"
modalityName Semantic   = "SEMANTIC"
modalityName Document   = "DOCUMENT"
modalityName Temporal   = "TEMPORAL"
modalityName Provenance = "PROVENANCE"
modalityName Spatial    = "SPATIAL"

||| Encode modality as C integer.
public export
modalityToInt : Modality -> Int
modalityToInt Graph      = 0
modalityToInt Vector     = 1
modalityToInt Tensor     = 2
modalityToInt Semantic   = 3
modalityToInt Document   = 4
modalityToInt Temporal   = 5
modalityToInt Provenance = 6
modalityToInt Spatial    = 7

-- ═══════════════════════════════════════════════════════════════════════
-- Value Types (type system for expressions)
-- ═══════════════════════════════════════════════════════════════════════

||| Types that VCL-total expressions can evaluate to.
public export
data VqlType
  = TString          -- Text values
  | TInt             -- Integer values
  | TFloat           -- Floating-point values
  | TBool            -- Boolean values
  | TBytes           -- Binary data (CBOR blobs)
  | TVector Nat      -- Fixed-dimension vector (f32 array)
  | TTimestamp       -- ISO 8601 timestamp
  | THash            -- SHA-256 hash string
  | TList VqlType    -- Homogeneous list
  | TRecord (List (String, VqlType)) -- Named fields
  | TOctad           -- Full octad reference
  | TNull VqlType    -- Nullable version of a type
  | TAny             -- Unresolved type (before type checking)

||| Proof that two types are compatible for comparison.
||| Only same-type comparisons are valid (no implicit coercion).
public export
data TypeCompatible : VqlType -> VqlType -> Type where
  SameType      : TypeCompatible t t
  NullCompat    : TypeCompatible (TNull t) t
  NullCompatSym : TypeCompatible t (TNull t)
  IntFloat      : TypeCompatible TInt TFloat   -- Numeric widening only
  FloatInt      : TypeCompatible TFloat TInt

-- ═══════════════════════════════════════════════════════════════════════
-- Expressions
-- ═══════════════════════════════════════════════════════════════════════

||| Field reference: MODALITY.field_name
public export
record FieldRef where
  constructor MkFieldRef
  modality  : Modality
  fieldName : String

||| Literal values in expressions.
public export
data Literal
  = LitString String
  | LitInt Int
  | LitFloat Double
  | LitBool Bool
  | LitNull
  | LitVector (List Double)

||| Comparison operators.
public export
data CompOp = Eq | NotEq | Lt | Gt | LtEq | GtEq | Like | In

||| Logical operators.
public export
data LogicOp = And | Or | Not

||| Aggregate functions.
public export
data AggFunc = Count | Sum | Avg | Min | Max

||| Expression AST node.
||| Every expression carries a type annotation (initially TAny,
||| resolved during type checking at Level 2+).
public export
data Expr
  = EField FieldRef VqlType              -- Field reference with type
  | ELiteral Literal VqlType             -- Literal with type
  | ECompare CompOp Expr Expr VqlType    -- Comparison (left op right)
  | ELogic LogicOp Expr (Maybe Expr) VqlType -- Logical (And/Or need two, Not needs one)
  | EAggregate AggFunc Expr VqlType      -- Aggregate function
  | EParam String VqlType                -- Parameterised input ($1, $name)
  | EStar                                -- Wildcard (*)
  | ESubquery Statement                  -- Subquery

-- ═══════════════════════════════════════════════════════════════════════
-- Clauses
-- ═══════════════════════════════════════════════════════════════════════

||| SELECT clause item.
public export
data SelectItem
  = SelField FieldRef         -- Single field
  | SelModality Modality      -- Entire modality
  | SelAggregate AggFunc Expr -- Aggregate expression
  | SelStar                   -- All modalities (*)

||| FROM clause source.
public export
data Source
  = SrcOctad String             -- HEXAD <uuid>
  | SrcFederation String        -- FEDERATION <pattern>
  | SrcStore String             -- STORE <id>

||| Drift policy for federation queries.
public export
data DriftPolicy = Strict | Repair | Tolerate | Latest

||| PROOF clause type (VCL-DT extension).
public export
data ProofClause
  = ProofAttached              -- PROOF ATTACHED (sigma type)
  | ProofWitness String        -- PROOF WITNESS <name>
  | ProofAssert Expr           -- PROOF ASSERT <condition>

||| Effect declaration for Level 7 (effect tracking).
public export
data EffectDecl
  = EffRead                    -- EFFECTS { Read }
  | EffWrite                   -- EFFECTS { Write }
  | EffReadWrite               -- EFFECTS { Read, Write }
  | EffConsume                 -- EFFECTS { Consume } (linear)

||| Version constraint for Level 8 (temporal safety).
public export
data VersionConstraint
  = VerLatest                  -- AT LATEST
  | VerAtLeast Nat             -- AT VERSION >= n
  | VerExact Nat               -- AT VERSION = n
  | VerRange Nat Nat           -- AT VERSION BETWEEN n AND m

||| Linearity annotation for Level 9.
public export
data LinearAnnotation
  = LinUnlimited               -- Default (no constraint)
  | LinUseOnce                 -- CONSUME AFTER 1 USE
  | LinBounded Nat             -- USAGE LIMIT n

-- ═══════════════════════════════════════════════════════════════════════
-- Statement (top-level query)
-- ═══════════════════════════════════════════════════════════════════════

||| A complete VCL-total query statement.
public export
record Statement where
  constructor MkStatement
  -- Core clauses (VCL 3.0)
  selectItems   : List SelectItem
  source        : Source
  whereClause   : Maybe Expr
  groupBy       : List FieldRef
  having        : Maybe Expr
  orderBy       : List (FieldRef, Bool)  -- (field, ascending?)
  limit         : Maybe Nat
  offset        : Maybe Nat
  -- VCL-total extensions
  proofClause   : Maybe ProofClause
  effectDecl    : Maybe EffectDecl
  versionConst  : Maybe VersionConstraint
  linearAnnot   : Maybe LinearAnnotation
  -- Metadata
  requestedLevel : SafetyLevel

-- ═══════════════════════════════════════════════════════════════════════
-- Well-Formedness Predicates
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that a statement has at least one select item.
public export
data HasSelectItems : Statement -> Type where
  MkHasSelect : NonEmpty (selectItems stmt) -> HasSelectItems stmt

||| Proof that a statement has a valid source.
public export
data HasSource : Statement -> Type where
  OctadSource : HasSource (MkStatement _ (SrcOctad _) _ _ _ _ _ _ _ _ _ _ _)
  FederationSource : HasSource (MkStatement _ (SrcFederation _) _ _ _ _ _ _ _ _ _ _ _)
  StoreSource : HasSource (MkStatement _ (SrcStore _) _ _ _ _ _ _ _ _ _ _ _)

||| Proof that a statement requesting Level 6+ has a LIMIT clause.
public export
data HasLimitIfRequired : Statement -> Type where
  NoLimitNeeded : HasLimitIfRequired stmt  -- Level < 6
  LimitPresent : (limit stmt = Just n) -> HasLimitIfRequired stmt

||| Proof that a statement requesting Level 7+ has an effect declaration.
public export
data HasEffectIfRequired : Statement -> Type where
  NoEffectNeeded : HasEffectIfRequired stmt
  EffectPresent : (effectDecl stmt = Just e) -> HasEffectIfRequired stmt

||| Proof that a statement requesting Level 8+ has a version constraint.
public export
data HasVersionIfRequired : Statement -> Type where
  NoVersionNeeded : HasVersionIfRequired stmt
  VersionPresent : (versionConst stmt = Just v) -> HasVersionIfRequired stmt

||| A well-formed statement satisfies all structural requirements.
public export
data WellFormed : Statement -> Type where
  MkWellFormed :
    HasSelectItems stmt ->
    HasSource stmt ->
    HasLimitIfRequired stmt ->
    HasEffectIfRequired stmt ->
    HasVersionIfRequired stmt ->
    WellFormed stmt

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI Exports
-- ═══════════════════════════════════════════════════════════════════════

||| Encode CompOp as C integer.
public export
compOpToInt : CompOp -> Int
compOpToInt Eq    = 0
compOpToInt NotEq = 1
compOpToInt Lt    = 2
compOpToInt Gt    = 3
compOpToInt LtEq  = 4
compOpToInt GtEq  = 5
compOpToInt Like  = 6
compOpToInt In    = 7

||| Encode AggFunc as C integer.
public export
aggFuncToInt : AggFunc -> Int
aggFuncToInt Count = 0
aggFuncToInt Sum   = 1
aggFuncToInt Avg   = 2
aggFuncToInt Min   = 3
aggFuncToInt Max   = 4

||| Encode EffectDecl as C integer.
public export
effectDeclToInt : EffectDecl -> Int
effectDeclToInt EffRead      = 0
effectDeclToInt EffWrite     = 1
effectDeclToInt EffReadWrite = 2
effectDeclToInt EffConsume   = 3
