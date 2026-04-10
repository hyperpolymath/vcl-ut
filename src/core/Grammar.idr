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

module VclTotal.Core.Grammar

import VclTotal.ABI.Types
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
-- Epistemic Agents
-- ═══════════════════════════════════════════════════════════════════════

||| An epistemic agent — an entity whose knowledge/belief state is tracked.
||| In VeriSimDB, agents are system components that produce or consume
||| propositions: provers, validators, the engine itself, or external users.
public export
data Agent
  = AgEngine          -- The VeriSimDB consonance engine itself
  | AgProver String   -- A named prover (e.g. "lean4", "idris2")
  | AgValidator       -- The VCL-total validation pipeline
  | AgUser String     -- A named external user / client
  | AgFederation      -- The federation consensus layer

||| Convert agent to its string name.
public export
agentName : Agent -> String
agentName AgEngine        = "ENGINE"
agentName (AgProver name) = "PROVER:" ++ name
agentName AgValidator     = "VALIDATOR"
agentName (AgUser name)   = "USER:" ++ name
agentName AgFederation    = "FEDERATION"

||| Encode agent as C integer (tag only; parameterised agents carry payload separately).
public export
agentToInt : Agent -> Int
agentToInt AgEngine        = 0
agentToInt (AgProver _)    = 1
agentToInt AgValidator     = 2
agentToInt (AgUser _)      = 3
agentToInt AgFederation    = 4

-- ═══════════════════════════════════════════════════════════════════════
-- Value Types (type system for expressions)
-- ═══════════════════════════════════════════════════════════════════════

||| Types that VCL-total expressions can evaluate to.
|||
||| The epistemic type constructors (TKnows, TBelieves, TCommonKnowledge)
||| encode S5 modal logic operators at the type level:
|||   - TKnows agent P     : agent has verified knowledge of P
|||   - TBelieves agent P  : agent holds P as belief (weaker than knowledge)
|||   - TCommonKnowledge P : all agents in the federation know P,
|||                          and know that all others know P (ad infinitum)
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
  -- Epistemic types (S5 modal logic operators)
  | TKnows Agent VqlType           -- K_a(P): agent knows proposition of type P
  | TBelieves Agent VqlType        -- B_a(P): agent believes proposition of type P
  | TCommonKnowledge VqlType       -- C(P): common knowledge across federation

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
||| Epistemic operators for modal logic expressions.
public export
data EpistemicOp
  = OpKnows             -- K_a: agent knows
  | OpBelieves          -- B_a: agent believes
  | OpCommonKnowledge   -- C: common knowledge (all agents, iterated)

||| Encode EpistemicOp as C integer.
public export
epistemicOpToInt : EpistemicOp -> Int
epistemicOpToInt OpKnows           = 0
epistemicOpToInt OpBelieves        = 1
epistemicOpToInt OpCommonKnowledge = 2

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
  -- Epistemic expression nodes (S5 modal logic)
  | EEpistemic EpistemicOp Agent Expr VqlType
      -- ^ Modal operator application: KNOWS agent expr, BELIEVES agent expr,
      --   or COMMON KNOWLEDGE expr. The VqlType is the epistemic result type
      --   (TKnows/TBelieves/TCommonKnowledge wrapping the inner type).
  | EAnnounce Agent Expr Expr VqlType
      -- ^ Public announcement: ANNOUNCE agent proposition body.
      --   Models the epistemic effect of an agent publicly declaring a fact.
      --   After announcement, all agents know the proposition holds.
      --   Type: the body expression type, evaluated in the updated epistemic state.

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

||| Epistemic clause for Level 10 (epistemic safety).
|||
||| Specifies the epistemic context: which agents are relevant, what they
||| know/believe, and what epistemic properties must hold for the query
||| result.  The clause triggers S5 modal checking in the pipeline.
|||
||| Syntax:
|||   EPISTEMIC { AGENTS engine, prover:lean4 ;
|||               REQUIRES KNOWS engine (status = 'verified') ;
|||               REQUIRES COMMON KNOWLEDGE (schema_version >= 3) }
public export
data EpistemicClause
  = EpClause
      (List Agent)               -- Agents in scope
      (List EpistemicRequirement) -- Requirements that must hold

||| A single epistemic requirement within an EPISTEMIC clause.
public export
data EpistemicRequirement
  = EpReqKnows Agent Expr         -- REQUIRES KNOWS <agent> <prop>
  | EpReqBelieves Agent Expr      -- REQUIRES BELIEVES <agent> <prop>
  | EpReqCommon Expr              -- REQUIRES COMMON KNOWLEDGE <prop>
  | EpReqEntails Agent Agent Expr -- REQUIRES <a1> ENTAILS <a2> <prop>
      -- ^ Agent a1's knowledge entails agent a2's knowledge of prop.
      --   Formalises knowledge transfer: K_a1(P) → K_a2(P).

||| Encode EpistemicRequirement tag as C integer.
public export
epReqToInt : EpistemicRequirement -> Int
epReqToInt (EpReqKnows _ _)     = 0
epReqToInt (EpReqBelieves _ _)  = 1
epReqToInt (EpReqCommon _)      = 2
epReqToInt (EpReqEntails _ _ _) = 3

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
  epistemicClause : Maybe EpistemicClause  -- Level 10: epistemic safety
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
  OctadSource : HasSource (MkStatement _ (SrcOctad _) _ _ _ _ _ _ _ _ _ _ _ _)
  FederationSource : HasSource (MkStatement _ (SrcFederation _) _ _ _ _ _ _ _ _ _ _ _ _)
  StoreSource : HasSource (MkStatement _ (SrcStore _) _ _ _ _ _ _ _ _ _ _ _ _)

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

||| Proof that a statement requesting Level 10 has an epistemic clause.
public export
data HasEpistemicIfRequired : Statement -> Type where
  NoEpistemicNeeded : HasEpistemicIfRequired stmt
  EpistemicPresent : (epistemicClause stmt = Just ec) -> HasEpistemicIfRequired stmt

||| A well-formed statement satisfies all structural requirements.
public export
data WellFormed : Statement -> Type where
  MkWellFormed :
    HasSelectItems stmt ->
    HasSource stmt ->
    HasLimitIfRequired stmt ->
    HasEffectIfRequired stmt ->
    HasVersionIfRequired stmt ->
    HasEpistemicIfRequired stmt ->
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
