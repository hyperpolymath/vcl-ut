// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// VCL-total Abstract Syntax Tree — ReScript representation
//
// Mirrors VclTotal.Core.Grammar (Idris2) for parser output.
// Every type here corresponds one-to-one with the Idris2 AST defined in
// src/core/Grammar.idr, enabling round-trip serialisation across the
// Idris2 → C ABI → Zig FFI → ReScript bridge.
//
// The Idris2 side carries dependent-type proofs (TypeCompatible,
// WellFormed, SafetyCertificate) that cannot be expressed in ReScript.
// This module provides the *data* representation only; the ReScript
// parser (VclTotalParser.res) constructs these nodes and the Zig FFI
// layer validates them against the formal specification.

// ═══════════════════════════════════════════════════════════════════════
// Modality References (VeriSimDB octad)
// ═══════════════════════════════════════════════════════════════════════

/// The 8 VeriSimDB modalities an octad can contain.
/// Maps to VclTotal.Core.Grammar.Modality (Idris2).
type modality = Graph | Vector | Tensor | Semantic | Document | Temporal | Provenance | Spatial

// ═══════════════════════════════════════════════════════════════════════
// Epistemic Agents
// ═══════════════════════════════════════════════════════════════════════

/// Epistemic agents whose knowledge/belief state is tracked.
/// Maps to VclTotal.Core.Grammar.Agent (Idris2).
type agent =
  | AgEngine
  | AgProver(string)
  | AgValidator
  | AgUser(string)
  | AgFederation

// ═══════════════════════════════════════════════════════════════════════
// Value Types (type system for expressions)
// ═══════════════════════════════════════════════════════════════════════

/// Types that VCL-total expressions can evaluate to.
/// Maps to VclTotal.Core.Grammar.VqlType (Idris2).
///
/// TVector carries a dimension count (e.g. TVector(768) for an embedding).
/// TRecord carries an array of (field_name, field_type) pairs.
/// TNull wraps any type to make it nullable.
/// TAny is unresolved — present before type-checking (Level 2+).
type rec vqlType =
  | TString
  | TInt
  | TFloat
  | TBool
  | TBytes
  | TVector(int)
  | TTimestamp
  | THash
  | TList(vqlType)
  | TRecord(array<(string, vqlType)>)
  | TOctad
  | TNull(vqlType)
  | TAny
  | TKnows(agent, vqlType)
  | TBelieves(agent, vqlType)
  | TCommonKnowledge(vqlType)

// ═══════════════════════════════════════════════════════════════════════
// Expressions — Field References and Literals
// ═══════════════════════════════════════════════════════════════════════

/// Field reference: MODALITY.field_name
/// E.g. GRAPH.name, VECTOR.embedding, TEMPORAL.created_at
/// Maps to VclTotal.Core.Grammar.FieldRef (Idris2 record).
type fieldRef = {modality: modality, fieldName: string}

/// Literal values that can appear in VCL-total expressions.
/// Maps to VclTotal.Core.Grammar.Literal (Idris2).
///
/// LitVector holds a dense float array (e.g. for similarity search).
type literal =
  | LitString(string)
  | LitInt(int)
  | LitFloat(float)
  | LitBool(bool)
  | LitNull
  | LitVector(array<float>)

// ═══════════════════════════════════════════════════════════════════════
// Operators
// ═══════════════════════════════════════════════════════════════════════

/// Comparison operators for WHERE clauses.
/// Maps to VclTotal.Core.Grammar.CompOp (Idris2).
type compOp = Eq | NotEq | Lt | Gt | LtEq | GtEq | Like | In

/// Logical operators for combining predicates.
/// Maps to VclTotal.Core.Grammar.LogicOp (Idris2).
/// Not is unary (right operand is None in ELogic).
type logicOp = And | Or | Not

/// Aggregate functions for SELECT and HAVING clauses.
/// Maps to VclTotal.Core.Grammar.AggFunc (Idris2).
type aggFunc = Count | Sum | Avg | Min | Max

/// Epistemic operators for modal logic expressions.
/// Maps to VclTotal.Core.Grammar.EpistemicOp (Idris2).
type epistemicOp = OpKnows | OpBelieves | OpCommonKnowledge

// ═══════════════════════════════════════════════════════════════════════
// Expression AST
// ═══════════════════════════════════════════════════════════════════════

/// Expression AST node.
/// Every expression carries a vqlType annotation (initially TAny,
/// resolved during type checking at Level 2+).
///
/// Maps to VclTotal.Core.Grammar.Expr (Idris2), which is mutually
/// recursive with Statement (via ESubquery).
///
/// - EField: references a modality field (GRAPH.name)
/// - ELiteral: a constant value ('hello', 42, true)
/// - ECompare: binary comparison (left op right), result type is TBool
/// - ELogic: logical combinator (And/Or need two exprs, Not needs one)
/// - EAggregate: aggregate function applied to an expression
/// - EParam: parameterised input ($1, $name) — required at Level 4+
/// - EStar: wildcard (*) in SELECT
/// - ESubquery: nested SELECT statement
type rec expr =
  | EField(fieldRef, vqlType)
  | ELiteral(literal, vqlType)
  | ECompare(compOp, expr, expr, vqlType)
  | ELogic(logicOp, expr, option<expr>, vqlType)
  | EAggregate(aggFunc, expr, vqlType)
  | EParam(string, vqlType)
  | EStar
  | ESubquery(statement)
  | EEpistemic(epistemicOp, agent, expr, vqlType)
  | EAnnounce(agent, expr, expr, vqlType)

// ═══════════════════════════════════════════════════════════════════════
// Clauses
// ═══════════════════════════════════════════════════════════════════════

/// SELECT clause item.
/// Maps to VclTotal.Core.Grammar.SelectItem (Idris2).
///
/// - SelField: single field reference (GRAPH.name)
/// - SelModality: entire modality (GRAPH)
/// - SelAggregate: aggregate expression (COUNT(GRAPH.name))
/// - SelStar: all modalities (*)
and selectItem =
  | SelField(fieldRef)
  | SelModality(modality)
  | SelAggregate(aggFunc, expr)
  | SelStar

/// FROM clause source.
/// Maps to VclTotal.Core.Grammar.Source (Idris2).
///
/// - SrcOctad: a single octad by UUID (HEXAD <uuid>)
/// - SrcFederation: a federation pattern (FEDERATION <glob>)
/// - SrcStore: a named store (STORE <id>)
and source =
  | SrcOctad(string)
  | SrcFederation(string)
  | SrcStore(string)

/// PROOF clause for dependent-type verification (VCL-DT extension).
/// Maps to VclTotal.Core.Grammar.ProofClause (Idris2).
///
/// - ProofAttached: sigma-type proof is bundled with the result
/// - ProofWitness: references a named witness (e.g. a pre-registered proof)
/// - ProofAssert: inline assertion expression
and proofClause =
  | ProofAttached
  | ProofWitness(string)
  | ProofAssert(expr)

/// Effect declaration for Level 7 (effect tracking).
/// Maps to VclTotal.Core.Grammar.EffectDecl (Idris2).
///
/// - EffRead: query only reads data
/// - EffWrite: query writes data
/// - EffReadWrite: query both reads and writes
/// - EffConsume: query consumes a linear resource (irreversible)
and effectDecl = EffRead | EffWrite | EffReadWrite | EffConsume

/// Version constraint for Level 8 (temporal safety).
/// Maps to VclTotal.Core.Grammar.VersionConstraint (Idris2).
///
/// VeriSimDB supports time-travel queries; these constrain which
/// version of the data the query operates on.
and versionConstraint =
  | VerLatest
  | VerAtLeast(int)
  | VerExact(int)
  | VerRange(int, int)

/// Linearity annotation for Level 9.
/// Maps to VclTotal.Core.Grammar.LinearAnnotation (Idris2).
///
/// - LinUnlimited: no constraint (default)
/// - LinUseOnce: resource consumed after one read (CONSUME AFTER 1 USE)
/// - LinBounded: resource has a fixed usage limit (USAGE LIMIT n)
and linearAnnotation =
  | LinUnlimited
  | LinUseOnce
  | LinBounded(int)

/// An epistemic requirement within an EPISTEMIC clause.
/// Maps to VclTotal.Core.Grammar.EpistemicRequirement (Idris2).
and epistemicRequirement =
  | EpReqKnows(agent, expr)
  | EpReqBelieves(agent, expr)
  | EpReqCommon(expr)
  | EpReqEntails(agent, agent, expr)

/// Epistemic clause for Level 10 (epistemic safety).
/// Maps to VclTotal.Core.Grammar.EpistemicClause (Idris2).
and epistemicClause = EpClause(array<agent>, array<epistemicRequirement>)

// ═══════════════════════════════════════════════════════════════════════
// Safety Levels
// ═══════════════════════════════════════════════════════════════════════

/// The 11 progressive safety levels (0-10).
/// Maps to VclTotal.ABI.Types.SafetyLevel (Idris2).
///
/// Each level subsumes all prior levels: a query at level N has passed
/// all checks from levels 0 through N.
and safetyLevel =
  | ParseSafe
  | SchemaBound
  | TypeCompat
  | NullSafe
  | InjectionProof
  | ResultTyped
  | CardinalitySafe
  | EffectTracked
  | TemporalSafe
  | LinearSafe
  | EpistemicSafe

// ═══════════════════════════════════════════════════════════════════════
// Statement (top-level query)
// ═══════════════════════════════════════════════════════════════════════

/// A complete VCL-total query statement.
/// Maps to VclTotal.Core.Grammar.Statement (Idris2 record).
///
/// Contains the standard SQL-like clauses (SELECT, FROM, WHERE, etc.)
/// plus VCL-total extension clauses for proof, effects, versioning, and
/// linearity. The requestedLevel indicates the highest safety level
/// that the parser inferred from the extension clauses present.
and statement = {
  /// Fields to retrieve (at least one required for well-formedness)
  selectItems: array<selectItem>,
  /// Data source (octad, federation, or store)
  source: source,
  /// Optional WHERE predicate
  whereClause: option<expr>,
  /// Fields to group by (empty array = no grouping)
  groupBy: array<fieldRef>,
  /// Optional HAVING predicate (requires GROUP BY)
  having: option<expr>,
  /// Order specification: (field, ascending?) pairs
  orderBy: array<(fieldRef, bool)>,
  /// Maximum number of results (required at Level 6+)
  limit: option<int>,
  /// Number of results to skip
  offset: option<int>,
  /// VCL-total extension: proof clause (Level 4+)
  proofClause: option<proofClause>,
  /// VCL-total extension: effect declaration (Level 7+)
  effectDecl: option<effectDecl>,
  /// VCL-total extension: version constraint (Level 8+)
  versionConst: option<versionConstraint>,
  /// VCL-total extension: linearity annotation (Level 9)
  linearAnnot: option<linearAnnotation>,
  /// VCL-total extension: epistemic clause (Level 10)
  epistemicClause: option<epistemicClause>,
  /// Highest safety level inferred from present clauses
  requestedLevel: safetyLevel,
}

// ═══════════════════════════════════════════════════════════════════════
// Conversion helpers
// ═══════════════════════════════════════════════════════════════════════

/// Convert a safety level to its integer tag (0-10).
/// Matches VclTotal.ABI.Types.safetyLevelToInt (Idris2).
let safetyLevelToInt = (level: safetyLevel): int =>
  switch level {
  | ParseSafe => 0
  | SchemaBound => 1
  | TypeCompat => 2
  | NullSafe => 3
  | InjectionProof => 4
  | ResultTyped => 5
  | CardinalitySafe => 6
  | EffectTracked => 7
  | TemporalSafe => 8
  | LinearSafe => 9
  | EpistemicSafe => 10
  }

/// Convert a modality to its string name.
/// Matches VclTotal.Core.Grammar.modalityName (Idris2).
let modalityName = (m: modality): string =>
  switch m {
  | Graph => "GRAPH"
  | Vector => "VECTOR"
  | Tensor => "TENSOR"
  | Semantic => "SEMANTIC"
  | Document => "DOCUMENT"
  | Temporal => "TEMPORAL"
  | Provenance => "PROVENANCE"
  | Spatial => "SPATIAL"
  }

/// Convert a modality to its integer tag (0-7).
/// Matches VclTotal.Core.Grammar.modalityToInt (Idris2).
let modalityToInt = (m: modality): int =>
  switch m {
  | Graph => 0
  | Vector => 1
  | Tensor => 2
  | Semantic => 3
  | Document => 4
  | Temporal => 5
  | Provenance => 6
  | Spatial => 7
  }

/// Convert a comparison operator to its integer tag (0-7).
/// Matches VclTotal.Core.Grammar.compOpToInt (Idris2).
let compOpToInt = (op: compOp): int =>
  switch op {
  | Eq => 0
  | NotEq => 1
  | Lt => 2
  | Gt => 3
  | LtEq => 4
  | GtEq => 5
  | Like => 6
  | In => 7
  }

/// Convert an aggregate function to its integer tag (0-4).
/// Matches VclTotal.Core.Grammar.aggFuncToInt (Idris2).
let aggFuncToInt = (f: aggFunc): int =>
  switch f {
  | Count => 0
  | Sum => 1
  | Avg => 2
  | Min => 3
  | Max => 4
  }

/// Convert an effect declaration to its integer tag (0-3).
/// Matches VclTotal.Core.Grammar.effectDeclToInt (Idris2).
let effectDeclToInt = (e: effectDecl): int =>
  switch e {
  | EffRead => 0
  | EffWrite => 1
  | EffReadWrite => 2
  | EffConsume => 3
  }

/// Compare two safety levels by their numeric rank.
/// Returns positive if a > b, negative if a < b, zero if equal.
let compareSafetyLevels = (a: safetyLevel, b: safetyLevel): int =>
  safetyLevelToInt(a) - safetyLevelToInt(b)

/// Return the higher of two safety levels.
let maxSafetyLevel = (a: safetyLevel, b: safetyLevel): safetyLevel =>
  if compareSafetyLevels(a, b) >= 0 {
    a
  } else {
    b
  }

/// Convert an agent to its string name.
/// Matches VclTotal.Core.Grammar.agentName (Idris2).
let agentName = (a: agent): string =>
  switch a {
  | AgEngine => "ENGINE"
  | AgProver(name) => "PROVER:" ++ name
  | AgValidator => "VALIDATOR"
  | AgUser(name) => "USER:" ++ name
  | AgFederation => "FEDERATION"
  }

/// Convert an agent to its integer tag (0-4).
/// Matches VclTotal.Core.Grammar.agentToInt (Idris2).
let agentToInt = (a: agent): int =>
  switch a {
  | AgEngine => 0
  | AgProver(_) => 1
  | AgValidator => 2
  | AgUser(_) => 3
  | AgFederation => 4
  }

/// Convert an epistemic operator to its integer tag (0-2).
/// Matches VclTotal.Core.Grammar.epistemicOpToInt (Idris2).
let epistemicOpToInt = (op: epistemicOp): int =>
  switch op {
  | OpKnows => 0
  | OpBelieves => 1
  | OpCommonKnowledge => 2
  }
