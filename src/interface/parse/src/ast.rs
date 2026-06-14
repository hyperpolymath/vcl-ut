// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Faithful Rust mirror of the Idris2 query AST in `src/core/Grammar.idr`
//! (the type the proof corpus certifies). One-to-one with the Idris
//! constructors so the P5b C-ABI marshaller is a structural map with no
//! semantic re-interpretation.
//!
//! TYPE ANNOTATIONS ARE DELIBERATELY ABSENT. In `Grammar.idr` every
//! `Expr` carries a `VqlType`, but the grammar comment is explicit that
//! it "initially [is] TAny, resolved during type checking at Level 2+".
//! A parser never resolves types, so encoding the slot here would be
//! dead, misleading data. The P5b marshaller sets every expression's
//! `VqlType` to `TAny`; the Idris certifier resolves it. This keeps the
//! parser's output honest about what parsing establishes (syntax only).

/// `Grammar.idr`: `data Modality`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Modality {
    Graph,
    Vector,
    Tensor,
    Semantic,
    Document,
    Temporal,
    Provenance,
    Spatial,
}

/// `Grammar.idr`: `data Agent`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Agent {
    Engine,
    Prover(String),
    Validator,
    User(String),
    Federation,
}

/// `Grammar.idr`: `data Literal`. Vectors keep `f64` (Idris `LitVector`
/// is `List Double`); `LitFloat` is `Double`.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Str(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Null,
    Vector(Vec<f64>),
}

/// `Grammar.idr`: `data CompOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompOp {
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    Like,
    In,
}

/// `Grammar.idr`: `data LogicOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicOp {
    And,
    Or,
    Not,
}

/// `Grammar.idr`: `data AggFunc`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AggFunc {
    Count,
    Sum,
    Avg,
    Min,
    Max,
}

/// `Grammar.idr`: `data EpistemicOp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EpistemicOp {
    Knows,
    Believes,
    CommonKnowledge,
}

/// `Grammar.idr`: `record FieldRef`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldRef {
    pub modality: Modality,
    pub field_name: String,
}

/// `Grammar.idr`: `data Expr` (the `mutual` block). `VqlType` slots are
/// omitted — see the module note.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Field(FieldRef),
    Literal(Literal),
    Compare(CompOp, Box<Expr>, Box<Expr>),
    /// `ELogic`: And/Or carry two operands, Not carries one (`None` rhs).
    Logic(LogicOp, Box<Expr>, Option<Box<Expr>>),
    Aggregate(AggFunc, Box<Expr>),
    Param(String),
    Star,
    Subquery(Box<Statement>),
    Epistemic(EpistemicOp, Agent, Box<Expr>),
    Announce(Agent, Box<Expr>, Box<Expr>),
}

/// `Grammar.idr`: `data SelectItem`.
#[derive(Debug, Clone, PartialEq)]
pub enum SelectItem {
    Field(FieldRef),
    Modality(Modality),
    Aggregate(AggFunc, Expr),
    Star,
}

/// `Grammar.idr`: `data Source`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    Octad(String),
    Federation(String),
    Store(String),
}

/// `Grammar.idr`: `data DriftPolicy` (defined in the grammar; not yet a
/// `Statement` field — mirrored for completeness/fidelity).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriftPolicy {
    Strict,
    Repair,
    Tolerate,
    Latest,
}

/// `Grammar.idr`: `data ProofClause`.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofClause {
    Attached,
    Witness(String),
    Assert(Expr),
}

/// `Grammar.idr`: `data EffectDecl`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectDecl {
    Read,
    Write,
    ReadWrite,
    Consume,
}

/// `Grammar.idr`: `data VersionConstraint` (Idris `Nat` -> `u64`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VersionConstraint {
    Latest,
    AtLeast(u64),
    Exact(u64),
    Range(u64, u64),
}

/// `Grammar.idr`: `data LinearAnnotation` (Idris `Nat` -> `u64`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinearAnnotation {
    Unlimited,
    UseOnce,
    Bounded(u64),
}

/// `Grammar.idr`: `data EpistemicRequirement`.
#[derive(Debug, Clone, PartialEq)]
pub enum EpistemicRequirement {
    Knows(Agent, Expr),
    Believes(Agent, Expr),
    Common(Expr),
    Entails(Agent, Agent, Expr),
}

/// `Grammar.idr`: `data EpistemicClause` (`EpClause agents requirements`).
#[derive(Debug, Clone, PartialEq)]
pub struct EpistemicClause {
    pub agents: Vec<Agent>,
    pub requirements: Vec<EpistemicRequirement>,
}

/// `interface/abi/Types.idr`: `data SafetyLevel` (tags 0..=10, exactly
/// `safetyLevelToInt`). `requested_level` on `Statement` is a stored
/// field there, consumed by `Checker.certifyRequested`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SafetyLevel {
    ParseSafe = 0,
    SchemaBound = 1,
    TypeCompat = 2,
    NullSafe = 3,
    InjectionProof = 4,
    ResultTyped = 5,
    CardinalitySafe = 6,
    EffectTracked = 7,
    TemporalSafe = 8,
    LinearSafe = 9,
    EpistemicSafe = 10,
}

/// `Grammar.idr`: `data Verb`. Read verbs (`Select`/`Inspect`/`Verify`) carry
/// the existing relational semantics; the mutating verbs (`Assert`/`Declare`/
/// `Retract`) are parsed as tags over the same body (S1). `Merge`/`Split`/
/// `Normalise` are the S2 consonance-transition verbs: they do NOT fit the
/// single-source, result-returning `Statement`, so they tag a [`Transition`]
/// (parsed by `parser::parse_op`, NOT `parse`) — see [`Transition`]/[`VclOp`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verb {
    Select,
    Inspect,
    Verify,
    Assert,
    Declare,
    Retract,
    // S2 transition verbs (see `Transition`/`VclOp` below).
    Merge,
    Split,
    Normalise,
}

/// `Grammar.idr`: `record Statement` (`orderBy` is `(field, ascending?)`;
/// Idris `Nat` limit/offset -> `u64`).
#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    pub select_items: Vec<SelectItem>,
    pub source: Source,
    pub where_clause: Option<Expr>,
    pub group_by: Vec<FieldRef>,
    pub having: Option<Expr>,
    pub order_by: Vec<(FieldRef, bool)>,
    pub limit: Option<u64>,
    pub offset: Option<u64>,
    pub proof_clause: Option<ProofClause>,
    pub effect_decl: Option<EffectDecl>,
    pub version_const: Option<VersionConstraint>,
    pub linear_annot: Option<LinearAnnotation>,
    pub epistemic_clause: Option<EpistemicClause>,
    pub requested_level: SafetyLevel,
    /// VCL consonance verb (S1) — mirrors `Grammar.idr`'s additive `verb`.
    pub verb: Verb,
}

// ── S2 consonance transitions (mirror of `src/core/Transition.idr`) ───
//
// MERGE / SPLIT / NORMALISE are the multi-subject / result-less
// consonance transitions. They do NOT fit `Statement` (single `source`,
// always result-returning), so they are a SEPARATE `Transition` type and
// the top-level operation is the sum `VclOp`. This mirrors the Idris
// constructors one-to-one (positional), so the marshaller stays a
// structural map. The proof corpus (`Transition.idr`) certifies only the
// statically-checkable obligations; the recompute port lives in
// `decider::certified_transition_level`.

/// `Transition.idr`: `data SubjectRef = MkSubjectRef String`. A consonance
/// subject identity handle (the octad / identity UUID), DELIBERATELY
/// distinct from [`Source`] (a read-LOCATION): two identities in the same
/// store are different subjects, which `Source` equality could not tell
/// apart. (Identity-vs-location beyond handle equality is OWED — see the
/// Idris module note and `VERIFICATION-STANCE.adoc` §S2.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubjectRef(pub String);

/// `Transition.idr`: `data RepairJustification` — the justified repair path
/// for a NORMALISE, mirroring the engine's authority-ranked regenerator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RepairJustification {
    /// `FromAuthoritative`: regenerate from the authoritative modality.
    FromAuthoritative(Modality),
    /// `MergeModalities`: merge across modalities.
    MergeModalities,
    /// `UserResolve`: escalate to a user decision.
    UserResolve,
}

/// `Transition.idr`: `data Transition`. MERGE/SPLIT carry an optional
/// `evidence` `Expr` (the consonance condition, e.g. a drift bound) and a
/// requested level; NORMALISE carries its justification by construction (an
/// unjustified normalise is UNREPRESENTABLE). Variants are positional,
/// matching the Idris constructors exactly.
#[derive(Debug, Clone, PartialEq)]
pub enum Transition {
    /// `TMerge left right into evidence level`: two DISTINCT inputs → one
    /// identity.
    Merge(SubjectRef, SubjectRef, SubjectRef, Option<Expr>, SafetyLevel),
    /// `TSplit from outL outR evidence level`: one identity → two DISTINCT
    /// outputs.
    Split(SubjectRef, SubjectRef, SubjectRef, Option<Expr>, SafetyLevel),
    /// `TNormalise subject justification level`: repair transition, NO result
    /// set, justified.
    Normalise(SubjectRef, RepairJustification, SafetyLevel),
}

/// `Transition.idr`: `data VclOp = Query Statement | Transit Transition` —
/// the top-level VCL operation: a relational query OR a consonance
/// transition. The `Query` payload is boxed (as `Expr::Subquery` already
/// boxes `Statement`) so the two arms are size-balanced; this is a pure
/// Rust-layout choice and does NOT change the wire image — a `Query` is
/// still tag `0` followed by the statement body.
#[derive(Debug, Clone, PartialEq)]
pub enum VclOp {
    Query(Box<Statement>),
    Transit(Transition),
}
