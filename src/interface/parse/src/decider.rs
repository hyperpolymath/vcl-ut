// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! P5c (recompute tier) — a **faithful** Rust port of the certified
//! VCL-total decision core: `VclTotal.Core.Decide` + the
//! `VclTotal.Core.Checker` `checkLevelN`/`certifyAt`/`certifiedLevel`
//! spine + `VclTotal.Core.Schema` resolution.
//!
//! ROLE. The corpus proves *once* (`checkLevelNSound`,
//! machine-checked, offline-re-checkable with Idris2) that the
//! decision procedure is sound. This module re-runs *that exact
//! procedure* so a consumer can independently recompute the safety
//! verdict over a wire-decoded `Statement`/`OctadSchema` (the
//! recompute-PCC tier; see `VERIFICATION-STANCE.adoc`'s two-tier
//! boundary model). It carries NO proofs and is NOT the source of
//! truth: faithfulness to the corpus is *machine-pinned* by the
//! cross-language conformance fixtures (`tests/conformance_emit.rs` ⇄
//! `WireConformance`), Rust verdict == Idris `certifiedLevel`, on the
//! same golden bytes.
//!
//! FAITHFULNESS ON THE WIRE DOMAIN. `Grammar.Expr` carries a `VqlType`
//! at every node; the wire format omits it and every decoder
//! (Idris `fromWire`, the Rust mirror) fills `TAny`. So on a
//! *wire-decoded* statement the corpus `resolveExprType` is `TAny`
//! everywhere except `EField` (→ schema) and `ESubquery` (→ `TOctad`).
//! The Rust `ast::Expr` therefore needs no `ty` field and this port is
//! exact *for the recompute domain* (decoded statements) — which is the
//! only domain this tier runs on. This is the precise reason the
//! no-`ty` AST is sound here, not a shortcut.
//!
//! Same SPARK-grade posture as the rest of the crate (lint set in
//! lib.rs): total, no panic, no unchecked arithmetic. Pure functions.

use crate::ast::{
    Agent, CompOp, EpistemicClause, EpistemicRequirement, Expr, FieldRef, Literal, Modality,
    SafetyLevel, SelectItem, Statement,
};
use crate::schema::{ModalitySchema, OctadSchema, VqlType};

// ── Schema resolution (Schema.idr) ───────────────────────────────────

fn modality_to_int(m: &Modality) -> u8 {
    match m {
        Modality::Graph => 0,
        Modality::Vector => 1,
        Modality::Tensor => 2,
        Modality::Semantic => 3,
        Modality::Document => 4,
        Modality::Temporal => 5,
        Modality::Provenance => 6,
        Modality::Spatial => 7,
    }
}

fn lookup_modality<'a>(m: &Modality, s: &'a OctadSchema) -> &'a ModalitySchema {
    match m {
        Modality::Graph => &s.graph,
        Modality::Vector => &s.vector,
        Modality::Tensor => &s.tensor,
        Modality::Semantic => &s.semantic,
        Modality::Document => &s.document,
        Modality::Temporal => &s.temporal,
        Modality::Provenance => &s.provenance,
        Modality::Spatial => &s.spatial,
    }
}

/// `Schema.resolveFieldRef` = `lookupField (fieldName ref) (lookupModality …)`;
/// `lookupField target = find (\f => f.name == target)` (first match).
fn resolve_field_ref<'a>(r: &FieldRef, s: &'a OctadSchema) -> Option<&'a crate::schema::FieldDef> {
    lookup_modality(&r.modality, s)
        .fields
        .iter()
        .find(|f| f.name == r.field_name)
}

/// `Schema.resolveType`: `Just fd => ty fd`, `Nothing => TAny`.
fn resolve_type(r: &FieldRef, s: &OctadSchema) -> VqlType {
    match resolve_field_ref(r, s) {
        Some(fd) => fd.ty.clone(),
        None => VqlType::TAny,
    }
}

/// `Schema.isNullable`: `Just fd => nullable fd`, `Nothing => True`
/// (unknown fields treated as nullable).
fn is_nullable(r: &FieldRef, s: &OctadSchema) -> bool {
    match resolve_field_ref(r, s) {
        Some(fd) => fd.nullable,
        None => true,
    }
}

// ── Type resolution over expressions (Decide.idr) ────────────────────
//
// On a wire-decoded statement every non-`EField` node's annotation is
// `TAny` (the wire format omits `VqlType`); `ESubquery` is `TOctad`,
// `EStar` is `TAny`. This mirrors `Decide.resolveExprType` exactly for
// the recompute domain.

fn resolve_expr_type(e: &Expr, s: &OctadSchema) -> VqlType {
    match e {
        Expr::Field(r) => resolve_type(r, s),
        Expr::Subquery(_) => VqlType::TOctad,
        _ => VqlType::TAny,
    }
}

fn resolve_select_item_type(si: &SelectItem, s: &OctadSchema) -> VqlType {
    match si {
        SelectItem::Field(r) => resolve_type(r, s),
        SelectItem::Modality(_) => VqlType::TOctad,
        SelectItem::Aggregate(_, e) => resolve_expr_type(e, s),
        SelectItem::Star => VqlType::TAny,
    }
}

fn not_any_ty(t: &VqlType) -> bool {
    !matches!(t, VqlType::TAny)
}

// ── Level 5 — ResultTyped ────────────────────────────────────────────

fn select_item_typed(si: &SelectItem, s: &OctadSchema) -> bool {
    not_any_ty(&resolve_select_item_type(si, s))
}

fn select_items_typed(items: &[SelectItem], s: &OctadSchema) -> bool {
    items.iter().all(|i| select_item_typed(i, s))
}

// ── Level 2 — TypeCompat ─────────────────────────────────────────────

fn agent_eq(a: &Agent, b: &Agent) -> bool {
    match (a, b) {
        (Agent::Engine, Agent::Engine)
        | (Agent::Validator, Agent::Validator)
        | (Agent::Federation, Agent::Federation) => true,
        (Agent::Prover(x), Agent::Prover(y)) | (Agent::User(x), Agent::User(y)) => x == y,
        _ => false,
    }
}

fn vqltype_eq(a: &VqlType, b: &VqlType) -> bool {
    use VqlType::{
        TAny, TBelieves, TBool, TBytes, TCommonKnowledge, TFloat, THash, TInt, TKnows, TList,
        TNull, TOctad, TRecord, TString, TTimestamp, TVector,
    };
    match (a, b) {
        (TString, TString)
        | (TInt, TInt)
        | (TFloat, TFloat)
        | (TBool, TBool)
        | (TBytes, TBytes)
        | (TTimestamp, TTimestamp)
        | (THash, THash)
        | (TOctad, TOctad)
        | (TAny, TAny) => true,
        (TVector(n), TVector(m)) => n == m,
        (TList(x), TList(y))
        | (TNull(x), TNull(y))
        | (TCommonKnowledge(x), TCommonKnowledge(y)) => vqltype_eq(x, y),
        (TKnows(a1, t1), TKnows(a2, t2)) | (TBelieves(a1, t1), TBelieves(a2, t2)) => {
            agent_eq(a1, a2) && vqltype_eq(t1, t2)
        }
        (TRecord(xs), TRecord(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys.iter())
                    .all(|((n1, t1), (n2, t2))| n1 == n2 && vqltype_eq(t1, t2))
        }
        _ => false,
    }
}

fn types_compatible(a: &VqlType, b: &VqlType) -> bool {
    // On a wire-decoded statement, `resolveExprType` returns `TAny` for every
    // non-`EField`/`ESubquery` node (literals, params, `*`, …), since the wire
    // format omits `VqlType` annotations (see crate-level note in `decider.rs`).
    // `TAny` is therefore the "not yet resolved" sentinel and is universally
    // compatible — otherwise *every* literal comparison would fail L2 even for
    // correctly-typed queries.
    if matches!(a, VqlType::TAny) || matches!(b, VqlType::TAny) {
        return true;
    }
    if vqltype_eq(a, b) {
        return true;
    }
    match (a, b) {
        (VqlType::TNull(inner), other) => vqltype_eq(inner, other),
        (other, VqlType::TNull(inner)) => vqltype_eq(other, inner),
        (VqlType::TInt, VqlType::TFloat) | (VqlType::TFloat, VqlType::TInt) => true,
        _ => false,
    }
}

/// `Decide.extractComparisons` — all `ECompare` nodes (op,l,r,ty); the
/// annotated type is unused by `comparisonCompatible` so it is dropped.
/// `ESubquery` opaque (own pass), exactly as the corpus.
fn extract_comparisons<'a>(e: &'a Expr, out: &mut Vec<(&'a Expr, &'a Expr)>) {
    match e {
        Expr::Compare(_, l, r) => {
            out.push((l, r));
            extract_comparisons(l, out);
            extract_comparisons(r, out);
        }
        Expr::Logic(_, l, None) => extract_comparisons(l, out),
        Expr::Logic(_, l, Some(r)) => {
            extract_comparisons(l, out);
            extract_comparisons(r, out);
        }
        Expr::Aggregate(_, e2) | Expr::Epistemic(_, _, e2) => extract_comparisons(e2, out),
        Expr::Announce(_, p, b) => {
            extract_comparisons(p, out);
            extract_comparisons(b, out);
        }
        _ => {}
    }
}

fn where_comparisons_compatible(w: &Option<Expr>, s: &OctadSchema) -> bool {
    match w {
        None => true,
        Some(e) => {
            let mut cs = Vec::new();
            extract_comparisons(e, &mut cs);
            cs.iter()
                .all(|(l, r)| types_compatible(&resolve_expr_type(l, s), &resolve_expr_type(r, s)))
        }
    }
}

// ── Level 4 — InjectionProof (Grammar.hasStringLit) ──────────────────

fn has_string_lit(e: &Expr) -> bool {
    match e {
        Expr::Literal(Literal::Str(_)) => true,
        Expr::Compare(_, l, r) => has_string_lit(l) || has_string_lit(r),
        Expr::Logic(_, l, None) => has_string_lit(l),
        Expr::Logic(_, l, Some(r)) => has_string_lit(l) || has_string_lit(r),
        Expr::Aggregate(_, e2) | Expr::Epistemic(_, _, e2) => has_string_lit(e2),
        Expr::Announce(_, p, b) => has_string_lit(p) || has_string_lit(b),
        _ => false,
    }
}

fn where_has_string_lit(stmt: &Statement) -> bool {
    match &stmt.where_clause {
        None => false,
        Some(e) => has_string_lit(e),
    }
}

// ── Level 3 — NullSafe ───────────────────────────────────────────────

fn field_ref_eq(a: &FieldRef, b: &FieldRef) -> bool {
    modality_to_int(&a.modality) == modality_to_int(&b.modality) && a.field_name == b.field_name
}

fn ref_elem(r: &FieldRef, gs: &[FieldRef]) -> bool {
    gs.iter().any(|g| field_ref_eq(r, g))
}

fn expr_field_refs(e: &Expr, out: &mut Vec<FieldRef>) {
    match e {
        Expr::Field(r) => out.push(r.clone()),
        Expr::Compare(_, l, r) => {
            expr_field_refs(l, out);
            expr_field_refs(r, out);
        }
        Expr::Logic(_, l, None) => expr_field_refs(l, out),
        Expr::Logic(_, l, Some(r)) => {
            expr_field_refs(l, out);
            expr_field_refs(r, out);
        }
        Expr::Aggregate(_, e2) | Expr::Epistemic(_, _, e2) => expr_field_refs(e2, out),
        Expr::Announce(_, p, b) => {
            expr_field_refs(p, out);
            expr_field_refs(b, out);
        }
        _ => {}
    }
}

/// `Decide.nullGuardedRefs` — guard clauses (`fld = NULL` / `NULL = fld`
/// / `fld <> NULL` / `NULL <> fld`) precede the general recursion, and a
/// matched guard returns its ref and does NOT fall through (top-down
/// match, exactly as the corpus).
fn null_guarded_refs(e: &Expr, out: &mut Vec<FieldRef>) {
    if let Expr::Compare(op, l, r) = e {
        let guard = matches!(op, CompOp::Eq | CompOp::NotEq);
        if guard {
            if let (Expr::Field(rf), Expr::Literal(Literal::Null)) = (l.as_ref(), r.as_ref()) {
                out.push(rf.clone());
                return;
            }
            if let (Expr::Literal(Literal::Null), Expr::Field(rf)) = (l.as_ref(), r.as_ref()) {
                out.push(rf.clone());
                return;
            }
        }
        null_guarded_refs(l, out);
        null_guarded_refs(r, out);
        return;
    }
    match e {
        Expr::Logic(_, l, None) => null_guarded_refs(l, out),
        Expr::Logic(_, l, Some(r)) => {
            null_guarded_refs(l, out);
            null_guarded_refs(r, out);
        }
        Expr::Aggregate(_, e2) | Expr::Epistemic(_, _, e2) => null_guarded_refs(e2, out),
        Expr::Announce(_, p, b) => {
            null_guarded_refs(p, out);
            null_guarded_refs(b, out);
        }
        _ => {}
    }
}

fn ref_unguarded(s: &OctadSchema, guarded: &[FieldRef], r: &FieldRef) -> bool {
    is_nullable(r, s) && !ref_elem(r, guarded)
}

fn expr_null_safe(e: &Expr, s: &OctadSchema) -> bool {
    let mut guarded = Vec::new();
    null_guarded_refs(e, &mut guarded);
    let mut refs = Vec::new();
    expr_field_refs(e, &mut refs);
    refs.iter().all(|r| !ref_unguarded(s, &guarded, r))
}

fn maybe_expr_null_safe(m: &Option<Expr>, s: &OctadSchema) -> bool {
    match m {
        None => true,
        Some(e) => expr_null_safe(e, s),
    }
}

fn null_safe_stmt(stmt: &Statement, s: &OctadSchema) -> bool {
    maybe_expr_null_safe(&stmt.where_clause, s) && maybe_expr_null_safe(&stmt.having, s)
}

// ── Level 1 — SchemaBound (statementFieldRefs; the thorough extractor) ─
//
// `checkLevel1 = allFieldRefsResolve (statementFieldRefs stmt) &&
//  allFieldRefsResolve (Levels.extractFieldRefs stmt)`. The corpus note
// is authoritative: `Levels.extractFieldRefs stmt ⊆ statementFieldRefs
// stmt` (the latter also descends `ESubquery`), so the second conjunct
// never changes the verdict — `verdict == allFieldRefsResolve
// (statementFieldRefs stmt)`. The conformance harness machine-pins this.

fn extract_field_refs(e: &Expr, out: &mut Vec<FieldRef>) {
    match e {
        Expr::Field(r) => out.push(r.clone()),
        Expr::Compare(_, l, r) => {
            extract_field_refs(l, out);
            extract_field_refs(r, out);
        }
        Expr::Logic(_, l, None) => extract_field_refs(l, out),
        Expr::Logic(_, l, Some(r)) => {
            extract_field_refs(l, out);
            extract_field_refs(r, out);
        }
        Expr::Aggregate(_, e2) | Expr::Epistemic(_, _, e2) => extract_field_refs(e2, out),
        Expr::Subquery(sub) => statement_field_refs(sub, out),
        Expr::Announce(_, p, b) => {
            extract_field_refs(p, out);
            extract_field_refs(b, out);
        }
        _ => {}
    }
}

fn sel_item_field_refs(si: &SelectItem, out: &mut Vec<FieldRef>) {
    match si {
        SelectItem::Field(r) => out.push(r.clone()),
        SelectItem::Aggregate(_, e) => extract_field_refs(e, out),
        _ => {}
    }
}

fn statement_field_refs(stmt: &Statement, out: &mut Vec<FieldRef>) {
    for si in &stmt.select_items {
        sel_item_field_refs(si, out);
    }
    if let Some(w) = &stmt.where_clause {
        extract_field_refs(w, out);
    }
    out.extend(stmt.group_by.iter().cloned());
    if let Some(h) = &stmt.having {
        extract_field_refs(h, out);
    }
    out.extend(stmt.order_by.iter().map(|(fr, _)| fr.clone()));
}

fn field_ref_resolves(r: &FieldRef, s: &OctadSchema) -> bool {
    resolve_field_ref(r, s).is_some()
}

fn check_level1(stmt: &Statement, s: &OctadSchema) -> bool {
    let mut refs = Vec::new();
    statement_field_refs(stmt, &mut refs);
    refs.iter().all(|r| field_ref_resolves(r, s))
}

// ── Levels 6–10 (Decide.idr Phase 4b) ────────────────────────────────

fn linear_enforced(stmt: &Statement) -> bool {
    matches!(
        stmt.linear_annot,
        Some(crate::ast::LinearAnnotation::UseOnce)
            | Some(crate::ast::LinearAnnotation::Bounded(_))
    )
}

fn agent_id(a: &Agent) -> String {
    match a {
        Agent::Engine => "ENGINE".to_string(),
        Agent::Prover(n) => format!("PROVER:{n}"),
        Agent::Validator => "VALIDATOR".to_string(),
        Agent::User(n) => format!("USER:{n}"),
        Agent::Federation => "FEDERATION".to_string(),
    }
}

fn agent_declared(a: &Agent, declared: &[Agent]) -> bool {
    let aid = agent_id(a);
    declared.iter().any(|d| aid == agent_id(d))
}

fn find_undeclared_agents(declared: &[Agent], reqs: &[EpistemicRequirement]) -> Vec<String> {
    let mut out = Vec::new();
    for r in reqs {
        match r {
            EpistemicRequirement::Knows(a, _) | EpistemicRequirement::Believes(a, _) => {
                if !agent_declared(a, declared) {
                    out.push(agent_id(a));
                }
            }
            EpistemicRequirement::Common(_) => {}
            EpistemicRequirement::Entails(a1, a2, _) => {
                if !agent_declared(a1, declared) {
                    out.push(agent_id(a1));
                }
                if !agent_declared(a2, declared) {
                    out.push(agent_id(a2));
                }
            }
        }
    }
    out
}

fn entails_pairs(reqs: &[EpistemicRequirement]) -> Vec<(String, String)> {
    reqs.iter()
        .filter_map(|r| match r {
            EpistemicRequirement::Entails(a1, a2, _) => Some((agent_id(a1), agent_id(a2))),
            _ => None,
        })
        .collect()
}

fn has_circular_entails(reqs: &[EpistemicRequirement]) -> bool {
    let pairs = entails_pairs(reqs);
    pairs
        .iter()
        .any(|(a, b)| pairs.iter().any(|(c, d)| a == d && b == c))
}

fn epi_struct_ok(stmt: &Statement) -> bool {
    match &stmt.epistemic_clause {
        None => false,
        Some(EpistemicClause {
            agents,
            requirements,
        }) => !agents.is_empty() && find_undeclared_agents(agents, requirements).is_empty(),
    }
}

fn epi_no_cycle(stmt: &Statement) -> bool {
    match &stmt.epistemic_clause {
        None => false,
        Some(EpistemicClause { requirements, .. }) => !has_circular_entails(requirements),
    }
}

fn epistemic_consistent_stmt(stmt: &Statement) -> bool {
    epi_struct_ok(stmt) && epi_no_cycle(stmt)
}

// ── checkLevelN verdicts (Checker.idr) ───────────────────────────────
//
// Each returns the *pass* bit (`.0` of the corpus `(Bool,String)`).
// Polarity note: L4's `l4Verdict True => (False, …)` — L4 PASSES iff
// the WHERE has NO raw string literal.

fn check_level(n: u8, stmt: &Statement, s: &OctadSchema) -> bool {
    match n {
        0 => true,
        1 => check_level1(stmt, s),
        2 => where_comparisons_compatible(&stmt.where_clause, s),
        3 => null_safe_stmt(stmt, s),
        4 => !where_has_string_lit(stmt),
        5 => select_items_typed(&stmt.select_items, s),
        6 => stmt.limit.is_some(),
        7 => stmt.effect_decl.is_some(),
        8 => stmt.version_const.is_some(),
        9 => linear_enforced(stmt),
        10 => epistemic_consistent_stmt(stmt),
        _ => false,
    }
}

fn safety_level_to_int(l: SafetyLevel) -> u8 {
    l as u8
}

/// Public wrapper around `check_level` for the vclt-gate binary and tests.
/// Returns `true` if the statement satisfies level `n` against `schema`.
/// Level 0 always passes; levels > 10 always fail (guard for future extension).
pub fn check_level_n(n: u8, stmt: &Statement, schema: &OctadSchema) -> bool {
    check_level(n, stmt, schema)
}

/// Human name for safety level `n` (matches the `SafetyLevel` enum tag and
/// the `levels[].name` field in the vclt-gate JSON response).
pub fn level_name(n: u8) -> &'static str {
    match n {
        0 => "ParseSafe",
        1 => "SchemaBound",
        2 => "TypeCompat",
        3 => "NullSafe",
        4 => "InjectionProof",
        5 => "ResultTyped",
        6 => "CardinalitySafe",
        7 => "EffectTracked",
        8 => "TemporalSafe",
        9 => "LinearSafe",
        10 => "EpistemicSafe",
        _ => "Unknown",
    }
}

/// Faithful port of `Checker.certifiedLevel`:
/// `certifyAt … (requestedLevel stmt)` is `Just` iff every
/// `checkLevel1 .. checkLevel⟨k⟩` accepts (L0 unconditional, k =
/// `safetyLevelToInt (requestedLevel stmt)`); then the result is
/// `safetyLevelToInt (requestedLevel stmt)` as an `Int`, else `-1`.
///
/// This is the recompute-tier verdict. A consumer compares it to the
/// producer's claimed level; equality means the consumer has
/// independently re-established the corpus-proved safety predicate
/// (`checkLevelNSound`, machine-checked once in the corpus).
pub fn certified_level(stmt: &Statement, schema: &OctadSchema) -> i64 {
    let k = safety_level_to_int(stmt.requested_level);
    let mut lvl = 1u8;
    while lvl <= k {
        if !check_level(lvl, stmt, schema) {
            return -1;
        }
        lvl = lvl.saturating_add(1);
    }
    i64::from(k)
}
