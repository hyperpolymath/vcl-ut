// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Total, panic-free recursive-descent parser for the VCL-total
//! relational core. Every path returns `Result`; cursor reads via
//! `slice::get` and advances via `saturating_add`.
//!
//! SCOPE (P5a first slice, #25): `SELECT … FROM … [WHERE] [GROUP BY]
//! [HAVING] [ORDER BY] [LIMIT] [OFFSET]` with the full expression
//! grammar (literals, params, `*`, fields, aggregates, comparisons,
//! AND/OR/NOT, parenthesised sub-expressions, scalar sub-queries). The
//! VCL-total extension clauses (PROOF / EFFECTS / AT VERSION /
//! CONSUME|USAGE / EPISTEMIC) and modal `KNOWS/BELIEVES/ANNOUNCE`
//! expressions are *fail-closed*: a typed `Unsupported` error, never a
//! silently-wrong AST. Coverage iterates per the #25 roadmap.

use crate::ast::*;

/// A parse failure: human message + 0-based char offset (from the
/// token's span, or `None` at end of input).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub msg: String,
    pub at: Option<usize>,
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.at {
            Some(p) => write!(f, "parse error at char {p}: {}", self.msg),
            None => write!(f, "parse error at end of input: {}", self.msg),
        }
    }
}
impl std::error::Error for ParseError {}

use crate::lexer::{Spanned, Tok};

/// Maximum expression-nesting depth. The grammar is mutually recursive
/// (`parse_expr → … → parse_primary → parse_expr` for parens/aggregates/
/// sub-queries, and `parse_not → parse_not` for `NOT` chains), so an
/// adversarial input of thousands of nested `(` or `NOT` would otherwise
/// exhaust the native stack — a process abort (SIGABRT), which is NOT a
/// `panic!` (so the crate's `deny(clippy::panic)` cannot see it) and NOT a
/// typed `ParseError`, violating the total / fail-closed contract. Past
/// this bound the parser returns a typed error instead. 256 levels is far
/// beyond any real query yet leaves the stack comfortably bounded.
const MAX_EXPR_DEPTH: usize = 256;

struct P {
    toks: Vec<Spanned>,
    pos: usize,
    /// Current expression-nesting depth (see [`MAX_EXPR_DEPTH`]).
    depth: usize,
}

impl P {
    /// Enter one expression-nesting level; a typed error past the bound
    /// (so deep nesting fails closed, never overflows the stack).
    fn enter(&mut self) -> Result<(), ParseError> {
        self.depth = self.depth.saturating_add(1);
        if self.depth > MAX_EXPR_DEPTH {
            return self.err(format!(
                "expression nesting too deep (limit {MAX_EXPR_DEPTH})"
            ));
        }
        Ok(())
    }
    /// Leave one expression-nesting level (tracks actual stack depth, so a
    /// wide-but-shallow expression is not falsely rejected).
    fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|s| &s.tok)
    }
    fn at(&self) -> Option<usize> {
        self.toks.get(self.pos).map(|s| s.at)
    }
    fn bump(&mut self) {
        self.pos = self.pos.saturating_add(1);
    }
    fn err<T>(&self, msg: impl Into<String>) -> Result<T, ParseError> {
        Err(ParseError {
            msg: msg.into(),
            at: self.at(),
        })
    }
    fn unsupported<T>(&self, what: &str) -> Result<T, ParseError> {
        Err(ParseError {
            msg: format!(
                "{what} is not yet supported by the P5a parser slice \
                 (fail-closed; tracked in #25)"
            ),
            at: self.at(),
        })
    }
    /// Case-insensitive keyword test on the current token.
    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), Some(Tok::Word(w)) if w.eq_ignore_ascii_case(kw))
    }
    /// Consume a specific keyword or error.
    fn eat_kw(&mut self, kw: &str) -> Result<(), ParseError> {
        if self.is_kw(kw) {
            self.bump();
            Ok(())
        } else {
            self.err(format!("expected keyword `{kw}`"))
        }
    }
    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Sym(x)) if *x == s)
    }
    fn eat_sym(&mut self, s: &str) -> Result<(), ParseError> {
        if self.is_sym(s) {
            self.bump();
            Ok(())
        } else {
            self.err(format!("expected `{s}`"))
        }
    }
}

/// Parse a complete VCL-total query string into a [`Statement`].
pub fn parse(input: &str) -> Result<Statement, ParseError> {
    let toks = crate::lexer::lex(input).map_err(|e| ParseError {
        msg: e.msg,
        at: Some(e.at),
    })?;
    let mut p = P {
        toks,
        pos: 0,
        depth: 0,
    };
    let stmt = parse_statement(&mut p)?;
    if p.is_sym(";") {
        p.bump();
    }
    if p.peek().is_some() {
        return p.err("trailing tokens after statement");
    }
    Ok(stmt)
}

/// Parse a complete VCL-total *operation* — the superset entry point. A
/// leading `MERGE`/`SPLIT`/`NORMALISE` keyword selects the S2 consonance
/// [`Transition`] arm (`VclOp::Transit`); any other leading verb is a
/// relational [`Statement`] (`VclOp::Query`). `parse` above is the
/// query-only view (it fail-closes on the transition verbs, unchanged);
/// `parse_op` is what the trusted gate routes through so a transition
/// reaches `decider::certified_transition_level`, NEVER the `Statement`
/// certifier.
pub fn parse_op(input: &str) -> Result<VclOp, ParseError> {
    let toks = crate::lexer::lex(input).map_err(|e| ParseError {
        msg: e.msg,
        at: Some(e.at),
    })?;
    let mut p = P {
        toks,
        pos: 0,
        depth: 0,
    };
    let op = if p.is_kw("MERGE") || p.is_kw("SPLIT") || p.is_kw("NORMALISE") {
        VclOp::Transit(parse_transition(&mut p)?)
    } else {
        VclOp::Query(Box::new(parse_statement(&mut p)?))
    };
    if p.is_sym(";") {
        p.bump();
    }
    if p.peek().is_some() {
        return p.err("trailing tokens after operation");
    }
    Ok(op)
}

/// Parse one consonance transition. The requested level is fixed at
/// `InjectionProof` (4) — the ceiling the S2 certificate establishes
/// (`Transition.idr::certifiedTransitionLevel`); there is no L5+ ladder for
/// a transition (no result set). NORMALISE REQUIRES an explicit
/// justification clause (fail-closed if absent) — an unjustified normalise
/// is unrepresentable, mirroring the Idris type.
fn parse_transition(p: &mut P) -> Result<Transition, ParseError> {
    if p.is_kw("MERGE") {
        p.bump();
        let left = parse_subject(p)?;
        let right = parse_subject(p)?;
        p.eat_kw("INTO")?;
        let into = parse_subject(p)?;
        let evidence = parse_opt_where(p)?;
        Ok(Transition::Merge(
            left,
            right,
            into,
            evidence,
            SafetyLevel::InjectionProof,
        ))
    } else if p.is_kw("SPLIT") {
        p.bump();
        let from = parse_subject(p)?;
        p.eat_kw("INTO")?;
        let out_l = parse_subject(p)?;
        let out_r = parse_subject(p)?;
        let evidence = parse_opt_where(p)?;
        Ok(Transition::Split(
            from,
            out_l,
            out_r,
            evidence,
            SafetyLevel::InjectionProof,
        ))
    } else {
        p.eat_kw("NORMALISE")?;
        let subject = parse_subject(p)?;
        let justification = parse_repair(p)?;
        Ok(Transition::Normalise(
            subject,
            justification,
            SafetyLevel::InjectionProof,
        ))
    }
}

/// A subject identity handle: a bareword or a `'quoted'` string (same
/// surface as a source argument, but a distinct AST node — identity, not
/// location).
fn parse_subject(p: &mut P) -> Result<SubjectRef, ParseError> {
    match p.peek() {
        Some(Tok::Str(s)) => {
            let v = s.clone();
            p.bump();
            Ok(SubjectRef(v))
        }
        Some(Tok::Word(w)) => {
            let v = w.clone();
            p.bump();
            Ok(SubjectRef(v))
        }
        _ => p.err("expected a subject identity handle (word or 'string')"),
    }
}

/// An optional `WHERE <expr>` evidence clause on MERGE/SPLIT.
fn parse_opt_where(p: &mut P) -> Result<Option<Expr>, ParseError> {
    if p.is_kw("WHERE") {
        p.bump();
        Ok(Some(parse_expr(p)?))
    } else {
        Ok(None)
    }
}

/// The NORMALISE repair justification:
/// `FROM AUTHORITATIVE <modality>` | `MERGE MODALITIES` | `USER RESOLVE`.
fn parse_repair(p: &mut P) -> Result<RepairJustification, ParseError> {
    if p.is_kw("FROM") {
        p.bump();
        p.eat_kw("AUTHORITATIVE")?;
        let m = parse_modality_kw(p)?;
        Ok(RepairJustification::FromAuthoritative(m))
    } else if p.is_kw("MERGE") {
        p.bump();
        p.eat_kw("MODALITIES")?;
        Ok(RepairJustification::MergeModalities)
    } else if p.is_kw("USER") {
        p.bump();
        p.eat_kw("RESOLVE")?;
        Ok(RepairJustification::UserResolve)
    } else {
        p.err(
            "NORMALISE requires a repair justification \
             (FROM AUTHORITATIVE <modality> | MERGE MODALITIES | USER RESOLVE)",
        )
    }
}

fn parse_modality_kw(p: &mut P) -> Result<Modality, ParseError> {
    match peek_modality(p) {
        Some(m) => {
            p.bump();
            Ok(m)
        }
        None => p.err("expected a modality (GRAPH|VECTOR|TENSOR|SEMANTIC|DOCUMENT|TEMPORAL|PROVENANCE|SPATIAL)"),
    }
}

fn parse_statement(p: &mut P) -> Result<Statement, ParseError> {
    // VCL consonance verb (S1). The read verbs (SELECT legacy / INSPECT /
    // VERIFY) and the promoted mutating verbs (ASSERT / DECLARE / RETRACT) all
    // parse as a tag over the same relational body. MERGE / SPLIT / NORMALISE
    // are deliberately NOT accepted, so they fail-closed (their semantics are
    // S2, multi-subject / result-less).
    let verb = if p.is_kw("INSPECT") {
        p.bump();
        Verb::Inspect
    } else if p.is_kw("VERIFY") {
        p.bump();
        Verb::Verify
    } else if p.is_kw("ASSERT") {
        p.bump();
        Verb::Assert
    } else if p.is_kw("DECLARE") {
        p.bump();
        Verb::Declare
    } else if p.is_kw("RETRACT") {
        p.bump();
        Verb::Retract
    } else {
        p.eat_kw("SELECT")?;
        Verb::Select
    };
    let select_items = parse_select_items(p)?;
    p.eat_kw("FROM")?;
    let source = parse_source(p)?;

    let mut where_clause = None;
    if p.is_kw("WHERE") {
        p.bump();
        where_clause = Some(parse_expr(p)?);
    }

    let mut group_by = Vec::new();
    if p.is_kw("GROUP") {
        p.bump();
        p.eat_kw("BY")?;
        group_by = parse_field_list(p)?;
    }

    let mut having = None;
    if p.is_kw("HAVING") {
        p.bump();
        having = Some(parse_expr(p)?);
    }

    let mut order_by = Vec::new();
    if p.is_kw("ORDER") {
        p.bump();
        p.eat_kw("BY")?;
        order_by = parse_order_list(p)?;
    }

    let mut limit = None;
    if p.is_kw("LIMIT") {
        p.bump();
        limit = Some(parse_u64(p)?);
    }
    let mut offset = None;
    if p.is_kw("OFFSET") {
        p.bump();
        offset = Some(parse_u64(p)?);
    }

    // Fail-closed on the not-yet-covered extension clauses.
    for kw in ["PROOF", "EFFECTS", "AT", "CONSUME", "USAGE", "EPISTEMIC"] {
        if p.is_kw(kw) {
            return p.unsupported(&format!("the `{kw}` clause"));
        }
    }

    let mut stmt = Statement {
        select_items,
        source,
        where_clause,
        group_by,
        having,
        order_by,
        limit,
        offset,
        proof_clause: None,
        effect_decl: None,
        version_const: None,
        linear_annot: None,
        epistemic_clause: None,
        requested_level: SafetyLevel::ParseSafe,
        verb,
    };
    stmt.requested_level = infer_requested_level(&stmt);
    Ok(stmt)
}

/// P5a requested-level policy (DOCUMENTED, conservative — NOT a proven
/// fact). The certifier checks *up to* this level; we pick the highest
/// feature-implied level present, with a relational base. Authoritative
/// reconciliation with the ReScript bridge's inference is a later #25
/// iteration. Until then this is the parser's stated intent only.
fn infer_requested_level(s: &Statement) -> SafetyLevel {
    if s.epistemic_clause.is_some() {
        SafetyLevel::EpistemicSafe
    } else if s.linear_annot.is_some() {
        SafetyLevel::LinearSafe
    } else if s.version_const.is_some() {
        SafetyLevel::TemporalSafe
    } else if s.effect_decl.is_some() {
        SafetyLevel::EffectTracked
    } else if s.limit.is_some() {
        SafetyLevel::CardinalitySafe
    } else if s.where_clause.is_some() || s.having.is_some() {
        // A predicate present ⇒ at least injection-safety is wanted.
        SafetyLevel::InjectionProof
    } else {
        SafetyLevel::SchemaBound
    }
}

fn parse_select_items(p: &mut P) -> Result<Vec<SelectItem>, ParseError> {
    let mut items = Vec::new();
    loop {
        items.push(parse_select_item(p)?);
        if p.is_sym(",") {
            p.bump();
            continue;
        }
        break;
    }
    Ok(items)
}

fn parse_select_item(p: &mut P) -> Result<SelectItem, ParseError> {
    for kw in ["KNOWS", "BELIEVES", "ANNOUNCE", "COMMON"] {
        if p.is_kw(kw) {
            return p.unsupported("modal/epistemic expressions");
        }
    }
    if p.is_sym("*") {
        p.bump();
        return Ok(SelectItem::Star);
    }
    if let Some(agg) = peek_agg(p) {
        p.bump();
        p.eat_sym("(")?;
        let e = if p.is_sym("*") {
            p.bump();
            Expr::Star
        } else {
            parse_expr(p)?
        };
        p.eat_sym(")")?;
        return Ok(SelectItem::Aggregate(agg, e));
    }
    if let Some(m) = peek_modality(p) {
        // `MODALITY.field` => field item; bare `MODALITY` => whole modality.
        p.bump();
        if p.is_sym(".") {
            p.bump();
            let field_name = parse_ident(p)?;
            return Ok(SelectItem::Field(FieldRef {
                modality: m,
                field_name,
            }));
        }
        return Ok(SelectItem::Modality(m));
    }
    p.err("expected a SELECT item (`*`, MODALITY[.field], or AGG(expr))")
}

fn parse_source(p: &mut P) -> Result<Source, ParseError> {
    // `OCTAD`/`HEXAD <id>`, `FEDERATION <pattern>`, `STORE <id>`.
    // OCTAD/HEXAD both accepted (grammar comment vs constructor name
    // disagree); reconciled with the ReScript bridge in a later slice.
    if p.is_kw("OCTAD") || p.is_kw("HEXAD") {
        p.bump();
        return Ok(Source::Octad(parse_source_arg(p)?));
    }
    if p.is_kw("FEDERATION") {
        p.bump();
        return Ok(Source::Federation(parse_source_arg(p)?));
    }
    if p.is_kw("STORE") {
        p.bump();
        return Ok(Source::Store(parse_source_arg(p)?));
    }
    p.err("expected FROM source (OCTAD|HEXAD|FEDERATION|STORE <id>)")
}

fn parse_source_arg(p: &mut P) -> Result<String, ParseError> {
    match p.peek() {
        Some(Tok::Str(s)) => {
            let v = s.clone();
            p.bump();
            Ok(v)
        }
        Some(Tok::Word(w)) => {
            let v = w.clone();
            p.bump();
            Ok(v)
        }
        _ => p.err("expected a source identifier (word or 'string')"),
    }
}

fn parse_field_list(p: &mut P) -> Result<Vec<FieldRef>, ParseError> {
    let mut fields = Vec::new();
    loop {
        fields.push(parse_field_ref(p)?);
        if p.is_sym(",") {
            p.bump();
            continue;
        }
        break;
    }
    Ok(fields)
}

fn parse_order_list(p: &mut P) -> Result<Vec<(FieldRef, bool)>, ParseError> {
    let mut out = Vec::new();
    loop {
        let f = parse_field_ref(p)?;
        let asc = if p.is_kw("DESC") {
            p.bump();
            false
        } else {
            if p.is_kw("ASC") {
                p.bump();
            }
            true
        };
        out.push((f, asc));
        if p.is_sym(",") {
            p.bump();
            continue;
        }
        break;
    }
    Ok(out)
}

fn parse_field_ref(p: &mut P) -> Result<FieldRef, ParseError> {
    let m = peek_modality(p)
        .ok_or(())
        .or_else(|()| p.err("expected MODALITY in field reference"))?;
    p.bump();
    p.eat_sym(".")?;
    let field_name = parse_ident(p)?;
    Ok(FieldRef {
        modality: m,
        field_name,
    })
}

// ── Expressions: OR < AND < NOT < comparison < primary ────────────────

fn parse_expr(p: &mut P) -> Result<Expr, ParseError> {
    // Depth-guarded: every parenthesised / aggregate / sub-query descent
    // re-enters here, so this is the chokepoint that bounds native-stack
    // growth (paired with `parse_not`'s own guard for `NOT` chains).
    p.enter()?;
    let r = parse_or(p);
    p.leave();
    r
}

fn parse_or(p: &mut P) -> Result<Expr, ParseError> {
    let mut lhs = parse_and(p)?;
    while p.is_kw("OR") {
        p.bump();
        let rhs = parse_and(p)?;
        lhs = Expr::Logic(LogicOp::Or, Box::new(lhs), Some(Box::new(rhs)));
    }
    Ok(lhs)
}

fn parse_and(p: &mut P) -> Result<Expr, ParseError> {
    let mut lhs = parse_not(p)?;
    while p.is_kw("AND") {
        p.bump();
        let rhs = parse_not(p)?;
        lhs = Expr::Logic(LogicOp::And, Box::new(lhs), Some(Box::new(rhs)));
    }
    Ok(lhs)
}

fn parse_not(p: &mut P) -> Result<Expr, ParseError> {
    if p.is_kw("NOT") {
        p.bump();
        // `NOT` self-recurses without re-entering `parse_expr`, so it needs
        // its own depth guard or a `NOT NOT NOT …` chain overflows the stack.
        p.enter()?;
        let inner = parse_not(p);
        p.leave();
        return Ok(Expr::Logic(LogicOp::Not, Box::new(inner?), None));
    }
    parse_comparison(p)
}

fn parse_comparison(p: &mut P) -> Result<Expr, ParseError> {
    let lhs = parse_primary(p)?;
    let op = match p.peek() {
        Some(Tok::Sym("=")) => Some(CompOp::Eq),
        Some(Tok::Sym("!=")) => Some(CompOp::NotEq),
        Some(Tok::Sym("<")) => Some(CompOp::Lt),
        Some(Tok::Sym(">")) => Some(CompOp::Gt),
        Some(Tok::Sym("<=")) => Some(CompOp::LtEq),
        Some(Tok::Sym(">=")) => Some(CompOp::GtEq),
        Some(Tok::Word(w)) if w.eq_ignore_ascii_case("LIKE") => Some(CompOp::Like),
        Some(Tok::Word(w)) if w.eq_ignore_ascii_case("IN") => Some(CompOp::In),
        _ => None,
    };
    match op {
        None => Ok(lhs),
        Some(o) => {
            p.bump();
            let rhs = parse_primary(p)?;
            Ok(Expr::Compare(o, Box::new(lhs), Box::new(rhs)))
        }
    }
}

fn parse_primary(p: &mut P) -> Result<Expr, ParseError> {
    // Modal expression nodes are fail-closed for the P5a slice.
    for kw in ["KNOWS", "BELIEVES", "ANNOUNCE", "COMMON"] {
        if p.is_kw(kw) {
            return p.unsupported("modal/epistemic expressions");
        }
    }
    match p.peek() {
        Some(Tok::Sym("*")) => {
            p.bump();
            Ok(Expr::Star)
        }
        Some(Tok::Sym("(")) => {
            p.bump();
            // `(SELECT …)` => scalar sub-query; else parenthesised expr.
            if p.is_kw("SELECT") {
                let sub = parse_statement(p)?;
                p.eat_sym(")")?;
                Ok(Expr::Subquery(Box::new(sub)))
            } else {
                let e = parse_expr(p)?;
                p.eat_sym(")")?;
                Ok(e)
            }
        }
        Some(Tok::Str(s)) => {
            let v = s.clone();
            p.bump();
            Ok(Expr::Literal(Literal::Str(v)))
        }
        Some(Tok::Int(n)) => {
            let v = *n;
            p.bump();
            Ok(Expr::Literal(Literal::Int(v)))
        }
        Some(Tok::Float(f)) => {
            let v = *f;
            p.bump();
            Ok(Expr::Literal(Literal::Float(v)))
        }
        Some(Tok::Param(name)) => {
            let v = name.clone();
            p.bump();
            Ok(Expr::Param(v))
        }
        Some(Tok::Word(w)) => {
            // Keyword literals first.
            if w.eq_ignore_ascii_case("TRUE") {
                p.bump();
                return Ok(Expr::Literal(Literal::Bool(true)));
            }
            if w.eq_ignore_ascii_case("FALSE") {
                p.bump();
                return Ok(Expr::Literal(Literal::Bool(false)));
            }
            if w.eq_ignore_ascii_case("NULL") {
                p.bump();
                return Ok(Expr::Literal(Literal::Null));
            }
            if let Some(agg) = peek_agg(p) {
                p.bump();
                p.eat_sym("(")?;
                let e = if p.is_sym("*") {
                    p.bump();
                    Expr::Star
                } else {
                    parse_expr(p)?
                };
                p.eat_sym(")")?;
                return Ok(Expr::Aggregate(agg, Box::new(e)));
            }
            if peek_modality(p).is_some() {
                return Ok(Expr::Field(parse_field_ref(p)?));
            }
            // Bare identifier not preceded by $ — treat as an unqualified
            // name parameter (schema-unresolved; fails SchemaBound at L1 if
            // the schema is strict, but is not an injection concern).
            let name = w.clone();
            p.bump();
            Ok(Expr::Param(name))
        }
        _ => p.err("expected an expression"),
    }
}

// ── Token classifiers ─────────────────────────────────────────────────

fn peek_modality(p: &P) -> Option<Modality> {
    if let Some(Tok::Word(w)) = p.peek() {
        let u = w.to_ascii_uppercase();
        return match u.as_str() {
            "GRAPH" => Some(Modality::Graph),
            "VECTOR" => Some(Modality::Vector),
            "TENSOR" => Some(Modality::Tensor),
            "SEMANTIC" => Some(Modality::Semantic),
            "DOCUMENT" => Some(Modality::Document),
            "TEMPORAL" => Some(Modality::Temporal),
            "PROVENANCE" => Some(Modality::Provenance),
            "SPATIAL" => Some(Modality::Spatial),
            _ => None,
        };
    }
    None
}

fn peek_agg(p: &P) -> Option<AggFunc> {
    if let Some(Tok::Word(w)) = p.peek() {
        let u = w.to_ascii_uppercase();
        return match u.as_str() {
            "COUNT" => Some(AggFunc::Count),
            "SUM" => Some(AggFunc::Sum),
            "AVG" => Some(AggFunc::Avg),
            "MIN" => Some(AggFunc::Min),
            "MAX" => Some(AggFunc::Max),
            _ => None,
        };
    }
    None
}

fn parse_ident(p: &mut P) -> Result<String, ParseError> {
    match p.peek() {
        Some(Tok::Word(w)) => {
            let v = w.clone();
            p.bump();
            Ok(v)
        }
        _ => p.err("expected an identifier"),
    }
}

fn parse_u64(p: &mut P) -> Result<u64, ParseError> {
    match p.peek() {
        Some(Tok::Int(n)) if *n >= 0 => {
            let v = *n as u64;
            p.bump();
            Ok(v)
        }
        Some(Tok::Int(_)) => p.err("expected a non-negative integer"),
        _ => p.err("expected an integer"),
    }
}
