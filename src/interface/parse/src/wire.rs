// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! P5b (#25): the C-ABI marshalling codec — `Statement` <-> a
//! deterministic, versioned, length-prefixed binary TLV. Normative
//! spec: `WIRE-FORMAT.adoc`. The P5b-step-2 Idris2 decoder must accept
//! this identical byte stream into `Grammar.idr`'s `Statement`.
//!
//! Same SPARK-grade posture as the parser (crate lint-set in lib.rs):
//! `to_wire` is total + deterministic; `from_wire` is **total** —
//! bounds-checked, no panic, no unbounded pre-allocation from untrusted
//! counts, every malformed input a typed [`WireError`].

use crate::ast::*;
use crate::schema::{FieldDef, ModalitySchema, OctadSchema, VqlType};

const MAGIC: [u8; 4] = *b"VCLW";
/// Distinct magic for the P5c `OctadSchema` stream so a schema/statement
/// mix-up is a hard `BadMagic`, never a silent mis-parse.
const SCHEMA_MAGIC: [u8; 4] = *b"VCLS";
const VERSION: u16 = 1;

/// Total decode failure (never a panic).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireError {
    BadMagic,
    BadVersion(u16),
    Truncated,
    BadTag {
        ty: &'static str,
        tag: u8,
    },
    BadBool(u8),
    BadUtf8,
    /// A `usize` count/length that does not fit the platform or exceeds
    /// the remaining input (anti-OOM: counts are validated, never
    /// pre-allocated against).
    LengthOverflow,
    TrailingBytes,
}

impl core::fmt::Display for WireError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            WireError::BadMagic => write!(f, "bad magic (not a VCLW stream)"),
            WireError::BadVersion(v) => write!(f, "unsupported wire version {v}"),
            WireError::Truncated => write!(f, "truncated input"),
            WireError::BadTag { ty, tag } => {
                write!(f, "bad {ty} discriminant {tag}")
            }
            WireError::BadBool(b) => write!(f, "bad bool byte {b}"),
            WireError::BadUtf8 => write!(f, "invalid UTF-8 in string"),
            WireError::LengthOverflow => write!(f, "length/count overflow"),
            WireError::TrailingBytes => write!(f, "trailing bytes after statement"),
        }
    }
}
impl std::error::Error for WireError {}

// ── Encoder (deterministic; canonical one-byte-string-per-value) ──────

/// Serialise a `Statement` to the v1 wire format. Total.
pub fn to_wire(s: &Statement) -> Vec<u8> {
    let mut o = Vec::new();
    o.extend_from_slice(&MAGIC);
    o.extend_from_slice(&VERSION.to_le_bytes());
    enc_stmt(s, &mut o);
    o
}

fn put_u8(o: &mut Vec<u8>, b: u8) {
    o.push(b);
}
fn put_bool(o: &mut Vec<u8>, b: bool) {
    o.push(u8::from(b));
}
fn put_u32(o: &mut Vec<u8>, n: u32) {
    o.extend_from_slice(&n.to_le_bytes());
}
fn put_u64(o: &mut Vec<u8>, n: u64) {
    o.extend_from_slice(&n.to_le_bytes());
}
fn put_i64(o: &mut Vec<u8>, n: i64) {
    o.extend_from_slice(&n.to_le_bytes());
}
fn put_f64(o: &mut Vec<u8>, n: f64) {
    o.extend_from_slice(&n.to_bits().to_le_bytes());
}
fn put_str(o: &mut Vec<u8>, s: &str) {
    // A string longer than u32::MAX bytes is not representable; clamp by
    // construction is impossible, so length is encoded saturating and
    // the (astronomically unreachable) excess is truncated rather than
    // panicking. Documented limit; never hit by real queries.
    let bytes = s.as_bytes();
    let n = u32::try_from(bytes.len()).unwrap_or(u32::MAX);
    put_u32(o, n);
    match bytes.get(..n as usize) {
        Some(slice) => o.extend_from_slice(slice),
        None => o.extend_from_slice(bytes),
    }
}
fn put_opt<T>(o: &mut Vec<u8>, v: &Option<T>, f: impl FnOnce(&T, &mut Vec<u8>)) {
    match v {
        None => o.push(0),
        Some(x) => {
            o.push(1);
            f(x, o);
        }
    }
}
fn put_len(o: &mut Vec<u8>, len: usize) {
    put_u32(o, u32::try_from(len).unwrap_or(u32::MAX));
}

fn enc_modality(m: &Modality, o: &mut Vec<u8>) {
    put_u8(
        o,
        match m {
            Modality::Graph => 0,
            Modality::Vector => 1,
            Modality::Tensor => 2,
            Modality::Semantic => 3,
            Modality::Document => 4,
            Modality::Temporal => 5,
            Modality::Provenance => 6,
            Modality::Spatial => 7,
        },
    );
}

fn enc_agent(a: &Agent, o: &mut Vec<u8>) {
    match a {
        Agent::Engine => put_u8(o, 0),
        Agent::Prover(n) => {
            put_u8(o, 1);
            put_str(o, n);
        }
        Agent::Validator => put_u8(o, 2),
        Agent::User(n) => {
            put_u8(o, 3);
            put_str(o, n);
        }
        Agent::Federation => put_u8(o, 4),
    }
}

fn enc_fieldref(fr: &FieldRef, o: &mut Vec<u8>) {
    enc_modality(&fr.modality, o);
    put_str(o, &fr.field_name);
}

fn enc_literal(l: &Literal, o: &mut Vec<u8>) {
    match l {
        Literal::Str(s) => {
            put_u8(o, 0);
            put_str(o, s);
        }
        Literal::Int(n) => {
            put_u8(o, 1);
            put_i64(o, *n);
        }
        Literal::Float(x) => {
            put_u8(o, 2);
            put_f64(o, *x);
        }
        Literal::Bool(b) => {
            put_u8(o, 3);
            put_bool(o, *b);
        }
        Literal::Null => put_u8(o, 4),
        Literal::Vector(v) => {
            put_u8(o, 5);
            put_len(o, v.len());
            for x in v {
                put_f64(o, *x);
            }
        }
    }
}

fn comp_tag(c: CompOp) -> u8 {
    match c {
        CompOp::Eq => 0,
        CompOp::NotEq => 1,
        CompOp::Lt => 2,
        CompOp::Gt => 3,
        CompOp::LtEq => 4,
        CompOp::GtEq => 5,
        CompOp::Like => 6,
        CompOp::In => 7,
    }
}
fn logic_tag(l: LogicOp) -> u8 {
    match l {
        LogicOp::And => 0,
        LogicOp::Or => 1,
        LogicOp::Not => 2,
    }
}
fn agg_tag(a: AggFunc) -> u8 {
    match a {
        AggFunc::Count => 0,
        AggFunc::Sum => 1,
        AggFunc::Avg => 2,
        AggFunc::Min => 3,
        AggFunc::Max => 4,
    }
}
fn epi_tag(e: EpistemicOp) -> u8 {
    match e {
        EpistemicOp::Knows => 0,
        EpistemicOp::Believes => 1,
        EpistemicOp::CommonKnowledge => 2,
    }
}

fn enc_expr(e: &Expr, o: &mut Vec<u8>) {
    match e {
        Expr::Field(fr) => {
            put_u8(o, 0);
            enc_fieldref(fr, o);
        }
        Expr::Literal(l) => {
            put_u8(o, 1);
            enc_literal(l, o);
        }
        Expr::Compare(c, a, b) => {
            put_u8(o, 2);
            put_u8(o, comp_tag(*c));
            enc_expr(a, o);
            enc_expr(b, o);
        }
        Expr::Logic(l, a, b) => {
            put_u8(o, 3);
            put_u8(o, logic_tag(*l));
            enc_expr(a, o);
            put_opt(o, b, |x, oo| enc_expr(x, oo));
        }
        Expr::Aggregate(a, x) => {
            put_u8(o, 4);
            put_u8(o, agg_tag(*a));
            enc_expr(x, o);
        }
        Expr::Param(n) => {
            put_u8(o, 5);
            put_str(o, n);
        }
        Expr::Star => put_u8(o, 6),
        Expr::Subquery(s) => {
            put_u8(o, 7);
            enc_stmt(s, o);
        }
        Expr::Epistemic(op, ag, x) => {
            put_u8(o, 8);
            put_u8(o, epi_tag(*op));
            enc_agent(ag, o);
            enc_expr(x, o);
        }
        Expr::Announce(ag, p, b) => {
            put_u8(o, 9);
            enc_agent(ag, o);
            enc_expr(p, o);
            enc_expr(b, o);
        }
    }
}

fn enc_select_item(si: &SelectItem, o: &mut Vec<u8>) {
    match si {
        SelectItem::Field(fr) => {
            put_u8(o, 0);
            enc_fieldref(fr, o);
        }
        SelectItem::Modality(m) => {
            put_u8(o, 1);
            enc_modality(m, o);
        }
        SelectItem::Aggregate(a, e) => {
            put_u8(o, 2);
            put_u8(o, agg_tag(*a));
            enc_expr(e, o);
        }
        SelectItem::Star => put_u8(o, 3),
    }
}

fn enc_source(s: &Source, o: &mut Vec<u8>) {
    match s {
        Source::Octad(x) => {
            put_u8(o, 0);
            put_str(o, x);
        }
        Source::Federation(x) => {
            put_u8(o, 1);
            put_str(o, x);
        }
        Source::Store(x) => {
            put_u8(o, 2);
            put_str(o, x);
        }
    }
}

fn enc_proof(p: &ProofClause, o: &mut Vec<u8>) {
    match p {
        ProofClause::Attached => put_u8(o, 0),
        ProofClause::Witness(s) => {
            put_u8(o, 1);
            put_str(o, s);
        }
        ProofClause::Assert(e) => {
            put_u8(o, 2);
            enc_expr(e, o);
        }
    }
}

fn enc_effect(e: &EffectDecl, o: &mut Vec<u8>) {
    put_u8(
        o,
        match e {
            EffectDecl::Read => 0,
            EffectDecl::Write => 1,
            EffectDecl::ReadWrite => 2,
            EffectDecl::Consume => 3,
        },
    );
}

fn enc_version(v: &VersionConstraint, o: &mut Vec<u8>) {
    match v {
        VersionConstraint::Latest => put_u8(o, 0),
        VersionConstraint::AtLeast(n) => {
            put_u8(o, 1);
            put_u64(o, *n);
        }
        VersionConstraint::Exact(n) => {
            put_u8(o, 2);
            put_u64(o, *n);
        }
        VersionConstraint::Range(a, b) => {
            put_u8(o, 3);
            put_u64(o, *a);
            put_u64(o, *b);
        }
    }
}

fn enc_linear(l: &LinearAnnotation, o: &mut Vec<u8>) {
    match l {
        LinearAnnotation::Unlimited => put_u8(o, 0),
        LinearAnnotation::UseOnce => put_u8(o, 1),
        LinearAnnotation::Bounded(n) => {
            put_u8(o, 2);
            put_u64(o, *n);
        }
    }
}

fn enc_epi_req(r: &EpistemicRequirement, o: &mut Vec<u8>) {
    match r {
        EpistemicRequirement::Knows(a, e) => {
            put_u8(o, 0);
            enc_agent(a, o);
            enc_expr(e, o);
        }
        EpistemicRequirement::Believes(a, e) => {
            put_u8(o, 1);
            enc_agent(a, o);
            enc_expr(e, o);
        }
        EpistemicRequirement::Common(e) => {
            put_u8(o, 2);
            enc_expr(e, o);
        }
        EpistemicRequirement::Entails(a, b, e) => {
            put_u8(o, 3);
            enc_agent(a, o);
            enc_agent(b, o);
            enc_expr(e, o);
        }
    }
}

fn enc_epi_clause(c: &EpistemicClause, o: &mut Vec<u8>) {
    put_len(o, c.agents.len());
    for a in &c.agents {
        enc_agent(a, o);
    }
    put_len(o, c.requirements.len());
    for r in &c.requirements {
        enc_epi_req(r, o);
    }
}

fn safety_tag(s: SafetyLevel) -> u8 {
    s as u8
}

fn enc_stmt(s: &Statement, o: &mut Vec<u8>) {
    put_len(o, s.select_items.len());
    for si in &s.select_items {
        enc_select_item(si, o);
    }
    enc_source(&s.source, o);
    put_opt(o, &s.where_clause, enc_expr);
    put_len(o, s.group_by.len());
    for fr in &s.group_by {
        enc_fieldref(fr, o);
    }
    put_opt(o, &s.having, enc_expr);
    put_len(o, s.order_by.len());
    for (fr, asc) in &s.order_by {
        enc_fieldref(fr, o);
        put_bool(o, *asc);
    }
    put_opt(o, &s.limit, |n, oo| put_u64(oo, *n));
    put_opt(o, &s.offset, |n, oo| put_u64(oo, *n));
    put_opt(o, &s.proof_clause, enc_proof);
    put_opt(o, &s.effect_decl, enc_effect);
    put_opt(o, &s.version_const, enc_version);
    put_opt(o, &s.linear_annot, enc_linear);
    put_opt(o, &s.epistemic_clause, enc_epi_clause);
    put_u8(o, safety_tag(s.requested_level));
}

// ── Decoder (total: bounds-checked, no panic, no untrusted pre-alloc) ─

struct D<'a> {
    b: &'a [u8],
    pos: usize,
}

impl<'a> D<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], WireError> {
        let end = self.pos.checked_add(n).ok_or(WireError::LengthOverflow)?;
        let slice = self.b.get(self.pos..end).ok_or(WireError::Truncated)?;
        self.pos = end;
        Ok(slice)
    }
    fn u8(&mut self) -> Result<u8, WireError> {
        Ok(*self.take(1)?.first().ok_or(WireError::Truncated)?)
    }
    fn boolean(&mut self) -> Result<bool, WireError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            x => Err(WireError::BadBool(x)),
        }
    }
    fn arr8(&mut self) -> Result<[u8; 8], WireError> {
        <[u8; 8]>::try_from(self.take(8)?).map_err(|_| WireError::Truncated)
    }
    fn u16(&mut self) -> Result<u16, WireError> {
        let s = self.take(2)?;
        let a = <[u8; 2]>::try_from(s).map_err(|_| WireError::Truncated)?;
        Ok(u16::from_le_bytes(a))
    }
    fn u32(&mut self) -> Result<u32, WireError> {
        let s = self.take(4)?;
        let a = <[u8; 4]>::try_from(s).map_err(|_| WireError::Truncated)?;
        Ok(u32::from_le_bytes(a))
    }
    fn u64(&mut self) -> Result<u64, WireError> {
        Ok(u64::from_le_bytes(self.arr8()?))
    }
    fn i64(&mut self) -> Result<i64, WireError> {
        Ok(i64::from_le_bytes(self.arr8()?))
    }
    fn f64(&mut self) -> Result<f64, WireError> {
        Ok(f64::from_bits(u64::from_le_bytes(self.arr8()?)))
    }
    /// A length/count: read u32, validate it fits the *remaining*
    /// input's worst case is the caller's job (each element does its
    /// own bounds-check on read); we only convert without overflow and
    /// never pre-allocate against it.
    fn count(&mut self) -> Result<usize, WireError> {
        usize::try_from(self.u32()?).map_err(|_| WireError::LengthOverflow)
    }
    fn string(&mut self) -> Result<String, WireError> {
        let n = self.count()?;
        let bytes = self.take(n)?;
        core::str::from_utf8(bytes)
            .map(str::to_owned)
            .map_err(|_| WireError::BadUtf8)
    }
    fn opt<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, WireError>,
    ) -> Result<Option<T>, WireError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(f(self)?)),
            x => Err(WireError::BadTag {
                ty: "option",
                tag: x,
            }),
        }
    }
    /// Decode `count` items by repeated bounds-checked reads. No
    /// pre-allocation from the untrusted count (anti-OOM): the vector
    /// can only grow as fast as input is actually consumed.
    fn vec<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, WireError>,
    ) -> Result<Vec<T>, WireError> {
        let n = self.count()?;
        let mut v = Vec::new();
        let mut i = 0usize;
        while i < n {
            v.push(f(self)?);
            i = i.saturating_add(1);
        }
        Ok(v)
    }
}

/// Decode a v1 wire stream into a `Statement`. Total.
pub fn from_wire(input: &[u8]) -> Result<Statement, WireError> {
    let mut d = D { b: input, pos: 0 };
    if d.take(4)? != MAGIC {
        return Err(WireError::BadMagic);
    }
    let ver = d.u16()?;
    if ver != VERSION {
        return Err(WireError::BadVersion(ver));
    }
    let s = dec_stmt(&mut d)?;
    if d.pos != d.b.len() {
        return Err(WireError::TrailingBytes);
    }
    Ok(s)
}

fn dec_modality(d: &mut D) -> Result<Modality, WireError> {
    match d.u8()? {
        0 => Ok(Modality::Graph),
        1 => Ok(Modality::Vector),
        2 => Ok(Modality::Tensor),
        3 => Ok(Modality::Semantic),
        4 => Ok(Modality::Document),
        5 => Ok(Modality::Temporal),
        6 => Ok(Modality::Provenance),
        7 => Ok(Modality::Spatial),
        t => Err(WireError::BadTag {
            ty: "Modality",
            tag: t,
        }),
    }
}

fn dec_agent(d: &mut D) -> Result<Agent, WireError> {
    match d.u8()? {
        0 => Ok(Agent::Engine),
        1 => Ok(Agent::Prover(d.string()?)),
        2 => Ok(Agent::Validator),
        3 => Ok(Agent::User(d.string()?)),
        4 => Ok(Agent::Federation),
        t => Err(WireError::BadTag {
            ty: "Agent",
            tag: t,
        }),
    }
}

fn dec_fieldref(d: &mut D) -> Result<FieldRef, WireError> {
    let modality = dec_modality(d)?;
    let field_name = d.string()?;
    Ok(FieldRef {
        modality,
        field_name,
    })
}

fn dec_literal(d: &mut D) -> Result<Literal, WireError> {
    match d.u8()? {
        0 => Ok(Literal::Str(d.string()?)),
        1 => Ok(Literal::Int(d.i64()?)),
        2 => Ok(Literal::Float(d.f64()?)),
        3 => Ok(Literal::Bool(d.boolean()?)),
        4 => Ok(Literal::Null),
        5 => Ok(Literal::Vector(d.vec(|dd| dd.f64())?)),
        t => Err(WireError::BadTag {
            ty: "Literal",
            tag: t,
        }),
    }
}

fn dec_comp(d: &mut D) -> Result<CompOp, WireError> {
    match d.u8()? {
        0 => Ok(CompOp::Eq),
        1 => Ok(CompOp::NotEq),
        2 => Ok(CompOp::Lt),
        3 => Ok(CompOp::Gt),
        4 => Ok(CompOp::LtEq),
        5 => Ok(CompOp::GtEq),
        6 => Ok(CompOp::Like),
        7 => Ok(CompOp::In),
        t => Err(WireError::BadTag {
            ty: "CompOp",
            tag: t,
        }),
    }
}
fn dec_logic(d: &mut D) -> Result<LogicOp, WireError> {
    match d.u8()? {
        0 => Ok(LogicOp::And),
        1 => Ok(LogicOp::Or),
        2 => Ok(LogicOp::Not),
        t => Err(WireError::BadTag {
            ty: "LogicOp",
            tag: t,
        }),
    }
}
fn dec_agg(d: &mut D) -> Result<AggFunc, WireError> {
    match d.u8()? {
        0 => Ok(AggFunc::Count),
        1 => Ok(AggFunc::Sum),
        2 => Ok(AggFunc::Avg),
        3 => Ok(AggFunc::Min),
        4 => Ok(AggFunc::Max),
        t => Err(WireError::BadTag {
            ty: "AggFunc",
            tag: t,
        }),
    }
}
fn dec_epi_op(d: &mut D) -> Result<EpistemicOp, WireError> {
    match d.u8()? {
        0 => Ok(EpistemicOp::Knows),
        1 => Ok(EpistemicOp::Believes),
        2 => Ok(EpistemicOp::CommonKnowledge),
        t => Err(WireError::BadTag {
            ty: "EpistemicOp",
            tag: t,
        }),
    }
}

fn dec_expr(d: &mut D) -> Result<Expr, WireError> {
    match d.u8()? {
        0 => Ok(Expr::Field(dec_fieldref(d)?)),
        1 => Ok(Expr::Literal(dec_literal(d)?)),
        2 => {
            let c = dec_comp(d)?;
            let a = Box::new(dec_expr(d)?);
            let b = Box::new(dec_expr(d)?);
            Ok(Expr::Compare(c, a, b))
        }
        3 => {
            let l = dec_logic(d)?;
            let a = Box::new(dec_expr(d)?);
            let b = d.opt(|dd| dec_expr(dd).map(Box::new))?;
            Ok(Expr::Logic(l, a, b))
        }
        4 => {
            let a = dec_agg(d)?;
            Ok(Expr::Aggregate(a, Box::new(dec_expr(d)?)))
        }
        5 => Ok(Expr::Param(d.string()?)),
        6 => Ok(Expr::Star),
        7 => Ok(Expr::Subquery(Box::new(dec_stmt(d)?))),
        8 => {
            let op = dec_epi_op(d)?;
            let ag = dec_agent(d)?;
            Ok(Expr::Epistemic(op, ag, Box::new(dec_expr(d)?)))
        }
        9 => {
            let ag = dec_agent(d)?;
            let p = Box::new(dec_expr(d)?);
            let b = Box::new(dec_expr(d)?);
            Ok(Expr::Announce(ag, p, b))
        }
        t => Err(WireError::BadTag { ty: "Expr", tag: t }),
    }
}

fn dec_select_item(d: &mut D) -> Result<SelectItem, WireError> {
    match d.u8()? {
        0 => Ok(SelectItem::Field(dec_fieldref(d)?)),
        1 => Ok(SelectItem::Modality(dec_modality(d)?)),
        2 => {
            let a = dec_agg(d)?;
            Ok(SelectItem::Aggregate(a, dec_expr(d)?))
        }
        3 => Ok(SelectItem::Star),
        t => Err(WireError::BadTag {
            ty: "SelectItem",
            tag: t,
        }),
    }
}

fn dec_source(d: &mut D) -> Result<Source, WireError> {
    match d.u8()? {
        0 => Ok(Source::Octad(d.string()?)),
        1 => Ok(Source::Federation(d.string()?)),
        2 => Ok(Source::Store(d.string()?)),
        t => Err(WireError::BadTag {
            ty: "Source",
            tag: t,
        }),
    }
}

fn dec_proof(d: &mut D) -> Result<ProofClause, WireError> {
    match d.u8()? {
        0 => Ok(ProofClause::Attached),
        1 => Ok(ProofClause::Witness(d.string()?)),
        2 => Ok(ProofClause::Assert(dec_expr(d)?)),
        t => Err(WireError::BadTag {
            ty: "ProofClause",
            tag: t,
        }),
    }
}

fn dec_effect(d: &mut D) -> Result<EffectDecl, WireError> {
    match d.u8()? {
        0 => Ok(EffectDecl::Read),
        1 => Ok(EffectDecl::Write),
        2 => Ok(EffectDecl::ReadWrite),
        3 => Ok(EffectDecl::Consume),
        t => Err(WireError::BadTag {
            ty: "EffectDecl",
            tag: t,
        }),
    }
}

fn dec_version(d: &mut D) -> Result<VersionConstraint, WireError> {
    match d.u8()? {
        0 => Ok(VersionConstraint::Latest),
        1 => Ok(VersionConstraint::AtLeast(d.u64()?)),
        2 => Ok(VersionConstraint::Exact(d.u64()?)),
        3 => {
            let a = d.u64()?;
            let b = d.u64()?;
            Ok(VersionConstraint::Range(a, b))
        }
        t => Err(WireError::BadTag {
            ty: "VersionConstraint",
            tag: t,
        }),
    }
}

fn dec_linear(d: &mut D) -> Result<LinearAnnotation, WireError> {
    match d.u8()? {
        0 => Ok(LinearAnnotation::Unlimited),
        1 => Ok(LinearAnnotation::UseOnce),
        2 => Ok(LinearAnnotation::Bounded(d.u64()?)),
        t => Err(WireError::BadTag {
            ty: "LinearAnnotation",
            tag: t,
        }),
    }
}

fn dec_epi_req(d: &mut D) -> Result<EpistemicRequirement, WireError> {
    match d.u8()? {
        0 => {
            let a = dec_agent(d)?;
            Ok(EpistemicRequirement::Knows(a, dec_expr(d)?))
        }
        1 => {
            let a = dec_agent(d)?;
            Ok(EpistemicRequirement::Believes(a, dec_expr(d)?))
        }
        2 => Ok(EpistemicRequirement::Common(dec_expr(d)?)),
        3 => {
            let a = dec_agent(d)?;
            let b = dec_agent(d)?;
            Ok(EpistemicRequirement::Entails(a, b, dec_expr(d)?))
        }
        t => Err(WireError::BadTag {
            ty: "EpistemicRequirement",
            tag: t,
        }),
    }
}

fn dec_epi_clause(d: &mut D) -> Result<EpistemicClause, WireError> {
    let agents = d.vec(dec_agent)?;
    let requirements = d.vec(dec_epi_req)?;
    Ok(EpistemicClause {
        agents,
        requirements,
    })
}

fn dec_safety(d: &mut D) -> Result<SafetyLevel, WireError> {
    match d.u8()? {
        0 => Ok(SafetyLevel::ParseSafe),
        1 => Ok(SafetyLevel::SchemaBound),
        2 => Ok(SafetyLevel::TypeCompat),
        3 => Ok(SafetyLevel::NullSafe),
        4 => Ok(SafetyLevel::InjectionProof),
        5 => Ok(SafetyLevel::ResultTyped),
        6 => Ok(SafetyLevel::CardinalitySafe),
        7 => Ok(SafetyLevel::EffectTracked),
        8 => Ok(SafetyLevel::TemporalSafe),
        9 => Ok(SafetyLevel::LinearSafe),
        10 => Ok(SafetyLevel::EpistemicSafe),
        t => Err(WireError::BadTag {
            ty: "SafetyLevel",
            tag: t,
        }),
    }
}

fn dec_stmt(d: &mut D) -> Result<Statement, WireError> {
    let select_items = d.vec(dec_select_item)?;
    let source = dec_source(d)?;
    let where_clause = d.opt(dec_expr)?;
    let group_by = d.vec(dec_fieldref)?;
    let having = d.opt(dec_expr)?;
    let order_by = d.vec(|dd| {
        let fr = dec_fieldref(dd)?;
        let asc = dd.boolean()?;
        Ok((fr, asc))
    })?;
    let limit = d.opt(|dd| dd.u64())?;
    let offset = d.opt(|dd| dd.u64())?;
    let proof_clause = d.opt(dec_proof)?;
    let effect_decl = d.opt(dec_effect)?;
    let version_const = d.opt(dec_version)?;
    let linear_annot = d.opt(dec_linear)?;
    let epistemic_clause = d.opt(dec_epi_clause)?;
    let requested_level = dec_safety(d)?;
    Ok(Statement {
        select_items,
        source,
        where_clause,
        group_by,
        having,
        order_by,
        limit,
        offset,
        proof_clause,
        effect_decl,
        version_const,
        linear_annot,
        epistemic_clause,
        requested_level,
    })
}

// ── P5c: OctadSchema codec (schema marshalling for the recompute tier)

fn enc_vqltype(t: &VqlType, o: &mut Vec<u8>) {
    match t {
        VqlType::TString => put_u8(o, 0),
        VqlType::TInt => put_u8(o, 1),
        VqlType::TFloat => put_u8(o, 2),
        VqlType::TBool => put_u8(o, 3),
        VqlType::TBytes => put_u8(o, 4),
        VqlType::TVector(n) => {
            put_u8(o, 5);
            put_u64(o, *n);
        }
        VqlType::TTimestamp => put_u8(o, 6),
        VqlType::THash => put_u8(o, 7),
        VqlType::TList(inner) => {
            put_u8(o, 8);
            enc_vqltype(inner, o);
        }
        VqlType::TRecord(fields) => {
            put_u8(o, 9);
            put_len(o, fields.len());
            for (name, fty) in fields {
                put_str(o, name);
                enc_vqltype(fty, o);
            }
        }
        VqlType::TOctad => put_u8(o, 10),
        VqlType::TNull(inner) => {
            put_u8(o, 11);
            enc_vqltype(inner, o);
        }
        VqlType::TAny => put_u8(o, 12),
        VqlType::TKnows(a, inner) => {
            put_u8(o, 13);
            enc_agent(a, o);
            enc_vqltype(inner, o);
        }
        VqlType::TBelieves(a, inner) => {
            put_u8(o, 14);
            enc_agent(a, o);
            enc_vqltype(inner, o);
        }
        VqlType::TCommonKnowledge(inner) => {
            put_u8(o, 15);
            enc_vqltype(inner, o);
        }
    }
}

fn enc_fielddef(f: &FieldDef, o: &mut Vec<u8>) {
    put_str(o, &f.name);
    enc_vqltype(&f.ty, o);
    put_bool(o, f.nullable);
    put_bool(o, f.indexed);
}

fn enc_modschema(m: &ModalitySchema, o: &mut Vec<u8>) {
    enc_modality(&m.modality, o);
    put_len(o, m.fields.len());
    for fd in &m.fields {
        enc_fielddef(fd, o);
    }
}

/// Serialise an `OctadSchema` to the v1 `VCLS` wire stream. Total.
pub fn to_wire_schema(s: &OctadSchema) -> Vec<u8> {
    let mut o = Vec::new();
    o.extend_from_slice(&SCHEMA_MAGIC);
    o.extend_from_slice(&VERSION.to_le_bytes());
    enc_modschema(&s.graph, &mut o);
    enc_modschema(&s.vector, &mut o);
    enc_modschema(&s.tensor, &mut o);
    enc_modschema(&s.semantic, &mut o);
    enc_modschema(&s.document, &mut o);
    enc_modschema(&s.temporal, &mut o);
    enc_modschema(&s.provenance, &mut o);
    enc_modschema(&s.spatial, &mut o);
    o
}

fn dec_vqltype(d: &mut D) -> Result<VqlType, WireError> {
    match d.u8()? {
        0 => Ok(VqlType::TString),
        1 => Ok(VqlType::TInt),
        2 => Ok(VqlType::TFloat),
        3 => Ok(VqlType::TBool),
        4 => Ok(VqlType::TBytes),
        5 => Ok(VqlType::TVector(d.u64()?)),
        6 => Ok(VqlType::TTimestamp),
        7 => Ok(VqlType::THash),
        8 => Ok(VqlType::TList(Box::new(dec_vqltype(d)?))),
        9 => {
            let fields = d.vec(|dd| {
                let name = dd.string()?;
                let fty = dec_vqltype(dd)?;
                Ok((name, fty))
            })?;
            Ok(VqlType::TRecord(fields))
        }
        10 => Ok(VqlType::TOctad),
        11 => Ok(VqlType::TNull(Box::new(dec_vqltype(d)?))),
        12 => Ok(VqlType::TAny),
        13 => {
            let a = dec_agent(d)?;
            Ok(VqlType::TKnows(a, Box::new(dec_vqltype(d)?)))
        }
        14 => {
            let a = dec_agent(d)?;
            Ok(VqlType::TBelieves(a, Box::new(dec_vqltype(d)?)))
        }
        15 => Ok(VqlType::TCommonKnowledge(Box::new(dec_vqltype(d)?))),
        t => Err(WireError::BadTag {
            ty: "VqlType",
            tag: t,
        }),
    }
}

fn dec_fielddef(d: &mut D) -> Result<FieldDef, WireError> {
    let name = d.string()?;
    let ty = dec_vqltype(d)?;
    let nullable = d.boolean()?;
    let indexed = d.boolean()?;
    Ok(FieldDef {
        name,
        ty,
        nullable,
        indexed,
    })
}

fn dec_modschema(d: &mut D) -> Result<ModalitySchema, WireError> {
    let modality = dec_modality(d)?;
    let fields = d.vec(dec_fielddef)?;
    Ok(ModalitySchema { modality, fields })
}

/// Decode a v1 `VCLS` wire stream into an `OctadSchema`. Total: every
/// input yields `Ok`/`Err`, never a panic (same contract as
/// [`from_wire`]).
pub fn from_wire_schema(input: &[u8]) -> Result<OctadSchema, WireError> {
    let mut d = D { b: input, pos: 0 };
    if d.take(4)? != SCHEMA_MAGIC {
        return Err(WireError::BadMagic);
    }
    let ver = d.u16()?;
    if ver != VERSION {
        return Err(WireError::BadVersion(ver));
    }
    let graph = dec_modschema(&mut d)?;
    let vector = dec_modschema(&mut d)?;
    let tensor = dec_modschema(&mut d)?;
    let semantic = dec_modschema(&mut d)?;
    let document = dec_modschema(&mut d)?;
    let temporal = dec_modschema(&mut d)?;
    let provenance = dec_modschema(&mut d)?;
    let spatial = dec_modschema(&mut d)?;
    if d.pos != d.b.len() {
        return Err(WireError::TrailingBytes);
    }
    Ok(OctadSchema {
        graph,
        vector,
        tensor,
        semantic,
        document,
        temporal,
        provenance,
        spatial,
    })
}
