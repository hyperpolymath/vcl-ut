// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Faithful Rust mirror of `src/core/Schema.idr`'s `OctadSchema`
//! (and the `VqlType` it carries, from `src/core/Grammar.idr`).
//!
//! NOTE — why `VqlType` lives here and not in [`crate::ast`]: the
//! parser deliberately omits `VqlType` because *parsing* establishes
//! syntax only and never resolves types (see the `ast` module note).
//! A *schema*, by contrast, IS a declaration of field types — `VqlType`
//! is its payload, not dead data. Keeping it in this separate module
//! preserves the parser's "syntax only" honesty while giving P5c the
//! schema the certified decider needs to recompute the safety verdict.
//! One-to-one with the Idris constructors so the wire codec is a
//! structural map with no re-interpretation.

use crate::ast::{Agent, Modality};

/// `Grammar.idr`: `data VqlType`. Recursive (so its wire decoder is
/// fuel-bounded, exactly like `Expr`).
#[derive(Debug, Clone, PartialEq)]
pub enum VqlType {
    TString,
    TInt,
    TFloat,
    TBool,
    TBytes,
    /// `TVector Nat` — fixed dimension (Idris `Nat`).
    TVector(u64),
    TTimestamp,
    THash,
    TList(Box<VqlType>),
    TRecord(Vec<(String, VqlType)>),
    TOctad,
    TNull(Box<VqlType>),
    TAny,
    TKnows(Agent, Box<VqlType>),
    TBelieves(Agent, Box<VqlType>),
    TCommonKnowledge(Box<VqlType>),
}

/// `Schema.idr`: `record FieldDef`.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldDef {
    pub name: String,
    pub ty: VqlType,
    pub nullable: bool,
    pub indexed: bool,
}

/// `Schema.idr`: `record ModalitySchema`.
#[derive(Debug, Clone, PartialEq)]
pub struct ModalitySchema {
    pub modality: Modality,
    pub fields: Vec<FieldDef>,
}

/// `Schema.idr`: `record OctadSchema` — the 8 modality schemas, in
/// record order (fixed arity; no length prefix on the wire).
#[derive(Debug, Clone, PartialEq)]
pub struct OctadSchema {
    pub graph: ModalitySchema,
    pub vector: ModalitySchema,
    pub tensor: ModalitySchema,
    pub semantic: ModalitySchema,
    pub document: ModalitySchema,
    pub temporal: ModalitySchema,
    pub provenance: ModalitySchema,
    pub spatial: ModalitySchema,
}
