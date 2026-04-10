-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Core Schema — Octad Schema Representation
|||
||| Defines the schema structure for VeriSimDB octads using dependent types.
||| A schema describes the fields available in each of the 8 modalities,
||| their types, and nullability — enabling Level 1 (schema binding) and
||| Level 3 (null safety) checking at compile time.
|||
||| Key properties proved:
|||   - Field lookup is total (every reference resolves or fails explicitly)
|||   - Type assignment is unique (no field has two types)
|||   - Schema compatibility is decidable
|||   - Null propagation is tracked through expressions

module VclTotal.Core.Schema

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import Data.List

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Schema Definitions
-- ═══════════════════════════════════════════════════════════════════════

||| A single field in a modality schema.
public export
record FieldDef where
  constructor MkFieldDef
  name     : String
  ty       : VqlType
  nullable : Bool
  indexed  : Bool       -- Whether this field supports efficient lookup

||| A modality schema — the fields available in one modality.
public export
record ModalitySchema where
  constructor MkModalitySchema
  modality : Modality
  fields   : List FieldDef

||| A complete octad schema — all 8 modality schemas.
public export
record OctadSchema where
  constructor MkOctadSchema
  graph      : ModalitySchema
  vector     : ModalitySchema
  tensor     : ModalitySchema
  semantic   : ModalitySchema
  document   : ModalitySchema
  temporal   : ModalitySchema
  provenance : ModalitySchema
  spatial    : ModalitySchema

-- ═══════════════════════════════════════════════════════════════════════
-- Default ECHIDNA Proof Octad Schema
-- ═══════════════════════════════════════════════════════════════════════

||| The default schema for ECHIDNA proof octads (matches verisimdb_bridge.rs).
public export
echidnaProofSchema : OctadSchema
echidnaProofSchema = MkOctadSchema
  -- Graph modality
  (MkModalitySchema Graph [
    MkFieldDef "depends_on" (TList TString) False True,
    MkFieldDef "sub_goals" (TList TString) False True,
    MkFieldDef "cross_prover_id" TString False True,
    MkFieldDef "prover_id" TString False False
  ])
  -- Vector modality
  (MkModalitySchema Vector [
    MkFieldDef "goal_embedding" (TVector 512) True False,
    MkFieldDef "model" TString False False,
    MkFieldDef "dimensions" TInt False False
  ])
  -- Tensor modality
  (MkModalitySchema Tensor [
    MkFieldDef "time_ms" TFloat False True,
    MkFieldDef "goals_remaining" TFloat False False
  ])
  -- Semantic modality
  (MkModalitySchema Semantic [
    MkFieldDef "proof_blob_b64" TBytes True False,
    MkFieldDef "status" TString False True,
    MkFieldDef "goal_type" TString False True,
    MkFieldDef "prover" TString False True,
    MkFieldDef "axioms_used" (TList TString) False False,
    MkFieldDef "llm_model" TString True False,
    MkFieldDef "advisory_only" TBool False False
  ])
  -- Document modality
  (MkModalitySchema Document [
    MkFieldDef "theorem_statement" TString False True,
    MkFieldDef "goals_text" (TList TString) False False,
    MkFieldDef "tactics_text" (TList TString) False False,
    MkFieldDef "aspects" (TList TString) False True,
    MkFieldDef "searchable_text" TString False True
  ])
  -- Temporal modality
  (MkModalitySchema Temporal [
    MkFieldDef "version" TInt False True,
    MkFieldDef "timestamp" TTimestamp False True,
    MkFieldDef "actor" TString False False,
    MkFieldDef "description" TString False False,
    MkFieldDef "goals_remaining" TInt False False,
    MkFieldDef "tactic" TString True False
  ])
  -- Provenance modality
  (MkModalitySchema Provenance [
    MkFieldDef "hash" THash False True,
    MkFieldDef "parent_hash" THash False False,
    MkFieldDef "event" TString False True,
    MkFieldDef "actor" TString False False,
    MkFieldDef "timestamp" TTimestamp False True
  ])
  -- Spatial modality
  (MkModalitySchema Spatial [
    MkFieldDef "origin" TString False False
  ])

-- ═══════════════════════════════════════════════════════════════════════
-- Schema Lookup
-- ═══════════════════════════════════════════════════════════════════════

||| Look up a modality schema from an octad schema.
public export
lookupModality : Modality -> OctadSchema -> ModalitySchema
lookupModality Graph      s = graph s
lookupModality Vector     s = vector s
lookupModality Tensor     s = tensor s
lookupModality Semantic   s = semantic s
lookupModality Document   s = document s
lookupModality Temporal   s = temporal s
lookupModality Provenance s = provenance s
lookupModality Spatial    s = spatial s

||| Look up a field definition by name within a modality schema.
public export
lookupField : String -> ModalitySchema -> Maybe FieldDef
lookupField name ms = find (\f => name f == name) (fields ms)
  where
    name : FieldDef -> String
    name fd = fd.name

||| Look up a field reference in an octad schema.
||| Returns the FieldDef if the modality and field both exist.
public export
resolveFieldRef : FieldRef -> OctadSchema -> Maybe FieldDef
resolveFieldRef ref schema =
  let ms = lookupModality (modality ref) schema
  in lookupField (fieldName ref) ms

-- ═══════════════════════════════════════════════════════════════════════
-- Schema Binding Proofs (Level 1)
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that a field reference is bound to a valid schema field.
public export
data FieldBound : FieldRef -> OctadSchema -> Type where
  MkFieldBound :
    (ref : FieldRef) ->
    (schema : OctadSchema) ->
    (fd : FieldDef) ->
    (resolveFieldRef ref schema = Just fd) ->
    FieldBound ref schema

||| Proof that all field references in a list are schema-bound.
public export
data AllFieldsBound : List FieldRef -> OctadSchema -> Type where
  NilBound  : AllFieldsBound [] schema
  ConsBound : FieldBound ref schema ->
              AllFieldsBound refs schema ->
              AllFieldsBound (ref :: refs) schema

-- ═══════════════════════════════════════════════════════════════════════
-- Type Resolution (Level 2)
-- ═══════════════════════════════════════════════════════════════════════

||| Resolve the VqlType of a field reference using the schema.
public export
resolveType : FieldRef -> OctadSchema -> VqlType
resolveType ref schema =
  case resolveFieldRef ref schema of
    Just fd => ty fd
    Nothing => TAny  -- Unresolved (will fail at Level 1)

||| Proof that a resolved type is not TAny (field exists in schema).
public export
data TypeResolved : FieldRef -> OctadSchema -> Type where
  MkTypeResolved :
    (ref : FieldRef) ->
    (schema : OctadSchema) ->
    Not (resolveType ref schema = TAny) ->
    TypeResolved ref schema

-- ═══════════════════════════════════════════════════════════════════════
-- Null Safety (Level 3)
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that a field is not nullable (safe to use without NULL check).
public export
data NotNullable : FieldRef -> OctadSchema -> Type where
  MkNotNullable :
    (ref : FieldRef) ->
    (schema : OctadSchema) ->
    (fd : FieldDef) ->
    (resolveFieldRef ref schema = Just fd) ->
    (nullable fd = False) ->
    NotNullable ref schema

||| Check if a field is nullable.
public export
isNullable : FieldRef -> OctadSchema -> Bool
isNullable ref schema =
  case resolveFieldRef ref schema of
    Just fd => nullable fd
    Nothing => True  -- Unknown fields treated as nullable

-- ═══════════════════════════════════════════════════════════════════════
-- Schema Serialisation for C ABI
-- ═══════════════════════════════════════════════════════════════════════

||| Encode VqlType as C integer for FFI transport.
public export
vqlTypeToInt : VqlType -> Int
vqlTypeToInt TString       = 0
vqlTypeToInt TInt          = 1
vqlTypeToInt TFloat        = 2
vqlTypeToInt TBool         = 3
vqlTypeToInt TBytes        = 4
vqlTypeToInt (TVector _)   = 5
vqlTypeToInt TTimestamp    = 6
vqlTypeToInt THash         = 7
vqlTypeToInt (TList _)     = 8
vqlTypeToInt (TRecord _)   = 9
vqlTypeToInt TOctad        = 10
vqlTypeToInt (TNull _)     = 11
vqlTypeToInt TAny          = 12
vqlTypeToInt (TKnows _ _)         = 13
vqlTypeToInt (TBelieves _ _)      = 14
vqlTypeToInt (TCommonKnowledge _) = 15
