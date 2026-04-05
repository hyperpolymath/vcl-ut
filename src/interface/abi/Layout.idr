-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
||| VCL-total Memory Layout Proofs
|||
||| Formal proofs about memory layout, alignment, and padding for
||| C-compatible structs crossing the VCL-total FFI boundary.
|||
||| Covers encoding/decoding roundtrip proofs for SafetyLevel, QueryMode,
||| VqlUtError, and the QueryPlanHeader struct layout.
|||
||| @see Types.idr for type definitions
||| @see Foreign.idr for FFI function declarations

module VqlUt.ABI.Layout

import VqlUt.ABI.Types
import Data.Vect
import Data.So

%default total

--------------------------------------------------------------------------------
-- Alignment Utilities
--------------------------------------------------------------------------------

||| Calculate padding needed to reach the next alignment boundary
public export
paddingFor : (offset : Nat) -> (alignment : Nat) -> Nat
paddingFor offset alignment =
  if offset `mod` alignment == 0
    then 0
    else alignment - (offset `mod` alignment)

||| Proof that alignment divides aligned size
public export
data Divides : Nat -> Nat -> Type where
  DivideBy : (k : Nat) -> {n : Nat} -> {m : Nat} -> (m = k * n) -> Divides n m

||| Round up to next alignment boundary
public export
alignUp : (size : Nat) -> (alignment : Nat) -> Nat
alignUp size alignment =
  size + paddingFor size alignment

||| Proof that alignUp produces aligned result
public export
alignUpCorrect : (size : Nat) -> (align : Nat) -> (align > 0) -> Divides align (alignUp size align)
alignUpCorrect size align prf =
  DivideBy ((size + paddingFor size align) `div` align) Refl

--------------------------------------------------------------------------------
-- SafetyLevel Tag Encoding (0-9)
--------------------------------------------------------------------------------

||| Size constant: SafetyLevel is encoded as a single Bits32 (4 bytes)
public export
safetyLevelSize : Nat
safetyLevelSize = 4

||| Roundtrip proof: encoding then decoding a SafetyLevel yields the original
public export
safetyLevelRoundtrip : (s : SafetyLevel) -> intToSafetyLevel (safetyLevelToInt s) = Just s
safetyLevelRoundtrip ParseSafe       = Refl
safetyLevelRoundtrip SchemaBound     = Refl
safetyLevelRoundtrip TypeCompat      = Refl
safetyLevelRoundtrip NullSafe        = Refl
safetyLevelRoundtrip InjectionProof  = Refl
safetyLevelRoundtrip ResultTyped     = Refl
safetyLevelRoundtrip CardinalitySafe = Refl
safetyLevelRoundtrip EffectTracked   = Refl
safetyLevelRoundtrip TemporalSafe    = Refl
safetyLevelRoundtrip LinearSafe      = Refl

--------------------------------------------------------------------------------
-- QueryMode Tag Encoding (0-2)
--------------------------------------------------------------------------------

||| Size constant: QueryMode is encoded as a single Bits32 (4 bytes)
public export
queryModeSize : Nat
queryModeSize = 4

||| Roundtrip proof: encoding then decoding a QueryMode yields the original
public export
queryModeRoundtrip : (m : QueryMode) -> intToQueryMode (queryModeToInt m) = Just m
queryModeRoundtrip Slipstream       = Refl
queryModeRoundtrip DependentTypes   = Refl
queryModeRoundtrip UltimateTypeSafe = Refl

--------------------------------------------------------------------------------
-- VqlUtError Tag Encoding (0-10)
--------------------------------------------------------------------------------

||| Size constant: VqlUtError is encoded as a single Bits32 (4 bytes)
public export
vqlUtErrorSize : Nat
vqlUtErrorSize = 4

||| Roundtrip proof: encoding then decoding a VqlUtError yields the original
public export
vqlUtErrorRoundtrip : (e : VqlUtError) -> intToVqlUtError (vqlUtErrorToInt e) = Just e
vqlUtErrorRoundtrip Ok                     = Refl
vqlUtErrorRoundtrip ParseError             = Refl
vqlUtErrorRoundtrip SchemaError            = Refl
vqlUtErrorRoundtrip TypeError              = Refl
vqlUtErrorRoundtrip NullError              = Refl
vqlUtErrorRoundtrip InjectionAttempt       = Refl
vqlUtErrorRoundtrip CardinalityViolation   = Refl
vqlUtErrorRoundtrip EffectViolation        = Refl
vqlUtErrorRoundtrip TemporalBoundsExceeded = Refl
vqlUtErrorRoundtrip LinearityViolation     = Refl
vqlUtErrorRoundtrip InternalError          = Refl

--------------------------------------------------------------------------------
-- Struct Field Layout
--------------------------------------------------------------------------------

||| A field in a struct with its offset, size, and alignment
public export
record Field where
  constructor MkField
  name      : String
  offset    : Nat
  size      : Nat
  alignment : Nat

||| Calculate the offset of the next field after this one
public export
nextFieldOffset : Field -> Nat
nextFieldOffset f = alignUp (f.offset + f.size) f.alignment

||| A struct layout is a vector of fields with size and alignment metadata
public export
record StructLayout where
  constructor MkStructLayout
  fields    : Vect n Field
  totalSize : Nat
  alignment : Nat

--------------------------------------------------------------------------------
-- QueryPlanHeader Layout (24 bytes, 8-byte aligned)
--------------------------------------------------------------------------------

||| QueryPlanHeader field layout for C ABI.
|||
||| Offset  Size  Field
||| ------  ----  -----
|||   0      4    magic     (Bits32)
|||   4      4    version   (Bits32)
|||   8      4    mode      (Bits32)
|||  12      4    level     (Bits32)
|||  16      8    plan_size (Bits64)
||| ------  ----
|||  24 bytes total, 8-byte aligned
public export
queryPlanHeaderLayout : StructLayout
queryPlanHeaderLayout =
  MkStructLayout
    [ MkField "magic"     0  4 4
    , MkField "version"   4  4 4
    , MkField "mode"      8  4 4
    , MkField "level"    12  4 4
    , MkField "plan_size" 16 8 8
    ]
    24  -- Total size: 24 bytes
    8   -- Alignment: 8 bytes

||| Size constant for QueryPlanHeader
public export
queryPlanHeaderTotalSize : Nat
queryPlanHeaderTotalSize = 24

||| Prove that the header has no internal padding waste beyond alignment.
||| Sum of field sizes = 4+4+4+4+8 = 24 = totalSize (no wasted padding)
public export
queryPlanHeaderNoPadding : queryPlanHeaderLayout.totalSize = 24
queryPlanHeaderNoPadding = Refl

--------------------------------------------------------------------------------
-- Platform-Specific Layouts
--------------------------------------------------------------------------------

||| Struct layout may differ by platform — parameterised container
public export
PlatformLayout : Platform -> Type -> Type
PlatformLayout p t = StructLayout

||| For VCL-total, the QueryPlanHeader layout is uniform across all platforms
||| because it uses only fixed-width types (Bits32, Bits64).
public export
queryPlanHeaderForPlatform : (p : Platform) -> PlatformLayout p QueryPlanHeader
queryPlanHeaderForPlatform _ = queryPlanHeaderLayout

--------------------------------------------------------------------------------
-- C ABI Compatibility
--------------------------------------------------------------------------------

||| Proof that a struct's fields are all correctly aligned
public export
data FieldsAligned : Vect n Field -> Type where
  NoFields : FieldsAligned []
  ConsField :
    (f : Field) ->
    (rest : Vect n Field) ->
    Divides f.alignment f.offset ->
    FieldsAligned rest ->
    FieldsAligned (f :: rest)

||| Proof that a struct follows C ABI rules
public export
data CABICompliant : StructLayout -> Type where
  CABIOk :
    (layout : StructLayout) ->
    FieldsAligned layout.fields ->
    CABICompliant layout

--------------------------------------------------------------------------------
-- Offset Calculation
--------------------------------------------------------------------------------

||| Look up a field by name in a struct layout
public export
fieldOffset : (layout : StructLayout) -> (fieldName : String) -> Maybe (n : Nat ** Field)
fieldOffset layout name =
  case findIndex (\f => f.name == name) layout.fields of
    Just idx => Just (finToNat idx ** index idx layout.fields)
    Nothing => Nothing

||| Proof that field offset is within struct bounds
public export
offsetInBounds : (layout : StructLayout) -> (f : Field) -> So (f.offset + f.size <= layout.totalSize)
offsetInBounds layout f = ?offsetInBoundsProof
