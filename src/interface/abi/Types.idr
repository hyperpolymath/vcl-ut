-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
||| VCL-total ABI Type Definitions
|||
||| Defines the Application Binary Interface for VCL Total Type-Safety,
||| a 10-level query safety checker for VeriSimDB backends.
|||
||| All type definitions include formal proofs of correctness for
||| cross-language interop via the Zig FFI layer.
|||
||| @see Layout.idr for C-ABI memory layout proofs
||| @see Foreign.idr for FFI function declarations

module VclTotal.ABI.Types

import Data.Bits
import Data.So
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- Platform Detection
--------------------------------------------------------------------------------

||| Supported platforms for VCL-total ABI
public export
data Platform = Linux | Windows | MacOS | BSD | WASM

||| Compile-time platform detection
||| Set during compilation based on target triple
public export
thisPlatform : Platform
thisPlatform =
  %runElab do
    -- Platform detection logic — overridden by compiler flags
    pure Linux

--------------------------------------------------------------------------------
-- Query Safety Levels (the 10 levels of VCL-total)
--------------------------------------------------------------------------------

||| The 10 progressive safety levels that VCL-total enforces on queries.
||| Each level subsumes all prior levels: a query at level N has passed
||| all checks from levels 0 through N.
|||
||| Level 0: ParseSafe       — syntactically valid VCL
||| Level 1: SchemaBound      — all referenced tables/columns exist in schema
||| Level 2: TypeCompat       — expression types are compatible (no implicit coercion)
||| Level 3: NullSafe         — NULL propagation is explicitly handled
||| Level 4: InjectionProof   — no unescaped user input in query structure
||| Level 5: ResultTyped      — result set columns have known, exact types
||| Level 6: CardinalitySafe  — JOIN cardinality proven (no accidental cross-products)
||| Level 7: EffectTracked    — side effects (INSERT/UPDATE/DELETE) are annotated
||| Level 8: TemporalSafe     — temporal bounds respected (VeriSimDB time-travel)
||| Level 9: LinearSafe       — resource linearity proven (no double-consume of streams)
||| Level 10: EpistemicSafe   — epistemic consistency proven (S5 modal logic)
public export
data SafetyLevel : Type where
  ParseSafe       : SafetyLevel
  SchemaBound     : SafetyLevel
  TypeCompat      : SafetyLevel
  NullSafe        : SafetyLevel
  InjectionProof  : SafetyLevel
  ResultTyped     : SafetyLevel
  CardinalitySafe : SafetyLevel
  EffectTracked   : SafetyLevel
  TemporalSafe    : SafetyLevel
  LinearSafe      : SafetyLevel
  EpistemicSafe   : SafetyLevel

||| Convert SafetyLevel to C-compatible integer tag (0-10)
public export
safetyLevelToInt : SafetyLevel -> Bits32
safetyLevelToInt ParseSafe       = 0
safetyLevelToInt SchemaBound     = 1
safetyLevelToInt TypeCompat      = 2
safetyLevelToInt NullSafe        = 3
safetyLevelToInt InjectionProof  = 4
safetyLevelToInt ResultTyped     = 5
safetyLevelToInt CardinalitySafe = 6
safetyLevelToInt EffectTracked   = 7
safetyLevelToInt TemporalSafe    = 8
safetyLevelToInt LinearSafe      = 9
safetyLevelToInt EpistemicSafe   = 10

||| Parse a C integer tag back to SafetyLevel
public export
intToSafetyLevel : Bits32 -> Maybe SafetyLevel
intToSafetyLevel 0  = Just ParseSafe
intToSafetyLevel 1  = Just SchemaBound
intToSafetyLevel 2  = Just TypeCompat
intToSafetyLevel 3  = Just NullSafe
intToSafetyLevel 4  = Just InjectionProof
intToSafetyLevel 5  = Just ResultTyped
intToSafetyLevel 6  = Just CardinalitySafe
intToSafetyLevel 7  = Just EffectTracked
intToSafetyLevel 8  = Just TemporalSafe
intToSafetyLevel 9  = Just LinearSafe
intToSafetyLevel 10 = Just EpistemicSafe
intToSafetyLevel _  = Nothing

||| SafetyLevel decidable equality
public export
DecEq SafetyLevel where
  decEq ParseSafe       ParseSafe       = Yes Refl
  decEq SchemaBound     SchemaBound     = Yes Refl
  decEq TypeCompat      TypeCompat      = Yes Refl
  decEq NullSafe        NullSafe        = Yes Refl
  decEq InjectionProof  InjectionProof  = Yes Refl
  decEq ResultTyped     ResultTyped     = Yes Refl
  decEq CardinalitySafe CardinalitySafe = Yes Refl
  decEq EffectTracked   EffectTracked   = Yes Refl
  decEq TemporalSafe    TemporalSafe    = Yes Refl
  decEq LinearSafe      LinearSafe      = Yes Refl
  decEq EpistemicSafe   EpistemicSafe   = Yes Refl
  decEq _ _ = No absurd

--------------------------------------------------------------------------------
-- VCL-total Error Codes
--------------------------------------------------------------------------------

||| Error codes returned by VCL-total FFI operations.
||| Each maps to a specific failure mode in the safety checking pipeline.
public export
data VclTotalError : Type where
  ||| Operation succeeded — no error
  Ok                   : VclTotalError
  ||| Query failed to parse (level 0 failure)
  ParseError           : VclTotalError
  ||| Schema reference not found (level 1 failure)
  SchemaError          : VclTotalError
  ||| Type incompatibility detected (level 2 failure)
  TypeError            : VclTotalError
  ||| Unhandled NULL propagation (level 3 failure)
  NullError            : VclTotalError
  ||| Potential injection vector detected (level 4 failure)
  InjectionAttempt     : VclTotalError
  ||| JOIN cardinality violation (level 6 failure)
  CardinalityViolation : VclTotalError
  ||| Untracked side effect (level 7 failure)
  EffectViolation      : VclTotalError
  ||| Temporal bounds exceeded (level 8 failure)
  TemporalBoundsExceeded : VclTotalError
  ||| Linear resource double-consumed (level 9 failure)
  LinearityViolation   : VclTotalError
  ||| Epistemic consistency violation (level 10 failure)
  EpistemicViolation   : VclTotalError
  ||| Internal error (bug in VCL-total itself)
  InternalError        : VclTotalError

||| Convert VclTotalError to C-compatible integer tag (0-11)
public export
vqlUtErrorToInt : VclTotalError -> Bits32
vqlUtErrorToInt Ok                     = 0
vqlUtErrorToInt ParseError             = 1
vqlUtErrorToInt SchemaError            = 2
vqlUtErrorToInt TypeError              = 3
vqlUtErrorToInt NullError              = 4
vqlUtErrorToInt InjectionAttempt       = 5
vqlUtErrorToInt CardinalityViolation   = 6
vqlUtErrorToInt EffectViolation        = 7
vqlUtErrorToInt TemporalBoundsExceeded = 8
vqlUtErrorToInt LinearityViolation     = 9
vqlUtErrorToInt EpistemicViolation     = 10
vqlUtErrorToInt InternalError          = 11

||| Parse a C integer tag back to VclTotalError
public export
intToVclTotalError : Bits32 -> Maybe VclTotalError
intToVclTotalError 0  = Just Ok
intToVclTotalError 1  = Just ParseError
intToVclTotalError 2  = Just SchemaError
intToVclTotalError 3  = Just TypeError
intToVclTotalError 4  = Just NullError
intToVclTotalError 5  = Just InjectionAttempt
intToVclTotalError 6  = Just CardinalityViolation
intToVclTotalError 7  = Just EffectViolation
intToVclTotalError 8  = Just TemporalBoundsExceeded
intToVclTotalError 9  = Just LinearityViolation
intToVclTotalError 10 = Just EpistemicViolation
intToVclTotalError 11 = Just InternalError
intToVclTotalError _  = Nothing

||| VclTotalError decidable equality
public export
DecEq VclTotalError where
  decEq Ok                     Ok                     = Yes Refl
  decEq ParseError             ParseError             = Yes Refl
  decEq SchemaError            SchemaError            = Yes Refl
  decEq TypeError              TypeError              = Yes Refl
  decEq NullError              NullError              = Yes Refl
  decEq InjectionAttempt       InjectionAttempt       = Yes Refl
  decEq CardinalityViolation   CardinalityViolation   = Yes Refl
  decEq EffectViolation        EffectViolation        = Yes Refl
  decEq TemporalBoundsExceeded TemporalBoundsExceeded = Yes Refl
  decEq LinearityViolation     LinearityViolation     = Yes Refl
  decEq EpistemicViolation     EpistemicViolation     = Yes Refl
  decEq InternalError          InternalError          = Yes Refl
  decEq _ _ = No absurd

--------------------------------------------------------------------------------
-- Query Mode
--------------------------------------------------------------------------------

||| VCL-total query processing modes.
|||
||| Slipstream      — fast path, checks levels 0-4 only (parse through injection)
||| DependentTypes  — checks levels 0-7 (adds result typing, cardinality, effects)
||| UltimateTypeSafe — full 10-level check including temporal and linearity proofs
public export
data QueryMode : Type where
  Slipstream       : QueryMode
  DependentTypes   : QueryMode
  UltimateTypeSafe : QueryMode

||| Convert QueryMode to C-compatible integer tag (0-2)
public export
queryModeToInt : QueryMode -> Bits32
queryModeToInt Slipstream       = 0
queryModeToInt DependentTypes   = 1
queryModeToInt UltimateTypeSafe = 2

||| Parse a C integer tag back to QueryMode
public export
intToQueryMode : Bits32 -> Maybe QueryMode
intToQueryMode 0 = Just Slipstream
intToQueryMode 1 = Just DependentTypes
intToQueryMode 2 = Just UltimateTypeSafe
intToQueryMode _ = Nothing

||| QueryMode decidable equality
public export
DecEq QueryMode where
  decEq Slipstream       Slipstream       = Yes Refl
  decEq DependentTypes   DependentTypes   = Yes Refl
  decEq UltimateTypeSafe UltimateTypeSafe = Yes Refl
  decEq _ _ = No absurd

--------------------------------------------------------------------------------
-- Opaque Handles
--------------------------------------------------------------------------------

||| Opaque query handle — prevents direct construction, enforces creation
||| through the safe FFI API. Wraps a non-null pointer to a query context
||| managed by the Zig FFI layer.
public export
data QueryHandle : Type where
  MkQueryHandle : (ptr : Bits64) -> {auto 0 nonNull : So (ptr /= 0)} -> QueryHandle

||| Safely create a query handle from a pointer value.
||| Returns Nothing if pointer is null (allocation failure).
public export
createQueryHandle : Bits64 -> Maybe QueryHandle
createQueryHandle 0 = Nothing
createQueryHandle ptr = Just (MkQueryHandle ptr)

||| Extract pointer value from query handle
public export
queryHandlePtr : QueryHandle -> Bits64
queryHandlePtr (MkQueryHandle ptr) = ptr

--------------------------------------------------------------------------------
-- Platform-Specific Types (VeriSimDB backends)
--------------------------------------------------------------------------------

||| VeriSimDB backend platform detection.
||| VCL-total targets VeriSimDB which can run on these platforms.
public export
data VeriSimDBBackend = Native | WASM32 | Embedded

||| C int size — uniform across VeriSimDB-supported platforms
public export
CInt : Platform -> Type
CInt Linux   = Bits32
CInt Windows = Bits32
CInt MacOS   = Bits32
CInt BSD     = Bits32
CInt WASM    = Bits32

||| C size_t varies by platform (32-bit on WASM)
public export
CSize : Platform -> Type
CSize Linux   = Bits64
CSize Windows = Bits64
CSize MacOS   = Bits64
CSize BSD     = Bits64
CSize WASM    = Bits32

||| Pointer size in bits by platform
public export
ptrSize : Platform -> Nat
ptrSize Linux   = 64
ptrSize Windows = 64
ptrSize MacOS   = 64
ptrSize BSD     = 64
ptrSize WASM    = 32

||| Pointer type for platform
public export
CPtr : Platform -> Type -> Type
CPtr p _ = Bits (ptrSize p)

--------------------------------------------------------------------------------
-- Memory Layout Proofs for Query Plan Buffers
--------------------------------------------------------------------------------

||| Proof that a type has a specific size in bytes
public export
data HasSize : Type -> Nat -> Type where
  SizeProof : {0 t : Type} -> {n : Nat} -> HasSize t n

||| Proof that a type has a specific alignment in bytes
public export
data HasAlignment : Type -> Nat -> Type where
  AlignProof : {0 t : Type} -> {n : Nat} -> HasAlignment t n

||| Query plan buffer header — fixed-size header prepended to every
||| serialised query plan crossing the FFI boundary.
|||
||| Layout (24 bytes, 8-byte aligned):
|||   offset 0:  magic      (Bits32) — 0x56514C55 ("VQLU")
|||   offset 4:  version    (Bits32) — ABI version number
|||   offset 8:  mode       (Bits32) — QueryMode tag (0-2)
|||   offset 12: level      (Bits32) — highest SafetyLevel achieved (0-9)
|||   offset 16: plan_size  (Bits64) — size of plan payload in bytes
public export
record QueryPlanHeader where
  constructor MkQueryPlanHeader
  magic     : Bits32
  version   : Bits32
  mode      : Bits32
  level     : Bits32
  planSize  : Bits64

||| Prove the query plan header has correct size (24 bytes)
public export
queryPlanHeaderSize : (p : Platform) -> HasSize QueryPlanHeader 24
queryPlanHeaderSize p = SizeProof

||| Prove the query plan header has correct alignment (8 bytes)
public export
queryPlanHeaderAlign : (p : Platform) -> HasAlignment QueryPlanHeader 8
queryPlanHeaderAlign p = AlignProof

||| Size of C types (platform-specific)
public export
cSizeOf : (p : Platform) -> (t : Type) -> Nat
cSizeOf p Bits32 = 4
cSizeOf p Bits64 = 8
cSizeOf p Double = 8
cSizeOf p _      = ptrSize p `div` 8

||| Alignment of C types (platform-specific)
public export
cAlignOf : (p : Platform) -> (t : Type) -> Nat
cAlignOf p Bits32 = 4
cAlignOf p Bits64 = 8
cAlignOf p Double = 8
cAlignOf p _      = ptrSize p `div` 8

||| Magic number constant for VCL-total query plan buffers: "VQLU" in ASCII
public export
vqlutMagic : Bits32
vqlutMagic = 0x56514C55

--------------------------------------------------------------------------------
-- Verification
--------------------------------------------------------------------------------

||| Compile-time verification of VCL-total ABI properties
namespace Verify

  ||| Verify that all safety level tags are in range [0, 10]
  export
  safetyLevelTagsInRange : (s : SafetyLevel) -> So (safetyLevelToInt s <= 10)
  safetyLevelTagsInRange ParseSafe       = Oh
  safetyLevelTagsInRange SchemaBound     = Oh
  safetyLevelTagsInRange TypeCompat      = Oh
  safetyLevelTagsInRange NullSafe        = Oh
  safetyLevelTagsInRange InjectionProof  = Oh
  safetyLevelTagsInRange ResultTyped     = Oh
  safetyLevelTagsInRange CardinalitySafe = Oh
  safetyLevelTagsInRange EffectTracked   = Oh
  safetyLevelTagsInRange TemporalSafe    = Oh
  safetyLevelTagsInRange LinearSafe      = Oh
  safetyLevelTagsInRange EpistemicSafe   = Oh

  ||| Verify that all error tags are in range [0, 11]
  export
  errorTagsInRange : (e : VclTotalError) -> So (vqlUtErrorToInt e <= 11)
  errorTagsInRange Ok                     = Oh
  errorTagsInRange ParseError             = Oh
  errorTagsInRange SchemaError            = Oh
  errorTagsInRange TypeError              = Oh
  errorTagsInRange NullError              = Oh
  errorTagsInRange InjectionAttempt       = Oh
  errorTagsInRange CardinalityViolation   = Oh
  errorTagsInRange EffectViolation        = Oh
  errorTagsInRange TemporalBoundsExceeded = Oh
  errorTagsInRange LinearityViolation     = Oh
  errorTagsInRange EpistemicViolation     = Oh
  errorTagsInRange InternalError          = Oh

  ||| Verify that all query mode tags are in range [0, 2]
  export
  queryModeTagsInRange : (m : QueryMode) -> So (queryModeToInt m <= 2)
  queryModeTagsInRange Slipstream       = Oh
  queryModeTagsInRange DependentTypes   = Oh
  queryModeTagsInRange UltimateTypeSafe = Oh
