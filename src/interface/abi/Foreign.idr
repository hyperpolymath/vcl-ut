-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
||| VCL-total Foreign Function Interface Declarations
|||
||| Declares all C-compatible functions implemented in the Zig FFI layer.
||| The pipeline processes queries through progressive safety levels:
|||
|||   parse -> bind_schema -> check_types -> check_effects -> compile
|||
||| Each stage returns a handle to an intermediate representation.
||| The final query plan carries proof of the highest achieved safety level.
|||
||| All functions are declared here with type signatures.
||| Implementations live in ffi/zig/src/main.zig

module VqlUt.ABI.Foreign

import VqlUt.ABI.Types
import VqlUt.ABI.Layout

%default total

--------------------------------------------------------------------------------
-- Library Version
--------------------------------------------------------------------------------

||| Get the VCL-total ABI version number.
||| Returns a semantic version encoded as (major << 16 | minor << 8 | patch).
export
%foreign "C:vqlut_abi_version, libvqlut"
prim__abiVersion : PrimIO Bits32

||| Safe wrapper: get ABI version as (major, minor, patch)
export
abiVersion : IO (Bits8, Bits8, Bits8)
abiVersion = do
  v <- primIO prim__abiVersion
  let major = cast {to=Bits8} (v `shiftR` 16)
  let minor = cast {to=Bits8} ((v `shiftR` 8) `and` 0xFF)
  let patch = cast {to=Bits8} (v `and` 0xFF)
  pure (major, minor, patch)

--------------------------------------------------------------------------------
-- Query Pipeline: Parse
--------------------------------------------------------------------------------

||| Parse a VCL query string into a parse tree handle.
||| This is stage 0 (ParseSafe) of the safety pipeline.
|||
||| @param query  Pointer to null-terminated VCL query string
||| @param mode   QueryMode tag (0=Slipstream, 1=DependentTypes, 2=UltimateTypeSafe)
||| @param outHandle  Out-pointer: receives parse tree handle on success
||| @return VqlUtError tag (0=Ok, 1=ParseError, ...)
export
%foreign "C:vqlut_parse, libvqlut"
prim__parse : Bits64 -> Bits32 -> Bits64 -> PrimIO Bits32

||| Safe wrapper: parse a query string.
||| Returns a QueryHandle on success, or a VqlUtError on failure.
export
parse : String -> QueryMode -> IO (Either VqlUtError QueryHandle)
parse query mode = do
  -- NOTE: In real usage, query string must be passed as a C string pointer.
  -- This wrapper demonstrates the calling convention.
  result <- primIO (prim__parse 0 (queryModeToInt mode) 0)
  case intToVqlUtError result of
    Just Ok => pure (Left InternalError) -- placeholder: real impl uses out-pointer
    Just err => pure (Left err)
    Nothing => pure (Left InternalError)

--------------------------------------------------------------------------------
-- Query Pipeline: Schema Binding
--------------------------------------------------------------------------------

||| Bind a parse tree to a database schema, producing a schema-bound tree.
||| This is stage 1 (SchemaBound) of the safety pipeline.
|||
||| @param parseTree   Handle from vqlut_parse
||| @param schemaHandle Handle to a loaded schema object
||| @param outHandle   Out-pointer: receives bound tree handle on success
||| @return VqlUtError tag
export
%foreign "C:vqlut_bind_schema, libvqlut"
prim__bindSchema : Bits64 -> Bits64 -> Bits64 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- Query Pipeline: Type Checking
--------------------------------------------------------------------------------

||| Type-check a schema-bound tree, producing a typed tree.
||| This is stage 2 (TypeCompat) of the safety pipeline.
||| Also checks NullSafe (level 3) and InjectionProof (level 4).
|||
||| @param boundTree  Handle from vqlut_bind_schema
||| @param outHandle  Out-pointer: receives typed tree handle on success
||| @return VqlUtError tag
export
%foreign "C:vqlut_check_types, libvqlut"
prim__checkTypes : Bits64 -> Bits64 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- Query Pipeline: Effect Checking
--------------------------------------------------------------------------------

||| Check effects on a typed tree, producing an effect-annotated tree.
||| This covers stages 5-7 (ResultTyped, CardinalitySafe, EffectTracked).
|||
||| @param typedTree  Handle from vqlut_check_types
||| @param outHandle  Out-pointer: receives annotated tree handle on success
||| @return VqlUtError tag
export
%foreign "C:vqlut_check_effects, libvqlut"
prim__checkEffects : Bits64 -> Bits64 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- Query Pipeline: Compilation
--------------------------------------------------------------------------------

||| Compile an annotated tree into a query plan.
||| In UltimateTypeSafe mode, also checks TemporalSafe (level 8)
||| and LinearSafe (level 9).
|||
||| @param annotatedTree  Handle from vqlut_check_effects
||| @param outPlan        Out-pointer: receives query plan buffer pointer
||| @param outPlanSize    Out-pointer: receives plan buffer size in bytes
||| @return VqlUtError tag
export
%foreign "C:vqlut_compile, libvqlut"
prim__compile : Bits64 -> Bits64 -> Bits64 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- Query Inspection
--------------------------------------------------------------------------------

||| Get the highest achieved safety level for a compiled query plan.
|||
||| @param planHandle  Handle from vqlut_compile
||| @return SafetyLevel tag (0-9), or 0xFFFFFFFF on error
export
%foreign "C:vqlut_get_safety_level, libvqlut"
prim__getSafetyLevel : Bits64 -> PrimIO Bits32

||| Safe wrapper: get the safety level of a query plan
export
getSafetyLevel : QueryHandle -> IO (Maybe SafetyLevel)
getSafetyLevel h = do
  tag <- primIO (prim__getSafetyLevel (queryHandlePtr h))
  pure (intToSafetyLevel tag)

--------------------------------------------------------------------------------
-- Resource Cleanup
--------------------------------------------------------------------------------

||| Destroy (free) any handle returned by VCL-total.
||| Safe to call with null (0) — will be a no-op.
||| After calling destroy, the handle must not be used again.
|||
||| @param handle  Any handle from vqlut_parse, vqlut_bind_schema, etc.
export
%foreign "C:vqlut_destroy, libvqlut"
prim__destroy : Bits64 -> PrimIO ()

||| Safe wrapper: destroy a query handle
export
destroy : QueryHandle -> IO ()
destroy h = primIO (prim__destroy (queryHandlePtr h))

--------------------------------------------------------------------------------
-- Error Handling
--------------------------------------------------------------------------------

||| Get the last error message as a C string.
||| Returns null if no error has occurred.
||| The returned string is valid until the next VCL-total call on the same thread.
export
%foreign "C:vqlut_last_error, libvqlut"
prim__lastError : PrimIO Bits64

||| Convert C string pointer to Idris String
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

||| Retrieve last error as string
export
lastError : IO (Maybe String)
lastError = do
  ptr <- primIO prim__lastError
  if ptr == 0
    then pure Nothing
    else pure (Just (prim__getString ptr))

||| Get human-readable description for a VqlUtError
export
errorDescription : VqlUtError -> String
errorDescription Ok                     = "Success"
errorDescription ParseError             = "Query failed to parse"
errorDescription SchemaError            = "Schema reference not found"
errorDescription TypeError              = "Type incompatibility detected"
errorDescription NullError              = "Unhandled NULL propagation"
errorDescription InjectionAttempt       = "Potential injection vector detected"
errorDescription CardinalityViolation   = "JOIN cardinality violation"
errorDescription EffectViolation        = "Untracked side effect"
errorDescription TemporalBoundsExceeded = "Temporal bounds exceeded"
errorDescription LinearityViolation     = "Linear resource double-consumed"
errorDescription InternalError          = "Internal VCL-total error"
