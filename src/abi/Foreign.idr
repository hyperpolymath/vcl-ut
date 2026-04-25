-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-ut Foreign Function Interface declarations.
|||
||| Declares the C-ABI entry points exported by the Zig FFI shim at
||| `ffi/zig/src/lib.zig`. Idris2's `%foreign` directive carries the
||| same signature both ways so the type checker catches drift.

module Foreign

import VclTypes

%default total

||| Verify a VCL query string against a schema. Returns an exit code
||| matching `VclTypes.verifyExitCode`:
|||   1..10  : Verified at that safety level
|||   0      : Pending (async checker still running)
|||   -1     : Rejected (call vclut_last_error to retrieve the message)
%foreign "C:vclut_verify_query, libvclut_ffi"
export
prim__verify : (queryStr : String) -> (schemaId : Bits64) -> PrimIO Int

||| Retrieve the most recent error message produced by the FFI layer.
||| Caller does not own the returned pointer; copy before the next FFI
||| call. Empty string when no error is pending.
%foreign "C:vclut_last_error, libvclut_ffi"
export
prim__lastError : PrimIO String

||| Reset the FFI's session state. Call once at process start before
||| any verify_query invocations.
%foreign "C:vclut_init, libvclut_ffi"
export
prim__init : PrimIO Int

||| Idiomatic Idris wrapper over `prim__verify` that promotes the raw
||| exit code to a structured `VerifyResult`.
public export
verifyQuery : String -> SchemaId -> IO VerifyResult
verifyQuery q (MkSchemaId sid) = do
  rc <- primIO $ prim__verify q sid
  case rc of
    1  => pure (Verified L1Wellformed)
    2  => pure (Verified L2Typed)
    3  => pure (Verified L3Bound)
    4  => pure (Verified L4Injective)
    5  => pure (Verified L5Total)
    6  => pure (Verified L6Cardinal)
    7  => pure (Verified L7Effects)
    8  => pure (Verified L8Linear)
    9  => pure (Verified L9Cost)
    10 => pure (Verified L10Provable)
    0  => pure Pending
    _  => do
      msg <- primIO prim__lastError
      pure (Rejected msg)
