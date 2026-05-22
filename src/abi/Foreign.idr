-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-ut Foreign Function Interface declarations.
|||
||| Declares the C-ABI entry points exported by the Zig FFI shim at
||| `ffi/zig/src/lib.zig`. Idris2's `%foreign` directive carries the
||| same signature both ways so the type checker catches drift.
|||
||| TRUST MODEL (standards#124, Phase 3d — honest scope). The `Int`
||| returned by `prim__verify` is an *attestation*, not a transported
||| dependent proof: a C ABI cannot carry a `SafetyCertificate` (this is
||| inherent to any FFI boundary). The real verification authority is
||| the Idris2 certifier `VclTotal.Core.Checker.certifyRequested` /
||| `certifiedLevel`, which yields a non-negative level *only* behind a
||| genuine, machine-checked dependent certificate. The mapping below
||| (`rc` → `Verified Ln`) is faithful — it asserts nothing the C side
||| did not return. As of Phase 3d the Zig shim is *fail-closed*: with
||| no verifier backend linked it returns `-1` (Rejected), so
||| `verifyQuery` honestly yields `Rejected …` rather than a fabricated
||| level (the previous shim lied — fixed). NAMED OWED (absent, not
||| faked): a string→`Statement` parser (none exists in the repo — the
||| corpus certifies an already-built AST); C-ABI `Statement`/
||| `OctadSchema` marshalling; the Idris→C build that would let the shim
||| call the certifier. See verification/proofs/VERIFICATION-STANCE.adoc.

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
