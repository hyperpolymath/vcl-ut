-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
||| VCL-total Tier-2 Foreign Function Interface (signed attestation)
|||
||| Idris-side bindings to the *honest* C ABI exposed by the Zig shim
||| `ffi/zig/src/lib.zig` (`vclut_verify_wire`), which calls into the
||| Rust crate `src/interface/attest` (`vclut_rs_verify`) — see
||| `src/interface/attest/ATTESTATION-FORMAT.adoc` for the wire
||| contract and `docs/decisions/0002-ffi-attestation-trust-boundary.adoc`
||| for the trust model rationale.
|||
||| **Architectural role.** This module replaces the level-asserting
||| legacy path (`VclTotal.Legacy.Foreign.getSafetyLevel`, deprecated
||| 2026-06-02). Where the legacy path returned a Zig-side integer
||| with no Idris verification, this module returns a 65-byte
||| Ed25519-signed attestation
|||
|||   `token = [level : Bits8] ++ [signature : Vect 64 Bits8]`
|||
||| over `DOMAIN ‖ sha256(stmt_wire) ‖ sha256(schema_wire) ‖ level`
||| (`DOMAIN = "VCLT-ATTEST-v1\0\0"`). The certifier signs *iff* the
||| conformance-pinned `vcltotal_parse::certified_level` lies in
||| `0..=10` — **fail-closed**, never a token for an unestablished
||| level.
|||
||| **Trust model (Tier-2 ceiling).** A C ABI erases types to machine
||| words; it cannot transport a re-checkable dependent
||| `SafetyCertificate`. Over a C ABI the honest ceiling is
||| trusted-certifier attestation, and that ceiling is what this
||| module exposes. The consumer's TCB is:
|||   (1) the certifier holds its Ed25519 key genuinely,
|||   (2) the certifier ran the conformance-pinned decider before
|||       signing,
|||   (3) the Ed25519-dalek + sha2 implementation in the Tier-2 crate.
|||
||| **Strictly weaker than Tier-1** (recompute-PCC over `wasm32`,
||| `src/interface/recompute-wasm`), which trusts neither (1) nor (2)
||| because the consumer re-runs the decision itself. Prefer Tier-1
||| where wasm hosting is available; Tier-2 is the C-ABI fallback.
|||
||| **No proofs.** Like all FFI plumbing, this module contains no
||| theorems — its safety properties live in the Tier-2 Rust crate's
||| tests (`src/interface/attest/src/lib.rs::tests` — roundtrip + 5
||| tamper variants + fail-closed + C-ABI). It is *not* in the
||| Idris2 proof corpus (`vclut-core.ipkg`); see
||| `verification/proofs/VERIFICATION-STANCE.adoc` §"Boundary model"
||| for what the Tier-2 ceiling does and does not guarantee.

module VclTotal.ABI.Tier2

import VclTotal.ABI.Types
import Data.Buffer
import Data.List

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Public surface
-- ═══════════════════════════════════════════════════════════════════════

||| Tier-2 verification verdict.
|||
|||   * `Verified lvl token` — certifier signed level `lvl`, attestation
|||     bytes are in `token` (always 65 bytes: 1 level + 64 signature).
|||   * `Rejected reason` — fail-closed; the certifier did not establish
|||     a level (decode failure, malformed input, level outside
|||     `0..=10`, or any other reject path). Token is NOT emitted.
public export
data Tier2Verdict : Type where
  Verified : SafetyLevel -> List Bits8 -> Tier2Verdict
  Rejected : String -> Tier2Verdict

||| The fixed Ed25519 attestation token width (`level : 1 byte`
||| + `signature : 64 bytes`).
public export
attestationTokenSize : Nat
attestationTokenSize = 65

||| Ed25519 seed/secret-key byte width.
public export
ed25519SeedSize : Nat
ed25519SeedSize = 32

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI declarations
-- ═══════════════════════════════════════════════════════════════════════

||| The honest Tier-2 entry point. Bound to the Zig shim
||| `vclut_verify_wire` in `ffi/zig/src/lib.zig`, which calls
||| `vclut_rs_verify` (`src/interface/attest/src/lib.rs`).
|||
||| ABI:
|||
|||   ```c
|||   int32_t vclut_verify_wire(
|||       const uint8_t* stmt_ptr,   size_t stmt_len,
|||       const uint8_t* schema_ptr, size_t schema_len,
|||       const uint8_t* sk_ptr,                       /* 32 bytes */
|||       uint8_t*       out_ptr,    size_t out_cap   /* >= 65 */
|||   );
|||   ```
|||
||| Returns `0..=10` on success (writes the 65-byte attestation to
||| `out_ptr`), `-1` on Reject (no write). Pointers must each describe
||| a valid range of the stated length; the function never reads or
||| writes outside the documented spans. See the Rust crate's `Safety`
||| comment for the precise contract.
export
%foreign "C:vclut_verify_wire, libvclut_ffi"
prim__vclutVerifyWire :
  Buffer -> Int ->     -- stmt
  Buffer -> Int ->     -- schema
  Buffer ->            -- 32-byte Ed25519 seed
  Buffer -> Int ->     -- out + cap
  PrimIO Int

-- ═══════════════════════════════════════════════════════════════════════
-- Internal helpers
-- ═══════════════════════════════════════════════════════════════════════

||| Marshal a `List Bits8` into a freshly-allocated `Buffer`. Returns
||| `Nothing` on allocation failure.
private
listToBuffer : List Bits8 -> IO (Maybe Buffer)
listToBuffer xs = do
  let n = length xs
  Just buf <- newBuffer (cast n) | Nothing => pure Nothing
  go buf 0 xs
  pure (Just buf)
  where
    go : Buffer -> Int -> List Bits8 -> IO ()
    go _   _ []        = pure ()
    go buf i (b :: bs) = do
      setBits8 buf i b
      go buf (i + 1) bs

||| Read the entire contents of a `Buffer` of declared length `n` into
||| a `List Bits8`. Reads bytes `[0, n)` in order.
private
bufferToList : Buffer -> Int -> IO (List Bits8)
bufferToList buf n = go 0 []
  where
    go : Int -> List Bits8 -> IO (List Bits8)
    go i acc =
      if i >= n
        then pure (reverse acc)
        else do
          b <- getBits8 buf i
          assert_total (go (i + 1) (b :: acc))

-- ═══════════════════════════════════════════════════════════════════════
-- Safe public wrapper
-- ═══════════════════════════════════════════════════════════════════════

||| Verify a wire-marshalled `(Statement, OctadSchema)` pair via the
||| Tier-2 signed-attestation backend. On success returns
||| `Verified level token` with the 65-byte attestation; on any
||| reject path returns `Rejected reason` with a human-readable cause.
|||
||| @param stmtWire   v1 statement-wire bytes (see
|||                   `src/interface/parse/WIRE-FORMAT.adoc`)
||| @param schemaWire v1 schema-wire bytes (`VCLS` magic)
||| @param sk         the certifier's 32-byte Ed25519 *seed* (NOT a
|||                   public key — this is the signing key). Real
|||                   provisioning is deployment via the estate token
|||                   vault.
|||
||| **Fail-closed contract.** This wrapper returns `Rejected` on:
|||   * `sk` not exactly 32 bytes;
|||   * buffer allocation failure (out of memory);
|||   * any negative `c_int` from the C backend (decode failure,
|||     malformed input, level outside `0..=10`);
|||   * a return value outside `0..=10` (defensive — the backend's
|||     contract already constrains this, but we re-check on the way
|||     out).
export
verifyWire :
  (stmtWire   : List Bits8) ->
  (schemaWire : List Bits8) ->
  (sk         : List Bits8) ->
  IO Tier2Verdict
verifyWire stmtWire schemaWire sk = do
  if length sk /= ed25519SeedSize
    then pure (Rejected
      "Ed25519 seed must be exactly 32 bytes")
    else do
      Just stmtBuf   <- listToBuffer stmtWire
        | Nothing => pure (Rejected "stmt buffer alloc failed")
      Just schemaBuf <- listToBuffer schemaWire
        | Nothing => pure (Rejected "schema buffer alloc failed")
      Just skBuf     <- listToBuffer sk
        | Nothing => pure (Rejected "sk buffer alloc failed")
      Just outBuf    <- newBuffer (cast attestationTokenSize)
        | Nothing => pure (Rejected "out buffer alloc failed")
      let stmtLen   : Int = cast (length stmtWire)
      let schemaLen : Int = cast (length schemaWire)
      let outCap    : Int = cast attestationTokenSize
      rc <- primIO (prim__vclutVerifyWire
        stmtBuf stmtLen schemaBuf schemaLen skBuf outBuf outCap)
      if rc < 0
        then pure (Rejected
          "Tier-2 backend Rejected (fail-closed): no certified level")
        else case intToSafetyLevel (cast rc) of
          Nothing  => pure (Rejected
            "Tier-2 backend returned out-of-range level — defensive Reject")
          Just lvl => do
            token <- bufferToList outBuf (cast attestationTokenSize)
            pure (Verified lvl token)
