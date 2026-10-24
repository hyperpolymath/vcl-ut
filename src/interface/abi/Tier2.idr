-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
||| VCL-total Tier-2 Foreign Function Interface (signed attestation)
|||
||| Idris-side bindings to the *honest* C ABI exposed by the Zig shim
||| `ffi/zig/src/lib.zig` (`vclut_verify_wire`), which calls into the
||| Rust crate `ffi/rust/attest` (`vclut_rs_verify`) — see
||| `ffi/rust/attest/ATTESTATION-FORMAT.adoc` for the wire
||| contract, `ffi/zig/include/vclut_ffi.h` for the normative C
||| declarations, and `docs/decisions/0002-ffi-attestation-trust-boundary.adoc`
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
||| `ffi/rust/recompute-wasm`), which trusts neither (1) nor (2)
||| because the consumer re-runs the decision itself. Prefer Tier-1
||| where wasm hosting is available; Tier-2 is the C-ABI fallback.
|||
||| **No proofs.** Like all FFI plumbing, this module contains no
||| theorems — its safety properties live in the Tier-2 Rust crate's
||| tests (`ffi/rust/attest/src/lib.rs::tests` — roundtrip + 5
||| tamper variants + fail-closed + C-ABI) and in the Zig shim's
||| precondition tests. It is *not* in the Idris2 proof corpus
||| (`vclut-core.ipkg`); it is typechecked by its own package
||| (`vclut-abi.ipkg`) in `.github/workflows/abi-gate.yml`. See
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
|||     Level 0 (`ParseSafe`) is a genuine `Verified`, not a pending state:
|||     the level→verdict mapping below is the wire entry point's, and on
|||     that entry point `0` carries a token. (`vclut_verify_query`, by
|||     contrast, uses `0` for *Pending* — the two must not share a
|||     mapping.)
|||   * `Rejected reason` — fail-closed; the certifier did not establish
|||     a level (decode failure, malformed input, level outside
|||     `0..=10`, a NULL pointer, a bad seed length, or insufficient out
|||     capacity). Token is NOT emitted. `reason` is the backend's own
|||     message from `vclut_last_error` where one was set.
public export
data Tier2Verdict : Type where
  Verified : SafetyLevel -> List Bits8 -> Tier2Verdict
  Rejected : String -> Tier2Verdict

||| The fixed Ed25519 attestation token width (`level : 1 byte`
||| + `signature : 64 bytes`).
public export
attestationTokenSize : Nat
attestationTokenSize = 65

||| Ed25519 seed/secret-key byte width. Transmitted to C explicitly so the
||| backend can reject a mismatch instead of reading past the buffer.
public export
ed25519SeedSize : Nat
ed25519SeedSize = 32

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI declarations
-- ═══════════════════════════════════════════════════════════════════════

||| The honest Tier-2 entry point. Bound to the Zig shim
||| `vclut_verify_wire` in `ffi/zig/src/lib.zig`, which calls
||| `vclut_rs_verify` (`ffi/rust/attest/src/lib.rs`).
|||
||| ABI (normative copy: `ffi/zig/include/vclut_ffi.h`):
|||
|||   ```c
|||   int32_t vclut_verify_wire(
|||       const uint8_t* stmt_ptr,   size_t stmt_len,
|||       const uint8_t* schema_ptr, size_t schema_len,
|||       const uint8_t* sk_ptr,     size_t sk_len,   /* sk_len == 32 */
|||       uint8_t*       out_ptr,    size_t out_cap   /* >= 65 */
|||   );
|||   ```
|||
||| Returns `0..=10` on success (writes the 65-byte attestation to
||| `out_ptr`), `-1` on Reject (no write). Pointers must each describe
||| a valid range of the stated length; the function never reads or
||| writes outside the documented spans, and rejects NULL rather than
||| dereferencing it. See the Rust crate's `Safety` comment and
||| `ffi/zig/src/lib.zig` for the precise contract.
|||
||| Lengths are `Bits64`, matching `size_t` on every 64-bit target this
||| repo builds — deliberately not `Int`, which Idris2 maps to C `int`
||| (32-bit) and would silently truncate a wire buffer over 2^31 bytes.
%foreign "C:vclut_verify_wire, libvclut_ffi"
export
prim__vclutVerifyWire :
  Buffer -> Bits64 ->     -- stmt
  Buffer -> Bits64 ->     -- schema
  Buffer -> Bits64 ->     -- 32-byte Ed25519 seed
  Buffer -> Bits64 ->     -- out + cap
  PrimIO Int

||| Last error message from the shim, for a `-1` result. Empty when no
||| error is pending. The pointer is thread-local and owned by the
||| library: copy before the next FFI call.
%foreign "C:vclut_last_error, libvclut_ffi"
export
prim__vclutLastError : PrimIO String

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

||| Read `fuel` bytes from `buf` starting at index 0, in order.
|||
||| Structural recursion on the `Nat` fuel, so the totality checker
||| accepts it directly (proof-corpus gate: zero proof-escape). Callers
||| pass a constant — `attestationTokenSize` — so no `Int`→`Nat`
||| conversion (which is where a `partial`/`assert_total` would creep in)
||| is needed.
private
readBytes : Buffer -> Nat -> IO (List Bits8)
readBytes buf fuel = go fuel 0 []
  where
    go : Nat -> Int -> List Bits8 -> IO (List Bits8)
    go Z     _ acc = pure (reverse acc)
    go (S k) i acc = do
      b <- getBits8 buf i
      go k (i + 1) (b :: acc)

||| The backend's reason for a reject, with a fixed fallback for the
||| (defensive) case where the shim set nothing.
private
rejectReason : IO String
rejectReason = do
  msg <- primIO prim__vclutLastError
  pure (if msg == ""
          then "Tier-2 backend Rejected (fail-closed): no certified level"
          else msg)

-- ═══════════════════════════════════════════════════════════════════════
-- Safe public wrapper
-- ═══════════════════════════════════════════════════════════════════════

||| Verify a wire-marshalled `(Statement, OctadSchema)` pair via the
||| Tier-2 signed-attestation backend. On success returns
||| `Verified level token` with the 65-byte attestation; on any
||| reject path returns `Rejected reason` with the backend's cause.
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
|||     malformed input, level outside `0..=10`, NULL argument, capacity
|||     too small) — with the backend's own message where it set one;
|||   * a return value outside `0..=10` (defensive — the backend's
|||     contract already constrains this, and the Zig shim rejects it,
|||     but we re-check on the way out).
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
      let stmtLen   : Bits64 = cast (length stmtWire)
      let schemaLen : Bits64 = cast (length schemaWire)
      let skLen     : Bits64 = cast ed25519SeedSize
      let outCap    : Bits64 = cast attestationTokenSize
      rc <- primIO (prim__vclutVerifyWire
        stmtBuf stmtLen schemaBuf schemaLen skBuf skLen outBuf outCap)
      if rc < 0
        then Rejected <$> rejectReason
        else case intToSafetyLevel (cast rc) of
          Nothing  => pure (Rejected
            "Tier-2 backend returned out-of-range level — defensive Reject")
          Just lvl => do
            token <- readBytes outBuf attestationTokenSize
            pure (Verified lvl token)
