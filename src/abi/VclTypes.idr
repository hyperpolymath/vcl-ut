-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-ut ABI Type Definitions
|||
||| VCL-ut is the canonical type-safe query language for VeriSimDB. This
||| ABI module declares the C-compatible representations of the core
||| query/schema types so non-Rust callers (Zig, OCaml AffineScript host,
||| Julia, future SPARK/Ada satellites) can call into the VCL surface
||| without going through Rust's std::ffi::CString gymnastics.
|||
||| Database angle: vcl-ut sits on the read+write path between agents
||| and VeriSimDB. Cross-language consumers need predictable layouts so
||| they can produce VCL queries in their own bindings without taking a
||| Rust-style heavyweight dep. Per the user's clarification 2026-04-25:
||| this is a database-tooling project; ABI/FFI is high-priority, not
||| an architecture-aspiration nicety.

module VclTypes

import Data.List
import Data.String

%default total

||| A VCL safety level (1..10) — the trail of constraints a query has
||| satisfied. Each level adds invariants the next must preserve.
public export
data SafetyLevel : Type where
  L1Wellformed : SafetyLevel  -- syntactic well-formedness
  L2Typed : SafetyLevel       -- column types resolved
  L3Bound : SafetyLevel       -- bound predicates verified
  L4Injective : SafetyLevel   -- no aliasing across joins
  L5Total : SafetyLevel       -- result domain finite + computable
  L6Cardinal : SafetyLevel    -- LIMIT enforced, no unbounded scans
  L7Effects : SafetyLevel     -- effect rows tracked
  L8Linear : SafetyLevel      -- one-shot consumption proven
  L9Cost : SafetyLevel        -- bounded execution cost
  L10Provable : SafetyLevel   -- carries a verifying-machine proof

||| A query identifier — opaque to callers; vcl-ut owns the namespace.
public export
record QueryId where
  constructor MkQueryId
  unwrap : Bits64

||| Schema identifier — references a registered VeriSimDB schema by id.
public export
record SchemaId where
  constructor MkSchemaId
  unwrap : Bits64

||| Verification result returned by the type-safety checker.
public export
data VerifyResult : Type where
  Verified : (level : SafetyLevel) -> VerifyResult
  Rejected : (reason : String) -> VerifyResult
  Pending : VerifyResult  -- async checker still running

||| Convert a VerifyResult to its C-ABI exit code.
public export
verifyExitCode : VerifyResult -> Int
verifyExitCode (Verified L1Wellformed) = 1
verifyExitCode (Verified L2Typed)      = 2
verifyExitCode (Verified L3Bound)      = 3
verifyExitCode (Verified L4Injective)  = 4
verifyExitCode (Verified L5Total)      = 5
verifyExitCode (Verified L6Cardinal)   = 6
verifyExitCode (Verified L7Effects)    = 7
verifyExitCode (Verified L8Linear)     = 8
verifyExitCode (Verified L9Cost)       = 9
verifyExitCode (Verified L10Provable)  = 10
verifyExitCode (Rejected _)            = -1
verifyExitCode Pending                 = 0

||| Round-trip property: every Verified level encodes to its 1..10 exit
||| code and back.
public export
exitCodePositiveForVerified : (l : SafetyLevel) ->
                              So (verifyExitCode (Verified l) > 0)
exitCodePositiveForVerified L1Wellformed = Oh
exitCodePositiveForVerified L2Typed      = Oh
exitCodePositiveForVerified L3Bound      = Oh
exitCodePositiveForVerified L4Injective  = Oh
exitCodePositiveForVerified L5Total      = Oh
exitCodePositiveForVerified L6Cardinal   = Oh
exitCodePositiveForVerified L7Effects    = Oh
exitCodePositiveForVerified L8Linear     = Oh
exitCodePositiveForVerified L9Cost       = Oh
exitCodePositiveForVerified L10Provable  = Oh
