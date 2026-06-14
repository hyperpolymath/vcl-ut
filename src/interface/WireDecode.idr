-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Interface — Wire Decoder (P5b step 2, vcl-ut#25)
|||
||| The certified half of the hypatia<->verisim marshalling seam. The
||| trusted Rust parser (P5a, #26) and its codec (P5b step 1, #28)
||| serialise a `Statement` to the v1 wire format normatively specified
||| in `src/interface/parse/WIRE-FORMAT.adoc`. This module decodes that
||| *identical* byte stream into `Grammar.idr`'s certified `Statement`.
|||
||| Posture (matches the SPARK-grade Rust side):
|||   * `%default total` — every function is machine-checked total.
|||   * ZERO proof-escape: no believe_me / postulate / assert_* /
|||     idris_crash / sorry anywhere. The totality is structural, not
|||     asserted.
|||   * Bounds-checked, no partial primitive: every malformed input is a
|||     typed `WireErr`, never a crash (the Idris analogue of the Rust
|||     decoder's `Result<_, WireError>` totality contract).
|||
||| Every definition is `public export`: the cross-language conformance
||| proofs in `WireConformance` are `Refl`s, so the decoder must reduce
||| transparently at compile time on concrete Rust-emitted bytes.
|||
||| Totality strategy. The grammar is mutually recursive (Expr embeds
||| Statement via Subquery; Statement embeds Expr). A binary parser over
||| a finite byte list is not structurally recursive on the input, so
||| recursion is bounded by *fuel*: a `Nat` that strictly decreases on
||| every descent into a sub-node. Every node's encoding begins with at
||| least one discriminant byte, so the node count of any stream is <=
||| its byte length; initialising fuel to the input length therefore
||| never spuriously exhausts on a well-formed stream, and the recursion
||| is structurally terminating on the fuel `Nat`. The recursion-bearing
||| list element decoders are inlined into the `mutual` block so the
||| size-change totality analysis sees the fuel-decreasing edges
||| directly (a higher-order vector combinator would hide them).
|||
||| Type slots. `Grammar.Expr` carries a `VqlType` at every node; the
||| wire format omits it (the parser does syntax only — see
||| WIRE-FORMAT.adoc). The decoder fills `TAny`, exactly the grammar's
||| documented "unresolved type before type checking"; the 10-level
||| checker resolves it at Level 2+. Faithful, not a shortcut.
|||
||| Float reconstruction. Idris2 0.8.0 exposes no pure, bit-exact
||| `Bits64 -> Double`. A finite IEEE-754 value is reconstructed by
||| exact power-of-two scaling (repeated *2.0 / /2.0, which is exact in
||| IEEE until over/underflow, matching the hardware), so ALL finite
||| values — including subnormals and f64::MIN/MAX — and both
||| infinities round-trip bit-exactly. A NaN bit-pattern decodes to *a*
||| NaN (0.0/0.0); the NaN *payload* is not preserved across the Idris
||| `Double` boundary. This single limitation is DISCLOSED here and in
||| WIRE-FORMAT.adoc rather than papered over: every consumer agrees
||| "this is NaN", the semantically meaningful invariant; the
||| exhaustive bit-exact float witness remains the Rust-side proptest.

module VclTotal.Interface.WireDecode

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import Data.List

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Errors (the Idris mirror of Rust `WireError`)
-- ═══════════════════════════════════════════════════════════════════════

public export
data WireErr
  = BadMagic
  | BadVersion
  | Truncated
  | BadTag String Bits8
  | BadBool Bits8
  | BadUtf8
  | LengthOverflow
  | TrailingBytes
  | OutOfFuel

public export
Show WireErr where
  show BadMagic        = "bad magic (not a VCLW stream)"
  show BadVersion      = "unsupported wire version"
  show Truncated       = "truncated input"
  show (BadTag ty t)   = "bad " ++ ty ++ " discriminant " ++ show t
  show (BadBool b)     = "bad bool byte " ++ show b
  show BadUtf8         = "invalid UTF-8 in string"
  show LengthOverflow  = "length/count overflow"
  show TrailingBytes   = "trailing bytes after statement"
  show OutOfFuel       = "decoder fuel exhausted (malformed/over-deep stream)"

public export
Eq WireErr where
  BadMagic       == BadMagic       = True
  BadVersion     == BadVersion     = True
  Truncated      == Truncated      = True
  (BadTag a x)   == (BadTag b y)   = a == b && x == y
  (BadBool x)    == (BadBool y)    = x == y
  BadUtf8        == BadUtf8        = True
  LengthOverflow == LengthOverflow = True
  TrailingBytes  == TrailingBytes  = True
  OutOfFuel      == OutOfFuel      = True
  _              == _              = False

||| A parser step: consume a prefix of the remaining bytes, yielding a
||| value and the rest, or a typed failure. Pure and total.
public export
0 Parse : Type -> Type
Parse a = List Bits8 -> Either WireErr (a, List Bits8)

-- ═══════════════════════════════════════════════════════════════════════
-- Primitive readers (fixed width; structural, no fuel needed)
-- ═══════════════════════════════════════════════════════════════════════

||| Split exactly `n` bytes off the front. Structural recursion on `n`.
public export
takeN : Nat -> List Bits8 -> Either WireErr (List Bits8, List Bits8)
takeN Z      bs        = Right ([], bs)
takeN (S _)  []        = Left Truncated
takeN (S k)  (b :: bs) = do (hd, tl) <- takeN k bs
                            Right (b :: hd, tl)

public export
byte : Parse Bits8
byte []        = Left Truncated
byte (b :: bs) = Right (b, bs)

||| Little-endian unsigned value of a byte list (b0 = least significant).
public export
leNat : List Bits8 -> Integer
leNat = go 0 1
  where
    go : Integer -> Integer -> List Bits8 -> Integer
    go acc _     []        = acc
    go acc place (b :: bs) = go (acc + place * cast b) (place * 256) bs

public export
u16le : Parse Integer
u16le inp = do (bs, r) <- takeN 2 inp
               Right (leNat bs, r)

public export
u32le : Parse Integer
u32le inp = do (bs, r) <- takeN 4 inp
               Right (leNat bs, r)

public export
u64le : Parse Integer
u64le inp = do (bs, r) <- takeN 8 inp
               Right (leNat bs, r)

||| u64 as a `Nat` (Grammar uses `Nat` for limit/offset/version/bounds).
public export
u64nat : Parse Nat
u64nat inp = do (v, r) <- u64le inp
                Right (integerToNat v, r)

||| Signed 64-bit two's-complement (Grammar `LitInt` is `Int`).
public export
i64le : Parse Int
i64le inp = do (v, r) <- u64le inp
               let s = if v >= 9223372036854775808
                         then v - 18446744073709551616
                         else v
               Right (cast s, r)

-- ── IEEE-754 binary64 reconstruction (exact for finite + infinities) ──

public export
twoPow : Nat -> Double
twoPow Z     = 1.0
twoPow (S k) = 2.0 * twoPow k

||| Multiply by 2 exactly `k` times (exact in IEEE until overflow→inf,
||| which is the correct binary64 behaviour).
public export
scaleUp : Nat -> Double -> Double
scaleUp Z     x = x
scaleUp (S k) x = scaleUp k (x * 2.0)

||| Halve exactly `k` times — exact in IEEE including gradual underflow
||| (division by two never rounds), so subnormals reconstruct exactly.
public export
scaleDown : Nat -> Double -> Double
scaleDown Z     x = x
scaleDown (S k) x = scaleDown k (x / 2.0)

||| Reconstruct the binary64 denoted by an exponent-relative integer
||| mantissa: `m * 2^e`, exactly, via power-of-two scaling only.
public export
ldexpExact : Integer -> Integer -> Double
ldexpExact m e =
  if e >= 0
    then scaleUp   (integerToNat e)          (cast m)
    else scaleDown (integerToNat (negate e)) (cast m)

||| Decode 8 little-endian bytes as binary64. Total. Bit-exact for all
||| finite values and both infinities; NaN payload not preserved
||| (decodes to a NaN) — disclosed (module header / WIRE-FORMAT.adoc).
public export
f64le : Parse Double
f64le inp = do
  (bs, r) <- takeN 8 inp
  let bits = leNat bs
  let sign = (bits `div` 9223372036854775808) `mod` 2
  let expo = (bits `div` 4503599627370496) `mod` 2048
  let mant = bits `mod` 4503599627370496
  let mag  : Double
      mag  = if expo == 2047
               then (if mant == 0
                       then 1.0 / 0.0                       -- +inf
                       else 0.0 / 0.0)                      -- NaN (payload not kept)
               else if expo == 0
                      then ldexpExact mant (-1074)          -- zero / subnormal
                      else ldexpExact (mant + 4503599627370496)
                                      (expo - 1075)         -- normal
  Right (if sign == 1 then negate mag else mag, r)

public export
boolByte : Parse Bool
boolByte inp = do (b, r) <- byte inp
                  case b of
                    0 => Right (False, r)
                    1 => Right (True, r)
                    x => Left (BadBool x)

||| u32 length/count as a `Nat`.
public export
u32count : Parse Nat
u32count inp = do (v, r) <- u32le inp
                  Right (integerToNat v, r)

-- ── UTF-8 string (strict; the Rust side uses core::str::from_utf8) ───

public export
cont : Bits8 -> Maybe Integer
cont b = let v = cast {to=Integer} b in
         if v >= 128 && v < 192 then Just (v - 128) else Nothing

||| Strict, total UTF-8 → codepoint list. Rejects overlong forms,
||| surrogates and out-of-range values exactly as a conformant decoder
||| must. Structural recursion on the byte list.
public export
utf8 : List Bits8 -> Either WireErr (List Char)
utf8 [] = Right []
utf8 (b0 :: rest) =
  let v0 = cast {to=Integer} b0 in
  if v0 < 128
    then do cs <- utf8 rest
            Right (chr (cast v0) :: cs)
    else if v0 < 194 then Left BadUtf8                     -- cont byte / overlong lead
    else if v0 < 224
      then case rest of
             (b1 :: tl) => case cont b1 of
                             Nothing => Left BadUtf8
                             Just c1 =>
                               let cp = (v0 - 192) * 64 + c1 in
                               if cp < 128 then Left BadUtf8
                               else do cs <- utf8 tl
                                       Right (chr (cast cp) :: cs)
             [] => Left Truncated
    else if v0 < 240
      then case rest of
             (b1 :: b2 :: tl) =>
               case (cont b1, cont b2) of
                 (Just c1, Just c2) =>
                   let cp = (v0 - 224) * 4096 + c1 * 64 + c2 in
                   if cp < 2048 then Left BadUtf8
                   else if cp >= 55296 && cp <= 57343 then Left BadUtf8
                   else do cs <- utf8 tl
                           Right (chr (cast cp) :: cs)
                 _ => Left BadUtf8
             _ => Left Truncated
    else if v0 < 245
      then case rest of
             (b1 :: b2 :: b3 :: tl) =>
               case (cont b1, cont b2, cont b3) of
                 (Just c1, Just c2, Just c3) =>
                   let cp = (v0 - 240) * 262144 + c1 * 4096 + c2 * 64 + c3 in
                   if cp < 65536 then Left BadUtf8
                   else if cp > 1114111 then Left BadUtf8
                   else do cs <- utf8 tl
                           Right (chr (cast cp) :: cs)
                 _ => Left BadUtf8
             _ => Left Truncated
    else Left BadUtf8

public export
vstring : Parse String
vstring inp = do
  (n, r0)  <- u32count inp
  (bs, r1) <- takeN n r0
  case utf8 bs of
    Left e   => Left e
    Right cs => Right (pack cs, r1)

-- ═══════════════════════════════════════════════════════════════════════
-- Non-recursive sum decoders (each consumes its discriminant byte)
-- ═══════════════════════════════════════════════════════════════════════

public export
decModality : Parse Modality
decModality inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (Graph, r);      1 => Right (Vector, r)
    2 => Right (Tensor, r);     3 => Right (Semantic, r)
    4 => Right (Document, r);   5 => Right (Temporal, r)
    6 => Right (Provenance, r); 7 => Right (Spatial, r)
    x => Left (BadTag "Modality" x)

public export
decAgent : Parse Agent
decAgent inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (AgEngine, r)
    1 => do (s, r1) <- vstring r; Right (AgProver s, r1)
    2 => Right (AgValidator, r)
    3 => do (s, r1) <- vstring r; Right (AgUser s, r1)
    4 => Right (AgFederation, r)
    x => Left (BadTag "Agent" x)

public export
decFieldRef : Parse FieldRef
decFieldRef inp = do
  (m, r0) <- decModality inp
  (n, r1) <- vstring r0
  Right (MkFieldRef m n, r1)

public export
decCompOp : Parse CompOp
decCompOp inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (Eq, r);   1 => Right (NotEq, r); 2 => Right (Lt, r)
    3 => Right (Gt, r);   4 => Right (LtEq, r);  5 => Right (GtEq, r)
    6 => Right (Like, r); 7 => Right (In, r)
    x => Left (BadTag "CompOp" x)

public export
decLogicOp : Parse LogicOp
decLogicOp inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (And, r); 1 => Right (Or, r); 2 => Right (Not, r)
    x => Left (BadTag "LogicOp" x)

public export
decAggFunc : Parse AggFunc
decAggFunc inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (Count, r); 1 => Right (Sum, r); 2 => Right (Avg, r)
    3 => Right (Min, r);   4 => Right (Max, r)
    x => Left (BadTag "AggFunc" x)

public export
decEpiOp : Parse EpistemicOp
decEpiOp inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (OpKnows, r); 1 => Right (OpBelieves, r)
    2 => Right (OpCommonKnowledge, r)
    x => Left (BadTag "EpistemicOp" x)

public export
decF64Vec : Parse (List Double)
decF64Vec i0 = do
  (n, i1) <- u32count i0
  go n i1
  where
    go : Nat -> Parse (List Double)
    go Z     i = Right ([], i)
    go (S k) i = do (x, i')   <- f64le i
                    (xs, i'') <- go k i'
                    Right (x :: xs, i'')

public export
decLiteral : Parse Literal
decLiteral inp = do
  (t, r) <- byte inp
  case t of
    0 => do (s, r1) <- vstring r;   Right (LitString s, r1)
    1 => do (n, r1) <- i64le r;     Right (LitInt n, r1)
    2 => do (x, r1) <- f64le r;     Right (LitFloat x, r1)
    3 => do (b, r1) <- boolByte r;  Right (LitBool b, r1)
    4 => Right (LitNull, r)
    5 => do (xs, r1) <- decF64Vec r; Right (LitVector xs, r1)
    x => Left (BadTag "Literal" x)

public export
decSource : Parse Source
decSource inp = do
  (t, r) <- byte inp
  case t of
    0 => do (s, r1) <- vstring r; Right (SrcOctad s, r1)
    1 => do (s, r1) <- vstring r; Right (SrcFederation s, r1)
    2 => do (s, r1) <- vstring r; Right (SrcStore s, r1)
    x => Left (BadTag "Source" x)

public export
decEffect : Parse EffectDecl
decEffect inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (EffRead, r);      1 => Right (EffWrite, r)
    2 => Right (EffReadWrite, r); 3 => Right (EffConsume, r)
    x => Left (BadTag "EffectDecl" x)

public export
decVersion : Parse VersionConstraint
decVersion inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (VerLatest, r)
    1 => do (n, r1) <- u64nat r; Right (VerAtLeast n, r1)
    2 => do (n, r1) <- u64nat r; Right (VerExact n, r1)
    3 => do (a, r1) <- u64nat r
            (b, r2) <- u64nat r1
            Right (VerRange a b, r2)
    x => Left (BadTag "VersionConstraint" x)

public export
decLinear : Parse LinearAnnotation
decLinear inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (LinUnlimited, r)
    1 => Right (LinUseOnce, r)
    2 => do (n, r1) <- u64nat r; Right (LinBounded n, r1)
    x => Left (BadTag "LinearAnnotation" x)

public export
decSafety : Parse SafetyLevel
decSafety inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (ParseSafe, r);       1 => Right (SchemaBound, r)
    2 => Right (TypeCompat, r);      3 => Right (NullSafe, r)
    4 => Right (InjectionProof, r);  5 => Right (ResultTyped, r)
    6 => Right (CardinalitySafe, r); 7 => Right (EffectTracked, r)
    8 => Right (TemporalSafe, r);    9 => Right (LinearSafe, r)
    10 => Right (EpistemicSafe, r)
    x => Left (BadTag "SafetyLevel" x)

-- ═══════════════════════════════════════════════════════════════════════
-- Fuel-bounded repetition for NON-recursive elements (total: structural
-- on the count `Nat`; the element decoder is total by its type)
-- ═══════════════════════════════════════════════════════════════════════

public export
decRepeat : Nat -> (Nat -> Parse a) -> Nat -> Parse (List a)
decRepeat _    _ Z     i = Right ([], i)
decRepeat fuel f (S k) i = do
  (x, i')   <- f fuel i
  (xs, i'') <- decRepeat fuel f k i'
  Right (x :: xs, i'')

public export
decVec : Nat -> (Nat -> Parse a) -> Parse (List a)
decVec fuel f inp = do
  (n, r) <- u32count inp
  decRepeat fuel f n r

public export
decOpt : Parse a -> Parse (Maybe a)
decOpt f inp = do
  (t, r) <- byte inp
  case t of
    0 => Right (Nothing, r)
    1 => do (x, r1) <- f r; Right (Just x, r1)
    x => Left (BadTag "option" x)

public export
decOrderItem : Parse (FieldRef, Bool)
decOrderItem i0 = do
  (fr, i1)  <- decFieldRef i0
  (asc, i2) <- boolByte i1
  Right ((fr, asc), i2)

-- ═══════════════════════════════════════════════════════════════════════
-- The mutually-recursive core (fuel strictly decreases on every descent;
-- recursion-bearing list decoders are inlined here so the size-change
-- analysis sees the decreasing edges directly)
-- ═══════════════════════════════════════════════════════════════════════

mutual
  public export
  decExpr : Nat -> Parse Expr
  decExpr Z     _   = Left OutOfFuel
  decExpr (S k) inp = do
    (t, r0) <- byte inp
    case t of
      0 => do (fr, r) <- decFieldRef r0;   Right (EField fr TAny, r)
      1 => do (l, r)  <- decLiteral r0;    Right (ELiteral l TAny, r)
      2 => do (c, r1) <- decCompOp r0
              (a, r2) <- decExpr k r1
              (b, r3) <- decExpr k r2
              Right (ECompare c a b TAny, r3)
      3 => do (lo, r1) <- decLogicOp r0
              (a, r2)  <- decExpr k r1
              (mb, r3) <- decOpt (decExpr k) r2
              Right (ELogic lo a mb TAny, r3)
      4 => do (ag, r1) <- decAggFunc r0
              (e, r2)  <- decExpr k r1
              Right (EAggregate ag e TAny, r2)
      5 => do (s, r) <- vstring r0;        Right (EParam s TAny, r)
      6 => Right (EStar, r0)
      7 => do (st, r) <- decStmt k r0;     Right (ESubquery st, r)
      8 => do (op, r1) <- decEpiOp r0
              (ag, r2) <- decAgent r1
              (e, r3)  <- decExpr k r2
              Right (EEpistemic op ag e TAny, r3)
      9 => do (ag, r1) <- decAgent r0
              (p, r2)  <- decExpr k r1
              (b, r3)  <- decExpr k r2
              Right (EAnnounce ag p b TAny, r3)
      x => Left (BadTag "Expr" x)

  public export
  decSelectItem : Nat -> Parse SelectItem
  decSelectItem Z     _   = Left OutOfFuel
  decSelectItem (S k) inp = do
    (t, r0) <- byte inp
    case t of
      0 => do (fr, r) <- decFieldRef r0; Right (SelField fr, r)
      1 => do (m, r)  <- decModality r0; Right (SelModality m, r)
      2 => do (ag, r1) <- decAggFunc r0
              (e, r2)  <- decExpr k r1
              Right (SelAggregate ag e, r2)
      3 => Right (SelStar, r0)
      x => Left (BadTag "SelectItem" x)

  public export
  decSelectItemsN : Nat -> Nat -> Parse (List SelectItem)
  decSelectItemsN _    Z     i = Right ([], i)
  decSelectItemsN fuel (S c) i = do
    (x, i')   <- decSelectItem fuel i
    (xs, i'') <- decSelectItemsN fuel c i'
    Right (x :: xs, i'')

  public export
  decSelectItemVec : Nat -> Parse (List SelectItem)
  decSelectItemVec fuel i = do
    (n, r) <- u32count i
    decSelectItemsN fuel n r

  public export
  decEpiReq : Nat -> Parse EpistemicRequirement
  decEpiReq Z     _   = Left OutOfFuel
  decEpiReq (S k) inp = do
    (t, r0) <- byte inp
    case t of
      0 => do (a, r1) <- decAgent r0
              (e, r2) <- decExpr k r1
              Right (EpReqKnows a e, r2)
      1 => do (a, r1) <- decAgent r0
              (e, r2) <- decExpr k r1
              Right (EpReqBelieves a e, r2)
      2 => do (e, r1) <- decExpr k r0
              Right (EpReqCommon e, r1)
      3 => do (a, r1) <- decAgent r0
              (b, r2) <- decAgent r1
              (e, r3) <- decExpr k r2
              Right (EpReqEntails a b e, r3)
      x => Left (BadTag "EpistemicRequirement" x)

  public export
  decEpiReqsN : Nat -> Nat -> Parse (List EpistemicRequirement)
  decEpiReqsN _    Z     i = Right ([], i)
  decEpiReqsN fuel (S c) i = do
    (x, i')   <- decEpiReq fuel i
    (xs, i'') <- decEpiReqsN fuel c i'
    Right (x :: xs, i'')

  public export
  decEpiReqVec : Nat -> Parse (List EpistemicRequirement)
  decEpiReqVec fuel i = do
    (n, r) <- u32count i
    decEpiReqsN fuel n r

  public export
  decProof : Nat -> Parse ProofClause
  decProof Z     _   = Left OutOfFuel
  decProof (S k) inp = do
    (t, r0) <- byte inp
    case t of
      0 => Right (ProofAttached, r0)
      1 => do (s, r) <- vstring r0;    Right (ProofWitness s, r)
      2 => do (e, r) <- decExpr k r0;  Right (ProofAssert e, r)
      x => Left (BadTag "ProofClause" x)

  public export
  decEpiClause : Nat -> Parse EpistemicClause
  decEpiClause Z     _   = Left OutOfFuel
  decEpiClause (S k) inp = do
    (ags, r1) <- decVec k (\_, x => decAgent x) inp
    (rqs, r2) <- decEpiReqVec k r1
    Right (EpClause ags rqs, r2)

  public export
  decStmt : Nat -> Parse Statement
  decStmt Z     _   = Left OutOfFuel
  decStmt (S k) inp = do
    (sel, r1)  <- decSelectItemVec k inp
    (src, r2)  <- decSource r1
    (wc,  r3)  <- decOpt (decExpr k) r2
    (gb,  r4)  <- decVec k (\_, x => decFieldRef x) r3
    (hav, r5)  <- decOpt (decExpr k) r4
    (ob,  r6)  <- decVec k (\_, x => decOrderItem x) r5
    (lim, r7)  <- decOpt (\x => u64nat x) r6
    (off, r8)  <- decOpt (\x => u64nat x) r7
    (pf,  r9)  <- decOpt (decProof k) r8
    (ef,  r10) <- decOpt (\x => decEffect x) r9
    (vc,  r11) <- decOpt (\x => decVersion x) r10
    (la,  r12) <- decOpt (\x => decLinear x) r11
    (ep,  r13) <- decOpt (decEpiClause k) r12
    (lvl, r14) <- decSafety r13
    -- `verb` is not carried on the wire (S1): decode defaults to VSelect, the
    -- read sense, keeping the byte format and the WireConformance Refls stable.
    Right (MkStatement sel src wc gb hav ob lim off pf ef vc la ep lvl VSelect, r14)

-- ═══════════════════════════════════════════════════════════════════════
-- Header + entry point
-- ═══════════════════════════════════════════════════════════════════════

public export
magic : List Bits8
magic = [86, 67, 76, 87]   -- "VCLW"

||| Decode a v1 wire stream into the certified `Statement`. Total: every
||| input yields `Right stmt` or a typed `Left WireErr`, never a crash.
||| Fuel is the input length — a sound over-approximation of the node
||| count (every node costs >= 1 discriminant byte), so a well-formed
||| stream never exhausts it.
public export
fromWire : List Bits8 -> Either WireErr Statement
fromWire input = do
  (m, r0) <- takeN 4 input
  if m /= magic then Left BadMagic else Right ()
  (ver, r1) <- u16le r0
  if ver /= 1 then Left BadVersion else Right ()
  (stmt, r2) <- decStmt (length input) r1
  if length r2 /= 0 then Left TrailingBytes else Right stmt

-- ═══════════════════════════════════════════════════════════════════════
-- P5c: OctadSchema decoder (schema marshalling for the recompute tier)
--
-- `VqlType` is recursive (TList/TNull/TRecord/TKnows/TBelieves/
-- TCommonKnowledge nest VqlType), so its decoder is fuel-bounded
-- exactly like `Expr`; the recursion-bearing record-field list is
-- inlined into the same `mutual` block so the size-change analysis
-- sees the fuel-decreasing edge directly. `VqlType` recursion is
-- independent of `Statement`/`Expr` (it only nests `VqlType` and the
-- non-recursive `Agent`), so this is its own block. Totality is
-- structural, ZERO proof-escape, identical posture to the Statement
-- decoder. The schema stream has its own magic (`VCLS`) so a
-- schema/statement mix-up is a hard `BadMagic`.
-- ═══════════════════════════════════════════════════════════════════════

mutual
  public export
  decVqlType : Nat -> Parse VqlType
  decVqlType Z     _   = Left OutOfFuel
  decVqlType (S k) inp = do
    (t, r0) <- byte inp
    case t of
      0  => Right (TString, r0)
      1  => Right (TInt, r0)
      2  => Right (TFloat, r0)
      3  => Right (TBool, r0)
      4  => Right (TBytes, r0)
      5  => do (n, r) <- u64nat r0; Right (TVector n, r)
      6  => Right (TTimestamp, r0)
      7  => Right (THash, r0)
      8  => do (v, r) <- decVqlType k r0; Right (TList v, r)
      9  => do (fs, r) <- decVqlRecVec k r0; Right (TRecord fs, r)
      10 => Right (TOctad, r0)
      11 => do (v, r) <- decVqlType k r0; Right (TNull v, r)
      12 => Right (TAny, r0)
      13 => do (a, r1) <- decAgent r0
               (v, r2) <- decVqlType k r1
               Right (TKnows a v, r2)
      14 => do (a, r1) <- decAgent r0
               (v, r2) <- decVqlType k r1
               Right (TBelieves a v, r2)
      15 => do (v, r) <- decVqlType k r0; Right (TCommonKnowledge v, r)
      x  => Left (BadTag "VqlType" x)

  public export
  decVqlRecN : Nat -> Nat -> Parse (List (String, VqlType))
  decVqlRecN _    Z     i = Right ([], i)
  decVqlRecN fuel (S c) i = do
    (nm, i1)  <- vstring i
    (vt, i2)  <- decVqlType fuel i1
    (xs, i3)  <- decVqlRecN fuel c i2
    Right ((nm, vt) :: xs, i3)

  public export
  decVqlRecVec : Nat -> Parse (List (String, VqlType))
  decVqlRecVec fuel i = do
    (n, r) <- u32count i
    decVqlRecN fuel n r

public export
decFieldDef : Nat -> Parse FieldDef
decFieldDef fuel inp = do
  (nm, r1) <- vstring inp
  (ty, r2) <- decVqlType fuel r1
  (nl, r3) <- boolByte r2
  (ix, r4) <- boolByte r3
  Right (MkFieldDef nm ty nl ix, r4)

public export
decFieldDefsN : Nat -> Nat -> Parse (List FieldDef)
decFieldDefsN _    Z     i = Right ([], i)
decFieldDefsN fuel (S c) i = do
  (x, i')   <- decFieldDef fuel i
  (xs, i'') <- decFieldDefsN fuel c i'
  Right (x :: xs, i'')

public export
decFieldDefVec : Nat -> Parse (List FieldDef)
decFieldDefVec fuel i = do
  (n, r) <- u32count i
  decFieldDefsN fuel n r

public export
decModalitySchema : Nat -> Parse ModalitySchema
decModalitySchema fuel inp = do
  (m, r1)  <- decModality inp
  (fs, r2) <- decFieldDefVec fuel r1
  Right (MkModalitySchema m fs, r2)

public export
schemaMagic : List Bits8
schemaMagic = [86, 67, 76, 83]   -- "VCLS"

||| Decode a v1 `VCLS` wire stream into the certified `OctadSchema`.
||| Total: every input yields `Right` or a typed `Left WireErr`, never
||| a crash. Fuel is the input length (sound: every node costs >= 1
||| discriminant byte). The 8 modality schemas are in `Schema.idr`
||| record order; no count prefix (fixed arity).
public export
fromWireSchema : List Bits8 -> Either WireErr OctadSchema
fromWireSchema input = do
  (m, r0) <- takeN 4 input
  if m /= schemaMagic then Left BadMagic else Right ()
  (ver, r1) <- u16le r0
  if ver /= 1 then Left BadVersion else Right ()
  let f = length input
  (gr, r2)  <- decModalitySchema f r1
  (ve, r3)  <- decModalitySchema f r2
  (te, r4)  <- decModalitySchema f r3
  (se, r5)  <- decModalitySchema f r4
  (do_, r6) <- decModalitySchema f r5
  (tm, r7)  <- decModalitySchema f r6
  (pr, r8)  <- decModalitySchema f r7
  (sp, r9)  <- decModalitySchema f r8
  if length r9 /= 0 then Left TrailingBytes
    else Right (MkOctadSchema gr ve te se do_ tm pr sp)
