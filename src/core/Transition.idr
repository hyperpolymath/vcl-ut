-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Core Transition — the consonance lifecycle verbs (S2).
|||
||| MERGE / SPLIT / NORMALISE are the multi-subject / result-less consonance
||| transitions (VeriSimDB lifecycle: … → Merged/Split → … → Normalised). They
||| do NOT fit `record Statement` (single `source`, always result-returning),
||| so they live here as a SEPARATE `Transition` type. `record Statement` and
||| every L0..L10 predicate stay byte-identical — S2 reopens ZERO existing
||| proofs (the only Grammar edit is the tag-only `Verb` extension).
|||
||| What S2 certifies (HONEST, PARTIAL — see VERIFICATION-STANCE.adoc §S2):
|||   * structural identity-distinctness (no self-merge; distinct SPLIT outputs)
|||   * injection-safety of the evidence clause (L4 polarity: NO raw string lit)
|||   * type-compatibility of the evidence clause (reuses the single-source-of-
|||     truth `Decide.whereComparisonsCompatible` on the evidence `Expr`)
||| Result-less NORMALISE genuinely OMITS L5 ResultTyped / L6 CardinalitySafe
||| (it has no result set) — they are absent, NOT vacuously passed.
|||
||| DISCLOSED-OWED (recorded, fail-closed, NEVER faked): provenance-descent of
||| a merged identity, engine-liveness of merge inputs, modality-presence for
||| NORMALISE, and identity-vs-location (`SubjectRef` is an identity handle, not
||| yet checked against the provenance graph).

module VclTotal.Core.Transition

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import VclTotal.Core.Schema
import VclTotal.Core.Decide

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Subjects + repair justification
-- ═══════════════════════════════════════════════════════════════════════

||| A consonance-subject identity handle (the octad / identity UUID).
||| DELIBERATELY distinct from `Source` (a read-LOCATION): two identities in
||| the same store are different subjects, which `Source` equality could not
||| tell apart. (Identity-vs-location beyond handle equality is OWED.)
public export
data SubjectRef = MkSubjectRef String

public export
subjectId : SubjectRef -> String
subjectId (MkSubjectRef s) = s

||| Equality of subjects by identity handle.
public export
subjectEq : SubjectRef -> SubjectRef -> Bool
subjectEq (MkSubjectRef a) (MkSubjectRef b) = a == b

||| The justified repair path for a NORMALISE, mirroring the engine's
||| authority-ranked regenerator (RegenerationStrategy).
public export
data RepairJustification
  = FromAuthoritative Modality   -- regenerate from the authoritative modality
  | MergeModalities              -- merge across modalities
  | UserResolve                  -- escalate to a user decision

-- ═══════════════════════════════════════════════════════════════════════
-- Transitions + the VCL operation sum
-- ═══════════════════════════════════════════════════════════════════════

||| A consonance transition. MERGE/SPLIT carry an optional `evidence` Expr (the
||| consonance condition, e.g. a drift bound) and a requested level; NORMALISE
||| carries its justification by construction (an unjustified normalise is
||| UNREPRESENTABLE).
public export
data Transition
  = TMerge SubjectRef SubjectRef SubjectRef (Maybe Expr) SafetyLevel
      -- ^ MERGE left right INTO into: two DISTINCT inputs → one identity.
  | TSplit SubjectRef SubjectRef SubjectRef (Maybe Expr) SafetyLevel
      -- ^ SPLIT from INTO outL outR: one identity → two DISTINCT outputs.
  | TNormalise SubjectRef RepairJustification SafetyLevel
      -- ^ NORMALISE subject: repair transition, NO result set, justified.

||| Top-level VCL operation: a relational query OR a consonance transition.
public export
data VclOp = Query Statement | Transit Transition

-- ═══════════════════════════════════════════════════════════════════════
-- Field projections
-- ═══════════════════════════════════════════════════════════════════════

public export
transitionEvidence : Transition -> Maybe Expr
transitionEvidence (TMerge _ _ _ ev _) = ev
transitionEvidence (TSplit _ _ _ ev _) = ev
transitionEvidence (TNormalise _ _ _)  = Nothing

public export
transitionLevel : Transition -> SafetyLevel
transitionLevel (TMerge _ _ _ _ lvl) = lvl
transitionLevel (TSplit _ _ _ _ lvl) = lvl
transitionLevel (TNormalise _ _ lvl)  = lvl

||| The verb tag of a transition (for the C ABI / dispatch).
public export
transitionVerb : Transition -> Verb
transitionVerb (TMerge _ _ _ _ _) = VMerge
transitionVerb (TSplit _ _ _ _ _) = VSplit
transitionVerb (TNormalise _ _ _) = VNormalise

-- ═══════════════════════════════════════════════════════════════════════
-- Deciders (reflection style, total)
-- ═══════════════════════════════════════════════════════════════════════

||| Structural identity-distinctness: MERGE's two inputs differ; SPLIT's two
||| outputs differ; NORMALISE is single-subject (trivially distinct).
public export
subjectsDistinct : Transition -> Bool
subjectsDistinct (TMerge l r _ _ _)  = not (subjectEq l r)
subjectsDistinct (TSplit _ ol oR _ _) = not (subjectEq ol oR)
subjectsDistinct (TNormalise _ _ _)   = True

||| Evidence injection-safety — L4 polarity: the evidence embeds NO raw string
||| literal (the canonical injection vector). `Nothing` evidence is safe.
public export
evidenceInjectionSafe : Transition -> Bool
evidenceInjectionSafe t = not (maybe False hasStringLit (transitionEvidence t))

||| Evidence type-compatibility — reuses the single-source-of-truth Statement
||| decider on the evidence `Expr`. `Nothing` evidence is vacuously compatible.
public export
evidenceTypeCompat : Transition -> OctadSchema -> Bool
evidenceTypeCompat t schema = whereComparisonsCompatible (transitionEvidence t) schema

||| S2 admissibility: all the statically-checkable obligations hold.
public export
transitionAdmissible : Transition -> OctadSchema -> Bool
transitionAdmissible t schema =
  subjectsDistinct t && evidenceInjectionSafe t && evidenceTypeCompat t schema

-- ═══════════════════════════════════════════════════════════════════════
-- Certificate + soundness (reflection style — same house pattern as L6..L10)
-- ═══════════════════════════════════════════════════════════════════════

||| Extract the left conjunct of a true `&&` (total, structural).
public export
andTrueLeft : {a, b : Bool} -> (a && b) = True -> a = True
andTrueLeft {a = True}  _   = Refl
andTrueLeft {a = False} prf = absurd prf

||| The S2 transition safety certificate. Carries the genuine admissibility
||| decider (structural distinctness + evidence injection-safety + evidence
||| type-compatibility). NON-vacuous: see `certifiedSubjectsDistinct`.
public export
data TransitionSafe : Transition -> OctadSchema -> Type where
  MkTransitionSafe : transitionAdmissible t schema = True -> TransitionSafe t schema

||| Soundness: the decider reflects exactly the certificate.
public export
transitionAdmissibleSound :
  (t : Transition) -> (schema : OctadSchema) ->
  transitionAdmissible t schema = True -> TransitionSafe t schema
transitionAdmissibleSound _ _ prf = MkTransitionSafe prf

||| A certified transition has structurally-distinct subjects (no self-merge /
||| distinct SPLIT outputs) — proof the certificate is not vacuous. The DEEPER
||| identity-conservation (provenance-descent, engine-liveness) is OWED.
public export
certifiedSubjectsDistinct : {t : Transition} -> {schema : OctadSchema} ->
                            TransitionSafe t schema -> subjectsDistinct t = True
certifiedSubjectsDistinct {t} {schema} (MkTransitionSafe prf) =
  -- `transitionAdmissible t schema` is definitionally
  -- `subjectsDistinct t && (evidenceInjectionSafe t && evidenceTypeCompat t schema)`;
  -- naming the conjuncts forces that reduction during unification.
  andTrueLeft {a = subjectsDistinct t}
              {b = evidenceInjectionSafe t && evidenceTypeCompat t schema} prf

-- ═══════════════════════════════════════════════════════════════════════
-- C ABI: certified transition level
-- ═══════════════════════════════════════════════════════════════════════

||| The achieved certificate level for a transition: the `InjectionProof` rung
||| (4) when admissible, or -1. Mirrors `Checker.certifiedLevel`; routed to
||| from the `Transit` arm of a `VclOp` (NEVER down-cast to the Statement
||| certifier).
public export
certifiedTransitionLevel : Transition -> OctadSchema -> Int
certifiedTransitionLevel t schema =
  if transitionAdmissible t schema then 4 else (-1)
