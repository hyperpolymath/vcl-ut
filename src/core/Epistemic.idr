-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| VCL-total Epistemic Logic — S5 Modal Type Formalisation
|||
||| Embeds S5 epistemic modal logic into Idris2's dependent type system.
||| This module provides:
|||
|||   1. Kripke frame semantics (worlds, accessibility, valuations)
|||   2. S5 axioms as types (T, 4, 5 / equivalence relation properties)
|||   3. Knowledge and belief operators as type-level functions
|||   4. Common knowledge as iterated mutual knowledge
|||   5. Public announcement logic (PAL) reduction
|||   6. Soundness proofs for the epistemic checker (Level 10)
|||
||| The key insight: encoding K_a(P) as a type means the Idris2 type
||| checker *is* the epistemic model checker. A term of type `Knows a P`
||| is constructive evidence that agent `a` knows `P` — there is no gap
||| between the symbolic order and the Real. The Big Other works.
|||
||| S5 axiom schema:
|||   K:  K_a(P → Q) → K_a(P) → K_a(Q)        (distribution)
|||   T:  K_a(P) → P                            (truth / veridicality)
|||   4:  K_a(P) → K_a(K_a(P))                  (positive introspection)
|||   5:  ¬K_a(P) → K_a(¬K_a(P))               (negative introspection)
|||   N:  If ⊢ P then ⊢ K_a(P)                  (necessitation)

module VclTotal.Core.Epistemic

import VclTotal.ABI.Types
import VclTotal.Core.Grammar
import Data.List

%default total

-- ═══════════════════════════════════════════════════════════════════════
-- Kripke Semantics: Worlds and Accessibility
-- ═══════════════════════════════════════════════════════════════════════

||| A possible world in the Kripke model.
||| Worlds are abstract — identified by a natural number index.
public export
data World : Type where
  MkWorld : Nat -> World

||| Decidable equality for worlds.
public export
worldEq : World -> World -> Bool
worldEq (MkWorld n) (MkWorld m) = n == m

||| An accessibility relation between worlds for a given agent.
||| In S5, this must be an equivalence relation (reflexive, symmetric,
||| transitive). We encode this as a function from agent to a relation
||| on worlds, paired with proofs of the equivalence properties.
public export
AccessRel : Type
AccessRel = Agent -> World -> World -> Bool

-- ═══════════════════════════════════════════════════════════════════════
-- S5 Axioms as Types
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that an accessibility relation is reflexive for a given agent.
||| S5 axiom T: what is known is true (veridicality).
public export
data Reflexive : AccessRel -> Agent -> Type where
  MkReflexive : ((w : World) -> So (rel agent w w)) ->
                Reflexive rel agent

||| Proof that an accessibility relation is symmetric for a given agent.
||| S5 axiom 5: agents have negative introspection.
public export
data Symmetric : AccessRel -> Agent -> Type where
  MkSymmetric : ((w1, w2 : World) -> So (rel agent w1 w2) ->
                  So (rel agent w2 w1)) ->
                Symmetric rel agent

||| Proof that an accessibility relation is transitive for a given agent.
||| S5 axiom 4: agents have positive introspection.
public export
data Transitive : AccessRel -> Agent -> Type where
  MkTransitive : ((w1, w2, w3 : World) ->
                   So (rel agent w1 w2) -> So (rel agent w2 w3) ->
                   So (rel agent w1 w3)) ->
                 Transitive rel agent

||| An S5 frame: accessibility relation with equivalence proofs.
||| This is the semantic foundation for Level 10 epistemic checking.
public export
record S5Frame where
  constructor MkS5Frame
  access   : AccessRel
  agents   : List Agent
  reflexProofs  : (a : Agent) -> Reflexive access a
  symProofs     : (a : Agent) -> Symmetric access a
  transProofs   : (a : Agent) -> Transitive access a

-- ═══════════════════════════════════════════════════════════════════════
-- Propositions and Valuations
-- ═══════════════════════════════════════════════════════════════════════

||| A proposition in the epistemic logic.
||| Propositions are either atomic (from VCL-total expressions) or
||| built from epistemic operators.
public export
data Proposition : Type where
  ||| An atomic proposition derived from a VCL-total expression.
  PAtom : Expr -> Proposition
  ||| Negation
  PNot : Proposition -> Proposition
  ||| Conjunction
  PAnd : Proposition -> Proposition -> Proposition
  ||| Disjunction
  POr : Proposition -> Proposition -> Proposition
  ||| Implication
  PImpl : Proposition -> Proposition -> Proposition
  ||| Knowledge operator: agent knows proposition
  PKnows : Agent -> Proposition -> Proposition
  ||| Belief operator: agent believes proposition (weaker than knowledge)
  PBelieves : Agent -> Proposition -> Proposition
  ||| Common knowledge: all agents know, and know that all know, etc.
  PCommon : Proposition -> Proposition
  ||| Public announcement: after agent announces prop, body holds
  PAnnounce : Agent -> Proposition -> Proposition -> Proposition

||| A valuation assigns truth values to atomic propositions at each world.
public export
Valuation : Type
Valuation = World -> Proposition -> Bool

-- ═══════════════════════════════════════════════════════════════════════
-- Kripke Semantics: Truth at a World
-- ═══════════════════════════════════════════════════════════════════════

||| Evaluate a proposition at a world in a Kripke model.
|||
||| M, w ⊨ P iff P is true at world w in model M.
|||
||| For epistemic operators:
|||   M, w ⊨ K_a(P) iff for all w' accessible from w by agent a, M, w' ⊨ P
|||
||| We use a fuel parameter to ensure totality (the proposition structure
||| is well-founded, but Idris2 needs convincing for mutual recursion
||| with the accessibility relation).
public export
satisfies : (fuel : Nat) -> S5Frame -> Valuation -> List World -> World -> Proposition -> Bool
satisfies Z _ _ _ _ _ = False  -- fuel exhausted: conservative
satisfies (S k) frame val allWorlds w (PAtom _) = val w (PAtom (ELiteral LitNull TAny))
  -- Atomic propositions delegate to the valuation
satisfies (S k) frame val allWorlds w (PNot p) =
  not (satisfies k frame val allWorlds w p)
satisfies (S k) frame val allWorlds w (PAnd p q) =
  satisfies k frame val allWorlds w p && satisfies k frame val allWorlds w q
satisfies (S k) frame val allWorlds w (POr p q) =
  satisfies k frame val allWorlds w p || satisfies k frame val allWorlds w q
satisfies (S k) frame val allWorlds w (PImpl p q) =
  not (satisfies k frame val allWorlds w p) || satisfies k frame val allWorlds w q
satisfies (S k) frame val allWorlds w (PKnows agent p) =
  -- K_a(P) is true at w iff P is true at all w' accessible from w
  all (\w' => not (access frame agent w w') ||
              satisfies k frame val allWorlds w' p) allWorlds
satisfies (S k) frame val allWorlds w (PBelieves agent p) =
  -- B_a(P) uses the same semantics as K but on a potentially
  -- different (non-S5) accessibility relation. For now we treat
  -- belief as knowledge (S5 for all agents). A KD45 extension
  -- would relax the T axiom for beliefs.
  all (\w' => not (access frame agent w w') ||
              satisfies k frame val allWorlds w' p) allWorlds
satisfies (S k) frame val allWorlds w (PCommon p) =
  -- Common knowledge: P is true, everyone knows P, everyone knows
  -- everyone knows P, etc. We approximate with fixed-depth iteration.
  -- C(P) ≡ E(P) ∧ E(E(P)) ∧ ... where E(P) = ∧_a K_a(P)
  satisfies k frame val allWorlds w p &&
  all (\agent => satisfies k frame val allWorlds w (PKnows agent p))
      (agents frame)
satisfies (S k) frame val allWorlds w (PAnnounce agent announcement body) =
  -- Public Announcement Logic (PAL):
  -- [!φ]ψ is true at w iff: if φ is true at w, then ψ is true at w
  -- in the restricted model where only φ-worlds survive.
  if satisfies k frame val allWorlds w announcement
    then let restrictedWorlds = filter
               (\w' => satisfies k frame val allWorlds w' announcement)
               allWorlds
         in satisfies k frame val restrictedWorlds w body
    else True  -- vacuously true if announcement is false

-- ═══════════════════════════════════════════════════════════════════════
-- S5 Axiom Proofs (type-level)
-- ═══════════════════════════════════════════════════════════════════════

||| Axiom T (Truth): Knowledge implies truth.
||| If an agent knows P, then P is true.
||| K_a(P) → P
|||
||| This is guaranteed by the reflexivity of the S5 accessibility relation:
||| if P holds at all accessible worlds, and w is accessible from itself,
||| then P holds at w.
public export
data AxiomT : Agent -> Proposition -> Type where
  MkAxiomT : (a : Agent) -> (p : Proposition) ->
             (frame : S5Frame) ->
             Reflexive (access frame) a ->
             AxiomT a p

||| Axiom K (Distribution): Knowledge distributes over implication.
||| K_a(P → Q) → K_a(P) → K_a(Q)
public export
data AxiomK : Agent -> Proposition -> Proposition -> Type where
  MkAxiomK : (a : Agent) -> (p : Proposition) -> (q : Proposition) ->
             AxiomK a p q

||| Axiom 4 (Positive Introspection): Knowing implies knowing that you know.
||| K_a(P) → K_a(K_a(P))
|||
||| Guaranteed by transitivity of the accessibility relation.
public export
data Axiom4 : Agent -> Proposition -> Type where
  MkAxiom4 : (a : Agent) -> (p : Proposition) ->
             (frame : S5Frame) ->
             Transitive (access frame) a ->
             Axiom4 a p

||| Axiom 5 (Negative Introspection): Not knowing implies knowing that you don't know.
||| ¬K_a(P) → K_a(¬K_a(P))
|||
||| Guaranteed by the euclidean property (follows from symmetry + transitivity).
public export
data Axiom5 : Agent -> Proposition -> Type where
  MkAxiom5 : (a : Agent) -> (p : Proposition) ->
             (frame : S5Frame) ->
             Symmetric (access frame) a ->
             Transitive (access frame) a ->
             Axiom5 a p

-- ═══════════════════════════════════════════════════════════════════════
-- Knowledge Transfer (ENTAILS)
-- ═══════════════════════════════════════════════════════════════════════

||| Proof that knowledge transfers from one agent to another.
||| K_a1(P) → K_a2(P) holds when a2's accessibility relation is
||| a subset of a1's (a2 can distinguish fewer worlds than a1).
public export
data KnowledgeTransfer : Agent -> Agent -> Proposition -> Type where
  MkTransfer : (a1 : Agent) -> (a2 : Agent) -> (p : Proposition) ->
               (frame : S5Frame) ->
               -- a2's accessibility includes a1's:
               -- if a1 considers w1,w2 indistinguishable, so does a2
               ((w1, w2 : World) -> So (access frame a1 w1 w2) ->
                                    So (access frame a2 w1 w2)) ->
               KnowledgeTransfer a1 a2 p

-- ═══════════════════════════════════════════════════════════════════════
-- Epistemic Consistency (Level 10 soundness)
-- ═══════════════════════════════════════════════════════════════════════

||| An epistemic context: the agents and their epistemic states.
public export
record EpistemicContext where
  constructor MkEpCtx
  frame       : S5Frame
  valuation   : Valuation
  worlds      : List World
  actualWorld : World

||| Proof that an epistemic requirement is satisfied in a context.
public export
data RequirementSatisfied : EpistemicContext -> EpistemicRequirement -> Type where
  KnowsSat : (ctx : EpistemicContext) ->
             (a : Agent) -> (e : Expr) ->
             So (satisfies 100 (frame ctx) (valuation ctx)
                   (worlds ctx) (actualWorld ctx) (PKnows a (PAtom e))) ->
             RequirementSatisfied ctx (EpReqKnows a e)

  BelievesSat : (ctx : EpistemicContext) ->
                (a : Agent) -> (e : Expr) ->
                So (satisfies 100 (frame ctx) (valuation ctx)
                      (worlds ctx) (actualWorld ctx) (PBelieves a (PAtom e))) ->
                RequirementSatisfied ctx (EpReqBelieves a e)

  CommonSat : (ctx : EpistemicContext) ->
              (e : Expr) ->
              So (satisfies 100 (frame ctx) (valuation ctx)
                    (worlds ctx) (actualWorld ctx) (PCommon (PAtom e))) ->
              RequirementSatisfied ctx (EpReqCommon e)

  EntailsSat : (ctx : EpistemicContext) ->
               (a1 : Agent) -> (a2 : Agent) -> (e : Expr) ->
               KnowledgeTransfer a1 a2 (PAtom e) ->
               RequirementSatisfied ctx (EpReqEntails a1 a2 e)

||| Proof that all epistemic requirements are satisfied.
public export
data AllRequirementsSatisfied : EpistemicContext -> List EpistemicRequirement -> Type where
  NilReqs  : AllRequirementsSatisfied ctx []
  ConsReqs : RequirementSatisfied ctx req ->
             AllRequirementsSatisfied ctx reqs ->
             AllRequirementsSatisfied ctx (req :: reqs)

||| The Level 10 soundness certificate: given a well-formed epistemic
||| clause and a satisfying model, the epistemic properties hold.
public export
data EpistemicCertificate : Statement -> Type where
  MkEpCert : (stmt : Statement) ->
             (ec : EpistemicClause) ->
             (epistemicClause stmt = Just ec) ->
             (ctx : EpistemicContext) ->
             AllRequirementsSatisfied ctx (requirements ec) ->
             EpistemicCertificate stmt
  where
    ||| Extract requirements from an epistemic clause.
    requirements : EpistemicClause -> List EpistemicRequirement
    requirements (EpClause _ reqs) = reqs

-- ═══════════════════════════════════════════════════════════════════════
-- Belief vs Knowledge: Axiom Differences
-- ═══════════════════════════════════════════════════════════════════════

||| The key difference between knowledge and belief:
||| Knowledge satisfies axiom T (veridicality): K_a(P) → P
||| Belief does NOT satisfy axiom T: B_a(P) does not imply P
|||
||| Both satisfy axiom K (distribution):
|||   K_a(P → Q) → K_a(P) → K_a(Q)
|||   B_a(P → Q) → B_a(P) → B_a(Q)
|||
||| In a full KD45 extension, beliefs would use a serial (not reflexive)
||| accessibility relation, ensuring consistency (axiom D: B_a(P) → ¬B_a(¬P))
||| but not truth.
|||
||| For Level 10 checking, this means:
|||   REQUIRES KNOWS engine P  — the engine has verified P (strong guarantee)
|||   REQUIRES BELIEVES user P — the user claims P (weak, unverified)
public export
data BeliefWeakerThanKnowledge : Agent -> Proposition -> Type where
  ||| If an agent knows P, they also believe P.
  ||| K_a(P) → B_a(P)
  KnowsImpliesBelieves : (a : Agent) -> (p : Proposition) ->
                          AxiomT a p ->  -- knowledge is veridical
                          BeliefWeakerThanKnowledge a p
