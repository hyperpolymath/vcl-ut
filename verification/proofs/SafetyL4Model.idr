-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

||| Self-contained machine-checked model of the Level-4 (SQL-injection)
||| safety remediation for vcl-ut (hyperpolymath/standards#124).
|||
||| WHY THIS IS A STANDALONE HARNESS, NOT AN IN-REPO PROOF
||| ------------------------------------------------------
||| The shipped `src/core/*.idr` + `src/interface/abi/*.idr` corpus does
||| NOT compile on origin/main (see verification/proofs/VERIFICATION-
||| STANCE.adoc for the full catalogue: ABI.Types missing
||| `Decidable.Equality`, malformed enum `DecEq`, ill-typed
||| `CPtr = Bits n`, `createQueryHandle` lacking its `So` witness;
||| Grammar.idr forward-references `Statement`/`EpistemicClause` with no
||| `mutual` block; no ipkg/CI ever checked any of it). The in-repo L4
||| fix (commit on branch fix/vclut-l4-devacuize-honest-stance) is
||| logically correct and reviewable but cannot be `idris2 --check`-ed
||| in situ until the surrounding corpus is resurrected (tracked OWED).
|||
||| This module reproduces the *exact mathematical content* of that fix
||| against a minimal, self-contained model of the relevant AST fragment,
||| so the theorems themselves are genuinely machine-verified by
||| idris2 0.8.0 with NO believe_me / postulate / assert_total / sorry.
||| Every definition below is byte-faithful to the corresponding shipped
||| definition (Grammar.hasStringLit, Composition.joinWhere,
||| Levels.NoRawUserInput, Checker.checkLevel4 / checkLevel4Sound,
||| Composition.noRawUserInputCompose).

module SafetyL4Model

%default total

-- ── Minimal model of the relevant Grammar fragment ───────────────────

||| The only `Literal` distinction Level-4 cares about: is it a string?
public export
data Literal = LitString String | LitOther

||| The Expr fragment that `hasStringLit` traverses. Constructor set and
||| recursion are exactly those of the shipped `Grammar.Expr` clauses
||| that `Grammar.hasStringLit` matches (others collapse to the `_`
||| catch-all = False, modelled by `EOpaque`).
public export
data Expr
  = ELiteral Literal
  | ECompare Expr Expr
  | ELogic1  Expr            -- ELogic _ l Nothing _
  | ELogic2  Expr Expr       -- ELogic _ l (Just r) _
  | EAggregate Expr
  | EOpaque                  -- EField/EParam/EStar/ESubquery/... ⇒ False

||| Faithful copy of shipped `Grammar.hasStringLit`.
public export
hasStringLit : Expr -> Bool
hasStringLit (ELiteral (LitString _)) = True
hasStringLit (ELiteral LitOther)      = False
hasStringLit (ECompare l r)           = hasStringLit l || hasStringLit r
hasStringLit (ELogic1 l)              = hasStringLit l
hasStringLit (ELogic2 l r)            = hasStringLit l || hasStringLit r
hasStringLit (EAggregate e)           = hasStringLit e
hasStringLit EOpaque                  = False

||| A statement is modelled by just its WHERE clause (all `checkLevel4`
||| / `NoRawUserInput` depends on).
public export
WhereClause : Type
WhereClause = Maybe Expr

||| Faithful copy of shipped `Grammar.whereHasStringLit`.
public export
whereHasStringLit : WhereClause -> Bool
whereHasStringLit w = maybe False hasStringLit w

-- ── Levels.NoRawUserInput (the de-vacuized predicate) ────────────────

||| Was `data NoRawUserInput where AllParameterised : NoRawUserInput stmt`
||| — vacuous (held for ANY statement, incl. injection). Now carries the
||| real evidence `whereHasStringLit = False`.
public export
data NoRawUserInput : WhereClause -> Type where
  MkNoRawUserInput : whereHasStringLit w = False -> NoRawUserInput w

-- ── Checker.checkLevel4 + soundness ──────────────────────────────────

public export
checkLevel4 : WhereClause -> (Bool, String)
checkLevel4 w = l4Verdict (whereHasStringLit w)
  where
    l4Verdict : Bool -> (Bool, String)
    l4Verdict True  = (False, "L4 FAILED — raw string literal in WHERE")
    l4Verdict False = (True,  "L4 — WHERE uses only parameterised inputs")

falseNotTrue : (False = True) -> Void
falseNotTrue Refl impossible

||| Soundness: `checkLevel4` accepting a statement genuinely yields the
||| (now real) `NoRawUserInput` witness. Vacuously unstateable before
||| the de-vacuization.
export
checkLevel4Sound : (w : WhereClause) -> (m : String) ->
                   checkLevel4 w = (True, m) -> NoRawUserInput w
checkLevel4Sound w m prf with (whereHasStringLit w) proof p
  checkLevel4Sound w m prf | False = MkNoRawUserInput p
  checkLevel4Sound w m prf | True  = void (falseNotTrue (cong fst prf))

-- A negative check: an injection-bearing WHERE is *rejected* (the old
-- vacuous predicate would have "accepted" it via AllParameterised).
export
injectionRejected :
  fst (checkLevel4 (Just (ECompare EOpaque (ELiteral (LitString "1=1"))))) = False
injectionRejected = Refl

-- ── Composition.joinWhere + noRawUserInputCompose ────────────────────

||| Faithful copy of shipped `Composition.joinWhere`.
public export
joinWhere : WhereClause -> WhereClause -> WhereClause
joinWhere Nothing   Nothing   = Nothing
joinWhere (Just w)  Nothing   = Just w
joinWhere Nothing   (Just w)  = Just w
joinWhere (Just w1) (Just w2) = Just (ELogic2 w1 w2)

trueNotFalse : (True = False) -> Void
trueNotFalse Refl impossible

||| `False`-absorbing disjunction: both disjuncts False ⇒ whole False.
orFalseFalse : (x : Bool) -> x = False -> (y : Bool) -> y = False ->
               (x || y) = False
orFalseFalse False Refl _ yp = yp
orFalseFalse True  xp _ _    = void (trueNotFalse xp)

||| The join of two injection-free WHERE clauses is injection-free.
||| Mirrors shipped `Composition.noRawUserInputCompose`'s `joinFree`.
joinFree :
  (a, b : WhereClause) ->
  whereHasStringLit a = False ->
  whereHasStringLit b = False ->
  whereHasStringLit (joinWhere a b) = False
joinFree Nothing   Nothing   _  _  = Refl
joinFree (Just _)  Nothing   p1 _  = p1
joinFree Nothing   (Just _)  _  p2 = p2
joinFree (Just x)  (Just y)  p1 p2 =
  orFalseFalse (hasStringLit x) p1 (hasStringLit y) p2

||| Level-4 injection-freedom is GENUINELY closed under join (not
||| vacuously, as when the predicate was `AllParameterised`).
export
noRawUserInputCompose :
  (w1, w2 : WhereClause) ->
  NoRawUserInput w1 -> NoRawUserInput w2 ->
  NoRawUserInput (joinWhere w1 w2)
noRawUserInputCompose w1 w2 (MkNoRawUserInput n1) (MkNoRawUserInput n2) =
  MkNoRawUserInput (joinFree w1 w2 n1 n2)
