import Setlec.Semantics.Canon
import Setlec.Verify.Denote.Shift

/-!
# `denote_closed`'s `denote2` twin

*(Re-based to `Setlec/SetBase/*` at THE SEPARATION's S2, task #161: the
module already imported nothing but base — `SetBase/Canon` and
`Verify/Denote/Shift` — and three of the graded lane's carriers
(`Annot/{BitClosed,BitInst}`, `Interp2/OkPTransport`) crossed to it.
Path and module name changed; namespaces, statements and proofs
verbatim.)*


Seal 52's actionable residue, half of it: `ValueResidues2.closed`
(`Step2Cons.lean`) asks that the leaf a value install stores is
lift-invariant, and names v1's `denote_closed`
(`Verify/Denote/Shift.lean`) as the twin the tree does not have.
Here it is.

## The transposition is *not* a second induction

v1 proves closedness by an induction over `denote`'s own recursion
(`denote_bvarsBelow`, twenty-four cases).  The annotated twin needs
none of it: `denote2_erase` says the canonical annotation **erases**
to the denotation, and lifting an `AVExpr` is `VExpr.liftN` on the
erasure with the numerals riding along untouched (`erase_liftN`).  So
v1's conclusion transports back through `erase` in one step, and the
only new content is `AVExpr.liftN_eq_self` below — the observation
that a numeral slot cannot be the reason a lift moves a term.

*The rule this instance illustrates: before transposing a v1
induction, check whether the erasure law already carries it.*

## The fuel shape

**No fuel quantifier is added.**  `denote2`'s fuel appears only in the
*premise* — the run that produced the leaf — and the conclusion is a
syntactic equation about that leaf.  So this twin is not one of the
statements that needs the campaign's `∀ F, ∃ F' ≥ F` slack: there is
no `denote2` success on the right-hand side to pay for.  (Contrast
`MemberBlock2` and `Denote2InstLevels`, where the conclusion *is* a
run and the slack is mandatory.)

## What is *not* here

`denote_params_ext`'s twin.  It does not transpose this way — the
erasure law cannot carry it, because the fact it must preserve lives
exactly in the slots `erase` forgets.  See `Step2Cons.lean`'s
`ValueResidues2M.params` docstring for where it stalls.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open Setlec (Env Expr Name CheckMode)

namespace AVExpr

/-- **A lift that does not move the erasure does not move the term.**
`liftN` never reads or writes a numeral slot, so an annotated term is
lift-invariant exactly when its erasure is — and the erasure's
invariance is `VExpr.bvarsBelow`, which v1's lemmas produce. -/
theorem liftN_eq_self : ∀ (e : AVExpr) {k : Nat},
    VExpr.bvarsBelow k e.erase → ∀ n : Nat, liftN n e k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k h n
    have h' : i < k := h
    simp [liftN, h']
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k h n; rw [liftN_app, ihf h.1 n, iha h.2 n]
  | lam u A b ihA ihb =>
    intro k h n; rw [liftN_lam, ihA h.1 n, ihb h.2 n]
  | pi u v A B ihA ihB =>
    intro k h n; rw [liftN_pi, ihA h.1 n, ihB h.2 n]
  | letE T v b ihT ihv ihb =>
    intro k h n; rw [liftN_letE, ihT h.1 n, ihv h.2.1 n, ihb h.2.2 n]
  | eqE T a b ihT iha ihb =>
    intro k h n; rw [liftN_eqE, ihT h.1 n, iha h.2.1 n, ihb h.2.2 n]
  | proj i e ihe =>
    intro k h n; rw [liftN_proj, ihe h n]

/-- **`liftN_eq_self`'s substitution twin.**  `inst` never reads or
writes a numeral slot either, and it touches a term only at the `bvar`
whose index *is* the cut — so a term with no bound variable at or
above `k` is `inst`-invariant at `k`, for every substituend.

Stated with the substituend last (and universally quantified) because
that is the shape the leaf premise of `denoteP_substFvarAt` wants: the
stored annotations are invariant under *any* substitution, which is
what makes the `.const` and `.lit` clauses of the walk close. -/
theorem inst_eq_self : ∀ (e : AVExpr) {k : Nat},
    VExpr.bvarsBelow k e.erase → ∀ x : AVExpr, inst e x k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k h x
    have h' : i < k := h
    simp [inst, h']
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k h x; rw [inst_app, ihf h.1 x, iha h.2 x]
  | lam u A b ihA ihb =>
    intro k h x; rw [inst_lam, ihA h.1 x, ihb h.2 x]
  | pi u v A B ihA ihB =>
    intro k h x; rw [inst_pi, ihA h.1 x, ihB h.2 x]
  | letE T v b ihT ihv ihb =>
    intro k h x; rw [inst_letE, ihT h.1 x, ihv h.2.1 x, ihb h.2.2 x]
  | eqE T a b ihT iha ihb =>
    intro k h x; rw [inst_eqE, ihT h.1 x, iha h.2.1 x, ihb h.2.2 x]
  | proj i e ihe =>
    intro k h x; rw [inst_proj, ihe h x]

end AVExpr

namespace Interp2

/-- **`denote_closed`'s twin.**  A closed subject's canonical
annotation is closed, in the lifting form `EnvS2U.acval_closed` and
`ValueResidues2.closed` state it.

The valuation premise is v1's own: the leaves' *erasures* are closed,
which at an install is `EnvS.cval_closed` composed with
`EnvS2U.acval_erase`. -/
theorem denote2_closed {mode : CheckMode}
    {acval : Name → (Name → Nat) → AVExpr} {cval : TConstVal}
    {env : Env} {φ : Name → Nat} {fuel : Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {e : Expr} {ea : AVExpr} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denote2 mode acval env φ fuel 0 e = some ea) (n k : Nat) :
    ea.liftN n k = ea :=
  AVExpr.liftN_eq_self ea
    (VExpr.bvarsBelow.mono (Nat.zero_le k)
      (denote_closed hcl hnf hb (denote2_erase hlink 0 e h))) n

end Interp2

end Setlec.SetR
