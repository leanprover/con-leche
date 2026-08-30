import Setlec.SetR.Interp2.Step2.Dispatch

/-!
# `denote2` across a spine, a depth, and a level substitution

The three algebraic facts the **delta exit** of the reduction loop
needs, plus the one that is not algebraic at all.

`unfoldDefinition` (`Setlec/Kernel/Core.lean`) rewrites
`mkAppN (.const n us) args` to
`mkAppN (value.instantiateLevelParams cv.levelParams us) args`, so a
consumer of `EnvS2.acval_defn` has three gaps to cross:

| gap | this file |
|---|---|
| the head sits under a spine | `denote2_mkAppN_swap` |
| the field speaks at depth `0`, the loop runs at depth `d` | `denote2_depth_of_closed` |
| the field speaks about `value`, the reduct is `value.instantiateLevelParams …` | **`Denote2InstLevels` — a residue, not a theorem** |

The first two are structural and are proved here.  The third is
**not**, and that is this file's finding.

## Why the level crossing is not a structural induction

On the v1 lane the same crossing is `denote_instLevels`
(`Setlec/Verify/Denote/Levels.lean`), an unconditional equality proved
by one induction over `denote`: `denote` reads the level assignment
only at `.sort` (through `Level.eval`) and at `.const` (through
`Level.substFn`), and `Level.eval_subst` / `Level.substFn_map_subst`
settle both clauses.

`denote2` reads it at those two clauses **and** through
`sortOfE`/`lamSortE`, which are `inferTypeCore` and `whnf` *runs*
(`Annot/Canon.lean`).  At a `.forallE`/`.lam` node the two sides of the
crossing therefore compare

```
sortOfE μ env φ F d (ty.instantiateLevelParams ks us)
sortOfE μ env (Level.substFn φ ks us) F d ty
```

— two runs of the checker on **different terms**.  Relating them is a
statement about the checker, not about `denote2`: *inference and
head normalisation commute with level instantiation.*  Nothing of that
kind is in the tree; the depth-shift analogue (`shiftClaims`,
`Setlec/Verify/Deep.lean`, which is what makes `denote2_shiftFrom`
cheap) was landed for the memo cache and has no level-side twin.

Note also that the equality form is the wrong shape even if the
metatheorem is proved: instantiation can make a run **succeed that did
not** (level equalities that are open at a parameter close at an
instance), so the honest statement is the implication in the direction
the delta exit consumes, with the `∃ F' ≥ F` slack `Claims2B` already
uses everywhere.

## The smallest-fuel test, applied before stating

`Denote2InstLevels` asserts a `denote2` success as a **conclusion** —
the shape STOP 2 refuted three times.  It survives the test because the
fuel is existential (`∃ F', F ≤ F' ∧ …`) and the subject's success is a
hypothesis: at `F = 1` the hypothesis forces the subject binder-free
and the conclusion holds at the same fuel.  It is stated over an
`EnvS2` rather than a bare `acval` because its `.const` clause needs
`acval_params` — over an arbitrary valuation the two sides read the
same constant at two assignments that agree only on that constant's
own parameters, and the statement would be false.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## The spine

`denote2`'s `.app` clause is structural, so replacing a spine's head by
a term with the *same* annotation replaces nothing else.  The fuel is
allowed to move up in the same step: the arguments ride along on
`denote2_fuelMono`, which returns the same `AVExpr`. -/

/-- **Head swap under a spine.**  If the head's annotation survives a
move to `F' ≥ F` — for whatever reason: the same term, an unfolding, a
different term with the same canonical annotation — then so does the
whole application's, unchanged. -/
theorem denote2_mkAppN_swap {d : Nat} :
    ∀ (as : List Expr) {f g : Expr} {F F' : Nat} {ea : AVExpr},
      F ≤ F' →
      (∀ fa : AVExpr, denote2 μ acval env φ F d f = some fa →
        denote2 μ acval env φ F' d g = some fa) →
      denote2 μ acval env φ F d (Expr.mkAppN f as) = some ea →
      denote2 μ acval env φ F' d (Expr.mkAppN g as) = some ea := by
  intro as
  induction as with
  | nil => intro f g F F' ea _ hswap h; exact hswap ea h
  | cons a as ih =>
    intro f g F F' ea hle hswap h
    refine ih (f := .app f a) (g := .app g a) hle ?_ h
    intro fa hfa
    rw [denote2] at hfa
    rcases hf : denote2 μ acval env φ F d f with _ | fx
    · rw [hf] at hfa; exact nomatch hfa
    rw [hf] at hfa
    rcases ha : denote2 μ acval env φ F d a with _ | ax
    · rw [ha] at hfa; exact nomatch hfa
    rw [ha] at hfa
    obtain rfl : fa = .app fx ax := (Option.some.inj hfa).symm
    rw [denote2, hswap fx hf, denote2_fuelMono hle d a ha]
    rfl

/-! ## The depth

`EnvS2.acval_defn` speaks at depth `0`; the reduction loop runs at the
subject's depth.  For a term with no `fvar` leaves the shift is the
identity on the *expression* (`shiftFrom_eq_self_of_not_hasFvar`) and
`denote2_shiftFrom` then moves the annotation by a `liftN`, which
`EnvS2.acval_closed` undoes.  So a closed stored value annotates the
same at every depth — the transpose of v1's `denote_lift` step inside
`delta_coreR`. -/

/-- **A closed term's canonical annotation does not depend on the
depth**, provided the annotation itself is lift-invariant (which
`EnvS2.acval_closed` supplies for every valuation leaf). -/
theorem denote2_depth_of_closed (henv : Setlec.EnvWF env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {F : Nat} {e : Expr} {ea : AVExpr} (hfv : e.hasFvar = false)
    (hcl : ∀ k : Nat, ea.liftN 1 k = ea)
    (h : denote2 μ acval env φ F 0 e = some ea) :
    ∀ d : Nat, denote2 μ acval env φ F d e = some ea := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih =>
    have hs := denote2_shiftFrom (μ := μ) (acval := acval) (φ := φ)
      (f := F) (p := 0) henv hacl e d (Nat.zero_le d)
      (Expr.WScoped.of_not_hasFvar hfv)
    rw [Expr.shiftFrom_eq_self_of_not_hasFvar hfv, ih] at hs
    rw [hs]
    simp [hcl]

/-! ## The level substitution — the residue -/

/-- **The level-instantiation crossing for `denote2`** — v1's
`denote_instLevels` in the annotated currency, and *not* provable the
same way (see the module docstring): its binder clauses need
`inferTypeCore`/`whnf` to commute with level instantiation, which is a
metatheorem about the checker with no counterpart in the tree.

Stated as the implication the delta exit consumes rather than as v1's
equality, because instantiation can make a run succeed that did not,
and with `Claims2B`'s own `∃ F' ≥ F` slack, because the instantiated
term's sort computations are not the ones the hypothesis paid for. -/
def Denote2InstLevels (μ : CheckMode) {env : Env} (m : EnvS2 V env) :
    Prop :=
  ∀ (φ : Name → Nat) (ks : List Name) (us : List Level) (F d : Nat)
    (e : Expr) (ea : AVExpr),
    denote2 μ m.acval env (Level.substFn φ ks us) F d e = some ea →
    ∃ F', F ≤ F' ∧
      denote2 μ m.acval env φ F' d (e.instantiateLevelParams ks us)
        = some ea

end Setlec.SetR.Interp2
