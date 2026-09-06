import Setlec.Kernel.ExprOps

/-!
# `stripPis` monotonicity

The two `∀`-tower monotonicity lemmas the direct-entry fold
(`SetP/DirectFoldEntryP.lean`) uses to step a constructor type's
telescope.

**What this file used to be** (2026-09-05): the discharge of
`ProjStepR` — R6 `Red.projRed`, the scrutinee's reduction at the
`.proj` site, and the stuck branch `Red.projArg` — together with the
generic constructor-spine telescope walk `tele_of_inferSpineR`.  All of
it was the collapsed model's derivation bridge and went with the R
tier; these two lemmas are pure `Expr` arithmetic that never mentioned
a relation, and they stayed because a live consumer uses them.  *A
spec function's home is decided by what its statement mentions* — the
interned batch's rule, applied to a residue instead of a move.
-/
namespace Setlec.Semantics

/-- `stripPis` is monotone downwards. -/
theorem stripPis_mono : ∀ (k : Nat) {E : Expr},
    (E.stripPis (k + 1)).isSome = true → (E.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro E _; rfl
  | succ k ih =>
    intro E h
    match E, h with
    | .forallE n ty b mb, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h ⊢
      exact ih h

/-- `stripPis` is monotone downwards, at any gap. -/
theorem stripPis_le : ∀ {k n : Nat}, k ≤ n → ∀ {E : Expr},
    (E.stripPis n).isSome = true → (E.stripPis k).isSome = true := by
  intro k n
  induction n with
  | zero => intro h E hE; obtain rfl : k = 0 := Nat.le_zero.mp h; exact hE
  | succ n ih =>
    intro h E hE
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (by omega) (stripPis_mono n hE)
    · obtain rfl : k = n + 1 := by omega
      exact hE

end Setlec.Semantics
