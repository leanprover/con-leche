import Setlec.Verify.PropWhen
import Setlec.Verify.Level
import Setlec.Kernel.Direct

/-!
# The guard's zeroing instantiation, semantically (task #175 W4c, P3 module 7)

`directGuardSigma resSort lps guard` is the level instantiation the
entry install validates a `Prop`-declared structure's projection type
at: the block's parameters, with those the guard forces to zero
(`Level.zeronessOf`) replaced by `zero`.  The one fact the P stage
needs: **wherever the guard is `Prop`, the instantiation is the
identity on the valuation** — a reading at `σ` is the reading at the
valuation itself.  (At a non-`Prop` structure `σ` is the parameter
list, and the identity is `substFn_param_self`.)
-/

namespace Setlec

/-- A substitution of the parameter list by a function of the names,
at a valuation. -/
theorem Level.substFn_map_fn (φ : Name → Nat) (f : Name → Level) :
    ∀ (ks : List Name) (n : Name),
      Level.substFn φ ks (ks.map f) n = if n ∈ ks then Level.eval φ (f n) else φ n
  | [], n => by simp [Level.substFn]
  | k :: ks, n => by
    simp only [List.map_cons, Level.substFn]
    by_cases hk : k = n
    · subst hk
      simp
    · rw [if_neg hk, Level.substFn_map_fn φ f ks n]
      have : (n ∈ k :: ks) ↔ (n ∈ ks) := by
        simp only [List.mem_cons]
        exact ⟨fun h => h.resolve_left (fun h' => hk h'.symm), Or.inr⟩
      simp only [this]

/-- **The zeroing instantiation fixes every valuation at which the
guard is `Prop`** (and every valuation at a non-`Prop` structure). -/
theorem substFn_directGuardSigma (φ : Name → Nat) (resSort : Level) (lps : List Name)
    (guard : Level)
    (hz : (Level.isEquiv resSort .zero == some true) = true → Level.eval φ guard = 0) :
    Level.substFn φ lps (directGuardSigma resSort lps guard) = φ := by
  unfold directGuardSigma
  by_cases hp : (Level.isEquiv resSort .zero == some true) = true
  · rw [if_pos hp]
    cases hzo : guard.zeronessOf with
    | never => exact Level.substFn_param_self φ lps
    | ifAllZero ps =>
      funext n
      rw [Level.substFn_map_fn]
      split
      · split
        · next hc =>
          have hs := PropWhen.zeronessOf_sound φ guard
          rw [hzo, hz hp] at hs
          simp only [PropWhen.holds, beq_self_eq_true, List.all_eq_true, beq_iff_eq] at hs
          have := hs n (List.mem_of_elem_eq_true hc)
          simp [Level.eval, this]
        · rfl
      · rfl
  · rw [if_neg hp]
    exact Level.substFn_param_self φ lps

/-- The instantiation has the parameters' length. -/
theorem directGuardSigma_length (resSort : Level) (lps : List Name) (guard : Level) :
    (directGuardSigma resSort lps guard).length = lps.length := by
  unfold directGuardSigma
  split
  · split <;> simp
  · simp

end Setlec
