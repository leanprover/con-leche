import Setlec.Verify.PropWhen
import Setlec.Verify.Level
import Setlec.Kernel.Direct.Parts

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

/-- The guard instantiation's zeroing walk, against a mask whose set
positions (relative to the walk's offset) are zero at `φ`. -/
theorem substFn_directGuardSigma_go (φ : Name → Nat) (m : PropWhen) :
    ∀ (lps : List Name) (k : Nat),
      (∀ j, PropWhen.tb m (k + j) = true → ∃ h : j < lps.length, φ lps[j] = 0) →
      ∀ n, Level.substFn φ lps (directGuardSigma.go m lps k) n = φ n
  | [], _, _, n => by simp [Level.substFn]
  | p :: rest, k, hm, n => by
    simp only [directGuardSigma.go, Level.substFn]
    by_cases hp : p = n
    · subst hp
      simp only [if_true]
      split
      · rename_i ht
        obtain ⟨_, h0⟩ := hm 0 (by simpa using ht)
        simpa [Level.eval] using h0.symm
      · rfl
    · rw [if_neg hp]
      exact substFn_directGuardSigma_go φ m rest (k + 1) (fun j hj => by
        obtain ⟨hlt, h0⟩ := hm (j + 1) (by rw [show k + (j + 1) = k + 1 + j by omega]; exact hj)
        exact ⟨by simpa using hlt, by simpa using h0⟩) n

/-- **The zeroing instantiation fixes every valuation at which the
guard is `Prop`** (and every valuation at a non-`Prop` structure).
Packed datum: the guard's mask is positional over `lps`; a set position
is a parameter the guard forces to zero, hence zero at `φ`
(`Level.holds_maskOf_of_eval_zero`). -/
theorem substFn_directGuardSigma (φ : Name → Nat) (resSort : Level) (lps : List Name)
    (guard : Level)
    (hz : (Level.isEquiv resSort .zero == some true) = true → Level.eval φ guard = 0) :
    Level.substFn φ lps (directGuardSigma resSort lps guard) = φ := by
  simp only [directGuardSigma]
  by_cases hp : (Level.isEquiv resSort .zero == some true) = true
  · rw [if_pos hp]
    by_cases hm : (Level.maskOf lps guard == PropWhen.never) = true
    · rw [if_pos hm]; exact Level.substFn_param_self φ lps
    · rw [if_neg hm]
      have hne : Level.maskOf lps guard ≠ .never := by simpa using hm
      have hh := Level.holds_maskOf_of_eval_zero (ps := lps) (hz hp) hne
      obtain ⟨-, hbits⟩ := PropWhen.holds_iff.mp hh
      have hdef := Level.maskOf_paramsDefined lps guard
      funext n
      refine substFn_directGuardSigma_go φ _ lps 0 (fun j hj => ?_) n
      have hj' : PropWhen.tb (Level.maskOf lps guard) j = true := by simpa using hj
      have hlt : j < lps.length := PropWhen.tb_lt_of_paramsDefined hne hdef hj'
      refine ⟨hlt, ?_⟩
      have := hbits j (Nat.lt_of_not_le fun h64 => by
        rw [PropWhen.tb_of_ge h64] at hj'; exact absurd hj' (by decide)) hj'
      simpa [Level.valAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using this
  · rw [if_neg hp]
    exact Level.substFn_param_self φ lps

theorem directGuardSigma_go_length (m : PropWhen) :
    ∀ (lps : List Name) (k : Nat), (directGuardSigma.go m lps k).length = lps.length
  | [], _ => rfl
  | _ :: rest, k => by simp [directGuardSigma.go, directGuardSigma_go_length m rest (k + 1)]

/-- The instantiation has the parameters' length. -/
theorem directGuardSigma_length (resSort : Level) (lps : List Name) (guard : Level) :
    (directGuardSigma resSort lps guard).length = lps.length := by
  simp only [directGuardSigma]
  split
  · split
    · simp
    · exact directGuardSigma_go_length _ lps 0
  · simp

end Setlec
