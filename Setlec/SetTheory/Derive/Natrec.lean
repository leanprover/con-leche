import Setlec.SetTheory.Derive.Omega
import Setlec.SetTheory.Derive.Graphs

/-!
# Recursion on `ω`

The classical set-theoretic recursion theorem is not needed: by
`mem_omega_iff`/`vnat_inj`, every member of `ω` is a *unique* `vnat k`,
so recursion on `ω` is meta-level recursion on `Nat` transported along
`vnat`.  The step function is applied as a curried set-theoretic
function (`app`), matching the `SetTheory.natrec` interface; off `ω`
the value is junk (`empty`), which no law constrains.
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

/-- Meta-level iteration of the set-level step function. -/
noncomputable def natIter (z s : V) : Nat → V
  | 0 => z
  | k + 1 => app (app s (vnat k)) (natIter z s k)

open Classical in
/-- Set-theoretic recursion on `ω`, through the meta-level naming
`vnat` of its members. -/
noncomputable def natrec (z s n : V) : V :=
  if h : ∃ k, n = vnat k then natIter z s (Classical.choose h) else empty

theorem natrec_vnat (z s : V) (k : Nat) :
    natrec z s (vnat k) = natIter z s k := by
  unfold natrec
  rw [dif_pos ⟨k, rfl⟩]
  congr 1
  exact (vnat_inj (Classical.choose_spec (⟨k, rfl⟩ : ∃ k', (vnat k : V) = vnat k'))).symm

theorem natrec_empty (z s : V) : natrec z s empty = z := by
  have h : (empty : V) = vnat 0 := rfl
  rw [h, natrec_vnat]
  rfl

theorem natrec_vsucc (z s : V) {n : V} (hn : n ∈ᵗ (omega : V)) :
    natrec z s (vsucc n) = app (app s n) (natrec z s n) := by
  obtain ⟨k, rfl⟩ := mem_omega_iff.mp hn
  have h : vsucc (vnat k : V) = vnat (k + 1) := rfl
  rw [h, natrec_vnat, natrec_vnat]
  rfl

/-- The recursion theorem with typing: the motive `M` is applied as a
set-theoretic function. -/
theorem natrec_mem {M z s n : V}
    (hz : z ∈ᵗ app M empty)
    (hs : ∀ k, k ∈ᵗ (omega : V) → ∀ ih, ih ∈ᵗ app M k →
      app (app s k) ih ∈ᵗ app M (vsucc k))
    (hn : n ∈ᵗ (omega : V)) : natrec z s n ∈ᵗ app M n := by
  obtain ⟨k, rfl⟩ := mem_omega_iff.mp hn
  clear hn
  rw [natrec_vnat]
  induction k with
  | zero => exact hz
  | succ k ih =>
    exact hs (vnat k) (vnat_mem_omega k) (natIter z s k) ih

end Setlec.TG
