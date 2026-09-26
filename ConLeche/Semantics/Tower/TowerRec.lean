module

public import ConLeche.Semantics.Tower.TowerMk

@[expose] public section

/-!
# The projection spine on tower members (task #175, stage 3d)

`projList` as a mapped range, and the grading of the uniform projection
spelling `projAV` on members of a tower carrier — the two facts the
structure and sum stages read a tower's fields through.  (The
structure-route recursor leaf `structRecAV` this module first held is
retired — lane DMASTER.)
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Projection-list arithmetic -/

theorem projList_eq_map_range (n : Nat) (x : V) :
    projList n x = (List.range n).map fun i => projS i x := by
  apply List.ext_getElem
  · rw [projList_length, List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact projList_get n i x (by rwa [projList_length] at h1)

/-! ## The projection spine's grading -/

/-- **The uniform projection spelling is graded on tower members**:
each `.proj` node's `WellDenoted` package is one `sigmaSet w` level of
the carrier, peeled by `mem_sigma_elim` — both regimes (at squash the
subject is `pt` throughout and the tail memberships are `pt`'s). -/
theorem projAV_wellDenoted_tower {w : Nat} :
    ∀ {i : Nat} {Fs : List AnnotTerm} {ρ : Nat → V} {e : AnnotTerm}
      {σ : Nat → V},
      WellDenoted V σ e →
      interp V σ e ∈ˢ towerSet w (teleOfFields ρ Fs) →
      FieldsBound w ρ Fs → i < Fs.length →
      WellDenoted V σ (projAV i e)
  | 0, F :: Fs', ρ, e, σ, hok, hx, hbnd, _ => by
    show WellDenoted V σ (.fst e)
    rw [WellDenoted]
    refine ⟨hok, w, w, interp V ρ F,
      fun a => towerSet w (teleOfFields (cons a ρ) Fs'), ?_, hbnd.1,
      fun a ha => towerSet_univ_teleOfFields (hbnd.2 a ha)⟩
    rwa [show Nat.max w w = w from Nat.max_self w]
  | i + 1, F :: Fs', ρ, e, σ, hok, hx, hbnd, hi => by
    obtain ⟨a, b, ha, hb, hz, hpos⟩ :=
      mem_sigma_elim (A := interp V ρ F)
        (B := fun a => towerSet w (teleOfFields (cons a ρ) Fs')) hx
    have hok1 : WellDenoted V σ (.snd e) := by
      rw [WellDenoted]
      refine ⟨hok, w, w, interp V ρ F,
        fun a => towerSet w (teleOfFields (cons a ρ) Fs'), ?_, hbnd.1,
        fun a' ha' => towerSet_univ_teleOfFields (hbnd.2 a' ha')⟩
      rwa [show Nat.max w w = w from Nat.max_self w]
    have hmem1 : interp V σ (.snd e)
        ∈ˢ towerSet w (teleOfFields (cons a ρ) Fs') := by
      rw [interp_snd]
      rcases Nat.eq_zero_or_pos w with rfl | hwpos
      · rw [hz rfl, ssnd_pt]
        rw [(towerSet_zero_elim _ hb).1] at hb
        exact hb
      · rw [hpos (Nat.pos_iff_ne_zero.mp hwpos), ssnd_spair]
        exact hb
    exact projAV_wellDenoted_tower (i := i) (Fs := Fs') (ρ := cons a ρ)
      (e := .snd e) hok1 hmem1 (hbnd.2 a ha)
      (by exact Nat.lt_of_succ_lt_succ hi)

end ConLeche.Semantics
