import ConLeche.Model.Inductives.StructIntro

/-!
# `projAV`'s grading under equal-valued subjects (task #175 wiring, W5 S3)

The uniform projection spelling's truthfulness is a chain of
memberships of the subject's *value*, so it transfers to any
equal-valued graded subject — what the stuck-projection and
congruence rows (`ProjRowsP`, `DefEqP`) need when they replace a
subject by its head normal form.  Below the claims tier so that
`DefEqP` (under the step assembly) can read it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `projAV`'s grading under equal-valued subjects -/

/-- The subject of a graded projection spine is graded. -/
theorem WellDenoted_projAV_hoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ (projAV i e) → WellDenoted V σ e
  | 0, e, σ, h => ((WellDenoted_proj V σ 0 e) ▸ h).1
  | i + 1, e, σ, h =>
    ((WellDenoted_proj V σ 1 e) ▸
      (WellDenoted_projAV_hoist (i := i) (e := .proj 1 e) h)).1

/-- The subject of a bit-valid projection spine is bit-valid. -/
theorem AnnotValid_projAV_hoist :
    ∀ {i : Nat} {e : AnnotTerm} {σ : Nat → V},
      AnnotValid V σ (projAV i e) → AnnotValid V σ e
  | 0, e, σ, h => (AnnotValid_proj V σ 0 e) ▸ h
  | i + 1, e, σ, h =>
    (AnnotValid_proj V σ 1 e) ▸
      (AnnotValid_projAV_hoist (i := i) (e := .proj 1 e) h)

/-- **`projAV`'s truthfulness transfers to an equal-valued graded
subject**: every `.proj` node's package is a membership of the
subject's value, and only the value enters. -/
theorem WellDenoted_projAV_congr :
    ∀ {i : Nat} {e e' : AnnotTerm} {σ : Nat → V},
      interp V σ e = interp V σ e' → WellDenoted V σ e' →
      WellDenoted V σ (projAV i e) → WellDenoted V σ (projAV i e')
  | 0, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (.proj 0 e')
    have h : WellDenoted V σ (.proj 0 e) := hok
    rw [WellDenoted_proj] at h ⊢
    obtain ⟨-, h2, u, v, A, Bf, hs, hA, hB⟩ := h
    exact ⟨hok', h2, u, v, A, Bf, heq ▸ hs, hA, hB⟩
  | i + 1, e, e', σ, heq, hok', hok => by
    show WellDenoted V σ (projAV i (.proj 1 e'))
    have hok1 : WellDenoted V σ (.proj 1 e) :=
      WellDenoted_projAV_hoist (i := i) (e := .proj 1 e) hok
    refine WellDenoted_projAV_congr (i := i) (e := .proj 1 e)
      (e' := .proj 1 e') ?_ ?_ hok
    · simp only [interp_proj, heq]
    · rw [WellDenoted_proj] at hok1 ⊢
      obtain ⟨-, h2, u, v, A, Bf, hs, hA, hB⟩ := hok1
      exact ⟨hok', h2, u, v, A, Bf, heq ▸ hs, hA, hB⟩

/-- `WellDenotedV` form of the congruence. -/
theorem WellDenotedV_projAV_congr {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') (hok' : WellDenotedV V σ e')
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ (projAV i e') :=
  ⟨WellDenoted_projAV_congr heq hok'.1 hok.1, projAV_validV hok'.2⟩

/-- `WellDenotedV` of the subject, off the spine's. -/
theorem WellDenotedV_projAV_hoist {i : Nat} {e : AnnotTerm} {σ : Nat → V}
    (hok : WellDenotedV V σ (projAV i e)) : WellDenotedV V σ e :=
  ⟨WellDenoted_projAV_hoist hok.1, AnnotValid_projAV_hoist hok.2⟩

/-- The interpretation of the spine, at equal-valued subjects. -/
theorem interp_projAV_congr {i : Nat} {e e' : AnnotTerm} {σ : Nat → V}
    (heq : interp V σ e = interp V σ e') :
    interp V σ (projAV i e) = interp V σ (projAV i e') := by
  rw [projAV_interp, projAV_interp, heq]

end ConLeche.Model
