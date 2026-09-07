import Lech.SetP.Direct.DirectIntroP

/-!
# `projAV`'s grading under equal-valued subjects (task #175 wiring, W5 S3)

The uniform projection spelling's truthfulness is a chain of
memberships of the subject's *value*, so it transfers to any
equal-valued graded subject — what the stuck-projection and
congruence rows (`ProjRowsP`, `DefEqP`) need when they replace a
subject by its head normal form.  Below the claims tier so that
`DefEqP` (under the step assembly) can read it.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `projAV`'s grading under equal-valued subjects -/

/-- The subject of a graded projection spine is graded. -/
theorem AnnotOk2_projAV_hoist :
    ∀ {i : Nat} {e : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ (projAV i e) → AnnotOk2 V σ e
  | 0, e, σ, h => ((AnnotOk2_proj V σ 0 e) ▸ h).1
  | i + 1, e, σ, h =>
    ((AnnotOk2_proj V σ 1 e) ▸
      (AnnotOk2_projAV_hoist (i := i) (e := .proj 1 e) h)).1

/-- The subject of a bit-valid projection spine is bit-valid. -/
theorem AnnotValidV_projAV_hoist :
    ∀ {i : Nat} {e : AVExpr} {σ : Nat → V},
      AnnotValidV V σ (projAV i e) → AnnotValidV V σ e
  | 0, e, σ, h => (AnnotValidV_proj V σ 0 e) ▸ h
  | i + 1, e, σ, h =>
    (AnnotValidV_proj V σ 1 e) ▸
      (AnnotValidV_projAV_hoist (i := i) (e := .proj 1 e) h)

/-- **`projAV`'s truthfulness transfers to an equal-valued graded
subject**: every `.proj` node's package is a membership of the
subject's value, and only the value enters. -/
theorem AnnotOk2_projAV_congr :
    ∀ {i : Nat} {e e' : AVExpr} {σ : Nat → V},
      interp2 V σ e = interp2 V σ e' → AnnotOk2 V σ e' →
      AnnotOk2 V σ (projAV i e) → AnnotOk2 V σ (projAV i e')
  | 0, e, e', σ, heq, hok', hok => by
    show AnnotOk2 V σ (.proj 0 e')
    have h : AnnotOk2 V σ (.proj 0 e) := hok
    rw [AnnotOk2_proj] at h ⊢
    obtain ⟨-, h2, u, v, A, Bf, hs, hA, hB⟩ := h
    exact ⟨hok', h2, u, v, A, Bf, heq ▸ hs, hA, hB⟩
  | i + 1, e, e', σ, heq, hok', hok => by
    show AnnotOk2 V σ (projAV i (.proj 1 e'))
    have hok1 : AnnotOk2 V σ (.proj 1 e) :=
      AnnotOk2_projAV_hoist (i := i) (e := .proj 1 e) hok
    refine AnnotOk2_projAV_congr (i := i) (e := .proj 1 e)
      (e' := .proj 1 e') ?_ ?_ hok
    · simp only [interp2_proj, heq]
    · rw [AnnotOk2_proj] at hok1 ⊢
      obtain ⟨-, h2, u, v, A, Bf, hs, hA, hB⟩ := hok1
      exact ⟨hok', h2, u, v, A, Bf, heq ▸ hs, hA, hB⟩

/-- `AnnotOkP` form of the congruence. -/
theorem AnnotOkP_projAV_congr {i : Nat} {e e' : AVExpr} {σ : Nat → V}
    (heq : interp2 V σ e = interp2 V σ e') (hok' : AnnotOkP V σ e')
    (hok : AnnotOkP V σ (projAV i e)) : AnnotOkP V σ (projAV i e') :=
  ⟨AnnotOk2_projAV_congr heq hok'.1 hok.1, projAV_validV hok'.2⟩

/-- `AnnotOkP` of the subject, off the spine's. -/
theorem AnnotOkP_projAV_hoist {i : Nat} {e : AVExpr} {σ : Nat → V}
    (hok : AnnotOkP V σ (projAV i e)) : AnnotOkP V σ e :=
  ⟨AnnotOk2_projAV_hoist hok.1, AnnotValidV_projAV_hoist hok.2⟩

/-- The interpretation of the spine, at equal-valued subjects. -/
theorem interp2_projAV_congr {i : Nat} {e e' : AVExpr} {σ : Nat → V}
    (heq : interp2 V σ e = interp2 V σ e') :
    interp2 V σ (projAV i e) = interp2 V σ (projAV i e') := by
  rw [projAV_interp, projAV_interp, heq]

end Lech.SetP
