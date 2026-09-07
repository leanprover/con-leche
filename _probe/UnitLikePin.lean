/-
Task #161 residual round 1 — the mechanized half of the
unreachability argument for the unit-like branch's omitted type
comparison.

`unitLikePin`: after item C1 (the pinned-name test), `isUnitLikeTy`
accepts NOTHING but a bare `PUnit` constant.  Hence, at a firing
unit-like branch, the two inferred-and-whnf'd types are
`.const PUnit us` and `.const PUnit vs`, and the comparison the
official kernel runs there (`is_def_eq_core(t_type, infer_type(s))`,
type_checker.cpp:1168) can only ever decide a LEVEL question.

The residual — that the two level lists are always equivalent at a
reachable call — is a statement about the defeq descent, not about
this function; it is argued in DESIGN.md, not mechanized here.
-/
import ConLeche.Kernel.Core

namespace ConLeche

/-- The pinned-name test accepts only a bare `PUnit` constant. -/
theorem unitLikeTy_eq_punit_const {env : Env} {t : Expr}
    (h : isUnitLikeTy env t = true) :
    ∃ us : List Level, t = .const punitName us := by
  cases t with
  | const c us =>
    refine ⟨us, ?_⟩
    simp only [isUnitLikeTy, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1]
  | _ => simp [isUnitLikeTy] at h

/-- Both sides of a firing unit-like branch: the whnf'd types are two
`PUnit` constants, so the omitted comparison is exactly a comparison
of their level lists. -/
theorem unitLike_pair_punit {env : Env} {ta tb : Expr}
    (ha : isUnitLikeTy env ta = true) (hb : isUnitLikeTy env tb = true) :
    ∃ us vs : List Level,
      ta = .const punitName us ∧ tb = .const punitName vs := by
  obtain ⟨us, hu⟩ := unitLikeTy_eq_punit_const ha
  obtain ⟨vs, hv⟩ := unitLikeTy_eq_punit_const hb
  exact ⟨us, vs, hu, hv⟩

end ConLeche

#print axioms ConLeche.unitLikeTy_eq_punit_const
#print axioms ConLeche.unitLike_pair_punit
