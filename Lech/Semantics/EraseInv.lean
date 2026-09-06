import Lech.Kernel.StdAxioms

/-!
# `eraseNames` / `erasePw` head inversions (task #161, S1)

THE SEPARATION's shared base: the two constant-head inversions of the
checker's two erasures, lifted out of `SetR/Install/Axiom.lean` (design
census §3.3, edge 6).  They are **pure `Expr` syntax** — no `EnvS`, no
valuation, no relation — and both lanes invert through them: the
collapsed lane at the axiom install, the graded lane at
`Interp2/ErasePwInv.lean`'s composite heads.

Statements verbatim from their old home; the namespace is unchanged.
-/

namespace Lech.Semantics

/-- `eraseNames` fixes a bare constant (local twin of the TT lane's
`eraseNames_const_inv`). -/
theorem eraseNames_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.eraseNames = .const n us) : e = .const n us := by
  cases e <;> simp only [Expr.eraseNames] at h <;> first
    | exact h
    | exact nomatch h

/-- `erasePw` fixes a constant (task #161 P5: `matchesPin` compares
through `Expr.erasePw` as well, so a pinned-shape inversion has to see
through both erasures).  Head inversion, as above. -/
theorem erasePw_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.erasePw = .const n us) : e = .const n us := by
  cases e <;> simp only [Expr.erasePw] at h <;> first
    | exact h
    | exact nomatch h


end Lech.Semantics
