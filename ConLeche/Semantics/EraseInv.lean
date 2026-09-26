module

public import ConLeche.Kernel.StdAxioms

@[expose] public section

/-!
# `erasePw` head inversions (task #161, S1)

The constant-head inversion of the checker's erasure.  It is **pure
`Expr` syntax** — no valuation, no relation — and the model inverts
through it at the axiom installs and at `Model/ErasePwInv.lean`'s
composite heads.
-/

namespace ConLeche.Semantics

/-- `erasePw` fixes a constant (task #161 P5: `matchesPin` compares
through `Expr.erasePw`, so a pinned-shape inversion has to see through
that erasure).  Head inversion. -/
theorem erasePw_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.erasePw = .const n us) : e = .const n us := by
  cases e <;> simp only [Expr.erasePw] at h <;> first
    | exact h
    | exact nomatch h


end ConLeche.Semantics
