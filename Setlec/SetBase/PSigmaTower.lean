import Setlec.SetBase.EqTower

/-!
# The pair block's value towers, at the base (task #161 S7, Wall C)

`PSigma'.rec`'s and the two native projections' `VExpr` towers, and
their closedness.  Pure `VExpr` syntax — no environment, no `denote`,
no `EnvS` — declared in `SetR/Install/BasisS.lean` only because the
collapsed install needed them first; the P lane reads them at
`BasisPSigmaP`.  Relocated verbatim, names unchanged, at the batch
that killed the `BasisEmptyP -> Install/BasisS` import (which is what
had been resolving them for the P lane — the census's "the gate sees
imports, not crossings" finding again).
-/

namespace Setlec.SetR

open Setlec Setlec.TT

/-- `PSigma'.rec`'s valuation: the minor premise at the subject's two
projections — `psigmaRec_derivable` (`Setlec/TT/Examples.lean`).  The
last of the layer's *derived* four, and the one that derives through
**structure η** where `Eq.rec` derived through proof irrelevance. -/
def psigmaRecValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN))
    (.lam (.pi (.bvar 0) (.sort (ψ vN)))
      (.lam (.pi (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
            [.bvar 1, .bvar 0]) (.sort 0))
        (.lam (.pi (.bvar 2)
            (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 2) (VExpr.mkAppN
                (VExpr.const .psigmaMk [ψ uN, ψ vN])
                [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))
          (.lam (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
              [.bvar 3, .bvar 2])
            (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
              (.proj 1 (.bvar 0)))))))


/-- The tower is closed. -/
theorem psigmaRecValT_closed (ψ : Name → Nat) :
    VExpr.Closed (psigmaRecValT ψ) := by
  simp only [psigmaRecValT, VExpr.Closed, VExpr.bvarsBelow,
    VExpr.mkAppN]
  repeat' apply And.intro
  all_goals first | trivial | omega


/-- The pinned pair's projection valuations: the layer's `proj` former
under the parameter binders (`psigmaFst_derivable`). -/
def pairProjValT (i : Nat) (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN))
    (.lam (.pi (.bvar 0) (.sort (ψ vN)))
      (.lam (VExpr.mkAppN (VExpr.const .psigma [ψ uN, ψ vN])
          [.bvar 1, .bvar 0])
        (.proj i (.bvar 0))))


theorem pairProjValT_closed (i : Nat) (ψ : Name → Nat) :
    VExpr.Closed (pairProjValT i ψ) := by
  simp only [pairProjValT, VExpr.Closed, VExpr.bvarsBelow, VExpr.mkAppN]
  repeat' apply And.intro
  all_goals first | trivial | omega


end Setlec.SetR
