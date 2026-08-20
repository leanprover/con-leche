import Setlec.Model.BasisInstall

/-!
# `PSigma'.rec` iota-rule semantics
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The `PSigma'.rec` rule -/

/-- The (annotated) rhs of `PSigma'.rec`'s single rule. -/
def psigmaRecRhsA : Expr := ((ConstantInfo.recRules psigmaRecA).getD 0 default).rhs

/-- Interpretation of the `PSigma'.rec` rule rhs (every λ tag is `0`:
the motive is Prop-valued). -/
theorem interp_psigmaRec_rhs {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    interpClosed V cval env ψ psigmaRecRhsA =
      some (SetTheory.lam 0 (univ (ψ uN)) fun A =>
        SetTheory.lam 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          SetTheory.lam 0
            (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              fun _ => univ 0) fun M =>
            SetTheory.lam 0
              (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M
                  (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) fun mk =>
              SetTheory.lam 0 A fun a =>
                SetTheory.lam 0 (SetTheory.app B a) fun b =>
                  SetTheory.app (SetTheory.app mk a) b) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA :=
    hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' :=
    hvalM
  simp only [interpClosed, psigmaRecRhsA, psigmaRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', hfindM', hvalM', psigmaA, psigmaMkA,
    List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    hfindS', hvalS', hfindM', hvalM',
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The fold equation of `PSigma'.rec`'s rule: everything collapses to
the proof point (Prop-valued motive). -/
theorem psigmaMk_iota {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ')
    {Av Bv Mv mkv av bv : V} :
    ∃ R, interpClosed V cval env ψ psigmaRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaRecVal V ψ) Av) Bv) Mv) mkv)
        (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkVal V ψ) Av) Bv) av) bv) =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app R Av) Bv) Mv) mkv) av) bv := by
  refine ⟨_, interp_psigmaRec_rhs hfindS hvalS hfindM hvalM, ?_⟩
  rw [show (psigmaRecVal V ψ : V) = pt from by
      simp only [psigmaRecVal]; exact lam_zero]
  simp only [lam_zero, app_pt]

end Setlec
