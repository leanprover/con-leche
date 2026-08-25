import Setlec.Model.Basis.Util

/-!
# `Empty` basis block: interpretation and `hkey` obligations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The `Empty` block -/

/-- Interpretation of `Empty`'s pinned type, computed. -/
theorem interp_empty_type {cval : ConstVal V} :
    interpClosed V cval env ψ emptyA.toConstantVal.type =
      some (univ 1) := by
  simp [interpClosed, interpExpr, emptyA, ConstantInfo.toConstantVal,
    Level.eval]

/-- The empty set inhabits `Empty`'s type. -/
theorem empty_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ emptyA.toConstantVal.type = some T ∧
      (SetTheory.empty : V) ∈ˢ T :=
  ⟨univ 1, interp_empty_type, empty_mem_univ 1⟩

/-- Interpretation of `Empty.rec`'s pinned type, computed. -/
theorem interp_emptyRec_type {cval : ConstVal V}
    (hfindE : env.find? emptyName = some emptyA)
    (hvalE : ∀ ψ' : Name → Nat, cval emptyName ψ' = SetTheory.empty) :
    interpClosed V cval env ψ emptyRecA.toConstantVal.type =
      some (pi (if ψ uN = 0 then 0 else Nat.max 1 (ψ uN))
        (pi (ψ uN + 1) SetTheory.empty fun _ => univ (ψ uN)) fun M =>
        pi (ψ uN) SetTheory.empty fun t => SetTheory.app M t) := by
  have hfindE' : env.find? (Name.anonymous.str "Empty") = some emptyA :=
    hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Empty") ψ' = SetTheory.empty := hvalE
  simp only [interpClosed, emptyRecA, ConstantInfo.toConstantVal,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', emptyA, List.length_cons, List.length_nil, reduceIte,
    Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Empty.rec`'s value inhabits its type (vacuously). -/
theorem emptyRec_key {cval : ConstVal V}
    (hfindE : env.find? emptyName = some emptyA)
    (hvalE : ∀ ψ' : Name → Nat, cval emptyName ψ' = SetTheory.empty) :
    ∃ T, interpClosed V cval env ψ emptyRecA.toConstantVal.type = some T ∧
      emptyRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_emptyRec_type hfindE hvalE, ?_⟩
  simp only [emptyRecVal]
  refine lam_mem (V := V) fun M hM => ?_
  exact lam_mem (V := V)
    (B := fun t => SetTheory.app M t)
    fun t ht => absurd ht (not_mem_empty t)

/-- `Empty.rec`'s type carries truthful annotations. -/
theorem annotOk_emptyRec_type {cval : ConstVal V}
    (hfindE : env.find? emptyName = some emptyA)
    (hvalE : ∀ ψ' : Name → Nat, cval emptyName ψ' = SetTheory.empty) :
    AnnotOk V cval env ψ 0 (rho0 V) emptyRecA.toConstantVal.type := by
  have hfindE' : env.find? (Name.anonymous.str "Empty") = some emptyA :=
    hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Empty") ψ' = SetTheory.empty := hvalE
  simp only [emptyRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨?_, ?_⟩
  · -- the motive space `(t : Empty) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ?_⟩
    intro t A hA ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    refine ⟨univ (ψ uN), ?_⟩
    simp [Expr.instantiate1, interpExpr, Level.eval, uN]
  · intro M A hA hM
    have hA' : A = pi (ψ uN + 1) SetTheory.empty fun _ => univ (ψ uN) := by
      simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE', emptyA,
        ConstantInfo.toConstantVal, Level.eval, uN,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hA
      rw [← hA]
      rfl
    subst hA'
    refine ⟨?_, ?_⟩
    · -- opened `∀ (t : Empty), motive t`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ?_⟩
      intro t At hAt ht
      have hAt' : At = SetTheory.empty := by
        simp [interpExpr, hfindE', hvalE', emptyA,
          ConstantInfo.toConstantVal,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAt
        exact hAt.symm
      rw [hAt'] at ht
      exact absurd ht (not_mem_empty t)
    · refine ⟨pi (ψ uN) SetTheory.empty (fun t => SetTheory.app M t),
        ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE', emptyA,
        ConstantInfo.toConstantVal, Level.eval, uN,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl

end Setlec
