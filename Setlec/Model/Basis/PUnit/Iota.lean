import Setlec.Model.BasisInstall

/-!
# `PUnit.rec` iota-rule semantics (rhs interpretation, annotation truthfulness, fold equation)
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- The (annotated) rhs of `PUnit.rec`'s single rule. -/
def punitRecRhsA : Expr := ((ConstantInfo.recRules punitRecA).getD 0 default).rhs

/-- Interpretation of the `PUnit.rec` rule rhs. -/
theorem interp_punitRec_rhs {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt) :
    interpClosed V cval env ψ punitRecRhsA =
      some (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
        (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
        SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) := by
  have hfindP' : env.find? (Name.anonymous.str "PUnit") = some punitA := hfindP
  have hvalP' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PUnit") ψ' = unitSet := hvalP
  have hfindU' : env.find? ((Name.anonymous.str "PUnit").str "unit") = some punitUnitA :=
    hfindU
  have hvalU' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PUnit").str "unit") ψ' = pt := hvalU
  simp only [interpClosed, punitRecRhsA, punitRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindP', hvalP', hfindU', hvalU', punitA, punitUnitA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, u1N,
    hfindP', hvalP', hfindU', hvalU', punitA, punitUnitA,
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The `PUnit.rec` rule rhs carries truthful annotations. -/
theorem annotOk_punitRec_rhs {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt) :
    AnnotOk V cval env ψ 0 (rho0 V) punitRecRhsA := by
  have hfindP' : env.find? (Name.anonymous.str "PUnit") = some punitA := hfindP
  have hvalP' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PUnit") ψ' = unitSet := hvalP
  have hfindU' : env.find? ((Name.anonymous.str "PUnit").str "unit") = some punitUnitA :=
    hfindU
  have hvalU' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PUnit").str "unit") ψ' = pt := hvalU
  simp only [punitRecRhsA, punitRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨?_, ⟨_, rfl⟩, ?_⟩
  · -- the motive space
    try simp only [AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro t A hA ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨univ (ψ u1N), ?_, ?_⟩
    · simp [Expr.instantiate1, interpExpr, Level.eval, u1N]
    · exact univ_mem_univ (ψ u1N)
  · intro M A hA hM
    have hA' : A = pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N) := by
      have : interpExpr V cval env ψ 0 (rho0 V)
          (Expr.forallE (Name.anonymous.str "t")
            (Expr.const (Name.anonymous.str "PUnit") [Level.param (Name.anonymous.str "u")])
            (Expr.sort (Level.param (Name.anonymous.str "u_1")))
            ⟨BinderInfo.default, some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩) =
          some (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) := by
        simp only [interpExpr, hfindP', hvalP', punitA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, u1N]
        rfl
      rw [this] at hA
      exact (Option.some.inj hA).symm
    subst hA'
    refine ⟨?_, ?_⟩
    · -- the inner λ over `motive PUnit.unit`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, pt, ψ u1N + 1, unitSet, (fun _ => univ (ψ u1N)),
        ?_, ?_, hM, pt_mem_unitSet,
        fun _ _ => univ_mem_univ (ψ u1N)⟩, ⟨_, rfl⟩, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindU', hvalU',
          punitUnitA, ConstantInfo.toConstantVal]
        try rfl
      intro m Am hAm hm
      have hAm' : Am = SetTheory.app M pt := by
        simp [interpExpr, Expr.instantiate1, updV, hfindU', hvalU',
          punitUnitA, ConstantInfo.toConstantVal,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAm
        exact hAm.symm
      rw [hAm'] at hm
      refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨m, SetTheory.app M pt, ?_, hm, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · exact app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
    · intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.lam (ψ u1N) (SetTheory.app M pt) (fun m => m),
        pi (ψ u1N) (SetTheory.app M pt) (fun _ => SetTheory.app M pt),
        ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindU', hvalU',
          punitUnitA, ConstantInfo.toConstantVal, Level.eval, u1N,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · exact lam_mem (V := V) (B := fun _ => SetTheory.app M pt)
          fun m hm => hm
      · have hMpt : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        exact pi_mem_univ (u := ψ u1N) (v := ψ u1N) hMpt
          (fun _ _ => hMpt)

/-- The fold equation of `PUnit.rec`'s rule. -/
theorem punitRec_iota {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt)
    {Mv mv tv : V}
    (hM : Mv ∈ˢ pi (ψ u1N + 1) unitSet (fun _ => univ (ψ u1N)))
    (hm : mv ∈ˢ SetTheory.app Mv pt) (ht : tv ∈ˢ unitSet) :
    ∃ R, interpClosed V cval env ψ punitRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ) Mv) mv)
        tv = SetTheory.app (SetTheory.app R Mv) mv := by
  refine ⟨_, interp_punitRec_rhs hfindP hvalP hfindU hvalU, ?_⟩
  have hMpt : SetTheory.app Mv pt ∈ˢ univ (ψ u1N) :=
    app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse: both sides are the proof point
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ)
        Mv) mv) tv = pt := by
      simp only [punitRecVal, h0, reduceIte]
      rw [lam_zero, app_pt, app_pt, app_pt]
    have hR : SetTheory.app (SetTheory.app
        (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) Mv) mv =
        pt := by
      rw [if_pos h0, lam_zero, app_pt, app_pt]
    rw [hL, hR]
  · -- data: both sides compute to the minor premise
    have habs1 : Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) :=
      Nat.le_antisymm
        (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
        (Nat.le_max_right _ _)
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 :=
      fun hc => h0 (Nat.le_zero.mp (hc ▸ Nat.le_max_right _ _))
    have hspace : ∀ M : V, SetTheory.app M pt ∈ˢ univ (ψ u1N) →
        (pi (ψ u1N) unitSet fun _ => SetTheory.app M pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro M hMpt'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N)) (v := ψ u1N)
        (B := fun _ => SetTheory.app M pt)
        (unitSet_mem_univ _) (fun _ _ => hMpt')
      have habs2 : Nat.max (Nat.max (ψ uN) (ψ u1N)) (ψ u1N) =
          Nat.max (ψ uN) (ψ u1N) :=
        Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
          (Nat.le_max_left _ _)
      rw [if_neg h0, habs2] at this
      exact this
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ)
        Mv) mv) tv = mv := by
      simp only [punitRecVal, if_neg h0]
      have h1 : SetTheory.app
          (SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
              fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m) Mv =
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app Mv pt)
            fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m := by
        refine app_lam hM
          (B := fun M => pi (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
            fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app M pt)
          (fun M hM' => lam_mem (V := V)
            (B := fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app M pt)
            fun m hm' => lam_mem (V := V)
              (B := fun _ => SetTheory.app M pt) fun _ _ => hm')
          (fun M hM' => ?_)
        have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        have := pi_mem_univ (u := ψ u1N) (v := Nat.max (ψ uN) (ψ u1N))
          (B := fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app M pt)
          hMpt' (fun _ _ => hspace M hMpt')
        rw [if_neg hwne, habs1] at this
        exact this
      rw [h1]
      have h2 : SetTheory.app
          (SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app Mv pt)
            fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m) mv =
          SetTheory.lam (ψ u1N) unitSet fun _ => mv := by
        refine app_lam hm
          (B := fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app Mv pt)
          (fun m hm' => lam_mem (V := V)
            (B := fun _ => SetTheory.app Mv pt) fun _ _ => hm')
          (fun _ _ => hspace Mv hMpt)
      rw [h2]
      exact app_lam ht (B := fun _ => SetTheory.app Mv pt)
        (fun _ _ => hm) (fun _ _ => hMpt)
    have hR : SetTheory.app (SetTheory.app
        (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) Mv) mv =
        mv := by
      have h1 : SetTheory.app
          (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
            (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) Mv =
          SetTheory.lam (ψ u1N) (SetTheory.app Mv pt) fun m => m := by
        refine app_lam hM
          (B := fun M => pi (ψ u1N) (SetTheory.app M pt)
            fun _ => SetTheory.app M pt)
          (fun M hM' => lam_mem (V := V)
            (B := fun _ => SetTheory.app M pt) fun m hm' => hm')
          (fun M hM' => ?_)
        have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app M pt) hMpt' (fun _ _ => hMpt')
        by_cases hz : ψ u1N = 0
        · exact absurd hz h0
        · rw [if_neg hz] at this
          have hms : Nat.max (ψ u1N) (ψ u1N) = ψ u1N := Nat.max_self _
          rw [hms] at this
          rw [if_neg hz]
          rw [show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _]
          exact this
      rw [h1]
      exact app_lam hm (B := fun _ => SetTheory.app Mv pt)
        (fun m hm' => hm') (fun _ _ => hMpt)
    rw [hL, hR]

end Setlec
