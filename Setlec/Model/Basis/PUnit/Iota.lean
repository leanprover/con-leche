import Setlec.Model.BasisInstall
import Setlec.Model.RuleFold

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

/-- The value-level fold of `PUnit.rec`: applied through its telescope
to any constructor point, the recursor value returns the minor
premise (the Prop collapse is self-handling). -/
theorem punitRecVal_fold {Mv mv tv : V}
    (hM : Mv ∈ˢ pi (ψ u1N + 1) unitSet (fun _ => univ (ψ u1N)))
    (hm : mv ∈ˢ SetTheory.app Mv pt) (ht : tv ∈ˢ unitSet) :
    SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ) Mv) mv)
      tv = mv := by
  have hMpt : SetTheory.app Mv pt ∈ˢ univ (ψ u1N) :=
    app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse: the recursor collapses to the proof point, and so
    -- does the minor premise (its space is a truth value)
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ)
        Mv) mv) tv = pt := by
      simp only [punitRecVal, h0, reduceIte]
      rw [lam_zero, app_pt, app_pt, app_pt]
    rw [hL]
    exact (mem_univ_zero (h0 ▸ hMpt) hm).symm
  · -- data: the value computes to the minor premise
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

/-- The `RecRulesOk` clause of `PUnit.rec`'s single rule: the canonical
λ-tower exists, is well-formed and resolves, and interprets (for every
level assignment) to the same set as the stored right-hand side. -/
theorem punitRec_ruleOk {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt)
    (hfindR : env.find? (punitName.str "rec") = some punitRecA)
    (hvalR : ∀ ψ' : Name → Nat,
      cval (punitName.str "rec") ψ' = punitRecVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts (punitName.str "rec") punitRecA.toConstantVal 2
        ((ConstantInfo.recRules punitRecA).getD 0 default)
        punitUnitA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 2 +
        RecRule.nfields ((ConstantInfo.recRules punitRecA).getD 0 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' punitRecRhsA = some Rv := by
  have hfindP' : env.find? (Name.anonymous.str "PUnit") = some punitA := hfindP
  have hvalP' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PUnit") ψ' = unitSet := hvalP
  have hfindU' : env.find? ((Name.anonymous.str "PUnit").str "unit") =
      some punitUnitA := hfindU
  have hvalU' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PUnit").str "unit") ψ' = pt := hvalU
  have hfindR' : env.find? ((Name.anonymous.str "PUnit").str "rec") =
      some punitRecA := hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PUnit").str "rec") ψ' = punitRecVal V ψ' :=
    hvalR
  -- the canonical tower's components, computed from the pinned data
  have hparts : ruleLhsParts (punitName.str "rec") punitRecA.toConstantVal 2
      ((ConstantInfo.recRules punitRecA).getD 0 default)
      punitUnitA.toConstantVal = some
      ([(Expr.fvar 0 (Name.anonymous.str "motive")
           (Expr.forallE (Name.anonymous.str "t")
             (Expr.const (Name.anonymous.str "PUnit")
               [Level.param (Name.anonymous.str "u")])
             (Expr.sort (Level.param (Name.anonymous.str "u_1")))
             ⟨BinderInfo.default,
               some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩),
         ⟨BinderInfo.default,
           some (Level.imax (Level.param (Name.anonymous.str "u_1"))
             (Level.param (Name.anonymous.str "u_1")))⟩),
        (Expr.fvar 1 (Name.anonymous.str "unit")
           (Expr.app
             (Expr.fvar 0 (Name.anonymous.str "motive")
               (Expr.forallE (Name.anonymous.str "t")
                 (Expr.const (Name.anonymous.str "PUnit")
                   [Level.param (Name.anonymous.str "u")])
                 (Expr.sort (Level.param (Name.anonymous.str "u_1")))
                 ⟨BinderInfo.default,
                   some (Level.succ
                     (Level.param (Name.anonymous.str "u_1")))⟩))
             (Expr.const ((Name.anonymous.str "PUnit").str "unit")
               [Level.param (Name.anonymous.str "u")])),
         ⟨BinderInfo.default,
           some (Level.param (Name.anonymous.str "u_1"))⟩)],
       Expr.app
         (Expr.app
           (Expr.app
             (Expr.const ((Name.anonymous.str "PUnit").str "rec")
               [Level.param (Name.anonymous.str "u_1"),
                Level.param (Name.anonymous.str "u")])
             (Expr.fvar 0 (Name.anonymous.str "motive")
               (Expr.forallE (Name.anonymous.str "t")
                 (Expr.const (Name.anonymous.str "PUnit")
                   [Level.param (Name.anonymous.str "u")])
                 (Expr.sort (Level.param (Name.anonymous.str "u_1")))
                 ⟨BinderInfo.default,
                   some (Level.succ
                     (Level.param (Name.anonymous.str "u_1")))⟩)))
           (Expr.fvar 1 (Name.anonymous.str "unit")
             (Expr.app
               (Expr.fvar 0 (Name.anonymous.str "motive")
                 (Expr.forallE (Name.anonymous.str "t")
                   (Expr.const (Name.anonymous.str "PUnit")
                     [Level.param (Name.anonymous.str "u")])
                   (Expr.sort (Level.param (Name.anonymous.str "u_1")))
                   ⟨BinderInfo.default,
                     some (Level.succ
                       (Level.param (Name.anonymous.str "u_1")))⟩))
               (Expr.const ((Name.anonymous.str "PUnit").str "unit")
                 [Level.param (Name.anonymous.str "u")]))))
         (Expr.const ((Name.anonymous.str "PUnit").str "unit")
           [Level.param (Name.anonymous.str "u")])) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts
    rfl rfl rfl rfl (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindR]; rfl)
      (show (env.find? ((Name.anonymous.str "PUnit").str "unit")).isSome = true
        by rw [hfindU']; rfl)
      (by simp [ConstantInfo.toConstantVal, punitRecA, Expr.constsResolve,
        hfindP', hfindU'])
      (by simp [ConstantInfo.toConstantVal, punitUnitA, Expr.constsResolve,
        hfindP'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    -- the shared interpretation of the motive space
    have hityM : interpExpr V cval env ψ' 0 (rho0 V)
        (Expr.forallE (Name.anonymous.str "t")
          (Expr.const (Name.anonymous.str "PUnit")
            [Level.param (Name.anonymous.str "u")])
          (Expr.sort (Level.param (Name.anonymous.str "u_1")))
          ⟨BinderInfo.default,
            some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩) =
        some (pi (ψ' u1N + 1) unitSet fun _ => univ (ψ' u1N)) := by
      simp only [interpExpr, hfindP', hvalP', punitA, ConstantInfo.toConstantVal,
        List.length_cons, List.length_nil, reduceIte, Level.eval, Level.substFn]
      simp [interpExpr, Expr.instantiate1, updV, u1N]
      rfl
    have hAtyM : AnnotOk V cval env ψ' 0 (rho0 V)
        (Expr.forallE (Name.anonymous.str "t")
          (Expr.const (Name.anonymous.str "PUnit")
            [Level.param (Name.anonymous.str "u")])
          (Expr.sort (Level.param (Name.anonymous.str "u_1")))
          ⟨BinderInfo.default,
            some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩) := by
      simp only [AnnotOk]
      refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
      intro t A hA ht
      refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
      refine ⟨univ (ψ' u1N), ?_, ?_⟩
      · simp [Expr.instantiate1, interpExpr, Level.eval, u1N]
      · simpa [Level.eval, u1N] using univ_mem_univ (ψ' u1N)
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) punitRecRhsA :=
      annotOk_punitRec_rhs (cval := cval) (ψ := ψ') hfindP hvalP hfindU hvalU
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL punitRecRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' punitRecRhsA = some Rv := by
      intro fvms bL hwf' ht
      obtain ⟨⟨Rv, hL, hR⟩, hA⟩ := TowerOk.out ht hwf' hAR
      exact ⟨hA, Rv, hL, hR⟩
    refine hstep hwf ?_
    -- stage 1: the motive binder
    refine TowerOk.cons (A := pi (ψ' u1N + 1) unitSet fun _ => univ (ψ' u1N))
      hityM hityM hAtyM ?_
    intro M hM
    have hMpt : SetTheory.app M pt ∈ˢ univ (ψ' u1N) :=
      app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ' u1N))
    -- stage 2: the minor-premise binder
    have hityU : interpExpr V cval env ψ' 1 (updV V (rho0 V) 0 M)
        (Expr.app
          (Expr.fvar 0 (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (Expr.const (Name.anonymous.str "PUnit")
                [Level.param (Name.anonymous.str "u")])
              (Expr.sort (Level.param (Name.anonymous.str "u_1")))
              ⟨BinderInfo.default,
                some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩))
          (Expr.const ((Name.anonymous.str "PUnit").str "unit")
            [Level.param (Name.anonymous.str "u")])) =
        some (SetTheory.app M pt) := by
      simp [interpExpr, updV, hfindU', hvalU', punitUnitA,
        ConstantInfo.toConstantVal]
    have hAtyU : AnnotOk V cval env ψ' 1 (updV V (rho0 V) 0 M)
        (Expr.app
          (Expr.fvar 0 (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (Expr.const (Name.anonymous.str "PUnit")
                [Level.param (Name.anonymous.str "u")])
              (Expr.sort (Level.param (Name.anonymous.str "u_1")))
              ⟨BinderInfo.default,
                some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩))
          (Expr.const ((Name.anonymous.str "PUnit").str "unit")
            [Level.param (Name.anonymous.str "u")])) := by
      simp only [AnnotOk]
      exact ⟨trivial, trivial, M, pt, ψ' u1N + 1, unitSet,
        (fun _ => univ (ψ' u1N)),
        (by simp [interpExpr, updV]),
        (by simp [interpExpr, hfindU', hvalU', punitUnitA,
          ConstantInfo.toConstantVal]),
        hM, pt_mem_unitSet, fun _ _ => univ_mem_univ _⟩
    refine TowerOk.cons (A := SetTheory.app M pt) hityU hityU hAtyU ?_
    intro m hm
    -- the bottom: the canonical lhs versus the opened rhs body
    have hirec : interpExpr V cval env ψ' 2 (updV V (updV V (rho0 V) 0 M) 1 m)
        (Expr.const ((Name.anonymous.str "PUnit").str "rec")
          [Level.param (Name.anonymous.str "u_1"),
           Level.param (Name.anonymous.str "u")]) =
        some (punitRecVal V ψ') := by
      simp only [interpExpr, hfindR', hvalR', punitRecA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte]
      simp [punitRecVal, Level.substFn, Level.eval, uN, u1N]
      try rfl
    have hifv0 : interpExpr V cval env ψ' 2 (updV V (updV V (rho0 V) 0 M) 1 m)
        (Expr.fvar 0 (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t")
            (Expr.const (Name.anonymous.str "PUnit")
              [Level.param (Name.anonymous.str "u")])
            (Expr.sort (Level.param (Name.anonymous.str "u_1")))
            ⟨BinderInfo.default,
              some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩)) =
        some M := by
      simp [interpExpr, updV]
    have hiunit : interpExpr V cval env ψ' 2 (updV V (updV V (rho0 V) 0 M) 1 m)
        (Expr.const ((Name.anonymous.str "PUnit").str "unit")
          [Level.param (Name.anonymous.str "u")]) = some pt := by
      simp [interpExpr, hfindU', hvalU', punitUnitA, ConstantInfo.toConstantVal]
    -- the recursor value's membership in its interpreted type
    obtain ⟨T, hT, hmem⟩ := punitRec_key (cval := cval) (env := env) (ψ := ψ')
      hfindP hvalP hfindU hvalU
    rw [interp_punitRec_type hfindP hvalP hfindU hvalU] at hT
    obtain rfl := Option.some.inj hT
    have hinner : ∀ M' : V,
        M' ∈ˢ (pi (ψ' u1N + 1) unitSet fun _ => univ (ψ' u1N)) →
        (pi (ψ' u1N) unitSet fun t => SetTheory.app M' t) ∈ˢ
          univ (if ψ' u1N = 0 then 0 else Nat.max (ψ' uN) (ψ' u1N)) :=
      fun M' hM' => pi_mem_univ (unitSet_mem_univ (ψ' uN))
        (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ _))
    have houter : ∀ M' : V,
        M' ∈ˢ (pi (ψ' u1N + 1) unitSet fun _ => univ (ψ' u1N)) →
        (pi (if ψ' u1N = 0 then 0 else Nat.max (ψ' uN) (ψ' u1N))
          (SetTheory.app M' pt) fun _ =>
          pi (ψ' u1N) unitSet fun t => SetTheory.app M' t) ∈ˢ
        univ (if (if ψ' u1N = 0 then 0 else Nat.max (ψ' uN) (ψ' u1N)) = 0
          then 0
          else Nat.max (ψ' u1N)
            (if ψ' u1N = 0 then 0 else Nat.max (ψ' uN) (ψ' u1N))) :=
      fun M' hM' => pi_mem_univ
        (app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ _))
        (fun _ _ => hinner M' hM')
    have hm1 : SetTheory.app (punitRecVal V ψ') M ∈ˢ
        pi (if ψ' u1N = 0 then 0 else Nat.max (ψ' uN) (ψ' u1N))
          (SetTheory.app M pt) (fun _ =>
            pi (ψ' u1N) unitSet fun t => SetTheory.app M t) :=
      app_mem hmem hM (fun M' hM' => houter M' hM')
    have hm2 : SetTheory.app (SetTheory.app (punitRecVal V ψ') M) m ∈ˢ
        pi (ψ' u1N) unitSet (fun t => SetTheory.app M t) :=
      app_mem hm1 hm (fun _ _ => hinner M hM)
    have hipartial1 : interpExpr V cval env ψ' 2
        (updV V (updV V (rho0 V) 0 M) 1 m)
        (Expr.app
          (Expr.const ((Name.anonymous.str "PUnit").str "rec")
            [Level.param (Name.anonymous.str "u_1"),
             Level.param (Name.anonymous.str "u")])
          (Expr.fvar 0 (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (Expr.const (Name.anonymous.str "PUnit")
                [Level.param (Name.anonymous.str "u")])
              (Expr.sort (Level.param (Name.anonymous.str "u_1")))
              ⟨BinderInfo.default,
                some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩))) =
        some (SetTheory.app (punitRecVal V ψ') M) := by
      rw [interpExpr, hirec, hifv0]
    have hifv1 : interpExpr V cval env ψ' 2 (updV V (updV V (rho0 V) 0 M) 1 m)
        (Expr.fvar 1 (Name.anonymous.str "unit")
          (Expr.app
            (Expr.fvar 0 (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (Expr.const (Name.anonymous.str "PUnit")
                  [Level.param (Name.anonymous.str "u")])
                (Expr.sort (Level.param (Name.anonymous.str "u_1")))
                ⟨BinderInfo.default,
                  some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩))
            (Expr.const ((Name.anonymous.str "PUnit").str "unit")
              [Level.param (Name.anonymous.str "u")]))) = some m := by
      simp [interpExpr, updV]
    have hipartial2 : interpExpr V cval env ψ' 2
        (updV V (updV V (rho0 V) 0 M) 1 m)
        (Expr.app
          (Expr.app
            (Expr.const ((Name.anonymous.str "PUnit").str "rec")
              [Level.param (Name.anonymous.str "u_1"),
               Level.param (Name.anonymous.str "u")])
            (Expr.fvar 0 (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (Expr.const (Name.anonymous.str "PUnit")
                  [Level.param (Name.anonymous.str "u")])
                (Expr.sort (Level.param (Name.anonymous.str "u_1")))
                ⟨BinderInfo.default,
                  some (Level.succ (Level.param (Name.anonymous.str "u_1")))⟩)))
          (Expr.fvar 1 (Name.anonymous.str "unit")
            (Expr.app
              (Expr.fvar 0 (Name.anonymous.str "motive")
                (Expr.forallE (Name.anonymous.str "t")
                  (Expr.const (Name.anonymous.str "PUnit")
                    [Level.param (Name.anonymous.str "u")])
                  (Expr.sort (Level.param (Name.anonymous.str "u_1")))
                  ⟨BinderInfo.default,
                    some (Level.succ
                      (Level.param (Name.anonymous.str "u_1")))⟩))
              (Expr.const ((Name.anonymous.str "PUnit").str "unit")
                [Level.param (Name.anonymous.str "u")])))) =
        some (SetTheory.app (SetTheory.app (punitRecVal V ψ') M) m) := by
      rw [interpExpr, hipartial1, hifv1]
    refine TowerOk.nil (w := m) ?_ ?_ ?_
    · -- the canonical lhs interprets to the folded value
      rw [interpExpr, hipartial2, hiunit]
      show some (SetTheory.app (SetTheory.app (SetTheory.app
        (punitRecVal V ψ') M) m) pt) = some m
      rw [punitRecVal_fold (ψ := ψ') hM hm pt_mem_unitSet]
    · -- the opened rhs body is the minor-premise variable
      simp [Expr.instantiate1, interpExpr, updV]
    · -- the canonical lhs carries truthful annotations
      simp only [AnnotOk]
      refine ⟨⟨⟨trivial, trivial,
          punitRecVal V ψ', M, _, _, _, hirec, hifv0, hmem, hM,
          fun M' hM' => houter M' hM'⟩,
        trivial,
        SetTheory.app (punitRecVal V ψ') M, m,
          (if ψ' u1N = 0 then 0 else Nat.max (ψ' uN) (ψ' u1N)),
          SetTheory.app M pt,
          (fun _ => pi (ψ' u1N) unitSet fun t => SetTheory.app M t),
          hipartial1, hifv1, hm1, hm, fun _ _ => hinner M hM⟩,
        trivial,
        SetTheory.app (SetTheory.app (punitRecVal V ψ') M) m, pt, ψ' u1N,
          unitSet, (fun t => SetTheory.app M t),
          hipartial2, hiunit, hm2, pt_mem_unitSet,
          fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ _)⟩

end Setlec
