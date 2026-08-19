import Setlec.Model.BasisInstall

/-!
# Iota-rule semantics for the pinned basis recursors

For each iota rule, three facts feed the `whnf` soundness of the
reduction step: the interpretation of the (annotated) rule rhs, the
truthfulness of its annotations, and the *fold equation* — the
recursor's value applied through the rule's telescope equals the rhs's
value applied to the non-index prefix and fields.
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


/-- The (annotated) rhs of `Eq.rec`'s single rule. -/
def eqRecRhsA : Expr := ((ConstantInfo.recRules eqRecA).getD 0 default).rhs

/-! The rhs's own lam-tag evaluations. -/

def eqRhsA' (u u1 : Nat) : Nat :=
  if erB u1 = 0 then 0 else Nat.max u (Nat.max (u1 + 1) (erB u1))
def eqRhsAl' (u u1 : Nat) : Nat :=
  if eqRhsA' u u1 = 0 then 0 else Nat.max u (eqRhsA' u u1)

theorem eqRhsA'_eq (u u1 : Nat) :
    eqRhsA' u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold eqRhsA'
  rw [erB_eq]
  by_cases h : u1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact max_eqrec_a'' u u1

theorem eqRhsAl'_eq (u u1 : Nat) :
    eqRhsAl' u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold eqRhsAl'
  rw [eqRhsA'_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero u1))]
    exact max_absorb_l' u (u1 + 1)

/-- Interpretation of the `Eq.rec` rule rhs. -/
theorem interp_eqRec_rhs {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    interpClosed V cval env ψ eqRecRhsA =
      some (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [interpClosed, eqRecRhsA, eqRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', hfindR', hvalR', eqA, eqReflA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, u1N,
    hfindE', hvalE', hfindR', hvalR', eqA, eqReflA,
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl


/-- The `Eq.rec` rule rhs carries truthful annotations. -/
theorem annotOk_eqRec_rhs {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) eqRecRhsA := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [eqRecRhsA, eqRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  have hMSmem : ∀ a', a' ∈ˢ A →
      eqRecMSpace V (ψ u1N) A a' ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hAmem
      (fun b hb => pi_mem_univ (u := 0) (v := ψ u1N + 1)
        (B := fun _ => univ (ψ u1N))
        (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
  have hMSeq : ∀ a', a' ∈ˢ A →
      (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a' := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_congr fun b hb => by rw [eqVal_app₃ hAmem ha' hb]
  have happM : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      SetTheory.app (SetTheory.app M' a')
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a') ∈ˢ
        univ (ψ u1N) := by
    intro a' ha' M' hM'
    rw [eqReflVal_app₂ hAmem ha']
    have hMa : SetTheory.app M' a' ∈ˢ pi (ψ u1N + 1) (eqv a' a')
        (fun _ => univ (ψ u1N)) := by
      have hM'' := hM'
      simp only [eqRecMSpace] at hM''
      exact app_mem hM'' ha' (fun b hb =>
        pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
    exact app_mem hMa (pt_mem_eqv_self a') (fun _ _ => univ_mem_univ (ψ u1N))
  refine ⟨?_, ?_⟩
  · -- opened `λ (a : α), …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro a Sa hSa hamem
    simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
      Option.some.injEq] at hSa
    subst hSa
    refine ⟨?_, ?_⟩
    · -- opened `λ (motive : …), …`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨?_, ⟨_, rfl⟩, ?_⟩
      · -- the motive space type (as in the recursor's type)
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ⟨_, rfl⟩, ?_⟩
        intro b Sb hSb hbmem
        simp [interpExpr, Expr.instantiate1, updV] at hSb
        subst hSb
        refine ⟨?_, ?_⟩
        · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ⟨_, rfl⟩, ?_⟩
          · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1),
                univ (ψ uN),
                (fun X => pi (Nat.max (ψ uN) 1) X fun _ =>
                  pi 1 X fun _ => univ 0),
                ?_, ?_, eqVal_mem, hAmem, fun X hX => eq_fibre_mem hX⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (eqVal V ψ) A, a, Nat.max (ψ uN) 1, A,
                (fun _ => pi 1 A fun _ => univ 0),
                ?_, ?_, eqVal_app_mem hAmem, hamem, fun y _ => ?_⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (SetTheory.app (eqVal V ψ) A) a, b, 1, A,
                (fun _ => univ 0),
                ?_, ?_, eqVal_app₂_mem hAmem hamem, hbmem,
                fun y _ => univ_mem_univ 0⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                hvalE', eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                hvalE', eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · exact pi_mem_univ (u := ψ uN) (v := 1)
                (B := fun _ => univ 0) hAmem
                (fun _ _ => univ_mem_univ 0)
            · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                hvalE', eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
          · intro h Sh hSh hhmem
            refine ⟨trivial, ?_⟩
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨univ (ψ u1N), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, Level.eval, u1N]
            · exact univ_mem_univ (ψ u1N)
        · intro v hv
          obtain rfl := Option.some.inj hv
          refine ⟨pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            (fun _ => univ (ψ u1N)), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              eqA, ConstantInfo.toConstantVal, Level.eval, u1N,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · rw [eqVal_app₃ hAmem hamem hbmem]
            exact pi_mem_univ (u := 0) (v := ψ u1N + 1)
              (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b)
              (fun _ _ => univ_mem_univ (ψ u1N))
      · intro M SM hSM hMmem
        simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
          eqA, ConstantInfo.toConstantVal, Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
        subst hSM
        have hMmem' : M ∈ˢ eqRecMSpace V (ψ u1N) A a := by
          rw [← hMSeq a hamem]
          exact hMmem
        refine ⟨?_, ?_⟩
        · -- opened `λ (refl : motive a (Eq.refl α a)). refl`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ⟨_, rfl⟩, ?_⟩
          · -- the refl-domain annotations (as in the recursor's type)
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                M, a, ψ u1N + 1, A,
                (fun b' => pi (ψ u1N + 1) (eqv a b') fun _ => univ (ψ u1N)),
                ?_, ?_, ?_, hamem, ?_⟩,
              ⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                eqReflVal V ψ, A, 0, univ (ψ uN),
                (fun X => pi 0 X fun x => eqv x x),
                ?_, ?_, eqReflVal_mem, hAmem,
                fun X hX => by
                  exact pi_mem_univ (u := ψ uN) (v := 0) hX
                    (fun x _ => eqv_mem_univ x x)⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (eqReflVal V ψ) A, a, 0, A, (fun x => eqv x x),
                ?_, ?_, eqReflVal_app_mem hAmem, hamem,
                fun x _ => eqv_mem_univ x x⟩,
              SetTheory.app M a,
              SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a,
              ψ u1N + 1, eqv a a, (fun _ => univ (ψ u1N)),
              ?_, ?_, ?_, ?_,
              fun _ _ => univ_mem_univ (ψ u1N)⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            · have := hMmem'
              simp only [eqRecMSpace] at this
              exact this
            · intro b' hb'
              exact pi_mem_univ (u := 0) (v := ψ u1N + 1)
                (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b')
                (fun _ _ => univ_mem_univ (ψ u1N))
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal]
              try rfl
            · have hMa : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
                  (fun _ => univ (ψ u1N)) := by
                have hM'' := hMmem'
                simp only [eqRecMSpace] at hM''
                exact app_mem hM'' hamem (fun b hb =>
                  pi_mem_univ (u := 0) (v := ψ u1N + 1)
                    (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b)
                    (fun _ _ => univ_mem_univ (ψ u1N)))
              exact hMa
            · rw [eqReflVal_app₂ hAmem hamem]
              exact pt_mem_eqv_self a
          · intro r Sr hSr hrmem
            refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨r, SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a),
              ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hSr
              rw [← hSr] at hrmem
              exact hrmem
            · exact happM a hamem M hMmem'
        · intro v hv
          obtain rfl := Option.some.inj hv
          refine ⟨SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun r => r),
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              (fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)),
            ?_, ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
              eqReflA, ConstantInfo.toConstantVal, Level.eval, u1N,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · exact lam_mem (V := V)
              (B := fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r hr => hr
          · exact pi_mem_univ (u := ψ u1N) (v := ψ u1N)
              (B := fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              (happM a hamem M hMmem')
              (fun _ _ => happM a hamem M hMmem')
    · -- fibre-universe of the `a` λ
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.lam (erB (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) (fun M =>
          SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun r => r)),
        pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) (fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))),
        ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
          hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
          Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · refine lam_mem (V := V) (B := fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)))
          fun M hM => ?_
        have hM' : M ∈ˢ eqRecMSpace V (ψ u1N) A a := by
          rw [← hMSeq a hamem]
          exact hM
        exact lam_mem (V := V) (B := fun _ =>
          SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun r hr => hr
      · rw [show Level.eval ψ
            (((Level.param (Name.anonymous.str "u")).imax
              (Level.zero.imax (Level.param (Name.anonymous.str "u_1")).succ)).imax
              ((Level.param (Name.anonymous.str "u_1")).imax
                (Level.param (Name.anonymous.str "u_1")))) =
            if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1) from by
          by_cases hu : ψ (Name.anonymous.str "u_1") = 0 <;>
            simp [Level.eval, uN, u1N, hu, Nat.max_self, max_eqrec_b]]
        rw [erB_eq]
        have hdom : (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
          rw [hMSeq a hamem]
          exact hMSmem a hamem
        have hfibs : ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) →
            (pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
              univ (ψ u1N) := by
          intro M hM
          have hM' : M ∈ˢ eqRecMSpace V (ψ u1N) A a := by
            rw [← hMSeq a hamem]
            exact hM
          have hrd := happM a hamem M hM'
          have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
            (B := fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            hrd (fun _ _ => hrd)
          by_cases hu1 : ψ u1N = 0
          · rw [if_pos hu1] at this
            exact hu1.symm ▸ this
          · rw [if_neg hu1] at this
            rw [show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
            exact this
        have hmem := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
          (v := ψ u1N)
          (B := fun M => pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          hdom hfibs
        by_cases hu1 : ψ u1N = 0
        · rw [if_pos hu1]
          rw [if_pos hu1] at hmem
          exact hmem
        · rw [if_neg hu1]
          rw [if_neg hu1, max_eqrec_b] at hmem
          exact hmem
  · -- fibre-universe of the `α` λ
    intro v hv
    obtain rfl := Option.some.inj hv
    have hafib : ∀ a', a' ∈ˢ A →
        (pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
            fun _ => SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) ∈ˢ
          univ (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro a' ha'
      rw [erB_eq]
      have hdom : (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
          fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
        rw [hMSeq a' ha']
        exact hMSmem a' ha'
      have hfibs : ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
          fun _ => univ (ψ u1N)) →
          (pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
            fun _ => SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) ∈ˢ
            univ (ψ u1N) := by
        intro M hM
        have hM' : M ∈ˢ eqRecMSpace V (ψ u1N) A a' := by
          rw [← hMSeq a' ha']
          exact hM
        have hrd := happM a' ha' M hM'
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app M a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
          hrd (fun _ _ => hrd)
        by_cases hu1 : ψ u1N = 0
        · rw [if_pos hu1] at this
          exact hu1.symm ▸ this
        · rw [if_neg hu1] at this
          rw [show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
          exact this
      have hmem := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
        (v := ψ u1N)
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
          fun _ => SetTheory.app (SetTheory.app M a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
        hdom hfibs
      by_cases hu1 : ψ u1N = 0
      · rw [if_pos hu1]
        rw [if_pos hu1] at hmem
        exact hmem
      · rw [if_neg hu1]
        rw [if_neg hu1, max_eqrec_b] at hmem
        exact hmem
    refine ⟨SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A (fun a =>
      SetTheory.lam (erB (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) fun M =>
        SetTheory.lam (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun r => r),
      pi (eqRhsA' (ψ uN) (ψ u1N)) A (fun a =>
        pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)),
      ?_, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
        hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
        Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · refine lam_mem (V := V) (B := fun a =>
        pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun a ha => ?_
      refine lam_mem (V := V) (B := fun M =>
        pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun M hM => ?_
      exact lam_mem (V := V) (B := fun _ =>
        SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun r hr => hr
    · rw [show Level.eval ψ
          ((Level.param (Name.anonymous.str "u")).imax
            ((((Level.param (Name.anonymous.str "u")).imax
              (Level.zero.imax (Level.param (Name.anonymous.str "u_1")).succ))).imax
              ((Level.param (Name.anonymous.str "u_1")).imax
                (Level.param (Name.anonymous.str "u_1"))))) =
          if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1) from by
        by_cases hu : ψ (Name.anonymous.str "u_1") = 0 <;>
          simp [Level.eval, uN, u1N, hu, Nat.max_self, max_eqrec_b,
            max_absorb_l']]
      rw [eqRhsA'_eq]
      have hmem := pi_mem_univ (u := ψ uN)
        (v := if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1))
        (B := fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        hAmem hafib
      by_cases hu1 : ψ u1N = 0
      · rw [if_pos hu1]
        rw [show (if ψ u1N = 0 then 0
            else Nat.max (ψ uN) (ψ u1N + 1)) = 0 from if_pos hu1] at hmem
        rw [if_pos rfl] at hmem
        exact hmem
      · rw [if_neg hu1]
        have hne : (if ψ u1N = 0 then 0
            else Nat.max (ψ uN) (ψ u1N + 1)) ≠ 0 := by
          rw [if_neg hu1]
          exact max_ne_zero_r' (Nat.succ_ne_zero _)
        rw [if_neg hne, if_neg hu1] at hmem
        rw [show Nat.max (ψ uN) (Nat.max (ψ uN) (ψ u1N + 1)) =
          Nat.max (ψ uN) (ψ u1N + 1) from max_absorb_l' _ _] at hmem
        exact hmem


/-- The fold equation of `Eq.rec`'s rule: the recursor applied through
its telescope (with the major reduced to a reflexivity proof) equals
the rhs applied to the non-index prefix. -/
theorem eqRec_iota {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ')
    {Av av Mv rv bv hv : V}
    (hA : Av ∈ˢ univ (ψ uN)) (ha : av ∈ˢ Av)
    (hM : Mv ∈ˢ eqRecMSpace V (ψ u1N) Av av)
    (hr : rv ∈ˢ SetTheory.app (SetTheory.app Mv av) pt)
    (hb : bv ∈ˢ Av) (hh : hv ∈ˢ eqv av bv) :
    ∃ R, interpClosed V cval env ψ eqRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv)
        hv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Av) av)
        Mv) rv := by
  refine ⟨_, interp_eqRec_rhs hfindE hvalE hfindR hvalR, ?_⟩
  obtain rfl : av = bv := mem_eqv hh
  obtain rfl : hv = pt := mem_univ_zero (eqv_mem_univ av av) hh
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse: both sides are the proof point
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) av)
        pt = pt := by
      simp only [eqRecVal, h0, reduceIte]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt, app_pt, app_pt]
    have hR : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
          SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
            SetTheory.lam (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b =>
                pi (ψ u1N + 1)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  fun _ => univ (ψ u1N)) fun M =>
              SetTheory.lam (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun r => r) Av) av) Mv) rv = pt := by
      rw [show eqRhsAl' (ψ uN) (ψ u1N) = 0 from by
        rw [eqRhsAl'_eq, if_pos h0]]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt]
    rw [hL, hR]
  · -- data levels: both sides compute to the minor premise
    have hMv := hM
    simp only [eqRecMSpace] at hMv
    have hMafib : ∀ b', b' ∈ˢ Av →
        (pi (ψ u1N + 1) (eqv av b') fun _ => univ (ψ u1N)) ∈ˢ
          univ (ψ u1N + 1) :=
      fun b' hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
        (B := fun _ => univ (ψ u1N))
        (eqv_mem_univ av b') (fun _ _ => univ_mem_univ (ψ u1N))
    have hMa : SetTheory.app Mv av ∈ˢ pi (ψ u1N + 1) (eqv av av)
        (fun _ => univ (ψ u1N)) := app_mem hMv ha hMafib
    have hMapt : SetTheory.app (SetTheory.app Mv av) pt ∈ˢ univ (ψ u1N) :=
      app_mem hMa (pt_mem_eqv_self av) (fun _ _ => univ_mem_univ (ψ u1N))
    -- parametric universe facts for the value-side telescopes
    have hMS : ∀ A : V, A ∈ˢ univ (ψ uN) → ∀ a : V, a ∈ˢ A →
        eqRecMSpace V (ψ u1N) A a ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hA'
        (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
    have hMapt' : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        SetTheory.app (SetTheory.app M a) pt ∈ˢ univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      simp only [eqRecMSpace] at hM'
      have hMa' : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
          (fun _ => univ (ψ u1N)) :=
        app_mem hM' ha' (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
      exact app_mem hMa' (pt_mem_eqv_self a)
        (fun _ _ => univ_mem_univ (ψ u1N))
    have hT5 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have h5 : ∀ b, b ∈ˢ A →
          (pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ univ (ψ u1N) := by
        intro b hb'
        have := pi_mem_univ (u := 0) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app M a) pt)
          (eqv_mem_univ a b) (fun _ _ => hMapt' A hA' a ha' M hM')
        rw [if_neg h0] at this
        exact this
      have := pi_mem_univ (u := ψ uN) (v := ψ u1N)
        (B := fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) hA' h5
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 :=
      max_ne_zero_r' h0
    have hT4 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun _ => pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt)
        (hMapt' A hA' a ha' M hM') (fun _ _ => hT5 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this
      exact this
    have hT3 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
        (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt)
        (hMS A hA' a ha') (fun M hM' => hT4 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (Nat.max (ψ uN) (ψ u1N + 1)) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N + 1) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _,
            Nat.max_le.mpr ⟨Nat.le_max_left _ _,
              Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩)
          (Nat.le_max_left _ _)] at this
      exact this
    -- the left fold
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) av)
        pt = rv := by
      simp only [eqRecVal, if_neg h0]
      have h1 := app_lam (v := Nat.max (ψ uN) (ψ u1N + 1)) (a := Av)
        (A := univ (ψ uN)) hA
        (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt)
        (F := fun A => SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a)
            fun M => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun r =>
              SetTheory.lam (ψ u1N) A fun _b =>
                SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r)
        (fun A hA' => lam_mem (V := V) fun a ha' =>
          lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' =>
              lam_mem (V := V) fun b hb' =>
                lam_mem (V := V) fun h hh' => hr')
        (fun A hA' => by
          have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ u1N + 1))
            (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
              (eqRecMSpace V (ψ u1N) A a) fun M =>
              pi (Nat.max (ψ uN) (ψ u1N))
                (SetTheory.app (SetTheory.app M a) pt) fun _ =>
                pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                  SetTheory.app (SetTheory.app M a) pt)
            hA' (fun a ha' => hT3 A hA' a ha')
          rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero _)),
            max_absorb_l'] at this
          exact this)
      rw [h1]
      have h2 := app_lam (v := Nat.max (ψ uN) (ψ u1N + 1)) (a := av)
        (A := Av) ha
        (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
        (F := fun a => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av a) fun M =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun r =>
            SetTheory.lam (ψ u1N) Av fun _b =>
              SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r)
        (fun a ha' => lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' =>
            lam_mem (V := V) fun b hb' =>
              lam_mem (V := V) fun h hh' => hr')
        (fun a ha' => hT3 Av hA a ha')
      rw [h2]
      have h3 := app_lam (v := Nat.max (ψ uN) (ψ u1N)) (a := Mv)
        (A := eqRecMSpace V (ψ u1N) Av av) hM
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M av) pt) fun _ =>
          pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
            SetTheory.app (SetTheory.app M av) pt)
        (F := fun M => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M av) pt) fun r =>
          SetTheory.lam (ψ u1N) Av fun _b =>
            SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r)
        (fun M hM' => lam_mem (V := V) fun r hr' =>
          lam_mem (V := V) fun b hb' =>
            lam_mem (V := V) fun h hh' => hr')
        (fun M hM' => hT4 Av hA av ha M hM')
      rw [h3]
      have h4 := app_lam (v := Nat.max (ψ uN) (ψ u1N)) (a := rv)
        (A := SetTheory.app (SetTheory.app Mv av) pt) hr
        (B := fun _ => pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (F := fun r => SetTheory.lam (ψ u1N) Av fun _b =>
          SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r)
        (fun r hr' => lam_mem (V := V) fun b hb' =>
          lam_mem (V := V) fun h hh' => hr')
        (fun _ _ => hT5 Av hA av ha Mv hM)
      rw [h4]
      have h5 := app_lam (v := ψ u1N) (a := av) (A := Av) ha
        (B := fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (F := fun _b => SetTheory.lam (ψ u1N) (eqv av _b) fun _h => rv)
        (fun b hb' => lam_mem (V := V) fun h hh' => hr)
        (fun b hb' => by
          have := pi_mem_univ (u := 0) (v := ψ u1N)
            (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
            (eqv_mem_univ av b) (fun _ _ => hMapt)
          rw [if_neg h0] at this
          exact this)
      rw [h5]
      exact app_lam (v := ψ u1N) (a := pt) (A := eqv av av)
        (pt_mem_eqv_self av)
        (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
        (F := fun _h => rv)
        (fun _ _ => hr)
        (fun _ _ => hMapt)
    -- the right fold
    have hrd : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      rw [eqReflVal_app₂ hA' ha']
      refine hMapt' A hA' a ha' M ?_
      rw [← show (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a from by
          unfold eqRecMSpace
          exact pi_congr fun b hb' => by rw [eqVal_app₃ hA' ha' hb']]
      exact hM'
    have hMv' : Mv ∈ˢ (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
        fun _ => univ (ψ u1N)) := by
      rw [show (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) Av av from by
          unfold eqRecMSpace
          exact pi_congr fun b hb' => by rw [eqVal_app₃ hA ha hb']]
      exact hM
    have hrfib : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        (pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
        (B := fun _ => SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (hrd A hA' a ha' M hM') (fun _ _ => hrd A hA' a ha' M hM')
      rw [if_neg h0,
        show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
      exact this
    have hMSi : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      rw [show (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a from by
          unfold eqRecMSpace
          exact pi_congr fun b hb' => by rw [eqVal_app₃ hA' ha' hb']]
      exact hMS A hA' a ha'
    have hT3r : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      rw [erB_eq]
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1)) (v := ψ u1N)
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (hMSi A hA' a ha') (fun M hM' => hrfib A hA' a ha' M hM')
      rw [if_neg h0, max_eqrec_b] at this
      exact this
    have hR : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
          SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
            SetTheory.lam (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b =>
                pi (ψ u1N + 1)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  fun _ => univ (ψ u1N)) fun M =>
              SetTheory.lam (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun r => r) Av) av) Mv) rv = rv := by
      have h1 := app_lam (v := eqRhsAl' (ψ uN) (ψ u1N)) (a := Av)
        (A := univ (ψ uN)) hA
        (B := fun A => pi (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (F := fun A => SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r)
        (fun A hA' => lam_mem (V := V) fun a ha' =>
          lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' => hr')
        (fun A hA' => by
          rw [eqRhsAl'_eq, eqRhsA'_eq, if_neg h0]
          have := pi_mem_univ (u := ψ uN)
            (v := Nat.max (ψ uN) (ψ u1N + 1))
            (B := fun a => pi (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
              pi (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun _ => SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            hA' (fun a ha' => hT3r A hA' a ha')
          rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero _)),
            max_absorb_l'] at this
          exact this)
      rw [h1]
      have h2 := app_lam (v := eqRhsA' (ψ uN) (ψ u1N)) (a := av)
        (A := Av) ha
        (B := fun a => pi (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
        (F := fun a => SetTheory.lam (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun r => r)
        (fun a ha' => lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr')
        (fun a ha' => by
          rw [eqRhsA'_eq, if_neg h0]
          exact hT3r Av hA a ha')
      rw [h2]
      have h3 := app_lam (v := erB (ψ u1N)) (a := Mv)
        (A := pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
          fun _ => univ (ψ u1N)) hMv'
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun _ => SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
        (F := fun M => SetTheory.lam (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun r => r)
        (fun M hM' => lam_mem (V := V) fun r hr' => hr')
        (fun M hM' => by
          rw [erB_eq]
          exact hrfib Av hA av ha M hM')
      rw [h3]
      have hrveq : rv ∈ˢ SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av) := by
        rw [eqReflVal_app₂ hA ha]
        exact hr
      exact app_lam (v := ψ u1N) (a := rv)
        (A := SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av)) hrveq
        (B := fun _ => SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
        (F := fun r => r)
        (fun r hr' => hr')
        (fun _ _ => hrd Av hA av ha Mv hMv')
    rw [hL, hR]


/-! ## The `Nat.rec` rules -/

/-- The (annotated) rhs of `Nat.rec`'s zero rule. -/
def natRecZeroRhsA : Expr := ((ConstantInfo.recRules natRecA).getD 0 default).rhs

/-- The (annotated) rhs of `Nat.rec`'s successor rule. -/
def natRecSuccRhsA : Expr := ((ConstantInfo.recRules natRecA).getD 1 default).rhs

/-- Raw-shaped evaluation of the zero rule's minor-premise λ tag. -/
def nrZ (u : Nat) : Nat := if u = 0 then 0 else Nat.max (en11UU u) u

/-- Raw-shaped evaluation of the zero rule's motive λ tag. -/
def nrM (u : Nat) : Nat := if nrZ u = 0 then 0 else Nat.max u (nrZ u)

theorem nrZ_eq (u : Nat) : nrZ u = if u = 0 then 0 else Nat.max 1 u := by
  unfold nrZ
  rw [en11UU_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
      (Nat.le_max_left _ _)

theorem nrM_eq (u : Nat) : nrM u = if u = 0 then 0 else Nat.max 1 u := by
  unfold nrM
  rw [nrZ_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 u ≠ 0)]
    exact max_absorb_r' 1 u

/-- Interpretation of the `Nat.rec` zero rule rhs. -/
theorem interp_natRecZero_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    interpClosed V cval env ψ natRecZeroRhsA =
      some (SetTheory.lam (nrM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _s => z) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  simp only [interpClosed, natRecZeroRhsA, natRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA,
    natSuccA, List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, nrM, nrZ, en11UU, enUU,
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- Interpretation of the `Nat.rec` successor rule rhs. -/
theorem interp_natRecSucc_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ') :
    interpClosed V cval env ψ natRecSuccRhsA =
      some (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  have hfindR' : env.find? ((Name.anonymous.str "Nat").str "rec") = some natRecA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "rec") ψ' = natRecVal V ψ' := hvalR
  simp only [interpClosed, natRecSuccRhsA, natRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', hfindR', hvalR',
    natA, natZeroA, natSuccA,
    List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, enM, enZ, en1U, en11UU, enUU,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', hfindR', hvalR',
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The `Nat.rec` value applied through its telescope is set-theoretic
recursion. -/
theorem natRecVal_fold {Mv zv sv nv : V}
    (hM : Mv ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN))
    (hz : zv ∈ˢ SetTheory.app Mv natzero)
    (hs : sv ∈ˢ pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app Mv n) fun _ =>
        SetTheory.app Mv (natsucc n))
    (hn : nv ∈ˢ omega) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (natRecVal V ψ) Mv) zv) sv) nv = natrec zv sv nv := by
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
    fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
  have hstep : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app Mv k →
      SetTheory.app (SetTheory.app sv k) ih ∈ˢ
        SetTheory.app Mv (natsucc k) := by
    intro k hk ih hih
    have hsfib : ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro n hn'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn')
        (fun _ _ => hMfib (natsucc n) (natsucc_mem hn'))
      by_cases hu : ψ uN = 0
      · simpa [hu] using this
      · simpa [hu, Nat.max_self] using this
    exact app_mem (app_mem hs hk hsfib) hih
      (fun _ _ => hMfib (natsucc k) (natsucc_mem hk))
  by_cases h0 : ψ uN = 0
  · -- Prop collapse: both sides are the proof point
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) nv = pt := by
      simp only [natRecVal, h0, reduceIte]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt]
    rw [hL]
    exact (mem_univ_zero (h0 ▸ hMfib nv hn)
      (natrec_mem hz hstep hn)).symm
  · simp only [natRecVal, if_neg h0]
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hT4 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun t => SetTheory.app M t)
        (omega_mem_univ (V := V))
        (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (hSsp M hM') (fun _ _ => hT4 M hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t)
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have hrecmem : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) →
        ∀ t, t ∈ˢ omega → natrec z s t ∈ˢ SetTheory.app M t := by
      intro M hM' z hz' s hs' t ht'
      refine natrec_mem hz' ?_ ht'
      intro k hk ih hih
      exact app_mem (app_mem hs' hk (hsfib M hM')) hih
        (fun _ _ => app_mem hM' (natsucc_mem hk)
          (fun _ _ => univ_mem_univ (ψ uN)))
    have h1 := app_lam (v := Nat.max 1 (ψ uN)) (a := Mv)
      (A := pi (ψ uN + 1) omega fun _ => univ (ψ uN)) hM
      (B := fun M => pi (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun _ =>
        pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t)
      (F := fun M => SetTheory.lam (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun z =>
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec z s t)
      (fun M hM' => lam_mem (V := V) fun z hz' =>
        lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun t ht' => hrecmem M hM' z hz' s hs' t ht')
      (fun M hM' => hT2 M hM')
    rw [h1]
    have h2 := app_lam (v := Nat.max 1 (ψ uN)) (a := zv)
      (A := SetTheory.app Mv natzero) hz
      (B := fun _ => pi (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun _ =>
        pi (ψ uN) omega fun t => SetTheory.app Mv t)
      (F := fun z => SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec z s t)
      (fun z hz' => lam_mem (V := V) fun s hs' =>
        lam_mem (V := V) fun t ht' => hrecmem Mv hM z hz' s hs' t ht')
      (fun _ _ => hT3 Mv hM)
    rw [h2]
    have h3 := app_lam (v := Nat.max 1 (ψ uN)) (a := sv)
      (A := pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) hs
      (B := fun _ => pi (ψ uN) omega fun t => SetTheory.app Mv t)
      (F := fun s => SetTheory.lam (ψ uN) omega fun t => natrec zv s t)
      (fun s hs' => lam_mem (V := V) fun t ht' =>
        hrecmem Mv hM zv hz s hs' t ht')
      (fun _ _ => hT4 Mv hM)
    rw [h3]
    exact app_lam (v := ψ uN) (a := nv) (A := omega) hn
      (B := fun t => SetTheory.app Mv t)
      (F := fun t => natrec zv sv t)
      (fun t ht' => hrecmem Mv hM zv hz sv hs t ht')
      (fun t ht' => hMfib t ht')


/-- The fold equation of `Nat.rec`'s zero rule. -/
theorem natZero_iota {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    {Mv zv sv : V}
    (hM : Mv ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN))
    (hz : zv ∈ˢ SetTheory.app Mv natzero)
    (hs : sv ∈ˢ pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app Mv n) fun _ =>
        SetTheory.app Mv (natsucc n)) :
    ∃ R, interpClosed V cval env ψ natRecZeroRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) natzero =
      SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv) sv := by
  refine ⟨_, interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc,
    ?_⟩
  rw [natRecVal_fold hM hz hs natzero_mem, natrec_zero]
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
    fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
  by_cases h0 : ψ uN = 0
  · -- Prop collapse: the rhs value is the proof point, and so is `zv`
    have hR : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv) zv) sv = pt := by
      rw [show nrM (ψ uN) = 0 from by rw [nrM_eq, if_pos h0]]
      rw [lam_zero, app_pt, app_pt, app_pt]
    rw [hR]
    exact mem_univ_zero (h0 ▸ hMfib natzero natzero_mem) hz
  · -- data levels: the rhs value projects out the minor premise
    rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by rw [nrM_eq, if_neg h0],
      show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by rw [nrZ_eq, if_neg h0],
      enUU_eq]
    have hSspEq : ∀ M : V,
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) := fun M =>
      pi_congr fun n hn' => by rw [natSuccVal_app hn']
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          SetTheory.app M natzero) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
        (B := fun _ => SetTheory.app M natzero)
        (hSsp M hM')
        (fun _ _ => app_mem hM' natzero_mem
          (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0,
        show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
          Nat.le_antisymm
            (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
            (Nat.le_max_left _ _)] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (ψ uN)
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            SetTheory.app M natzero) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          SetTheory.app M natzero)
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have h1 := app_lam (v := Nat.max 1 (ψ uN)) (a := Mv)
      (A := pi (ψ uN + 1) omega fun _ => univ (ψ uN)) hM
      (B := fun M => pi (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun _ =>
        pi (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          SetTheory.app M natzero)
      (F := fun M => SetTheory.lam (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun z =>
        SetTheory.lam (ψ uN)
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun _s => z)
      (fun M hM' => by
        rw [hSspEq M]
        exact lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' => hz')
      (fun M hM' => hT2 M hM')
    rw [h1]
    have h2 := app_lam (v := Nat.max 1 (ψ uN)) (a := zv)
      (A := SetTheory.app Mv natzero) hz
      (B := fun _ => pi (ψ uN)
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun _ =>
        SetTheory.app Mv natzero)
      (F := fun z => SetTheory.lam (ψ uN)
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        fun _s => z)
      (fun z hz' => by
        rw [hSspEq Mv]
        exact lam_mem (V := V) fun s hs' => hz')
      (fun _ _ => hT3 Mv hM)
    rw [h2]
    rw [hSspEq Mv]
    exact (app_lam (v := ψ uN) (a := sv)
      (A := pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) hs
      (B := fun _ => SetTheory.app Mv natzero)
      (F := fun _s => zv)
      (fun _ _ => hz)
      (fun _ _ => hMfib natzero natzero_mem)).symm

/-- The fold equation of `Nat.rec`'s successor rule. -/
theorem natSucc_iota {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ')
    {Mv zv sv nv : V}
    (hM : Mv ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN))
    (hz : zv ∈ˢ SetTheory.app Mv natzero)
    (hs : sv ∈ˢ pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app Mv n) fun _ =>
        SetTheory.app Mv (natsucc n))
    (hn : nv ∈ˢ omega) :
    ∃ R, interpClosed V cval env ψ natRecSuccRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) (natsucc nv) =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv)
        sv) nv := by
  refine ⟨_, interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc
    hfindR hvalR, ?_⟩
  rw [natRecVal_fold hM hz hs (natsucc_mem hn), natrec_succ zv sv hn]
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
    fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
  have hstep : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app Mv k →
      SetTheory.app (SetTheory.app sv k) ih ∈ˢ
        SetTheory.app Mv (natsucc k) := by
    intro k hk ih hih
    have hsfib : ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro n hn'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn')
        (fun _ _ => hMfib (natsucc n) (natsucc_mem hn'))
      by_cases hu : ψ uN = 0
      · simpa [hu] using this
      · simpa [hu, Nat.max_self] using this
    exact app_mem (app_mem hs hk hsfib) hih
      (fun _ _ => hMfib (natsucc k) (natsucc_mem hk))
  by_cases h0 : ψ uN = 0
  · -- Prop collapse: the rhs value is the proof point, and so is the
    -- applied minor premise
    have hR : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (enM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (en1U (ψ uN))
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun s =>
              SetTheory.lam (ψ uN) omega fun n =>
                SetTheory.app (SetTheory.app s n)
                  (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv) zv)
        sv) nv = pt := by
      rw [show enM (ψ uN) = 0 from by rw [enM_eq, if_pos h0]]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt]
    rw [hR]
    exact mem_univ_zero (h0 ▸ hMfib (natsucc nv) (natsucc_mem hn))
      (hstep nv hn (natrec zv sv nv) (natrec_mem hz hstep hn))
  · -- data levels: the rhs value applies the minor premise to `n` and
    -- the recursive call
    rw [show enM (ψ uN) = Nat.max 1 (ψ uN) from by rw [enM_eq, if_neg h0],
      show enZ (ψ uN) = Nat.max 1 (ψ uN) from by rw [enZ_eq, if_neg h0],
      show en1U (ψ uN) = Nat.max 1 (ψ uN) from by rw [en1U_eq, if_neg h0],
      enUU_eq]
    have hSspEq : ∀ M : V,
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) := fun M =>
      pi_congr fun n hn' => by rw [natSuccVal_app hn']
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hbody : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) →
        ∀ n, n ∈ˢ omega →
        SetTheory.app (SetTheory.app s n)
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (natRecVal V ψ) M) z) s) n) ∈ˢ
          SetTheory.app M (natsucc n) := by
      intro M hM' z hz' s hs' n hn'
      rw [natRecVal_fold hM' hz' hs' hn']
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have hstep' : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app M k →
          SetTheory.app (SetTheory.app s k) ih ∈ˢ
            SetTheory.app M (natsucc k) := by
        intro k hk ih hih
        exact app_mem (app_mem hs' hk (hsfib M hM')) hih
          (fun _ _ => hMfib' (natsucc k) (natsucc_mem hk))
      exact hstep' n hn' _ (natrec_mem hz' hstep' hn')
    have hT4 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n => SetTheory.app M (natsucc n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => app_mem hM' (natsucc_mem hn')
          (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun n => SetTheory.app M (natsucc n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app M (natsucc n))
        (hSsp M hM') (fun _ _ => hT4 M hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun n => SetTheory.app M (natsucc n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun n => SetTheory.app M (natsucc n))
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have h1 := app_lam (v := Nat.max 1 (ψ uN)) (a := Mv)
      (A := pi (ψ uN + 1) omega fun _ => univ (ψ uN)) hM
      (B := fun M => pi (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun _ =>
        pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun n => SetTheory.app M (natsucc n))
      (F := fun M => SetTheory.lam (Nat.max 1 (ψ uN))
        (SetTheory.app M natzero) fun z =>
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s =>
          SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n))
      (fun M hM' => by
        rw [hSspEq M]
        exact lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun n hn' =>
              hbody M hM' z hz' s hs' n hn')
      (fun M hM' => hT2 M hM')
    rw [h1]
    have h2 := app_lam (v := Nat.max 1 (ψ uN)) (a := zv)
      (A := SetTheory.app Mv natzero) hz
      (B := fun _ => pi (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (natsucc n)) fun _ =>
        pi (ψ uN) omega fun n => SetTheory.app Mv (natsucc n))
      (F := fun z => SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        fun s =>
        SetTheory.lam (ψ uN) omega fun n =>
          SetTheory.app (SetTheory.app s n)
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (natRecVal V ψ) Mv) z) s) n))
      (fun z hz' => by
        rw [hSspEq Mv]
        exact lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun n hn' =>
            hbody Mv hM z hz' s hs' n hn')
      (fun _ _ => hT3 Mv hM)
    rw [h2]
    rw [hSspEq Mv]
    have h3 := app_lam (v := Nat.max 1 (ψ uN)) (a := sv)
      (A := pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) hs
      (B := fun _ => pi (ψ uN) omega fun n =>
        SetTheory.app Mv (natsucc n))
      (F := fun s => SetTheory.lam (ψ uN) omega fun n =>
        SetTheory.app (SetTheory.app s n)
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (natRecVal V ψ) Mv) zv) s) n))
      (fun s hs' => lam_mem (V := V) fun n hn' =>
        hbody Mv hM zv hz s hs' n hn')
      (fun _ _ => hT4 Mv hM)
    rw [h3]
    have h4 := app_lam (v := ψ uN) (a := nv) (A := omega) hn
      (B := fun n => SetTheory.app Mv (natsucc n))
      (F := fun n => SetTheory.app (SetTheory.app sv n)
        (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (natRecVal V ψ) Mv) zv) sv) n))
      (fun n hn' => hbody Mv hM zv hz sv hs n hn')
      (fun n hn' => hMfib (natsucc n) (natsucc_mem hn'))
    rw [h4, natRecVal_fold hM hz hs hn]


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


/-- The `Nat.rec` zero rule rhs carries truthful annotations. -/
theorem annotOk_natRecZero_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) natRecZeroRhsA := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  simp only [natRecZeroRhsA, natRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨?_, ⟨_, rfl⟩, ?_⟩
  · -- the motive space `(t : Nat) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro t A hA ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨univ (ψ uN), ?_, ?_⟩
    · simp [Expr.instantiate1, interpExpr, Level.eval, uN]
    · exact univ_mem_univ (ψ uN)
  · intro M A hA hM
    have hA' : A = pi (ψ uN + 1) omega fun _ => univ (ψ uN) := by
      have : interpExpr V cval env ψ 0 (rho0 V)
          (Expr.forallE (Name.anonymous.str "t")
            (Expr.const (Name.anonymous.str "Nat") [])
            (Expr.sort (Level.param (Name.anonymous.str "u")))
            ⟨BinderInfo.default, some (Level.succ (Level.param (Name.anonymous.str "u")))⟩) =
          some (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) := by
        simp only [interpExpr, hfindN', hvalN', natA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, uN]
        rfl
      rw [this] at hA
      exact (Option.some.inj hA).symm
    subst hA'
    have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app M n ∈ˢ univ (ψ uN) :=
      fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
    have hMz : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
      hMfib natzero natzero_mem
    have hsfib : ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro n hn
      have := pi_mem_univ (u := ψ uN) (v := ψ uN)
        (B := fun _ => SetTheory.app M (natsucc n))
        (hMfib n hn)
        (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
      by_cases hu : ψ uN = 0
      · simpa [hu] using this
      · rw [if_neg hu, show Nat.max (ψ uN) (ψ uN) = ψ uN from
          Nat.max_self _] at this
        exact this
    -- the successor space: raw fibres fold to `natsucc` fibres
    have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) :=
      pi_congr fun n hn => by rw [natSuccVal_app hn]
    have hSsp : (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
        univ (nrZ (ψ uN)) := by
      rw [hSspEq, enUU_eq, nrZ_eq]
      by_cases hu : ψ uN = 0
      · rw [if_pos hu]
        have := pi_mem_univ (u := 1) (v := ψ uN)
          (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n))
          (omega_mem_univ (V := V)) hsfib
        rw [if_pos hu] at this
        exact hu ▸ this
      · rw [if_neg hu]
        have := pi_mem_univ (u := 1) (v := ψ uN)
          (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n))
          (omega_mem_univ (V := V)) hsfib
        rw [if_neg hu] at this
        exact this
    -- the s-λ's pi type sits in the z-cod universe
    have hBin : (pi (ψ uN)
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
        (fun _ => SetTheory.app M natzero)) ∈ˢ
        univ (nrZ (ψ uN)) := by
      rw [nrZ_eq]
      have hSsp' := hSsp
      rw [nrZ_eq] at hSsp'
      by_cases hu : ψ uN = 0
      · rw [if_pos hu]
        rw [if_pos hu] at hSsp'
        have := pi_mem_univ (u := 0) (v := ψ uN)
          (B := fun _ => SetTheory.app M natzero)
          hSsp' (fun _ _ => hMz)
        rw [if_pos hu] at this
        exact hu ▸ this
      · rw [if_neg hu]
        rw [if_neg hu] at hSsp'
        have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
          (B := fun _ => SetTheory.app M natzero)
          hSsp' (fun _ _ => hMz)
        rw [if_neg hu,
          show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
            Nat.le_antisymm
              (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
              (Nat.le_max_left _ _)] at this
        exact this
    refine ⟨?_, ?_⟩
    · -- the z-λ over `motive Nat.zero`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, natzero, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
        ?_, ?_, hM, natzero_mem,
        fun _ _ => univ_mem_univ (ψ uN)⟩, ⟨_, rfl⟩, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal]
        try rfl
      intro z Az hAz hz
      have hAz' : Az = SetTheory.app M natzero := by
        simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAz
        exact hAz.symm
      rw [hAz'] at hz
      refine ⟨?_, ?_⟩
      · -- the s-λ over the successor space
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ⟨_, rfl⟩, ?_⟩
        · -- the successor space is annotation-truthful
          try simp only [AnnotOk]
          refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
          intro n An hAn hn
          have hAn' : An = omega := by
            simp [interpExpr, hfindN', hvalN', natA,
              ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAn
            exact hAn.symm
          rw [hAn'] at hn
          refine ⟨?_, ?_⟩
          · -- the ih-∀ inside the successor space
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              M, n, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
              ?_, ?_, hM, hn, fun _ _ => univ_mem_univ (ψ uN)⟩,
              ⟨_, rfl⟩, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            intro ih Aih hAih hih
            refine ⟨?_, ?_⟩
            · -- the body `motive (Nat.succ n)` of the ih-∀
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                ⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                natSuccVal V ψ, n, 1, omega, (fun _ => omega),
                ?_, ?_, natSuccVal_mem, hn, fun _ _ => omega_mem_univ⟩,
                M, SetTheory.app (natSuccVal V ψ) n,
                ψ uN + 1, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hM, ?_, fun _ _ => univ_mem_univ (ψ uN)⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · rw [natSuccVal_app hn]
                exact natsucc_mem hn
            · intro v hv
              obtain rfl := Option.some.inj hv
              refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · rw [natSuccVal_app hn]
                exact hMfib (natsucc n) (natsucc_mem hn)
          · intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                hvalSc', natSuccA, ConstantInfo.toConstantVal,
                Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · rw [show (pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
                  (pi (ψ uN) (SetTheory.app M n) fun _ =>
                    SetTheory.app M (natsucc n)) from
                pi_congr fun _ _ => by rw [natSuccVal_app hn]]
              rw [show Level.eval ψ ((Level.param (Name.anonymous.str "u")).imax
                  (Level.param (Name.anonymous.str "u"))) =
                  enUU (ψ uN) from by
                simp [Level.eval, uN, enUU,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl, enUU_eq]
              by_cases hu : ψ uN = 0
              · rw [hu]
                exact hu ▸ hsfib n hn
              · exact hsfib n hn
        · intro s As hAs hs
          refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
          intro v hv
          obtain rfl := Option.some.inj hv
          refine ⟨z, SetTheory.app M natzero, ?_, hz, hMz⟩
          simp [interpExpr, Expr.instantiate1, updV]
      · -- z-cod slot: the s-λ's value and pi type
        intro v hv
        obtain rfl := Option.some.inj hv
        refine ⟨SetTheory.lam (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _s => z),
          pi (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _ => SetTheory.app M natzero), ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
            hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA, natSuccA,
            ConstantInfo.toConstantVal, Level.eval, uN,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · exact lam_mem (V := V)
            (B := fun _ => SetTheory.app M natzero) fun _ _ => hz
        · rw [show Level.eval ψ (((Level.zero.succ.imax
              ((Level.param (Name.anonymous.str "u")).imax
                (Level.param (Name.anonymous.str "u")))).imax
              (Level.param (Name.anonymous.str "u")))) = nrZ (ψ uN) from by
            simp [Level.eval, uN, nrZ, en11UU, enUU,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl]
          exact hBin
    · -- motive-cod slot: the z-λ pack's value and pi type
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _s => z),
        pi (nrZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _ => SetTheory.app M natzero), ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
          hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA, natSuccA,
          ConstantInfo.toConstantVal, Level.eval, uN,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · exact lam_mem (V := V)
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _ => SetTheory.app M natzero))
          fun z hz => lam_mem (V := V)
            (B := fun _ => SetTheory.app M natzero) fun _ _ => hz
      · rw [show Level.eval ψ ((Level.param (Name.anonymous.str "u")).imax
            ((Level.zero.succ.imax
              ((Level.param (Name.anonymous.str "u")).imax
                (Level.param (Name.anonymous.str "u")))).imax
              (Level.param (Name.anonymous.str "u")))) = nrM (ψ uN) from by
          simp [Level.eval, uN, nrM, nrZ, en11UU, enUU,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl]
        rw [nrM_eq]
        have hBin' := hBin
        rw [nrZ_eq] at hBin'
        by_cases hu : ψ uN = 0
        · rw [if_pos hu]
          rw [if_pos hu] at hBin'
          rw [show nrZ (ψ uN) = 0 from by rw [nrZ_eq, if_pos hu]]
          have := pi_mem_univ (u := ψ uN) (v := 0)
            (B := fun _ => pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              (fun _ => SetTheory.app M natzero))
            hMz (fun _ _ => hBin')
          rw [if_pos rfl] at this
          exact this
        · rw [if_neg hu]
          rw [if_neg hu] at hBin'
          rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
            rw [nrZ_eq, if_neg hu]]
          have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
            (B := fun _ => pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              (fun _ => SetTheory.app M natzero))
            hMz (fun _ _ => hBin')
          rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 (ψ uN) ≠ 0),
            max_absorb_r' 1 (ψ uN)] at this
          exact this



/-- The `Nat.rec` successor rule rhs carries truthful annotations. -/
theorem annotOk_natRecSucc_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) natRecSuccRhsA := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  have hfindR' : env.find? ((Name.anonymous.str "Nat").str "rec") = some natRecA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "rec") ψ' = natRecVal V ψ' := hvalR
  -- the recursor's value inhabits its interpreted type
  obtain ⟨Trec, hTi, hRecT⟩ := natRec_key (env := env) (ψ := ψ)
    hfindN hvalN hfindZ hvalZ hfindSc hvalSc
  rw [interp_natRec_type hfindN hvalN hfindZ hvalZ hfindSc hvalSc] at hTi
  obtain rfl := Option.some.inj hTi
  -- parametric universe facts about an arbitrary motive
  have hMfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      ∀ n, n ∈ˢ omega → SetTheory.app M' n ∈ˢ univ (ψ uN) :=
    fun M' hM' n hn => app_mem hM' hn (fun _ _ => univ_mem_univ (ψ uN))
  have hrawP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      ∀ n, n ∈ˢ omega →
      SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n) ∈ˢ univ (ψ uN) := by
    intro M' hM' n hn
    rw [natSuccVal_app hn]
    exact hMfibP M' hM' (natsucc n) (natsucc_mem hn)
  have hsfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      ∀ n, n ∈ˢ omega →
      (pi (ψ uN) (SetTheory.app M' n) fun _ =>
        SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
        univ (ψ uN) := by
    intro M' hM' n hn
    have := pi_mem_univ (u := ψ uN) (v := ψ uN)
      (B := fun _ => SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
      (hMfibP M' hM' n hn) (fun _ _ => hrawP M' hM' n hn)
    by_cases hu : ψ uN = 0
    · simpa [hu] using this
    · rw [if_neg hu, show Nat.max (ψ uN) (ψ uN) = ψ uN from
        Nat.max_self _] at this
      exact this
  have hspP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
        univ (en11UU (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := 1) (v := enUU (ψ uN))
      (B := fun n => pi (ψ uN) (SetTheory.app M' n) fun _ =>
        SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
      omega_mem_univ
      (fun n hn => by
        try dsimp only
        rw [enUU_eq]
        exact hsfibP M' hM' n hn)
  have htTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
        univ (en1U (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := 1) (v := ψ uN)
      (B := fun t => SetTheory.app M' t)
      omega_mem_univ (fun t ht => hMfibP M' hM' t ht)
  have hs2P : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
        fun _ => pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
        univ (enZ (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN))
      (hspP M' hM') (fun _ _ => htTP M' hM')
  have hzTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (enZ (ψ uN)) (SetTheory.app M' natzero) fun _ =>
        pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
        univ (enM (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := ψ uN) (v := enZ (ψ uN))
      (hMfibP M' hM' natzero natzero_mem) (fun _ _ => hs2P M' hM')
  simp only [natRecSuccRhsA, natRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    AnnotOk]
  refine ⟨?_, ⟨_, rfl⟩, ?_⟩
  · -- the motive space `(t : Nat) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro t A hA ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨univ (ψ uN), ?_, ?_⟩
    · simp [Expr.instantiate1, interpExpr, Level.eval, uN]
    · exact univ_mem_univ (ψ uN)
  · intro M A hA hM
    have hA' : A = pi (ψ uN + 1) omega fun _ => univ (ψ uN) := by
      have : interpExpr V cval env ψ 0 (rho0 V)
          (Expr.forallE (Name.anonymous.str "t")
            (Expr.const (Name.anonymous.str "Nat") [])
            (Expr.sort (Level.param (Name.anonymous.str "u")))
            ⟨BinderInfo.default, some (Level.succ (Level.param (Name.anonymous.str "u")))⟩) =
          some (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) := by
        simp only [interpExpr, hfindN', hvalN', natA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, uN]
        rfl
      rw [this] at hA
      exact (Option.some.inj hA).symm
    subst hA'
    have hMfib := hMfibP M hM
    have hMz : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
      hMfib natzero natzero_mem
    refine ⟨?_, ?_⟩
    · -- the z-λ over `motive Nat.zero`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, natzero, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
        ?_, ?_, hM, natzero_mem,
        fun _ _ => univ_mem_univ (ψ uN)⟩, ⟨_, rfl⟩, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal]
        try rfl
      intro z Az hAz hz
      have hAz' : Az = SetTheory.app M natzero := by
        simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAz
        exact hAz.symm
      rw [hAz'] at hz
      refine ⟨?_, ?_⟩
      · -- the s-λ over the successor space
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ⟨_, rfl⟩, ?_⟩
        · -- the successor space is annotation-truthful
          try simp only [AnnotOk]
          refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
          intro n An hAn hn
          have hAn' : An = omega := by
            simp [interpExpr, hfindN', hvalN', natA,
              ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAn
            exact hAn.symm
          rw [hAn'] at hn
          refine ⟨?_, ?_⟩
          · -- the ih-∀ inside the successor space
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              M, n, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
              ?_, ?_, hM, hn, fun _ _ => univ_mem_univ (ψ uN)⟩,
              ⟨_, rfl⟩, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            intro ih Aih hAih hih
            refine ⟨?_, ?_⟩
            · -- the body `motive (Nat.succ n)` of the ih-∀
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                ⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                natSuccVal V ψ, n, 1, omega, (fun _ => omega),
                ?_, ?_, natSuccVal_mem, hn, fun _ _ => omega_mem_univ⟩,
                M, SetTheory.app (natSuccVal V ψ) n,
                ψ uN + 1, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hM, ?_, fun _ _ => univ_mem_univ (ψ uN)⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · rw [natSuccVal_app hn]
                exact natsucc_mem hn
            · intro v hv
              obtain rfl := Option.some.inj hv
              refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · exact hrawP M hM n hn
          · intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                hvalSc', natSuccA, ConstantInfo.toConstantVal,
                Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · rw [show Level.eval ψ ((Level.param (Name.anonymous.str "u")).imax
                  (Level.param (Name.anonymous.str "u"))) =
                  enUU (ψ uN) from by
                simp [Level.eval, uN, enUU,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl, enUU_eq]
              by_cases hu : ψ uN = 0
              · rw [hu]
                exact hu ▸ hsfibP M hM n hn
              · exact hsfibP M hM n hn
        · intro s As hAs hs
          have hAs' : As = pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n) := by
            simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
              hfindSc', hvalSc', natA, natSuccA,
              ConstantInfo.toConstantVal, Level.eval, uN, enUU,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              at hAs
            rw [← hAs]
            rfl
          rw [hAs'] at hs
          refine ⟨?_, ?_⟩
          · -- the n-λ over `Nat`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
            intro n An hAn hn
            have hAn' : An = omega := by
              simp [interpExpr, hfindN', hvalN', natA,
                ConstantInfo.toConstantVal,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hAn
              exact hAn.symm
            rw [hAn'] at hn
            -- the recursor call chain memberships
            have h1 : SetTheory.app (natRecVal V ψ) M ∈ˢ
                pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
                  pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n' =>
                    pi (ψ uN) (SetTheory.app M n') fun _ =>
                      SetTheory.app M (SetTheory.app (natSuccVal V ψ) n'))
                    fun _ => pi (ψ uN) omega fun t => SetTheory.app M t :=
              app_mem hRecT hM (fun M' hM' => hzTP M' hM')
            have h2 : SetTheory.app (SetTheory.app (natRecVal V ψ) M) z ∈ˢ
                pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n' =>
                  pi (ψ uN) (SetTheory.app M n') fun _ =>
                    SetTheory.app M (SetTheory.app (natSuccVal V ψ) n'))
                  fun _ => pi (ψ uN) omega fun t => SetTheory.app M t :=
              app_mem h1 hz (fun _ _ => hs2P M hM)
            have h3 : SetTheory.app (SetTheory.app (SetTheory.app
                (natRecVal V ψ) M) z) s ∈ˢ
                pi (ψ uN) omega fun t => SetTheory.app M t :=
              app_mem h2 hs (fun _ _ => htTP M hM)
            have h4 : SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n ∈ˢ
                SetTheory.app M n :=
              app_mem h3 hn (fun t ht => hMfib t ht)
            have hsn : SetTheory.app s n ∈ˢ
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n) :=
              app_mem hs hn (fun n' hn' => by
                try dsimp only
                rw [enUU_eq]
                by_cases hu : ψ uN = 0
                · rw [hu]
                  exact hu ▸ hsfibP M hM n' hn'
                · exact hsfibP M hM n' hn')
            refine ⟨?_, ?_⟩
            · -- the body `s n (Nat.rec motive z s n)`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                s, n, enUU (ψ uN), omega,
                (fun n' => pi (ψ uN) (SetTheory.app M n') fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n')),
                ?_, ?_, hs, hn,
                (fun n' hn' => by
                  try dsimp only
                  rw [enUU_eq]
                  by_cases hu : ψ uN = 0
                  · rw [hu]
                    exact hu ▸ hsfibP M hM n' hn'
                  · exact hsfibP M hM n' hn')⟩,
                ⟨⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                  natRecVal V ψ, M, enM (ψ uN),
                  pi (ψ uN + 1) omega (fun _ => univ (ψ uN)),
                  (fun M' => pi (enZ (ψ uN)) (SetTheory.app M' natzero)
                    fun _ => pi (en1U (ψ uN))
                      (pi (enUU (ψ uN)) omega fun n' =>
                        pi (ψ uN) (SetTheory.app M' n') fun _ =>
                          SetTheory.app M'
                            (SetTheory.app (natSuccVal V ψ) n'))
                      fun _ => pi (ψ uN) omega fun t =>
                        SetTheory.app M' t),
                  ?_, ?_, hRecT, hM, fun M' hM' => hzTP M' hM'⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (natRecVal V ψ) M, z, enZ (ψ uN),
                  SetTheory.app M natzero,
                  (fun _ => pi (en1U (ψ uN))
                    (pi (enUU (ψ uN)) omega fun n' =>
                      pi (ψ uN) (SetTheory.app M n') fun _ =>
                        SetTheory.app M
                          (SetTheory.app (natSuccVal V ψ) n'))
                    fun _ => pi (ψ uN) omega fun t => SetTheory.app M t),
                  ?_, ?_, h1, hz, fun _ _ => hs2P M hM⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (SetTheory.app (natRecVal V ψ) M) z, s,
                  en1U (ψ uN),
                  pi (enUU (ψ uN)) omega (fun n' =>
                    pi (ψ uN) (SetTheory.app M n') fun _ =>
                      SetTheory.app M (SetTheory.app (natSuccVal V ψ) n')),
                  (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t),
                  ?_, ?_, h2, hs, fun _ _ => htTP M hM⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (SetTheory.app (SetTheory.app
                    (natRecVal V ψ) M) z) s, n, ψ uN, omega,
                  (fun t => SetTheory.app M t),
                  ?_, ?_, h3, hn, fun t ht => hMfib t ht⟩,
                SetTheory.app s n,
                SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n,
                ψ uN, SetTheory.app M n,
                (fun _ => SetTheory.app M
                  (SetTheory.app (natSuccVal V ψ) n)),
                ?_, ?_, hsn, h4, fun _ _ => hrawP M hM n hn⟩
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
            · -- n-cod slot
              intro v hv
              obtain rfl := Option.some.inj hv
              refine ⟨SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n),
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
              · exact hrawP M hM n hn
          · -- s-cod slot
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n),
              pi (ψ uN) omega fun n =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
              ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
                hfindR', hvalR', natA, natRecA,
                ConstantInfo.toConstantVal, Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · refine lam_mem (V := V) (B := fun n =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
                fun n hn => ?_
              have hsn := app_mem hs hn (fun n' hn' => by
                try dsimp only
                rw [enUU_eq]
                by_cases hu : ψ uN = 0
                · rw [hu]
                  exact hu ▸ hsfibP M hM n' hn'
                · exact hsfibP M hM n' hn')
              have h4 := app_mem (app_mem (app_mem
                (app_mem hRecT hM (fun M' hM' => hzTP M' hM'))
                hz (fun _ _ => hs2P M hM))
                hs (fun _ _ => htTP M hM))
                hn (fun t ht => hMfib t ht)
              exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
            · rw [show Level.eval ψ (Level.zero.succ.imax
                  (Level.param (Name.anonymous.str "u"))) =
                  en1U (ψ uN) from by
                simp [Level.eval, uN, en1U,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl]
              exact pi_mem_univ (u := 1) (v := ψ uN)
                (B := fun n => SetTheory.app M
                  (SetTheory.app (natSuccVal V ψ) n))
                omega_mem_univ (fun n hn => hrawP M hM n hn)
      · -- z-cod slot
        intro v hv
        obtain rfl := Option.some.inj hv
        refine ⟨SetTheory.lam (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s => SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n),
          pi (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
          ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
            hfindR', hvalR', hfindSc', hvalSc', natA, natRecA, natSuccA,
            ConstantInfo.toConstantVal, Level.eval, uN, en1U, enUU,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · refine lam_mem (V := V) (B := fun _ =>
            pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s hs => ?_
          refine lam_mem (V := V) (B := fun n =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun n hn => ?_
          have hsn := app_mem hs hn (fun n' hn' => by
            try dsimp only
            rw [enUU_eq]
            by_cases hu : ψ uN = 0
            · rw [hu]
              exact hu ▸ hsfibP M hM n' hn'
            · exact hsfibP M hM n' hn')
          have h4 := app_mem (app_mem (app_mem
            (app_mem hRecT hM (fun M' hM' => hzTP M' hM'))
            hz (fun _ _ => hs2P M hM))
            hs (fun _ _ => htTP M hM))
            hn (fun t ht => hMfib t ht)
          exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
        · rw [show Level.eval ψ ((Level.zero.succ.imax
              ((Level.param (Name.anonymous.str "u")).imax
                (Level.param (Name.anonymous.str "u")))).imax
              (Level.zero.succ.imax
                (Level.param (Name.anonymous.str "u")))) =
              enZ (ψ uN) from by
            by_cases hu : ψ (Name.anonymous.str "u") = 0 <;>
              simp [Level.eval, enZ, en1U, en11UU, enUU, uN, hu,
                Nat.max_self]]
          exact pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN))
            (hspP M hM)
            (fun _ _ => pi_mem_univ (u := 1) (v := ψ uN)
              (B := fun n => SetTheory.app M
                (SetTheory.app (natSuccVal V ψ) n))
              omega_mem_univ (fun n hn => hrawP M hM n hn))
    · -- motive-cod slot
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
        SetTheory.lam (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s => SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n),
        pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
        ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
          hfindZ', hvalZ', hfindR', hvalR', hfindSc', hvalSc',
          natA, natZeroA, natRecA, natSuccA,
          ConstantInfo.toConstantVal, Level.eval, uN, enZ, en1U, en11UU, enUU,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · refine lam_mem (V := V) (B := fun _ =>
          pi (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun z hz => ?_
        refine lam_mem (V := V) (B := fun _ =>
          pi (ψ uN) omega fun n =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s hs => ?_
        refine lam_mem (V := V) (B := fun n =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun n hn => ?_
        have hsn := app_mem hs hn (fun n' hn' => by
          try dsimp only
          rw [enUU_eq]
          by_cases hu : ψ uN = 0
          · rw [hu]
            exact hu ▸ hsfibP M hM n' hn'
          · exact hsfibP M hM n' hn')
        have h4 := app_mem (app_mem (app_mem
          (app_mem hRecT hM (fun M' hM' => hzTP M' hM'))
          hz (fun _ _ => hs2P M hM))
          hs (fun _ _ => htTP M hM))
          hn (fun t ht => hMfib t ht)
        exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
      · rw [show Level.eval ψ ((Level.param (Name.anonymous.str "u")).imax
            ((Level.zero.succ.imax
              ((Level.param (Name.anonymous.str "u")).imax
                (Level.param (Name.anonymous.str "u")))).imax
              (Level.zero.succ.imax
                (Level.param (Name.anonymous.str "u"))))) =
            enM (ψ uN) from by
          by_cases hu : ψ (Name.anonymous.str "u") = 0 <;>
            simp [Level.eval, enM, enZ, en1U, en11UU, enUU, uN, hu,
              Nat.max_self]]
        exact pi_mem_univ (u := ψ uN) (v := enZ (ψ uN))
          hMz
          (fun _ _ => pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN))
            (hspP M hM)
            (fun _ _ => pi_mem_univ (u := 1) (v := ψ uN)
              (B := fun n => SetTheory.app M
                (SetTheory.app (natSuccVal V ψ) n))
              omega_mem_univ (fun n hn => hrawP M hM n hn)))


/-- The `PSigma'.rec` rule rhs carries truthful annotations. -/
theorem annotOk_psigmaRec_rhs {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaRecRhsA := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' := hvalM
  simp only [psigmaRecRhsA, psigmaRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  have hsigU : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B ∈ˢ
        univ (Nat.max (ψ uN) (ψ vN)) := by
    intro B hB
    rw [psigmaVal_fold hAmem hB]
    exact sigma_mem_univ hAmem (fun x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))
  have hβdomU : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hAmem
      (fun _ _ => univ_mem_univ (ψ vN))
  have hMspU : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) ∈ˢ
      univ (if 1 = 0 then 0 else Nat.max (Nat.max (ψ uN) (ψ vN)) 1) :=
    fun B hB => pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 1)
      (hsigU B hB) (fun _ _ => univ_mem_univ 0)
  -- the fully parametric β-slot tower fact
  have hmk4P : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ) A) B) a) b ∈ˢ
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B := by
    intro B hB a ha b hb
    rw [psigmaVal_fold hAmem hB]
    exact psigmaMkVal_app₄_mem hAmem hB ha hb
  have happMP : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ M, M ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) →
      ∀ x, x ∈ˢ SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B →
      SetTheory.app M x ∈ˢ univ 0 :=
    fun B hB M hM x hx => app_mem hM hx (fun _ _ => univ_mem_univ 0)
  have ht3P : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ M, M ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) →
      (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ univ 0 := by
    intro B hB M hM
    have := pi_mem_univ (u := ψ uN) (v := 0)
      (B := fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      hAmem
      (fun a ha => by
        have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
          app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
        have := pi_mem_univ (u := ψ vN) (v := 0)
          (B := fun b => SetTheory.app M
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
          hBa (fun b hb => happMP B hB M hM _ (hmk4P B hB a ha b hb))
        rw [if_pos rfl] at this
        exact this)
    rw [if_pos rfl] at this
    exact this
  have ht2P : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ M, M ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) →
      (pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ univ 0 := by
    intro B hB M hM
    have := pi_mem_univ (u := 0) (v := 0)
      (B := fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      (ht3P B hB M hM) (fun _ _ => ht3P B hB M hM)
    rw [if_pos rfl] at this
    exact this
  have htBP : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      (pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0)
        fun M => pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
          fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ
        univ 0 := by
    intro B hB
    have := pi_mem_univ
      (u := if 1 = 0 then 0 else Nat.max (Nat.max (ψ uN) (ψ vN)) 1)
      (v := 0)
      (B := fun M => pi 0 (pi 0 A fun a =>
        pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      (hMspU B hB) (fun M hM => ht2P B hB M hM)
    rw [if_pos rfl] at this
    exact this
  refine ⟨?_, ?_⟩
  · -- the β-λ
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ⟨_, rfl⟩, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨univ (ψ vN), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
      · exact univ_mem_univ (ψ vN)
    · intro B SB hSB hBmem
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSB
      subst hSB
      have hBmem' : B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) := hBmem
      refine ⟨?_, ?_⟩
      · -- the motive-λ
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ⟨_, rfl⟩, ?_⟩
        · -- the motive space `(t : PSigma' α β) → Prop`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
              psigmaVal V ψ, A,
              Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1),
              univ (ψ uN),
              (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
                (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                  univ (Nat.max (ψ uN) (ψ vN))),
              ?_, ?_, psigmaVal_mem, hAmem, ?_⟩,
            (by simp [Expr.instantiate1, AnnotOk]),
            SetTheory.app (psigmaVal V ψ) A, B,
            Nat.max (ψ uN) (ψ vN) + 1,
            pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
            (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
            ?_, ?_, psigmaVal_app_mem hAmem, hBmem',
            fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN))⟩,
            ⟨_, rfl⟩, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · intro X hX
            have hdom : (pi (ψ vN + 1) X fun _ => univ (ψ vN)) ∈ˢ
                univ (Nat.max (ψ uN) (ψ vN + 1)) :=
              pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hX
                (fun _ _ => univ_mem_univ (ψ vN))
            exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
              (v := Nat.max (ψ uN) (ψ vN) + 1) hdom
              (fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN)))
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · intro t St hSt htmem
            refine ⟨trivial, ?_⟩
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨univ 0, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
            · exact univ_mem_univ 0
        · intro M SM hSM hMmem
          simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
          subst hSM
          have hMmem' : M ∈ˢ pi 1
              (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              (fun _ => univ 0) := hMmem
          have happM := happMP B hBmem' M hMmem'
          have hmk4 := hmk4P B hBmem'
          refine ⟨?_, ?_⟩
          · -- the mk-λ
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨?_, ⟨_, rfl⟩, ?_⟩
            · -- the minor-premise space
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ⟨_, rfl⟩, ?_⟩
              intro a Sa hSa hamem
              simp [interpExpr, Expr.instantiate1, updV] at hSa
              subst hSa
              refine ⟨?_, ?_⟩
              · -- opened `∀ (snd : β fst), motive (mk …)`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                  (by simp [Expr.instantiate1, AnnotOk]), B, a, ψ vN + 1, A,
                  (fun _ => univ (ψ vN)), ?_, ?_, hBmem', hamem,
                  fun _ _ => univ_mem_univ (ψ vN)⟩, ⟨_, rfl⟩, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV]
                intro b Sb hSb hbmem
                simp [interpExpr, Expr.instantiate1, updV,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff] at hSb
                subst hSb
                refine ⟨?_, ?_⟩
                · -- the body `motive (mk α β fst snd)`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    ⟨⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                      psigmaMkVal V ψ, A,
                      (if Nat.max (ψ uN) (ψ vN) = 0 then 0
                        else Nat.max (ψ uN) (ψ vN + 1)),
                      univ (ψ uN),
                      (fun X => pi (Nat.max (ψ uN) (ψ vN))
                        (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
                          pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
                            pi (Nat.max (ψ uN) (ψ vN))
                              (SetTheory.app B' a') fun _ =>
                              sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x =>
                                SetTheory.app B' x),
                      ?_, ?_, psigmaMkVal_mem, hAmem,
                      fun X hX => psigmaMk_space1 hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (psigmaMkVal V ψ) A, B,
                      Nat.max (ψ uN) (ψ vN),
                      pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
                      (fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
                        pi (Nat.max (ψ uN) (ψ vN))
                          (SetTheory.app B' a') fun _ =>
                          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                            SetTheory.app B' x),
                      ?_, ?_, psigmaMkVal_app_mem hAmem, hBmem',
                      fun B' hB' => psigmaMk_space2 hAmem hB'⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B,
                      a, Nat.max (ψ uN) (ψ vN), A,
                      (fun a' => pi (Nat.max (ψ uN) (ψ vN))
                        (SetTheory.app B a') fun _ =>
                        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                          SetTheory.app B x),
                      ?_, ?_, psigmaMkVal_app₂_mem hAmem hBmem', hamem,
                      fun a' ha' => psigmaMk_space3 hAmem hBmem' ha'⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (SetTheory.app
                        (psigmaMkVal V ψ) A) B) a,
                      b, Nat.max (ψ uN) (ψ vN), SetTheory.app B a,
                      (fun _ => sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                        SetTheory.app B x),
                      ?_, ?_, psigmaMkVal_app₃_mem hAmem hBmem' hamem, hbmem,
                      fun _ _ => sigma_mem_univ hAmem (fun x hx =>
                        app_mem hBmem' hx fun _ _ => univ_mem_univ (ψ vN))⟩,
                    M,
                    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                      (psigmaMkVal V ψ) A) B) a) b,
                    1,
                    SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B,
                    (fun _ => univ 0),
                    ?_, ?_, hMmem', hmk4 a hamem b hbmem,
                    fun _ _ => univ_mem_univ 0⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                · -- fibre-universe of `snd` (annotation `0`)
                  intro v hv
                  obtain rfl := Option.some.inj hv
                  refine ⟨SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b), ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · exact happM _ (hmk4 a hamem b hbmem)
              · -- fibre-universe of `fst` (annotation `imax v 0`)
                intro v hv
                obtain rfl := Option.some.inj hv
                refine ⟨pi 0 (SetTheory.app B a) (fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b)), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                    hvalM', psigmaMkA, ConstantInfo.toConstantVal, Level.eval,
                    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                  try rfl
                · have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                    app_mem hBmem' hamem fun _ _ => univ_mem_univ (ψ vN)
                  exact pi_mem_univ (u := ψ vN) (v := 0) hBa
                    (fun b hb => happM _ (hmk4 a hamem b hb))
            · intro m Sm hSm hmmem
              simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                hfindM', hvalM', psigmaA, psigmaMkA,
                ConstantInfo.toConstantVal, Level.eval,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hSm
              subst hSm
              have hmmem' : m ∈ˢ pi 0 A fun a =>
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                        a) b) := hmmem
              have hma : ∀ a, a ∈ˢ A → SetTheory.app m a ∈ˢ
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                        a) b) := by
                intro a ha
                refine app_mem hmmem' ha (fun a' ha' => ?_)
                have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
                  app_mem hBmem' ha' fun _ _ => univ_mem_univ (ψ vN)
                have := pi_mem_univ (u := ψ vN) (v := 0)
                  (B := fun b => SetTheory.app M
                    (SetTheory.app (SetTheory.app (SetTheory.app
                      (SetTheory.app (psigmaMkVal V ψ) A) B) a') b))
                  hBa (fun b hb => happM _ (hmk4 a' ha' b hb))
                rw [if_pos rfl] at this
                exact this
              have hmab : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
                  SetTheory.app (SetTheory.app m a) b ∈ˢ
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                        a) b) := by
                intro a ha b hb
                exact app_mem (hma a ha) hb
                  (fun b' hb' => happM _ (hmk4 a ha b' hb'))
              refine ⟨?_, ?_⟩
              · -- the fst-λ
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
                intro a Sa hSa hamem
                have hSa' : Sa = A := by
                  simp [interpExpr, Expr.instantiate1, updV,
                    -ite_eq_left_iff, -ite_eq_right_iff,
                    -Nat.max_eq_zero_iff] at hSa
                  exact hSa.symm
                rw [hSa'] at hamem
                refine ⟨?_, ?_⟩
                · -- the snd-λ
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                    (by simp [Expr.instantiate1, AnnotOk]),
                    B, a, ψ vN + 1, A, (fun _ => univ (ψ vN)),
                    ?_, ?_, hBmem', hamem,
                    fun _ _ => univ_mem_univ (ψ vN)⟩, ⟨_, rfl⟩, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                  intro b Sb hSb hbmem
                  have hSb' : Sb = SetTheory.app B a := by
                    simp [interpExpr, Expr.instantiate1, updV,
                      -ite_eq_left_iff, -ite_eq_right_iff,
                      -Nat.max_eq_zero_iff] at hSb
                    exact hSb.symm
                  rw [hSb'] at hbmem
                  refine ⟨?_, ?_⟩
                  · -- the body `mk fst snd`
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      m, a, 0, A,
                      (fun a' => pi 0 (SetTheory.app B a') fun b' =>
                        SetTheory.app M (SetTheory.app (SetTheory.app
                          (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                            A) B) a') b')),
                      ?_, ?_, hmmem', hamem,
                      (fun a' ha' => by
                        try dsimp only
                        have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
                          app_mem hBmem' ha' fun _ _ =>
                            univ_mem_univ (ψ vN)
                        have := pi_mem_univ (u := ψ vN) (v := 0)
                          (B := fun b' => SetTheory.app M
                            (SetTheory.app (SetTheory.app (SetTheory.app
                              (SetTheory.app (psigmaMkVal V ψ) A) B)
                                a') b'))
                          hBa (fun b' hb' =>
                            happM _ (hmk4 a' ha' b' hb'))
                        rw [if_pos rfl] at this
                        exact this)⟩,
                      (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app m a, b, 0, SetTheory.app B a,
                      (fun b' => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b')),
                      ?_, ?_, hma a hamem, hbmem,
                      (fun b' hb' => happM _ (hmk4 a hamem b' hb'))⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                  · -- snd-cod slot (annotation `0`)
                    intro v hv
                    obtain rfl := Option.some.inj hv
                    refine ⟨SetTheory.app (SetTheory.app m a) b,
                      SetTheory.app M (SetTheory.app (SetTheory.app
                        (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                          A) B) a) b),
                      ?_, hmab a hamem b hbmem,
                      happM _ (hmk4 a hamem b hbmem)⟩
                    simp [interpExpr, Expr.instantiate1, updV]
                · -- fst-cod slot (annotation `imax v 0`)
                  intro v hv
                  obtain rfl := Option.some.inj hv
                  refine ⟨SetTheory.lam 0 (SetTheory.app B a) fun b =>
                    SetTheory.app (SetTheory.app m a) b,
                    pi 0 (SetTheory.app B a) fun b =>
                      SetTheory.app M (SetTheory.app (SetTheory.app
                        (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                          A) B) a) b),
                    ?_, ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV,
                      -ite_eq_left_iff, -ite_eq_right_iff,
                      -Nat.max_eq_zero_iff]
                    try rfl
                  · exact lam_mem (V := V)
                      (B := fun b => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                      fun b hb => hmab a hamem b hb
                  · have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                      app_mem hBmem' hamem fun _ _ => univ_mem_univ (ψ vN)
                    have := pi_mem_univ (u := ψ vN) (v := 0)
                      (B := fun b => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                      hBa (fun b hb => happM _ (hmk4 a hamem b hb))
                    rw [if_pos rfl] at this
                    exact this
              · -- mk-cod slot (annotation `imax u (imax v 0)`)
                intro v hv
                obtain rfl := Option.some.inj hv
                refine ⟨SetTheory.lam 0 A fun a =>
                  SetTheory.lam 0 (SetTheory.app B a) fun b =>
                    SetTheory.app (SetTheory.app m a) b,
                  pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                        A) B) a) b),
                  ?_, ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV,
                    -ite_eq_left_iff, -ite_eq_right_iff,
                    -Nat.max_eq_zero_iff]
                  try rfl
                · exact lam_mem (V := V)
                    (B := fun a => pi 0 (SetTheory.app B a) fun b =>
                      SetTheory.app M (SetTheory.app (SetTheory.app
                        (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                          A) B) a) b))
                    fun a ha => lam_mem (V := V)
                      (B := fun b => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                      fun b hb => hmab a ha b hb
                · exact ht3P B hBmem' M hMmem'
          · -- motive-cod slot
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨SetTheory.lam 0 (pi 0 A fun a =>
              pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b))
              fun mk => SetTheory.lam 0 A fun a =>
                SetTheory.lam 0 (SetTheory.app B a) fun b =>
                  SetTheory.app (SetTheory.app mk a) b,
              pi 0 (pi 0 A fun a =>
                pi 0 (SetTheory.app B a) fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b))
              fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b),
              ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
                psigmaMkA, ConstantInfo.toConstantVal, Level.eval,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · refine lam_mem (V := V)
                (B := fun _ => pi 0 A fun a =>
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                        A) B) a) b))
                fun mk hmk => ?_
              have hmka : ∀ a, a ∈ˢ A → SetTheory.app mk a ∈ˢ
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                        A) B) a) b) := by
                intro a ha
                refine app_mem hmk ha (fun a' ha' => ?_)
                have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
                  app_mem hBmem' ha' fun _ _ => univ_mem_univ (ψ vN)
                have := pi_mem_univ (u := ψ vN) (v := 0)
                  (B := fun b' => SetTheory.app M
                    (SetTheory.app (SetTheory.app (SetTheory.app
                      (SetTheory.app (psigmaMkVal V ψ) A) B) a') b'))
                  hBa (fun b' hb' => happM _ (hmk4 a' ha' b' hb'))
                rw [if_pos rfl] at this
                exact this
              refine lam_mem (V := V)
                (B := fun a => pi 0 (SetTheory.app B a) fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                      A) B) a) b))
                fun a ha => ?_
              refine lam_mem (V := V)
                (B := fun b => SetTheory.app M
                  (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                fun b hb => ?_
              exact app_mem (hmka a ha) hb
                (fun b' hb' => happM _ (hmk4 a ha b' hb'))
            · exact ht2P B hBmem' M hMmem'
      · -- β-cod slot
        intro v hv
        obtain rfl := Option.some.inj hv
        refine ⟨SetTheory.lam 0
          (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _ => univ 0)
          fun M => SetTheory.lam 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun mk => SetTheory.lam 0 A fun a =>
              SetTheory.lam 0 (SetTheory.app B a) fun b =>
                SetTheory.app (SetTheory.app mk a) b,
          pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _ => univ 0)
          fun M => pi 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b),
          ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            hfindM', hvalM', psigmaA, psigmaMkA,
            ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · refine lam_mem (V := V)
            (B := fun M => pi 0 (pi 0 A fun a =>
              pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b))
              fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b))
            fun M hM => ?_
          have happM := happMP B hBmem' M hM
          refine lam_mem (V := V)
            (B := fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun mk hmk => ?_
          have hmka : ∀ a, a ∈ˢ A → SetTheory.app mk a ∈ˢ
              pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b) := by
            intro a ha
            refine app_mem hmk ha (fun a' ha' => ?_)
            have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
              app_mem hBmem' ha' fun _ _ => univ_mem_univ (ψ vN)
            have := pi_mem_univ (u := ψ vN) (v := 0)
              (B := fun b' => SetTheory.app M
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (psigmaMkVal V ψ) A) B) a') b'))
              hBa (fun b' hb' =>
                happM _ (hmk4P B hBmem' a' ha' b' hb'))
            rw [if_pos rfl] at this
            exact this
          refine lam_mem (V := V)
            (B := fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun a ha => ?_
          refine lam_mem (V := V)
            (B := fun b => SetTheory.app M
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
            fun b hb => ?_
          exact app_mem (hmka a ha) hb
            (fun b' hb' => happM _ (hmk4P B hBmem' a ha b' hb'))
        · exact htBP B hBmem'
  · -- α-cod slot
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨SetTheory.lam 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B => SetTheory.lam 0
        (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
          fun _ => univ 0)
        fun M => SetTheory.lam 0 (pi 0 A fun a =>
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
          fun mk => SetTheory.lam 0 A fun a =>
            SetTheory.lam 0 (SetTheory.app B a) fun b =>
              SetTheory.app (SetTheory.app mk a) b,
      pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ)
          A) B) fun _ => univ 0)
        fun M => pi 0 (pi 0 A fun a =>
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
          fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b),
      ?_, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
        hfindM', hvalM', psigmaA, psigmaMkA,
        ConstantInfo.toConstantVal, Level.eval, uN, vN,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · refine lam_mem (V := V)
        (B := fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app
            (psigmaVal V ψ) A) B) fun _ => univ 0)
          fun M => pi 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
        fun B hB => ?_
      refine lam_mem (V := V)
        (B := fun M => pi 0 (pi 0 A fun a =>
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
          fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
        fun M hM => ?_
      have happM := happMP B hB M hM
      refine lam_mem (V := V)
        (B := fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app
            (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
              a) b))
        fun mk hmk => ?_
      have hmka : ∀ a, a ∈ˢ A → SetTheory.app mk a ∈ˢ
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b) := by
        intro a ha
        refine app_mem hmk ha (fun a' ha' => ?_)
        have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
          app_mem hB ha' fun _ _ => univ_mem_univ (ψ vN)
        have := pi_mem_univ (u := ψ vN) (v := 0)
          (B := fun b' => SetTheory.app M
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a') b'))
          hBa (fun b' hb' => happM _ (hmk4P B hB a' ha' b' hb'))
        rw [if_pos rfl] at this
        exact this
      refine lam_mem (V := V)
        (B := fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app
            (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
              a) b))
        fun a ha => ?_
      refine lam_mem (V := V)
        (B := fun b => SetTheory.app M
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun b hb => ?_
      exact app_mem (hmka a ha) hb
        (fun b' hb' => happM _ (hmk4P B hB a ha b' hb'))
    · have := pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1)) (v := 0)
        (B := fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app
            (psigmaVal V ψ) A) B) fun _ => univ 0)
          fun M => pi 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
        hβdomU (fun B hB => htBP B hB)
      rw [if_pos rfl] at this
      exact this


/-! ## Claims-side glue

Per rule, one lemma packaging exactly what the `whnfCore` iota-branch
soundness needs: the rule-rhs interpretation, the fold equation, and the
membership facts that let the reduct's `AnnotOk` app-chain be
reassembled.  The membership hypotheses are the ∃-witnesses of the
*original* application chain's `AnnotOk`; canonical domains are
recovered with `lam_dom` away from the Prop collapse, and under the
collapse everything is the proof point. -/

/-- One `AnnotOk`-app typing slot. -/
def AppSlot (f a : V) : Prop :=
  ∃ vE A B, f ∈ˢ pi vE A (B : V → V) ∧ a ∈ˢ A ∧
    ∀ x, x ∈ˢ A → B x ∈ˢ univ vE

/-- Away from `pi 0`, an abstraction's membership transfers elements of
the pi's domain into its own. -/
theorem lam_dom_of_ne {w vE : Nat} {D A : V} {F : V → V} {B : V → V}
    (h : SetTheory.lam w D F ∈ˢ pi vE A B) (hw : w ≠ 0) :
    ∀ x, x ∈ˢ A → x ∈ˢ D := by
  by_cases hvE : vE = 0
  · subst hvE
    exact absurd (mem_pi_zero h) (lam_ne_pt hw)
  · exact lam_dom h hvE hw

/-- The proof point inhabits every trivial Prop-pi. -/
theorem pt_mem_pi_unit {A : V} : (pt : V) ∈ˢ pi 0 A fun _ => unitSet := by
  have := lam_mem (V := V) (v := 0) (A := A) (F := fun _ => pt)
    (B := fun _ => unitSet) (fun _ _ => pt_mem_unitSet)
  rw [lam_zero] at this
  exact this

/-- Claims glue for the `PUnit.rec` rule. -/
theorem punitIota_claims {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt)
    {Mv mv tv : V} {vE1 vE2 : Nat} {A1 A2 : V} {B1 B2 : V → V}
    (h1 : (punitRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hM : Mv ∈ˢ A1)
    (h2 : SetTheory.app (punitRecVal V ψ) Mv ∈ˢ pi vE2 A2 B2)
    (hm : mv ∈ˢ A2)
    (htv : tv = pt) :
    ∃ R, interpClosed V cval env ψ punitRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ) Mv) mv)
        tv = SetTheory.app (SetTheory.app R Mv) mv ∧
      AppSlot (V := V) R Mv ∧ AppSlot (V := V) (SetTheory.app R Mv) mv := by
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse: recursor and reduct values are the proof point
    refine ⟨_, interp_punitRec_rhs hfindP hvalP hfindU hvalU, ?_, ?_, ?_⟩
    · rw [show (punitRecVal V ψ : V) = pt from by
        simp only [punitRecVal, h0, reduceIte]; exact lam_zero]
      rw [show (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) = pt from by
        rw [if_pos h0]; exact lam_zero]
      simp only [app_pt]
    · refine ⟨0, A1, fun _ => unitSet, ?_, hM, fun _ _ => unitSet_mem_univ 0⟩
      rw [show (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) = pt from by
        rw [if_pos h0]; exact lam_zero]
      exact pt_mem_pi_unit (V := V)
    · refine ⟨0, A2, fun _ => unitSet, ?_, hm, fun _ _ => unitSet_mem_univ 0⟩
      rw [show (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) = pt from by
        rw [if_pos h0]; exact lam_zero]
      rw [app_pt]
      exact pt_mem_pi_unit (V := V)
  · -- data: recover the canonical memberships and fold
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 := max_ne_zero_r' h0
    have h1' := h1
    rw [show (punitRecVal V ψ : V) = SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) (fun M =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
            fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m) from by
      simp only [punitRecVal, if_neg h0]] at h1'
    have hMc : Mv ∈ˢ pi (ψ u1N + 1) unitSet (fun _ => univ (ψ u1N)) :=
      lam_dom_of_ne h1' hwne Mv hM
    have hMpt : SetTheory.app Mv pt ∈ˢ univ (ψ u1N) :=
      app_mem hMc pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
    have hspace : ∀ M : V, SetTheory.app M pt ∈ˢ univ (ψ u1N) →
        (pi (ψ u1N) unitSet fun _ => SetTheory.app M pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro M hMpt'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N)) (v := ψ u1N)
        (B := fun _ => SetTheory.app M pt)
        (unitSet_mem_univ _) (fun _ _ => hMpt')
      rw [if_neg h0, show Nat.max (Nat.max (ψ uN) (ψ u1N)) (ψ u1N) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
          (Nat.le_max_left _ _)] at this
      exact this
    have happ1 : SetTheory.app (punitRecVal V ψ) Mv =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app Mv pt)
          fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m := by
      rw [show (punitRecVal V ψ : V) = SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) (fun M =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
              fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m) from by
        simp only [punitRecVal, if_neg h0]]
      refine app_lam hMc
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
      rw [if_neg hwne, show Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this
      exact this
    have h2' := h2
    rw [happ1] at h2'
    have hmc : mv ∈ˢ SetTheory.app Mv pt :=
      lam_dom_of_ne h2' hwne mv hm
    obtain ⟨R', hR'i, hfold⟩ := punitRec_iota hfindP hvalP hfindU hvalU
      hMc hmc (htv.symm ▸ pt_mem_unitSet)
    rw [interp_punitRec_rhs hfindP hvalP hfindU hvalU] at hR'i
    obtain rfl := Option.some.inj hR'i
    refine ⟨_, interp_punitRec_rhs hfindP hvalP hfindU hvalU, hfold, ?_, ?_⟩
    · refine ⟨if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N),
        pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N),
        fun M => pi (ψ u1N) (SetTheory.app M pt) fun _ =>
          SetTheory.app M pt,
        ?_, hMc, ?_⟩
      · exact lam_mem (V := V)
          (B := fun M => pi (ψ u1N) (SetTheory.app M pt) fun _ =>
            SetTheory.app M pt)
          fun M hM' => lam_mem (V := V)
            (B := fun _ => SetTheory.app M pt) fun m hm' => hm'
      · intro M hM'
        have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app M pt) hMpt' (fun _ _ => hMpt')
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _] at this
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _]
        exact this
    · have happR : SetTheory.app (SetTheory.lam
          (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) Mv =
          SetTheory.lam (ψ u1N) (SetTheory.app Mv pt) fun m => m := by
        refine app_lam hMc
          (B := fun M => pi (ψ u1N) (SetTheory.app M pt) fun _ =>
            SetTheory.app M pt)
          (fun M hM' => lam_mem (V := V)
            (B := fun _ => SetTheory.app M pt) fun m hm' => hm')
          (fun M hM' => ?_)
        have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app M pt) hMpt' (fun _ _ => hMpt')
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _] at this
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _]
        exact this
      refine ⟨ψ u1N, SetTheory.app Mv pt, fun _ => SetTheory.app Mv pt,
        ?_, hmc, fun _ _ => hMpt⟩
      rw [happR]
      exact lam_mem (V := V) (B := fun _ => SetTheory.app Mv pt)
        fun m hm' => hm'


/-- Claims glue for the `PSigma'.rec` rule (Prop-valued motive: both
sides of the fold are the proof point, for any major value). -/
theorem psigmaIota_claims {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ')
    {Av Bv Mv mkv tv av bv : V} {S1 S2 S3 S4 S5 S6 : V}
    (hAv : Av ∈ˢ S1) (hBv : Bv ∈ˢ S2) (hMv : Mv ∈ˢ S3)
    (hmkv : mkv ∈ˢ S4) (hav : av ∈ˢ S5) (hbv : bv ∈ˢ S6) :
    ∃ R, interpClosed V cval env ψ psigmaRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaRecVal V ψ) Av) Bv) Mv) mkv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app R Av) Bv) Mv) mkv) av) bv ∧
      AppSlot (V := V) R Av ∧
      AppSlot (V := V) (SetTheory.app R Av) Bv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Av) Bv) Mv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app R Av)
        Bv) Mv) mkv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app R Av) Bv) Mv) mkv) av ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app R Av) Bv) Mv) mkv) av) bv := by
  refine ⟨_, interp_psigmaRec_rhs hfindS hvalS hfindM hvalM, ?_⟩
  have hRpt : (SetTheory.lam 0 (univ (ψ uN)) fun A =>
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
                SetTheory.app (SetTheory.app mk a) b) = (pt : V) := lam_zero
  have hrec_pt : (psigmaRecVal V ψ : V) = pt := by
    simp only [psigmaRecVal]; exact lam_zero
  rw [hRpt, hrec_pt]
  simp only [app_pt]
  exact ⟨trivial,
    ⟨0, S1, fun _ => unitSet, pt_mem_pi_unit (V := V), hAv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S2, fun _ => unitSet, pt_mem_pi_unit (V := V), hBv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S3, fun _ => unitSet, pt_mem_pi_unit (V := V), hMv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S4, fun _ => unitSet, pt_mem_pi_unit (V := V), hmkv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S5, fun _ => unitSet, pt_mem_pi_unit (V := V), hav,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S6, fun _ => unitSet, pt_mem_pi_unit (V := V), hbv,
      fun _ _ => unitSet_mem_univ 0⟩⟩


/-- Claims glue for the `Nat.rec` zero rule. -/
theorem natZeroIota_claims {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    {Mv zv sv tv : V} {vE1 vE2 vE3 : Nat} {A1 A2 A3 : V} {B1 B2 B3 : V → V}
    (h1 : (natRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hM : Mv ∈ˢ A1)
    (h2 : SetTheory.app (natRecVal V ψ) Mv ∈ˢ pi vE2 A2 B2) (hz : zv ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv ∈ˢ pi vE3 A3 B3)
    (hs : sv ∈ˢ A3)
    (htv : tv = natzero) :
    ∃ R, interpClosed V cval env ψ natRecZeroRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv) sv ∧
      AppSlot (V := V) R Mv ∧
      AppSlot (V := V) (SetTheory.app R Mv) zv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Mv) zv) sv := by
  subst htv
  by_cases h0 : ψ uN = 0
  · -- Prop collapse
    refine ⟨_, interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc, ?_⟩
    have hRpt : (SetTheory.lam (nrM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _s => z) = (pt : V) := by
      rw [show nrM (ψ uN) = 0 from by rw [nrM_eq, if_pos h0]]
      exact lam_zero
    have hrec_pt : (natRecVal V ψ : V) = pt := by
      simp only [natRecVal, h0, reduceIte]
      exact lam_zero
    rw [hRpt, hrec_pt]
    simp only [app_pt]
    exact ⟨trivial,
      ⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hM,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), hz,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hs,
        fun _ _ => unitSet_mem_univ 0⟩⟩
  · -- data levels
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hrec_lam : (natRecVal V ψ : V) = SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      simp only [natRecVal, if_neg h0]
    have h1' := h1
    rw [hrec_lam] at h1'
    have hMc : Mv ∈ˢ pi (ψ uN + 1) omega (fun _ => univ (ψ uN)) :=
      lam_dom_of_ne h1' hwne Mv hM
    have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
      fun n hn' => app_mem hMc hn' (fun _ _ => univ_mem_univ (ψ uN))
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hT4 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun t => SetTheory.app M t)
        (omega_mem_univ (V := V))
        (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0] at this
      exact this
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (hSsp M hM') (fun _ _ => hT4 M hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t)
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have hrecmem : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) →
        ∀ t, t ∈ˢ omega → natrec z s t ∈ˢ SetTheory.app M t := by
      intro M hM' z hz' s hs' t ht'
      refine natrec_mem hz' ?_ ht'
      intro k hk ih hih
      exact app_mem (app_mem hs' hk (hsfib M hM')) hih
        (fun _ _ => app_mem hM' (natsucc_mem hk)
          (fun _ _ => univ_mem_univ (ψ uN)))
    have happ1 : SetTheory.app (natRecVal V ψ) Mv =
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app Mv natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      rw [hrec_lam]
      exact app_lam hMc
        (B := fun M => pi (Nat.max 1 (ψ uN))
          (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t)
        (fun M hM' => lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun t ht' => hrecmem M hM' z hz' s hs' t ht')
        (fun M hM' => hT2 M hM')
    have h2' := h2
    rw [happ1] at h2'
    have hzc : zv ∈ˢ SetTheory.app Mv natzero :=
      lam_dom_of_ne h2' hwne zv hz
    have happ2 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv =
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec zv s t := by
      rw [happ1]
      exact app_lam hzc
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app Mv t)
        (fun z hz' => lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun t ht' => hrecmem Mv hMc z hz' s hs' t ht')
        (fun _ _ => hT3 Mv hMc)
    have h3' := h3
    rw [happ2] at h3'
    have hsc : sv ∈ˢ (pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) :=
      lam_dom_of_ne h3' hwne sv hs
    obtain ⟨R', hR'i, hfold⟩ := natZero_iota hfindN hvalN hfindZ hvalZ
      hfindSc hvalSc hMc hzc hsc
    rw [interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc]
      at hR'i
    obtain rfl := Option.some.inj hR'i
    refine ⟨_, interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc, hfold, ?_, ?_, ?_⟩
    · -- R applied to the motive
      refine ⟨Nat.max 1 (ψ uN),
        pi (ψ uN + 1) omega fun _ => univ (ψ uN),
        fun M => pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero,
        ?_, hMc, ?_⟩
      · rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrM_eq, if_neg h0]]
        refine lam_mem (V := V) fun M hM' => ?_
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        refine lam_mem (V := V) fun z hz' => ?_
        exact lam_mem (V := V) fun _s _ => hz'
      · intro M hM'
        have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) :=
          pi_congr fun n hn' => by rw [natSuccVal_app hn']
        have hMz' : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
          app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN))
        have hin : (pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero) ∈ˢ
            univ (Nat.max 1 (ψ uN)) := by
          rw [hSspEq, enUU_eq]
          have hSsp' := hSsp M hM'
          have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
            (B := fun _ => SetTheory.app M natzero)
            hSsp' (fun _ _ => hMz')
          rw [if_neg h0,
            show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
              Nat.le_antisymm
                (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
                (Nat.le_max_left _ _)] at this
          exact this
        have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero)
          hMz' (fun _ _ => hin)
        rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
        exact this
    · -- R Mv applied to the base case
      have hSspEqv : (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n)) =
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) :=
        pi_congr fun n hn' => by rw [natSuccVal_app hn']
      have hMz : SetTheory.app Mv natzero ∈ˢ univ (ψ uN) :=
        hMfib natzero natzero_mem
      have hinv : (pi (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => SetTheory.app Mv natzero) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
        rw [hSspEqv, enUU_eq]
        have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
          (B := fun _ => SetTheory.app Mv natzero)
          (hSsp Mv hMc) (fun _ _ => hMz)
        rw [if_neg h0,
          show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
            Nat.le_antisymm
              (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
              (Nat.le_max_left _ _)] at this
        exact this
      have happR : SetTheory.app (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv =
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app Mv natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                  SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z := by
        rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrM_eq, if_neg h0]]
        refine app_lam hMc
          (B := fun M => pi (nrZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
            pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _ => SetTheory.app M natzero)
          (fun M hM' => lam_mem (V := V) fun z hz' =>
            lam_mem (V := V) fun _s _ => hz')
          (fun M hM' => ?_)
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) :=
          pi_congr fun n hn' => by rw [natSuccVal_app hn']
        have hMz' : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
          app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN))
        have hin : (pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero) ∈ˢ
            univ (Nat.max 1 (ψ uN)) := by
          rw [hSspEq, enUU_eq]
          have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
            (B := fun _ => SetTheory.app M natzero)
            (hSsp M hM') (fun _ _ => hMz')
          rw [if_neg h0,
            show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
              Nat.le_antisymm
                (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
                (Nat.le_max_left _ _)] at this
          exact this
        have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero)
          hMz' (fun _ _ => hin)
        rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
        exact this
      refine ⟨Nat.max 1 (ψ uN), SetTheory.app Mv natzero,
        fun _ => pi (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => SetTheory.app Mv natzero,
        ?_, hzc, fun _ _ => hinv⟩
      rw [happR]
      rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
        rw [nrZ_eq, if_neg h0]]
      refine lam_mem (V := V) fun z hz' => ?_
      exact lam_mem (V := V) fun _s _ => hz'
    · -- R Mv zv applied to the step case
      have hSspEqv : (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n)) =
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) :=
        pi_congr fun n hn' => by rw [natSuccVal_app hn']
      have hMz : SetTheory.app Mv natzero ∈ˢ univ (ψ uN) :=
        hMfib natzero natzero_mem
      have happR : SetTheory.app (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv =
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app Mv natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                  SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z := by
        rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrM_eq, if_neg h0]]
        refine app_lam hMc
          (B := fun M => pi (nrZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
            pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _ => SetTheory.app M natzero)
          (fun M hM' => lam_mem (V := V) fun z hz' =>
            lam_mem (V := V) fun _s _ => hz')
          (fun M hM' => ?_)
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) :=
          pi_congr fun n hn' => by rw [natSuccVal_app hn']
        have hMz' : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
          app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN))
        have hin : (pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero) ∈ˢ
            univ (Nat.max 1 (ψ uN)) := by
          rw [hSspEq, enUU_eq]
          have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
            (B := fun _ => SetTheory.app M natzero)
            (hSsp M hM') (fun _ _ => hMz')
          rw [if_neg h0,
            show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
              Nat.le_antisymm
                (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
                (Nat.le_max_left _ _)] at this
          exact this
        have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero)
          hMz' (fun _ _ => hin)
        rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
        exact this
      have happR2 : SetTheory.app (SetTheory.app (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv) zv =
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
            fun _s => zv := by
        rw [happR]
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        refine app_lam hzc
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app Mv natzero)
          (fun z hz' => lam_mem (V := V) fun _s _ => hz')
          (fun _ _ => ?_)
        rw [hSspEqv, enUU_eq]
        have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
          (B := fun _ => SetTheory.app Mv natzero)
          (hSsp Mv hMc) (fun _ _ => hMz)
        rw [if_neg h0,
          show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
            Nat.le_antisymm
              (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
              (Nat.le_max_left _ _)] at this
        exact this
      refine ⟨ψ uN,
        pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        fun _ => SetTheory.app Mv natzero,
        ?_, ?_, fun _ _ => hMz⟩
      · rw [happR2]
        exact lam_mem (V := V) fun _s _ => hzc
      · rw [hSspEqv, enUU_eq]
        exact hsc


/-- Claims glue for the `Nat.rec` successor rule. -/
theorem natSuccIota_claims {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ')
    {Mv zv sv tv nv : V} {vE1 vE2 vE3 vE' : Nat} {A1 A2 A3 A' : V}
    {B1 B2 B3 B' : V → V}
    (h1 : (natRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hM : Mv ∈ˢ A1)
    (h2 : SetTheory.app (natRecVal V ψ) Mv ∈ˢ pi vE2 A2 B2) (hz : zv ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv ∈ˢ pi vE3 A3 B3)
    (hs : sv ∈ˢ A3)
    (hmaj : (natSuccVal V ψ : V) ∈ˢ pi vE' A' B') (hn : nv ∈ˢ A')
    (htv : tv = SetTheory.app (natSuccVal V ψ) nv) :
    ∃ R, interpClosed V cval env ψ natRecSuccRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv)
        sv) nv ∧
      AppSlot (V := V) R Mv ∧
      AppSlot (V := V) (SetTheory.app R Mv) zv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Mv) zv) sv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app R Mv)
        zv) sv) nv := by
  have hnc : nv ∈ˢ omega := by
    have hmaj' := hmaj
    rw [show (natSuccVal V ψ : V) = SetTheory.lam 1 omega natsucc from by
      simp only [natSuccVal]] at hmaj'
    exact lam_dom_of_ne hmaj' (by decide) nv hn
  subst htv
  rw [natSuccVal_app hnc]
  by_cases h0 : ψ uN = 0
  · -- Prop collapse
    refine ⟨_, interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc hfindR hvalR, ?_⟩
    have hRpt : (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) = (pt : V) := by
      rw [show enM (ψ uN) = 0 from by rw [enM_eq, if_pos h0]]
      exact lam_zero
    have hrec_pt : (natRecVal V ψ : V) = pt := by
      simp only [natRecVal, h0, reduceIte]
      exact lam_zero
    rw [hRpt, hrec_pt]
    simp only [app_pt]
    exact ⟨trivial,
      ⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hM,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), hz,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hs,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, omega, fun _ => unitSet, pt_mem_pi_unit (V := V), hnc,
        fun _ _ => unitSet_mem_univ 0⟩⟩
  · -- data levels
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    -- parametric facts (raw fibre forms)
    have hMfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega → SetTheory.app M' n ∈ˢ univ (ψ uN) :=
      fun M' hM' n hn' => app_mem hM' hn' (fun _ _ => univ_mem_univ (ψ uN))
    have hrawP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n) ∈ˢ
          univ (ψ uN) := by
      intro M' hM' n hn'
      rw [natSuccVal_app hn']
      exact hMfibP M' hM' (natsucc n) (natsucc_mem hn')
    have hsfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M' hM' n hn'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN)
        (B := fun _ => SetTheory.app M' (natsucc n))
        (hMfibP M' hM' n hn')
        (fun _ _ => hMfibP M' hM' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSspEqP : ∀ M' : V,
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (natsucc n)) := fun M' =>
      pi_congr fun n hn' => by rw [natSuccVal_app hn']
    have hSspP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      rw [hSspEqP M', enUU_eq]
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfibP M' hM' n hn')
      rw [if_neg h0] at this
      exact this
    have htTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => SetTheory.app M'
          (SetTheory.app (natSuccVal V ψ) n))
        (omega_mem_univ (V := V))
        (fun n hn' => hrawP M' hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hs2P : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
        (hSspP M' hM') (fun _ _ => htTP M' hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hzTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M' natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M' n) fun _ =>
                SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
        (hMfibP M' hM' natzero natzero_mem)
        (fun _ _ => hs2P M' hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have hbody : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M' natzero →
        ∀ s, s ∈ˢ (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) →
        ∀ n, n ∈ˢ omega →
        SetTheory.app (SetTheory.app s n)
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (natRecVal V ψ) M') z) s) n) ∈ˢ
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n) := by
      intro M' hM' z hz' s hs' n hn'
      rw [hSspEqP M', enUU_eq] at hs'
      rw [natRecVal_fold hM' hz' hs' hn', natSuccVal_app hn']
      have hstep' : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app M' k →
          SetTheory.app (SetTheory.app s k) ih ∈ˢ
            SetTheory.app M' (natsucc k) := by
        intro k hk ih hih
        exact app_mem (app_mem hs' hk (hsfibP M' hM')) hih
          (fun _ _ => hMfibP M' hM' (natsucc k) (natsucc_mem hk))
      exact hstep' n hn' _ (natrec_mem hz' hstep' hn')
    -- canonical memberships from the original chain
    have hrec_lam : (natRecVal V ψ : V) = SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      simp only [natRecVal, if_neg h0]
    have h1' := h1
    rw [hrec_lam] at h1'
    have hMc : Mv ∈ˢ pi (ψ uN + 1) omega (fun _ => univ (ψ uN)) :=
      lam_dom_of_ne h1' hwne Mv hM
    have hrecmem : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M' natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (natsucc n)) →
        ∀ t, t ∈ˢ omega → natrec z s t ∈ˢ SetTheory.app M' t := by
      intro M' hM' z hz' s hs' t ht'
      refine natrec_mem hz' ?_ ht'
      intro k hk ih hih
      exact app_mem (app_mem hs' hk (hsfibP M' hM')) hih
        (fun _ _ => hMfibP M' hM' (natsucc k) (natsucc_mem hk))
    have hT4n : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun t => SetTheory.app M' t)
        (omega_mem_univ (V := V))
        (fun t ht => hMfibP M' hM' t ht)
      rw [if_neg h0] at this
      exact this
    have hSspN : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfibP M' hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hT3n : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (hSspN M' hM') (fun _ _ => hT4n M' hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2n : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M' natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M' n) fun _ =>
                SetTheory.app M' (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M' t)
        (hMfibP M' hM' natzero natzero_mem)
        (fun _ _ => hT3n M' hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have happ1 : SetTheory.app (natRecVal V ψ) Mv =
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app Mv natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      rw [hrec_lam]
      exact app_lam hMc
        (B := fun M => pi (Nat.max 1 (ψ uN))
          (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t)
        (fun M hM' => lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun t ht' => hrecmem M hM' z hz' s hs' t ht')
        (fun M hM' => hT2n M hM')
    have h2' := h2
    rw [happ1] at h2'
    have hzc : zv ∈ˢ SetTheory.app Mv natzero :=
      lam_dom_of_ne h2' hwne zv hz
    have happ2 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv =
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec zv s t := by
      rw [happ1]
      exact app_lam hzc
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app Mv t)
        (fun z hz' => lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun t ht' => hrecmem Mv hMc z hz' s hs' t ht')
        (fun _ _ => hT3n Mv hMc)
    have h3' := h3
    rw [happ2] at h3'
    have hsc : sv ∈ˢ (pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) :=
      lam_dom_of_ne h3' hwne sv hs
    obtain ⟨R', hR'i, hfold⟩ := natSucc_iota hfindN hvalN hfindZ hvalZ
      hfindSc hvalSc hfindR hvalR hMc hzc hsc hnc
    rw [interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc
      hfindR hvalR] at hR'i
    obtain rfl := Option.some.inj hR'i
    have henM : enM (ψ uN) = Nat.max 1 (ψ uN) := by rw [enM_eq, if_neg h0]
    have henZ : enZ (ψ uN) = Nat.max 1 (ψ uN) := by rw [enZ_eq, if_neg h0]
    have hen1U : en1U (ψ uN) = Nat.max 1 (ψ uN) := by
      rw [en1U_eq, if_neg h0]
    -- fold applications of R
    have hsc' : sv ∈ˢ (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n)) := by
      rw [hSspEqP Mv, enUU_eq]
      exact hsc
    have happR1 : SetTheory.app (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv =
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app Mv natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) Mv) z) s) n) := by
      rw [henM, henZ, hen1U]
      exact app_lam hMc
        (B := fun M => pi (Nat.max 1 (ψ uN))
          (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
        (fun M hM' => lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun n hn' =>
              hbody M hM' z hz' s hs' n hn')
        (fun M hM' => hzTP M hM')
    have happR2 : SetTheory.app (SetTheory.app (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv) zv =
        SetTheory.lam (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun s =>
          SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) Mv) zv) s) n) := by
      rw [happR1, henZ]
      refine app_lam hzc
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        (fun z hz' => by
          rw [hen1U]
          exact lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun n hn' =>
              hbody Mv hMc z hz' s hs' n hn')
        (fun _ _ => hs2P Mv hMc)
    have happR3 : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv) zv) sv =
        SetTheory.lam (ψ uN) omega fun n =>
          SetTheory.app (SetTheory.app sv n)
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (natRecVal V ψ) Mv) zv) sv) n) := by
      rw [happR2]
      exact app_lam hsc'
        (B := fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        (fun s hs'' => lam_mem (V := V) fun n hn' =>
          hbody Mv hMc zv hzc s hs'' n hn')
        (fun _ _ => by
          rw [hen1U]
          exact htTP Mv hMc)
    refine ⟨_, interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc hfindR hvalR, hfold, ?_, ?_, ?_, ?_⟩
    · refine ⟨Nat.max 1 (ψ uN),
        pi (ψ uN + 1) omega fun _ => univ (ψ uN),
        fun M => pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
        ?_, hMc, ?_⟩
      · rw [henM]
        refine lam_mem (V := V) fun M hM' => ?_
        rw [henZ]
        refine lam_mem (V := V) fun z hz' => ?_
        rw [hen1U]
        refine lam_mem (V := V) fun s hs' => ?_
        exact lam_mem (V := V) fun n hn' => hbody M hM' z hz' s hs' n hn'
      · intro M hM'
        exact hzTP M hM'
    · refine ⟨Nat.max 1 (ψ uN), SetTheory.app Mv natzero,
        fun _ => pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        ?_, hzc, ?_⟩
      · rw [happR1, henZ]
        refine lam_mem (V := V) fun z hz' => ?_
        rw [hen1U]
        refine lam_mem (V := V) fun s hs' => ?_
        exact lam_mem (V := V) fun n hn' => hbody Mv hMc z hz' s hs' n hn'
      · intro _ _
        exact hs2P Mv hMc
    · refine ⟨Nat.max 1 (ψ uN),
        pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        ?_, hsc', ?_⟩
      · rw [happR2]
        rw [hen1U]
        refine lam_mem (V := V) fun s hs'' => ?_
        exact lam_mem (V := V) fun n hn' => hbody Mv hMc zv hzc s hs'' n hn'
      · intro _ _
        exact htTP Mv hMc
    · refine ⟨ψ uN, omega,
        fun n => SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        ?_, hnc, fun n hn' => hrawP Mv hMc n hn'⟩
      rw [happR3]
      exact lam_mem (V := V) fun n hn' =>
        hbody Mv hMc zv hzc sv hsc' n hn'


/-- Claims glue for the `Eq.rec` rule. -/
theorem eqIota_claims {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ')
    {Av av Mv rv bv tv : V} {vE1 vE2 vE3 vE4 vE5 vE6 : Nat}
    {A1 A2 A3 A4 A5 A6 : V} {B1 B2 B3 B4 B5 B6 : V → V}
    (h1 : (eqRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hA : Av ∈ˢ A1)
    (h2 : SetTheory.app (eqRecVal V ψ) Av ∈ˢ pi vE2 A2 B2) (ha : av ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av ∈ˢ pi vE3 A3 B3)
    (hM : Mv ∈ˢ A3)
    (h4 : SetTheory.app (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av)
      av) Mv ∈ˢ pi vE4 A4 B4)
    (hr : rv ∈ˢ A4)
    (h5 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (eqRecVal V ψ) Av) av) Mv) rv ∈ˢ pi vE5 A5 B5)
    (hb : bv ∈ˢ A5)
    (h6 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv ∈ˢ pi vE6 A6 B6)
    (hh : tv ∈ˢ A6) :
    ∃ R, interpClosed V cval env ψ eqRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv)
        tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Av) av)
        Mv) rv ∧
      AppSlot (V := V) R Av ∧
      AppSlot (V := V) (SetTheory.app R Av) av ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Av) av) Mv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app R Av)
        av) Mv) rv := by
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse
    refine ⟨_, interp_eqRec_rhs hfindE hvalE hfindR hvalR, ?_⟩
    have hRpt : (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN))
        fun A => SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) = (pt : V) := by
      rw [show eqRhsAl' (ψ uN) (ψ u1N) = 0 from by
        rw [eqRhsAl'_eq, if_pos h0]]
      exact lam_zero
    have hrec_pt : (eqRecVal V ψ : V) = pt := by
      simp only [eqRecVal, h0, reduceIte]
      exact lam_zero
    rw [hRpt, hrec_pt]
    simp only [app_pt]
    exact ⟨trivial,
      ⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hA,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), ha,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hM,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A4, fun _ => unitSet, pt_mem_pi_unit (V := V), hr,
        fun _ _ => unitSet_mem_univ 0⟩⟩
  · -- data levels
    have hsne : Nat.max (ψ uN) (ψ u1N + 1) ≠ 0 :=
      max_ne_zero_r' (Nat.succ_ne_zero _)
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 := max_ne_zero_r' h0
    have hrec_lam : (eqRecVal V ψ : V) =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) (univ (ψ uN)) fun A =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
              (eqRecMSpace V (ψ u1N) A a) fun M =>
              SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
                (SetTheory.app (SetTheory.app M a) pt) fun r =>
                SetTheory.lam (ψ u1N) A fun _b =>
                  SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r := by
      simp only [eqRecVal, if_neg h0]
    have h1' := h1
    rw [hrec_lam] at h1'
    have hAc : Av ∈ˢ univ (ψ uN) := lam_dom_of_ne h1' hsne Av hA
    -- parametric universe facts (as in the fold equation)
    have hMS : ∀ A : V, A ∈ˢ univ (ψ uN) → ∀ a : V, a ∈ˢ A →
        eqRecMSpace V (ψ u1N) A a ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hA'
        (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
    have hMapt' : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        SetTheory.app (SetTheory.app M a) pt ∈ˢ univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      simp only [eqRecMSpace] at hM'
      have hMa' : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
          (fun _ => univ (ψ u1N)) :=
        app_mem hM' ha' (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
      exact app_mem hMa' (pt_mem_eqv_self a)
        (fun _ _ => univ_mem_univ (ψ u1N))
    have hT5 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have h5 : ∀ b, b ∈ˢ A →
          (pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ univ (ψ u1N) := by
        intro b hb'
        have := pi_mem_univ (u := 0) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app M a) pt)
          (eqv_mem_univ a b) (fun _ _ => hMapt' A hA' a ha' M hM')
        rw [if_neg h0] at this
        exact this
      have := pi_mem_univ (u := ψ uN) (v := ψ u1N)
        (B := fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) hA' h5
      rw [if_neg h0] at this
      exact this
    have hT4 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun _ => pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt)
        (hMapt' A hA' a ha' M hM') (fun _ _ => hT5 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this
      exact this
    have hT3 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
        (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt)
        (hMS A hA' a ha') (fun M hM' => hT4 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (Nat.max (ψ uN) (ψ u1N + 1)) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N + 1) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _,
            Nat.max_le.mpr ⟨Nat.le_max_left _ _,
              Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩)
          (Nat.le_max_left _ _)] at this
      exact this
    have hT2 : ∀ (A : V), A ∈ˢ univ (ψ uN) →
        (pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ u1N + 1))
        (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
        hA' (fun a ha' => hT3 A hA' a ha')
      rw [if_neg hsne, max_absorb_l'] at this
      exact this
    -- fold the original chain to recover canonical memberships
    have happ1 : SetTheory.app (eqRecVal V ψ) Av =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) Av fun a =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (eqRecMSpace V (ψ u1N) Av a) fun M =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun r =>
              SetTheory.lam (ψ u1N) Av fun _b =>
                SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r := by
      rw [hrec_lam]
      exact app_lam hAc
        (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt)
        (fun A hA' => lam_mem (V := V) fun a ha' =>
          lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' =>
              lam_mem (V := V) fun b hb' =>
                lam_mem (V := V) fun h hh' => hr')
        (fun A hA' => hT2 A hA')
    have h2' := h2
    rw [happ1] at h2'
    have hac : av ∈ˢ Av := lam_dom_of_ne h2' hsne av ha
    have happ2 : SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av av) fun M =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M av) pt) fun r =>
            SetTheory.lam (ψ u1N) Av fun _b =>
              SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r := by
      rw [happ1]
      exact app_lam hac
        (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
        (fun a ha' => lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' =>
            lam_mem (V := V) fun b hb' =>
              lam_mem (V := V) fun h hh' => hr')
        (fun a ha' => hT3 Av hAc a ha')
    have h3' := h3
    rw [happ2] at h3'
    have hMc : Mv ∈ˢ eqRecMSpace V (ψ u1N) Av av :=
      lam_dom_of_ne h3' hwne Mv hM
    have happ3 : SetTheory.app (SetTheory.app (SetTheory.app (eqRecVal V ψ)
        Av) av) Mv =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app Mv av) pt) fun r =>
          SetTheory.lam (ψ u1N) Av fun _b =>
            SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r := by
      rw [happ2]
      exact app_lam hMc
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M av) pt) fun _ =>
          pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
            SetTheory.app (SetTheory.app M av) pt)
        (fun M hM' => lam_mem (V := V) fun r hr' =>
          lam_mem (V := V) fun b hb' =>
            lam_mem (V := V) fun h hh' => hr')
        (fun M hM' => hT4 Av hAc av hac M hM')
    have h4' := h4
    rw [happ3] at h4'
    have hrc : rv ∈ˢ SetTheory.app (SetTheory.app Mv av) pt :=
      lam_dom_of_ne h4' hwne rv hr
    have happ4 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (eqRecVal V ψ) Av) av) Mv) rv =
        SetTheory.lam (ψ u1N) Av fun _b =>
          SetTheory.lam (ψ u1N) (eqv av _b) fun _h => rv := by
      rw [happ3]
      exact app_lam hrc
        (B := fun _ => pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (fun r hr' => lam_mem (V := V) fun b hb' =>
          lam_mem (V := V) fun h hh' => hr')
        (fun _ _ => hT5 Av hAc av hac Mv hMc)
    have h5' := h5
    rw [happ4] at h5'
    have hbc : bv ∈ˢ Av := lam_dom_of_ne h5' h0 bv hb
    have happ5 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv =
        SetTheory.lam (ψ u1N) (eqv av bv) fun _h => rv := by
      rw [happ4]
      refine app_lam hbc
        (B := fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (fun b hb' => lam_mem (V := V) fun h hh' => hrc)
        (fun b hb' => ?_)
      have := pi_mem_univ (u := 0) (v := ψ u1N)
        (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
        (eqv_mem_univ av b)
        (fun _ _ => hMapt' Av hAc av hac Mv hMc)
      rw [if_neg h0] at this
      exact this
    have h6' := h6
    rw [happ5] at h6'
    have hhc : tv ∈ˢ eqv av bv := lam_dom_of_ne h6' h0 tv hh
    obtain ⟨R', hR'i, hfold⟩ := eqRec_iota hfindE hvalE hfindR hvalR
      hAc hac hMc hrc hbc hhc
    rw [interp_eqRec_rhs hfindE hvalE hfindR hvalR] at hR'i
    obtain rfl := Option.some.inj hR'i
    -- the reduct chain facts
    have heqAl : eqRhsAl' (ψ uN) (ψ u1N) = Nat.max (ψ uN) (ψ u1N + 1) := by
      rw [eqRhsAl'_eq, if_neg h0]
    have heqA' : eqRhsA' (ψ uN) (ψ u1N) = Nat.max (ψ uN) (ψ u1N + 1) := by
      rw [eqRhsA'_eq, if_neg h0]
    have herB : erB (ψ u1N) = ψ u1N := erB_eq _
    have hMSeqP : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_congr fun b hb' => by rw [eqVal_app₃ hA' ha' hb']
    have hrdP : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      rw [eqReflVal_app₂ hA' ha']
      refine hMapt' A hA' a ha' M ?_
      rw [← hMSeqP A hA' a ha']
      exact hM'
    have hrfibP : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        (pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
        (B := fun _ => SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (hrdP A hA' a ha' M hM') (fun _ _ => hrdP A hA' a ha' M hM')
      rw [if_neg h0,
        show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
      exact this
    have hT3r : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      rw [herB]
      have hMSi : (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
        rw [hMSeqP A hA' a ha']
        exact hMS A hA' a ha'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1)) (v := ψ u1N)
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        hMSi (fun M hM' => hrfibP A hA' a ha' M hM')
      rw [if_neg h0, max_eqrec_b] at this
      exact this
    have hMvraw : Mv ∈ˢ (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
        fun _ => univ (ψ u1N)) := by
      rw [hMSeqP Av hAc av hac]
      exact hMc
    have hrvraw : rv ∈ˢ SetTheory.app (SetTheory.app Mv av)
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av) := by
      rw [eqReflVal_app₂ hAc hac]
      exact hrc
    have happR1 : SetTheory.app (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N))
        (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) Av =
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) Av fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) Av fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) Av) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
              fun r => r := by
      rw [heqAl, heqA']
      exact app_lam hAc
        (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (fun A hA' => lam_mem (V := V) fun a ha' => by
          rw [herB]
          exact lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' => hr')
        (fun A hA' => by
          have := pi_mem_univ (u := ψ uN)
            (v := Nat.max (ψ uN) (ψ u1N + 1))
            (B := fun a => pi (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
              pi (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun _ => SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            hA' (fun a ha' => hT3r A hA' a ha')
          rw [if_neg hsne, max_absorb_l'] at this
          exact this)
    have happR2 : SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) Av) av =
        SetTheory.lam (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b =>
            pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) Av) av) b)
              fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M av)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
            fun r => r := by
      rw [happR1, heqA']
      exact app_lam hac
        (B := fun a => pi (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
        (fun a ha' => by
          rw [herB]
          exact lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' => hr')
        (fun a ha' => hT3r Av hAc a ha')
    have happR3 : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) Av) av) Mv =
        SetTheory.lam (ψ u1N)
          (SetTheory.app (SetTheory.app Mv av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun r => r := by
      rw [happR2, herB]
      exact app_lam hMvraw
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun _ => SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
        (fun M hM' => lam_mem (V := V) fun r hr' => hr')
        (fun M hM' => hrfibP Av hAc av hac M hM')
    refine ⟨_, interp_eqRec_rhs hfindE hvalE hfindR hvalR, hfold,
      ?_, ?_, ?_, ?_⟩
    · refine ⟨Nat.max (ψ uN) (ψ u1N + 1), univ (ψ uN),
        fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a),
        ?_, hAc, ?_⟩
      · rw [heqAl, heqA']
        refine lam_mem (V := V) fun A hA' => ?_
        refine lam_mem (V := V) fun a ha' => ?_
        rw [herB]
        exact lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr'
      · intro A hA'
        have := pi_mem_univ (u := ψ uN)
          (v := Nat.max (ψ uN) (ψ u1N + 1))
          (B := fun a => pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          hA' (fun a ha' => hT3r A hA' a ha')
        rw [if_neg hsne, max_absorb_l'] at this
        exact this
    · refine ⟨Nat.max (ψ uN) (ψ u1N + 1), Av,
        fun a => pi (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a),
        ?_, hac, ?_⟩
      · rw [happR1, heqA']
        refine lam_mem (V := V) fun a ha' => ?_
        rw [herB]
        exact lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr'
      · intro a ha'
        exact hT3r Av hAc a ha'
    · refine ⟨ψ u1N,
        pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app
            (SetTheory.app (eqVal V ψ) Av) av) b)
          fun _ => univ (ψ u1N),
        fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun _ => SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av),
        ?_, hMvraw, ?_⟩
      · rw [happR2, herB]
        exact lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr'
      · intro M hM'
        exact hrfibP Av hAc av hac M hM'
    · refine ⟨ψ u1N,
        SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av),
        fun _ => SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av),
        ?_, hrvraw, fun _ _ => hrdP Av hAc av hac Mv hMvraw⟩
      rw [happR3]
      exact lam_mem (V := V) fun r hr' => hr'

end Setlec
