import Setlec.Model.TypeChecker

/-!
# Interpretation computations for the pinned basis declarations

Each pinned (annotated) basis type's interpretation is computed
concretely here, and the hand-written value is shown to inhabit it —
the `hkey` obligations of basis installation
(`Setlec.Model.Consistency`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}

open SetTheory Expr

private theorem max_absorb_r' (u v : Nat) : Nat.max v (Nat.max u v) = Nat.max u v :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_max_right u v, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

/-- Interpretation of `PUnit`'s pinned type (`Sort u`). -/
theorem interp_punit_type {cval : ConstVal V} :
    interpClosed V cval env ψ punitA.toConstantVal.type = some (univ (ψ uN)) := by
  simp [interpClosed, punitA, ConstantInfo.toConstantVal, interpExpr, Level.eval, uN]

/-- `PUnit`'s value inhabits its type. -/
theorem punit_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ punitA.toConstantVal.type = some T ∧
      (unitSet : V) ∈ˢ T :=
  ⟨univ (ψ uN), interp_punit_type, unitSet_mem_univ _⟩

/-- `PUnit.unit`'s value inhabits its type. -/
theorem punitUnit_key {cval : ConstVal V}
    (hfind : env.find? punitName = some punitA)
    (hval : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet) :
    ∃ T, interpClosed V cval env ψ punitUnitA.toConstantVal.type = some T ∧
      (pt : V) ∈ˢ T := by
  refine ⟨unitSet, ?_, pt_mem_unitSet⟩
  simp only [interpClosed, punitUnitA, ConstantInfo.toConstantVal, interpExpr]
  rw [show (Name.anonymous.str "PUnit") = punitName from rfl, hfind]
  simp [punitA, ConstantInfo.toConstantVal, hval]

/-- The interpretation of `PUnit.rec`'s pinned type, computed. -/
theorem interp_punitRec_type {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt) :
    interpClosed V cval env ψ punitRecA.toConstantVal.type =
      some (pi
        (if (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) = 0 then 0
          else Nat.max (ψ u1N) (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)))
        (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
        pi (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app M pt) fun _ =>
          pi (ψ u1N) unitSet fun t => SetTheory.app M t) := by
  have hfindP' : env.find? (Name.anonymous.str "PUnit") = some punitA := hfindP
  have hvalP' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PUnit") ψ' = unitSet := hvalP
  have hfindU' : env.find? ((Name.anonymous.str "PUnit").str "unit") = some punitUnitA :=
    hfindU
  have hvalU' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PUnit").str "unit") ψ' = pt := hvalU
  simp only [interpClosed, punitRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindP', hvalP', hfindU', hvalU', punitA, punitUnitA, List.length_cons,
    List.length_nil, reduceIte, if_true, if_false, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, u1N]
  rfl

/-- `PUnit.rec`'s value inhabits its type. -/
theorem punitRec_key {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt) :
    ∃ T, interpClosed V cval env ψ punitRecA.toConstantVal.type = some T ∧
      punitRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_punitRec_type hfindP hvalP hfindU hvalU, ?_⟩
  have hW : (if (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) = 0 then 0
      else Nat.max (ψ u1N) (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N))) =
      (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) := by
    by_cases h0 : ψ u1N = 0
    · simp [h0]
    · simp only [if_neg h0]
      rw [if_neg (by
        intro hc
        exact h0 (Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hc))))]
      exact max_absorb_r' _ _
  rw [hW]
  simp only [punitRecVal]
  refine lam_mem fun M hM => ?_
  refine lam_mem fun m hm => ?_
  refine lam_mem fun t ht => ?_
  have : t = pt := mem_unitSet ht
  rw [this]
  exact hm

/-- The pinned `PUnit.rec` type's annotations are truthful. -/
theorem annotOk_punitRec_type {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt) :
    AnnotOk V cval env ψ 0 (rho0 V) punitRecA.toConstantVal.type := by
  have hfindP' : env.find? (Name.anonymous.str "PUnit") = some punitA := hfindP
  have hvalP' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PUnit") ψ' = unitSet := hvalP
  have hfindU' : env.find? ((Name.anonymous.str "PUnit").str "unit") = some punitUnitA :=
    hfindU
  have hvalU' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PUnit").str "unit") ψ' = pt := hvalU
  simp only [punitRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨?_, ⟨_, rfl⟩, ?_⟩
  · -- the motive space `Π t : PUnit. Sort u_1`, annotated `u_1 + 1`
    try simp only [AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro t A hA ht
    refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨univ (ψ u1N), ?_, ?_⟩
    · simp [Expr.instantiate1, interpExpr, Level.eval, u1N]
    · simpa [Level.eval, u1N] using univ_mem_univ (ψ u1N)
  · intro M A hA hM
    -- A is the motive space
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
    constructor
    · -- annotations of the opened body are truthful
      simp only [Expr.instantiate1, AnnotOk]
      refine ⟨?_, ⟨_, rfl⟩, ?_⟩
      · -- `motive PUnit.unit` : the app clause
        try simp only [AnnotOk]
        refine ⟨?_, ?_, M, pt, ψ u1N + 1, unitSet,
          (fun _ => univ (ψ u1N)), ?_, ?_, hM, pt_mem_unitSet,
          fun _ _ => univ_mem_univ _⟩
        · simp only [reduceIte]
          simp [AnnotOk]
        · simp [AnnotOk]
        · simp [interpExpr, updV]
        · simp only [interpExpr, hfindU', hvalU', punitUnitA, ConstantInfo.toConstantVal,
            List.length_cons, List.length_nil, reduceIte]
          try rfl
      · intro m Am hAm hmem
        constructor
        · -- opened inner body `Π t : PUnit. motive t`
          try simp only [Expr.instantiate1, AnnotOk]
          refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
          intro t At hAt htm
          have hAt' : At = unitSet := by
            simp only [interpExpr, hfindP', hvalP', punitA, ConstantInfo.toConstantVal,
              List.length_cons, List.length_nil, reduceIte] at hAt
            exact (Option.some.inj hAt).symm
          subst hAt'
          refine ⟨?_, ?_⟩
          · -- `motive t` app clause
            try simp only [Expr.instantiate1, AnnotOk]
            refine ⟨?_, ?_, M, t, ψ u1N + 1, unitSet,
              (fun _ => univ (ψ u1N)), ?_, ?_, hM, htm, fun _ _ => univ_mem_univ _⟩
            · simp only [reduceIte]
              simp [Expr.instantiate1, AnnotOk]
            · simp [Expr.instantiate1, AnnotOk]
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
          · intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨SetTheory.app M t, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · have := app_mem hM htm (fun _ _ => univ_mem_univ _)
              simpa [Level.eval, u1N] using this
        · intro v hv
          obtain rfl := Option.some.inj hv
          -- interp of the opened inner Π and its universe
          refine ⟨pi (ψ u1N) unitSet (fun t => SetTheory.app M t), ?_, ?_⟩
          · simp only [interpExpr, Expr.instantiate1, updV, hfindP', hvalP', punitA,
              ConstantInfo.toConstantVal, List.length_cons, List.length_nil, reduceIte]
            simp [interpExpr, Expr.instantiate1, updV, u1N, uN]
            rfl
          · have hpiu := pi_mem_univ (u := ψ uN) (v := ψ u1N)
              (B := fun t => SetTheory.app M t) (unitSet_mem_univ (ψ uN))
              (fun t htm => app_mem hM htm (fun _ _ => univ_mem_univ _))
            simp only [Level.eval, uN, u1N]
            exact hpiu
    · intro v hv
      obtain rfl := Option.some.inj hv
      -- interp of the opened body and its universe (the imax rule)
      refine ⟨pi (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N))
        (SetTheory.app M pt) (fun _ => pi (ψ u1N) unitSet (fun t => SetTheory.app M t)),
        ?_, ?_⟩
      · simp only [interpExpr, Expr.instantiate1, updV, hfindP', hvalP', hfindU', hvalU',
          punitA, punitUnitA, ConstantInfo.toConstantVal, List.length_cons,
          List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, uN, u1N]
        rfl
      · have hdom : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ _)
        have hfib : ∀ x, x ∈ˢ SetTheory.app M pt →
            pi (ψ u1N) unitSet (fun t => SetTheory.app M t) ∈ˢ
              univ (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) := by
          intro x hx
          exact pi_mem_univ (unitSet_mem_univ (ψ uN))
            (fun t htm => app_mem hM htm (fun _ _ => univ_mem_univ _))
        have hres := pi_mem_univ (u := ψ u1N)
          (v := if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) hdom hfib
        simp only [Level.eval]
        simp only [show (Name.anonymous.str "u_1") = u1N from rfl,
          show (Name.anonymous.str "u") = uN from rfl]
        by_cases h0 : ψ u1N = 0
        · simp only [h0, reduceIte] at hres ⊢
          simpa using hres
        · simp only [if_neg h0] at hres ⊢
          exact hres

end Setlec

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}

open SetTheory Expr

/-- Interpretation of `Eq`'s pinned type, computed. -/
theorem interp_eq_type {cval : ConstVal V} :
    interpClosed V cval env ψ eqA.toConstantVal.type =
      some (pi (Nat.max (ψ uN) (Nat.max (ψ uN) 1)) (univ (ψ uN)) fun A =>
        pi (Nat.max (ψ uN) 1) A fun _ =>
          pi 1 A fun _ => univ 0) := by
  simp only [interpClosed, eqA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD]
  simp [interpExpr, Expr.instantiate1, updV, uN]
  try rfl

/-- The fibre family of `Eq`'s value, in its universe. -/
theorem eq_fibre_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi (Nat.max (ψ uN) 1) A fun _ => pi 1 A fun _ => univ 0) ∈ˢ
      univ (Nat.max (ψ uN) (Nat.max (ψ uN) 1)) := by
  have hmem := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) 1)
    (B := fun _ => pi 1 A (fun _ => univ 0)) hA
    (fun x _ => pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
      hA (fun _ _ => univ_mem_univ 0))
  have h1 : 1 ≤ Nat.max (ψ uN) 1 := Nat.le_max_right _ _
  have hne : Nat.max (ψ uN) 1 ≠ 0 := fun hc => absurd (hc ▸ h1) (by decide)
  rwa [if_neg hne] at hmem

/-- `Eq`'s value is a member of its pi-type (the shape app reasoning
uses). -/
theorem eqVal_mem :
    (eqVal V ψ : V) ∈ˢ pi (Nat.max (ψ uN) (Nat.max (ψ uN) 1)) (univ (ψ uN))
      (fun A => pi (Nat.max (ψ uN) 1) A fun _ => pi 1 A fun _ => univ 0) := by
  simp only [eqVal]
  refine lam_mem (V := V) (B := fun A => pi (Nat.max (ψ uN) 1) A fun _ =>
    pi 1 A fun _ => univ 0) fun A hA => ?_
  refine lam_mem (V := V) (B := fun _ => pi 1 A fun _ => univ 0) fun x hx => ?_
  refine lam_mem (V := V) (B := fun _ => univ 0) fun y hy => ?_
  exact eqv_mem_univ x y

/-- `Eq`'s value inhabits its type. -/
theorem eq_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ eqA.toConstantVal.type = some T ∧
      eqVal V ψ ∈ˢ T :=
  ⟨_, interp_eq_type, eqVal_mem⟩

/-- Applying `Eq`'s value to a domain computes to the binary lam pack. -/
theorem eqVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqVal V ψ) A =
      SetTheory.lam (Nat.max (ψ uN) 1) A fun x =>
        SetTheory.lam 1 A fun y => eqv x y := by
  simp only [eqVal]
  exact app_lam
    (B := fun X => pi (Nat.max (ψ uN) 1) X fun _ => pi 1 X fun _ => univ 0) hA
    (fun X hX => lam_mem (V := V) (B := fun _ => pi 1 X fun _ => univ 0)
      fun x _ => lam_mem (V := V) (B := fun _ => univ 0)
        fun y _ => eqv_mem_univ x y)
    (fun X hX => eq_fibre_mem hX)

theorem eqVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqVal V ψ) A ∈ˢ
      pi (Nat.max (ψ uN) 1) A (fun _ => pi 1 A fun _ => univ 0) := by
  rw [eqVal_app hA]
  exact lam_mem (V := V) (B := fun _ => pi 1 A fun _ => univ 0)
    fun x _ => lam_mem (V := V) (B := fun _ => univ 0)
      fun y _ => eqv_mem_univ x y

/-- Applying `Eq`'s value to a domain and a point. -/
theorem eqVal_app₂ {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (eqVal V ψ) A) a =
      SetTheory.lam 1 A fun y => eqv a y := by
  rw [eqVal_app hA]
  exact app_lam (B := fun _ => pi 1 A fun _ => univ 0) ha
    (fun x _ => lam_mem (V := V) (B := fun _ => univ 0)
      fun y _ => eqv_mem_univ x y)
    (fun x _ => by
      exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0) hA
        (fun _ _ => univ_mem_univ 0))

theorem eqVal_app₂_mem {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (eqVal V ψ) A) a ∈ˢ
      pi 1 A (fun _ => univ 0) := by
  rw [eqVal_app₂ hA ha]
  exact lam_mem (V := V) (B := fun _ => univ 0) fun y _ => eqv_mem_univ a y

/-- The full application of `Eq`'s value is the equality truth value. -/
theorem eqVal_app₃ {A a b : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b =
      eqv a b := by
  rw [eqVal_app₂ hA ha]
  exact app_lam (B := fun _ => univ 0) hb
    (fun y _ => eqv_mem_univ a y)
    (fun y _ => univ_mem_univ 0)

/-- `Eq`'s type carries truthful annotations. -/
theorem annotOk_eq_type {cval : ConstVal V} :
    AnnotOk V cval env ψ 0 (rho0 V) eqA.toConstantVal.type := by
  simp only [eqA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · try simp only [Expr.instantiate1, AnnotOk]
    refine ⟨by simp only [reduceIte]; simp [AnnotOk], ⟨_, rfl⟩, ?_⟩
    intro x Sx hSx hxmem
    have hSx' : Sx = A := by
      simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
        Option.some.injEq] at hSx
      exact hSx.symm
    rw [hSx'] at hxmem
    refine ⟨?_, ?_⟩
    · try simp only [Expr.instantiate1, AnnotOk]
      refine ⟨by simp only [reduceIte]; simp [Expr.instantiate1, AnnotOk],
        ⟨_, rfl⟩, ?_⟩
      intro y Sy hSy hymem
      refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨univ 0, ?_, ?_⟩
      · simp [Expr.instantiate1, interpExpr, Level.eval]
      · simpa [Level.eval] using univ_mem_univ 0
    · intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
      · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
          hAmem (fun _ _ => univ_mem_univ 0)
  · intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi (Nat.max (ψ uN) 1) A (fun _ => pi 1 A (fun _ => univ 0)), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, uN]
      try rfl
    · have hmem := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) 1)
        (B := fun _ => pi 1 A (fun _ => univ 0)) hAmem
        (fun x _ => pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
          hAmem (fun _ _ => univ_mem_univ 0))
      have h1 : 1 ≤ Nat.max (ψ uN) 1 := Nat.le_max_right _ _
      have hne : Nat.max (ψ uN) 1 ≠ 0 := fun hc => absurd (hc ▸ h1) (by decide)
      rw [if_neg hne] at hmem
      have hne' : Level.eval ψ
          ((Level.param (Name.anonymous.str "u")).imax Level.zero.succ) ≠ 0 := hne
      have hev : Level.eval ψ ((Level.param (Name.anonymous.str "u")).imax
          ((Level.param (Name.anonymous.str "u")).imax Level.zero.succ)) =
          Nat.max (ψ uN) (Nat.max (ψ uN) 1) := by
        show (if Level.eval ψ
            ((Level.param (Name.anonymous.str "u")).imax Level.zero.succ) = 0
          then 0
          else Max.max (ψ uN) (Level.eval ψ
            ((Level.param (Name.anonymous.str "u")).imax Level.zero.succ))) = _
        rw [if_neg hne']
        rfl
      rw [hev]
      exact hmem

/-- Interpretation of `Eq.refl`'s pinned type, computed (both pis are
Prop-level: the codomain annotations are `0` and `imax u 0`). -/
theorem interp_eqRefl_type {cval : ConstVal V}
    (hfind : env.find? eqName = some eqA)
    (hval : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    interpClosed V cval env ψ eqReflA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A => pi 0 A fun a =>
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a) := by
  have hfind' : env.find? (Name.anonymous.str "Eq") = some eqA := hfind
  have hval' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hval
  simp only [interpClosed, eqReflA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, hfind', hval', eqA,
    List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN]
  try rfl

/-- `Eq.refl`'s value inhabits its type. -/
theorem eqRefl_key {cval : ConstVal V}
    (hfind : env.find? eqName = some eqA)
    (hval : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    ∃ T, interpClosed V cval env ψ eqReflA.toConstantVal.type = some T ∧
      eqReflVal V ψ ∈ˢ T := by
  refine ⟨_, interp_eqRefl_type hfind hval, ?_⟩
  simp only [eqReflVal]
  refine lam_mem (V := V) (B := fun A => pi 0 A fun a =>
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a)
    fun A hA => ?_
  refine lam_mem (V := V) (B := fun a =>
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a)
    fun a ha => ?_
  rw [eqVal_app₃ hA ha ha]
  exact pt_mem_eqv_self a

/-- `Eq.refl`'s type carries truthful annotations. -/
theorem annotOk_eqRefl_type {cval : ConstVal V}
    (hfind : env.find? eqName = some eqA)
    (hval : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) eqReflA.toConstantVal.type := by
  have hfind' : env.find? (Name.anonymous.str "Eq") = some eqA := hfind
  have hval' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hval
  simp only [eqReflA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- the inner `∀ (a : α), Eq α a a` (codomain annotation `0`)
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro x Sx hSx hxmem
    have hSx' : Sx = A := by
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Option.some.injEq] at hSx
      exact hSx.symm
    rw [hSx'] at hxmem
    refine ⟨?_, ?_⟩
    · -- annotations of the opened body `Eq α a a`: three app clauses
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
          eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1), univ (ψ uN),
          (fun X => pi (Nat.max (ψ uN) 1) X fun _ => pi 1 X fun _ => univ 0),
          ?_, ?_, eqVal_mem, hAmem, fun X hX => eq_fibre_mem hX⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (eqVal V ψ) A, x, Nat.max (ψ uN) 1, A,
          (fun _ => pi 1 A fun _ => univ 0),
          ?_, ?_, eqVal_app_mem hAmem, hxmem, fun y _ => ?_⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (SetTheory.app (eqVal V ψ) A) x, x, 1, A,
          (fun _ => univ 0),
          ?_, ?_, eqVal_app₂_mem hAmem hxmem, hxmem,
          fun y _ => univ_mem_univ 0⟩
      · simp only [interpExpr, hfind', hval', eqA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
          ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0) hAmem
          (fun _ _ => univ_mem_univ 0)
      · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
          ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
    · -- the fibre-universe fact for the inner binder (annotation `0`)
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) x) x,
        ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
          ConstantInfo.toConstantVal]
        try rfl
      · rw [eqVal_app₃ hAmem hxmem hxmem]
        exact eqv_mem_univ x x
  · -- the fibre-universe fact for the outer binder (annotation `imax u 0`)
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi 0 A (fun a =>
      SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a),
      ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
        ConstantInfo.toConstantVal, Level.eval]
      try rfl
    · have := pi_mem_univ (u := ψ uN) (v := 0)
        (B := fun a => SetTheory.app (SetTheory.app
          (SetTheory.app (eqVal V ψ) A) a) a) hAmem
        (fun a ha => by
          rw [eqVal_app₃ hAmem ha ha]
          exact eqv_mem_univ a a)
      exact this
end Setlec
