import Setlec.Model.TypeChecker
import Setlec.Model.BasisLemmas

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

/-- `Eq.refl`'s value is a member of the reflexivity pi-type. -/
theorem eqReflVal_mem :
    (eqReflVal V ψ : V) ∈ˢ pi 0 (univ (ψ uN))
      (fun A => pi 0 A fun a => eqv a a) := by
  simp only [eqReflVal]
  refine lam_mem (V := V) (B := fun A => pi 0 A fun a => eqv a a)
    fun A hA => ?_
  exact lam_mem (V := V) (B := fun a => eqv a a) fun a _ => pt_mem_eqv_self a

/-- Applying `Eq.refl`'s value to a domain. -/
theorem eqReflVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqReflVal V ψ) A = SetTheory.lam 0 A fun _ => pt := by
  simp only [eqReflVal]
  exact app_lam (B := fun X => pi 0 X fun a => eqv a a) hA
    (fun X _ => lam_mem (V := V) (B := fun a => eqv a a)
      fun a _ => pt_mem_eqv_self a)
    (fun X hX => pi_mem_univ (v := 0) hX (fun a _ => eqv_mem_univ a a))

/-- The full application of `Eq.refl`'s value is the proof point. -/
theorem eqReflVal_app₂ {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a = pt := by
  rw [eqReflVal_app hA]
  exact app_lam (B := fun x => eqv x x) ha
    (fun x _ => pt_mem_eqv_self x)
    (fun x _ => eqv_mem_univ x x)

theorem eqReflVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqReflVal V ψ) A ∈ˢ pi 0 A (fun x => eqv x x) := by
  rw [eqReflVal_app hA]
  exact lam_mem (V := V) (B := fun x => eqv x x) fun x _ => pt_mem_eqv_self x

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

/-! The evaluations of `Eq.rec`'s binder codomain annotations, in the
raw nested-`if` forms `interpExpr` computes (outermost binder last). -/

private def erB (u1 : Nat) : Nat := if u1 = 0 then 0 else u1
private def erRefl (u u1 : Nat) : Nat :=
  if erB u1 = 0 then 0 else Nat.max u (erB u1)
private def erM (u u1 : Nat) : Nat :=
  if erRefl u u1 = 0 then 0 else Nat.max u1 (erRefl u u1)
private def erA (u u1 : Nat) : Nat :=
  if erM u u1 = 0 then 0 else Nat.max u (Nat.max (u1 + 1) (erM u u1))
private def erAl (u u1 : Nat) : Nat :=
  if erA u u1 = 0 then 0 else Nat.max u (erA u u1)

/-- Interpretation of `Eq.rec`'s pinned type, computed. -/
theorem interp_eqRec_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    interpClosed V cval env ψ eqRecA.toConstantVal.type =
      some (pi (erAl (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        pi (erA (ψ uN) (ψ u1N)) A fun a =>
          pi (erM (ψ uN) (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            pi (erRefl (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) fun _ =>
              pi (erB (ψ u1N)) A fun b =>
                pi (ψ u1N)
                  (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
                  fun h => SetTheory.app (SetTheory.app M b) h) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [interpClosed, eqRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', hfindR', hvalR', eqA, eqReflA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, u1N,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-! Collapsing the raw annotation evaluations to `eqRecVal`'s tags. -/

private theorem max_absorb_l' (u v : Nat) :
    Nat.max u (Nat.max u v) = Nat.max u v :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

private theorem max_eqrec_a (u u1 : Nat) :
    Nat.max u (Nat.max (u1 + 1) (Nat.max u u1)) = Nat.max u (u1 + 1) :=
  Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.max_le.mpr ⟨Nat.le_max_right _ _,
        Nat.max_le.mpr ⟨Nat.le_max_left _ _,
          Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩)

private theorem erB_eq (u1 : Nat) : erB u1 = u1 := by
  unfold erB
  by_cases h : u1 = 0 <;> simp [h]

private theorem erRefl_eq (u u1 : Nat) :
    erRefl u u1 = if u1 = 0 then 0 else Nat.max u u1 := by
  unfold erRefl
  rw [erB_eq]

private theorem max_ne_zero_r {u u1 : Nat} (h : u1 ≠ 0) :
    Nat.max u u1 ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u u1))

private theorem erM_eq (u u1 : Nat) :
    erM u u1 = if u1 = 0 then 0 else Nat.max u u1 := by
  unfold erM
  rw [erRefl_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r h)]
    exact max_absorb_r' u u1

private theorem erA_eq (u u1 : Nat) :
    erA u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold erA
  rw [erM_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r h)]
    exact max_eqrec_a u u1

private theorem erAl_eq (u u1 : Nat) :
    erAl u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold erAl
  rw [erA_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r (Nat.succ_ne_zero u1))]
    exact max_absorb_l' u (u1 + 1)

/-- `Eq.rec`'s value inhabits its type (the equality collapse: the
motive's fibre at `b, h` is the fibre at `a, pt`). -/
theorem eqRec_key {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    ∃ T, interpClosed V cval env ψ eqRecA.toConstantVal.type = some T ∧
      eqRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_eqRec_type hfindE hvalE hfindR hvalR, ?_⟩
  rw [erAl_eq, erA_eq, erM_eq, erRefl_eq, erB_eq]
  simp only [eqRecVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun a ha => ?_
  have hMS : (pi (ψ u1N + 1) A fun b =>
      pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a := by
    unfold eqRecMSpace
    exact pi_congr fun b hb => by rw [eqVal_app₃ hA ha hb]
  rw [hMS]
  refine lam_mem (V := V) fun M hM => ?_
  rw [eqReflVal_app₂ hA ha]
  refine lam_mem (V := V) fun r hr => ?_
  refine lam_mem (V := V) fun b hb => ?_
  rw [eqVal_app₃ hA ha hb]
  refine lam_mem (V := V) fun h hh => ?_
  obtain rfl : a = b := mem_eqv hh
  obtain rfl : h = pt := mem_univ_zero (eqv_mem_univ a a) hh
  exact hr

/-! Unassociated (raw) forms of the two outermost `Eq.rec` annotation
evaluations (`interp_eqRec_type` states the simp-reassociated forms). -/

private def erA₀ (u u1 : Nat) : Nat :=
  if erM u u1 = 0 then 0 else Nat.max (Nat.max u (u1 + 1)) (erM u u1)

private theorem erA₀_eq_erA (u u1 : Nat) : erA₀ u u1 = erA u u1 := by
  unfold erA₀ erA
  by_cases h : erM u u1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact Nat.max_assoc u (u1 + 1) (erM u u1)

/-- `Eq.rec`'s type carries truthful annotations. -/
theorem annotOk_eqRec_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) eqRecA.toConstantVal.type := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [eqRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- application facts over the fixed domain `A`, parametric in the point
  have hMSmem : ∀ a', a' ∈ˢ A →
      eqRecMSpace V (ψ u1N) A a' ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hAmem
      (fun b hb => by
        exact pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
  have happM : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      ∀ b', b' ∈ˢ A →
      SetTheory.app M' b' ∈ˢ pi (ψ u1N + 1) (eqv a' b')
        fun _ => univ (ψ u1N) := by
    intro a' ha' M' hM' b' hb'
    simp only [eqRecMSpace] at hM'
    exact app_mem hM' hb' (fun b hb => by
      exact pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
        (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
  have happ2M : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      ∀ b', b' ∈ˢ A → ∀ h', h' ∈ˢ eqv a' b' →
      SetTheory.app (SetTheory.app M' b') h' ∈ˢ univ (ψ u1N) := by
    intro a' ha' M' hM' b' hb' h' hh'
    exact app_mem (happM a' ha' M' hM' b' hb') hh'
      (fun _ _ => univ_mem_univ (ψ u1N))
  -- the interp-form suffix types of the telescope and their universes
  have hMSeq : ∀ a', a' ∈ˢ A →
      (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a' := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_congr fun b hb => by rw [eqVal_app₃ hAmem ha' hb]
  have hT5 : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      ∀ b', b' ∈ˢ A →
      (pi (ψ u1N)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
        fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erB (ψ u1N)) := by
    intro a' ha' M' hM' b' hb'
    rw [eqVal_app₃ hAmem ha' hb']
    exact pi_mem_univ (u := 0) (v := ψ u1N) (eqv_mem_univ a' b')
      (fun h' hh' => happ2M a' ha' M' hM' b' hb' h' hh')
  have hT4 : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      (pi (erB (ψ u1N)) A fun b' =>
        pi (ψ u1N)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
          fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erRefl (ψ uN) (ψ u1N)) := by
    intro a' ha' M' hM'
    exact pi_mem_univ (u := ψ uN) (v := erB (ψ u1N)) hAmem
      (fun b' hb' => hT5 a' ha' M' hM' b' hb')
  have hT3 : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      (pi (erRefl (ψ uN) (ψ u1N))
        (SetTheory.app (SetTheory.app M' a')
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) fun _ =>
        pi (erB (ψ u1N)) A fun b' =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
            fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erM (ψ uN) (ψ u1N)) := by
    intro a' ha' M' hM'
    have hdom : SetTheory.app (SetTheory.app M' a')
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a') ∈ˢ
        univ (ψ u1N) := by
      rw [eqReflVal_app₂ hAmem ha']
      exact happ2M a' ha' M' hM' a' ha' pt (pt_mem_eqv_self a')
    exact pi_mem_univ (u := ψ u1N) (v := erRefl (ψ uN) (ψ u1N)) hdom
      (fun r hr => hT4 a' ha' M' hM')
  have hT2 : ∀ a', a' ∈ˢ A →
      (pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
          fun _ => univ (ψ u1N)) fun M' =>
        pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M' a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) fun _ =>
          pi (erB (ψ u1N)) A fun b' =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
              fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erA₀ (ψ uN) (ψ u1N)) := by
    intro a' ha'
    rw [hMSeq a' ha']
    exact pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
      (v := erM (ψ uN) (ψ u1N)) (hMSmem a' ha')
      (fun M' hM' => hT3 a' ha' M' hM')
  refine ⟨?_, ?_⟩
  · -- opened `∀ {a : α}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro a Sa hSa hamem
    simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
      Option.some.injEq] at hSa
    subst hSa
    refine ⟨?_, ?_⟩
    · -- opened `∀ {motive}, …`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨?_, ⟨_, rfl⟩, ?_⟩
      · -- AnnotOk of the motive space `(b : α) → Eq α a b → Sort u_1`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ⟨_, rfl⟩, ?_⟩
        intro b Sb hSb hbmem
        simp [interpExpr, Expr.instantiate1, updV] at hSb
        subst hSb
        refine ⟨?_, ?_⟩
        · -- opened `Eq α a b → Sort u_1`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ⟨_, rfl⟩, ?_⟩
          · -- AnnotOk of `Eq α a b` (three app clauses)
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1), univ (ψ uN),
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
            · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
                hAmem (fun _ _ => univ_mem_univ 0)
            · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
          · intro h Sh hSh hhmem
            refine ⟨trivial, ?_⟩
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨univ (ψ u1N), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, Level.eval, u1N]
            · exact univ_mem_univ (ψ u1N)
        · -- fibre-universe of the motive space's `b` binder
          intro v hv
          obtain rfl := Option.some.inj hv
          refine ⟨pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            (fun _ => univ (ψ u1N)), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              eqA, ConstantInfo.toConstantVal, Level.eval,
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
        · -- opened `∀ (refl : motive a (Eq.refl α a)), …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ⟨_, rfl⟩, ?_⟩
          · -- AnnotOk of `motive a (Eq.refl α a)` (app clauses)
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
              ?_, ?_, happM a hamem M hMmem' a hamem, ?_,
              fun _ _ => univ_mem_univ (ψ u1N)⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            · -- M ∈ its space, in the eqv form
              have := hMmem'
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
            · rw [eqReflVal_app₂ hAmem hamem]
              exact pt_mem_eqv_self a
          · intro r Sr hSr hrmem
            simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
              eqReflA, ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSr
            subst hSr
            refine ⟨?_, ?_⟩
            · -- opened `∀ {b : α}, …`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ⟨_, rfl⟩, ?_⟩
              intro b Sb hSb hbmem
              simp [interpExpr, Expr.instantiate1, updV] at hSb
              subst hSb
              refine ⟨?_, ?_⟩
              · -- opened `∀ (t : Eq α a b), motive b t`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨?_, ⟨_, rfl⟩, ?_⟩
                · -- AnnotOk of `Eq α a b` (three app clauses)
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
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
                  simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                    eqA, ConstantInfo.toConstantVal,
                    -ite_eq_left_iff, -ite_eq_right_iff,
                    -Nat.max_eq_zero_iff] at hSh
                  subst hSh
                  have hheqv : h ∈ˢ eqv a b := by
                    have : h ∈ˢ SetTheory.app (SetTheory.app
                        (SetTheory.app (eqVal V ψ) A) a) b := hhmem
                    rwa [eqVal_app₃ hAmem hamem hbmem] at this
                  refine ⟨?_, ?_⟩
                  · -- AnnotOk of the body `motive b t` (two app clauses)
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                        (by simp [Expr.instantiate1, AnnotOk]),
                        M, b, ψ u1N + 1, A,
                        (fun b' => pi (ψ u1N + 1) (eqv a b') fun _ =>
                          univ (ψ u1N)),
                        ?_, ?_, ?_, hbmem, ?_⟩,
                      (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app M b, h, ψ u1N + 1, eqv a b,
                      (fun _ => univ (ψ u1N)),
                      ?_, ?_, ?_, hheqv,
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
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · -- app M b at pi-level u1 (weakened annotation)
                      exact happM a hamem M hMmem' b hbmem
                  · -- fibre-universe of the `t` binder (annotation `u_1`)
                    intro v hv
                    obtain rfl := Option.some.inj hv
                    refine ⟨SetTheory.app (SetTheory.app M b) h, ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · exact happ2M a hamem M hMmem' b hbmem h hheqv
              · -- fibre-universe of the `b` binder (annotation `imax 0 u_1`)
                intro v hv
                obtain rfl := Option.some.inj hv
                refine ⟨pi (ψ u1N)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  (fun h' => SetTheory.app (SetTheory.app M b) h'), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                    eqA, ConstantInfo.toConstantVal, Level.eval,
                    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                  try rfl
                · exact hT5 a hamem M hMmem' b hbmem
            · -- fibre-universe of the `refl` binder
              intro v hv
              obtain rfl := Option.some.inj hv
              refine ⟨pi (erB (ψ u1N)) A (fun b' =>
                pi (ψ u1N)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b')
                  (fun h' => SetTheory.app (SetTheory.app M b') h')), ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                  eqA, ConstantInfo.toConstantVal, Level.eval,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl
              · exact hT4 a hamem M hMmem'
        · -- fibre-universe of the `motive` binder
          intro v hv
          obtain rfl := Option.some.inj hv
          refine ⟨pi (erRefl (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun _ => pi (erB (ψ u1N)) A fun b' =>
              pi (ψ u1N)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b')
                fun h' => SetTheory.app (SetTheory.app M b') h'), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
              Level.eval,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · exact hT3 a hamem M hMmem'
    · -- fibre-universe of the `a` binder
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) (fun M' =>
        pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M' a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          (fun _ => pi (erB (ψ u1N)) A fun b' =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b')
              fun h' => SetTheory.app (SetTheory.app M' b') h')), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
          hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
          Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · exact hT2 a hamem
  · -- fibre-universe of the `α` binder
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi (erA (ψ uN) (ψ u1N)) A (fun a =>
      pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) (fun M' =>
        pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M' a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          (fun _ => pi (erB (ψ u1N)) A fun b' =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b')
              fun h' => SetTheory.app (SetTheory.app M' b') h'))), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
        hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
        Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · have hEv : Level.eval ψ
          ((Level.param (Name.anonymous.str "u")).imax
            ((((Level.param (Name.anonymous.str "u")).imax
                (Level.zero.imax (Level.param (Name.anonymous.str "u_1")).succ))).imax
              ((Level.param (Name.anonymous.str "u_1")).imax
                ((Level.param (Name.anonymous.str "u")).imax
                  (Level.zero.imax (Level.param (Name.anonymous.str "u_1"))))))) =
          if erA (ψ uN) (ψ u1N) = 0 then 0
          else Nat.max (ψ uN) (erA (ψ uN) (ψ u1N)) := by
        show (if erA₀ (ψ uN) (ψ u1N) = 0 then 0
          else Nat.max (ψ uN) (erA₀ (ψ uN) (ψ u1N))) = _
        rw [erA₀_eq_erA]
      rw [hEv]
      refine pi_mem_univ (u := ψ uN) (v := erA (ψ uN) (ψ u1N)) hAmem
        (fun a ha => ?_)
      rw [← erA₀_eq_erA]
      exact hT2 a ha


/-! ## The `PSigma'` basis block -/

/-- Interpretation of `PSigma'`'s pinned type, computed. -/
theorem interp_psigma_type {cval : ConstVal V} :
    interpClosed V cval env ψ psigmaA.toConstantVal.type =
      some (pi
        (Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1))
        (univ (ψ uN)) fun A =>
        pi (Nat.max (ψ uN) (ψ vN) + 1) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
          fun _ => univ (Nat.max (ψ uN) (ψ vN))) := by
  simp only [interpClosed, psigmaA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, reduceIte]
  simp [interpExpr, Expr.instantiate1, updV, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `PSigma'`'s value is a member of its pi-type. -/
theorem psigmaVal_mem :
    (psigmaVal V ψ : V) ∈ˢ pi
      (Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1))
      (univ (ψ uN))
      (fun A => pi (Nat.max (ψ uN) (ψ vN) + 1)
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun _ =>
          univ (Nat.max (ψ uN) (ψ vN))) := by
  simp only [psigmaVal]
  refine lam_mem (V := V) (B := fun A => pi (Nat.max (ψ uN) (ψ vN) + 1)
    (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun _ =>
      univ (Nat.max (ψ uN) (ψ vN))) fun A hA => ?_
  refine lam_mem (V := V) (B := fun _ => univ (Nat.max (ψ uN) (ψ vN)))
    fun B hB => ?_
  exact sigma_mem_univ hA (fun x hx => app_mem hB hx fun _ _ =>
    univ_mem_univ (ψ vN))

/-- `PSigma'`'s value inhabits its type. -/
theorem psigma_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ psigmaA.toConstantVal.type = some T ∧
      psigmaVal V ψ ∈ˢ T :=
  ⟨_, interp_psigma_type, psigmaVal_mem⟩

/-- `PSigma'`'s type carries truthful annotations. -/
theorem annotOk_psigma_type {cval : ConstVal V} :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaA.toConstantVal.type := by
  simp only [psigmaA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- `∀ (β : α → Sort v), Sort (max u v)`
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
      refine ⟨trivial, ?_⟩
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨univ (Nat.max (ψ uN) (ψ vN)), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN, vN]
      · exact univ_mem_univ (Nat.max (ψ uN) (ψ vN))
  · intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi (Nat.max (ψ uN) (ψ vN) + 1)
      (pi (ψ vN + 1) A fun _ => univ (ψ vN)) (fun _ =>
        univ (Nat.max (ψ uN) (ψ vN))), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN, vN,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · have hdom : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ vN + 1)) := by
        exact pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hAmem
          (fun _ _ => univ_mem_univ (ψ vN))
      exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
        (v := Nat.max (ψ uN) (ψ vN) + 1) hdom
        (fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN)))


/-- Applying `PSigma'`'s value to a domain computes to the fibre-family
abstraction. -/
theorem psigmaVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaVal V ψ) A =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN) + 1)
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B x := by
  simp only [psigmaVal]
  exact app_lam hA
    (B := fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
      (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
        univ (Nat.max (ψ uN) (ψ vN)))
    (fun X hX => lam_mem (V := V)
      (B := fun _ => univ (Nat.max (ψ uN) (ψ vN)))
      fun B hB => sigma_mem_univ hX (fun x hx =>
        app_mem hB hx fun _ _ => univ_mem_univ (ψ vN)))
    (fun X hX => by
      have hdom : (pi (ψ vN + 1) X fun _ => univ (ψ vN)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ vN + 1)) :=
        pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hX
          (fun _ _ => univ_mem_univ (ψ vN))
      exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
        (v := Nat.max (ψ uN) (ψ vN) + 1) hdom
        (fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN))))

theorem psigmaVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaVal V ψ) A ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN) + 1) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
        (fun _ => univ (Nat.max (ψ uN) (ψ vN))) := by
  rw [psigmaVal_app hA]
  exact lam_mem (V := V) (B := fun _ => univ (Nat.max (ψ uN) (ψ vN)))
    fun B hB => sigma_mem_univ hA (fun x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))

/-! Raw evaluations of `PSigma'.mk`'s binder annotations. -/

private def emV (u v : Nat) : Nat :=
  if Nat.max u v = 0 then 0 else Nat.max v (Nat.max u v)
private def emB (u v : Nat) : Nat :=
  if emV u v = 0 then 0 else Nat.max u (emV u v)
private def emA (u v : Nat) : Nat :=
  if emB u v = 0 then 0 else Nat.max u (Nat.max (v + 1) (emB u v))

private theorem max_ne_zero_l {u v : Nat} (h : u ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_left u v))

private theorem max_ne_zero_r' {u v : Nat} (h : v ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u v))

private theorem emV_eq (u v : Nat) : emV u v = Nat.max u v := by
  unfold emV
  by_cases h : Nat.max u v = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact max_absorb_r' u v

private theorem emB_eq (u v : Nat) : emB u v = Nat.max u v := by
  unfold emB
  rw [emV_eq]
  by_cases h : Nat.max u v = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)

private theorem emA_eq (u v : Nat) :
    emA u v = if Nat.max u v = 0 then 0 else Nat.max u (v + 1) := by
  unfold emA
  rw [emB_eq]
  by_cases h : Nat.max u v = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact max_eqrec_a u v

/-- Interpretation of `PSigma'.mk`'s pinned type, computed. -/
theorem interp_psigmaMk_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    interpClosed V cval env ψ psigmaMkA.toConstantVal.type =
      some (pi (emA (ψ uN) (ψ vN)) (univ (ψ uN)) fun A =>
        pi (emB (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          pi (emV (ψ uN) (ψ vN)) A fun a =>
            pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun _ =>
              SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [interpClosed, psigmaMkA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', psigmaA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `PSigma'.mk`'s value inhabits its type. -/
theorem psigmaMk_key {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    ∃ T, interpClosed V cval env ψ psigmaMkA.toConstantVal.type = some T ∧
      psigmaMkVal V ψ ∈ˢ T := by
  refine ⟨_, interp_psigmaMk_type hfindS hvalS, ?_⟩
  rw [emA_eq, emB_eq, emV_eq]
  simp only [psigmaMkVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun B hB => ?_
  refine lam_mem (V := V) fun a ha => ?_
  refine lam_mem (V := V) fun b hb => ?_
  rw [psigmaVal_fold hA hB]
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simp only [hw, ↓reduceIte]
    exact pt_mem_sigma ha hb
  · simp only [if_neg hw]
    exact spair_mem hw ha hb


/-- `PSigma'.mk`'s type carries truthful annotations. -/
theorem annotOk_psigmaMk_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaMkA.toConstantVal.type := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [psigmaMkA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- the fibre-family space over `A`
  have hβmem : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hAmem
      (fun _ _ => univ_mem_univ (ψ vN))
  refine ⟨?_, ?_⟩
  · -- opened `∀ {β}, …`
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
      · -- opened `∀ (fst : α), …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ⟨_, rfl⟩, ?_⟩
        intro a Sa hSa hamem
        simp [interpExpr, Expr.instantiate1, updV] at hSa
        subst hSa
        refine ⟨?_, ?_⟩
        · -- opened `∀ (snd : β fst), …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
            (by simp [Expr.instantiate1, AnnotOk]), B, a, ψ vN + 1, A,
            (fun _ => univ (ψ vN)), ?_, ?_, hBmem', hamem,
            fun _ _ => univ_mem_univ (ψ vN)⟩, ⟨_, rfl⟩, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV]
          intro b Sb hSb hbmem
          simp [interpExpr, Expr.instantiate1, updV,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSb
          subst hSb
          refine ⟨?_, ?_⟩
          · -- the body `PSigma' α β` (two app clauses)
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
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
              fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN))⟩
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
          · -- fibre-universe of `snd` (annotation `max u v`)
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                psigmaA, ConstantInfo.toConstantVal]
              try rfl
            · rw [psigmaVal_fold hAmem hBmem']
              exact sigma_mem_univ hAmem (fun x hx =>
                app_mem hBmem' hx fun _ _ => univ_mem_univ (ψ vN))
        · -- fibre-universe of `fst` (annotation `imax v (max u v)`)
          intro v hv
          obtain rfl := Option.some.inj hv
          refine ⟨pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a)
            (fun _ => SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B),
            ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal, Level.eval,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
              app_mem hBmem' hamem fun _ _ => univ_mem_univ (ψ vN)
            exact pi_mem_univ (u := ψ vN) (v := Nat.max (ψ uN) (ψ vN)) hBa
              (fun _ _ => by
                rw [psigmaVal_fold hAmem hBmem']
                exact sigma_mem_univ hAmem (fun x hx =>
                  app_mem hBmem' hx fun _ _ => univ_mem_univ (ψ vN)))
      · -- fibre-universe of `β`
        intro v hv
        obtain rfl := Option.some.inj hv
        refine ⟨pi (emV (ψ uN) (ψ vN)) A (fun a =>
          pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a)
            (fun _ => SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)),
          ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · exact pi_mem_univ (u := ψ uN) (v := emV (ψ uN) (ψ vN)) hAmem
            (fun a ha => by
              have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                app_mem hBmem' ha fun _ _ => univ_mem_univ (ψ vN)
              exact pi_mem_univ (u := ψ vN) (v := Nat.max (ψ uN) (ψ vN)) hBa
                (fun _ _ => by
                  rw [psigmaVal_fold hAmem hBmem']
                  exact sigma_mem_univ hAmem (fun x hx =>
                    app_mem hBmem' hx fun _ _ => univ_mem_univ (ψ vN))))
  · -- fibre-universe of `α`
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi (emB (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      (fun B => pi (emV (ψ uN) (ψ vN)) A (fun a =>
        pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a)
          (fun _ => SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B))),
      ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
        psigmaA, ConstantInfo.toConstantVal, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
        (v := emB (ψ uN) (ψ vN)) hβmem
        (fun B hB => pi_mem_univ (u := ψ uN) (v := emV (ψ uN) (ψ vN)) hAmem
          (fun a ha => by
            have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
              app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
            exact pi_mem_univ (u := ψ vN) (v := Nat.max (ψ uN) (ψ vN)) hBa
              (fun _ _ => by
                rw [psigmaVal_fold hAmem hB]
                exact sigma_mem_univ hAmem (fun x hx =>
                  app_mem hB hx fun _ _ => univ_mem_univ (ψ vN)))))


/-! Membership forms for `PSigma'.mk`'s value and its partial
applications (the `AnnotOk` app clauses of the recursor's minor
premise). -/

private theorem psigmaMk_space3 {A B' a' : V}
    (hA : A ∈ˢ univ (ψ uN)) (hB' : B' ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN))
    (ha' : a' ∈ˢ A) :
    (pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
      sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN)) := by
  have hBa : SetTheory.app B' a' ∈ˢ univ (ψ vN) :=
    app_mem hB' ha' fun _ _ => univ_mem_univ (ψ vN)
  have := pi_mem_univ (u := ψ vN) (v := Nat.max (ψ uN) (ψ vN)) hBa
    (fun _ _ => sigma_mem_univ hA fun x hx =>
      app_mem hB' hx fun _ _ => univ_mem_univ (ψ vN))
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simpa [hw] using this
  · simpa [hw, max_absorb_r'] using this

private theorem psigmaMk_space2 {A B' : V}
    (hA : A ∈ˢ univ (ψ uN)) (hB' : B' ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    (pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
      pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN)) := by
  have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ vN)) hA
    (fun a' ha' => psigmaMk_space3 hA hB' ha')
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simpa [hw] using this
  · simpa [hw, max_absorb_l'] using this

private theorem psigmaMk_space1 {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi (Nat.max (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
        pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x) ∈ˢ
      univ (if Nat.max (ψ uN) (ψ vN) = 0 then 0
        else Nat.max (ψ uN) (ψ vN + 1)) := by
  have hdom : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hA
      (fun _ _ => univ_mem_univ (ψ vN))
  have := pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
    (v := Nat.max (ψ uN) (ψ vN)) hdom
    (fun B' hB' => psigmaMk_space2 hA hB')
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simpa [hw] using this
  · have habs : Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN)) =
        Nat.max (ψ uN) (ψ vN + 1) :=
      Nat.le_antisymm
        (Nat.max_le.mpr ⟨Nat.le_refl _,
          Nat.max_le.mpr ⟨Nat.le_max_left _ _,
            Nat.le_trans (Nat.le_succ (ψ vN)) (Nat.le_max_right _ _)⟩⟩)
        (Nat.le_max_left _ _)
    simpa [hw, habs] using this

theorem psigmaMkVal_mem :
    (psigmaMkVal V ψ : V) ∈ˢ pi
      (if Nat.max (ψ uN) (ψ vN) = 0 then 0 else Nat.max (ψ uN) (ψ vN + 1))
      (univ (ψ uN))
      (fun X => pi (Nat.max (ψ uN) (ψ vN))
        (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
          pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
            pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
              sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x =>
                SetTheory.app B' x) := by
  simp only [psigmaMkVal]
  refine lam_mem (V := V) fun X hX => ?_
  refine lam_mem (V := V) fun B' hB' => ?_
  refine lam_mem (V := V) fun a' ha' => ?_
  refine lam_mem (V := V) fun b hb => ?_
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simp only [hw, ↓reduceIte]
    exact pt_mem_sigma ha' hb
  · simp only [if_neg hw]
    exact spair_mem hw ha' hb

theorem psigmaMkVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaMkVal V ψ) A ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
        (fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
          pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
            sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
              SetTheory.app B' x) :=
  app_mem psigmaMkVal_mem hA (fun _X hX => psigmaMk_space1 hX)

theorem psigmaMkVal_app₂_mem {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN)) A (fun a' =>
        pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a') fun _ =>
          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
            SetTheory.app B x) :=
  app_mem (psigmaMkVal_app_mem hA) hB
    (fun _B' hB' => psigmaMk_space2 hA hB')

theorem psigmaMkVal_app₃_mem {A B a : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B) a ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) (fun _ =>
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B x) :=
  app_mem (psigmaMkVal_app₂_mem hA hB) ha
    (fun _a' ha' => psigmaMk_space3 hA hB ha')

theorem psigmaMkVal_app₄_mem {A B a b : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ SetTheory.app B a) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ) A) B) a) b ∈ˢ
      sigmaSet (Nat.max (ψ uN) (ψ vN)) A (fun x => SetTheory.app B x) :=
  app_mem (psigmaMkVal_app₃_mem hA hB ha) hb
    (fun _ _ => sigma_mem_univ hA fun _x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))

/-- Interpretation of `PSigma'.rec`'s pinned type, computed (the whole
telescope is propositional: every binder annotation evaluates to `0`
definitionally). -/
theorem interp_psigmaRec_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    interpClosed V cval env ψ psigmaRecA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A =>
        pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          pi 0 (pi 1
              (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              fun _ => univ 0) fun M =>
            pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) fun _ =>
              pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                fun t => SetTheory.app M t) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' := hvalM
  simp only [interpClosed, psigmaRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', hfindM', hvalM', psigmaA, psigmaMkA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `PSigma'.rec`'s value inhabits its type (elimination via
`mem_sigma_elim`: the target is the pair of its components — or the
proof point — so the minor premise's instance inhabits the motive's
fibre). -/
theorem psigmaRec_key {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    ∃ T, interpClosed V cval env ψ psigmaRecA.toConstantVal.type = some T ∧
      psigmaRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_psigmaRec_type hfindS hvalS hfindM hvalM, ?_⟩
  simp only [psigmaRecVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun B hB => ?_
  rw [psigmaVal_fold hA hB]
  refine lam_mem (V := V) fun M hM => ?_
  have hMin : (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
      SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) =
      (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (if Nat.max (ψ uN) (ψ vN) = 0 then pt
          else spair a b)) :=
    pi_congr fun a ha => pi_congr fun b hb => by
      rw [psigmaMkVal_fold hA hB ha hb]
  rw [hMin]
  refine lam_mem (V := V) fun m hm => ?_
  refine lam_mem (V := V) fun t ht => ?_
  obtain ⟨a', b', ha', hb', hw0, hwn⟩ := mem_sigma_elim ht
  have hMuniv : ∀ x, x ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) A
      (fun x => SetTheory.app B x) → SetTheory.app M x ∈ˢ univ 0 :=
    fun x hx => app_mem hM hx (fun _ _ => univ_mem_univ 0)
  have hifmem : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
      (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b) ∈ˢ
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A (fun x => SetTheory.app B x) := by
    intro a ha b hb
    by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
    · simp only [hw, ↓reduceIte]
      exact pt_mem_sigma ha hb
    · simp only [if_neg hw]
      exact spair_mem hw ha hb
  have h1 : SetTheory.app m a' ∈ˢ pi 0 (SetTheory.app B a')
      (fun b => SetTheory.app M
        (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a' b)) :=
    app_mem hm ha' (fun a ha => by
      have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
        app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
      exact pi_mem_univ (u := ψ vN) (v := 0) hBa
        (fun b hb => hMuniv _ (hifmem a ha b hb)))
  have h2 : SetTheory.app (SetTheory.app m a') b' ∈ˢ
      SetTheory.app M (if Nat.max (ψ uN) (ψ vN) = 0 then pt
        else spair a' b') :=
    app_mem h1 hb' (fun b hb => hMuniv _ (hifmem a' ha' b hb))
  have hteq : (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a' b') = t := by
    by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
    · rw [if_pos hw, hw0 hw]
    · rw [if_neg hw, hwn hw]
  rw [hteq] at h2
  have hpt : SetTheory.app (SetTheory.app m a') b' = pt :=
    mem_univ_zero (hMuniv t ht) h2
  rw [← hpt]
  exact h2


/-- `PSigma'.rec`'s type carries truthful annotations. -/
theorem annotOk_psigmaRec_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaRecA.toConstantVal.type := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' := hvalM
  simp only [psigmaRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- shared facts over `A`
  have hsigU : ∀ B, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B ∈ˢ
        univ (Nat.max (ψ uN) (ψ vN)) := by
    intro B hB
    rw [psigmaVal_fold hAmem hB]
    exact sigma_mem_univ hAmem (fun x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))
  -- the two-app `PSigma' α β` AnnotOk clause, for a given fibre value
  have hPSclause : ∀ (d' : Nat) (ρ' : Nat → V) (f a' : Expr),
      interpExpr V cval env ψ d' ρ' f = some (psigmaVal V ψ) →
      True := fun _ _ _ _ _ => trivial
  clear hPSclause
  refine ⟨?_, ?_⟩
  · -- opened `∀ {β}, …`
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
      · -- opened `∀ {motive}, …`
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
          have happM : ∀ x, x ∈ˢ
              SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B →
              SetTheory.app M x ∈ˢ univ 0 :=
            fun x hx => app_mem hMmem' hx (fun _ _ => univ_mem_univ 0)
          have hmk4 : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
              SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                (psigmaMkVal V ψ) A) B) a) b ∈ˢ
              SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B := by
            intro a ha b hb
            rw [psigmaVal_fold hAmem hBmem']
            exact psigmaMkVal_app₄_mem hAmem hBmem' ha hb
          refine ⟨?_, ?_⟩
          · -- opened `∀ (mk : …), …`
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
              refine ⟨?_, ?_⟩
              · -- opened `∀ (t : PSigma' α β), motive t`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                    psigmaVal V ψ, A,
                    Nat.max (Nat.max (ψ uN) (ψ vN + 1))
                      (Nat.max (ψ uN) (ψ vN) + 1),
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
                · simp [interpExpr, Expr.instantiate1, updV, hfindS',
                    hvalS', psigmaA, ConstantInfo.toConstantVal]
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
                · simp [interpExpr, Expr.instantiate1, updV, hfindS',
                    hvalS', psigmaA, ConstantInfo.toConstantVal]
                  try rfl
                · simp [interpExpr, Expr.instantiate1, updV]
                intro t St hSt htmem
                simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                  psigmaA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff] at hSt
                subst hSt
                refine ⟨?_, ?_⟩
                · -- the body `motive t`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    (by simp [Expr.instantiate1, AnnotOk]),
                    M, t, 1,
                    SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B,
                    (fun _ => univ 0),
                    ?_, ?_, hMmem', htmem,
                    fun _ _ => univ_mem_univ 0⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                · -- fibre-universe of `t` (annotation `0`)
                  intro v hv
                  obtain rfl := Option.some.inj hv
                  refine ⟨SetTheory.app M t, ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · exact app_mem hMmem' htmem (fun _ _ => univ_mem_univ 0)
              · -- fibre-universe of `mk` (annotation `imax (max u v) 0`)
                intro v hv
                obtain rfl := Option.some.inj hv
                refine ⟨pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                  (fun t => SetTheory.app M t), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                    psigmaA, ConstantInfo.toConstantVal, Level.eval,
                    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                  try rfl
                · exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 0)
                    (hsigU B hBmem')
                    (fun t ht => app_mem hMmem' ht (fun _ _ => univ_mem_univ 0))
          · -- fibre-universe of `motive`
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
              (fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                (fun t => SetTheory.app M t)), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                hfindM', hvalM', psigmaA, psigmaMkA,
                ConstantInfo.toConstantVal, Level.eval,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · have hminor : (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ
                  univ 0 :=
                pi_mem_univ (u := ψ uN) (v := 0) hAmem
                  (fun a ha => by
                    have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                      app_mem hBmem' ha fun _ _ => univ_mem_univ (ψ vN)
                    exact pi_mem_univ (u := ψ vN) (v := 0) hBa
                      (fun b hb => happM _ (hmk4 a ha b hb)))
              exact pi_mem_univ (u := 0) (v := 0) hminor
                (fun _ _ => pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 0)
                  (hsigU B hBmem')
                  (fun t ht => app_mem hMmem' ht
                    (fun _ _ => univ_mem_univ 0)))
      · -- fibre-universe of `β`
        intro v hv
        obtain rfl := Option.some.inj hv
        refine ⟨pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
          (fun _ => univ 0)) (fun M =>
            pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
              (fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                (fun t => SetTheory.app M t))), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            hfindM', hvalM', psigmaA, psigmaMkA,
            ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · have hMspace : (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ)
              A) B) fun _ => univ 0) ∈ˢ
              univ (Nat.max (Nat.max (ψ uN) (ψ vN)) 1) :=
            pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 1)
              (hsigU B hBmem') (fun _ _ => univ_mem_univ 0)
          refine pi_mem_univ (u := Nat.max (Nat.max (ψ uN) (ψ vN)) 1)
            (v := 0) hMspace (fun M hM => ?_)
          have hminor : (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ
              univ 0 :=
            pi_mem_univ (u := ψ uN) (v := 0) hAmem
              (fun a ha => by
                have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                  app_mem hBmem' ha fun _ _ => univ_mem_univ (ψ vN)
                exact pi_mem_univ (u := ψ vN) (v := 0) hBa
                  (fun b hb => app_mem hM
                    (by
                      rw [psigmaVal_fold hAmem hBmem']
                      exact psigmaMkVal_app₄_mem hAmem hBmem' ha hb)
                    (fun _ _ => univ_mem_univ 0)))
          exact pi_mem_univ (u := 0) (v := 0) hminor
            (fun _ _ => pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 0)
              (hsigU B hBmem')
              (fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ 0)))
  · -- fibre-universe of `α`
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN)) (fun B =>
      pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        (fun _ => univ 0)) (fun M =>
          pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
            (fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              (fun t => SetTheory.app M t)))), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
        hfindM', hvalM', psigmaA, psigmaMkA,
        ConstantInfo.toConstantVal, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · have hβ : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ vN + 1)) :=
        pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hAmem
          (fun _ _ => univ_mem_univ (ψ vN))
      refine pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1)) (v := 0) hβ
        (fun B hB => ?_)
      have hMspace : (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ)
          A) B) fun _ => univ 0) ∈ˢ
          univ (Nat.max (Nat.max (ψ uN) (ψ vN)) 1) :=
        pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 1)
          (hsigU B hB) (fun _ _ => univ_mem_univ 0)
      refine pi_mem_univ (u := Nat.max (Nat.max (ψ uN) (ψ vN)) 1)
        (v := 0) hMspace (fun M hM => ?_)
      have hminor : (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ
          univ 0 :=
        pi_mem_univ (u := ψ uN) (v := 0) hAmem
          (fun a ha => by
            have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
              app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
            exact pi_mem_univ (u := ψ vN) (v := 0) hBa
              (fun b hb => app_mem hM
                (by
                  rw [psigmaVal_fold hAmem hB]
                  exact psigmaMkVal_app₄_mem hAmem hB ha hb)
                (fun _ _ => univ_mem_univ 0)))
      exact pi_mem_univ (u := 0) (v := 0) hminor
        (fun _ _ => pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 0)
          (hsigU B hB)
          (fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ 0)))


/-! Partial-application computations for `PSigma'.mk`'s value (the
`PairMkFacts` domain facts read the `lam` tags off these). -/

theorem psigmaMkVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaMkVal V ψ) A =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN))
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
        SetTheory.lam (Nat.max (ψ uN) (ψ vN)) A fun a =>
          SetTheory.lam (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun b =>
            if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b := by
  simp only [psigmaMkVal]
  exact app_lam hA
    (B := fun X => pi (Nat.max (ψ uN) (ψ vN))
      (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
        pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
          pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
            sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x => SetTheory.app B' x)
    (fun _X hX => lam_mem (V := V) fun _B' hB' =>
      lam_mem (V := V) fun _a' ha' => lam_mem (V := V) fun _b hb => by
        by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
        · simp only [hw, ↓reduceIte]
          exact pt_mem_sigma ha' hb
        · simp only [if_neg hw]
          exact spair_mem hw ha' hb)
    (fun _X hX => psigmaMk_space1 hX)

theorem psigmaMkVal_app₂ {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN)) A fun a =>
        SetTheory.lam (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun b =>
          if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b := by
  rw [psigmaMkVal_app hA]
  exact app_lam hB
    (B := fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
      pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x)
    (fun _B' hB' => lam_mem (V := V) fun _a' ha' =>
      lam_mem (V := V) fun _b hb => by
        by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
        · simp only [hw, ↓reduceIte]
          exact pt_mem_sigma ha' hb
        · simp only [if_neg hw]
          exact spair_mem hw ha' hb)
    (fun _B' hB' => psigmaMk_space2 hA hB')

theorem psigmaMkVal_app₃ {A B a : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B) a =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun b =>
        if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b := by
  rw [psigmaMkVal_app₂ hA hB]
  exact app_lam ha
    (B := fun a' => pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a') fun _ =>
      sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B x)
    (fun _a' ha' => lam_mem (V := V) fun _b hb => by
      by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
      · simp only [hw, ↓reduceIte]
        exact pt_mem_sigma ha' hb
      · simp only [if_neg hw]
        exact spair_mem hw ha' hb)
    (fun _a' ha' => psigmaMk_space3 hA hB ha')


/-! ## The `Nat` basis block -/

/-- Interpretation of `Nat`'s pinned type (`Type`). -/
theorem interp_nat_type {cval : ConstVal V} :
    interpClosed V cval env ψ natA.toConstantVal.type = some (univ 1) := by
  simp [interpClosed, natA, ConstantInfo.toConstantVal, interpExpr, Level.eval]

/-- `Nat`'s value inhabits its type. -/
theorem nat_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ natA.toConstantVal.type = some T ∧
      (omega : V) ∈ˢ T :=
  ⟨univ 1, interp_nat_type, omega_mem_univ⟩

/-- `Nat.zero`'s value inhabits its type. -/
theorem natZero_key {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    ∃ T, interpClosed V cval env ψ natZeroA.toConstantVal.type = some T ∧
      (natzero : V) ∈ˢ T := by
  refine ⟨omega, ?_, natzero_mem⟩
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp [interpClosed, natZeroA, ConstantInfo.toConstantVal, interpExpr,
    hfindN', hvalN', natA]

/-- `Nat.succ`'s value is a member of its pi-type. -/
theorem natSuccVal_mem :
    (natSuccVal V ψ : V) ∈ˢ pi 1 omega (fun _ => omega) := by
  simp only [natSuccVal]
  exact lam_mem (V := V) (B := fun _ => omega) fun n hn => natsucc_mem hn

/-- Applying `Nat.succ`'s value computes to the successor. -/
theorem natSuccVal_app {n : V} (hn : n ∈ˢ omega) :
    SetTheory.app (natSuccVal V ψ) n = natsucc n := by
  simp only [natSuccVal]
  exact app_lam (B := fun _ => omega) hn (fun k hk => natsucc_mem hk)
    (fun _ _ => omega_mem_univ)

/-- Interpretation of `Nat.succ`'s pinned type, computed. -/
theorem interp_natSucc_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    interpClosed V cval env ψ natSuccA.toConstantVal.type =
      some (pi 1 omega fun _ => omega) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp only [interpClosed, natSuccA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, hfindN', hvalN', natA,
    List.length_nil, reduceIte]
  try simp [interpExpr, Expr.instantiate1, updV]
  try rfl

/-- `Nat.succ`'s value inhabits its type. -/
theorem natSucc_key {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    ∃ T, interpClosed V cval env ψ natSuccA.toConstantVal.type = some T ∧
      natSuccVal V ψ ∈ˢ T :=
  ⟨_, interp_natSucc_type hfindN hvalN, natSuccVal_mem⟩

/-- `Nat.succ`'s type carries truthful annotations. -/
theorem annotOk_natSucc_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    AnnotOk V cval env ψ 0 (rho0 V) natSuccA.toConstantVal.type := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp only [natSuccA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro n Sn hSn hnmem
  refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
  intro v hv
  obtain rfl := Option.some.inj hv
  refine ⟨omega, ?_, ?_⟩
  · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
      ConstantInfo.toConstantVal]
  · exact omega_mem_univ

/-! Raw evaluations of `Nat.rec`'s binder annotations. -/

private def enUU (u : Nat) : Nat := if u = 0 then 0 else u
private def en1U (u : Nat) : Nat := if u = 0 then 0 else Nat.max 1 u
private def en11UU (u : Nat) : Nat :=
  if enUU u = 0 then 0 else Nat.max 1 (enUU u)
private def enZ (u : Nat) : Nat :=
  if en1U u = 0 then 0 else Nat.max (en11UU u) (en1U u)
private def enM (u : Nat) : Nat :=
  if enZ u = 0 then 0 else Nat.max u (enZ u)

private theorem enUU_eq (u : Nat) : enUU u = u := by
  unfold enUU
  by_cases h : u = 0
  · rw [if_pos h, h]
  · rw [if_neg h]

private theorem en1U_eq (u : Nat) :
    en1U u = if u = 0 then 0 else Nat.max 1 u := rfl

private theorem en11UU_eq (u : Nat) :
    en11UU u = if u = 0 then 0 else Nat.max 1 u := by
  unfold en11UU
  rw [enUU_eq]

private theorem enZ_eq (u : Nat) :
    enZ u = if u = 0 then 0 else Nat.max 1 u := by
  unfold enZ
  rw [en11UU_eq, en1U_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 u ≠ 0)]
    exact Nat.max_self _

private theorem enM_eq (u : Nat) :
    enM u = if u = 0 then 0 else Nat.max 1 u := by
  unfold enM
  rw [enZ_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 u ≠ 0)]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.le_max_right 1 u, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)


/-- Interpretation of `Nat.rec`'s pinned type, computed. -/
theorem interp_natRec_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    interpClosed V cval env ψ natRecA.toConstantVal.type =
      some (pi (enM (ψ uN)) (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t) := by
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
  simp only [interpClosed, natRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA,
    natSuccA, List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Nat.rec`'s value inhabits its type (`natrec_mem`). -/
theorem natRec_key {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    ∃ T, interpClosed V cval env ψ natRecA.toConstantVal.type = some T ∧
      natRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_natRec_type hfindN hvalN hfindZ hvalZ hfindSc hvalSc, ?_⟩
  rw [enM_eq, enZ_eq, en1U_eq, enUU_eq]
  simp only [natRecVal]
  refine lam_mem (V := V) fun M hM => ?_
  refine lam_mem (V := V) fun z hz => ?_
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app M n ∈ˢ univ (ψ uN) :=
    fun n hn => app_mem hM hn (fun _ _ => univ_mem_univ (ψ uN))
  have hSuccSp : (pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
      (pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) :=
    pi_congr fun n hn => by rw [natSuccVal_app hn]
  rw [hSuccSp]
  refine lam_mem (V := V) fun s hs => ?_
  refine lam_mem (V := V) fun t ht => ?_
  have hsfib : ∀ n, n ∈ˢ omega →
      (pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
    intro n hn
    have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn)
      (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
    by_cases hu : ψ uN = 0
    · simpa [hu] using this
    · simpa [hu, Nat.max_self] using this
  refine natrec_mem hz ?_ ht
  intro k hk ih hih
  have h1 : SetTheory.app s k ∈ˢ pi (ψ uN) (SetTheory.app M k)
      (fun _ => SetTheory.app M (natsucc k)) :=
    app_mem hs hk hsfib
  exact app_mem h1 hih (fun _ _ => hMfib (natsucc k) (natsucc_mem hk))

/-- `Nat.rec`'s type carries truthful annotations. -/
theorem annotOk_natRec_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) natRecA.toConstantVal.type := by
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
  simp only [natRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨?_, ⟨_, rfl⟩, ?_⟩
  · -- the motive space `(t : Nat) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
    intro t St hSt htmem
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨univ (ψ uN), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN]
    · exact univ_mem_univ (ψ uN)
  · intro M SM hSM hMmem
    simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
      ConstantInfo.toConstantVal, Level.eval, uN,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
    subst hSM
    have hMmem' : M ∈ˢ pi (ψ uN + 1) omega (fun _ => univ (ψ uN)) := hMmem
    have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app M n ∈ˢ univ (ψ uN) :=
      fun n hn => app_mem hMmem' hn (fun _ _ => univ_mem_univ (ψ uN))
    refine ⟨?_, ?_⟩
    · -- opened `∀ (zero : motive Nat.zero), …`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, natzero, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
        ?_, ?_, hMmem', natzero_mem,
        fun _ _ => univ_mem_univ (ψ uN)⟩, ⟨_, rfl⟩, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal]
      intro z Sz hSz hzmem
      refine ⟨?_, ?_⟩
      · -- opened `∀ (succ : …), …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ⟨_, rfl⟩, ?_⟩
        · -- the successor minor-premise space
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
          intro n Sn hSn hnmem
          simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
            ConstantInfo.toConstantVal] at hSn
          subst hSn
          refine ⟨?_, ?_⟩
          · -- opened `∀ (n_ih : motive n), motive (Nat.succ n)`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              M, n, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
              ?_, ?_, hMmem', hnmem,
              fun _ _ => univ_mem_univ (ψ uN)⟩, ⟨_, rfl⟩, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            intro ih Sih hSih hihmem
            refine ⟨?_, ?_⟩
            · -- the body `motive (Nat.succ n)`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                ⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                  natSuccVal V ψ, n, 1, omega, (fun _ => omega),
                  ?_, ?_, natSuccVal_mem, hnmem,
                  fun _ _ => omega_mem_univ⟩,
                M, SetTheory.app (natSuccVal V ψ) n,
                ψ uN + 1, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hMmem', ?_,
                fun _ _ => univ_mem_univ (ψ uN)⟩⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · rw [natSuccVal_app hnmem]
                exact natsucc_mem hnmem
            · -- fibre-universe of `n_ih` (annotation `u`)
              intro v hv
              obtain rfl := Option.some.inj hv
              refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · rw [natSuccVal_app hnmem]
                exact hMfib (natsucc n) (natsucc_mem hnmem)
          · -- fibre-universe of `n` (annotation `imax u u`)
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨pi (ψ uN) (SetTheory.app M n) (fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                hvalSc', natSuccA, ConstantInfo.toConstantVal, Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · exact pi_mem_univ (u := ψ uN) (v := ψ uN)
                (B := fun _ => SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
                (hMfib n hnmem)
                (fun _ _ => by
                  try dsimp only
                  rw [natSuccVal_app hnmem]
                  exact hMfib (natsucc n) (natsucc_mem hnmem))
        · intro s Ss hSs hsmem
          refine ⟨?_, ?_⟩
          · -- opened `∀ (t : Nat), motive t`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
            intro t St hSt htmem
            simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
              ConstantInfo.toConstantVal] at hSt
            subst hSt
            refine ⟨?_, ?_⟩
            · -- the body `motive t`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                M, t, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hMmem', htmem,
                fun _ _ => univ_mem_univ (ψ uN)⟩
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
            · -- fibre-universe of `t` (annotation `u`)
              intro v hv
              obtain rfl := Option.some.inj hv
              refine ⟨SetTheory.app M t, ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV]
              · exact hMfib t htmem
          · -- fibre-universe of `succ` (annotation `imax 1 u`)
            intro v hv
            obtain rfl := Option.some.inj hv
            refine ⟨pi (ψ uN) omega (fun t => SetTheory.app M t), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
                natA, ConstantInfo.toConstantVal, Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · exact pi_mem_univ (u := 1) (v := ψ uN) omega_mem_univ
                (fun t ht => hMfib t ht)
      · -- fibre-universe of `zero`
        intro v hv
        obtain rfl := Option.some.inj hv
        refine ⟨pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
            hfindSc', hvalSc', natA, natSuccA,
            ConstantInfo.toConstantVal, Level.eval, uN,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · rw [show Level.eval ψ
              ((Level.zero.succ.imax ((Level.param (Name.anonymous.str "u")).imax
                (Level.param (Name.anonymous.str "u")))).imax
                (Level.zero.succ.imax (Level.param (Name.anonymous.str "u")))) =
              enZ (ψ uN) from by
            by_cases hu : ψ (Name.anonymous.str "u") = 0 <;>
              simp [Level.eval, enZ, en1U, en11UU, enUU, uN, hu, Nat.max_self]]
          have hsp : (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
              univ (en11UU (ψ uN)) :=
            pi_mem_univ (u := 1) (v := enUU (ψ uN))
              (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              omega_mem_univ
              (fun n hn => by
                try dsimp only
                rw [enUU_eq]
                have hin := pi_mem_univ (u := ψ uN) (v := ψ uN)
                  (B := fun _ => SetTheory.app M
                    (SetTheory.app (natSuccVal V ψ) n))
                  (hMfib n hn)
                  (fun _ _ => by
                    try dsimp only
                    rw [natSuccVal_app hn]
                    exact hMfib (natsucc n) (natsucc_mem hn))
                by_cases hu : ψ uN = 0
                · simpa [hu] using hin
                · simpa [hu, Nat.max_self] using hin)
          exact pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN)) hsp
            (fun _ _ => pi_mem_univ (u := 1) (v := ψ uN)
              (B := fun t => SetTheory.app M t) omega_mem_univ
              (fun t ht => hMfib t ht))
    · -- fibre-universe of `motive`
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨pi (enZ (ψ uN)) (SetTheory.app M natzero)
        (fun _ => pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t)), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
          hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA, natSuccA,
          ConstantInfo.toConstantVal, Level.eval, uN,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · rw [show Level.eval ψ
            ((Level.param (Name.anonymous.str "u")).imax
              ((Level.zero.succ.imax ((Level.param (Name.anonymous.str "u")).imax
                (Level.param (Name.anonymous.str "u")))).imax
                (Level.zero.succ.imax (Level.param (Name.anonymous.str "u"))))) =
            enM (ψ uN) from by
          by_cases hu : ψ (Name.anonymous.str "u") = 0 <;>
            simp [Level.eval, enM, enZ, en1U, en11UU, enUU, uN, hu,
              Nat.max_self]]
        have hsp : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
            univ (en11UU (ψ uN)) :=
          pi_mem_univ (u := 1) (v := enUU (ψ uN))
            (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            omega_mem_univ
            (fun n hn => by
              try dsimp only
              rw [enUU_eq]
              have hin := pi_mem_univ (u := ψ uN) (v := ψ uN)
                (B := fun _ => SetTheory.app M
                  (SetTheory.app (natSuccVal V ψ) n))
                (hMfib n hn)
                (fun _ _ => by
                  try dsimp only
                  rw [natSuccVal_app hn]
                  exact hMfib (natsucc n) (natsucc_mem hn))
              by_cases hu : ψ uN = 0
              · simpa [hu] using hin
              · simpa [hu, Nat.max_self] using hin)
        have hinner : (pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t)) ∈ˢ
            univ (enZ (ψ uN)) :=
          pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN)) hsp
            (fun _ _ => pi_mem_univ (u := 1) (v := ψ uN)
              (B := fun t => SetTheory.app M t) omega_mem_univ
              (fun t ht => hMfib t ht))
        exact pi_mem_univ (u := ψ uN) (v := enZ (ψ uN))
          (hMfib natzero natzero_mem) (fun _ _ => hinner)

end Setlec
