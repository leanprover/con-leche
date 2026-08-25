import Setlec.Model.Basis.Util

/-!
# `PUnit` basis block: interpretation and `hkey` obligations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

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
  have hcodM : (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) = 0 ↔
      ψ u1N = 0 := by
    by_cases h1 : ψ u1N = 0
    · simp [h1]
    · have hmx : ¬ Nat.max (ψ uN) (ψ u1N) = 0 := by
        simp [Nat.max_eq_zero_iff, h1]
      simp [h1, hmx]
  refine ⟨?_,
    (if (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) = 0 then 0
      else Nat.max (ψ u1N)
        (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N))), ?_, ?_⟩
  case refine_2 =>
    rintro v ⟨rfl⟩
    exact fun z hz => hz
  · -- the motive space `Π t : PUnit. Sort u_1`
    try simp only [AnnotOk]
    refine ⟨trivial, ψ u1N + 1, ?_, ?_⟩
    · rintro v ⟨rfl⟩
      exact fun z hz => hz
    · intro t A hA ht
      refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
      refine ⟨univ (ψ u1N), ?_, ?_⟩
      · simp [Expr.instantiate1, interpExpr, Level.eval, u1N]
      · exact univ_mem_univ (ψ u1N)
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
      refine ⟨?_, (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)), ?_, ?_⟩
      case refine_2 =>
        rintro v ⟨rfl⟩
        exact fun z hz => hz
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
          refine ⟨trivial, ψ u1N, ?_, ?_⟩
          · rintro v ⟨rfl⟩
            exact fun z hz => hz
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
          · refine ⟨SetTheory.app M t, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · exact app_mem hM htm (fun _ _ => univ_mem_univ _)
        · -- interp of the opened inner Π and its universe
          refine ⟨pi (ψ u1N) unitSet (fun t => SetTheory.app M t), ?_, ?_⟩
          · simp only [interpExpr, Expr.instantiate1, updV, hfindP', hvalP', punitA,
              ConstantInfo.toConstantVal, List.length_cons, List.length_nil, reduceIte]
            simp [interpExpr, Expr.instantiate1, updV, u1N, uN]
          · exact piC_mem_univ (u := ψ uN) (v := ψ u1N)
              (B := fun t => SetTheory.app M t) (unitSet_mem_univ (ψ uN))
              (fun t htm => app_mem hM htm (fun _ _ => univ_mem_univ _))
    · -- interp of the opened body and its universe
      refine ⟨pi (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N))
        (SetTheory.app M pt) (fun _ => pi (ψ u1N) unitSet (fun t => SetTheory.app M t)),
        ?_, ?_⟩
      · simp only [interpExpr, Expr.instantiate1, updV, hfindP', hvalP', hfindU', hvalU',
          punitA, punitUnitA, ConstantInfo.toConstantVal, List.length_cons,
          List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, uN, u1N]
      · have hdom : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM pt_mem_unitSet (fun _ _ => univ_mem_univ _)
        have hfib : ∀ x, x ∈ˢ SetTheory.app M pt →
            pi (ψ u1N) unitSet (fun t => SetTheory.app M t) ∈ˢ
              univ (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) := by
          intro x hx
          exact piC_mem_univ (unitSet_mem_univ (ψ uN))
            (fun t htm => app_mem hM htm (fun _ _ => univ_mem_univ _))
        exact piC_mem_univ (u := ψ u1N)
          (v := if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N)) hdom hfib

end Setlec

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}

open SetTheory Expr

end Setlec
