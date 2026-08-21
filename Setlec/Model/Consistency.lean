import Setlec.Model.Extend
import Setlec.Model.Basis.Quot.Iota
import Setlec.Model.Basis.Quot.Consistency
import Setlec.Model.StdAxioms

/-!
# Consistency of the checker

The headline results:

* `checkDecl_sound`: checking a declaration preserves having a model.
* `checkDecls_sound`: every environment accepted by `checkDecls` has a
  set-theoretic model (`EnvModel`).

Both are parametric in a model `V` of the target set theory: assuming
Tarski–Grothendieck set theory is consistent (i.e. a `SetTheory` instance
exists), no accepted environment can prove `False` — the concrete
"no proof of `Empty` is accepted" corollary lands once `Empty` is in the
supported fragment.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The common inversion + semantic-fact assembly for a checked value
against a checked (annotated) type. -/
private theorem value_facts {env : Env} (m : EnvModel V env)
    {value value' type vtype : Expr}
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotateCore env F 0 value = .ok value')
    (hvt : inferTypeCore env F 0 value' = .ok vtype)
    (hde : isDefEqCore env F 0 vtype type = .ok true)
    (htf : type.hasFvar = false)
    (htb : type.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T) :
    value'.hasFvar = false ∧
    (∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value') ∧
    (∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value' = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T) := by
  have hwv : WScoped 0 value := WScoped.of_not_hasFvar hivf
  have hvf' : value'.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F value hannv hwv).fvarsBelow)
  have hbv' : value'.looseBVarsBounded 0 = true := annotateCore_looseBVars F value hannv hlbv
  have hAv : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value' := fun ψ =>
    annotate_sound m value hannv hwv hlbv (Expr.LeavesBounded.of_not_hasFvar hivf)
      (rho0 V) (FvarsOk.of_not_hasFvar hivf)
  refine ⟨hvf', hAv, fun ψ => ?_⟩
  obtain ⟨⟨v, tv, hv, htv, hmem⟩, hwvt, hAvt⟩ :=
    inferTypeCore_sound (φ := ψ) m F hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
      (FvarsOk.of_not_hasFvar hvf') (hAv ψ)
  obtain ⟨T, hT⟩ := hkeyT ψ
  have hbvt : vtype.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf F hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
  have hLbvt : Expr.LeavesBounded vtype := fun l hl =>
    Expr.LeavesBounded.of_not_hasFvar hvf' l
      (inferTypeCore_fvarLeaves m.wf F hvt (WScoped.of_not_hasFvar hvf') l hl)
  have htveq : tv = T :=
    isDefEqCore_sound (φ := ψ) m F hde hwvt (WScoped.of_not_hasFvar htf)
      hbvt htb hLbvt (Expr.LeavesBounded.of_not_hasFvar htf)
      (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf F hvt
        (WScoped.of_not_hasFvar hvf')) (FvarsOk.of_not_hasFvar hvf'))
      (FvarsOk.of_not_hasFvar htf)
      hAvt (hAty ψ) htv hT
  exact ⟨v, T, hv, hT, htveq ▸ hmem⟩

private theorem max_ne_zero_r'' {u v : Nat} (h : v ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u v))

/-- `certifyNatEqs` succeeded on every equation. -/
private theorem certifyNatEqs_inv {F : Nat} {env : Env} :
    ∀ {eqs : List (Expr × Expr)},
      certifyNatEqs (fueledOps F) env eqs = .ok true →
      ∀ eq ∈ eqs, isDefEqCore env F 2 eq.1 eq.2 = .ok true := by
  intro eqs
  induction eqs with
  | nil => intro h eq hm; cases hm
  | cons e rest ih =>
    intro h eq hm
    simp only [certifyNatEqs, fueledOps_isDefEq, Bind.bind,
      Except.bind] at h
    revert h
    cases hde : isDefEqCore env F 2 e.1 e.2 with
    | error err => intro h; exact nomatch h
    | ok b =>
      cases b with
      | false =>
        intro h
        simp [pure, Except.pure] at h
      | true =>
        intro h
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact hde
        · exact ih (by simpa using h) eq hm'

/-- Apply definitional-equality soundness to two prepared equation
sides. -/
private theorem eqSides_defeq {env : Env} (m : EnvModel V env) (F : Nat)
    {l r : Expr} {ψ : Name → Nat} {ρ : Nat → V} {vl vr Tl Tr : V}
    (hde : isDefEqCore env F 2 l r = .ok true)
    (hl : EqSideOk env m.val ψ 2 ρ l vl Tl)
    (hr : EqSideOk env m.val ψ 2 ρ r vr Tr) :
    interpExpr V m.val env ψ 2 ρ l = interpExpr V m.val env ψ 2 ρ r := by
  obtain ⟨hli, -, hlA, hlF, hlW, hlB, hlL⟩ := hl
  obtain ⟨hri, -, hrA, hrF, hrW, hrB, hrL⟩ := hr
  rw [hli, hri]
  exact congrArg some
    (isDefEqCore_sound (φ := ψ) m F hde hlW hrW hlB hrB hlL hrL hlF hrF
      hlA hrA hli hri)

/-- Ditto against a bare stored constant (the `Bool` reducts). -/
private theorem eqSides_defeq_const {env : Env} (m : EnvModel V env)
    (F : Nat) {l : Expr} {bn : Name} {ci : ConstantInfo} {ψ : Name → Nat}
    {ρ : Nat → V} {vl Tl : V}
    (hde : isDefEqCore env F 2 l (.const bn []) = .ok true)
    (hl : EqSideOk env m.val ψ 2 ρ l vl Tl)
    (hf : env.find? bn = some ci)
    (hlp : ci.toConstantVal.levelParams = []) :
    interpExpr V m.val env ψ 2 ρ l =
      interpExpr V m.val env ψ 2 ρ (.const bn []) := by
  obtain ⟨hli, -, hlA, hlF, hlW, hlB, hlL⟩ := hl
  rw [hli, interp_const_mono hf hlp]
  exact congrArg some
    (isDefEqCore_sound (φ := ψ) m F hde hlW (by simp [WScoped]) hlB rfl hlL
      (fun l' hl' => by simp [Expr.fvarLeaves] at hl')
      hlF (fun l' hl' => by simp [Expr.fvarLeaves] at hl')
      hlA (by simp [AnnotOk]) hli (interp_const_mono hf hlp))

/-- The semantic recurrence equations of a certified structural-Nat
operation, from the kernel's pre-insertion value-substituted
certification (`certifyNatEqs`), the pinned type shapes and the
`Nat`/`Bool` pins. -/
private theorem natop_eqs_sound {env : Env} (m : EnvModel V env) (F : Nat)
    {c : Name} {H : Expr}
    (hc : c ∈ natOpNames)
    (hs : natLitSupported env = true)
    (hHf : H.hasFvar = false)
    (hHlb : H.looseBVarsBounded 0 = true)
    (hHA : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) H)
    (hHm : ∀ ψ : Name → Nat, ∃ hv,
      interpClosed V m.val env ψ H = some hv ∧
      (c = natPredName → hv ∈ˢ pi 1 (m.val natName ψ)
        (fun _ => m.val natName ψ)) ∧
      (c ≠ natPredName → ∃ C, hv ∈ˢ pi 1 (m.val natName ψ)
        (fun _ => pi 1 (m.val natName ψ) (fun _ => C)) ∧ C ∈ˢ univ 1 ∧
        (c ≠ natBeqName → c ≠ natBleName → C = m.val natName ψ)))
    (hdeps : ∀ n ∈ natOpDeps c, n ≠ c → natOpStoredOk env n = true)
    (hboolc : (c = natBeqName ∨ c = natBleName) →
      (∃ ciT, env.find? boolTrueName = some ciT ∧
        ciT.toConstantVal.levelParams = []) ∧
      (∃ ciF, env.find? boolFalseName = some ciF ∧
        ciF.toConstantVal.levelParams = []))
    (hcert : ∀ eq ∈ natOpEquations 0 c,
      isDefEqCore env F 2 (Expr.substConst0 c H eq.1)
        (Expr.substConst0 c H eq.2) = .ok true) :
    ∀ eq ∈ natOpEquations 0 c, ∀ (ψ : Name → Nat) (x y : V),
      (∀ T, interpExpr V m.val env ψ 2 (rho0 V) (.const natName []) =
        some T → x ∈ˢ T ∧ y ∈ˢ T) →
      interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
        (Expr.substConst0 c H eq.1) =
      interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
        (Expr.substConst0 c H eq.2) := by
  intro eq heqm ψ x y hxy
  have hde := hcert eq heqm
  obtain ⟨eqL, eqR⟩ := eq
  have hx : x ∈ˢ m.val natName ψ := (hxy _ (interpExpr_const_nat hs)).1
  have hy : y ∈ˢ m.val natName ψ := (hxy _ (interpExpr_const_nat hs)).2
  obtain ⟨hv, hHveq, hHmem⟩ := hHm ψ
  have hHi : interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
      H = some hv :=
    (interp_closed_invariant hHf 2 _).trans hHveq
  have hHA2 := AnnotOk.closed_invariant hHf 2
    (updV V (updV V (rho0 V) 0 x) 1 y) (hHA ψ)
  have hHF : FvarsOk V m.val env ψ 2
      (updV V (updV V (rho0 V) 0 x) 1 y) H := FvarsOk.of_not_hasFvar hHf
  have hHW : WScoped 2 H := WScoped.of_not_hasFvar hHf
  have hHL : Expr.LeavesBounded H := Expr.LeavesBounded.of_not_hasFvar hHf
  have hfx : EqSideOk env m.val ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
      (.fvar 0 (.str .anonymous "x") (.const natName [])) x
      (m.val natName ψ) := by
    have h0 := eqSide_fvar m hs (idx := 0) (nm := .str .anonymous "x")
      (dd := 2) (ρ := updV V (updV V (rho0 V) 0 x) 1 y) (by omega)
      (by rw [updV01_0]; exact hx)
    rw [updV01_0] at h0
    exact h0
  have hfy : EqSideOk env m.val ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
      (.fvar 1 (.str .anonymous "y") (.const natName [])) y
      (m.val natName ψ) := by
    have h0 := eqSide_fvar m hs (idx := 1) (nm := .str .anonymous "y")
      (dd := 2) (ρ := updV V (updV V (rho0 V) 0 x) 1 y) (by omega)
      (by rw [updV01_1]; exact hy)
    rw [updV01_1] at h0
    exact h0
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- pred
    have hHpi := hHmem.1 rfl
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app1 m hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) (eqSide_zero m hs))
        (eqSide_zero m hs)
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app1 m hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) (eqSide_succ m hs hfx))
        hfx
  · -- add
    obtain ⟨C, hHpi, hCu, hCid⟩ := hHmem.2 (by decide)
    rw [hCid (by decide) (by decide)] at hHpi
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_zero m hs))
        hfx
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_succ m hs hfy))
        (eqSide_succ m hs
          (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
            (natVal_mem_univ m hs ψ) hfx hfy))
  · -- sub
    obtain ⟨C, hHpi, hCu, hCid⟩ := hHmem.2 (by decide)
    rw [hCid (by decide) (by decide)] at hHpi
    obtain ⟨cvp, vp, hnf1, hfp, hlpp, hpredm, -⟩ :=
      natOpStored_facts m (hdeps natPredName (by decide) (by decide)) hs ψ
    have hpredpi := hpredm rfl
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_zero m hs))
        hfx
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_succ m hs hfy))
        (eqSide_app1c m hfp hlpp hpredpi (natVal_mem_univ m hs ψ)
          (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
            (natVal_mem_univ m hs ψ) hfx hfy))
  · -- mul
    obtain ⟨C, hHpi, hCu, hCid⟩ := hHmem.2 (by decide)
    rw [hCid (by decide) (by decide)] at hHpi
    obtain ⟨cva, va, hnf2, hfa, hlpa, -, haddm⟩ :=
      natOpStored_facts m (hdeps natAddName (by decide) (by decide)) hs ψ
    obtain ⟨Ca, haddpi, hCua, hCida, -⟩ := haddm (by decide)
    rw [hCida (by decide) (by decide)] at haddpi
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_zero m hs))
        (eqSide_zero m hs)
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_succ m hs hfy))
        (eqSide_app2c m hs hfa hlpa haddpi (natVal_mem_univ m hs ψ)
          (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
            (natVal_mem_univ m hs ψ) hfx hfy)
          hfx)
  · -- pow
    obtain ⟨C, hHpi, hCu, hCid⟩ := hHmem.2 (by decide)
    rw [hCid (by decide) (by decide)] at hHpi
    obtain ⟨cvm', vm', hnf3, hfm, hlpm, -, hmulm⟩ :=
      natOpStored_facts m (hdeps natMulName (by decide) (by decide)) hs ψ
    obtain ⟨Cm, hmulpi, hCum, hCidm, -⟩ := hmulm (by decide)
    rw [hCidm (by decide) (by decide)] at hmulpi
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_zero m hs))
        (eqSide_succ m hs (eqSide_zero m hs))
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
          (natVal_mem_univ m hs ψ) hfx (eqSide_succ m hs hfy))
        (eqSide_app2c m hs hfm hlpm hmulpi (natVal_mem_univ m hs ψ)
          (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi
            (natVal_mem_univ m hs ψ) hfx hfy)
          hfx)
  · -- beq
    obtain ⟨C, hHpi, hCu, -⟩ := hHmem.2 (by decide)
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hboolc (Or.inl rfl)
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq_const m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_zero m hs) (eqSide_zero m hs)) hT hlpT
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq_const m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_zero m hs) (eqSide_succ m hs hfy)) hF hlpF
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq_const m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_succ m hs hfx) (eqSide_zero m hs)) hF hlpF
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_succ m hs hfx) (eqSide_succ m hs hfy))
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu hfx hfy)
  · -- ble
    obtain ⟨C, hHpi, hCu, -⟩ := hHmem.2 (by decide)
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hboolc (Or.inr rfl)
    simp +decide [natOpEquations, Prod.mk.injEq] at heqm
    rcases heqm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq_const m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_zero m hs) hfy) hT hlpT
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq_const m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_succ m hs hfx) (eqSide_zero m hs)) hF hlpF
    · simp +decide only [Expr.substConst0] at hde ⊢
      exact eqSides_defeq m F hde
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu
          (eqSide_succ m hs hfx) (eqSide_succ m hs hfy))
        (eqSide_app2 m hs hHi hHA2 hHF hHW hHlb hHL hHpi hCu hfx hfy)

/-- What the `propext` branch of `stdAxiomOk` checked. -/
private theorem stdAxiomOk_propext_inv {env : Env} {cvA : ConstantVal}
    (hn : cvA.name = propextName) (h : stdAxiomOk env cvA = true) :
    env.find? eqName = some eqA ∧
    (∃ cvI caps, env.find? iffName = some (.indInfo cvI caps) ∧
      ConstantVal.matchesPin cvI iffA.toConstantVal = true) ∧
    (∃ cvIi, env.find? iffIntroName = some (.ctorInfo cvIi 2 2) ∧
      ConstantVal.matchesPin cvIi iffIntroA.toConstantVal = true) ∧
    (∃ cvIr rules, env.find? iffRecName = some (.recInfo cvIr 2 1 1 0 rules) ∧
      ConstantVal.matchesPin cvIr iffRecA.toConstantVal = true) ∧
    ConstantVal.matchesPin cvA propextA = true := by
  rw [stdAxiomOk, if_pos hn] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hE, hIff⟩, hIfi⟩, hIfr⟩, hpin⟩ := h
  refine ⟨hE, ?_, ?_, ?_, hpin⟩
  · revert hIff; split
    · next cvI caps hfI => exact fun hp => ⟨cvI, caps, hfI, hp⟩
    · exact fun hc => nomatch hc
  · revert hIfi; split
    · next cvIi hfI => exact fun hp => ⟨cvIi, hfI, hp⟩
    · exact fun hc => nomatch hc
  · revert hIfr; split
    · next cvIr rules hfI => exact fun hp => ⟨cvIr, rules, hfI, hp⟩
    · exact fun hc => nomatch hc

/-- What the `Classical.choice` branch of `stdAxiomOk` checked. -/
private theorem stdAxiomOk_choice_inv {env : Env} {cvA : ConstantVal}
    (hn : cvA.name = choiceName) (hn' : cvA.name ≠ propextName)
    (h : stdAxiomOk env cvA = true) :
    (∃ cvN caps, env.find? nonemptyName = some (.indInfo cvN caps) ∧
      ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true) ∧
    (∃ cvNi, env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1) ∧
      ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal = true) ∧
    (∃ cvNr rules,
      env.find? nonemptyRecName = some (.recInfo cvNr 1 1 1 0 rules) ∧
      ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal = true) ∧
    ConstantVal.matchesPin cvA choiceA = true := by
  rw [stdAxiomOk, if_neg hn', if_pos hn] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hN, hNi⟩, hNr⟩, hpin⟩ := h
  refine ⟨?_, ?_, ?_, hpin⟩
  · revert hN; split
    · next cvN caps hfN => exact fun hp => ⟨cvN, caps, hfN, hp⟩
    · exact fun hc => nomatch hc
  · revert hNi; split
    · next cvNi hfN => exact fun hp => ⟨cvNi, hfN, hp⟩
    · exact fun hc => nomatch hc
  · revert hNr; split
    · next cvNr rules hfN => exact fun hp => ⟨cvNr, rules, hfN, hp⟩
    · exact fun hc => nomatch hc

/-- Checking a declaration preserves having a model. -/
theorem checkDecl_sound {env env' : Env} {d : Declaration}
    (h : checkDecl (fueledOps F) env d = .ok env') (m : EnvModel V env) : Nonempty (EnvModel V env') := by
  cases d with
  | axiomDecl cv =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    by_cases hok : stdAxiomOk env { cv with type := type } = true
    case neg => simp [hok, pure, Except.pure] at h
    simp only [hok, if_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    -- semantic facts about the annotated type
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false :=
      not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F cv.type hann hwt).fvarsBelow)
    have hbt' : type.looseBVarsBounded 0 = true :=
      annotateCore_looseBVars F cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat,
        AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt
        (Expr.LeavesBounded.of_not_hasFvar hitf) (rho0 V)
        (FvarsOk.of_not_hasFvar hitf)
    by_cases hnp : cv.name = propextName
    · -- propext
      obtain ⟨hE, ⟨cvI, capsI, hIf, hIp⟩, ⟨cvIi, hIif, hIip⟩,
          ⟨cvIr, rulesI, hIrf, hIrp⟩, hpinP⟩ :=
        stdAxiomOk_propext_inv (cvA := { cv with type := type }) hnp hok
      have hvalE : ∀ ψ' : Name → Nat, m.val eqName ψ' = eqVal V ψ' := by
        intro ψ'
        obtain ⟨-, hval⟩ := m.ind_ok.right.right.right.left eqName eqA hE
          rfl (by decide)
        rw [hval ψ']
        show pinnedVal V eqName ψ' = eqVal V ψ'
        delta pinnedVal
        rw [if_pos rfl]
      have hkey : ∀ ψ : Name → Nat, ∃ T,
          interpClosed V m.val env ψ type = some T ∧ propextVal V ∈ˢ T := by
        intro ψ
        obtain ⟨T, hT, hmem⟩ :=
          propext_key m hE hvalE hIf hIp hIif hIip hIrf hIrp ψ
        exact ⟨T, (interpClosed_matchesPin hpinP).trans hT, hmem⟩
      obtain ⟨m', -, -⟩ := extend_basis_one m
        (.axiomInfo { cv with type := type })
        (fun _ => propextVal V)
        hfind'
        ⟨htf, htp, Expr.constsResolve_mono htr, hbt',
          fun _ _ _ hx => ConstantInfo.noConfusion hx,
          fun _ _ _ _ _ _ hx => ConstantInfo.noConfusion hx⟩
        htr
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => hkey ψ)
        (fun _ _ _ => rfl)
        (fun ψ => hAty ψ)
        (fun _ _ hx _ => nomatch hx)
        (fun _ _ _ hx _ => nomatch hx)
        (fun _ _ hx _ => nomatch hx)
        (fun hn => absurd (hnp.symm.trans hn) (by decide))
        (fun hb _ => by simp [ConstantInfo.isBasis] at hb)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _ _ _ _ _ _ _ _ _ hx => nomatch hx)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _ hor => by
          rcases hor with ⟨_, _, hx⟩ | ⟨_, _, _, hx⟩ <;> exact nomatch hx)
        (fun T j hh => absurd (hnp.symm.trans hh).symm
          (Name.num_ne_str _ _ _ _))
        (fun _ _ hx _ _ => nomatch hx)
        (fun _ _ hx _ _ => nomatch hx)
      exact ⟨m'⟩
    · -- Classical.choice
      by_cases hnc : cv.name = choiceName
      case neg =>
        rw [stdAxiomOk, if_neg hnp, if_neg hnc] at hok
        exact nomatch hok
      obtain ⟨⟨cvN, capsN, hNf, hNp⟩, ⟨cvNi, hNif, hNip⟩,
          ⟨cvNr, rulesN, hNrf, hNrp⟩, hpinC⟩ :=
        stdAxiomOk_choice_inv (cvA := { cv with type := type }) hnc hnp hok
      have hlp : cv.levelParams = [uN] := by
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq] at hpinC
        exact hpinC.1.2
      have hkey : ∀ ψ : Name → Nat, ∃ T,
          interpClosed V m.val env ψ type = some T ∧
            choiceVal V (ψ uN) ∈ˢ T := by
        intro ψ
        obtain ⟨T, hT, hmem⟩ :=
          choice_key m hNf hNp hNif hNip hNrf hNrp ψ
        exact ⟨T, (interpClosed_matchesPin hpinC).trans hT, hmem⟩
      obtain ⟨m', -, -⟩ := extend_basis_one m
        (.axiomInfo { cv with type := type })
        (fun ψ => choiceVal V (ψ uN))
        hfind'
        ⟨htf, htp, Expr.constsResolve_mono htr, hbt',
          fun _ _ _ hx => ConstantInfo.noConfusion hx,
          fun _ _ _ _ _ _ hx => ConstantInfo.noConfusion hx⟩
        htr
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => hkey ψ)
        (fun ψ₁ ψ₂ hψ => by
          rw [hψ uN (by rw [hlp]; exact List.mem_singleton.mpr rfl)])
        (fun ψ => hAty ψ)
        (fun _ _ hx _ => nomatch hx)
        (fun _ _ _ hx _ => nomatch hx)
        (fun _ _ hx _ => nomatch hx)
        (fun hn => absurd (hnc.symm.trans hn) (by decide))
        (fun hb _ => by simp [ConstantInfo.isBasis] at hb)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _ _ _ _ _ _ _ _ _ hx => nomatch hx)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _ hor => by
          rcases hor with ⟨_, _, hx⟩ | ⟨_, _, _, hx⟩ <;> exact nomatch hx)
        (fun T j hh => absurd (hnc.symm.trans hh).symm
          (Name.num_ne_str _ _ _ _))
        (fun _ _ hx _ _ => nomatch hx)
        (fun _ _ hx _ _ => nomatch hx)
      exact ⟨m'⟩
  | indDecl block => exact checkIndDecl_sound h m
  | basisDecl kind =>
    match kind, h with
    | .natK, h => ?_
    | .psigmaK, h => ?_
    | .eqK, h => ?_
    | .punitK, h => ?_
    | .emptyK, h => ?_
    | .quotK, h => ?_
    case _ =>
      simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind, reduceCtorEq, reduceIte, pure, Except.pure] at h
      -- step 1: Nat
      by_cases h1 : (env.find? natA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Nat.zero
      by_cases h2 : ((⟨natA :: env.consts⟩ : Env).find? natZeroA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Nat.succ
      by_cases h3 : ((⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 4: Nat.rec
      by_cases h4 : ((⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find? natRecA.name).isNone
      case neg => simp [h4, pure, Except.pure] at h
      simp only [h4, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the four model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m natA (fun _ => omega)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [natA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => nat_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 natZeroA
        (fun _ => natzero)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [natZeroA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natZeroA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => natZero_key rfl (fun ψ' => hval1 ψ'))
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natZeroA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natZeroA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natZeroA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      have hvalN2 : ∀ ψ' : Name → Nat, m2.val natName ψ' = omega := fun ψ' => by
        rw [hpres2 natName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 natSuccA
        (fun ψ => natSuccVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [natSuccA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natSuccA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => natSucc_key rfl hvalN2)
        (fun _ _ _ => rfl)
        (fun ψ => annotOk_natSucc_type rfl hvalN2)
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natSuccA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natSuccA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      have hvalN3 : ∀ ψ' : Name → Nat, m3.val natName ψ' = omega := fun ψ' => by
        rw [hpres3 natName ψ' (by decide)]
        exact hvalN2 ψ'
      have hvalZ3 : ∀ ψ' : Name → Nat, m3.val natZeroName ψ' = natzero := fun ψ' => by
        rw [hpres3 natZeroName ψ' (by decide)]
        exact hval2 ψ'
      obtain ⟨m4, hval4, hpres4⟩ := extend_basis_one m3 natRecA
        (fun ψ => natRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h4)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [natRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [natRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => natRec_key rfl hvalN3 rfl hvalZ3 rfl (fun ψ' => hval3 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [natRecVal]
          rw [hψ uN (by simp [natRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_natRec_type rfl hvalN3 rfl hvalZ3 rfl
          (fun ψ' => hval3 ψ'))
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_neg (by decide), Env.find?_cons, if_pos (by decide)],
            by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [natRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalN' : ∀ ψ' : Name → Nat, val' natName ψ' = omega := by
            intro ψ'
            rw [hv2 natName ψ' (by decide)]
            exact hvalN3 ψ'
          have hvalZ' : ∀ ψ' : Name → Nat, val' natZeroName ψ' = natzero := by
            intro ψ'
            rw [hv2 natZeroName ψ' (by decide)]
            exact hvalZ3 ψ'
          have hvalSc' : ∀ ψ' : Name → Nat,
              val' natSuccName ψ' = natSuccVal V ψ' := by
            intro ψ'
            rw [hv2 natSuccName ψ' (by decide)]
            exact hval3 ψ'
          have hvalRc' : ∀ ψ' : Name → Nat,
              val' (natName.str "rec") ψ' = natRecVal V ψ' :=
            fun ψ' => hv1 ψ'
          have hfN' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natName = some natA := rfl
          have hfZ' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natZeroName = some natZeroA := rfl
          have hfSc' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natSuccName = some natSuccA := rfl
          have hfRc' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              (natName.str "rec") = some natRecA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · -- zero rule
            refine ⟨fun ψ => annotOk_natRecZero_rhs (cval := val') (ψ := ψ)
              rfl hvalN' rfl hvalZ' rfl hvalSc', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hplain _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [natZeroA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Mv, _ | ⟨zv, _ | ⟨sv, _ | ⟨x, rest⟩⟩⟩⟩ <;>
              simp at hlen
            rcases margs with _ | ⟨y, ys⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            rw [hv1] at hp1 hp2 hp3
            have htv' : tv = natzero := by
              rw [htv, hv2 _ _ (by decide)]
              exact hvalZ3 ψj
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩⟩ :=
              natZeroIota_claims (cval := val') (ψ := ψ)
                hfN' hvalN' hfZ' hvalZ' hfSc' hvalSc'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3 htv'
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' natRecA.name ψ)
                  ([Mv, zv, sv] ++ [tv]) = SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' natRecA.name ψ) Mv) zv) sv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩, trivial⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · -- successor rule
            refine ⟨fun ψ => annotOk_natRecSucc_rhs (cval := val') (ψ := ψ)
              rfl hvalN' rfl hvalZ' rfl hvalSc' hfRc' hvalRc', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hplain _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [natSuccA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Mv, _ | ⟨zv, _ | ⟨sv, _ | ⟨x, rest⟩⟩⟩⟩ <;>
              simp at hlen
            rcases margs with _ | ⟨y1, _ | ⟨y2, ys⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            rw [hv1] at hp1 hp2 hp3
            obtain ⟨hms1, -⟩ := hmch
            obtain ⟨vE', A', B', hq', hn', hf'⟩ := hms1
            have hsucceq : ∀ ψ'' : Name → Nat,
                val' ((Name.anonymous.str "Nat").str "succ") ψ'' =
                natSuccVal V ψ := by
              intro ψ''
              rw [hv2 _ _ (by decide)]
              exact hval3 ψ''
            rw [hsucceq] at hq'
            have htv' : tv = SetTheory.app (natSuccVal V ψ) y1 := by
              rw [htv, show SpineFold V (val'
                  ((Name.anonymous.str "Nat").str "succ") ψj) [y1] =
                  SetTheory.app (val'
                    ((Name.anonymous.str "Nat").str "succ") ψj) y1 from rfl,
                hsucceq]
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩⟩ :=
              natSuccIota_claims (cval := val') (ψ := ψ)
                hfN' hvalN' hfZ' hvalZ' hfSc' hvalSc' hfRc' hvalRc'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3
                (vE' := vE') (A' := A') (B' := B') hq' hn' htv'
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' natRecA.name ψ)
                  ([Mv, zv, sv] ++ [tv]) = SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' natRecA.name ψ) Mv) zv) sv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [natRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Nat").str "zero") = some natZeroA := by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Nat").str "succ") = some natSuccA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      exact ⟨m4⟩
    case _ =>
      simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind, reduceCtorEq, reduceIte, pure, Except.pure] at h
      -- step 1: PSigma'
      by_cases h1 : (env.find? psigmaA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: PSigma'.mk
      by_cases h2 : ((⟨psigmaA :: env.consts⟩ : Env).find? psigmaMkA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: PSigma'.rec
      by_cases h3 : ((⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- the semantic pair facts the environment invariant records
      have htyfacts : ∀ ψ' : Name → Nat,
          PairTyFacts V (psigmaVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_⟩
        · intro vE A₀ B₀ x hmem hx
          simp only [psigmaVal] at hmem
          exact lam_pi_dom hmem
            (max_ne_zero_r'' (Nat.succ_ne_zero (Nat.max (ψ' uN) (ψ' vN)))) hx
        · intro vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaVal_app hvA] at hmem
          exact lam_pi_dom hmem (Nat.succ_ne_zero _) hx
        · intro vA vB hvA hvB
          exact psigmaVal_fold hvA hvB
      have hmkfacts : ∀ ψ' : Name → Nat,
          PairMkFacts V (psigmaMkVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hw vE A₀ B₀ x hmem hx
          simp only [psigmaMkVal] at hmem
          refine lam_pi_dom hmem ?_ hx
          rw [if_neg hw]
          exact max_ne_zero_r'' (Nat.succ_ne_zero (ψ' vN))
        · intro hw vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaMkVal_app hvA] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB vE A₂ B₂ x hvA hvB hmem hx
          rw [psigmaMkVal_app₂ hvA hvB] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB va vE A₃ B₃ x hvA hvB hva hmem hx
          rw [psigmaMkVal_app₃ hvA hvB hva] at hmem
          exact lam_pi_dom hmem hw hx
        · intro vA vB va vb hvA hvB hva hvb
          exact psigmaMkVal_fold hvA hvB hva hvb
        · intro hw x y z w'
          simp only [psigmaMkVal]
          rw [if_pos hw, lam_zero, app_pt, app_pt, app_pt, app_pt]
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m psigmaA
        (fun ψ => psigmaVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [psigmaA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => psigma_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaVal]
          rw [hψ uN (by simp [psigmaA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigma_type)
        (fun cv _ hx _ => ⟨by cases hx; rfl, htyfacts⟩)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [psigmaA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [psigmaA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 psigmaMkA
        (fun ψ => psigmaMkVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [psigmaMkA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaMkA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => psigmaMk_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaMkVal]
          rw [hψ uN (by simp [psigmaMkA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaMkA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaMk_type rfl (fun ψ' => hval1 ψ'))
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx _ => by
          cases hx
          exact ⟨rfl, rfl, rfl, hmkfacts⟩)
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [psigmaMkA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [psigmaMkA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      have hvalS2 : ∀ ψ' : Name → Nat, m2.val psigmaName ψ' = psigmaVal V ψ' :=
        fun ψ' => by
          rw [hpres2 psigmaName ψ' (by decide)]
          exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 psigmaRecA
        (fun ψ => psigmaRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [psigmaRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [psigmaRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => psigmaRec_key rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaRecVal]
          rw [hψ uN (by simp [psigmaRecA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaRecA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaRec_type rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [psigmaRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalS' : ∀ ψ' : Name → Nat,
              val' psigmaName ψ' = psigmaVal V ψ' := by
            intro ψ'
            rw [hv2 psigmaName ψ' (by decide)]
            exact hvalS2 ψ'
          have hvalM' : ∀ ψ' : Name → Nat,
              val' psigmaMkName ψ' = psigmaMkVal V ψ' := by
            intro ψ'
            rw [hv2 psigmaMkName ψ' (by decide)]
            exact hval2 ψ'
          have hfS' : Env.find?
              (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ : Env)
              psigmaName = some psigmaA := rfl
          have hfM' : Env.find?
              (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ : Env)
              psigmaMkName = some psigmaMkA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_psigmaRec_rhs (cval := val') (ψ := ψ)
              rfl hvalS' rfl hvalM', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hplain _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [psigmaMkA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Av, _ | ⟨Bv, _ | ⟨Mv, _ | ⟨mkv,
              _ | ⟨x, rest⟩⟩⟩⟩⟩ <;> simp at hlen
            rcases margs with _ | ⟨p1, _ | ⟨p2, _ | ⟨av, _ | ⟨bv,
              _ | ⟨y, ys⟩⟩⟩⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, hs5, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            obtain ⟨vE4, A4, B4, hp4, hm4, hf4⟩ := hs4
            obtain ⟨hms1, hms2, hms3, hms4, -⟩ := hmch
            obtain ⟨vE5, A5, B5, hp5, hm5, hf5⟩ := hms3
            obtain ⟨vE6, A6, B6, hp6, hm6, hf6⟩ := hms4
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩,
              ⟨vS5, AS5, BS5, hq13, hq14, hq15⟩,
              ⟨vS6, AS6, BS6, hq16, hq17, hq18⟩⟩ :=
              psigmaIota_claims (cval := val') (ψ := ψ)
                (Av := Av) (Bv := Bv) (Mv := Mv) (mkv := mkv) (tv := tv)
                (av := av) (bv := bv)
                hfS' hvalS' hfM' hvalM' hm1 hm2 hm3 hm4 hm5 hm6
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' psigmaRecA.name ψ)
                  ([Av, Bv, Mv, mkv] ++ [tv]) =
                  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (val' psigmaRecA.name ψ) Av) Bv)
                    Mv) mkv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩,
                ⟨vS5, AS5, BS5, hq13, hq14, hq15⟩,
                ⟨vS6, AS6, BS6, hq16, hq17, hq18⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [psigmaRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env)
                ((Name.anonymous.str "PSigma'").str "mk") =
                some psigmaMkA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind, reduceCtorEq, reduceIte, pure, Except.pure] at h
      -- step 1: Eq
      by_cases h1 : (env.find? eqA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Eq.refl
      by_cases h2 : ((⟨eqA :: env.consts⟩ : Env).find? eqReflA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Eq.rec
      by_cases h3 : ((⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m eqA (fun ψ => eqVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [eqA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => eq_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqVal]
          rw [hψ uN (by simp [eqA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eq_type)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [eqA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [eqA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 eqReflA
        (fun ψ => eqReflVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [eqReflA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqReflA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => eqRefl_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqReflVal]
          rw [hψ uN (by simp [eqReflA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRefl_type rfl (fun ψ' => hval1 ψ'))
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [eqReflA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [eqReflA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      have hvalE2 : ∀ ψ' : Name → Nat, m2.val eqName ψ' = eqVal V ψ' := fun ψ' => by
        rw [hpres2 eqName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 eqRecA
        (fun ψ => eqRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [eqRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [eqRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => eqRec_key rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqRecVal]
          rw [hψ u1N (by simp [eqRecA, ConstantInfo.toConstantVal, u1N]),
            hψ uN (by simp [eqRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRec_type rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [eqRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalE' : ∀ ψ' : Name → Nat, val' eqName ψ' = eqVal V ψ' := by
            intro ψ'
            rw [hv2 eqName ψ' (by decide)]
            exact hvalE2 ψ'
          have hvalR' : ∀ ψ' : Name → Nat,
              val' eqReflName ψ' = eqReflVal V ψ' := by
            intro ψ'
            rw [hv2 eqReflName ψ' (by decide)]
            exact hval2 ψ'
          have hfE' : Env.find?
              (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env)
              eqName = some eqA := rfl
          have hfR' : Env.find?
              (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env)
              eqReflName = some eqReflA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_eqRec_rhs (cval := val') (ψ := ψ)
              rfl hvalE' rfl hvalR', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hplain _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [eqReflA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Av, _ | ⟨av, _ | ⟨Mv, _ | ⟨rv,
              _ | ⟨bv, _ | ⟨x, rest⟩⟩⟩⟩⟩⟩ <;> simp at hlen
            rcases margs with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3,
              _ | ⟨y, ys⟩⟩⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            obtain ⟨vE4, A4, B4, hp4, hm4, hf4⟩ := hs4
            obtain ⟨vE5, A5, B5, hp5, hm5, hf5⟩ := hs5
            obtain ⟨vE6, A6, B6, hp6, hm6, hf6⟩ := hs6
            rw [hv1] at hp1 hp2 hp3 hp4 hp5 hp6
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩⟩ :=
              eqIota_claims (cval := val') (ψ := ψ)
                hfE' hvalE' hfR' hvalR'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3
                (vE4 := vE4) (A4 := A4) (B4 := B4) hp4 hm4
                (vE5 := vE5) (A5 := A5) (B5 := B5) hp5 hm5
                (vE6 := vE6) (A6 := A6) (B6 := B6) hp6 hm6
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' eqRecA.name ψ)
                  ([Av, av, Mv, rv, bv] ++ [tv]) =
                  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' eqRecA.name ψ) Av) av) Mv) rv) bv) tv
                  from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [eqRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨eqReflA :: eqA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Eq").str "refl") = some eqReflA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      exact ⟨m3⟩
    simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind, reduceCtorEq, reduceIte, pure, Except.pure] at h
    -- step 1: PUnit
    by_cases h1 : (env.find? punitA.name).isNone
    case neg => simp [h1, pure, Except.pure] at h
    simp only [h1, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 2: PUnit.unit
    by_cases h2 : ((⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name).isNone
    case neg => simp [h2, pure, Except.pure] at h
    simp only [h2, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 3: PUnit.rec
    by_cases h3 : ((⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitRecA.name).isNone
    case neg => simp [h3, pure, Except.pure] at h
    simp only [h3, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    -- chain the three model extensions
    obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m punitA (fun _ => unitSet)
      (Option.isNone_iff_eq_none.mp h1)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [punitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitA])⟩
      rfl
      (fun _ _ _ hx => nomatch hx)
      (fun ψ => punit_key)
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv _ hx hn => absurd hn (by decide))
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv _ _ _ ψ x hx => mem_unitSet hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
        absurd hx (by simp [punitA]))
      (fun _ _ _ _ _ _ hx =>
        absurd hx (by simp [punitA]))
      (fun hres _ => absurd hres (by decide))
      (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
      (fun _ _ _ _ hres => absurd hres (by decide))
      (fun _ _ _ _ hres => absurd hres (by decide))
    obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 punitUnitA (fun _ => pt)
      (Option.isNone_iff_eq_none.mp h2)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [punitUnitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitUnitA])⟩
      rfl
      (fun _ _ _ hx => nomatch hx)
      (fun ψ => punitUnit_key rfl (fun ψ' => hval1 ψ'))
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitUnitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv _ hx _ => nomatch hx)
      (fun cv nP nF hx hn => absurd hn (by decide))
      (fun cv _ hx _ => nomatch hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
        absurd hx (by simp [punitUnitA]))
      (fun _ _ _ _ _ _ hx =>
        absurd hx (by simp [punitUnitA]))
      (fun hres _ => absurd hres (by decide))
      (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
      (fun _ _ _ _ hres => absurd hres (by decide))
      (fun _ _ _ _ hres => absurd hres (by decide))
    have hvalP2 : ∀ ψ' : Name → Nat, m2.val punitName ψ' = unitSet := fun ψ' => by
      rw [hpres2 punitName ψ' (by decide)]
      exact hval1 ψ'
    obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 punitRecA
      (fun ψ => punitRecVal V ψ)
      (Option.isNone_iff_eq_none.mp h3)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [punitRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [punitRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
      rfl
      (fun _ _ _ hx => nomatch hx)
      (fun ψ => punitRec_key rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun ψ₁ ψ₂ hψ => by
        simp only [punitRecVal]
        rw [hψ u1N (by simp [punitRecA, ConstantInfo.toConstantVal, u1N]),
          hψ uN (by simp [punitRecA, ConstantInfo.toConstantVal, uN])])
      (fun ψ => annotOk_punitRec_type rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun cv _ hx _ => nomatch hx)
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv _ hx _ => nomatch hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩⟩)
      (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
        simp only [punitRecA] at heq
        injection heq with h1 h2 h3 h4 h5 h6
        subst h1 h2 h3 h4 h5 h6
        intro r hr
        have hvalP' : ∀ ψ' : Name → Nat, val' punitName ψ' = unitSet := by
          intro ψ'
          rw [hv2 punitName ψ' (by decide)]
          exact hvalP2 ψ'
        have hvalU' : ∀ ψ' : Name → Nat, val' punitUnitName ψ' = pt := by
          intro ψ'
          rw [hv2 punitUnitName ψ' (by decide)]
          exact hval2 ψ'
        rcases List.mem_cons.mp hr with rfl | hr
        · refine ⟨fun ψ => annotOk_punitRec_rhs (cval := val') (ψ := ψ)
            rfl hvalP' rfl hvalU', ?_⟩
          intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
            htv _hpeq _hplain _hlev _hfit
          have hje := Option.some.inj hfj
          simp only [punitUnitA] at hje
          injection hje with hj1 hj2 hj3
          subst hj1 hj2 hj3
          rcases args with _ | ⟨Mv, _ | ⟨mv, _ | ⟨x, rest⟩⟩⟩ <;>
            simp at hlen
          rcases margs with _ | ⟨y, ys⟩ <;> simp at hmlen
          obtain ⟨hs1, hs2, hs3, -⟩ := hch
          obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
          obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
          rw [hv1] at hp1 hp2
          have htv' : tv = pt := by
            rw [htv, hv2 _ _ (by decide)]
            exact hval2 ψj
          have hfP' : Env.find?
              (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env)
              punitName = some punitA := rfl
          have hfU' : Env.find?
              (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env)
              punitUnitName = some punitUnitA := rfl
          obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
            ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩⟩ :=
            punitIota_claims (cval := val') (ψ := ψ) hfP' hvalP' hfU' hvalU'
              (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
              (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2 htv'
          refine ⟨R, hRi, ?_, ?_⟩
          · rw [show SpineFold V (val' punitRecA.name ψ)
                ([Mv, mv] ++ [tv]) = SetTheory.app (SetTheory.app
                  (SetTheory.app (val' punitRecA.name ψ) Mv) mv) tv
                from rfl]
            rw [hv1]
            exact hfold
          · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩, trivial⟩
        · cases hr)
      (fun cvR nP nM nm ni rules heq => by
        simp only [punitRecA] at heq
        injection heq with h1 h2 h3 h4 h5 h6
        subst h1 h2 h3 h4 h5 h6
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · have hf : Env.find?
              (⟨punitUnitA :: punitA :: env.consts⟩ : Env)
              ((Name.anonymous.str "PUnit").str "unit") =
              some punitUnitA := by
            rw [Env.find?_cons, if_pos (by decide)]
          exact ⟨_, _, _, hf⟩
        · cases hr)
      (fun hres _ => absurd hres (by decide))
      (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
      (fun _ _ _ _ hres => absurd hres (by decide))
      (fun _ _ _ _ hres => absurd hres (by decide))
    exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind, reduceCtorEq, reduceIte, pure, Except.pure] at h
      -- step 1: Empty
      by_cases h1 : (env.find? emptyA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Empty.rec
      by_cases h2 : ((⟨emptyA :: env.consts⟩ : Env).find?
        emptyRecA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m emptyA
        (fun _ => SetTheory.empty)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [emptyA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [emptyA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => empty_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [emptyA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun _ ψ x hx' => not_mem_empty x hx')
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [emptyA]))
        (fun _ _ _ _ _ _ hx => absurd hx (by simp [emptyA]))
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      have hvalE1 : ∀ ψ' : Name → Nat, m1.val emptyName ψ' =
          SetTheory.empty := fun ψ' => hval1 ψ'
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 emptyRecA
        (fun ψ => emptyRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [emptyRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [emptyRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h6
            cases hr⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => emptyRec_key rfl (fun ψ' => hvalE1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [emptyRecVal]
          rw [hψ uN (by simp [emptyRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_emptyRec_type rfl (fun ψ' => hvalE1 ψ'))
        (fun cv _ hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [emptyRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h6
          intro r hr
          cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [emptyRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h6
          intro r hr
          cases hr)
        (fun hres _ => absurd hres (by decide))
        (fun T j hh => absurd hh.symm (Name.num_ne_str _ _ _ _))
        (fun _ _ _ _ hres => absurd hres (by decide))
        (fun _ _ _ _ hres => absurd hres (by decide))
      exact ⟨m2⟩

    case _ => exact installQuotBasis_sound h m

  | defnDecl cv value hint =>
    simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    -- the structural-Nat pin arm: invert the guard checks and the
    -- pre-insertion value-substituted certification
    have harm : env' =
        ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
          env.consts⟩ ∧
        (natOpNames.contains cv.name = true →
          (natOpGuard (⟨ConstantInfo.defnInfo { cv with type := type }
              value' hint :: env.consts⟩ : Env) cv.name &&
            (natOpDeps cv.name).all (natOpStoredOk
              (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
                env.consts⟩ : Env))) = true ∧
          certifyNatEqs (fueledOps F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) = .ok true) := by
      by_cases hnop : natOpNames.contains cv.name = true
      · rw [if_pos hnop] at h
        by_cases hgd : (natOpGuard (⟨ConstantInfo.defnInfo
              { cv with type := type } value' hint :: env.consts⟩ : Env)
              cv.name &&
            (natOpDeps cv.name).all (natOpStoredOk
              (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
                env.consts⟩ : Env))) = true
        case neg =>
          rw [if_neg hgd] at h
          simp [Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at h
        rw [if_pos hgd] at h
        have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type }
            value' hint :: env.consts⟩ : Env).find? cv.name =
            some (.defnInfo { cv with type := type } value' hint) := by
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.defnInfo { cv with type := type }
              value' hint).name = cv.name from rfl)]
        rw [hfind2] at h
        dsimp only at h
        revert h
        cases hcert0 : certifyNatEqs (fueledOps F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error err => intro h; exact nomatch h
        | ok okb =>
          cases okb with
          | false =>
            intro h
            simp [throw, throwThe, MonadExceptOf.throw, pure,
              Except.pure] at h
          | true =>
            intro h
            simp only [↓reduceIte, pure, Except.pure,
              Except.ok.injEq] at h
            exact ⟨h.symm, fun _ => ⟨hgd, rfl⟩⟩
      · rw [if_neg hnop] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨h.symm, fun hc => absurd hc hnop⟩
    obtain ⟨rfl, harm2⟩ := harm
    -- semantic facts about the annotated type
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false :=
      not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F cv.type hann hwt).fvarsBelow)
    have hbt' : type.looseBVarsBounded 0 = true := annotateCore_looseBVars F cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferTypeCore_sound (φ := ψ) m F hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    refine extend_model m hfind' htp htf htr (annotateCore_looseBVars F cv.type hann hlbt)
      hvp hvf' hvr (annotateCore_looseBVars F value hannv hlbv) hkey hAty hAval
      (ConstantInfo.defnInfo { cv with type := type } value' hint) rfl rfl
      (fun cv2 value2 h2v heq => by injection heq with h1 h2; exact ⟨h1.symm, h2.symm⟩)
      rfl
      hres'
      hpshape'
      ?_
    intro hcontains _
    obtain ⟨hgd, hcert0⟩ := harm2 hcontains
    simp only [Bool.and_eq_true] at hgd
    obtain ⟨hguard2, hdeps2⟩ := hgd
    have hcmem : cv.name ∈ natOpNames := List.contains_iff_mem.mp hcontains
    have hnepins := natOpNames_ne_pins hcmem
    have hs2 : natLitSupported (⟨ConstantInfo.defnInfo
        { cv with type := type } value' hint :: env.consts⟩ : Env) = true :=
      (natOpGuard_inv hguard2).1
    have hfNat : (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
        env.consts⟩ : Env).find? natName = env.find? natName := by
      rw [Env.find?_cons, if_neg (show ¬ ((ConstantInfo.defnInfo
        { cv with type := type } value' hint).name = natName) from
        fun hh => hnepins.1 hh)]
    have hfZero : (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
        env.consts⟩ : Env).find? natZeroName = env.find? natZeroName := by
      rw [Env.find?_cons, if_neg (show ¬ ((ConstantInfo.defnInfo
        { cv with type := type } value' hint).name = natZeroName) from
        fun hh => hnepins.2.1 hh)]
    have hfSucc : (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
        env.consts⟩ : Env).find? natSuccName = env.find? natSuccName := by
      rw [Env.find?_cons, if_neg (show ¬ ((ConstantInfo.defnInfo
        { cv with type := type } value' hint).name = natSuccName) from
        fun hh => hnepins.2.2.1 hh)]
    have hsenv : natLitSupported env = true := by
      rw [← natLitSupported_congr hfNat hfZero hfSucc]
      exact hs2
    refine ⟨hguard2, ?_⟩
    -- the self pin
    have hself : natOpStoredOk (⟨ConstantInfo.defnInfo
        { cv with type := type } value' hint :: env.consts⟩ : Env) cv.name
        = true :=
      List.all_eq_true.mp hdeps2 cv.name (natOpDeps_self hcmem)
    have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type }
        value' hint :: env.consts⟩ : Env).find? cv.name =
        some (.defnInfo { cv with type := type } value' hint) := by
      rw [Env.find?_cons,
        if_pos (show (ConstantInfo.defnInfo { cv with type := type }
          value' hint).name = cv.name from rfl)]
    have hpin2 : natOpTyPinned (⟨ConstantInfo.defnInfo
        { cv with type := type } value' hint :: env.consts⟩ : Env) cv.name
        type = true := by
      unfold natOpStoredOk at hself
      rw [hfind2] at hself
      simp only [Bool.and_eq_true] at hself
      exact hself.2
    have hbne : (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
        env.consts⟩ : Env).find? boolName = env.find? boolName := by
      rw [Env.find?_cons, if_neg (show ¬ ((ConstantInfo.defnInfo
        { cv with type := type } value' hint).name = boolName) from
        fun hh => hnepins.2.2.2.1 hh)]
    have hpin : natOpTyPinned env cv.name type = true := by
      rw [← natOpTyPinned_congr hbne]
      exact hpin2
    have hHm : ∀ ψ : Name → Nat, ∃ hv,
        interpClosed V m.val env ψ value' = some hv ∧
        (cv.name = natPredName → hv ∈ˢ pi 1 (m.val natName ψ)
          (fun _ => m.val natName ψ)) ∧
        (cv.name ≠ natPredName → ∃ C, hv ∈ˢ pi 1 (m.val natName ψ)
          (fun _ => pi 1 (m.val natName ψ) (fun _ => C)) ∧ C ∈ˢ univ 1 ∧
          (cv.name ≠ natBeqName → cv.name ≠ natBleName →
            C = m.val natName ψ)) := by
      intro ψ
      obtain ⟨v, T, hvv, hTT, hmemvT⟩ := hkey ψ
      obtain ⟨h1, h2⟩ := natOpTyPinned_interp m hpin hsenv ψ
      refine ⟨v, hvv, ?_, ?_⟩
      · intro hp
        rw [h1 hp] at hTT
        obtain rfl := Option.some.inj hTT
        exact hmemvT
      · intro hp
        obtain ⟨C, hCi, hCu, hCid⟩ := h2 hp
        rw [hCi] at hTT
        obtain rfl := Option.some.inj hTT
        exact ⟨C, hmemvT, hCu, hCid⟩
    have hdepsE : ∀ n ∈ natOpDeps cv.name, n ≠ cv.name →
        natOpStoredOk env n = true := by
      intro n hn hne
      exact natOpStoredOk_cons_down (c₀ := ConstantInfo.defnInfo
          { cv with type := type } value' hint)
        hne (fun hh => hnepins.2.2.2.1 hh)
        (List.all_eq_true.mp hdeps2 n hn)
    have hboolcE : (cv.name = natBeqName ∨ cv.name = natBleName) →
        (∃ ciT, env.find? boolTrueName = some ciT ∧
          ciT.toConstantVal.levelParams = []) ∧
        (∃ ciF, env.find? boolFalseName = some ciF ∧
          ciF.toConstantVal.levelParams = []) := by
      intro hcb
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ :=
        (natOpGuard_inv hguard2).2.2 hcb
      have hTd : (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
          env.consts⟩ : Env).find? boolTrueName =
          env.find? boolTrueName := by
        rw [Env.find?_cons, if_neg (show ¬ ((ConstantInfo.defnInfo
        { cv with type := type } value' hint).name = boolTrueName) from
        fun hh => hnepins.2.2.2.2.1 hh)]
      have hFd : (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
          env.consts⟩ : Env).find? boolFalseName =
          env.find? boolFalseName := by
        rw [Env.find?_cons, if_neg (show ¬ ((ConstantInfo.defnInfo
        { cv with type := type } value' hint).name = boolFalseName) from
        fun hh => hnepins.2.2.2.2.2 hh)]
      exact ⟨⟨ciT, hTd.symm.trans hT, hlpT⟩, ⟨ciF, hFd.symm.trans hF, hlpF⟩⟩
    have hcertE : ∀ eq ∈ natOpEquations 0 cv.name,
        isDefEqCore env F 2 (Expr.substConst0 cv.name value' eq.1)
          (Expr.substConst0 cv.name value' eq.2) = .ok true := by
      intro eq heq
      exact certifyNatEqs_inv hcert0 _ (List.mem_map_of_mem heq)
    exact natop_eqs_sound m F hcmem hsenv hvf'
      (annotateCore_looseBVars F value hannv hlbv) hAval hHm hdepsE
      hboolcE hcertE
  | thmDecl cv value =>
    simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    -- the theorem-specific proposition check re-runs inference on the type
    cases hst2 : inferTypeCore env F 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSortCore env F 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false :=
      not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F cv.type hann hwt).fvarsBelow)
    have hbt' : type.looseBVarsBounded 0 = true := annotateCore_looseBVars F cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferTypeCore_sound (φ := ψ) m F hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotateCore_looseBVars F cv.type hann hlbt)
      hvp hvf' hvr (annotateCore_looseBVars F value hannv hlbv) hkey hAty hAval
      (ConstantInfo.thmInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 h2 heq => nomatch heq)
      rfl
      hres'
      hpshape'
      (fun _ hex => by obtain ⟨cv₀, v₀, heq⟩ := hex; exact nomatch heq)
      (fun _ hex => by obtain ⟨cv₀, v₀, h₀, heq⟩ := hex; exact nomatch heq)

  | opaqueDecl cv value =>
    simp only [checkDecl, checkDefnVal, checkOpaqueVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false :=
      not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F cv.type hann hwt).fvarsBelow)
    have hbt' : type.looseBVarsBounded 0 = true := annotateCore_looseBVars F cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferTypeCore_sound (φ := ψ) m F hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotateCore_looseBVars F cv.type hann hlbt)
      hvp hvf' hvr (annotateCore_looseBVars F value hannv hlbv) hkey hAty hAval
      (ConstantInfo.thmInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 h2 heq => nomatch heq)
      rfl
      hres'
      hpshape'
      (fun _ hex => by obtain ⟨cv₀, v₀, heq⟩ := hex; exact nomatch heq)
      (fun _ hex => by obtain ⟨cv₀, v₀, h₀, heq⟩ := hex; exact nomatch heq)

private theorem foldlM_sound {env' : Env} :
    ∀ (ds : List Declaration) (env : Env), Nonempty (EnvModel V env) →
      ds.foldlM (checkDecl (fueledOps F)) env = .ok env' → Nonempty (EnvModel V env')
  | [], env, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl (fueledOps F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_sound ds env1 (checkDecl_sound hd m) h

/-- Soundness: every accepted environment has a set-theoretic model. -/
theorem checkDecls_sound {ds : List Declaration} {env' : Env}
    (h : checkDecls (fueledOps F) ds = .ok env') : Nonempty (EnvModel V env') :=
  foldlM_sound ds Env.empty ⟨EnvModel.empty V⟩ h

/-- Model-level core of the consistency corollary: a modeled
environment stores no constant of type `Empty`. -/
theorem no_constant_of_Empty {env : Env} (m : EnvModel V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨T, hTi, hmem⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty] at hTi
  simp only [interpClosed, interpExpr] at hTi
  split at hTi
  · split at hTi
    · obtain rfl := Option.some.inj hTi
      exact m.ind_ok.right.right.right.right.right.right _ _ hmem
    · exact nomatch hTi
  · exact nomatch hTi

/-- A checked `def` or `theorem` stores a constant carrying the
annotated declared type. -/
theorem checkDecl_stores {env env₁ : Env} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint} {d : Declaration}
    (h : checkDecl (fueledOps F) env d = .ok env₁)
    (hd : d = .defnDecl cv value hint ∨ d = .thmDecl cv value) :
    ∃ type, annotateCore env F 0 cv.type = .ok type ∧
      ∃ c ∈ env₁.consts, c.toConstantVal = ⟨cv.name, cv.levelParams, type⟩ := by
  rcases hd with rfl | rfl
  · simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have henv1 : env₁ =
        ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
          env.consts⟩ := by
      by_cases hnop : natOpNames.contains cv.name = true
      · rw [if_pos hnop] at h
        by_cases hgd : (natOpGuard (⟨ConstantInfo.defnInfo
              { cv with type := type } value' hint :: env.consts⟩ : Env)
              cv.name &&
            (natOpDeps cv.name).all (natOpStoredOk
              (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
                env.consts⟩ : Env))) = true
        case neg =>
          rw [if_neg hgd] at h
          simp [Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at h
        rw [if_pos hgd] at h
        have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type }
            value' hint :: env.consts⟩ : Env).find? cv.name =
            some (.defnInfo { cv with type := type } value' hint) := by
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.defnInfo { cv with type := type }
              value' hint).name = cv.name from rfl)]
        rw [hfind2] at h
        dsimp only at h
        revert h
        cases hcert0 : certifyNatEqs (fueledOps F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error err => intro h; exact nomatch h
        | ok okb =>
          cases okb with
          | false =>
            intro h
            simp [throw, throwThe, MonadExceptOf.throw, pure,
              Except.pure] at h
          | true =>
            intro h
            simp only [↓reduceIte, pure, Except.pure,
              Except.ok.injEq] at h
            exact h.symm
      · rw [if_neg hnop] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h.symm
    subst henv1
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩
  · simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    cases hst2 : inferTypeCore env F 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSortCore env F 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩

/-- If any `def`/`theorem` in the input claims type `Empty`, the fold
rejects: at the step that checks it, the extended environment would
store a constant of type `Empty`, contradicting its model. -/
private theorem foldlM_no_Empty_decl :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      ds.foldlM (checkDecl (fueledOps F)) env = .ok env' →
      ∀ {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint},
        (Declaration.defnDecl cv value hint ∈ ds ∨
          Declaration.thmDecl cv value ∈ ds) →
        cv.type = .const emptyName [] → False
  | [], _, _, _, _, _, _, _, hd, _ => by
    rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, cv, value, hint, hd, hty => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl (fueledOps F) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨m⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        have h1 : annotateCore env F 0 (.const emptyName []) =
            .ok type := hann
        cases F with
        | zero =>
          rw [annotateCore_zero] at h1
          simp [throw, throwThe, MonadExceptOf.throw] at h1
        | succ F' =>
          rw [annotateCore_succ] at h1
          simpa [annotateBody, pure, Except.pure] using h1
      obtain ⟨m1⟩ := checkDecl_sound hdd m
      exact no_constant_of_Empty m1 c hc (by rw [hcv])
    · have hd' : Declaration.defnDecl cv value hint ∈ ds ∨
          Declaration.thmDecl cv value ∈ ds := by
        rcases hd with hd | hd
        · rcases List.mem_cons.mp hd with rfl | hmem
          · exact absurd (Or.inl rfl) hdis
          · exact Or.inl hmem
        · rcases List.mem_cons.mp hd with rfl | hmem
          · exact absurd (Or.inr rfl) hdis
          · exact Or.inr hmem
      exact foldlM_no_Empty_decl ds env1 (checkDecl_sound hdd m) h hd' hty

/-- **Input-level consistency corollary**: the checker never accepts a
declaration list containing a `def` or `theorem` whose stated type is
`Empty` — no reference to the resulting environment needed. -/
theorem no_proof_of_Empty_input (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls (fueledOps F) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_decl ds Env.empty ⟨EnvModel.empty V⟩ h hd hty

/-- **No proof of `Empty` is ever accepted.**  If the checker accepts a
declaration list, then no constant in the resulting environment has
type `Empty`.  The name `Empty` is reserved: input declarations cannot
redefine it, so the only thing it can ever denote is the pinned empty
inductive, modeled by the empty set.  Together with the realizability
of the `SetTheory` interface this is the consistency statement: an
accepted proof of the empty type would exhibit a member of the empty
set. -/
theorem no_proof_of_Empty (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls (fueledOps F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound (V := V) h
  exact no_constant_of_Empty m c hc hty

end Setlec
