import Setlec.Model.Extend.Transport

/-!
# Model — split out of `Setlec.Model.Extend`

`extend_model`: the common model-extension argument for a new plain
constant (definition, theorem or axiom) with an annotated, checked
type and value, as a wrapper around `extend_fresh` with the value
interpretation as the hand-supplied valuation.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The common model-extension argument, for a new constant `c₀` with an
annotated, checked type and value. -/
theorem extend_model {env : Env} (m : EnvModel V env)
    {name : Name} {lps : List Name} {type value : Expr}
    (hfind' : env.find? name = none)
    (htp : type.allLevelParamsDefined lps = true)
    (htf : type.hasFvar = false)
    (htr : type.constsResolve env = true)
    (htb : type.looseBVarsBounded 0 = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hvf : value.hasFvar = false)
    (hvr : value.constsResolve env = true)
    (hvb : value.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value)
    (c₀ : ConstantInfo)
    (hc₀cv : c₀.toConstantVal = ⟨name, lps, type⟩)
    (hc₀name : c₀.name = name)
    (hc₀val : ∀ cv2 value2 h2, c₀ = ConstantInfo.defnInfo cv2 value2 h2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀thm : ∀ cv2 value2, c₀ = ConstantInfo.thmInfo cv2 value2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀nb : c₀.isBasis = false)
    (hc₀nres : reservedBasisNames.contains name = false)
    (hc₀pshape : name.isProjFnShape = false)
    (hnatop : natOpNames.contains name = true →
      (∃ cv₀ v₀ h₀, c₀ = ConstantInfo.defnInfo cv₀ v₀ h₀) →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) name = true ∧
      ∀ eq ∈ natOpEquations 0 name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V m.val env ψ 2 (rho0 V) (.const natName []) =
          some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
          (Expr.substConst0 name value eq.1) =
        interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
          (Expr.substConst0 name value eq.2))
    (hdivmod : natDivModNames.contains name = true →
      (∃ cv₀ v₀ h₀, c₀ = ConstantInfo.defnInfo cv₀ v₀ h₀) →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) name = true ∧
      ∀ val' : ConstVal V,
        (∀ ψ : Name → Nat,
          interpClosed V m.val env ψ value = some (val' name ψ)) →
        (∀ n, n ≠ name → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
        DivModEqs V val' name) :
    Nonempty (EnvModel V ⟨c₀ :: env.consts⟩) := by
  have hc₀fresh : env.find? c₀.name = none := by
    rw [hc₀name]
    exact hfind'
  have hwf : ConstWF ⟨c₀ :: env.consts⟩ c₀ := by
    rw [ConstWF, hc₀cv]
    refine ⟨htf, htp, Expr.constsResolve_mono htr, htb, ?_, ?_, ?_⟩
    · intro cv2 value2 h2 heq
      obtain ⟨rfl, rfl⟩ := hc₀val cv2 value2 h2 heq
      exact ⟨hvf, hvp, Expr.constsResolve_mono hvr, hvb⟩
    · intro cv mI rP rules heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
    · intro cv2 value2 heq
      obtain ⟨rfl, rfl⟩ := hc₀thm cv2 value2 heq
      exact ⟨hvf, hvp, Expr.constsResolve_mono hvr, hvb⟩
  have htyres0 : c₀.toConstantVal.type.constsResolve env = true := by
    rw [hc₀cv]
    exact htr
  -- the hand-supplied valuation: the value's interpretation
  obtain ⟨v₀f, hv₀f⟩ : ∃ v₀f : (Name → Nat) → V, v₀f = fun ψ =>
      (interpClosed V m.val env ψ value).getD SetTheory.empty := ⟨_, rfl⟩
  have hv₀ : ∀ ψ : Name → Nat,
      interpClosed V m.val env ψ value = some (v₀f ψ) := by
    intro ψ
    obtain ⟨v, T, hv, -, -⟩ := hkey ψ
    rw [hv, hv₀f]
    simp [hv]
  -- the head clause of `NatOpsOk`, from `hnatop`'s certification
  -- facts through the head-substitution transport
  have hnatophead : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' c₀.name ψ = v₀f ψ) →
      (∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
      ∀ cv₀ v₀' h₀', c₀ = .defnInfo cv₀ v₀' h₀' → c₀.name ∈ natOpNames →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2 (rho0 V)
          (.const natName []) = some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.1 =
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.2 := by
    intro val' hvhead hagreeN cv₀ v₀' h₀' heq hcn
    rw [hc₀name] at hcn
    have hcontains : natOpNames.contains name = true :=
      List.contains_iff_mem.mpr hcn
    obtain ⟨hguard2, heqs⟩ := hnatop hcontains ⟨cv₀, v₀', h₀', heq⟩
    obtain ⟨cvS, vS, hntS, hfS, hlpS⟩ := natOpGuard_self_defn hcn hguard2
    have hfhead : (⟨c₀ :: env.consts⟩ : Env).find? name = some c₀ := by
      rw [Env.find?_cons, if_pos hc₀name]
    rw [hfhead] at hfS
    have hc₀eq : c₀ = ConstantInfo.defnInfo cvS vS hntS := Option.some.inj hfS
    have hlp₀ : c₀.toConstantVal.levelParams = [] := by
      rw [hc₀eq]
      exact hlpS
    have hnepins := natOpNames_ne_pins hcn
    have hfNat : (⟨c₀ :: env.consts⟩ : Env).find? natName =
        env.find? natName := by
      rw [Env.find?_cons, if_neg (fun h => hnepins.1 (hc₀name.symm.trans h))]
    have hfZero : (⟨c₀ :: env.consts⟩ : Env).find? natZeroName =
        env.find? natZeroName := by
      rw [Env.find?_cons,
        if_neg (fun h => hnepins.2.1 (hc₀name.symm.trans h))]
    have hfSucc : (⟨c₀ :: env.consts⟩ : Env).find? natSuccName =
        env.find? natSuccName := by
      rw [Env.find?_cons,
        if_neg (fun h => hnepins.2.2.1 (hc₀name.symm.trans h))]
    have hs2 : natLitSupported (⟨c₀ :: env.consts⟩ : Env) = true :=
      (natOpGuard_inv hguard2).1
    have hsenv : natLitSupported env = true := by
      rw [← natLitSupported_congr hfNat hfZero hfSucc]
      exact hs2
    constructor
    · rw [hc₀name]
      exact hguard2
    · rw [hc₀name]
      intro eq heqm ψ x y hxy
      obtain ⟨hsh1, hsh2⟩ := natOpEquations_shape hcn eq heqm
      obtain ⟨v, T, hv, hT, hmem⟩ := hkey ψ
      have hval'eq : ∀ ψ' : Name → Nat, val' name ψ' =
          (interpClosed V m.val env ψ' value).getD SetTheory.empty := by
        intro ψ'
        rw [← hc₀name, hvhead ψ', hv₀f]
      have hhead : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) (.const c₀.name []) =
          interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
            value := by
        rw [hc₀name, interp_const_mono hfhead hlp₀,
          interp_closed_invariant (cval := m.val) hvf 2
            (updV V (updV V (rho0 V) 0 x) 1 y)]
        unfold interpClosed
        rw [show interpExpr V m.val env ψ 0 (rho0 V) value = some v from hv]
        simp [hval'eq, hv]
      have hprem : ∀ T', interpExpr V m.val env ψ 2 (rho0 V)
          (.const natName []) = some T' → x ∈ˢ T' ∧ y ∈ˢ T' := by
        intro T' hT'
        refine hxy T' ?_
        rw [interpExpr_const_nat hs2]
        rw [interpExpr_const_nat hsenv] at hT'
        rw [← hT']
        have hvals : val' natName ψ = m.val natName ψ :=
          hagreeN natName (fun h => hnepins.1 (h.trans hc₀name).symm) ψ
        rw [hvals]
      have hgoal := heqs eq heqm ψ x y hprem
      rw [interp_substConst0 hc₀fresh hlp₀ hagreeN hhead eq.1 hsh1,
        interp_substConst0 hc₀fresh hlp₀ hagreeN hhead eq.2 hsh2,
        hc₀name]
      exact hgoal

  -- the head clause of `DivModOk`: value-level, so the certification
  -- facts transfer to any valuation agreeing off the head
  have hdivmodhead : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' c₀.name ψ = v₀f ψ) →
      (∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
      ∀ cv₀ v₀' h₀', c₀ = .defnInfo cv₀ v₀' h₀' →
      c₀.name ∈ natDivModNames →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) c₀.name = true ∧
      DivModEqs V val' c₀.name := by
    intro val' hvhead hagreeN cv₀ v₀' h₀' heq hcn
    rw [hc₀name] at hcn
    have hcontains : natDivModNames.contains name = true :=
      List.contains_iff_mem.mpr hcn
    obtain ⟨hguard2, heqsGen⟩ := hdivmod hcontains ⟨cv₀, v₀', h₀', heq⟩
    refine ⟨by rw [hc₀name]; exact hguard2, ?_⟩
    rw [hc₀name]
    refine heqsGen val' ?_ ?_
    · intro ψ
      rw [← hc₀name, hvhead ψ]
      exact hv₀ ψ
    · intro n hne ψ'
      exact hagreeN n (by rw [hc₀name]; exact hne) ψ'
  obtain ⟨m', -, -⟩ := extend_fresh m c₀ v₀f hc₀fresh hwf htyres0
    (fun cv2 value2 h2 heq => by
      obtain ⟨-, rfl⟩ := hc₀val cv2 value2 h2 heq
      exact ⟨hvr, hAval, hv₀⟩)
    (fun cv2 value2 heq => by
      obtain ⟨-, rfl⟩ := hc₀thm cv2 value2 heq
      exact ⟨hvr, hAval, hv₀⟩)
    (fun ψ => by
      obtain ⟨v, T, hv, hT, hmem⟩ := hkey ψ
      refine ⟨T, ?_, ?_⟩
      · rw [hc₀cv]
        exact hT
      · rw [show v₀f ψ = v from by rw [hv₀f]; simp [hv]]
        exact hmem)
    (fun ψ₁ ψ₂ hψ => by
      rw [hv₀f]
      have heqi : interpClosed V m.val env ψ₁ value =
          interpClosed V m.val env ψ₂ value := by
        unfold interpClosed
        refine interp_params_ext m.val_params ?_ value 0 (rho0 V) hvp
        intro p hp
        refine hψ p ?_
        rw [hc₀cv]
        exact hp
      simp [heqi])
    (fun ψ => by
      rw [hc₀cv]
      exact hAty ψ)
    (fun cv caps heq _ => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun cv nP nF heq _ => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun cv caps heq _ => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun hn => absurd ((hc₀name.symm.trans hn) ▸ hc₀nres) (by decide))
    (fun hb _ => by
      rw [hc₀nb] at hb
      exact nomatch hb)
    (fun cv mI rP rules heq => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun val' _ _ cvR mI rP rules heq => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun cvR mI rP rules heq => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun _ hk => by
      rcases hk with ⟨cv, caps, heq⟩ | ⟨cv, cnP, cnF, heq⟩ <;>
        (rw [heq] at hc₀nb; simp [ConstantInfo.isBasis] at hc₀nb))
    (fun T j _ _ _ _ hh _ => by
      exfalso
      rw [hc₀name.symm.trans hh] at hc₀pshape
      exact nomatch hc₀pshape)
    (fun entry heq _ => by
      exfalso
      rw [heq] at hc₀name
      rw [← hc₀name] at hc₀pshape
      simp [ConstantInfo.name, ConstantInfo.toConstantVal, projFnName,
        Name.isProjFnShape] at hc₀pshape)
    (fun cv caps heq _ _ => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    (fun cv caps heq _ _ => by
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb)
    hnatophead
    hdivmodhead
  exact ⟨m'⟩
end Setlec
