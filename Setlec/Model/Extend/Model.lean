import Setlec.Model.Extend.Sibs

/-!
# Model — split out of `Setlec.Model.Extend`

`extend_model`: the common model-extension argument for a new plain
constant (definition, theorem or axiom) with an annotated, checked
type and value.
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
    (hc₀val : ∀ cv2 value2, c₀ = ConstantInfo.defnInfo cv2 value2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀nb : c₀.isBasis = false)
    (hc₀nres : reservedBasisNames.contains name = false)
    (hc₀pshape : name.isProjFnShape = false)
    (hnatop : natOpNames.contains name = true →
      (∃ cv₀ v₀, c₀ = ConstantInfo.defnInfo cv₀ v₀) →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) name = true ∧
      ∀ eq ∈ natOpEquations 0 name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V m.val env ψ 2 (rho0 V) (.const natName []) =
          some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
          (Expr.substConst0 name value eq.1) =
        interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
          (Expr.substConst0 name value eq.2)) :
    Nonempty (EnvModel V ⟨c₀ :: env.consts⟩) := by
  have hfresh := find?_none_ne hfind'
  obtain ⟨val', hval'⟩ : ∃ val' : ConstVal V, val' = fun n ψ =>
      if n = name
      then (interpClosed V m.val env ψ value).getD SetTheory.empty
      else m.val n ψ := ⟨_, rfl⟩
  have hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ := by
    intro n hn ψ
    have : n ≠ name := by
      intro heq; rw [heq, hfind'] at hn; simp at hn
    simp [hval', this]
  have hc₀fresh : env.find? c₀.name = none := by rw [hc₀name]; exact hfind'
  have htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := val') hc₀fresh hres]
    exact interp_cval_ext hagree e 0 (rho0 V)
  have hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ 0 (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hc₀fresh e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm) e 0 (rho0 V) ha
  have hwf' : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons m.wf ?_
    rw [ConstWF, hc₀cv]
    refine ⟨htf, htp, Expr.constsResolve_mono htr, htb, ?_, ?_⟩
    · intro cv2 value2 heq
      obtain ⟨rfl, rfl⟩ := hc₀val cv2 value2 heq
      exact ⟨hvf, hvp, Expr.constsResolve_mono hvr, hvb⟩
    · intro cv nP nM nm ni rules heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- val_params
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      have hncv : n = name := by rw [← hn, hc₀name]
      subst hncv
      simp only [hval', if_pos rfl]
      have : interpClosed V m.val env ψ₁ value = interpClosed V m.val env ψ₂ value := by
        unfold interpClosed
        refine interp_params_ext m.val_params ?_ value 0 (rho0 V) hvp
        intro p hp
        refine hψ p ?_
        rw [hc₀cv]
        exact hp
      rw [this]
    · next hn =>
      have hne : n ≠ name := by
        intro heq
        rw [heq, hfind'] at hf
        exact nomatch hf
      simp only [hval', if_neg hne]
      exact m.val_params n ci hf ψ₁ ψ₂ hψ
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨v, T, hv, hT, hmem⟩ := hkey ψ
      refine ⟨T, ?_, ?_⟩
      · rw [hc₀cv]
        exact (htrans type htr ψ).trans hT
      · rw [hc₀name]
        simp only [hval', if_pos rfl, hv, Option.getD_some]
        exact hmem
    · obtain ⟨t, ht, hmem⟩ := m.mem_type c hc ψ
      obtain ⟨-, -, hres, -⟩ := m.wf c hc
      refine ⟨t, ?_, ?_⟩
      · rw [htrans c.toConstantVal.type hres ψ]
        exact ht
      · have hne : c.name ≠ name := hfresh c hc
        simp [hval', hne, hmem]
  · -- defn_eq
    intro cv2 value2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · obtain ⟨hcv2, hval2⟩ := hc₀val cv2 value2 heq.symm
      obtain ⟨v, T, hv, -, -⟩ := hkey ψ
      rw [hval2, htrans value hvr ψ, hv, hcv2]
      simp [hval', hv]
    · obtain ⟨-, -, -, -, hvalwf, -⟩ := m.wf _ hmem2
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 rfl
      have := m.defn_eq cv2 value2 hmem2 ψ
      rw [htrans _ hres2 ψ, this]
      have hne : cv2.name ≠ name :=
        hfresh (.defnInfo cv2 value2) hmem2
      simp [hval', hne]
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨?_, ?_⟩
      · rw [hc₀cv]
        exact hAtrans type htr ψ (hAty ψ)
      · intro cv2 value2 heq
        obtain ⟨-, hval2⟩ := hc₀val cv2 value2 heq
        rw [hval2]
        exact hAtrans value hvr ψ (hAval ψ)
    · obtain ⟨-, -, htyres, -, hvalwf, -⟩ := m.wf c hc
      obtain ⟨hA1, hA2⟩ := m.annot_ok c hc ψ
      refine ⟨hAtrans _ htyres ψ hA1, ?_⟩
      intro cv2 value2 heq
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 heq
      exact hAtrans _ hres2 ψ (hA2 cv2 value2 heq)
  · -- ind_ok: the fresh constant is a definition or theorem, so every
    -- inductive-kind lookup still resolves to the old environment, and
    -- the valuation agrees there.
    refine ⟨?_, ?_, ?_, ?_, BasisBlocks.cons m.ind_ok.right.right.right.right.left
      hc₀fresh (fun cv nP nM nm ni rules heq => by
        rw [heq] at hc₀nb
        simp [ConstantInfo.isBasis] at hc₀nb),
      RecCtorsStored.cons m.ind_ok.right.right.right.right.right.left hc₀fresh
        (fun cvR nP nM nm ni rules heq => by
          rw [heq] at hc₀nb
          simp [ConstantInfo.isBasis] at hc₀nb), ?_⟩
    · intro cv caps hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : psigmaName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv caps).name = psigmaName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hlp, hfacts⟩ := m.ind_ok.1 cv caps hfp
        refine ⟨hlp, fun ψ => ?_⟩
        have hvagree : val' psigmaName ψ = m.val psigmaName ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hfacts ψ
    · intro cv nP nF hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : psigmaMkName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.ctorInfo cv nP nF).name = psigmaMkName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hnP, hnF, hlp, hfacts⟩ := m.ind_ok.right.left cv nP nF hfp
        refine ⟨hnP, hnF, hlp, fun ψ => ?_⟩
        have hvagree : val' psigmaMkName ψ = m.val psigmaMkName ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hfacts ψ
    · intro cv caps hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : punitName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv caps).name = punitName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hvagree : val' punitName ψ = m.val punitName ψ := by
          simp [hval', hne]
        rw [hvagree] at hx
        exact m.ind_ok.right.right.left cv caps hfp ψ x hx
    · intro n ci hfp hbasis hres2
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        rw [hc₀nb] at hbasis
        exact nomatch hbasis
      · next hn =>
        have hne : n ≠ name := by
          intro hcontra
          rw [hcontra, hfind'] at hfp
          exact nomatch hfp
        obtain ⟨hpi, hpv⟩ := m.ind_ok.right.right.right.left n ci hfp
          hbasis hres2
        refine ⟨hpi, fun ψ => ?_⟩
        have hvagree : val' n ψ = m.val n ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hpv ψ
    · -- the Empty type stays uninhabited
      intro ψ x hx
      have hne : emptyName ≠ name := by
        intro hcontra
        rw [← hcontra] at hc₀nres
        exact absurd hc₀nres (by decide)
      have hvagree : val' emptyName ψ = m.val emptyName ψ := by
        simp [hval', hne]
      rw [hvagree] at hx
      exact m.ind_ok.right.right.right.right.right.right ψ x hx
  · -- rec_rules: no recursor is added
    exact RecRulesOk.cons m hc₀fresh
      (fun n hn ψ => hagree n hn ψ)
      (fun e hres ψ => htrans e hres ψ)
      (fun e hres ψ hAe => hAtrans e hres ψ hAe)
      (fun cvR nP nM nm ni rules heq => by
        rw [heq] at hc₀nb
        simp [ConstantInfo.isBasis] at hc₀nb)
  · -- modeled_ok: no inductive-kind constant is added
    refine ModeledOk.cons m.modeled_ok m.wf hc₀fresh ?_ ?_ ?_ ?_ ?_ ?_
    · intro n ψ hn
      have hne : n ≠ name := by
        rw [← hc₀name]
        exact hn
      simp [hval', hne]
    · intro cv caps heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
    · intro cv cnP cnF heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
    · intro T j hh
      exfalso
      rw [hc₀name.symm.trans hh] at hc₀pshape
      exact nomatch hc₀pshape
    · intro cv caps heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
    · intro cv caps heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
  · -- nat_ops: preservation, plus the head clause when the new
    -- definition is itself a fast-path operation (`hnatop`'s
    -- certification facts through the head-substitution transport)
    have hagreeN : ∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat,
        val' n ψ' = m.val n ψ' := by
      intro n hne ψ'
      have hne' : n ≠ name := by rw [← hc₀name]; exact hne
      simp [hval', hne']
    refine NatOpsOk.cons m.nat_ops hc₀fresh hagreeN ?_
    intro cv₀ v₀ heq hcn
    rw [hc₀name] at hcn
    have hcontains : natOpNames.contains name = true :=
      List.contains_iff_mem.mpr hcn
    obtain ⟨hguard2, heqs⟩ := hnatop hcontains ⟨cv₀, v₀, heq⟩
    obtain ⟨cvS, vS, hfS, hlpS⟩ := natOpGuard_self_defn hcn hguard2
    have hfhead : (⟨c₀ :: env.consts⟩ : Env).find? name = some c₀ := by
      rw [Env.find?_cons, if_pos hc₀name]
    rw [hfhead] at hfS
    have hc₀eq : c₀ = ConstantInfo.defnInfo cvS vS := Option.some.inj hfS
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
      have hhead : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) (.const c₀.name []) =
          interpExpr V m.val env ψ 2 (updV V (updV V (rho0 V) 0 x) 1 y)
            value := by
        rw [hc₀name, interp_const_mono hfhead hlp₀,
          interp_closed_invariant (cval := m.val) hvf 2
            (updV V (updV V (rho0 V) 0 x) 1 y)]
        unfold interpClosed
        rw [show interpExpr V m.val env ψ 0 (rho0 V) value = some v from hv]
        simp [hval', hv]
      have hprem : ∀ T', interpExpr V m.val env ψ 2 (rho0 V)
          (.const natName []) = some T' → x ∈ˢ T' ∧ y ∈ˢ T' := by
        intro T' hT'
        refine hxy T' ?_
        rw [interpExpr_const_nat hs2]
        rw [interpExpr_const_nat hsenv] at hT'
        rw [← hT']
        have hvals : val' natName ψ = m.val natName ψ := by
          have : natName ≠ name := fun h => hnepins.1 h.symm
          simp [hval', this]
        rw [hvals]
      have hgoal := heqs eq heqm ψ x y hprem
      rw [interp_substConst0 hc₀fresh hlp₀ hagreeN hhead eq.1 hsh1,
        interp_substConst0 hc₀fresh hlp₀ hagreeN hhead eq.2 hsh2,
        hc₀name]
      exact hgoal

end Setlec
