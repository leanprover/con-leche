import Setlec.Model.Core.Certs

/-!
# Checker-core soundness: StructEta

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- A successful structural eta certification (in its `With` form,
against a separately derived weak-head-normal type of the stuck side)
identifies the constructor application's interpretation with the stuck
side's: the stored eta law — stated over the public constructor and
projection functions, its family premise discharged from the
certificate's own lookups — reconstructs the member directly. -/
theorem structEtaWith_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {a b tb wtb : Expr} {ρ : Nat → V} {va vb : V}
    (h : structEtaCertWithP env fuel d a b wtb = .ok true)
    (htb : inferTypeCore env fuel d b = .ok tb)
    (hwtb : whnf env fuel d tb = .ok wtb)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps,
    hfn, hfc, hal, hwfn, hfT, hce, hcc, hcp, hcf, hres,
    hresC, htal, hulen, hclps, hTstrip, hlev, hic, hpc, hd1, -, hd2⟩ :=
    structEtaCertWith_inv h
  -- level assignments
  obtain ⟨ψ', hψ'⟩ : ∃ x, x = Level.substFn φ cvT.levelParams us' :=
    ⟨_, rfl⟩
  have hψc : Level.substFn φ cvc.levelParams us = ψ' := by
    rw [hψ', hclps]
    exact Level.substFn_congr (Level.isEquivList_sound hlev φ)
  -- b's type reduces to the structure type; extract the spine facts
  obtain ⟨-, ⟨vb', vtb, hbi, htbi, hmemb⟩, hAtb⟩ :=
    ihi htb hwb hbb hLbb hokb
  obtain rfl : vb = vb' := by
    rw [hvb] at hbi
    exact Option.some.inj hbi
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiw, hAwtb⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hAtb
  have hvtbI : interpExpr V m.val env φ d ρ wtb = some vtb := by
    rw [hiw]
    exact htbi
  have hwtbW' := whnf_WScoped m.wf fuel hwtb hwtbW
  have hbwtb := whnf_looseBVars m.wf fuel hwtb hbtb
  have hLwtb : Expr.LeavesBounded wtb := fun l hl =>
    hLbtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hokwtb : FvarsOk V m.val env φ d ρ wtb :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hoktb
  -- the head's interpretation
  have hvalT : interpExpr V m.val env φ d ρ (.const T us') =
      some (m.val T ψ') := by
    simp only [interpExpr, hfT]
    rw [if_pos (show us'.length =
      (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hulen)]
    rw [hψ']
    rfl
  have hwtb_eq : Expr.mkAppN (.const T us') wtb.getAppArgs = wtb := by
    rw [← hwfn]
    exact Expr.mkAppN_getApp wtb
  have hAwtb' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const T us') wtb.getAppArgs) := by
    rw [hwtb_eq]
    exact hAwtb
  -- the type-argument spine and the type's value fold
  obtain ⟨psv, hspT, hAtargs, hvtb⟩ : ∃ psv,
      InterpSpine m.val env φ d ρ wtb.getAppArgs psv ∧
      (∀ x ∈ wtb.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      vtb = SpineFold V (m.val T ψ') psv := by
    cases hcase : wtb.getAppArgs with
    | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hwtbc : wtb = .const T us' := by
          rw [← Expr.mkAppN_getApp wtb, hwfn, hcase]
          rfl
        rw [hwtbc, hvalT] at hvtbI
        exact (Option.some.inj hvtbI).symm
    | cons t ts =>
      rw [← hcase]
      have hne : wtb.getAppArgs ≠ [] := by
        rw [hcase]
        simp
      obtain ⟨-, hAargs, vf, vs, hvf, hsp, -, hfold⟩ :=
        annotOk_spine_inv _ _ hne hAwtb'
      obtain rfl : m.val T ψ' = vf := by
        rw [hvalT] at hvf
        exact Option.some.inj hvf
      refine ⟨vs, hsp, hAargs, ?_⟩
      rw [hwtb_eq] at hfold
      rw [hfold] at hvtbI
      exact (Option.some.inj hvtbI).symm
  have hpslen : psv.length = wtb.getAppArgs.length :=
    InterpSpine.length hspT
  -- fit the type arguments through the type former's telescope
  obtain ⟨hTtf, -, -, hTtb, -, -⟩ := m.wf _ (find?_mem hfT)
  have hThf : (cvT.type.instantiateLevelParams cvT.levelParams
      us').hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hTtf
  have hTw : WScoped d (cvT.type.instantiateLevelParams cvT.levelParams
      us') := WScoped.of_not_hasFvar hThf
  have hTb : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hTtb
  have hTA : AnnotOk V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    exact AnnotOk.closed_invariant hThf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TT, hTT⟩ : ∃ TT, interpExpr V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TT := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hThf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have htargswf : ∀ x ∈ wtb.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨hwtbW'.getAppArgs x hx, looseBVarsBounded_getAppArgs hbwtb x hx,
      ?_, ?_, hAtargs x hx⟩
    · intro l hl
      exact hLwtb l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        hokwtb
  obtain ⟨restT, hfitIT⟩ := certs_fit ihd ihi _ _ _ TT hic hTw hTb
    (Expr.LeavesBounded.of_not_hasFvar hThf)
    (FvarsOk.of_not_hasFvar hThf) hTA hTT htargswf hspT
  obtain ⟨dT, ρT, restT', hfitT⟩ := TeleFitI.toTeleFit hfitIT hTw (by
    rw [htal]
    exact stripPis_instantiateLevelParams_isSome _ _ _ hTstrip)
  have hmemb' : vb ∈ˢ SpineFold V
      (m.val T (Level.substFn φ cvT.levelParams us')) psv := by
    rw [← hψ']
    rw [hvtb] at hmemb
    exact hmemb
  -- the constructor application's spine
  have ha_eq : Expr.mkAppN (.const c us) a.getAppArgs = a := by
    rw [← hfn]
    exact Expr.mkAppN_getApp a
  have haa' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const c us) a.getAppArgs) := by
    rw [ha_eq]
    exact haa
  have huslen : us.length = cvc.levelParams.length := by
    rw [hclps, ← hulen]
    exact Level.isEquivList_length hlev
  have hvalC : interpExpr V m.val env φ d ρ (.const c us) =
      some (m.val c ψ') := by
    simp only [interpExpr, hfc]
    rw [if_pos (show us.length =
      (ConstantInfo.ctorInfo cvc cnP cnF).toConstantVal.levelParams.length
      from huslen)]
    rw [show (ConstantInfo.ctorInfo cvc cnP cnF).toConstantVal.levelParams
      = cvc.levelParams from rfl, hψc]
  obtain ⟨avs, hspA, haargsA, hva'⟩ : ∃ avs,
      InterpSpine m.val env φ d ρ a.getAppArgs avs ∧
      (∀ x ∈ a.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      va = SpineFold V (m.val c ψ') avs := by
    cases hcase : a.getAppArgs with
    | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hac : a = .const c us := by
          rw [← Expr.mkAppN_getApp a, hfn, hcase]
          rfl
        rw [hac, hvalC] at hva
        exact (Option.some.inj hva).symm
    | cons t ts =>
      rw [← hcase]
      have hane : a.getAppArgs ≠ [] := by
        rw [hcase]
        simp
      obtain ⟨-, hAargs, vf, vs, hvf, hsp, -, hfold⟩ :=
        annotOk_spine_inv _ _ hane haa'
      obtain rfl : m.val c ψ' = vf := by
        rw [hvalC] at hvf
        exact Option.some.inj hvf
      refine ⟨vs, hsp, hAargs, ?_⟩
      rw [ha_eq] at hfold
      rw [hfold] at hva
      exact (Option.some.inj hva).symm
  have haargswf : ∀ x ∈ a.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨hwa.getAppArgs x hx, looseBVarsBounded_getAppArgs hba x hx,
      ?_, ?_, haargsA x hx⟩
    · intro l hl
      exact hLba l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        hoka
  -- the parameter prefix matches the type's arguments
  have hpref : avs.take cnP = psv := by
    refine defEqList_values ihd _ _ _ _ hd1 ?_ htargswf
      (InterpSpine.take cnP hspA) hspT
    intro x hx
    exact haargswf x (List.mem_of_mem_take hx)
  -- the projection certificates
  have hpcFacts : ∀ i, i < cnF → ∃ (cvp : ConstantVal)
      (mIp rPp : Nat) (rulesp : List RecRule),
      env.find? (projFnName T i) =
        some (.recInfo cvp mIp rPp rulesp) ∧
      cvp.levelParams = cvT.levelParams ∧
      (cvp.type.stripPis (wtb.getAppArgs.length + 1)).isSome = true ∧
      iotaCertsP env fuel d
        (cvp.type.instantiateLevelParams cvp.levelParams us')
        (wtb.getAppArgs ++ [b]) = .ok true := by
    intro i hi
    exact structEtaProjCerts_inv (List.range cnF) hpc i
      (List.mem_range.mpr hi)
  -- each projection application's chain facts
  have hprojFacts : ∀ j, j < cnF →
      AnnotOk V m.val env φ d ρ
        (Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b])) ∧
      interpExpr V m.val env φ d ρ
        (Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b])) =
      some (SpineFold V (m.val (projFnName T j) ψ') (psv ++ [vb])) := by
    intro j hj
    obtain ⟨cvp, mIp, rPp, rulesp, hfpj, hplps,
      hpstrip, hicj⟩ := hpcFacts j hj
    have hpname : cvp.name = projFnName T j := by
      have h1 := List.find?_some hfpj
      exact eq_of_beq h1
    have hplen : us'.length = cvp.levelParams.length := by
      rw [hplps]
      exact hulen
    have hψp : Level.substFn φ cvp.levelParams us' = ψ' := by
      rw [hplps, hψ']
    have hvalP : interpExpr V m.val env φ d ρ
        (.const (projFnName T j) us') =
        some (m.val (projFnName T j) ψ') := by
      simp only [interpExpr, hfpj]
      rw [if_pos (show us'.length =
        (ConstantInfo.recInfo cvp mIp rPp
          rulesp).toConstantVal.levelParams.length from hplen)]
      rw [show (ConstantInfo.recInfo cvp mIp rPp
        rulesp).toConstantVal.levelParams = cvp.levelParams from rfl, hψp]
    -- the projection function's type facts
    obtain ⟨hPtf, -, -, hPtb, -, -⟩ := m.wf _ (find?_mem hfpj)
    have hPhf : (cvp.type.instantiateLevelParams cvp.levelParams
        us').hasFvar = false := by
      rw [hasFvar_instantiateLevelParams]
      exact hPtf
    have hPw : WScoped d (cvp.type.instantiateLevelParams cvp.levelParams
        us') := WScoped.of_not_hasFvar hPhf
    have hPb : (cvp.type.instantiateLevelParams cvp.levelParams
        us').looseBVarsBounded 0 = true := by
      rw [looseBVarsBounded_instantiateLevelParams]
      exact hPtb
    have hPA : AnnotOk V m.val env φ d ρ
        (cvp.type.instantiateLevelParams cvp.levelParams us') := by
      obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfpj)
        (Level.substFn φ cvp.levelParams us')
      exact AnnotOk.closed_invariant hPhf d ρ
        (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
    obtain ⟨PT, hPT, hPmem⟩ : ∃ PT, interpExpr V m.val env φ d ρ
        (cvp.type.instantiateLevelParams cvp.levelParams us') = some PT ∧
        m.val (projFnName T j) (Level.substFn φ cvp.levelParams us')
          ∈ˢ PT := by
      obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfpj)
        (Level.substFn φ cvp.levelParams us')
      refine ⟨T0, ?_, ?_⟩
      · rw [interp_closed_invariant hPhf d ρ]
        unfold interpClosed
        rw [interp_instLevels m.val_params]
        exact hT0
      · rw [← hpname]
        exact hTm
    have hargs5 : ∀ x ∈ wtb.getAppArgs ++ [b],
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact htargswf x hx
      · obtain rfl : x = b := by simpa using hx
        exact ⟨hwb, hbb, hLbb, hokb, hab⟩
    have hspPB : InterpSpine m.val env φ d ρ (wtb.getAppArgs ++ [b])
        (psv ++ [vb]) :=
      InterpSpine.append hspT ⟨hvb, trivial⟩
    obtain ⟨restP, hfitIP⟩ := certs_fit ihd ihi _ _ _ PT hicj hPw hPb
      (Expr.LeavesBounded.of_not_hasFvar hPhf)
      (FvarsOk.of_not_hasFvar hPhf) hPA hPT hargs5 hspPB
    obtain ⟨dP, ρP, restP', hfitP⟩ := TeleFitI.toTeleFit hfitIP hPw (by
      rw [show (wtb.getAppArgs ++ [b]).length = wtb.getAppArgs.length + 1
        from by simp]
      exact stripPis_instantiateLevelParams_isSome _ _ _ hpstrip)
    have hψpmem : m.val (projFnName T j) ψ' ∈ˢ PT := by
      rw [← hψp]
      exact hPmem
    have hch := TeleFit.chainSlots hfitP hPA hPT hψpmem
    have hconstA : AnnotOk V m.val env φ d ρ
        (.const (projFnName T j) us') := by
      simp [AnnotOk]
    obtain ⟨hA1, hI1⟩ := annotOk_spine (wtb.getAppArgs ++ [b])
      (.const (projFnName T j) us') hconstA hvalP
      (fun x hx => (hargs5 x hx).2.2.2.2) hspPB hch
    exact ⟨hA1, hI1⟩
  -- the field values are the projections'
  have hprojSpine : InterpSpine m.val env φ d ρ
      ((List.range cnF).map fun i =>
        Expr.mkAppN (.const (projFnName T i) us')
          (wtb.getAppArgs ++ [b]))
      ((List.range cnF).map fun i =>
        SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb])) := by
    have hgen : ∀ (l : List Nat), (∀ i ∈ l, i < cnF) →
        InterpSpine m.val env φ d ρ
          (l.map fun i => Expr.mkAppN (.const (projFnName T i) us')
            (wtb.getAppArgs ++ [b]))
          (l.map fun i =>
            SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb])) := by
      intro l
      induction l with
      | nil => intro _; exact trivial
      | cons i l ih =>
        intro hl
        exact ⟨(hprojFacts i (hl i List.mem_cons_self)).2,
          ih (fun i' hi' => hl i' (List.mem_cons_of_mem _ hi'))⟩
    exact hgen (List.range cnF) (fun i hi => List.mem_range.mp hi)
  have hflds : avs.drop cnP = (List.range cnF).map fun i =>
      SpineFold V (m.val (projFnName T i) ψ') (psv ++ [vb]) := by
    refine defEqList_values ihd _ _ _ _ hd2 ?_ ?_
      (InterpSpine.drop cnP hspA) hprojSpine
    · intro x hx
      exact haargswf x (List.mem_of_mem_drop hx)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hif := hprojFacts i (List.mem_range.mp hi)
      refine ⟨?_, ?_, ?_, ?_, hif.1⟩
      · refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwtbW'.getAppArgs x hx
        · obtain rfl : x = b := by simpa using hx
          exact hwb
      · refine looseBVarsBounded_mkAppN (by rfl) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact looseBVarsBounded_getAppArgs hbwtb x hx
        · obtain rfl : x = b := by simpa using hx
          exact hbb
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact hLwtb l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = b := by simpa using hx
            exact hLbb l hlx
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact hokwtb l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = b := by simpa using hx
            exact hokb l hlx
  -- the stored (public) eta law, its family premise discharged from
  -- the certificate's own lookups
  have hfam : EtaFamilyStored env T caps := by
    refine ⟨by rw [hcc]; exact hresC, ⟨cvc, ?_⟩, ?_⟩
    · rw [hcc, hcp, hcf]
      exact hfc
    · intro j hj
      rw [hcf] at hj
      obtain ⟨cvp, mIp, rPp, rulesp, hfpj, -, -, -⟩ := hpcFacts j hj
      exact ⟨cvp, mIp, rPp, rulesp, hfpj⟩
  have hlaw := m.caps_ok.1 T cvT caps hfT hce hres hfam
  have hvbEq := hlaw φ us' psv vb d ρ dT ρT restT'
    (by rw [hpslen, htal, hcp]) hmemb' hfitT
  rw [hcf, hcc] at hvbEq
  rw [hva', ← List.take_append_drop cnP avs, hpref, hflds]
  rw [hψ']
  exact hvbEq.symm

/-- A successful structural eta certification (whole-certificate form,
deriving the stuck side's type itself). -/
theorem structEta_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : structEtaCertP env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨tb, wtb, htb, hwtb, hW⟩ := structEtaCert_inv h
  exact structEtaWith_sound ihw ihd ihi hW htb hwtb
    hwa hwb hba hbb hLba hLbb hoka hokb haa hab hva hvb

set_option maxHeartbeats 3200000 in
/-- A successful unit-likeness certification identifies the two
interpretations: both values inhabit the same interpreted unit-like
family, whose stored law makes any two members equal. -/
theorem structUnit_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : structUnitCertP env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb, hta, hwta, hwfn, hfT,
    hcu, hres, htal, hulen, hTstrip, htb, hwtb, hde, hic⟩ :=
    structUnitCert_inv h
  obtain ⟨ψ', hψ'⟩ : ∃ x, x = Level.substFn φ cvT.levelParams us' :=
    ⟨_, rfl⟩
  -- a's type facts
  obtain ⟨-, ⟨va', vta, hai, htai, hmema⟩, hAta⟩ :=
    ihi hta hwa hba hLba hoka
  obtain rfl : va = va' := by
    rw [hva] at hai
    exact Option.some.inj hai
  have hwtaW := inferTypeCore_WScoped m.wf fuel hta hwa
  have hbta := inferTypeCore_looseBVars m.wf fuel hta hwa hba hLba
  have hLbta : Expr.LeavesBounded ta := fun l hl =>
    hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hwa l hl)
  have hokta : FvarsOk V m.val env φ d ρ ta :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hwa) hoka
  obtain ⟨hiwa, hAwta⟩ := ihw hwta hwtaW hbta hLbta hokta hAta
  have hvtaI : interpExpr V m.val env φ d ρ wta = some vta := by
    rw [hiwa]
    exact htai
  have hwtaW' := whnf_WScoped m.wf fuel hwta hwtaW
  have hbwta := whnf_looseBVars m.wf fuel hwta hbta
  have hLwta : Expr.LeavesBounded wta := fun l hl =>
    hLbta l (whnf_fvarLeaves m.wf fuel hwta l hl)
  have hokwta : FvarsOk V m.val env φ d ρ wta :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuel hwta) hokta
  -- b's type facts
  obtain ⟨-, ⟨vb', vtb, hbi, htbi, hmemb⟩, hAtb⟩ :=
    ihi htb hwb hbb hLbb hokb
  obtain rfl : vb = vb' := by
    rw [hvb] at hbi
    exact Option.some.inj hbi
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiwb, hAwtb⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hAtb
  have hvtbI : interpExpr V m.val env φ d ρ wtb = some vtb := by
    rw [hiwb]
    exact htbi
  have hwtbW' := whnf_WScoped m.wf fuel hwtb hwtbW
  have hbwtb := whnf_looseBVars m.wf fuel hwtb hbtb
  have hLwtb : Expr.LeavesBounded wtb := fun l hl =>
    hLbtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hokwtb : FvarsOk V m.val env φ d ρ wtb :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hoktb
  -- the two types interpret equally
  have htyeq : vta = vtb :=
    ihd hde hwtaW' hwtbW' hbwta hbwtb hLwta hLwtb hokwta hokwtb
      hAwta hAwtb hvtaI hvtbI
  -- decompose the family application
  have hvalT : interpExpr V m.val env φ d ρ (.const T us') =
      some (m.val T ψ') := by
    simp only [interpExpr, hfT]
    rw [if_pos (show us'.length =
      (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hulen)]
    rw [hψ']
    rfl
  have hwta_eq : Expr.mkAppN (.const T us') wta.getAppArgs = wta := by
    rw [← hwfn]
    exact Expr.mkAppN_getApp wta
  have hAwta' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const T us') wta.getAppArgs) := by
    rw [hwta_eq]
    exact hAwta
  obtain ⟨psv, hspT, hAtargs, hvta⟩ : ∃ psv,
      InterpSpine m.val env φ d ρ wta.getAppArgs psv ∧
      (∀ x ∈ wta.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      vta = SpineFold V (m.val T ψ') psv := by
    cases hcase : wta.getAppArgs with
    | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hwtac : wta = .const T us' := by
          rw [← Expr.mkAppN_getApp wta, hwfn, hcase]
          rfl
        rw [hwtac, hvalT] at hvtaI
        exact (Option.some.inj hvtaI).symm
    | cons t ts =>
      rw [← hcase]
      have hne : wta.getAppArgs ≠ [] := by
        rw [hcase]
        simp
      obtain ⟨-, hAargs, vf, vs, hvf, hsp, -, hfold⟩ :=
        annotOk_spine_inv _ _ hne hAwta'
      obtain rfl : m.val T ψ' = vf := by
        rw [hvalT] at hvf
        exact Option.some.inj hvf
      refine ⟨vs, hsp, hAargs, ?_⟩
      rw [hwta_eq] at hfold
      rw [hfold] at hvtaI
      exact (Option.some.inj hvtaI).symm
  have hpslen : psv.length = wta.getAppArgs.length :=
    InterpSpine.length hspT
  -- fit the type arguments through the family's telescope
  obtain ⟨hTtf, -, -, hTtb, -, -⟩ := m.wf _ (find?_mem hfT)
  have hThf : (cvT.type.instantiateLevelParams cvT.levelParams
      us').hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hTtf
  have hTw : WScoped d (cvT.type.instantiateLevelParams cvT.levelParams
      us') := WScoped.of_not_hasFvar hThf
  have hTb : (cvT.type.instantiateLevelParams cvT.levelParams
      us').looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hTtb
  have hTA : AnnotOk V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    exact AnnotOk.closed_invariant hThf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TT, hTT⟩ : ∃ TT, interpExpr V m.val env φ d ρ
      (cvT.type.instantiateLevelParams cvT.levelParams us') = some TT := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfT)
      (Level.substFn φ cvT.levelParams us')
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hThf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have htargswf : ∀ x ∈ wta.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨hwtaW'.getAppArgs x hx,
      looseBVarsBounded_getAppArgs hbwta x hx, ?_, ?_, hAtargs x hx⟩
    · intro l hl
      exact hLwta l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        hokwta
  obtain ⟨restT, hfitIT⟩ := certs_fit ihd ihi _ _ _ TT hic hTw
    hTb (Expr.LeavesBounded.of_not_hasFvar hThf)
    (FvarsOk.of_not_hasFvar hThf) hTA hTT htargswf hspT
  obtain ⟨dT, ρT, restT', hfitT⟩ := TeleFitI.toTeleFit hfitIT hTw (by
    rw [htal]
    exact stripPis_instantiateLevelParams_isSome _ _ _ hTstrip)
  -- the stored unit law
  have hlaw := m.caps_ok.2 T cvT caps hfT hcu hres
  have hmema' : va ∈ˢ SpineFold V
      (m.val T (Level.substFn φ cvT.levelParams us')) psv := by
    rw [← hψ']
    rw [hvta] at hmema
    exact hmema
  have hmemb' : vb ∈ˢ SpineFold V
      (m.val T (Level.substFn φ cvT.levelParams us')) psv := by
    rw [← hψ']
    rw [← htyeq, hvta] at hmemb
    exact hmemb
  exact hlaw φ us' psv va vb d ρ dT ρT restT'
    (by rw [hpslen, htal]) hmema' hmemb' hfitT

end Claims

end Setlec
