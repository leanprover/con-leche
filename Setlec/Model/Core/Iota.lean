import Setlec.Model.Core.MajorToCtor

/-!
# Checker-core soundness: Iota

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

/-- Soundness of one iota step: the reduct's interpretation matches the
original application spine's, its annotations are truthful, and it stays
well-scoped — everything the whnf recursion needs to continue.  Fully
generic: the fold facts come from the environment model's `rec_rules`,
never from identifying the recursor by name. -/
theorem iota_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {fe ae e'' : Expr} {ρ : Nat → V}
    (hio : iotaRecP env fuel d (.app fe ae) = .ok (some e''))
    (hw : WScoped d (Expr.app fe ae))
    (hb : (Expr.app fe ae).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (Expr.app fe ae))
    (hok : FvarsOk V m.val env φ d ρ (Expr.app fe ae))
    (ha : AnnotOk V m.val env φ d ρ (Expr.app fe ae)) :
    (interpExpr V m.val env φ d ρ e'' =
      interpExpr V m.val env φ d ρ (Expr.app fe ae) ∧
     AnnotOk V m.val env φ d ρ e'') ∧
    WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded e'' ∧ FvarsOk V m.val env φ d ρ e'' := by
  obtain ⟨c, us, cv, nP, nM, nm, ni, rules, major₀, major, cj, usj, cvj,
    cnP, cnF, r, hfn, hfc, hlen, hmaj, hsub, hmfn, hfj, hrule, hml1, hml2,
    har1, har2, hlev, hpeq, hcerts, hmcerts, heout⟩ :=
    iotaRec_inv hio
  obtain rfl : cj = r.ctor :=
    (eq_of_beq (by simpa using List.find?_some hrule)).symm
  -- generic well-scopedness of the reduct
  have hargsW : ∀ x ∈ (Expr.app fe ae).getAppArgs, WScoped d x :=
    fun x hx => hw.getAppArgs x hx
  have hargsB : ∀ x ∈ (Expr.app fe ae).getAppArgs,
      x.looseBVarsBounded 0 = true :=
    fun x hx => looseBVarsBounded_getAppArgs hb x hx
  have hargsL : ∀ x ∈ (Expr.app fe ae).getAppArgs, Expr.LeavesBounded x :=
    fun x hx l hl => hLb l (fvarLeaves_getAppArgs hx l hl)
  have hargsO : ∀ x ∈ (Expr.app fe ae).getAppArgs,
      FvarsOk V m.val env φ d ρ x :=
    fun x hx => FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
      hok
  have hmajarg := getD_mem (l := (Expr.app fe ae).getAppArgs)
    (i := nP + nM + nm + ni) (dflt := Expr.bvar 0) (by omega)
  have hmaj0W : WScoped d major₀ := whnf_WScoped m.wf fuel hmaj
    (hargsW _ hmajarg)
  have hmaj0B : major₀.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hmaj (hargsB _ hmajarg)
  have hmaj0Lsub := whnf_fvarLeaves m.wf fuel hmaj
  have hmaj0L : Expr.LeavesBounded major₀ :=
    fun l hl => hargsL _ hmajarg l (hmaj0Lsub l hl)
  have hmaj0O : FvarsOk V m.val env φ d ρ major₀ :=
    FvarsOk.of_subset hmaj0Lsub (hargsO _ hmajarg)
  -- the stuck major's claims, then the substituted major's
  have hspine0 : Expr.app fe ae =
      Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs) := by
    have := (Expr.mkAppN_getApp (Expr.app fe ae)).symm
    rw [hfn] at this
    exact this
  have hane0 : (Expr.app fe ae).getAppArgs ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  have ha0' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs)) :=
    hspine0 ▸ ha
  obtain ⟨-, hxsA0, -⟩ := annotOk_spine_inv _ _ hane0 ha0'
  obtain ⟨hmieq0, hmA0⟩ := ihw hmaj (hargsW _ hmajarg) (hargsB _ hmajarg)
    (hargsL _ hmajarg) (hargsO _ hmajarg) (hxsA0 _ hmajarg)
  obtain ⟨hcvteq, hcvtA, hcvtW, hcvtB, hcvtL, hcvtO⟩ :=
    litToCtorIfNat_claims (e := major₀) m hmaj0W hmaj0B hmaj0L hmaj0O hmA0
  obtain ⟨hmieqS, hmA, hmajW, hmajB, hmajL, hmajO⟩ :=
    majorToCtor_claims ihw ihd ihi hsub hmfn hfj hml1 har2
      hmcerts hcvtW hcvtB hcvtL hcvtO hcvtA
  obtain ⟨-, -, -, -, -, hrules⟩ := m.wf _ (find?_mem hfc)
  obtain ⟨hrf, hrlp, hrres, hrlb⟩ := hrules cv nP nM nm ni rules rfl r
    (List.mem_of_find?_eq_some hrule)
  have hclInst : (r.rhs.instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]; exact hrf
  have hrhsW : WScoped d (r.rhs.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar hclInst
  have hallW : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), WScoped d x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsW _ (List.mem_of_mem_take hx)
    · exact hmajW.getAppArgs _ (List.mem_of_mem_drop hx)
  have hallB : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsB _ (List.mem_of_mem_take hx)
    · exact looseBVarsBounded_getAppArgs hmajB _ (List.mem_of_mem_drop hx)
  have hallL : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), Expr.LeavesBounded x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsL _ (List.mem_of_mem_take hx)
    · exact fun l hl => hmajL l
        (fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hl)
  have hallO : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), FvarsOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsO _ (List.mem_of_mem_take hx)
    · exact FvarsOk.of_subset
        (fun l hl => fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hl)
        hmajO
  have hscoped : WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e'' ∧ FvarsOk V m.val env φ d ρ e'' := by
    subst heout
    refine ⟨Expr.WScoped.mkAppN hrhsW hallW,
      looseBVarsBounded_mkAppN
        (by rw [looseBVarsBounded_instantiateLevelParams]; exact hrlb)
        hallB, ?_, ?_⟩
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar hclInst] at hl'
        cases hl'
      · exact hallL x hx l hlx
    · intro l hl
      rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar hclInst] at hl'
        cases hl'
      · exact hallO x hx l hlx
  refine ⟨?_, hscoped⟩
  -- the spine's annotation chain
  have hspine : Expr.app fe ae =
      Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs) := by
    have := (Expr.mkAppN_getApp (Expr.app fe ae)).symm
    rw [hfn] at this
    exact this
  have hane : (Expr.app fe ae).getAppArgs ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  have ha' : AnnotOk V m.val env φ d ρ
      (Expr.mkAppN (.const c us) ((Expr.app fe ae).getAppArgs)) :=
    hspine ▸ ha
  obtain ⟨-, hxsA, vf0, vs, hif0, hisp, hchain, hifold⟩ :=
    annotOk_spine_inv _ _ hane ha'
  -- head value
  simp only [interpExpr, hfc] at hif0
  split at hif0
  case isFalse => exact nomatch hif0
  obtain hv0 := (Option.some.inj hif0)
  -- split off the major argument
  obtain ⟨xl, hxeq, hxg⟩ := take_concat_of_length
    (l := (Expr.app fe ae).getAppArgs) (n := nP + nM + nm + ni) hlen
  have hxlmem : xl ∈ (Expr.app fe ae).getAppArgs := by
    rw [hxeq]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hmieq : interpExpr V m.val env φ d ρ major =
      interpExpr V m.val env φ d ρ xl := by
    rw [hmieqS, hcvteq]
    rw [show (Expr.app fe ae).getAppArgs.getD (nP + nM + nm + ni)
        (Expr.bvar 0) = xl from by
      rw [List.getD_eq_getElem?_getD, hxg]
      rfl] at hmieq0
    exact hmieq0
  -- values along the spine, split at the major
  rw [hxeq] at hisp
  obtain ⟨vsi, vst, rfl, hspi, hspl⟩ := InterpSpine.append_inv hisp
  obtain ⟨tvv, rfl⟩ : ∃ tvv, vst = [tvv] := by
    match vst, hspl with
    | [tvv], _ => exact ⟨tvv, rfl⟩
    | [], h => exact nomatch h
    | _ :: _ :: _, h => exact nomatch h.2
  obtain ⟨hixl, -⟩ := hspl
  -- the major's constructor spine
  have hmspine : major = Expr.mkAppN (.const (RecRule.ctor r) usj) major.getAppArgs := by
    have := (Expr.mkAppN_getApp major).symm
    rw [hmfn] at this
    exact this
  have himaj : interpExpr V m.val env φ d ρ major = some tvv := by
    rw [hmieq, hixl]
  have hctor : ∃ ws, (∀ x ∈ major.getAppArgs, AnnotOk V m.val env φ d ρ x) ∧
      InterpSpine m.val env φ d ρ major.getAppArgs ws ∧
      ChainSlots V (m.val (RecRule.ctor r)
        (Level.substFn φ (ConstantInfo.ctorInfo cvj cnP
          cnF).toConstantVal.levelParams usj)) ws ∧
      tvv = SpineFold V (m.val (RecRule.ctor r)
        (Level.substFn φ (ConstantInfo.ctorInfo cvj cnP
          cnF).toConstantVal.levelParams usj)) ws ∧
      ws.length = cnP + cnF := by
    by_cases hm0 : major.getAppArgs = []
    · refine ⟨[], by simp [hm0], by simp [hm0, InterpSpine], trivial,
        ?_, by rw [hm0] at hml1; exact hml1⟩
      rw [hmspine, hm0] at himaj
      simp only [Expr.mkAppN, interpExpr, hfj] at himaj
      split at himaj
      · exact (Option.some.inj himaj).symm
      · exact nomatch himaj
    · have hmA' : AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const (RecRule.ctor r) usj) major.getAppArgs) :=
        hmspine ▸ hmA
      obtain ⟨-, hmxsA, w0, ws, hiw0, hmsp, hmchain, hmfold⟩ :=
        annotOk_spine_inv _ _ hm0 hmA'
      simp only [interpExpr, hfj] at hiw0
      split at hiw0
      · obtain hw0 := (Option.some.inj hiw0)
        subst hw0
        refine ⟨ws, hmxsA, hmsp, hmchain, ?_,
          by rw [InterpSpine.length hmsp, hml1]⟩
        rw [hmspine] at himaj
        rw [hmfold] at himaj
        exact (Option.some.inj himaj).symm
      · exact nomatch hiw0
  obtain ⟨ws, hmxsA, hmsp, hmchain, htveq, hwslen⟩ := hctor
  -- the certified telescope fits
  obtain ⟨hRtf, -, -, hRtb, -, -⟩ := m.wf _ (find?_mem hfc)
  have hRhf : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar
      = false := by
    rw [hasFvar_instantiateLevelParams]; exact hRtf
  have hRw : WScoped d (cv.type.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar hRhf
  have hRb : (cv.type.instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]; exact hRtb
  have hRA : AnnotOk V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfc)
      (Level.substFn φ cv.levelParams us)
    exact AnnotOk.closed_invariant hRhf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨T, hRT⟩ : ∃ T, interpExpr V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us) = some T := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfc)
      (Level.substFn φ cv.levelParams us)
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hRhf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have hcertargs : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take
      (nP + nM + nm + ni) ++ [major]),
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      FvarsOk V m.val env φ d ρ x ∧ AnnotOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxm := List.mem_of_mem_take hx
      exact ⟨hargsW _ hxm, hargsB _ hxm, hargsL _ hxm, hargsO _ hxm,
        hxsA _ hxm⟩
    · obtain rfl : x = major := by simpa using hx
      exact ⟨hmajW, hmajB, hmajL, hmajO, hmA⟩
  have hspR : InterpSpine m.val env φ d ρ
      ((Expr.app fe ae).getAppArgs.take (nP + nM + nm + ni) ++ [major])
      (vsi ++ [tvv]) :=
    InterpSpine.append hspi ⟨himaj, trivial⟩
  obtain ⟨restR, hfitIR⟩ := certs_fit ihd ihi
    _ _ _ T hcerts hRw hRb (Expr.LeavesBounded.of_not_hasFvar hRhf)
    (FvarsOk.of_not_hasFvar hRhf) hRA hRT hcertargs hspR
  obtain ⟨dR, ρR, restR', hfitR⟩ := TeleFitI.toTeleFit hfitIR hRw (by
    rw [show ((Expr.app fe ae).getAppArgs.take (nP + nM + nm + ni) ++
        [major]).length = nP + nM + nm + ni + 1 from by
      rw [List.length_append, List.length_take]
      simp [hlen]]
    exact stripPis_instantiateLevelParams_isSome _ _ _ har1)
  obtain ⟨hCtf, -, -, hCtb, -, -⟩ := m.wf _ (find?_mem hfj)
  have hChf : (cvj.type.instantiateLevelParams cvj.levelParams usj).hasFvar
      = false := by
    rw [hasFvar_instantiateLevelParams]; exact hCtf
  have hCw : WScoped d (cvj.type.instantiateLevelParams cvj.levelParams
      usj) := WScoped.of_not_hasFvar hChf
  have hCb : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]; exact hCtb
  have hCA : AnnotOk V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    exact AnnotOk.closed_invariant hChf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TC, hCT⟩ : ∃ TC, interpExpr V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC := by
    obtain ⟨T0, hT0, -⟩ := m.mem_type _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    refine ⟨T0, ?_⟩
    rw [interp_closed_invariant hChf d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hT0
  have hcertmargs : ∀ x ∈ major.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      FvarsOk V m.val env φ d ρ x ∧ AnnotOk V m.val env φ d ρ x := by
    intro x hxm
    exact ⟨hmajW.getAppArgs _ hxm,
      looseBVarsBounded_getAppArgs hmajB _ hxm,
      fun l hl => hmajL l (fvarLeaves_getAppArgs hxm l hl),
      FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hxm l hl) hmajO,
      hmxsA _ hxm⟩
  obtain ⟨restC, hfitIC⟩ := certs_fit ihd ihi
    _ _ _ TC hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
    (FvarsOk.of_not_hasFvar hChf) hCA hCT hcertmargs hmsp
  -- rebase the constructor fit at the recursor fit's final frame
  obtain ⟨hdR, hagrR, -⟩ := TeleFit.toTeleFitI hfitR hRw
  have hfitIC' := TeleFitI.lift hfitIC hCw hdR hagrR
  obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC'
    (hCw.mono hdR) (by
    rw [show major.getAppArgs.length = cnP + cnF from hml1]
    exact stripPis_instantiateLevelParams_isSome _ _ _ har2)
  -- the rule's fold facts
  obtain ⟨hrhsA, hfolds⟩ := m.rec_rules c cv nP nM nm ni rules hfc r
    (List.mem_of_find?_eq_some hrule)
  have hchain' : ChainSlots V (m.val c
      (Level.substFn φ (ConstantInfo.recInfo cv nP nM nm ni
        rules).toConstantVal.levelParams us)) (vsi ++ [tvv]) := by
    rw [hv0]
    exact hchain
  have hvsilen : vsi.length = nP + nM + nm + ni := by
    have := InterpSpine.length hspi
    rw [this, List.length_take]
    rw [hxeq] at hlen
    simp at hlen
    omega
  have hparameq : ws.take cnP = (vsi ++ [tvv]).take cnP := by
    have hspT1 : InterpSpine m.val env φ d ρ
        (major.getAppArgs.take cnP) (ws.take cnP) :=
      InterpSpine.take _ hmsp
    have hspT2 : InterpSpine m.val env φ d ρ
        ((Expr.app fe ae).getAppArgs.take cnP)
        ((vsi ++ [tvv]).take cnP) := by
      have := InterpSpine.take cnP hisp
      rw [← hxeq] at this
      exact this
    refine defEqList_values ihd
      _ _ _ _ hpeq ?_ ?_ hspT1 hspT2
    · intro x hx
      have hxm := List.mem_of_mem_take hx
      exact ⟨hmajW.getAppArgs _ hxm,
        looseBVarsBounded_getAppArgs hmajB _ hxm,
        fun l hl => hmajL l (fvarLeaves_getAppArgs hxm l hl),
        FvarsOk.of_subset
          (fun l hl => fvarLeaves_getAppArgs hxm l hl) hmajO,
        hmxsA _ hxm⟩
    · intro x hx
      have hxm := List.mem_of_mem_take hx
      exact ⟨hargsW _ hxm, hargsB _ hxm, hargsL _ hxm, hargsO _ hxm,
        hxsA _ hxm⟩
  have hψeq : ∀ p ∈ cvj.levelParams,
      Level.substFn φ
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams usj p =
      Level.substFn φ
        (ConstantInfo.recInfo cv nP nM nm ni rules).toConstantVal.levelParams
        us p := by
    intro p hp
    have h1 : Level.substFn φ cvj.levelParams usj =
        Level.substFn φ cvj.levelParams
          (cvj.levelParams.map fun q =>
            Level.subst cv.levelParams us (.param q)) :=
      Level.substFn_congr (Level.isEquivList_sound hlev φ)
    have h2 : (cvj.levelParams.map fun q =>
        Level.subst cv.levelParams us (.param q)) =
        (cvj.levelParams.map Level.param).map
          (Level.subst cv.levelParams us) := by
      simp [List.map_map, Function.comp]
    have h3 := Level.substFn_map_subst (φ := φ) (ks := cv.levelParams)
      (vs := us) (ks' := cvj.levelParams)
      (ws := cvj.levelParams.map Level.param) (by simp) hp
    show Level.substFn φ cvj.levelParams usj p = _
    rw [h1, h2, h3, Level.substFn_map_param]
    rfl
  obtain ⟨R, hRi, hfoldEq, hRchain⟩ := hfolds cvj cnP cnF hfj _ _
    vsi ws tvv hvsilen hwslen hchain' hmchain htveq hparameq hψeq
    ⟨φ, us, usj, d, ρ, dR, ρR, restR', dC, ρC, restC', rfl, rfl,
      hfitR, hfitC⟩
  -- the reduct's interpretation and annotation chain
  have hRinst : interpExpr V m.val env φ d ρ
      (r.rhs.instantiateLevelParams cv.levelParams us) = some R := by
    rw [interp_closed_invariant hclInst d ρ]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hRi
  have hArhs : AnnotOk V m.val env φ d ρ
      (r.rhs.instantiateLevelParams cv.levelParams us) := by
    have h1 := AnnotOk.instLevels (ks := cv.levelParams) (vs := us)
      m.val_params r.rhs 0 (rho0 V)
      (hrhsA (Level.substFn φ cv.levelParams us))
    exact AnnotOk.closed_invariant hclInst d ρ h1
  have htake : (Expr.app fe ae).getAppArgs.take (nP + nM + nm) =
      ((Expr.app fe ae).getAppArgs.take (nP + nM + nm + ni)).take
        (nP + nM + nm) := by
    rw [List.take_take]
    congr 1
    omega
  have hspR : InterpSpine m.val env φ d ρ
      ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
        major.getAppArgs.drop cnP)
      (vsi.take (nP + nM + nm) ++ ws.drop cnP) := by
    refine InterpSpine.append ?_ (InterpSpine.drop cnP hmsp)
    rw [htake]
    exact InterpSpine.take _ hspi
  have hxsAR : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take (nP + nM + nm) ++
      major.getAppArgs.drop cnP), AnnotOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxsA _ (List.mem_of_mem_take hx)
    · exact hmxsA _ (List.mem_of_mem_drop hx)
  obtain ⟨hAe, hie⟩ := annotOk_spine _ _ hArhs hRinst hxsAR hspR hRchain
  rw [← heout] at hAe hie
  refine ⟨?_, hAe⟩
  have hifold' : interpExpr V m.val env φ d ρ (Expr.app fe ae) =
      some (SpineFold V vf0 (vsi ++ [tvv])) := by
    rw [← hspine] at hifold
    exact hifold
  rw [hie, hifold', ← hv0, hfoldEq]

end Claims

end Setlec
