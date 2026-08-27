import Setlec.Model.Core.MajorToCtor
import Setlec.Model.Core.NestedFire
import Setlec.Model.RuleFold

/-!
# Checker-core soundness: Iota

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims mode m φ fuel) (ihd : DefEqClaims mode m φ fuel)
  (ihi : InferClaims mode m φ fuel)

/-- Soundness of one iota step: the reduct's interpretation matches the
original application spine's, its annotations are truthful, and it stays
well-scoped — everything the whnf recursion needs to continue.  Fully
generic: the fold facts come from the environment model's `rec_rules`,
never from identifying the recursor by name. -/
theorem iota_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims mode m φ fuel) (ihd : DefEqClaims mode m φ fuel)
    (ihi : InferClaims mode m φ fuel)
    {d : Nat} {fe ae e'' : Expr} {ρ : Nat → V}
    (hio : iotaRecP mode env fuel d (.app fe ae) = .ok (some e''))
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
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj, cvj,
    cnP, cnF, r, cbinders, cbody, residual, cr, usr, hfn, hfc, hlen, hmaj,
    hlit, hsub, hmfn, hfj, hrule, hml, har1, har2, hplain, hlev, hpeq, hcerts,
    hmcerts, hstrip, hres, hrfn, hieq, heout⟩ :=
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
    (i := mI) (dflt := Expr.bvar 0) (by omega)
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
    litMajorToCtor_claims ihw hlit hmaj0W hmaj0B hmaj0L hmaj0O hmA0
  obtain ⟨hmieqS, hmA, hmajW, hmajB, hmajL, hmajO⟩ :=
    majorToCtor_claims ihw ihd ihi hsub hmfn hfj
      hcvtW hcvtB hcvtL hcvtO hcvtA
  obtain ⟨-, -, -, -, -, hrules, -⟩ := m.wf _ (find?_mem hfc)
  obtain ⟨hrf, hrlp, hrres, hrlb, hnestWF⟩ := hrules cv mI rP rules rfl r
    (List.mem_of_find?_eq_some hrule)
  have hclInst : (r.rhs.instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]; exact hrf
  have hrhsW : WScoped d (r.rhs.instantiateLevelParams cv.levelParams us) :=
    WScoped.of_not_hasFvar hclInst
  have hallW : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take rP ++
      major.getAppArgs.drop r.ctorParams), WScoped d x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsW _ (List.mem_of_mem_take hx)
    · exact hmajW.getAppArgs _ (List.mem_of_mem_drop hx)
  have hallB : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take rP ++
      major.getAppArgs.drop r.ctorParams), x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsB _ (List.mem_of_mem_take hx)
    · exact looseBVarsBounded_getAppArgs hmajB _ (List.mem_of_mem_drop hx)
  have hallL : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take rP ++
      major.getAppArgs.drop r.ctorParams), Expr.LeavesBounded x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hargsL _ (List.mem_of_mem_take hx)
    · exact fun l hl => hmajL l
        (fvarLeaves_getAppArgs (List.mem_of_mem_drop hx) l hl)
  have hallO : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take rP ++
      major.getAppArgs.drop r.ctorParams), FvarsOk V m.val env φ d ρ x := by
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
    (l := (Expr.app fe ae).getAppArgs) (n := mI) hlen
  have hxlmem : xl ∈ (Expr.app fe ae).getAppArgs := by
    rw [hxeq]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hmieq : interpExpr V m.val env φ d ρ major =
      interpExpr V m.val env φ d ρ xl := by
    rw [hmieqS, hcvteq]
    rw [show (Expr.app fe ae).getAppArgs.getD mI
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
      ws.length = r.ctorParams + r.nfields ∧
      usj.length = cvj.levelParams.length := by
    by_cases hm0 : major.getAppArgs = []
    · refine ⟨[], by simp [hm0], by simp [hm0, InterpSpine], trivial,
        ?_, by rw [hm0] at hml; exact hml, ?_⟩
      · rw [hmspine, hm0] at himaj
        simp only [Expr.mkAppN, interpExpr, hfj] at himaj
        split at himaj
        · exact (Option.some.inj himaj).symm
        · exact nomatch himaj
      · rw [hmspine, hm0] at himaj
        simp only [Expr.mkAppN, interpExpr, hfj] at himaj
        split at himaj
        · next _ hcond => exact hcond
        · exact nomatch himaj
    · have hmA' : AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const (RecRule.ctor r) usj) major.getAppArgs) :=
        hmspine ▸ hmA
      obtain ⟨-, hmxsA, w0, ws, hiw0, hmsp, hmchain, hmfold⟩ :=
        annotOk_spine_inv _ _ hm0 hmA'
      simp only [interpExpr, hfj] at hiw0
      split at hiw0
      · next _ hcond =>
        obtain hw0 := (Option.some.inj hiw0)
        subst hw0
        refine ⟨ws, hmxsA, hmsp, hmchain, ?_,
          by rw [InterpSpine.length hmsp, hml], hcond⟩
        rw [hmspine] at himaj
        rw [hmfold] at himaj
        exact (Option.some.inj himaj).symm
      · exact nomatch hiw0
  obtain ⟨ws, hmxsA, hmsp, hmchain, htveq, hwslen, husjlen⟩ := hctor
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
  obtain ⟨T, hRT, hRmem⟩ : ∃ T, interpExpr V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us) = some T ∧
      m.val c (Level.substFn φ cv.levelParams us) ∈ˢ T := by
    obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfc)
      (Level.substFn φ cv.levelParams us)
    have hcname : cv.name = c := by
      have := find?_name hfc
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T0, ?_, ?_⟩
    · rw [interp_closed_invariant hRhf d ρ]
      unfold interpClosed
      rw [interp_instLevels m.val_params]
      exact hT0
    · rw [← hcname]
      exact hTm
  have hvf0T : vf0 ∈ˢ T := hv0 ▸ hRmem
  have hcertargs : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take
      mI ++ [major]),
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
      ((Expr.app fe ae).getAppArgs.take mI ++ [major])
      (vsi ++ [tvv]) :=
    InterpSpine.append hspi ⟨himaj, trivial⟩
  obtain ⟨restR, hfitIR⟩ := certs_fit ihd ihi
    _ _ _ T hcerts hRw hRb (Expr.LeavesBounded.of_not_hasFvar hRhf)
    (FvarsOk.of_not_hasFvar hRhf) hRA hRT hcertargs hspR
  obtain ⟨dR, ρR, restR', hfitR⟩ := TeleFitI.toTeleFit hfitIR hRw (by
    rw [show ((Expr.app fe ae).getAppArgs.take mI ++
        [major]).length = mI + 1 from by
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
  obtain ⟨TC, hCT, hCmem⟩ : ∃ TC, interpExpr V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC ∧
      m.val (RecRule.ctor r) (Level.substFn φ cvj.levelParams usj)
        ∈ˢ TC := by
    obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    have hcjname : cvj.name = RecRule.ctor r := by
      have := find?_name hfj
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T0, ?_, ?_⟩
    · rw [interp_closed_invariant hChf d ρ]
      unfold interpClosed
      rw [interp_instLevels m.val_params]
      exact hT0
    · rw [← hcjname]
      exact hTm
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
  -- the recursor fit's final-frame fvar spine (for the nested premise)
  obtain ⟨hdR, hagrR, argsRF, hfitRF, hfvRF⟩ :=
    TeleFit.toTeleFitI hfitR hRw
  -- the rule's total λ-equality
  obtain ⟨hrhsA, hlemi', hplainLe', hpinsLen', hfolds⟩ :=
    m.rec_rules c cv mI rP rules hfc r (List.mem_of_find?_eq_some hrule)
  have hlemi : rP ≤ mI := hlemi' hplain
  have hvsilen : vsi.length = mI := by
    have := InterpSpine.length hspi
    rw [this, List.length_take]
    rw [hxeq] at hlen
    simp at hlen
    omega
  -- the kernel's residual is the constructor walk's
  rw [piResidual_eq_telescopeInst, TeleFitI.rest_eq hfitIC] at hres
  obtain rfl : restC = residual := Option.some.inj hres
  obtain ⟨hrw, hrb, hrA, hrleaves⟩ := TeleFitI.rest_wf hfitIC hCw hCb hCA
  have hrL : Expr.LeavesBounded restC := by
    intro l hl
    rcases hrleaves l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hChf] at hl'
      cases hl'
    · exact (hcertmargs a ha).2.2.1 l hla
  have hrO : FvarsOk V m.val env φ d ρ restC := by
    intro l hl
    rcases hrleaves l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hChf] at hl'
      cases hl'
    · exact (hcertmargs a ha).2.2.2.1 l hla
  have hlenieq := defEqList_length (env := env) (fuel := fuel) _ _ hieq
  have htakelen : ((Expr.app fe ae).getAppArgs.take
      mI).length = mI := by
    rw [List.length_take, hlen]
    omega
  -- the runtime residual as an instantiation sequence of the
  -- (instantiated) constructor result
  obtain ⟨mid, hmid, bs', body', hstripMid, hbodyMid, -⟩ :=
    telescopeInst_stripPis (r.ctorParams + r.nfields) major.getAppArgs 0 hml
      (by simpa using hstrip)
  rw [TeleFitI.rest_eq hfitIC] at hmid
  obtain rfl : restC = mid := Option.some.inj hmid
  have hrestCeq : restC = instSeq major.getAppArgs
      (r.ctorParams + r.nfields - 1) cbody := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstripMid
    rw [hstripMid.2, hbodyMid]
    simp
  have hcbodyF : cbody.hasFvar = false :=
    stripPis_body_hasFvar _ hstrip hChf
  have hcbodyB : cbody.looseBVarsBounded (r.ctorParams + r.nfields) = true := by
    have := stripPis_body_bounded _ hstrip hCb
    simpa using this
  have hcspine : cbody = Expr.mkAppN (.const cr usr) cbody.getAppArgs := by
    have := (Expr.mkAppN_getApp cbody).symm
    rw [hrfn] at this
    exact this
  have hinstM : instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) cbody =
      Expr.mkAppN (.const cr usr)
        (cbody.getAppArgs.map (instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) ·)) := by
    conv => lhs; rw [hcspine]
    rw [instSeq_mkAppN, instSeq_eq_self _ _ (by simp [Expr.looseBVarsBounded])]
  have hrArgs : restC.getAppArgs =
      cbody.getAppArgs.map (instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) ·) := by
    rw [hrestCeq, hinstM, Expr.getAppArgs_mkAppN]
    simp [Expr.getAppArgs]
  -- the fire-mode premises, specialized from the kernel's comparand
  -- checks (`recFireComparands`)
  have hplainPrem : r.fire = RecRuleFire.plain →
      ws.take r.ctorParams = (vsi ++ [tvv]).take r.ctorParams ∧
      ∀ p ∈ cvj.levelParams,
        Level.substFn φ
          (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams
          usj p =
        Level.substFn φ
          (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams
          us p := by
    intro hfp
    have hpeq' : defEqListP mode env fuel d
        (major.getAppArgs.take r.ctorParams)
        ((Expr.app fe ae).getAppArgs.take r.ctorParams) = .ok true := by
      have h0 := hpeq
      simp only [recFireComparands, hfp] at h0
      exact h0
    have hlev' : Level.isEquivList usj (cvj.levelParams.map fun p =>
        Level.subst cv.levelParams us (.param p)) = some true := by
      have h0 := hlev
      simp only [recFireComparands, hfp] at h0
      exact h0
    constructor
    · have hspT1 : InterpSpine m.val env φ d ρ
          (major.getAppArgs.take r.ctorParams) (ws.take r.ctorParams) :=
        InterpSpine.take _ hmsp
      have hspT2 : InterpSpine m.val env φ d ρ
          ((Expr.app fe ae).getAppArgs.take r.ctorParams)
          ((vsi ++ [tvv]).take r.ctorParams) := by
        have := InterpSpine.take r.ctorParams hisp
        rw [← hxeq] at this
        exact this
      refine defEqList_values ihd
        _ _ _ _ hpeq' ?_ ?_ hspT1 hspT2
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
    · intro p hp
      have h1 : Level.substFn φ cvj.levelParams usj =
          Level.substFn φ cvj.levelParams
            (cvj.levelParams.map fun q =>
              Level.subst cv.levelParams us (.param q)) :=
        Level.substFn_congr (Level.isEquivList_sound hlev' φ)
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
  have hnestedPrem : ∀ lvls pins,
      r.fire = RecRuleFire.nested lvls pins →
      rP ≤ mI ∧
      (∀ p ∈ cvj.levelParams,
        Level.substFn φ
          (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams
          usj p =
        Level.substFn (Level.substFn φ
          (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us)
          cvj.levelParams lvls p) ∧
      ∃ (dP : Nat) (ρP : Nat → V) (spineP : List Expr),
        FvarSpine dP ρP spineP (vsi.take rP) ∧
        (∀ a ∈ spineP, ∃ i nm, a = Expr.fvar i nm (.sort .zero)) ∧
        (pins.map fun pin => Expr.instSeq spineP (spineP.length - 1)
          (pin.instantiateLevelParams cv.levelParams us)).mapM
          (interpExpr V m.val env φ dP ρP) =
          some (ws.take r.ctorParams) :=
    nested_fire_premise ihd hnestWF hpeq hlev husjlen hml hvsilen har1
      htakelen hargsW hargsB hargsL hargsO hmajW hmajB hmajL hmajO
      hmxsA hmsp hspi hRw hRb hRA hRhf hfitIR hdR hagrR hfitRF hfvRF
  -- ===== the total λ-equality, consumed =====
  obtain ⟨fvms, bL, hparts, hFwf, hflen, -, hψf⟩ :=
    hfolds cvj cnP cnF hfj hplain
  obtain ⟨hAL, Rv, hLi, hRi⟩ :=
    hψf (Level.substFn φ (ConstantInfo.recInfo cv mI rP
      rules).toConstantVal.levelParams us)
  obtain ⟨fvsP, rest0, usC, cargs, cdoms0, crestP, xFvs, crest2, rbs, rb,
    heqO, hcinst, hopenX, hstripR, hfireCase, hfvmsEq, hbLEq⟩ :=
    ruleLhsParts_inv hparts
  obtain ⟨hfvsPinst, hfvsPlen, hfvsPshape⟩ := openPisAtFvars_spec rP 0 heqO
  obtain ⟨hxFvsInst, hxFvsLen, hxFvsShape⟩ :=
    openPisAtFvars_spec (RecRule.nfields r) rP hopenX
  -- the target value spine and the canonical frame
  have hwsl : ws.length = r.ctorParams + r.nfields := hwslen
  have hxslen : (vsi.take rP ++ ws.drop r.ctorParams).length =
      rP + RecRule.nfields r := by
    simp only [List.length_append, List.length_take, List.length_drop,
      hvsilen, hwsl]
    omega
  -- the canonical parameter-spine values: the constructor's parameter
  -- values are the leading recursor arguments (plain) resp. the stored
  -- pins' values (nested)
  have hcargsLen : cargs.length = RecRule.ctorParams r := by
    rcases hfireCase with ⟨hfp, -, hce⟩ | ⟨lvls, pins, hfn', -, hce⟩
    · rw [hce, List.length_take, hfvsPlen]
      exact Nat.min_eq_left (hplainLe' hfp)
    · rw [hce, List.length_map]
      exact hpinsLen' lvls pins hfn'
  -- ===== the canonical frame: spine, values, argument facts =====
  have hrbsLen : rbs.length = rP + RecRule.nfields r :=
    Expr.stripLams_length _ hstripR
  have hspineLen : (fvsP ++ xFvs).length = rP + RecRule.nfields r := by
    rw [List.length_append, hfvsPlen, hxFvsLen]
  have hzipfst : ∀ (k : Nat) (p : Expr × BinderMeta), fvms[k]? = some p →
      (fvsP ++ xFvs)[k]? = some p.1 := by
    intro k p hp
    rw [hfvmsEq] at hp
    exact (zip_getElem?_parts _ _ k p hp).1
  have hzipfst' : ∀ (k : Nat) (a : Expr), (fvsP ++ xFvs)[k]? = some a →
      ∃ mb, fvms[k]? = some (a, mb) := by
    intro k a ha
    have hk : k < rP + RecRule.nfields r := by
      rcases Nat.lt_or_ge k (rP + RecRule.nfields r) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by omega)] at ha
        exact nomatch ha
    obtain ⟨p, hp⟩ : ∃ p, fvms[k]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by rw [hflen]; omega)⟩
    obtain ⟨h1, -⟩ := zip_getElem?_parts _ _ k p (by rw [← hfvmsEq]; exact hp)
    rw [ha] at h1
    obtain rfl := Option.some.inj h1
    exact ⟨p.2, hp⟩
  -- the value spine and the canonical valuation
  have hxslen' : (vsi.take rP ++ ws.drop r.ctorParams).length =
      rP + RecRule.nfields r := hxslen
  -- frame entry well-formedness, positionally
  have hentryWf : ∀ (k : Nat) (a : Expr), (fvsP ++ xFvs)[k]? = some a →
      ∃ nm ty, a = .fvar k nm ty ∧ WScoped k ty ∧
        ty.looseBVarsBounded 0 = true := by
    intro k a ha
    obtain ⟨mb, hp⟩ := hzipfst' k a ha
    obtain ⟨nm, ty, h1, h2, h3⟩ := hFwf.get k (a, mb) hp
    exact ⟨nm, ty, by simpa using h1, by simpa using h2, h3⟩
  -- the canonical frame
  have hρval : ∀ (k : Nat) (v : V),
      (vsi.take rP ++ ws.drop r.ctorParams)[k]? = some v →
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 (0 + k) = v := by
    intro k v hv
    exact snocFrame_snd_get _ 0 (rho0 V) k v hv
  have hfsP : FvarSpine (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 fvsP (vsi.take rP) := by
    refine FvarSpine_of_open heqO ?_ (by omega) ?_
    · rw [List.length_take, hvsilen]
      omega
    · intro k v hv
      have := hρval k v (by
        rw [List.getElem?_append_left]
        · exact hv
        · have hk : k < rP := by
            rcases Nat.lt_or_ge k rP with hlt | hge
            · exact hlt
            · rw [List.getElem?_eq_none
                (by rw [List.length_take, hvsilen]; omega)] at hv
              exact nomatch hv
          rw [List.length_take, hvsilen]
          omega)
      simpa using this
  have hfsX : FvarSpine (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 xFvs
      (ws.drop r.ctorParams) := by
    refine FvarSpine_of_open hopenX ?_ (by omega) ?_
    · rw [List.length_drop, hwsl]
      omega
    · intro k v hv
      have := hρval (rP + k) v (by
        rw [List.getElem?_append_right
          (by rw [List.length_take, hvsilen]; omega)]
        rw [show rP + k - (vsi.take rP).length = k from by
          rw [List.length_take, hvsilen]; omega]
        exact hv)
      rw [show 0 + (rP + k) = rP + k from by omega] at this
      exact this
  have hentryWf' : ∀ a ∈ fvsP ++ xFvs,
      WScoped (rP + RecRule.nfields r) a ∧
        a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl, hw, hb⟩ := hentryWf k a hk
    have hkN : k < rP + RecRule.nfields r := by
      rcases Nat.lt_or_ge k (rP + RecRule.nfields r) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by omega)] at hk
        exact nomatch hk
    exact ⟨by
      simp only [WScoped]
      exact ⟨hkN, hw⟩, rfl⟩
  have hiaP : InstArgs m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 fvsP (vsi.take rP) :=
    InstArgs.of_fvarSpine hfsP
      (fun a ha => hentryWf' a (List.mem_append.mpr (Or.inl ha)))
  have hiaX : InstArgs m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 xFvs
      (ws.drop r.ctorParams) :=
    InstArgs.of_fvarSpine hfsX
      (fun a ha => hentryWf' a (List.mem_append.mpr (Or.inr ha)))
  -- the constructor's parameter values at the canonical frame
  have hiaCargs : InstArgs m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 cargs
      (ws.take r.ctorParams) := by
    rcases hfireCase with ⟨hfp, -, hce⟩ | ⟨lvls, pins, hfn', -, hce⟩
    · -- plain: the leading prefix variables
      have hwsTake : ws.take r.ctorParams = vsi.take r.ctorParams := by
        obtain ⟨h1, -⟩ := hplainPrem hfp
        rw [h1, List.take_append_of_le_length
          (by rw [hvsilen]; exact Nat.le_trans (hplainLe' hfp) hlemi)]
      rw [hce, hwsTake,
        show vsi.take (RecRule.ctorParams r) =
          (vsi.take rP).take (RecRule.ctorParams r) from by
          rw [List.take_take, Nat.min_eq_left (hplainLe' hfp)]]
      exact InstArgs.take _ hiaP
    · -- nested: the stored pins' values, relocated from the premise's
      -- frame through the universal level/frame bridge
      obtain ⟨hrPmI, hlvl, dP, ρP, spineP, hFvP, hshP, hmapP⟩ :=
        hnestedPrem lvls pins hfn'
      obtain ⟨-, -, hpinsWf, -⟩ := hnestWF lvls pins hfn'
      have hspPlen : spineP.length = rP := by
        have h1 := FvarSpine.length hFvP
        rw [h1, List.length_take, hvsilen]
        omega
      have hiaSpineP : InstArgs m.val env φ dP ρP spineP (vsi.take rP) :=
        InstArgs_of_FvarSpine_sanitized hFvP hshP
      have hpinVal : ∀ (pin : Expr) (v : V), pin ∈ pins →
          interpExpr V m.val env φ dP ρP
            (instSeq spineP (spineP.length - 1)
              (pin.instantiateLevelParams cv.levelParams us)) = some v →
          interpExpr V m.val env (Level.substFn φ
            (ConstantInfo.recInfo cv mI rP
              rules).toConstantVal.levelParams us)
            (rP + RecRule.nfields r)
            (snocFrame (V := V) 0 (rho0 V)
              (vsi.take rP ++ ws.drop r.ctorParams)).2
            (Expr.instSpine fvsP (rP - 1) pin) = some v := by
        intro pin v hpin hv
        obtain ⟨hpF, hpPs, -, hpB⟩ := hpinsWf pin hpin
        rw [Expr.instSpine_eq_instSeq,
          show (rP : Nat) - 1 = fvsP.length - 1 from by rw [hfvsPlen]]
        rw [interp_instSeq_swap₁ (φ := φ) m.val_params
          (ks₂ := cv.levelParams) (us₂ := us) (ps := cv.levelParams)
          hiaP hiaSpineP hpF
          (by rw [hfvsPlen]; exact hpB) hpPs
          (fun p _ => rfl)]
        exact hv
      have hassemble : ∀ (ps' : List Expr) (vs' : List V),
          (∀ p ∈ ps', p ∈ pins) →
          (ps'.map fun pin => instSeq spineP (spineP.length - 1)
            (pin.instantiateLevelParams cv.levelParams us)).mapM
            (interpExpr V m.val env φ dP ρP) = some vs' →
          InstArgs m.val env (Level.substFn φ
            (ConstantInfo.recInfo cv mI rP
              rules).toConstantVal.levelParams us)
            (rP + RecRule.nfields r)
            (snocFrame (V := V) 0 (rho0 V)
              (vsi.take rP ++ ws.drop r.ctorParams)).2
            (ps'.map fun p => Expr.instSpine fvsP (rP - 1) p) vs' := by
        intro ps'
        induction ps' with
        | nil =>
          intro vs' _ hm
          obtain rfl : vs' = [] := by simpa using hm.symm
          trivial
        | cons p0 ps' ihp =>
          intro vs' hmem hm
          rw [List.map_cons, List.mapM_cons] at hm
          cases hv0 : interpExpr V m.val env φ dP ρP
              (instSeq spineP (spineP.length - 1)
                (p0.instantiateLevelParams cv.levelParams us)) with
          | none => rw [hv0] at hm; exact nomatch hm
          | some v0 =>
            rw [hv0] at hm
            cases hvs : (ps'.map fun pin => instSeq spineP
                (spineP.length - 1)
                (pin.instantiateLevelParams cv.levelParams us)).mapM
                (interpExpr V m.val env φ dP ρP) with
            | none => rw [hvs] at hm; exact nomatch hm
            | some vrest =>
              rw [hvs] at hm
              obtain rfl : vs' = v0 :: vrest := by simpa using hm.symm
              obtain ⟨hpF, -, -, hpB⟩ :=
                hpinsWf p0 (hmem p0 List.mem_cons_self)
              refine ⟨⟨?_, ?_, hpinVal p0 v0
                (hmem p0 List.mem_cons_self) hv0⟩,
                ihp vrest (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
                  hvs⟩
              · dsimp only
                rw [Expr.instSpine_eq_instSeq]
                refine instSeq_wscoped _ (WScoped.of_not_hasFvar hpF) ?_
                intro a ha
                exact (hentryWf' a (List.mem_append.mpr (Or.inl ha))).1
              · dsimp only
                rw [Expr.instSpine_eq_instSeq,
                  show (rP : Nat) - 1 = fvsP.length - 1 from by
                    rw [hfvsPlen]]
                refine instSeq_bclosed ?_ ?_
                · intro a ha
                  exact (hentryWf' a (List.mem_append.mpr (Or.inl ha))).2
                · rw [hfvsPlen]
                  exact hpB
      rw [hce]
      exact hassemble pins (ws.take r.ctorParams) (fun p hp => hp) hmapP
  have hiaC2 : InstArgs m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 (cargs ++ xFvs) ws := by
    have h0 := InstArgs.append hiaCargs hiaX
    rwa [List.take_append_drop] at h0
  -- ===== the canonical frame fit =====
  obtain ⟨⟨bsFull, restFull⟩, hstripFull⟩ := Option.isSome_iff_exists.mp har1
  obtain ⟨restPre, hstripPre⟩ := stripPis_prefix rP ((mI + 1) - rP)
    (by rw [show rP + ((mI + 1) - rP) = mI + 1 from by omega]
        exact hstripFull)
  obtain ⟨⟨bsC, cbodyRaw⟩, hstripRaw⟩ := Option.isSome_iff_exists.mp har2
  obtain ⟨-, hRtps, -, -, -, -⟩ := m.wf _ (find?_mem hfc)
  obtain ⟨-, hCtps, -, -, -, -⟩ := m.wf _ (find?_mem hfj)
  -- the consumer's prefix fit
  have hsplitPre : (Expr.app fe ae).getAppArgs.take mI ++ [major] =
      (Expr.app fe ae).getAppArgs.take rP ++
        ((((Expr.app fe ae).getAppArgs.take mI).drop rP) ++ [major]) := by
    conv => lhs; rw [← List.take_append_drop rP
      ((Expr.app fe ae).getAppArgs.take mI)]
    rw [List.take_take, Nat.min_eq_left hlemi, List.append_assoc]
  have hfitIR' : TeleFitI V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us)
      ((Expr.app fe ae).getAppArgs.take rP ++
        ((((Expr.app fe ae).getAppArgs.take mI).drop rP) ++ [major]))
      (vsi ++ [tvv]) restR := by
    rw [← hsplitPre]
    exact hfitIR
  obtain ⟨midPre, hfitPre0⟩ := TeleFitI.take_prefix hfitIR'
  have hpreLen : ((Expr.app fe ae).getAppArgs.take rP).length = rP := by
    rw [List.length_take, hlen]
    omega
  have hfitPre : TeleFitI V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us)
      ((Expr.app fe ae).getAppArgs.take rP) (vsi.take rP) midPre := by
    rw [show vsi.take rP = (vsi ++ [tvv]).take
        ((Expr.app fe ae).getAppArgs.take rP).length from by
      rw [hpreLen, List.take_append_of_le_length (by rw [hvsilen]; omega)]]
    exact hfitPre0
  -- prefix memberships via the level/frame bridge
  have hmemPre := fit_mem_swap₂ (φ := φ) m.val_params
    (ψ := Level.substFn φ (ConstantInfo.recInfo cv mI rP
      rules).toConstantVal.levelParams us)
    (ks₁ := []) (us₁ := []) (ks₂ := cv.levelParams) (us₂ := us)
    (ps := cv.levelParams)
    hRtf hRtb hstripPre hRtps (fun p _ => rfl) hfitPre hiaP hfvsPlen
  -- the prefix domains are the frame annotations
  obtain ⟨-, hdomsPre⟩ := instPisAt_stripPis fvsP hfvsPinst
    (by rw [hfvsPlen]; exact hstripPre)
  -- the composed constructor walk and the field memberships
  have hcomp := instPisAt_append_of cargs hcinst hxFvsInst
  have hspineClen : (cargs ++ xFvs).length =
      RecRule.ctorParams r + RecRule.nfields r := by
    rw [List.length_append, hcargsLen, hxFvsLen]
  have hmemFld : ∀ (j : Nat) (a : Expr) (v : V), xFvs[j]? = some a →
      ws[RecRule.ctorParams r + j]? = some v →
      ∃ A, interpExpr V m.val env (Level.substFn φ
          (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us)
          (rP + RecRule.nfields r)
          (snocFrame (V := V) 0 (rho0 V)
            (vsi.take rP ++ ws.drop r.ctorParams)).2
          (Expr.fvarTypeD a) = some A ∧ v ∈ˢ A := by
    intro j a v ha hv
    have hjlt : j < RecRule.nfields r := by
      rcases Nat.lt_or_ge j (RecRule.nfields r) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by rw [hxFvsLen]; omega)] at ha
        exact nomatch ha
    have hkC : RecRule.ctorParams r + j <
        RecRule.ctorParams r + RecRule.nfields r := by omega
    obtain ⟨b, hbk⟩ : ∃ b, bsC[RecRule.ctorParams r + j]? = some b := by
      have := Expr.stripPis_length _ hstripRaw
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hdomAt : (cdoms0 ++ xFvs.map Expr.fvarTypeD)[RecRule.ctorParams r
        + j]? = some (Expr.fvarTypeD a) := by
      rw [List.getElem?_append_right (by
        rw [show cdoms0.length = cargs.length from
          instPisAt_length _ hcinst, hcargsLen]
        omega)]
      rw [show RecRule.ctorParams r + j - cdoms0.length = j from by
        rw [show cdoms0.length = cargs.length from
          instPisAt_length _ hcinst, hcargsLen]
        omega]
      rw [List.getElem?_map, ha]
      rfl
    rcases hfireCase with ⟨hfp, -, -⟩ | ⟨lvls, pins, hfn', -, -⟩
    · -- plain
      have hcinst' : Expr.instPisAt (cargs ++ xFvs) cvj.type =
          some (cdoms0 ++ xFvs.map Expr.fvarTypeD, crest2) := by
        have h0 := hcomp
        rw [hfp] at h0
        exact h0
      obtain ⟨-, hdomsC⟩ := instPisAt_stripPis _ hcinst'
        (by rw [hspineClen]; exact hstripRaw)
      have hφψC : ∀ p ∈ cvj.levelParams,
          Level.substFn (Level.substFn φ (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us) [] [] p =
          Level.substFn φ cvj.levelParams usj p := by
        intro p hp
        show Level.substFn φ (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us p = _
        exact ((hplainPrem hfp).2 p hp).symm
      have hmemsw := fit_mem_swap₂ (φ := φ) m.val_params
        (ks₁ := []) (us₁ := []) (ks₂ := cvj.levelParams) (us₂ := usj)
        (ps := cvj.levelParams)
        hCtf hCtb hstripRaw hCtps hφψC hfitIC hiaC2 hspineClen
      obtain ⟨A, hAi, hvA⟩ := hmemsw (RecRule.ctorParams r + j) b v hbk hv
      refine ⟨A, ?_, hvA⟩
      have hdc := hdomsC (RecRule.ctorParams r + j) b hbk
      rw [hdomAt] at hdc
      obtain hface := Option.some.inj hdc
      rw [Expr.instantiateLevelParams_nil] at hAi
      rw [show Expr.fvarTypeD a = instSeq
        ((cargs ++ xFvs).take (RecRule.ctorParams r + j))
        (RecRule.ctorParams r + j - 1) b.2.1 from hface]
      exact hAi
    · -- nested
      have hcinst' : Expr.instPisAt (cargs ++ xFvs)
          (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
          some (cdoms0 ++ xFvs.map Expr.fvarTypeD, crest2) := by
        have h0 := hcomp
        rw [hfn'] at h0
        exact h0
      obtain ⟨⟨bsCI, cbodyI⟩, hstripCI⟩ := Option.isSome_iff_exists.mp
        (Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams lvls
          _ (by rw [hstripRaw]; rfl))
      obtain ⟨-, hbsCI⟩ := Expr.stripPis_instantiateLevelParams_eq
        cvj.levelParams lvls _ hstripRaw hstripCI
      obtain ⟨-, hdomsC⟩ := instPisAt_stripPis _ hcinst'
        (by rw [hspineClen]; exact hstripCI)
      obtain ⟨-, hlvl, -⟩ := hnestedPrem lvls pins hfn'
      have hφψC : ∀ p ∈ cvj.levelParams,
          Level.substFn (Level.substFn φ (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us) cvj.levelParams lvls p =
          Level.substFn φ cvj.levelParams usj p :=
        fun p hp => (hlvl p hp).symm
      have hmemsw := fit_mem_swap₂ (φ := φ) m.val_params
        (ks₁ := cvj.levelParams) (us₁ := lvls) (ks₂ := cvj.levelParams)
        (us₂ := usj) (ps := cvj.levelParams)
        hCtf hCtb hstripRaw hCtps hφψC hfitIC hiaC2 hspineClen
      obtain ⟨A, hAi, hvA⟩ := hmemsw (RecRule.ctorParams r + j) b v hbk hv
      refine ⟨A, ?_, hvA⟩
      obtain ⟨bI, hbI⟩ : ∃ bI, bsCI[RecRule.ctorParams r + j]? =
          some bI := by
        have := Expr.stripPis_length _ hstripCI
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hdc := hdomsC (RecRule.ctorParams r + j) bI hbI
      rw [hdomAt] at hdc
      obtain hface := Option.some.inj hdc
      have hdEq : bI.2.1 = b.2.1.instantiateLevelParams cvj.levelParams
          lvls := hbsCI (RecRule.ctorParams r + j) b bI hbk hbI
      rw [show Expr.fvarTypeD a = instSeq
        ((cargs ++ xFvs).take (RecRule.ctorParams r + j))
        (RecRule.ctorParams r + j - 1) bI.2.1 from hface, hdEq]
      exact hAi
  -- the frame fit, assembled positionally
  have hframe : FrameFit m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      0 (rho0 V) fvms (vsi.take rP ++ ws.drop r.ctorParams) := by
    refine FrameFit.of_pointwise (by rw [hflen, hxslen']) ?_ ?_
    · intro k p hp
      obtain ⟨nm, ty, h1, -, -⟩ := hFwf.get k p hp
      exact ⟨nm, ty, p.2, by rw [← h1]⟩
    · intro k nm ty mb x hp hx
      have haC : (fvsP ++ xFvs)[k]? = some (.fvar (0 + k) nm ty) := by
        have := hzipfst k (.fvar (0 + k) nm ty, mb) hp
        exact this
      have hkN : k < rP + RecRule.nfields r := by
        rcases Nat.lt_or_ge k (rP + RecRule.nfields r) with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by rw [hspineLen]; omega)] at haC
          exact nomatch haC
      obtain ⟨nm2, ty2, h1, hwty2, -⟩ := hFwf.get k _ hp
      have hwty : WScoped (0 + k) ty := by
        have h1' : Expr.fvar (0 + k) nm ty = Expr.fvar (0 + k) nm2 ty2 := h1
        injection h1' with e1 e2 e3
        rw [← e3] at hwty2
        exact hwty2
      have hliftAgr : ∀ i, i < 0 + k →
          (snocFrame (V := V) 0 (rho0 V)
            (vsi.take rP ++ ws.drop r.ctorParams)).2 i =
          (snocFrame (V := V) 0 (rho0 V)
            ((vsi.take rP ++ ws.drop r.ctorParams).take k)).2 i := by
        intro i hi
        exact (snocFrame_take_agree _ k 0 (rho0 V) i hi
          (by rw [hxslen']; omega)).symm
      have hlift := interp_lift (cval := m.val) (env := env)
        (φ := Level.substFn φ (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us) hwty
        (rP + RecRule.nfields r) (by omega)
        (snocFrame (V := V) 0 (rho0 V)
          ((vsi.take rP ++ ws.drop r.ctorParams).take k)).2
        (snocFrame (V := V) 0 (rho0 V)
          (vsi.take rP ++ ws.drop r.ctorParams)).2 hliftAgr
      rcases Nat.lt_or_ge k rP with hkP | hkP
      · -- prefix position
        have haP : fvsP[k]? = some (.fvar (0 + k) nm ty) := by
          rw [List.getElem?_append_left (by rw [hfvsPlen]; omega)] at haC
          exact haC
        obtain ⟨b, hbk⟩ : ∃ b, (bsFull.take rP)[k]? = some b := by
          have := Expr.stripPis_length _ hstripFull
          exact ⟨_, List.getElem?_eq_getElem (by
            rw [List.length_take]
            omega)⟩
        have hxv : (vsi.take rP)[k]? = some x := by
          rw [List.getElem?_append_left
            (by rw [List.length_take, hvsilen]; omega)] at hx
          exact hx
        obtain ⟨A, hAi, hvA⟩ := hmemPre k b x hbk hxv
        rw [Expr.instantiateLevelParams_nil] at hAi
        have hdp := hdomsPre k b hbk
        rw [List.getElem?_map, haP] at hdp
        have hdp' : Expr.fvarTypeD (.fvar (0 + k) nm ty) =
            instSeq (fvsP.take k) (k - 1) b.2.1 :=
          Option.some.inj hdp
        have htyD : ty = instSeq (fvsP.take k) (k - 1) b.2.1 := by
          simpa [Expr.fvarTypeD] using hdp'
        refine ⟨A, ?_, hvA⟩
        rw [htyD] at hlift ⊢
        rw [← hlift]
        exact hAi
      · -- field position
        have haX : xFvs[k - rP]? = some (.fvar (0 + k) nm ty) := by
          rw [List.getElem?_append_right (by rw [hfvsPlen]; omega)] at haC
          rw [show k - fvsP.length = k - rP from by rw [hfvsPlen]] at haC
          exact haC
        have hxv : ws[RecRule.ctorParams r + (k - rP)]? = some x := by
          rw [List.getElem?_append_right
            (by rw [List.length_take, hvsilen]; omega)] at hx
          rw [show k - (vsi.take rP).length = k - rP from by
            rw [List.length_take, hvsilen]; omega] at hx
          rw [List.getElem?_drop] at hx
          exact hx
        obtain ⟨A, hAi, hvA⟩ := hmemFld (k - rP) _ x haX hxv
        refine ⟨A, ?_, hvA⟩
        rw [show Expr.fvarTypeD (Expr.fvar (0 + k) nm ty) = ty from rfl]
          at hAi
        rw [← hlift]
        exact hAi
  -- ===== the tower fold =====
  obtain ⟨w, hwI, hfoldEq2, hchainL⟩ := closeLamsAt_fold hframe hFwf
    (hAL : AnnotOk V m.val env _ 0 (rho0 V) (closeLamsAt fvms bL))
    (hLi : interpExpr V m.val env _ 0 (rho0 V) (closeLamsAt fvms bL) =
      some Rv)
  rw [show (snocFrame (V := V) 0 (rho0 V)
      (vsi.take rP ++ ws.drop r.ctorParams)).1 =
      rP + RecRule.nfields r from by
    rw [snocFrame_fst, hxslen']
    omega] at hwI
  -- ===== the fire-mode data, unified =====
  obtain ⟨ks1, us1, hctyEq, hφψC1, husC, husCLen⟩ :
      ∃ (ks1 : List Name) (us1 : List Level),
        (match RecRule.fire r with
          | RecRuleFire.nested lvls _ =>
            cvj.type.instantiateLevelParams cvj.levelParams lvls
          | _ => cvj.type) =
          cvj.type.instantiateLevelParams ks1 us1 ∧
        (∀ p ∈ cvj.levelParams,
          Level.substFn (Level.substFn φ (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us) ks1 us1 p =
          Level.substFn φ cvj.levelParams usj p) ∧
        (∀ p ∈ cvj.levelParams,
          Level.substFn (Level.substFn φ (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us) cvj.levelParams usC p =
          Level.substFn φ cvj.levelParams usj p) ∧
        usC.length = cvj.levelParams.length := by
    rcases hfireCase with ⟨hfp, husCe, -⟩ | ⟨lvls, pins, hfn', husCe, -⟩
    · refine ⟨[], [], by rw [hfp, Expr.instantiateLevelParams_nil], ?_, ?_, ?_⟩
      · intro p hp
        show Level.substFn φ (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us p = _
        exact ((hplainPrem hfp).2 p hp).symm
      · intro p hp
        rw [husCe, show Level.substFn (Level.substFn φ
          (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us) cvj.levelParams
          (cvj.levelParams.map Level.param) p =
          Level.substFn φ (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us p from
          Level.substFn_map_param]
        exact ((hplainPrem hfp).2 p hp).symm
      · rw [husCe]
        simp
    · obtain ⟨-, hlvl, -⟩ := hnestedPrem lvls pins hfn'
      have hlev' : Level.isEquivList usj (lvls.map
          (Level.subst cv.levelParams us)) = some true := by
        have h0 := hlev
        simp only [recFireComparands, hfn'] at h0
        exact h0
      have hlvlLen : lvls.length = cvj.levelParams.length := by
        have h1 := Level.isEquivList_length hlev'
        rw [List.length_map] at h1
        omega
      refine ⟨cvj.levelParams, lvls, by rw [hfn'], fun p hp =>
        (hlvl p hp).symm, ?_, by rw [husCe]; exact hlvlLen⟩
      intro p hp
      rw [husCe]
      exact (hlvl p hp).symm
  -- ===== the canonical index tuple's values =====
  have hcinstU : Expr.instPisAt (cargs ++ xFvs)
      (cvj.type.instantiateLevelParams ks1 us1) =
      some (cdoms0 ++ xFvs.map Expr.fvarTypeD, crest2) := by
    rw [← hctyEq]
    exact hcomp
  obtain ⟨⟨bsU, cbodyU⟩, hstripU⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome ks1 us1
      (RecRule.ctorParams r + RecRule.nfields r) (by rw [hstripRaw]; rfl))
  obtain ⟨hcbodyUeq, -⟩ := Expr.stripPis_instantiateLevelParams_eq ks1 us1
    _ hstripRaw hstripU
  obtain ⟨hcrest2Eq, -⟩ := instPisAt_stripPis _ hcinstU
    (by rw [hspineClen]; exact hstripU)
  obtain ⟨hcbodyJeq, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams usj _ hstripRaw hstrip
  -- the raw constructor result's head constant
  obtain ⟨usr0, hrawFn, -⟩ :
      ∃ usr0, cbodyRaw.getAppFn = .const cr usr0 ∧
        usr = usr0.map (Level.subst cvj.levelParams usj) := by
    have h0 := hrfn
    rw [hcbodyJeq, getAppFn_instantiateLevelParams] at h0
    exact instantiateLevelParams_eq_const h0
  have hrawSpine : cbodyRaw = Expr.mkAppN (.const cr usr0)
      cbodyRaw.getAppArgs := by
    have := (Expr.mkAppN_getApp cbodyRaw).symm
    rw [hrawFn] at this
    exact this
  have hcbodyRawF : cbodyRaw.hasFvar = false :=
    stripPis_body_hasFvar _ hstripRaw hCtf
  have hcbodyRawB : cbodyRaw.looseBVarsBounded
      (RecRule.ctorParams r + RecRule.nfields r) = true := by
    have := stripPis_body_bounded _ hstripRaw hCtb
    simpa using this
  have hcbodyRawPs : cbodyRaw.allLevelParamsDefined cvj.levelParams =
      true :=
    allLevelParamsDefined_stripPis_body _ hstripRaw hCtps
  -- decompose the two residuals' argument spines over the raw arguments
  have hcrest2Args : crest2.getAppArgs =
      cbodyRaw.getAppArgs.map (fun x =>
        instSeq (cargs ++ xFvs) (RecRule.ctorParams r + RecRule.nfields r
          - 1) (x.instantiateLevelParams ks1 us1)) := by
    rw [hcrest2Eq, hcbodyUeq, hrawSpine, instantiateLevelParams_mkAppN]
    rw [show (Expr.const cr usr0).instantiateLevelParams ks1 us1 =
      Expr.const cr (usr0.map (Level.subst ks1 us1)) from rfl]
    rw [show (cargs ++ xFvs).length - 1 =
      RecRule.ctorParams r + RecRule.nfields r - 1 from by
      rw [hspineClen]]
    rw [instSeq_mkAppN, instSeq_eq_self _ _
      (by simp [Expr.looseBVarsBounded])]
    simp [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.map_map,
      Function.comp]
  have hrArgsRaw : restC.getAppArgs =
      cbodyRaw.getAppArgs.map (fun x =>
        instSeq major.getAppArgs (RecRule.ctorParams r + RecRule.nfields r
          - 1) (x.instantiateLevelParams cvj.levelParams usj)) := by
    rw [hrArgs, hcbodyJeq, hrawSpine, instantiateLevelParams_mkAppN]
    rw [show (Expr.const cr usr0).instantiateLevelParams cvj.levelParams
      usj = Expr.const cr (usr0.map (Level.subst cvj.levelParams usj))
      from rfl]
    simp [Expr.getAppArgs_mkAppN, Expr.getAppArgs, List.map_map,
      Function.comp]
  have hiaMargs : InstArgs m.val env φ d ρ major.getAppArgs ws :=
    TeleFitI.toInstArgs hfitIC
  have hidxVals : (crest2.getAppArgs.drop (RecRule.ctorParams r)).mapM
      (interpExpr V m.val env (Level.substFn φ
        (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us)
        (rP + RecRule.nfields r)
        (snocFrame (V := V) 0 (rho0 V)
          (vsi.take rP ++ ws.drop r.ctorParams)).2) =
      some (vsi.drop rP) := by
    by_cases hrnil : restC.getAppArgs = []
    · have hcnil : cbodyRaw.getAppArgs = [] := by
        rw [hrArgsRaw] at hrnil
        exact List.map_eq_nil_iff.mp hrnil
      have hni : mI ≤ rP := by
        rw [hrnil] at hlenieq
        simp only [List.drop_nil, List.length_nil, List.length_drop,
          htakelen] at hlenieq
        omega
      have hvnil : vsi.drop rP = [] :=
        List.drop_eq_nil_of_le (by rw [hvsilen]; omega)
      rw [hcrest2Args, hcnil, hvnil]
      simp
    · have hrspine : restC = Expr.mkAppN (.const cr usr)
          restC.getAppArgs := by
        have := (Expr.mkAppN_getApp restC).symm
        rw [show restC.getAppFn = .const cr usr from by
          rw [hrestCeq, hcspine, instSeq_mkAppN, instSeq_eq_self _ _
            (by simp [Expr.looseBVarsBounded]), Expr.getAppFn_mkAppN]
          rfl]
          at this
        exact this
      have hrA' : AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const cr usr) restC.getAppArgs) := hrspine ▸ hrA
      obtain ⟨-, hrxsA, vr0, vsRes, hir0, hispRes, -, -⟩ :=
        annotOk_spine_inv _ _ hrnil hrA'
      have hvals : vsRes.drop r.ctorParams = vsi.drop rP := by
        refine defEqList_values ihd _ _ _ _ hieq ?_ ?_
          (InterpSpine.drop r.ctorParams hispRes) ?_
        · intro x hx
          have hxm := List.mem_of_mem_drop hx
          exact ⟨hrw.getAppArgs _ hxm,
            looseBVarsBounded_getAppArgs hrb _ hxm,
            fun l hl => hrL l (fvarLeaves_getAppArgs hxm l hl),
            FvarsOk.of_subset
              (fun l hl => fvarLeaves_getAppArgs hxm l hl) hrO,
            hrxsA _ hxm⟩
        · intro x hx
          have hxm := List.mem_of_mem_take (List.mem_of_mem_drop hx)
          exact ⟨hargsW _ hxm, hargsB _ hxm, hargsL _ hxm, hargsO _ hxm,
            hxsA _ hxm⟩
        · exact InterpSpine.drop rP hspi
      have hspineM : InterpSpine m.val env φ d ρ
          ((cbodyRaw.getAppArgs.drop (RecRule.ctorParams r)).map (fun x =>
            instSeq major.getAppArgs
              (RecRule.ctorParams r + RecRule.nfields r - 1)
              (x.instantiateLevelParams cvj.levelParams usj)))
          (vsRes.drop r.ctorParams) := by
        have h0 := InterpSpine.drop r.ctorParams hispRes
        rw [hrArgsRaw, ← List.map_drop] at h0
        exact h0
      have hconv : ∀ (l : List Expr) (vs0 : List V),
          (∀ x ∈ l, x ∈ cbodyRaw.getAppArgs) →
          InterpSpine m.val env φ d ρ
            (l.map (fun x => instSeq major.getAppArgs
              (RecRule.ctorParams r + RecRule.nfields r - 1)
              (x.instantiateLevelParams cvj.levelParams usj))) vs0 →
          InterpSpine m.val env (Level.substFn φ
            (ConstantInfo.recInfo cv mI rP
              rules).toConstantVal.levelParams us)
            (rP + RecRule.nfields r)
            (snocFrame (V := V) 0 (rho0 V)
              (vsi.take rP ++ ws.drop r.ctorParams)).2
            (l.map (fun x => instSeq (cargs ++ xFvs)
              (RecRule.ctorParams r + RecRule.nfields r - 1)
              (x.instantiateLevelParams ks1 us1))) vs0 := by
        intro l
        induction l with
        | nil =>
          intro vs0 _ hs
          match vs0, hs with
          | [], _ => trivial
        | cons x l ihl =>
          intro vs0 hmem hs
          match vs0, hs with
          | v :: vs0, ⟨hix, hrest⟩ =>
            refine ⟨?_, ihl vs0
              (fun y hy => hmem y (List.mem_cons_of_mem _ hy)) hrest⟩
            have hxmem := hmem x List.mem_cons_self
            have hxcl : x.hasFvar = false :=
              hasFvar_getAppArgs hcbodyRawF _ hxmem
            have hxb : x.looseBVarsBounded
                (RecRule.ctorParams r + RecRule.nfields r) = true :=
              looseBVarsBounded_getAppArgs hcbodyRawB _ hxmem
            have hxps : x.allLevelParamsDefined cvj.levelParams = true :=
              allLevelParamsDefined_getAppArgs hcbodyRawPs _ hxmem
            have hswap := interp_instSeq_swap₂ (φ := φ) m.val_params
              (ks₁ := ks1) (us₁ := us1) (ks₂ := cvj.levelParams)
              (us₂ := usj) (ps := cvj.levelParams)
              hiaC2 hiaMargs hxcl
              (by rw [hspineClen]; exact hxb) hxps hφψC1
            rw [show (cargs ++ xFvs).length - 1 =
              RecRule.ctorParams r + RecRule.nfields r - 1 from by
              rw [hspineClen]] at hswap
            rw [show major.getAppArgs.length - 1 =
              RecRule.ctorParams r + RecRule.nfields r - 1 from by
              rw [hml]] at hswap
            dsimp only
            rw [hswap]
            exact hix
      have hspineC2 := hconv
        (cbodyRaw.getAppArgs.drop (RecRule.ctorParams r))
        (vsRes.drop r.ctorParams)
        (fun x hx => List.mem_of_mem_drop hx) hspineM
      rw [hcrest2Args, ← List.map_drop, ← hvals]
      exact InterpSpine.mapM_eq hspineC2
  -- ===== the body's value at the extension frame =====
  have hheadI : interpExpr V m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2
      (.const c (cv.levelParams.map .param)) =
      some (m.val c (Level.substFn φ (ConstantInfo.recInfo cv mI rP
        rules).toConstantVal.levelParams us)) := by
    simp only [interpExpr, hfc]
    rw [if_pos (by simp [ConstantInfo.toConstantVal])]
    rw [show Level.substFn (Level.substFn φ
        (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us)
        (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams
        (cv.levelParams.map Level.param) =
        Level.substFn φ (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us from
      funext fun p => Level.substFn_map_param]
  have hctorHeadI : interpExpr V m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2
      (.const (RecRule.ctor r) usC) =
      some (m.val (RecRule.ctor r)
        (Level.substFn φ (ConstantInfo.ctorInfo cvj cnP
          cnF).toConstantVal.levelParams usj)) := by
    simp only [interpExpr, hfj]
    rw [if_pos (by exact husCLen)]
    congr 1
    exact m.val_params _ _ hfj _ _ husC
  have hctorI : interpExpr V m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2
      (Expr.mkAppN (.const (RecRule.ctor r) usC) (cargs ++ xFvs)) =
      some tvv := by
    rw [interp_mkAppN _ _ hctorHeadI (InstArgs.toInterpSpine hiaC2)]
    rw [htveq]
  have hbodyI : interpExpr V m.val env (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP rules).toConstantVal.levelParams us)
      (rP + RecRule.nfields r)
      (snocFrame (V := V) 0 (rho0 V)
        (vsi.take rP ++ ws.drop r.ctorParams)).2 bL =
      some (SpineFold V (m.val c (Level.substFn φ
        (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us)) (vsi ++ [tvv])) := by
    rw [hbLEq]
    have hsingle : InterpSpine m.val env (Level.substFn φ
        (ConstantInfo.recInfo cv mI rP
          rules).toConstantVal.levelParams us)
        (rP + RecRule.nfields r)
        (snocFrame (V := V) 0 (rho0 V)
          (vsi.take rP ++ ws.drop r.ctorParams)).2
        [Expr.mkAppN (.const (RecRule.ctor r) usC) (cargs ++ xFvs)]
        [tvv] := ⟨hctorI, trivial⟩
    rw [interp_mkAppN _ _ hheadI
      (InterpSpine.append (InterpSpine.append
        (InstArgs.toInterpSpine hiaP) (InterpSpine.of_mapM hidxVals))
        hsingle)]
    rw [List.take_append_drop]
  have hweq : w = SpineFold V (m.val c (Level.substFn φ
      (ConstantInfo.recInfo cv mI rP
        rules).toConstantVal.levelParams us)) (vsi ++ [tvv]) := by
    rw [hwI] at hbodyI
    exact Option.some.inj hbodyI
  -- ===== the reduct =====
  have hRinst : interpExpr V m.val env φ d ρ
      (r.rhs.instantiateLevelParams cv.levelParams us) = some Rv := by
    rw [interp_closed_invariant hclInst d ρ]
    show interpClosed V m.val env _ _ = _
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    exact hRi
  have hArhs : AnnotOk V m.val env φ d ρ
      (r.rhs.instantiateLevelParams cv.levelParams us) := by
    have h1 := AnnotOk.instLevels (ks := cv.levelParams) (vs := us)
      m.val_params r.rhs 0 (rho0 V)
      (hrhsA (Level.substFn φ cv.levelParams us))
    exact AnnotOk.closed_invariant hclInst d ρ h1
  have htake : (Expr.app fe ae).getAppArgs.take rP =
      ((Expr.app fe ae).getAppArgs.take mI).take
        rP := by
    rw [List.take_take]
    congr 1
    omega
  have hspRed : InterpSpine m.val env φ d ρ
      ((Expr.app fe ae).getAppArgs.take rP ++
        major.getAppArgs.drop r.ctorParams)
      (vsi.take rP ++ ws.drop r.ctorParams) := by
    refine InterpSpine.append ?_ (InterpSpine.drop r.ctorParams hmsp)
    rw [htake]
    exact InterpSpine.take _ hspi
  have hxsAR : ∀ x ∈ ((Expr.app fe ae).getAppArgs.take rP ++
      major.getAppArgs.drop r.ctorParams), AnnotOk V m.val env φ d ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxsA _ (List.mem_of_mem_take hx)
    · exact hmxsA _ (List.mem_of_mem_drop hx)
  obtain ⟨hAe, hie⟩ := annotOk_spine _ _ hArhs hRinst hxsAR hspRed hchainL
  rw [← heout] at hAe hie
  refine ⟨?_, hAe⟩
  have hifold' : interpExpr V m.val env φ d ρ (Expr.app fe ae) =
      some (SpineFold V vf0 (vsi ++ [tvv])) := by
    rw [← hspine] at hifold
    exact hifold
  have hfinal : SpineFold V Rv
      (vsi.take rP ++ ws.drop r.ctorParams) =
      SpineFold V vf0 (vsi ++ [tvv]) := by
    rw [hfoldEq2, hweq, hv0]
  rw [hie, hifold', hfinal]




end Claims

end Setlec
