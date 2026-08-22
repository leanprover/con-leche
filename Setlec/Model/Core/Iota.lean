import Setlec.Model.Core.MajorToCtor
import Setlec.Model.Core.NestedFire

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
      (by rw [hml]; exact har2)
      hmcerts hcvtW hcvtB hcvtL hcvtO hcvtA
  obtain ⟨-, -, -, -, -, hrules⟩ := m.wf _ (find?_mem hfc)
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
  obtain ⟨hdR, hagrR, argsRF, hfitRF, hfvRF⟩ :=
    TeleFit.toTeleFitI hfitR hRw
  have hfitIC' := TeleFitI.lift hfitIC hCw hdR hagrR
  obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC'
    (hCw.mono hdR) (by
    rw [show major.getAppArgs.length = r.ctorParams + r.nfields from hml]
    exact stripPis_instantiateLevelParams_isSome _ _ _ har2)
  -- the rule's fold facts
  obtain ⟨hrhsA, hlemi', hfolds⟩ := m.rec_rules c cv mI rP rules hfc r
    (List.mem_of_find?_eq_some hrule)
  have hlemi : rP ≤ mI := hlemi' hplain
  have hchain' : ChainSlots V (m.val c
      (Level.substFn φ (ConstantInfo.recInfo cv mI rP
        rules).toConstantVal.levelParams us)) (vsi ++ [tvv]) := by
    rw [hv0]
    exact hchain
  have hvsilen : vsi.length = mI := by
    have := InterpSpine.length hspi
    rw [this, List.length_take]
    rw [hxeq] at hlen
    simp at hlen
    omega
  -- the canonical-index certificate: the kernel's residual is the
  -- constructor walk's; its trailing slots are the canonical index
  -- expressions, whose values (by the index `defEqList` check) are the
  -- recursor's index-argument values — transported onto the opened
  -- (fvar-instantiated) residual `restC'` by the value-congruence of
  -- instantiation sequences
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
  -- frame bookkeeping
  have hdC : d ≤ dC := Nat.le_trans hdR (TeleFit.toTeleFitI hfitC
    (WScoped.of_not_hasFvar hChf)).1
  obtain ⟨hdRC, hagrRC, argsCF, hfitCF, hfvCF⟩ :=
    TeleFit.toTeleFitI hfitC (WScoped.of_not_hasFvar hChf)
  have hagrC : ∀ i, i < d → ρC i = ρ i := by
    intro i hi
    rw [hagrRC i (by omega), hagrR i hi]
  -- both residuals are instantiation sequences of the constructor's
  -- stripped result
  have hlenCF : argsCF.length = r.ctorParams + r.nfields := by
    have h1 := TeleFitI.vs_length hfitCF
    rw [hwslen] at h1
    omega
  obtain ⟨mid, hmid, bs', body', hstripMid, hbodyMid, -⟩ :=
    telescopeInst_stripPis (r.ctorParams + r.nfields) major.getAppArgs 0 hml
      (by simpa using hstrip)
  rw [TeleFitI.rest_eq hfitIC] at hmid
  obtain rfl : restC = mid := Option.some.inj hmid
  have hrestCeq : restC = instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) cbody := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstripMid
    rw [hstripMid.2, hbodyMid]
    simp
  obtain ⟨midF, hmidF, bsF', bodyF', hstripF, hbodyF, -⟩ :=
    telescopeInst_stripPis (r.ctorParams + r.nfields) argsCF 0 hlenCF
      (by simpa using hstrip)
  rw [TeleFitI.rest_eq hfitCF] at hmidF
  obtain rfl : restC' = midF := Option.some.inj hmidF
  have hrestC'eq : restC' = instSeq argsCF (r.ctorParams + r.nfields - 1) cbody := by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstripF
    rw [hstripF.2, hbodyF]
    simp
  -- the stripped result's own well-formedness and constant head
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
  have hinstF : instSeq argsCF (r.ctorParams + r.nfields - 1) cbody =
      Expr.mkAppN (.const cr usr)
        (cbody.getAppArgs.map (instSeq argsCF (r.ctorParams + r.nfields - 1) ·)) := by
    conv => lhs; rw [hcspine]
    rw [instSeq_mkAppN, instSeq_eq_self _ _ (by simp [Expr.looseBVarsBounded])]
  have hrArgs : restC.getAppArgs =
      cbody.getAppArgs.map (instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) ·) := by
    rw [hrestCeq, hinstM, Expr.getAppArgs_mkAppN]
    simp [Expr.getAppArgs]
  have hrArgsF : restC'.getAppArgs =
      cbody.getAppArgs.map (instSeq argsCF (r.ctorParams + r.nfields - 1) ·) := by
    rw [hrestC'eq, hinstF, Expr.getAppArgs_mkAppN]
    simp [Expr.getAppArgs]
  -- argument spines with the constructor values, at the final frame
  have hInstF : InstArgs m.val env φ dC ρC argsCF ws :=
    TeleFitI.toInstArgs hfitCF
  have hInstM : InstArgs m.val env φ dC ρC major.getAppArgs ws :=
    InstArgs.lift (TeleFitI.toInstArgs hfitIC) hdC hagrC
  have hmapM : (restC'.getAppArgs.drop r.ctorParams).mapM
      (interpExpr V m.val env φ dC ρC) = some (vsi.drop rP) := by
    by_cases hrnil : restC.getAppArgs = []
    · have hcnil : cbody.getAppArgs = [] := by
        rw [hrArgs] at hrnil
        exact List.map_eq_nil_iff.mp hrnil
      have hni : mI ≤ rP := by
        rw [hrnil] at hlenieq
        simp only [List.drop_nil, List.length_nil, List.length_drop,
          htakelen] at hlenieq
        omega
      have hvnil : vsi.drop rP = [] :=
        List.drop_eq_nil_of_le (by rw [hvsilen]; omega)
      rw [hrArgsF, hcnil, hvnil]
      simp
    · have hrspine : restC = Expr.mkAppN (.const cr usr)
          restC.getAppArgs := by
        rw [hrArgs]
        exact hrestCeq.trans hinstM
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
      -- convert the dropped spine to the fvar-instantiated exprs at the
      -- final frame
      have hspineM : InterpSpine m.val env φ d ρ
          ((cbody.getAppArgs.drop r.ctorParams).map
            (instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) ·))
          (vsRes.drop r.ctorParams) := by
        have := InterpSpine.drop r.ctorParams hispRes
        rw [hrArgs, ← List.map_drop] at this
        exact this
      have hconv : ∀ (l : List Expr) (vs0 : List V),
          (∀ x ∈ l, x ∈ cbody.getAppArgs) →
          InterpSpine m.val env φ d ρ
            (l.map (instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) ·)) vs0 →
          InterpSpine m.val env φ dC ρC
            (l.map (instSeq argsCF (r.ctorParams + r.nfields - 1) ·)) vs0 := by
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
            have hxw : WScoped d (instSeq major.getAppArgs
                (r.ctorParams + r.nfields - 1) x) := by
              have : instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) x ∈
                  restC.getAppArgs := by
                rw [hrArgs]
                exact List.mem_map.mpr ⟨x, hxmem, rfl⟩
              exact hrw.getAppArgs _ this
            have hxb : x.looseBVarsBounded (r.ctorParams + r.nfields) = true :=
              looseBVarsBounded_getAppArgs hcbodyB _ hxmem
            have hxfb : Expr.fvarsBelow dC x :=
              (WScoped.of_not_hasFvar
                (hasFvar_getAppArgs hcbodyF _ hxmem)).fvarsBelow
            have hlift : interpExpr V m.val env φ dC ρC
                (instSeq major.getAppArgs (r.ctorParams + r.nfields - 1) x) = some v := by
              rw [interp_lift hxw dC hdC ρ ρC hagrC]
              exact hix
            have hcongr := interp_instSeq_congr hInstF hInstM hxfb
              (by rw [hlenCF]; exact hxb)
            rw [show argsCF.length - 1 = r.ctorParams + r.nfields - 1 from by
                rw [hlenCF]] at hcongr
            rw [show major.getAppArgs.length - 1 = r.ctorParams + r.nfields - 1 from by
                rw [hml]] at hcongr
            rw [hcongr]
            exact hlift
      have hspineF := hconv (cbody.getAppArgs.drop r.ctorParams) (vsRes.drop r.ctorParams)
        (fun x hx => List.mem_of_mem_drop hx) hspineM
      rw [hrArgsF, ← List.map_drop, ← hvals]
      exact InterpSpine.mapM_eq hspineF
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
    have hpeq' : defEqListP env fuel d
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
      mI = rP ∧
      (∀ p ∈ cvj.levelParams,
        Level.substFn φ
          (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams
          usj p =
        Level.substFn (Level.substFn φ
          (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.levelParams us)
          cvj.levelParams lvls p) ∧
      ∃ (dP : Nat) (ρP : Nat → V) (spineP : List Expr),
        FvarSpine dP ρP spineP vsi ∧
        (∀ a ∈ spineP, ∃ i nm, a = Expr.fvar i nm (.sort .zero)) ∧
        (pins.map fun pin => Expr.instSeq spineP (spineP.length - 1)
          (pin.instantiateLevelParams cv.levelParams us)).mapM
          (interpExpr V m.val env φ dP ρP) =
          some (ws.take r.ctorParams) :=
    nested_fire_premise ihd hnestWF hpeq hlev husjlen hml hvsilen har1
      htakelen hargsW hargsB hargsL hargsO hmajW hmajB hmajL hmajO
      hmxsA hmsp hspi hRw hRb hRA hRhf hfitIR hdR hagrR hfitRF hfvRF
  obtain ⟨R, hRi, hfoldEq, hRchain⟩ := hfolds cvj cnP cnF hfj _ _
    vsi ws tvv hvsilen hwslen hchain' hmchain htveq hplainPrem hplain
    ⟨φ, us, usj, d, ρ, dR, ρR, restR', dC, ρC, restC', rfl, rfl,
      hfitR, hfitC, hmapM, hnestedPrem⟩
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
  have htake : (Expr.app fe ae).getAppArgs.take rP =
      ((Expr.app fe ae).getAppArgs.take mI).take
        rP := by
    rw [List.take_take]
    congr 1
    omega
  have hspR : InterpSpine m.val env φ d ρ
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
