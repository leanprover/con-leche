module

public import ConLeche.Model.Inductives.TargetFlat
public import ConLeche.Model.Inductives.TargetCallCore
public import ConLeche.Model.Inductives.TargetClass
import ConLeche.Model.Inductives.TargetClassFrame
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Inductives.SumKit
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Semantics.Kit
import ConLeche.Model.Capstone
import ConLeche.Verify.EnvBound
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.InstList

public section

/-!
# A call around a flat home's cycle lands at the stage (PRIMREC, lane FLATHOME)

`tgtCall_flatFit`: at an OUTSIDE class's rule whose fields fit the
constructor's hole reading at a STAGE `Y` (a sub-tuple of the home's
tuple space), a call the check typed at the home's holes
(`targetIntraCallOk`, `TargetIntraCallRun`) has its target in `Y` at the
callee's component, at the call's index readings.  Assembled from the
generic hole call (`holeCall_gen`, at the valuation holding the stage's
hole values) and the stage fit (`stage_fieldMem`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor TargetIh TargetFamily)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Land

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}

set_option maxHeartbeats 8000000 in
/-- **A call around a flat home's cycle lands at the stage** (see the
module docstring). -/
theorem tgtCall_flatFit (hμ : μ.verifiedChecks = true) (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {rc : ConLeche.RecShape} {M : TargetMajor} {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape out) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hdsOk : TgtDsOk envC rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound envC (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envC r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape out).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape out).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape out).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape out).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound envC ((tgtFam pp.toBlockShape out).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape out) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs) = tgtAbs μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)
    {xs fs : List V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ) Δ
      (Q.fvsPref ++ Q.fvsF).reverse)
    (hxl : xs.length = rc.rP) (hfsl : fs.length = cA.2)
    -- the caller's class: an outside one, its recorded block and constructor
    (hMo : M.member = none) {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) (hhome : M.home = D.names)
    (hjD : j < D.nctors mm)
    (hfc : envC.find? (D.ctorName mm j) = some (.ctorInfo cA.1 M.ds.length cA.2))
    (hlps : ∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = cvI.levelParams)
    (hul : M.lvls.length = cvI.levelParams.length)
    (hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false)
    {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mpC.base2.acval envC ψ rc.rP M.ds dsa)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams M.lvls)).length = M.ds.length)
    (hsat : Sat V (D.params (Level.substFn ψ cvI.levelParams M.lvls)).reverse
      (keyFrame dsa rc.rP (consList xs ρ)))
    -- the stage
    {Y : Nat → V}
    (hY : InTupleSpace (D.w (Level.substFn ψ cvI.levelParams M.lvls)) D.N
      (D.idx (Level.substFn ψ cvI.levelParams M.lvls) (keyFrame dsa rc.rP (consList xs ρ))) Y)
    (hfit : SpineFit (D.frame (Level.substFn ψ cvI.levelParams M.lvls)
        (keyFrame dsa rc.rP (consList xs ρ)) Y)
      (D.fields (Level.substFn ψ cvI.levelParams M.lvls) mm j) fs)
    -- the call: one around the cycle
    {q : Nat}
    (hq : q < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    {rk : List Nat} (hrk : (tgtFam pp.toBlockShape out).ranks = some rk)
    (hrank : rk.getD ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD
        q default).callee 0 = rk.getD ((ConLeche.nameIdxOf? (tgtFam pp.toBlockShape out).recNames
        r0.1.name).getD 0) 0)
    (hidsLen : (D.ids (D.names.idxOf (tgtMajor out
        ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
          default).callee).ind) (Level.substFn ψ cvI.levelParams M.lvls)).length
      = ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
          default).idx.length)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
        c j q).map (·.2.2)) bs) :
    SpineFit (keyFrame dsa rc.rP (consList xs ρ))
      (D.ids (D.names.idxOf (tgtMajor out
        ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
          default).callee).ind) (Level.substFn ψ cvI.levelParams M.lvls))
      ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
        ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
          ψ c j q)
      ∈ˢ app (Y (D.names.idxOf (tgtMajor out
          ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
            default).callee).ind))
        (tupW (D.u (D.names.idxOf (tgtMajor out
          ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
            default).callee).ind) (Level.substFn ψ cvI.levelParams M.lvls))
          ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ))))) := by
  -- the entry and its runs
  have hIhL : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = Q.ihs.toList := by rw [tgtIhL, ← hAbs]
  generalize hih : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
    default = ih at *
  have hihMem : ih ∈ Q.ihs.toList := by rw [← hih, ← hIhL]; exact ConLeche.getD_mem hq
  have hidsLen2 := hidsLen
  obtain ⟨I⟩ := ConLeche.targetIntraCallOk_run
    (ConLeche.targetIntraCallsOk_each Q.hintra ih hihMem) hrk hrank
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hfi : ih.field < cA.2 := tgtIh_field_lt Q hihMem
  have hscope := targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hher hcbF hformerF
    (fun c' => (hRT3 c').1) hihMem
  have htL := hscope.2.2.2.2.2
  have hidxL := tgtIh_idxLeaves Q hle hbf hFr hher hihMem
  have hframeL : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := frame_leaves_mem hFr hher
  -- the callee's major and its hole in the caller's home
  have hmaj' : (tgtFam pp.toBlockShape out).majors.getD ih.callee default
      = tgtMajor out ih.callee := by
    simp only [tgtFam, tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases out[ih.callee]? <;> rfl
  have hhm := I.hhome
  rw [hmaj'] at hhm
  generalize hM' : tgtMajor out ih.callee = M' at *
  generalize hgrp : ConLeche.targetHomeGrp (mkFEnv envC) M = grp at I
  have hgn : grp.map (·.1) = D.names := by
    rw [← hgrp]; simp [ConLeche.targetHomeGrp, List.map_map, Function.comp_def, hhome]
  have hgl : grp.length = D.k := by
    rw [← hcl.hkN, ← hgn, List.length_map]
  have hmemH : M'.ind ∈ D.names := by rw [← hhome]; exact List.contains_iff_mem.mp hhm
  generalize ht : M.home.idxOf M'.ind = t at I
  have htD : D.names.idxOf M'.ind = t := by rw [← ht, hhome]
  have htk : t < D.k := by rw [← htD, ← hcl.hkN]; exact List.idxOf_lt_length_iff.mpr hmemH
  -- the home's group: its entries, their hole types
  have hgget : ∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
      grp.getD mm' default = (D.member mm', cv.type.instantiateLevelParams cv.levelParams M.lvls) := by
    intro mm' hmm'
    obtain ⟨cv, caps, hf, -⟩ := hlps mm' hmm'
    refine ⟨cv, caps, hf, ?_⟩
    have hmn : M.home.getD mm' default = D.member mm' := by rw [hhome]; rfl
    rw [← hgrp]
    simp only [ConLeche.targetHomeGrp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by rw [hhome, hcl.hkN]; exact hmm')]
    simp only [Option.map_some, Option.getD_some]
    have hmn' : M.home[mm']'(by rw [hhome, hcl.hkN]; exact hmm') = D.member mm' := by
      rw [← hmn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
    rw [hmn', ConLeche.mkFEnv_find?, hf]
  have hgT : GrpTy envC D M.lvls grp := by
    refine ⟨by rw [hgn]; exact hcl.hnN, fun p hp => ?_⟩
    obtain ⟨mm', hmm', hget⟩ := List.getElem_of_mem hp
    have hmm'k : mm' < D.k := by rw [← hgl]; exact hmm'
    obtain ⟨cv, caps, hf, hg⟩ := hgget mm' hmm'k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm', Option.getD_some, hget] at hg
    exact ⟨mm', hmm'k, by rw [hg], cv, caps, hf, by rw [hg]⟩
  -- the field's home-abstracted domain
  obtain ⟨doms, hdoms⟩ : ∃ doms, ConLeche.targetPiDomsWith Q.fvsF I.crestH = some doms := by
    cases hd : ConLeche.targetPiDomsWith Q.fvsF I.crestH with
    | none =>
      exfalso
      have h0 := I.hfld
      rw [hd] at h0
      exact inferTypeCore_bvar_absurd' h0
    | some doms => exact ⟨doms, rfl⟩
  have hfldE : ((ConLeche.targetPiDomsWith Q.fvsF I.crestH).getD []).getD ih.field default
      = doms.getD ih.field default := by rw [hdoms]; rfl
  -- the frame's fields, as variables below the holes
  have hfvs : ∀ x ∈ Q.fvsF, ∃ j' ty, x = .fvar j' ty ∧ j' < rc.rP + cA.2 ∧ Expr.WScoped j' ty := by
    intro x hx
    obtain ⟨j', ty, rfl⟩ := hFr.mem_fvar (List.mem_reverse.mpr (List.mem_append_right _ hx))
    have hw := hFr.2.2 _ (List.mem_reverse.mpr (List.mem_append_right _ hx))
    simp only [Expr.WScoped] at hw
    exact ⟨j', ty, rfl, hw.1, hw.2⟩
  have hlenS : (xs ++ fs).length = rc.rP + cA.2 := by rw [List.length_append, hxl, hfsl]
  have hvals : ∀ l, l < cA.2 → interp V (consList (xs ++ fs) ρ)
      ((denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2) (Q.fvsF.getD l default)).getD default)
        = fs.getD l pt := by
    intro l hl
    have hlt : rc.rP + l < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + l) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    have hget : Q.fvsF.getD l default = Expr.fvar (rc.rP + l) ty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [List.getElem_append_right (by omega)] at hty
      simpa [hlp] using hty
    rw [hget, denoteMeta_fvar, Option.getD_some, interp_bvar,
      consList_getD_of_lt _ _ _ (by omega), hlenS,
      show rc.rP + cA.2 - 1 - (rc.rP + cA.2 - 1 - (rc.rP + l)) = rc.rP + l by omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hxl,
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  -- the key frame, past the fields
  have hds' : ∀ x ∈ M.ds, Expr.WScoped (rc.rP + cA.2) x ∧ x.looseBVarsBounded 0 = true :=
    fun x hx => ⟨(hdsOk x hx).1.mono (by omega), (hdsOk x hx).2.1⟩
  have hdsa' := ConLeche.Model.DenoteMetaSpine.lift (m := mpC.base2) (show rc.rP ≤ rc.rP + cA.2 by omega)
    (fun x hx => (hdsOk x hx).1) hdsa
  have hkf : keyFrame (dsa.map (AnnotTerm.liftN (rc.rP + cA.2 - rc.rP) · 0)) (rc.rP + cA.2)
      (consList (xs ++ fs) ρ) = keyFrame dsa rc.rP (consList xs ρ) := by
    have := keyFrame_lift dsa rc.rP fs (consList xs ρ)
    rw [← consList_append, hfsl, show rc.rP + cA.2 - rc.rP = cA.2 by omega] at *
    exact this
  -- the stage fit
  have hfc' : envC.find? (D.ctorName mm j) = some (.ctorInfo cA.1 M.ds.length cA.2) := hfc
  have hcrH : ConLeche.instPisWith M.ds ((cA.1.type.instantiateLevelParams cA.1.levelParams
      M.lvls).replaceConsts (ConLeche.grpSub M.lvls (rc.rP + cA.2) grp)) = some I.crestH := by
    have := I.hcrest; rw [hgrp] at this; exact this
  have hstage := stage_fieldMem mpC hcl.hD hcl.hnN hcl.hkN hlps hcl.hnd hul hds' hdsa' hgT hgn
    hcl.hmm hjD hfc' hcrH hlf hfvs hdoms hsat hY hkf hfsl hvals hfit
  -- the home group's hole types: closed, read, inhabited by the stage's hole values
  generalize hψ' : Level.substFn ψ cvI.levelParams M.lvls = ψ' at *
  generalize hρp : keyFrame dsa rc.rP (consList xs ρ) = ρp at *
  have hglen : (grp.map Prod.snd).length = grp.length := List.length_map _
  have hgetD2 : ∀ t', (grp.map Prod.snd).getD t' default = (grp.getD t' default).2 := by
    intro t'
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases grp[t']? <;> rfl
  have hvget : ∀ t', t' < D.k → (grpVals D ψ' grp ρp Y).getD t' pt = D.holeVal ψ' ρp Y t' := by
    intro t' ht'
    obtain ⟨cv, caps, -, hg⟩ := hgget t' ht'
    have hl : t' < grp.length := by rw [hgl]; exact ht'
    simp only [grpVals, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]
    have hg' : grp[t'] = (D.member t', cv.type.instantiateLevelParams cv.levelParams M.lvls) := by
      rw [← hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
    rw [hg', idxOf_member hcl.hnN hcl.hkN ht']
  have hformer : ∀ t', t' < (grp.map Prod.snd).length →
      ((grp.map Prod.snd).getD t' default).hasFvar = false ∧
      ((grp.map Prod.snd).getD t' default).looseBVarsBounded 0 = true ∧
      ConstsBound envC ((grp.map Prod.snd).getD t' default) ∧
      ∃ T : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0 ((grp.map Prod.snd).getD t' default)
          = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧
        ∀ σ : Nat → V, (grpVals D ψ' grp ρp Y).getD t' pt ∈ˢ interp V σ T := by
    intro t' ht'
    rw [hglen, hgl] at ht'
    obtain ⟨cv, caps, hf, hg⟩ := hgget t' ht'
    rw [hgetD2, hg]
    dsimp only
    have hmem := List.mem_of_find?_eq_some hf
    have hwf := mpC.base2.wf _ hmem
    obtain ⟨ta, hta⟩ := mpC.type_reads _ hmem ψ'
    change denoteMeta mpC.base2.acval envC ψ' 0 cv.type = some ta at hta
    have hlps' : cv.levelParams = cvI.levelParams := by
      obtain ⟨cv', caps', hf', hl'⟩ := hlps t' ht'
      rw [hf] at hf'
      obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
      exact hl'
    refine ⟨by rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1,
      constsBound_of_constsResolve _
        (by rw [ConLeche.Expr.constsResolve_instantiateLevelParams]; exact hwf.2.2.1),
      ta, ?_, fun σ => mpC.type_wellDenotedV _ hmem ψ' ta hta σ, fun σ => ?_⟩
    · rw [denotePInstLevels, hlps', hψ']; exact hta
    · rw [hvget t' ht']
      exact holeVal_mem_type mpC hcl.hD ht' hf hta hY σ
  -- the callee's hole type, a Π-tower over its parameters and indices
  obtain ⟨hL0, -, hrd, -, -⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cvt, capst, hft, hrdt⟩ := hrd t htk
  obtain ⟨pds, hpdsR, hpdsM, hpdsNZ⟩ := hrdt ψ'
  have hTt : denoteMeta mpC.base2.acval envC ψ 0 ((grp.map Prod.snd).getD t default)
      = some (mkPisAV pds (.sort (D.w ψ'))) := by
    obtain ⟨cv, caps, hf, hg⟩ := hgget t htk
    rw [hft] at hf
    obtain ⟨rfl, rfl⟩ : cvt = cv ∧ capst = caps := by simpa using hf
    obtain ⟨cv', caps', hf', hl'⟩ := hlps t htk
    rw [hft] at hf'
    obtain ⟨rfl, rfl⟩ : cvt = cv' ∧ capst = caps' := by simpa using hf'
    rw [hgetD2, hg, denotePInstLevels, hl', hψ']
    exact hpdsR
  have hpdsLen : pds.length = (M.ds ++ ih.idx).length := by
    have h1 := congrArg List.length hpdsM
    rw [List.length_map, List.length_append, hL0.parsLen t htk, hlenP] at h1
    rw [h1, List.length_append, ← hidsLen2, htD]
  -- the field's leaves: the frame's and the home's holes
  have hcrestF : (cA.1.type.instantiateLevelParams cA.1.levelParams M.lvls).hasFvar = false := by
    have h0 := hCf
    simp only [ConLeche.targetCtorAt, hMo] at h0
    exact h0
  have hfldL : ∀ l ∈ (doms.getD ih.field default).fvarLeaves, Expr.fvar l.1 l.2 ∈
      (ConLeche.targetHoles (grp.map Prod.snd) (rc.rP + cA.2)).reverse
        ++ (Q.fvsPref ++ Q.fvsF).reverse := by
    intro l hl
    by_cases hdl : ih.field < doms.length
    · have hmemd : doms.getD ih.field default ∈ doms := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdl, Option.getD_some]
        exact List.getElem_mem _
      rcases piDomsWith_fvarLeaves Q.fvsF I.crestH doms hdoms _ hmemd l hl with h1 | ⟨x, hx, h1⟩
      · rcases instPisWith_fvarLeaves M.ds _ I.crestH hcrH l h1 with h2 | ⟨a, ha, h2⟩
        · obtain ⟨c0, us0, r, hr, h3⟩ := ConLeche.fvarLeaves_replaceConsts_closed _ hcrestF l h2
          unfold ConLeche.grpSub at hr
          split at hr
          · obtain ⟨l1, l2, heq, -⟩ := List.lookup_eq_some_iff.mp hr
            have hm : (c0, r) ∈ grp.mapIdx fun i (x : Name × Expr) =>
                (x.1, Expr.fvar (rc.rP + cA.2 + i) x.2) := by
              rw [heq]; simp
            obtain ⟨i, hi', hx⟩ := List.mem_mapIdx.mp hm
            obtain rfl := (Prod.mk.inj hx).2.symm
            have hcl0 : grp[i].2.hasFvar = false := by
              obtain ⟨_, _, _, cv0, caps0, hf0, hg0⟩ := hgT.2 grp[i] (List.getElem_mem hi')
              rw [hg0, Expr.hasFvar_instantiateLevelParams]
              exact (mpC.base2.wf _ (List.mem_of_find?_eq_some hf0)).1
            simp only [Expr.fvarLeaves, List.mem_cons,
              ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl0, List.not_mem_nil,
              or_false] at h3
            subst h3
            refine List.mem_append_left _ (List.mem_reverse.mpr ?_)
            simp only [ConLeche.targetHoles, List.mem_map, List.mem_range, List.length_map]
            refine ⟨i, hi', ?_⟩
            rw [hgetD2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
          · exact nomatch hr
        · exact List.mem_append_right _ (List.mem_reverse.mpr
            (List.mem_append_left _ ((hdsOk a ha).2.2.2 l h2)))
      · exact List.mem_append_right _ (List.mem_reverse.mpr
          (hframeL x (List.mem_append_right _ hx) l h1))
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hl
      exact absurd hl (by simp [show (default : Expr) = .bvar 0 from rfl, Expr.fvarLeaves])
  have hargsL : ∀ x ∈ M.ds ++ ih.idx, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
    intro x hx l hl
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ ((hdsOk x hx).2.2.2 l hl)
    · exact hidxL x hx l hl
  -- the check's run, at the generic hole call's spelling
  have hhole : ConLeche.targetIntraHole (mkFEnv envC) (tgtFam pp.toBlockShape out) M
      (rc.rP + cA.2) ih = .fvar (rc.rP + cA.2 + t) ((grp.map Prod.snd).getD t default) := by
    unfold ConLeche.targetIntraHole
    rw [hmaj', ht, hgrp, hgetD2]
  have hfldI := I.hfld
  have hwantI := I.hwant
  have hdeqI := I.hdeq
  rw [hfldE, hgrp, ← hglen] at hfldI
  rw [hhole, hgrp, ← hglen] at hwantI
  rw [hfldE, hhole, hgrp, ← hglen] at hdeqI
  have hTel : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).teles
      = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hFF : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).fields
      = Q.fvsF := congrArg (·.fields) hFrEq
  have hbs' : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval envC ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))).getD []) bs := by
    have := hbs
    simp only [tgtTlA, tgtTeleTys] at this
    rw [hih, hTel, hB, List.map_map] at this
    simpa [Function.comp_def] using this
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨hspA, hbl, hmemA⟩ := holeCall_gen (V := V) (mT := mpC.base2) (envT := envC) (φ := ψ) hμ hacl
    (Rules.RulesInputs.ofSem mpC ψ) hfldI hwantI hdeqI hFr hxl hfsl hW ih.field hfldL htL
    hargsL (hv := grpVals D ψ' grp ρp Y) (by simp [grpVals, hglen]) hformer
    (fun A hA => hstage ih.field hfi A (by rw [hglen] at hA; exact hA))
    (by rw [hglen, hgl]; exact htk) hTt hpdsNZ hpdsLen bs hbs'
  -- the applied field and the index arguments, in the rule data's spelling
  obtain ⟨fty, hfty⟩ : ∃ fty, Q.fvsF.getD ih.field default = Expr.fvar (rc.rP + ih.field) fty := by
    have hlt : rc.rP + ih.field < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + ih.field) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.getElem_append_right (by omega)] at hty
    simpa [hlp] using hty
  obtain ⟨hFap, hEis⟩ := tgtFapEis_interp mpC ψ ρ hih hTel hFF hB hfty hxl hfsl hfi hbl
  -- the parameters' values: the key frame's
  have hdsl : dsa.length = M.ds.length := (DenoteMetaSpine.length_eq hdsa).symm
  have hdsV : M.ds.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mpC.base2.acval envC ψ
          (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
          (x.instantiateList (locOpen (rc.rP + cA.2)
            ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length) 0)).getD default))
      = frameIdx (D.params ψ').length ρp := by
    rw [← hρp, hlenP, ← hdsl]
    unfold keyFrame
    rw [show dsa.length = (dsa.map (interp V (consList xs ρ))).length by simp,
      frameIdx_consList', ← DenoteMetaSpine.getD_eq hdsa, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨hwx, hbx, -, -⟩ := hdsOk x hx
    rw [ConLeche.Expr.instantiateList_eq_self hbx,
      denoteMeta_lift mpC.base2.acval_closed hwx _ (by omega)]
    obtain ⟨a, ha⟩ : ∃ a, denoteMeta mpC.base2.acval envC ψ rc.rP x = some a := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact ⟨_, by
        have := DenoteMetaSpine.getD hdsa default i hi
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this⟩
    rw [ha, Option.map_some, Option.getD_some]
    simp only [Function.comp, ha, Option.getD_some]
    rw [show consList bs (consList (xs ++ fs) ρ) = consList (fs ++ bs) (consList xs ρ) by
      rw [consList_append, consList_append],
      show rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length - rc.rP
        = (fs ++ bs).length by simp [hfsl, hbl]; omega,
      interp_liftN_consList]
  rw [List.map_append, hdsV, hvget t htk] at hmemA
  rw [← hbl, ← hEis, ← hFap] at hmemA
  rw [htD]
  have hisl : ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval envC ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))).length
        = (D.ids t ψ').length := by
    rw [hEis, List.length_map, ← htD, hidsLen2]
  exact holeVal_foldl_mem hL0 htk hsat hisl hmemA

end Land

end ConLeche.Model
