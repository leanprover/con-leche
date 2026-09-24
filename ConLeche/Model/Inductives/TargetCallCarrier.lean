module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.StructBits
import ConLeche.Semantics.Kit
import ConLeche.Verify.Leaves
import ConLeche.Verify.InstList

public section

/-!
# A target call's target at the CARRIER (lane RECLIB, B3 (e))

`tgtCall_coreFit` at the valuation that gives every member hole its
member constant's own value: the holes lie in their formers' types (the
constants inhabit their stored types, `EnvModelM.mem_type`), and the
called field lies in its member-abstracted type's reading because at
that valuation the abstraction IS the concrete term (`targetAbs_read`)
and the frame's fields fit their concrete readings.  The call target's
index readings then fit the callee's member's index telescope and the
applied field lies in the member's former applied to the parameters and
them — a MAJOR of the callee's class, which is what the graph kit's `ih`
rows read.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Carrier

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

set_option maxHeartbeats 4000000 in
/-- **A target call's target at the carrier.** -/
theorem tgtCall_carrier (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTas ctorsAs (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape false nested blk cvTas ctorsAs out)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c
      ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j) (xs ++ fs))
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    {r : Nat}
    (hr : r < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ
        c j r).map (·.2.2)) bs) :
    SpineFit (consList (xs.take d.nP) ρ)
      (d.IdsM (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee) ψ)
      ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env
        ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env
          ψ c j r)
      ∈ˢ (xs.take d.nP ++ (tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out
          mpC.base2.acval fe.env ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))).foldl
          SetTheory.app
          (interp V ρ (mpC.base2.acval (d.memberName (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
              default).callee)) ψ)) := by
  have hdR' := hdR
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the rule, its run and the entry
  obtain ⟨r0, hr0⟩ : ∃ r0, (tgtRs out)[c]? = some r0 := ⟨_, List.getElem?_eq_getElem hc⟩
  have hjr : j < r0.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr0, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, r0.2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r0.2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr0]; exact hjr)⟩
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs⟩ := tgtRuleAt_facts h R hr0 hcA hrhs
  have hIhL : tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  have hrl : r < Q.ihs.toList.length := by rw [← hIhL]; exact hr
  have hihMem : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default ∈ Q.ihs.toList := by
    rw [hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl, Option.getD_some]
    exact List.getElem_mem hrl
  obtain ⟨C⟩ := Q.call hihMem
  have hcal : ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default).callee < (tgtRs out).length := by
    simpa [tgtFam] using targetCall_callee_lt C
  obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type))
      out c j).getD r default).callee]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
  obtain ⟨-, hmemk, -, -, -⟩ := blockRecMajor_run (hm := trivial) hμ mpC h hmr hr1 ψ
  -- the constructor's type and the frame
  obtain ⟨ms0, hms0, hctA, -⟩ := recStage_ctorsAt (hm := trivial) h hr0
  have hmemk0 : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms0).1
  have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk0 j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hCc : ConstsBound fe.env cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
  obtain ⟨hFr, -, -, -⟩ := targetFrame_facts Q.hpref Q.hcrest hds Q.hfld hTf hTb hTc
    (by rw [hct]; exact hCf) (by rw [hct]; exact hCb) (by rw [hct]; exact hCc)
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr0, hrP]
  have hfl : (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).length
      = cA.2 := blockRuleFdomsAV_length_run (hm := trivial) (mpC := mpC) h hr0 hcA hrhs _
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hfsl : fs.length = cA.2 := by
    have hsl := hsp.length_eq
    simp only [List.length_append, hpl, hfl] at hsl
    omega
  -- the holes at the members' own values
  have hkN := hN.2.2
  let hvC : Nat → V := fun t =>
    interp V ρ (mpC.base2.acval ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD
      ppsOf).memberName t) ψ)
  let hv : List V := (List.range cvTas.length).map hvC
  have hvl : hv.length = cvTas.length := by simp [hv]
  have hvget : ∀ t, t < cvTas.length → hv.getD t pt = hvC t := by
    intro t ht; simp [hv, List.getD_eq_getElem?_getD, List.getElem?_range ht]
  have hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T := by
    intro t ht
    obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t]? = some cv := ⟨_, List.getElem?_eq_getElem ht⟩
    obtain ⟨hname, -, ⟨caps, hfind⟩, -, -, hFD⟩ := hmr.2.2.2.1 t cv hcv
    have hgc : cvTas.getD t default = cv := by rw [List.getD_eq_getElem?_getD, hcv]; rfl
    rw [hgc, hvget t ht]
    refine ⟨_, hFD.read ψ, ?_⟩
    have hm := mpC.mem_type (.indInfo cv caps) (List.mem_of_find?_eq_some hfind) ψ _
      (hFD.read ψ) ρ
    show interp V ρ (mpC.base2.acval _ ψ) ∈ˢ _
    rw [hname]
    exact hm
  -- the member constants: found, at the block's levels, valued by `hvC`
  have hnames : ∀ (n : Name) (t : Nat),
      pp.toBlockShape.memberNames.findIdx? (· == n) = some t →
      t < (cvTas.map (·.type)).length ∧ ∃ ci : ConstantInfo, fe.env.find? n = some ci ∧
        (pp.toBlockShape.lps.map Level.param).length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (mpC.base2.acval n
          (Level.substFn ψ ci.toConstantVal.levelParams (pp.toBlockShape.lps.map Level.param)))
          = hvC t := by
    intro n t hft
    obtain ⟨htl, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hft
    have hmn : pp.toBlockShape.memberNames[t] = n := by simpa using hbeq
    have htl' : t < pp.toBlockShape.members.length := by
      simpa [ConLeche.BlockShape.memberNames] using htl
    have htc : t < cvTas.length := by rw [hkN, hmr.2.1]; exact htl'
    obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t]? = some cv := ⟨_, List.getElem?_eq_getElem htc⟩
    obtain ⟨hname, hlps, ⟨caps, hfind⟩, -, -, -⟩ := hmr.2.2.2.1 t cv hcv
    obtain ⟨hnameMs, -⟩ := hmr.2.2.2.2.1 t _ (List.getElem?_eq_getElem htl')
    have hn : n = cv.name := by
      rw [← hmn, ← hname, hnameMs]
      simp [ConLeche.BlockShape.memberNames]
    subst hn
    refine ⟨by simpa using htc, .indInfo cv caps, hfind,
      by show _ = cv.levelParams.length; rw [hlps]; simp, fun σ => ?_⟩
    show interp V σ (mpC.base2.acval cv.name (Level.substFn ψ cv.levelParams
      (pp.toBlockShape.lps.map Level.param))) = _
    rw [hlps, Level.substFn_param_self, ← hname]
    exact acval_interp_closed mpC.base2 _ ψ σ ρ
  -- the called field lies in its member-abstracted type's reading
  have hii : ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ
          (tgtB pp.toBlockShape out c j + cvTas.length)
          (tgtAbsM pp.toBlockShape (cvTas.map (·.type)) out c j
            ((tgtFieldFvs pp.toBlockShape out c j).getD
              ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
                default).field default).fvarTypeD) = some Aty →
      fs.getD ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).field pt
        ∈ˢ interp V (consList (xs ++ fs ++ hv) ρ) Aty := by
    intro Aty hA
    have hfi : ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
        default).field < cA.2 := by
      refine Nat.lt_of_not_le fun hge => ?_
      have hg : Q.fvsF.getD ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c
          j).getD r default).field default = .bvar 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      have h0 := C.hfld
      rw [hg] at h0
      exact inferTypeCore_bvar_absurd' h0
    generalize ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default).field = fi at hA hfi ⊢
    have hFF : tgtFieldFvs pp.toBlockShape out c j = Q.fvsF := congrArg (·.fields) hFrEq
    -- the field variable and its concrete type
    have hlt : rc.rP + fi < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + fi) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    have hfvi : Q.fvsF.getD fi default = Expr.fvar (rc.rP + fi) ty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [List.getElem_append_right (by omega)] at hty
      simpa [hlp] using hty
    have hwty : Expr.WScoped (rc.rP + fi) ty := by
      have := hFr.2.2 _ (List.mem_reverse.mpr (List.getElem_mem hlt))
      rw [hty] at this
      unfold Expr.WScoped at this
      exact this.2
    have hleaves : ∀ l ∈ ty.fvarLeaves, l.1 < rc.rP + fi :=
      fun l hl => ConLeche.Expr.fvarLeaves_lt_of_wscoped hwty l hl
    rw [hFF, hfvi, tgtAbsM, hB] at hA
    have hAty : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + (cvTas.map (·.type)).length + 0)
        ((ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2)) ty).instantiateList [] 0)
        = some Aty := by
      rw [ConLeche.Expr.instantiateList_nil, List.length_map, Nat.add_zero]; exact hA
    -- the concrete field type's reading at the frame
    have hdF : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + fi) ty
        = some ((blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).getD fi
            default) := by
      have hcd := blockCtorData_of_core hcore hcj
      obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr0
      have h1 := (blockRuleFdomsAV_eq (hm := trivial) h hr0 hcA hrhs hcd hCf TE.nP_le ψ).2 fi
        (Expr.fvar (rc.rP + fi) ty)
        (by rw [← hFldEq, List.getElem?_eq_getElem (by omega)]
            congr 1
            have := hfvi
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
            exact this)
      rw [← hrP] at h1
      exact h1
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := fe.env) (φ := ψ)
      (fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m)
      (cA.2 - fi + cvTas.length) (rc.rP + fi) ty 0 [] [] hleaves (LocList.nil _) (LocList.nil _)
    simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero, hdF, Option.map_some] at hd
    have hSr := targetAbs_read (m := mpC.base2) (env := fe.env) (φ := ψ)
      (names := pp.toBlockShape.memberNames) (lvls := pp.toBlockShape.lps.map .param)
      (formerTys := cvTas.map (·.type)) (B := rc.rP + cA.2) (hvC := hvC) hnames ty 0 [] []
      (LocList.nil _) (LocList.nil _)
    rw [hAty, ConLeche.Expr.instantiateList_nil,
      show rc.rP + cA.2 + (cvTas.map (·.type)).length + 0
        = rc.rP + fi + (cA.2 - fi + cvTas.length) from by rw [List.length_map]; omega, hd] at hSr
    obtain ⟨hval, -⟩ := hSr [] (consList hv (consList (xs ++ fs) ρ)) rfl (fun t ht => by
      rw [List.length_map] at ht ⊢
      rw [consList_getD_of_lt _ _ _ (by rw [hvl]; omega), hvl,
        show cvTas.length - 1 - (cvTas.length - 1 - t) = t from by omega, hvget t ht])
    rw [show consList (xs ++ fs ++ hv) ρ = consList hv (consList (xs ++ fs) ρ) from
      consList_append _ _ _]
    rw [consList_nil] at hval
    rw [hval, interp_liftN]
    -- the frame below the field's own depth
    have hsh : shiftE (cA.2 - fi + cvTas.length) 0 (consList hv (consList (xs ++ fs) ρ))
        = consList ((xs ++ fs).take (rc.rP + fi)) ρ := by
      have hsplit : consList hv (consList (xs ++ fs) ρ)
          = consList ((xs ++ fs).drop (rc.rP + fi) ++ hv)
              (consList ((xs ++ fs).take (rc.rP + fi)) ρ) := by
        rw [← consList_append ((xs ++ fs).take (rc.rP + fi)), ← List.append_assoc,
          List.take_append_drop, consList_append (xs ++ fs) hv ρ]
      rw [hsplit, show cA.2 - fi + cvTas.length
        = ((xs ++ fs).drop (rc.rP + fi) ++ hv).length from by
          simp [hvl, hxl, hfsl]; omega, shiftE_consList]
    rw [hsh]
    have hmemF := FixKI.spineFit_getD_mem' hsp (l := rc.rP + fi) (by simp [hpl, hfl]; omega)
    have e1 : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c
        ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).getD
          (rc.rP + fi) default
        = (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).getD fi
            default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hpl,
        show rc.rP + fi - rc.rP = fi from by omega, ← List.getD_eq_getElem?_getD]
    have e2 : (xs ++ fs).getD (rc.rP + fi) pt = fs.getD fi pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hxl,
        show rc.rP + fi - rc.rP = fi from by omega, ← List.getD_eq_getElem?_getD]
    rw [e1, e2] at hmemF
    exact hmemF
  obtain ⟨h1, h2⟩ := tgtCall_coreFit hμ h R hdR' hN hS hcore hmr hM hnd ψ ρ hc hj hsp hxs
    hr hv hvl hvTy hii bs hbs
  rw [hvget _ (by rw [hkN]; exact hmemk)] at h2
  exact ⟨h1, h2⟩

end Carrier

end ConLeche.Model
