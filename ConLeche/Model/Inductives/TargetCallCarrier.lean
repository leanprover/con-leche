module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Semantics.Kit
import ConLeche.Verify.Leaves

public section

/-!
# A target call's target at the CARRIER (lane RECLIB, B3 (e))

`tgtCall_coreFitG` at the valuation that gives every member hole its
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

section MemberHoles

variable {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V} {pp : BlockParts}
  {cvTas : List ConstantVal}

/-- **The member constants' own values lie in their formers' types**
(`EnvModelM.mem_type`): the holes' values `hv`, when they are the
members' own values. -/
theorem memberHoles_ty (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {hv : List V}
    (hvget : ∀ t, t < cvTas.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (d.memberName t) ψ)) :
    ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T := by
  intro t ht
  obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t]? = some cv := ⟨_, List.getElem?_eq_getElem ht⟩
  obtain ⟨hname, -, ⟨caps, hfind⟩, -, -, hFD⟩ := hmr.2.2.2.1 t cv hcv
  have hgc : cvTas.getD t default = cv := by rw [List.getD_eq_getElem?_getD, hcv]; rfl
  rw [hgc, hvget t ht]
  refine ⟨_, hFD.read ψ, ?_⟩
  have hm := mpC.mem_type (.indInfo cv caps) (List.mem_of_find?_eq_some hfind) ψ _
    (hFD.read ψ) ρ
  rw [hname]
  exact hm

/-- **The member constants: found, at the block's levels, valued by
`hvC`** — `targetAbs_read`'s name premise at the members' own values. -/
theorem memberHoles_names (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {hvC : Nat → V}
    (hvget : ∀ t, t < cvTas.length → hvC t = interp V ρ (mpC.base2.acval (d.memberName t) ψ)) :
    ∀ (n : Name) (t : Nat),
      pp.toBlockShape.memberNames.findIdx? (· == n) = some t →
      t < (cvTas.map (·.type)).length ∧ ∃ ci : ConstantInfo, envC.find? n = some ci ∧
        (pp.toBlockShape.lps.map Level.param).length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (mpC.base2.acval n
          (Level.substFn ψ ci.toConstantVal.levelParams (pp.toBlockShape.lps.map Level.param)))
          = hvC t := by
  intro n t hft
  obtain ⟨htl, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hft
  have hmn : pp.toBlockShape.memberNames[t] = n := by simpa using hbeq
  have htl' : t < pp.toBlockShape.members.length := by
    simpa [ConLeche.BlockShape.memberNames] using htl
  have htc : t < cvTas.length := by rw [hN.2.2, hmr.2.1]; exact htl'
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
  rw [hlps, Level.substFn_param_self, ← hname, hvget t htc]
  exact acval_interp_closed mpC.base2 _ ψ σ ρ

/-- **A called field lies in its member-abstracted type's reading**, at
the holes' values `hv` read by `hnames`: at that valuation the
abstraction IS the concrete field type (`targetAbs_read`), and the frame's
fields fit their concrete readings `fd` (`hF`, `hsp`). -/
theorem field_mem_absRead (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {rP nF : Nat} {fvsPref fvsF : List Expr}
    (hFr : FvarList (rP + nF) (fvsPref ++ fvsF).reverse)
    (hlp : fvsPref.length = rP) (hlf : fvsF.length = nF)
    {pd fd : List AnnotTerm} (hpl : pd.length = rP) (hfl : fd.length = nF)
    (hF : ∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (rP + l) x.fvarTypeD = some (fd.getD l default))
    {xs fs : List V} (hsp : SpineFit ρ (pd ++ fd) (xs ++ fs)) (hxl : xs.length = rP)
    (hfsl : fs.length = nF) {hv : List V} (hvl : hv.length = cvTas.length)
    (hvget : ∀ t, t < cvTas.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (d.memberName t) ψ))
    {fi : Nat} (hfi : fi < nF) (Aty : AnnotTerm)
    (hA : denoteMeta mpC.base2.acval envC ψ (rP + nF + (cvTas.map (·.type)).length)
      (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
        (ConLeche.targetHoles (cvTas.map (·.type)) (rP + nF))
        (fvsF.getD fi default).fvarTypeD) = some Aty) :
    fs.getD fi pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty := by
  -- the field variable and its concrete type
  have hlt : rP + fi < (fvsPref ++ fvsF).length := by simp [hlp, hlf]; omega
  obtain ⟨ty, hty⟩ := hFr.reverse_idx (rP + fi) _
    (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
  have hfvi : fvsF.getD fi default = Expr.fvar (rP + fi) ty := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.getElem_append_right (by omega)] at hty
    simpa [hlp] using hty
  have hwty : Expr.WScoped (rP + fi) ty := by
    have := hFr.2.2 _ (List.mem_reverse.mpr (List.getElem_mem hlt))
    rw [hty] at this
    unfold Expr.WScoped at this
    exact this.2
  have hleaves : ∀ l ∈ ty.fvarLeaves, l.1 < rP + fi :=
    fun l hl => ConLeche.Expr.fvarLeaves_lt_of_wscoped hwty l hl
  rw [hfvi] at hA
  have hAty : denoteMeta mpC.base2.acval envC ψ (rP + nF + (cvTas.map (·.type)).length + 0)
      ((ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
        (ConLeche.targetHoles (cvTas.map (·.type)) (rP + nF)) ty).instantiateList [] 0)
      = some Aty := by
    rw [ConLeche.Expr.instantiateList_nil, Nat.add_zero]; exact hA
  have hdF : denoteMeta mpC.base2.acval envC ψ (rP + fi) ty = some (fd.getD fi default) := by
    refine hF fi (Expr.fvar (rP + fi) ty) ?_
    have := hfvi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    rw [List.getElem?_eq_getElem (by omega)]
    exact congrArg some this
  have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m)
    (nF - fi + cvTas.length) (rP + fi) ty 0 [] [] hleaves (LocList.nil _) (LocList.nil _)
  simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero, hdF, Option.map_some] at hd
  have hSr := targetAbs_read (m := mpC.base2) (env := envC) (φ := ψ)
    (names := pp.toBlockShape.memberNames) (lvls := pp.toBlockShape.lps.map .param)
    (formerTys := cvTas.map (·.type)) (B := rP + nF) (hvC := fun t => hv.getD t pt)
    (memberHoles_names hN hmr ψ ρ hvget) ty 0 [] [] (LocList.nil _) (LocList.nil _)
  rw [hAty, ConLeche.Expr.instantiateList_nil,
    show rP + nF + (cvTas.map (·.type)).length + 0
      = rP + fi + (nF - fi + cvTas.length) from by rw [List.length_map]; omega, hd] at hSr
  obtain ⟨hval, -⟩ := hSr [] (consList hv (consList (xs ++ fs) ρ)) rfl (fun t ht => by
    rw [List.length_map] at ht ⊢
    rw [consList_getD_of_lt _ _ _ (by rw [hvl]; omega), hvl,
      show cvTas.length - 1 - (cvTas.length - 1 - t) = t from by omega])
  rw [consList_nil] at hval
  rw [hval, interp_liftN]
  have hsh : shiftE (nF - fi + cvTas.length) 0 (consList hv (consList (xs ++ fs) ρ))
      = consList ((xs ++ fs).take (rP + fi)) ρ := by
    have hsplit : consList hv (consList (xs ++ fs) ρ)
        = consList ((xs ++ fs).drop (rP + fi) ++ hv)
            (consList ((xs ++ fs).take (rP + fi)) ρ) := by
      rw [← consList_append ((xs ++ fs).take (rP + fi)), ← List.append_assoc,
        List.take_append_drop, consList_append (xs ++ fs) hv ρ]
    rw [hsplit, show nF - fi + cvTas.length
      = ((xs ++ fs).drop (rP + fi) ++ hv).length from by
        simp [hvl, hxl, hfsl]; omega, shiftE_consList]
  rw [hsh]
  have hmemF := FixKI.spineFit_getD_mem' hsp (l := rP + fi) (by simp [hpl, hfl]; omega)
  have e1 : (pd ++ fd).getD (rP + fi) default = fd.getD fi default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hpl,
      show rP + fi - rP = fi from by omega, ← List.getD_eq_getElem?_getD]
  have e2 : (xs ++ fs).getD (rP + fi) pt = fs.getD fi pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hxl,
      show rP + fi - rP = fi from by omega, ← List.getD_eq_getElem?_getD]
  rw [e1, e2] at hmemF
  exact hmemF

end MemberHoles

section Carrier

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

set_option maxHeartbeats 4000000 in
/-- **A target call's target at the carrier, at ANY caller** (lane
NESTIND, session 9): at the caller rule's
frame facts, its field openers' readings `fd` (`hF`) and its walk
context, for a MEMBER callee. -/
theorem tgtCall_carrierG (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {rc : ConLeche.RecShape} {M : TargetMajor} {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hnP : pp.toBlockShape.nP ≤ rc.rP)
    (hdsOk : TgtDsOk fe.env rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound fe.env (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound fe.env r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound fe.env ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs) = tgtAbs μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j)
    {pd fd : List AnnotTerm} (hpl : pd.length = rc.rP) (hfl : fd.length = cA.2)
    (hF : ∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
      denoteMeta mpC.base2.acval fe.env ψ (rc.rP + l) x.fvarTypeD = some (fd.getD l default))
    {xs fs : List V} (hsp : SpineFit ρ (pd ++ fd) (xs ++ fs)) {Δ : List AnnotTerm}
    (hW : WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ) Δ
      (Q.fvsPref ++ Q.fvsF).reverse)
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    {r : Nat}
    (hr : r < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    (hm1 : memR ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default).callee)
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
  obtain ⟨-, hmemk, -, -, -⟩ := blockRecMajor_run (hm := hm1) hμ mpC h hmr hr1 ψ
  obtain ⟨hFr, -, -, -⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hfsl : fs.length = cA.2 := by
    have hsl := hsp.length_eq
    simp only [List.length_append, hpl, hfl] at hsl
    omega
  have hformerF := hmr.formers_noFvar
  -- the holes at the members' own values
  have hkN := hN.2.2
  let hvC : Nat → V := fun t =>
    interp V ρ (mpC.base2.acval ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD
      ppsOf).memberName t) ψ)
  let hv : List V := (List.range cvTas.length).map hvC
  have hvl : hv.length = cvTas.length := by simp [hv]
  have hvget : ∀ t, t < cvTas.length → hv.getD t pt = hvC t := by
    intro t ht; simp [hv, List.getD_eq_getElem?_getD, List.getElem?_range ht]
  have hvget' : ∀ t, t < cvTas.length → hv.getD t pt = interp V ρ (mpC.base2.acval
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).memberName t) ψ) := hvget
  have hvTy := memberHoles_ty hmr ψ ρ hvget'
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
    have hFF : tgtFieldFvs pp.toBlockShape out c j = Q.fvsF := congrArg (·.fields) hFrEq
    rw [hFF, tgtAbsM, hB] at hA
    rw [show consList (xs ++ fs ++ hv) ρ = consList hv (consList (xs ++ fs) ρ) from
      consList_append _ _ _]
    exact field_mem_absRead hN hmr ψ ρ hFr hlp hlf hpl hfl hF hsp hxl hfsl hvl hvget'
      (tgtIh_field_lt Q hihMem) Aty (by rw [List.length_map]; exact hA)
  obtain ⟨h1, h2⟩ := tgtCall_coreFitG hμ h hdR' hN hmr hnd hformerF ψ ρ Q hrP hnP hdsOk hCf hCb
    hCc hbf hTf hTb hTc hle hRT3 hB hFrEq hAbs hW hxs hfsl hr hm1 hv hvl hvTy hii bs hbs
  rw [hvget _ (by rw [hkN]; exact hmemk)] at h2
  exact ⟨h1, h2⟩

end Carrier

end ConLeche.Model
