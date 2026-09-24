module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.Capstone
import ConLeche.Semantics.Kit
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.BetaGate

public section

/-!
# A target call's target, at a valuation of the holes (lane RECLIB, B3 (e) + B4)

The target check types every recursive call on the member-ABSTRACTED
terms (`targetCallOk`, K1): at the rule frame extended by the block's
member HOLES (`targetHoles`, after the prefix and the fields), the
field's abstract type through whnf (`fnorm`) is defeq to
`∀ a⃗, hole_m x⃗ e⃗` (`hdeq`), whose body was inferred (`hwant`).  So at
EVERY valuation of the holes satisfying their types (each hole at its
member former's type), a field lying in its abstract type's reading has
its call target in the hole's family: the index readings fit the
member's index telescope at the parameters, and the applied field lies
in the hole applied to them.

`tgtCall_core` states that once, at a hole valuation `hv` with a
member-application law (`hlaw`: the hole of the callee's member, applied
to the parameters and a fitting index spine, is `Y` at the index
tuple).  Its two instances:

* the CARRIER — `hv` the member constants' own values, `hlaw` the lfp
  clause's leaf, `hii` the concrete field fit (the abstraction read at
  the constants' values is the concrete term): the call target is a
  MAJOR (`TargetRowCall.lean`);
* the SEPARATED tuple — `hv` the clause's hole values (`holeVal`),
  `hlaw` `holeVal_app`, `hii` the hole fit at it: the call target lies
  in the property (`TargetRowInd.lean`, B4).
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

/-- An inference run never types a loose bound variable. -/
theorem inferTypeCore_bvar_absurd' {mode : CheckMode} {env : Env} {F d i : Nat} {t : Expr}
    (h : ConLeche.inferTypeCore mode env F d (.bvar i) = .ok t) : False := by
  cases F with
  | zero =>
    simp [ConLeche.inferTypeCore, ConLeche.pureFns, ConLeche.coreKnot, throw, throwThe,
      MonadExceptOf.throw] at h
  | succ F => exact ConLeche.Rules.inferTypeCore_bvar_inv h

section MajDom

/-- **A stored recursor's major domain, peeled at closed arguments**: the
recursor's type opened at its `mI` leading binders by any bvar-closed
terms is a `∀` whose domain is the eliminated member at the arguments'
parameters and indices (today's type pin, `RecTyEntry`). -/
theorem tgtMajDom_open {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hm : memR c) (hr : rs[c]? = some r)
    {args : List Expr} (hcl : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (hlen : args.length = pp.toBlockShape.majorIdxAt c) {res : Expr}
    (hres : Expr.instPisAtLift args r.1.type = some res) :
    ∃ (ms : ConLeche.MemberShape) (body : Expr) (bm : ConLeche.BinderMeta),
      pp.toBlockShape.members[pp.toBlockShape.recTgtAt c]? = some ms ∧
      res = .forallE (Expr.mkAppN (.const ms.cvT.name (pp.toBlockShape.lps.map .param))
        (args.take pp.toBlockShape.nP ++ args.drop (pp.toBlockShape.rulePrefixAt c))) body bm := by
  obtain ⟨rc, u, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyAt h hm hr
  obtain ⟨hTf, -, -, -, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  have hop := TE.hopen
  obtain ⟨fvs1, fvs', o, hop1, hop2, hF⟩ :=
    openPisAtFvars_split (pp.toBlockShape.majorIdxAt c) (m := 1) hop
  obtain ⟨dom, body, bm, rfl, rfl⟩ : ∃ dom body bm, o = .forallE dom body bm ∧
      fvs' = [Expr.fvar (pp.toBlockShape.majorIdxAt c) dom] := by
    match o, hop2 with
    | .forallE dom body bm, hop2 =>
      simp only [ConLeche.openPisAtFvars, Nat.zero_add] at hop2
      simp only [Option.some.injEq, Prod.mk.injEq] at hop2
      exact ⟨dom, body, bm, rfl, hop2.1.symm⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [ConLeche.openPisAtFvars] at h
  have hl1 : fvs1.length = pp.toBlockShape.majorIdxAt c :=
    ConLeche.Verify.openPisAtFvars_length _ hop1
  have hmajE : TE.maj = Expr.fvar (pp.toBlockShape.majorIdxAt c) dom := by
    have := TE.hmaj
    rw [hF, List.getElem?_append_right (by omega), hl1, Nat.sub_self] at this
    exact (Option.some.inj this).symm
  have hdom : dom = Expr.mkAppN (.const TE.ms.cvT.name (pp.toBlockShape.lps.map .param))
      (fvs1.take pp.toBlockShape.nP ++ fvs1.drop (pp.toBlockShape.rulePrefixAt c)) := by
    have hd : Expr.fvarTypeD TE.maj = dom := by rw [hmajE]; rfl
    rw [← hd]
    conv => lhs; rw [← ConLeche.Expr.mkAppN_getApp (Expr.fvarTypeD TE.maj)]
    rw [TE.hmajFn, ← List.take_append_drop pp.toBlockShape.nP (Expr.fvarTypeD TE.maj).getAppArgs,
      TE.hmajParams, TE.hmajIdx, hF]
    have hnP := TE.hroom
    have hmI := TE.hmI
    congr 2
    · rw [List.take_append_of_le_length (by omega)]
    · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
      rw [List.take_of_length_le (by simp; omega)]
  -- the peel at the openers, and at the arguments
  have hins1 := ConLeche.Verify.openPisAtFvars_instPisAt _ hop1
  rw [ConLeche.instPisAtLift_eq_instPisAt hcl] at hres
  obtain ⟨⟨ds, res'⟩, hres2, rfl⟩ := Option.map_eq_some_iff.mp hres
  have hidx := ConLeche.openPisAtFvars_index _ _ _ hop1
  have hrep := instPisAt_replF (g := fun i => args[i]?) (fun i x hx => hcl x (List.mem_of_getElem? hx))
    fvs1 args r.1.type hins1 (by rw [hl1, hlen]) (fun j hj hj' => by
      obtain ⟨ty, hty⟩ := hidx j _ (List.getElem?_eq_getElem hj)
      rw [hty]
      simp [replF, List.getElem?_eq_getElem hj'])
  rw [replF_of_not_hasFvar _ _ hTf, hres2] at hrep
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrep)
  have hmapF : fvs1.map (replF fun i => args[i]?) = args := by
    apply List.ext_getElem (by simp [hl1, hlen])
    intro j h1 h2
    simp only [List.getElem_map]
    obtain ⟨ty, hty⟩ := hidx j _ (List.getElem?_eq_getElem (by simpa using h1))
    rw [hty]
    simp [replF, List.getElem?_eq_getElem h2]
  refine ⟨TE.ms, replF (fun i => args[i]?) body, bm, TE.hms, ?_⟩
  rw [hdom]
  simp only [replF, replF_mkAppN, List.map_append]
  rw [List.map_take, List.map_drop, hmapF]

end MajDom

section Core

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

/-- **A target call's target, at a valuation of the holes, as a FIT**:
`tgtCall_core` before the member-application law — the index readings
fit the callee's member's index telescope at the parameters, and the
applied field lies in the callee's hole applied to them. -/
theorem tgtCall_coreFit (hμ : μ.verifiedChecks = true)
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
    (hv : List V) (hvl : hv.length = cvTas.length)
    (hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T)
    (hii : ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ
          (tgtB pp.toBlockShape out c j + cvTas.length)
          (tgtAbsM pp.toBlockShape (cvTas.map (·.type)) out c j
            ((tgtFieldFvs pp.toBlockShape out c j).getD
              ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
                default).field default).fvarTypeD) = some Aty →
      fs.getD ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).field pt
        ∈ˢ interp V (consList (xs ++ fs ++ hv) ρ) Aty)
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
          (hv.getD (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
              default).callee) pt) := by
  have hdR' := hdR
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hver : μ = .verified := CheckMode.eq_verified hμ
  -- the rule and its run
  obtain ⟨r0, hr0⟩ : ∃ r0, (tgtRs out)[c]? = some r0 := ⟨_, List.getElem?_eq_getElem hc⟩
  have hjr : j < r0.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr0, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, r0.2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r0.2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr0]; exact hjr)⟩
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs⟩ := tgtRuleAt_facts h R hr0 hcA hrhs
  -- the entry
  have hIhL : tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  generalize hih : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
    default = ih at *
  have hrl : r < Q.ihs.toList.length := by rw [← hIhL]; exact hr
  have hihMem : ih ∈ Q.ihs.toList := by
    rw [← hih, hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl, Option.getD_some]
    exact List.getElem_mem hrl
  obtain ⟨C⟩ := Q.call hihMem
  -- the constructor's stored type: closed, bounded
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
  -- the frame
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest (tgtDsOk_of_take Q.hpref hTf hTc hds) Q.hfld hTf hTb hTc
    (by rw [hct]; exact hCf) (by rw [hct]; exact hCb) (by rw [hct]; exact hCc)
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr0, hrP]
  have hfl : (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).length
      = cA.2 := blockRuleFdomsAV_length_run (hm := trivial) (mpC := mpC) h hr0 hcA hrhs _
  have hdF : ∀ (l : Nat) (x : Expr),
      (blockRuleFieldFvs pp.toBlockShape (tgtRs out) c j)[l]? = some x →
        denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).getD l
              default) := by
    have hcd := blockCtorData_of_core hcore hcj
    obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr0
    exact (blockRuleFdomsAV_eq (hm := trivial) h hr0 hcA hrhs hcd hCf TE.nP_le ψ).2
  have hdoms : ∀ (q : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[q]? = some x →
      denoteMeta mpC.base2.acval fe.env ψ q (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).reverse.getD
              (rc.rP + cA.2 - 1 - q) default) := by
    intro q x hx
    have hq := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := fe.env)
      (ψ := ψ) (ihdoms := []) (fvsIh := []) hpl hfl rfl
      (openPisAtFvars_length _ Q.hpref) (openPisAtFvars_length _ Q.hfld) rfl
      (blockRulePdomsAV_reads hμ mpC h hr0 _ (by rw [← hrP]; exact Q.hpref))
      (by rw [hFldEq, hrP]; exact hdF)
      (fun l x hx => nomatch hx) q x (by simpa using hx)
    simpa using hq
  have hokPF := blockRuleHokPF_run hμ h hdR' hS hcore hmr c r0 trivial hr0 j cA hcA ψ
  have hokΔ : ∀ q, q < rc.rP + cA.2 → ∀ ρ' : Nat → V,
      Sat V (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).reverse ρ' →
      WellDenotedV V (fun l => ρ' (l + (rc.rP + cA.2 - 1 - q) + 1))
        ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).reverse.getD
              (rc.rP + cA.2 - 1 - q) default) := by
    intro q hq ρ' hsat
    have hk := blockRuleHokΔ_of (V := V) (ihdoms := []) hpl hfl rfl
      (fun l hl σ' ys hys => by
        have := hokPF l (by rw [← hrP]; simpa using hl) σ' ys (by simpa using hys)
        simpa using this) q (by simpa using hq) ρ' (by simpa using hsat)
    simpa using hk
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rc.rP + cA.2)
      = some ([], Expr.sort .zero) := rfl
  have hW := walkCtx_blockFrame (V := V) (mT := mpC.base2) (ψ := ψ) (ihdoms := []) (ihvals := [])
    Q.hpref Q.hfld h₃ hpl hfl rfl
    (by simpa using hdoms) (by simpa using hokΔ)
    (by simpa using hlbF) (by simpa using hcbF) (by simpa using hher) hsp (by simp [SpineFit])
  simp only [List.append_nil, List.reverse_nil, List.nil_append, consList_nil,
    Nat.add_zero] at hW
  -- the frame's two segments
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hfsl : fs.length = cA.2 := by
    have hsl := hsp.length_eq
    simp only [List.length_append, hpl, hfl] at hsl
    omega
  -- the called field is a field of the constructor
  have hfi : ih.field < cA.2 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hg : Q.fvsF.getD ih.field default = .bvar 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h0 := C.hfld
    rw [hg] at h0
    exact inferTypeCore_bvar_absurd' h0
  -- the field's abstract telescope through whnf
  obtain ⟨-, hallN⟩ := ConLeche.targetFieldNorms_run Q.hfnorm
  obtain ⟨t0, ht0, hrun0⟩ := hallN ih.field _ (List.getElem?_eq_getElem (by omega))
  have hfnorm : ConLeche.targetWhnfPis (ConLeche.fueledOps μ F) fe.env
      (rc.rP + cA.2 + (cvTas.map (·.type)).length)
      (ConLeche.whnfWalkFuel
        (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2))
          (Q.fvsF.getD ih.field default).fvarTypeD))
      (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
        (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2))
        (Q.fvsF.getD ih.field default).fvarTypeD) = .ok (Q.fnorm.getD ih.field default) := by
    have e1 : Q.fnorm.getD ih.field default = t0 := by
      rw [List.getD_eq_getElem?_getD, ht0]; rfl
    have e2 : Q.fvsF.getD ih.field default = Q.fvsF[ih.field]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [e1, e2]
    exact hrun0
  -- the formers
  have hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  -- the telescope's and the index arguments' leaves
  have hscope := targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hher hcbF hformerF
    (fun c' => (hRT3 c').1) hihMem
  have htL := hscope.2.2.2.2.2
  have hframeL : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := frame_leaves_mem hFr hher
  have hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
    rcases targetAbstract_entries (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs ih hihMem with h0 | h0
    · simp at h0
    · intro x hx l hl
      obtain ⟨y, hy, hly⟩ := fvarLeaves_instantiateList hFr Q.body hbf 0 l (h0 x hx l hl)
      exact hframeL y (List.mem_reverse.mp hy) l hly
  -- the call's shape
  obtain ⟨hidxLen, hrPc, hidxB⟩ : ih.idx.length + rc.rP
        = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0 ∧
      (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD ih.callee 0 = rc.rP ∧
      ∀ x ∈ ih.idx, x.looseBVarsBounded ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length
        = true := by
    rcases targetAbstract_callShape (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs ih hihMem with h0 | h0
    · simp at h0
    · exact h0
  -- the callee
  have hcal : ih.callee < (tgtRs out).length := by
    simpa [tgtFam] using targetCall_callee_lt C
  obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[ih.callee]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
  obtain ⟨-, hlenR, -⟩ := recStageG_recNames h
  have hcalR : ih.callee < pp.recs.length := by omega
  have hmIc : (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0
      = pp.toBlockShape.majorIdxAt ih.callee := by
    simp only [tgtFam, ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrPc' : pp.toBlockShape.rulePrefixAt ih.callee = rc.rP := by
    rw [← hrPc]
    simp only [tgtFam, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrecTy : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD ih.callee (.sort .zero)
      = r1.1.type := by
    simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr1]; rfl
  obtain ⟨hnPc, hmemk, hmI, -, -⟩ := blockRecMajor_run (hm := trivial) hμ mpC h hmr hr1 ψ
  obtain ⟨hnP0, -, -, -, -⟩ := blockRecMajor_run (hm := trivial) hμ mpC h hmr hr0 ψ
  obtain ⟨_, _, -, ⟨TE1⟩⟩ := ConLeche.recStage_tyAt h hr1
  have hdnP : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).nP
      = pp.toBlockShape.nP := hmr.1
  have hidxLen' : ih.idx.length
      = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).nIdxAt
          (pp.toBlockShape.recTgtAt ih.callee) := by
    rw [hmIc, hmI, hrPc'] at hidxLen; omega
  -- the call's major domain, opened
  have hmaj : ∀ os : List Expr, LocList (rc.rP + cA.2 + (cvTas.map (·.type)).length)
      ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length os →
      C.majDom.instantiateList os 0 = Expr.mkAppN
        (.const TE1.ms.cvT.name (pp.toBlockShape.lps.map .param))
        ((Q.fvsPref.take pp.toBlockShape.nP).map (·.instantiateList os 0)
          ++ ih.idx.map (·.instantiateList os 0)) := by
    intro os hos
    have hall := hos.allFvars
    have hoscl : ∀ o ∈ os, o.looseBVarsBounded 0 = true := by
      intro o ho; obtain ⟨i, ty, rfl⟩ := hall o ho; rfl
    have hprefF : ∀ x ∈ Q.fvsPref, ∃ i ty, x = Expr.fvar i ty := fun x hx =>
      hFr.mem_fvar (List.mem_reverse.mpr (List.mem_append_left _ hx))
    have hargsB : ∀ a ∈ Q.fvsPref ++ ih.idx, a.looseBVarsBounded os.length = true := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, ty, rfl⟩ := hprefF a ha; rfl
      · rw [hos.1]; exact hidxB a ha
    have hins := instPisAtLift_instantiateList hoscl (Q.fvsPref ++ ih.idx) hargsB
      (hRT3 ih.callee).2.1 C.hcallee
    rw [C.hmajDom, hrecTy] at hins
    simp only [Expr.instantiateList] at hins
    have hclA : ∀ a ∈ (Q.fvsPref ++ ih.idx).map (·.instantiateList os 0),
        a.looseBVarsBounded 0 = true := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact looseBVarsBounded_instantiateList_allFvars hall b 0
        (by simpa using hargsB b hb)
    have hlenA : ((Q.fvsPref ++ ih.idx).map (·.instantiateList os 0)).length
        = pp.toBlockShape.majorIdxAt ih.callee := by
      rw [List.length_map, List.length_append, hlp, ← hmIc]; omega
    obtain ⟨ms, body, bm', hms, heq⟩ := tgtMajDom_open (hm := trivial) h hr1 hclA hlenA hins
    obtain rfl : ms = TE1.ms := Option.some.inj (hms.symm.trans TE1.hms)
    injection heq with hdom
    rw [hdom, List.map_append, List.take_append_of_le_length (by rw [List.length_map, hlp]; omega),
      hrPc', List.drop_append_of_le_length (by simp [hlp]),
      List.drop_eq_nil_of_le (by simp [hlp]), List.nil_append, List.map_take]
  -- the callee's member: its hole and its former
  generalize htdef : pp.toBlockShape.recTgtAt ih.callee = t at *
  have hnd' : pp.toBlockShape.memberNames.Nodup := hnd
  have hI : pp.toBlockShape.memberNames.findIdx? (· == TE1.ms.cvT.name) = some t := by
    refine findIdx?_of_nodup hnd' ?_
    simp [ConLeche.BlockShape.memberNames, List.getElem?_map, ← htdef, TE1.hms]
  have hkN := hN.2.2
  have htk : t < (cvTas.map (fun cv : ConstantVal => cv.type)).length := by rw [List.length_map, hkN]; exact hmemk
  obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by simpa using htk)⟩
  obtain ⟨-, -, -, -, -, hFD⟩ := hmr.2.2.2.1 t cvTb hcvTb
  have hgetT : (cvTas.map (fun cv : ConstantVal => cv.type)).getD t default = cvTb.type := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcvTb]; rfl
  have hTt : denoteMeta mpC.base2.acval fe.env ψ 0 ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t default)
      = some (mkPisAV ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ)
          (.sort ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).resSort.eval
            ψ))) := by
    rw [hgetT]; exact hFD.read ψ
  have hpdsLen : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ).length
      = pp.toBlockShape.nP + ih.idx.length := by
    rw [hFD.len ψ, hdnP, hidxLen']
  -- the holes' values at their formers' types
  have hformerG : ∀ t', t' < (cvTas.map (fun cv : ConstantVal => cv.type)).length →
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).hasFvar = false ∧
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).looseBVarsBounded 0 = true ∧
      ConstsBound fe.env ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default) ∧
      ∃ T : AnnotTerm, denoteMeta mpC.base2.acval fe.env ψ 0 ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default)
          = some T ∧ (∀ σ : Nat → V, WellDenotedV V σ T) ∧
        ∀ σ : Nat → V, hv.getD t' pt ∈ˢ interp V σ T := by
    intro t' ht'
    have ht'' : t' < cvTas.length := by simpa using ht'
    obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t']? = some cv := ⟨_, List.getElem?_eq_getElem ht''⟩
    obtain ⟨-, -, ⟨caps, hfind⟩, hfv, hbv, hFD'⟩ := hmr.2.2.2.1 t' cv hcv
    have hg : (cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default = cv.type := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcv]; rfl
    have hwf := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
    obtain ⟨T', hT', hmemT'⟩ := hvTy t' ht''
    have hgc : (cvTas.getD t' default).type = cv.type := by
      rw [List.getD_eq_getElem?_getD, hcv]; rfl
    rw [hgc, hFD'.read ψ] at hT'
    obtain rfl := Option.some.inj hT'
    have hcl := bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hfv) hbv
      (hFD'.read ψ)
    rw [hg]
    exact ⟨hfv, hbv, constsBound_of_constsResolve _ hwf.2.2.1, _, hFD'.read ψ, hFD'.okTy ψ,
      fun σ => by rw [interp_closed V hcl σ ρ]; exact hmemT'⟩
  -- the frame data, in the rule data's spelling
  have hFF : tgtFieldFvs pp.toBlockShape out c j = Q.fvsF := congrArg (·.fields) hFrEq
  have hTel : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type)) out c j).teles
      = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hiiG : ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + (cvTas.map (fun cv : ConstantVal => cv.type)).length)
        (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (fun cv : ConstantVal => cv.type)) (rc.rP + cA.2))
          (Q.fvsF.getD ih.field default).fvarTypeD) = some Aty →
      fs.getD ih.field pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty := by
    intro Aty hA
    rw [← consList_append]
    refine hii Aty ?_
    rw [tgtAbsM, hB, hFF, List.length_map] at *
    exact hA
  have hbs' : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval fe.env ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))).getD []) bs := by
    have := hbs
    simp only [tgtTlA, tgtTeleTys] at this
    rw [hih, hTel, hB, List.map_map] at this
    simpa [Function.comp_def] using this
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨hspP, hmemF⟩ := targetCall_gen hμ hacl (Rules.RulesInputs.ofSem mpC ψ) C hfnorm hlp hlf
    hFr hxl hfsl hW hfi htL hidxL (by rw [hvl, List.length_map]) hformerG hiiG
    (nP := pp.toBlockShape.nP) (by rw [← hdnP, hrP]; exact hnP0) ((hRT3 ih.callee).1) hmaj hI htk hTt
    (hFD.bits ψ) hpdsLen bs hbs'
  have hFF' : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
      out c j).fields = Q.fvsF := congrArg (·.fields) hFrEq
  have hEis : (tgtEisA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
        out mpC.base2.acval fe.env ψ c j r).map
        (interp V (consList bs (consList (xs ++ fs) ρ)))
      = ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval fe.env ψ
            (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
            (x.instantiateList (locOpen (rc.rP + cA.2)
              ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length) 0)).getD default)) := by
    simp only [tgtEisA, tgtTeleTys]
    rw [hih, hTel, hB, List.length_map, List.map_map]
    rfl
  have hFap : interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type)) out
          mpC.base2.acval fe.env ψ c j r)
      = interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval fe.env ψ
            (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
            ((Expr.mkAppN (Q.fvsF.getD ih.field default)
              (ConLeche.structTeleVars ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)).instantiateList
              (locOpen (rc.rP + cA.2) ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
                0)).getD default) := by
    simp only [tgtFapA, tgtTeleTys]
    rw [hih, hTel, hB, hFF', List.length_map]
  rw [hEis, hFap]
  -- the parameters and the member's index telescope
  generalize hE : ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
      ((denoteMeta mpC.base2.acval fe.env ψ
        (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
        (x.instantiateList (locOpen (rc.rP + cA.2)
          ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length) 0)).getD default)) = E
    at hspP hmemF ⊢
  have hsplitP : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ).map
        (·.2.2)
      = (((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ).take
          pp.toBlockShape.nP).map (·.2.2)
        ++ (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).IdsM t ψ := by
    rw [BlockData.IdsM, hdnP, ← List.map_append, List.take_append_drop]
  rw [hsplitP] at hspP
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_split hspP
  have hl1 : as₁.length = (xs.take pp.toBlockShape.nP).length := by
    rw [h1.length_eq, List.length_map, List.length_take, List.length_take, hFD.len ψ, hdnP, hxl]
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl1
  rw [← hdnP] at h2 hmemF
  exact ⟨h2, hmemF⟩

/-- **A target call's target, at a valuation of the holes.**  At the
`(c, j)`-th rule, a frame the prefix and the fields fit (`hsp`), a
valuation `hv` of the member holes at their formers' types (`hvTy`),
under which the callee's member hole applied to the parameters and a
fitting index spine is `Y` at the index tuple (`hlaw`), and in which the
called field lies in its member-abstracted type's reading (`hii`): at
every spine `bs` of the call's telescope, the call's index readings
form an index tuple of the callee's member and the applied field lies
in `Y` there. -/
theorem tgtCall_core (hμ : μ.verifiedChecks = true)
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
    (hv : List V) (hvl : hv.length = cvTas.length)
    (hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T)
    (Y : V)
    (hlaw : ∀ is : List V,
      SpineFit (consList (xs.take d.nP) ρ)
        (d.IdsM (pp.toBlockShape.recTgtAt
          ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).callee) ψ) is →
      (xs.take d.nP ++ is).foldl SetTheory.app
          (hv.getD (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
              default).callee) pt)
        = app Y (d.tup ψ (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
              default).callee) is))
    (hii : ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ
          (tgtB pp.toBlockShape out c j + cvTas.length)
          (tgtAbsM pp.toBlockShape (cvTas.map (·.type)) out c j
            ((tgtFieldFvs pp.toBlockShape out c j).getD
              ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
                default).field default).fvarTypeD) = some Aty →
      fs.getD ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).field pt
        ∈ˢ interp V (consList (xs ++ fs ++ hv) ρ) Aty)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ
        c j r).map (·.2.2)) bs) :
    d.tup ψ (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee)
      ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env
        ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ))))
      ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env
          ψ c j r)
      ∈ˢ app Y (d.tup ψ (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee)
        ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          fe.env ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ))))) := by
  obtain ⟨h2, hmemF⟩ := tgtCall_coreFit hμ h R hdR hN hS hcore hmr hM hnd ψ ρ hc hj hsp hxs
    hr hv hvl hvTy hii bs hbs
  refine ⟨tupW_mem h2, ?_⟩
  rw [← hlaw _ h2]
  exact hmemF

end Core

end ConLeche.Model
