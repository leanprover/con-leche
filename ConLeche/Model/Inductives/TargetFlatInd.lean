module

import ConLeche.Model.Inductives.TargetFlatLand
import ConLeche.Model.Inductives.TargetFlatView
public import ConLeche.Model.Inductives.TargetRank
import ConLeche.Model.Inductives.TargetClassFrame
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Verify.Inductives.RecStage

public section

/-!
# The class induction on the route off the walk (PRIMREC, lanes FLATHOME, MEMBER)

`tgtClassInd_of_route`: at a family on the route (`targetRouteOf`),
the induction over the recursor classes, layer by layer along the call
graph's rank (`graphInd_of_layers`, `layerStep_of_der`).  A layer's
elements all have derivations along the calls inside the layer
(`tgtFlat_der`): the route puts every edge inside a cycle between two
classes of ONE home — the installing block's own members, or an older
block's members, at one instance — so, every class read at its home's
record (`tgtCls_view`, `TargetFlatView.lean`), a class's elements are
derived by its HOME's lfp induction at the class's frame, member and
outside classes alike — the stage tuple is the carrier separated by "derivable at every
class of the layer standing for this component", and a call around the
cycle lands in the stage (`tgtCall_flatFit`).
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

section Flat

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- The family's rank, as the checker computes it. -/
@[expose] def tgtRank (p : BlockShape) : Nat → Nat :=
  fun c => (ConLeche.graphRank (ConLeche.targetGraphOf p)).getD c 0

set_option maxHeartbeats 16000000 in
/-- **Every element of a layer's class has a derivation along the calls
inside the layer** (see the module docstring). -/
theorem tgtFlat_der (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC d.toLfp (tgtMajor out c).ind)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some (d.ctorsM c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    {names : List Name} (hM : BlockModelAt mpC.base2 names d)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hfl : ConLeche.targetRouteOf pp.toBlockShape (out.map (·.2.1)) = true)
    (ψ : Name → Nat) (ρ : Nat → V) (n : Nat)
    (hcold : ConLeche.targetHot pp.toBlockShape (out.map (·.2.1)) n = false) :
    ∀ xs c, c < (tgtRs out).length → tgtRank pp.toBlockShape c = n →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ y, y ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) t →
        Der (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (injX := tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (nCt := blockRecNCt (tgtRs out))
          (K := (tgtRs out).length)
          (fit := tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (call := tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
          xs (fun c' => tgtRank pp.toBlockShape c' = n) (tagged c t y) := by
  intro xs c hc hrc t ht y hy
  -- the route: an edge inside a layer joins classes of one home, at one instance
  have hroute : ∀ c', c' < (tgtRs out).length → tgtRank pp.toBlockShape c' = n →
      ∀ j, j < blockRecNCt (tgtRs out) c' →
      ∀ fs c'' t'' y'',
      tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c' j fs (tagged c'' t'' y'') →
      tgtRank pp.toBlockShape c'' = tgtRank pp.toBlockShape c' →
      (tgtMajor out c').member.isNone = (tgtMajor out c'').member.isNone ∧
        (tgtMajor out c').home.contains (tgtMajor out c'').ind = true ∧
        (tgtMajor out c'').lvls = (tgtMajor out c').lvls ∧
        (tgtMajor out c'').ds = (tgtMajor out c').ds := by
    intro c' hc' hrn j hj fs c'' t'' y'' hcall hrr
    obtain ⟨hcg, -, he⟩ := tgtCallee_edge h R hc' hj (tgtCall_callee hcall)
    have := ConLeche.targetHot_false_edge hcold hcg he hrn (hrr.trans hrn)
    have hgm : ∀ e, (out.map (·.2.1)).getD e default = tgtMajor out e := by
      intro e
      simp only [tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases out[e]? <;> rfl
    simpa only [hgm] using this
  -- the class's home, instantiation and component
  obtain ⟨cvI, hcl, -, -, -, -, -, -, -, hguard⟩ :=
    tgtCls_view hμ hcov h R hcls hdR hN hcore hctorsAs hmr hlfp ψ hc
  obtain ⟨-, -, hsat, htI⟩ := hguard ρ xs t ht
  have hL := mpC.lfpClause_of_mem hcl.hD
  generalize hD0 : tgtClsD d Dc out c = D at *
  generalize hψ0 : tgtClsψ cvc out ψ c = ψ0 at *
  generalize hρp : tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c = ρp at *
  generalize hm0 : tgtClsM mc pp.toBlockShape out c = m0 at *
  have hy' : y ∈ˢ app (D.carrier ψ0 ρp m0) t := by
    rw [← hD0, ← hψ0, ← hρp, ← hm0]; exact hy
  have hmN : m0 < D.N := Nat.lt_of_lt_of_le hcl.hmm hL.kN
  -- the stage's predicate: derivable at every class of the layer standing for the component
  let P : Nat → V → V → Prop := fun m i x => ∀ c', c' < (tgtRs out).length →
    tgtRank pp.toBlockShape c' = n → tgtClsD d Dc out c' = D → tgtClsψ cvc out ψ c' = ψ0 →
    tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c' = ρp →
    tgtClsM mc pp.toBlockShape out c' = m →
    i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c' →
    Der (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
      (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
      (injX := tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (nCt := blockRecNCt (tgtRs out))
      (K := (tgtRs out).length)
      (fit := tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
      (call := tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
      xs (fun c' => tgtRank pp.toBlockShape c' = n) (tagged c' i x)
  obtain ⟨hmono, -, hclo⟩ := hL.functor ψ0 ρp hsat
  have hind := lfpTuple_induction hclo hmono P ?step m0 hmN t htI y hy'
  · exact hind c hc hrc hD0 hψ0 hρp hm0 ht
  case step =>
    intro m hm i hi x hx c' hc' hrc' hD' hψ' hfr' hm' hi'
    subst hm'
    generalize hSdef : sepTuple (D.w ψ0) D.N (D.idx ψ0 ρp) (D.Φ ψ0 ρp) P = S at hx
    have hSmem : InTupleSpace (D.w ψ0) D.N (D.idx ψ0 ρp) S := by
      rw [← hSdef]; exact sepTuple_mem _ _ _ _ _
    have hSle : TupleLe D.N (D.idx ψ0 ρp) S (D.carrier ψ0 ρp) := by
      rw [← hSdef]; exact sepTuple_le _ _ _ _ _
    obtain ⟨j, fs, hHF, rfl⟩ :=
      (hL.fibre ψ0 ρp hsat S hSmem (tgtClsM mc pp.toBlockShape out c') hm i hi x).mp hx
    have hHFc : D.HFits ψ0 ρp (D.carrier ψ0 ρp) i (tgtClsM mc pp.toBlockShape out c') j fs :=
      hL.fitsMono ψ0 ρp hsat S _ hSmem (lfpTuple_mem _ _ _ _) hSle _ hm i j fs hHF
    have hinC : D.inj ψ0 (tgtClsM mc pp.toBlockShape out c') j fs
        ∈ˢ app (D.carrier ψ0 ρp (tgtClsM mc pp.toBlockShape out c')) i := by
      rw [← hL.carrier_eq hsat hm]
      exact (hL.fibre ψ0 ρp hsat _ (lfpTuple_mem _ _ _ _) _ hm i hi _).mpr ⟨j, fs, hHFc, rfl⟩
    have hinj : tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c' j fs
        = D.inj ψ0 (tgtClsM mc pp.toBlockShape out c') j fs := by
      rw [tgtClsInj, hD', hψ']
    rw [← hinj]
    obtain ⟨cvI', hcl', hψc', hhome', hdsLen', hul', hdsa', hlenP', -, hguard'⟩ :=
      tgtCls_view hμ hcov h R hcls hdR hN hcore hctorsAs hmr hlfp ψ hc'
    obtain ⟨-, hFr', hsat', -⟩ := hguard' ρ xs i hi'
    have hr' : (tgtRs out)[c']? = some (tgtRs out)[c'] := List.getElem?_eq_getElem hc'
    have hj : j < blockRecNCt (tgtRs out) c' := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr', Option.getD_some, tgtRs_ctors hr',
        hcl'.hlen, hD']
      exact hHF.1
    have hfitC : tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c' i j fs := by
      rw [tgtClsFit, hD', hψ', hfr']; exact hHFc
    refine Der.mk hc' hrc' hi' (by rw [hinj, tgtClsCr, hD', hψ', hfr']; exact hinC) hj
      hfitC ?calls
    case calls =>
    intro c'' t'' y'' hS'' ht'' hy'' hcall
    have hcallC := hcall
    obtain ⟨key, hkey, bs, hbs, heq⟩ := hcall
    simp only [tgtKeys, List.mem_map, List.mem_range] at hkey
    obtain ⟨q, hq, rfl⟩ := hkey
    obtain ⟨hc''eq, hteq, hyeq⟩ := tagged_inj heq
    dsimp only at hteq hyeq
    obtain ⟨hmn, hhomeC, hlvC, hdsC⟩ :=
      hroute c' hc' hrc' j hj fs c'' t'' y'' hcallC (hS''.trans hrc'.symm)
    subst hc''eq
    generalize hcal : ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c'
      j).getD q default).callee = c'' at *
    -- the caller's rule, its frame and its walk context
    obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc' hj
    obtain ⟨rc, rhs0, Q, hrP, -, -, hB, hFrEq, hAbs, hbf, hTf, hTb, hTc, hle, hRT3, hdsOk, hCf,
      hCb, hCc, hfdl, hF, hokPF⟩ := tgtFrame_cls hμ hcov h R hcls hdR hS hcore hmr ψ hc' hr' hcA hrhs
    have hspF := tgtCls_hspF hμ hcov h R hcls hdR hcore hmr hM ψ ρ 0 xs c' hc' j hj i fs hi' hfitC
    rw [tgtFdomsK, liftDomsK_zero] at hspF
    have hpre := tgtClsIs_pref hi'
    have hxs : xs.length = pp.toBlockShape.rulePrefixAt c' :=
      hpre.length_eq.trans (blockRulePdomsAV_length hμ mpC h hr' ψ)
    have hxl : xs.length = rc.rP := by rw [hxs, hrP]
    have hfsl : fs.length = cA.2 := by
      have hsl := hspF.length_eq
      simp only [List.length_append, blockRulePdomsAV_length hμ mpC h hr' ψ, hfdl] at hsl
      rw [hxs] at hsl; omega
    have hW := tgtFrame_walk hμ h ψ hr' Q hrP hTf hTb hTc hdsOk hCf hCb hCc hfdl hF hokPF hspF
    have hRPc : tgtRP pp.toBlockShape c' = rc.rP := by
      rw [hrP]; rfl
    rw [hRPc] at hdsa'
    obtain ⟨hiD, hfc0, hlpsI, hlpsC⟩ := hcl'.ctor_at (i := j) (cA := cA)
      (by rw [← tgtRs_ctors hr']; exact hcA)
    have hlps' : ∀ mm', mm' < (tgtClsD d Dc out c').k → ∃ cv caps,
        envC.find? ((tgtClsD d Dc out c').member mm') = some (.indInfo cv caps) ∧
        cv.levelParams = cvI'.levelParams := by
      intro mm' hmm'
      obtain ⟨cv, caps, hf, hl⟩ := hlpsC mm' hmm'
      exact ⟨cv, caps, hf, hl.trans hlpsI.symm⟩
    have hfc : envC.find? ((tgtClsD d Dc out c').ctorName (tgtClsM mc pp.toBlockShape out c') j)
        = some (.ctorInfo cA.1 (tgtMajor out c').ds.length cA.2) := by
      rw [hdsLen']; exact hfc0
    -- the callee: a class of the same home, instantiation and level
    have hc'' : c'' < (tgtRs out).length := by
      have := (tgtCallee_edge h R hc' hj (tgtCall_callee hcallC)).2.1
      have hlenR := (ConLeche.recStageG_recNames h).2.1
      simp only [ConLeche.targetCallGraph, List.length_map] at this
      omega
    have hr'' : (tgtRs out)[c'']? = some (tgtRs out)[c''] := List.getElem?_eq_getElem hc''
    obtain ⟨cvI'', hcl'', hψc'', -, -, -, -, -, hids'', hguard''⟩ :=
      tgtCls_view hμ hcov h R hcls hdR hN hcore hctorsAs hmr hlfp ψ hc''
    have hE1 : tgtClsD d Dc out c'' = tgtClsD d Dc out c' :=
      tgtClsD_edge hcov hcls hsel hc' hc'' hmn hhomeC hhome'
    have hE4 : tgtClsM mc pp.toBlockShape out c''
        = (tgtClsD d Dc out c').names.idxOf (tgtMajor out c'').ind := by
      have := hcl''.hmem
      rw [hE1] at this
      rw [← this, idxOf_member hcl'.hnN hcl'.hkN (by have := hcl''.hmm; rwa [hE1] at this)]
    have hE2 : tgtClsψ cvc out ψ c'' = tgtClsψ cvc out ψ c' := by
      rw [hψc'', hψc']
      obtain ⟨caps'', hf''⟩ := hcl''.hfind
      have hmm'' : tgtClsM mc pp.toBlockShape out c'' < (tgtClsD d Dc out c').k := by
        have := hcl''.hmm; rwa [hE1] at this
      obtain ⟨cv, caps, hf, hl⟩ := hlps' _ hmm''
      have hm'' : (tgtClsD d Dc out c').member (tgtClsM mc pp.toBlockShape out c'')
          = (tgtMajor out c'').ind := by
        have := hcl''.hmem; rwa [hE1] at this
      rw [hm'', hf''] at hf
      obtain ⟨rfl, rfl⟩ : cvI'' = cv ∧ caps'' = caps := by simpa using hf
      rw [hl, hlvC]
    -- the call's entry and shape
    have hIhL : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c' j
        = Q.ihs.toList := by rw [tgtIhL, ← hAbs]
    have hihMem : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c' j).getD q
        default ∈ Q.ihs.toList := by rw [← hIhL]; exact ConLeche.getD_mem hq
    obtain ⟨hidxLen, hrPc, -⟩ := tgtIh_callShape Q hle hihMem
    rw [hcal] at hidxLen hrPc
    obtain ⟨hmIc, hrPe, -⟩ := tgtFam_at h hr''
    have hRP'' : tgtRP pp.toBlockShape c'' = rc.rP := by
      rw [← hrPc, hrPe]; rfl
    have hE3 : tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c''
        = tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c' := by
      rw [(hguard'' ρ xs t'' ht'').2.1, hFr']
      unfold tgtOutDsa
      rw [hRP'', hRPc, hdsC]
    -- the callee's index count is the call's
    obtain ⟨rc'', u'', hrc'', ⟨E''⟩⟩ := targetEntryAt R hr''
    have hidsLen := hids''
    rw [hE1, hE4, hE2] at hidsLen
    have hnIdx : (tgtMajor out c'').nIdx
        = ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c' j).getD q
          default).idx.length := by
      have h1 := E''.hmI
      have h2 : pp.toBlockShape.majorIdxAt c'' = rc''.mI := by
        rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc'', Option.getD_some]
      have h3 : pp.toBlockShape.rulePrefixAt c'' = rc''.rP := by
        rw [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc'', Option.getD_some]
      rw [hmIc, h2] at hidxLen
      rw [hrPe, h3] at hrPc
      omega
    rw [hnIdx] at hidsLen
    -- the family is on the route: its ranks, and the caller's position
    have hrk : (tgtFam pp.toBlockShape out).ranks
        = some (ConLeche.graphRank (ConLeche.targetGraphOf pp.toBlockShape)) := by
      unfold tgtFam; simp [hfl]
    have hname : ConLeche.nameIdxOf? (tgtFam pp.toBlockShape out).recNames
        ((tgtRs out)[c']).1.name = some c' := by
      obtain ⟨-, hlenR, hallN⟩ := ConLeche.recStageG_recNames h
      obtain ⟨rcN, rN, hrcN, hrN, hnm, -⟩ := hallN c' (by omega)
      rw [hr'] at hrN
      obtain rfl := Option.some.inj hrN
      have hnd := ConLeche.targetRecPins_nodup R.pins
      have := ConLeche.nameIdxOf?_of_nodup hnd (c := c') (by simp; omega)
      have hg : (pp.toBlockShape.recs.map (·.cvR.name)).getD c' default = rcN.cvR.name := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, hrcN]
      rw [hg] at this
      simp only [tgtFam]
      rw [hnm]
      exact this
    have hrank : (ConLeche.graphRank (ConLeche.targetGraphOf pp.toBlockShape)).getD
        ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c' j).getD q
          default).callee 0
        = (ConLeche.graphRank (ConLeche.targetGraphOf pp.toBlockShape)).getD
          ((ConLeche.nameIdxOf? (tgtFam pp.toBlockShape out).recNames
            ((tgtRs out)[c']).1.name).getD 0) 0 := by
      rw [hname, Option.getD_some, hcal]
      exact hS''.trans hrc'.symm
    -- the caller carries no home normal forms (its layer is not hot)
    have hMh : (tgtMajor out c').homeNfs = none := by
      have hgm : (out.map (·.2.1)).getD c' default = tgtMajor out c' := by
        simp only [tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases out[c']? <;> rfl
      have := ConLeche.targetRouteOf_homeNfs hfl (c := c') (by simpa [tgtRs] using hc')
      rw [hgm, show (ConLeche.graphRank (ConLeche.targetGraphOf pp.toBlockShape)).getD c' 0 = n
        from hrc', hcold] at this
      simpa using this
    -- the stage, at the caller's class
    subst hD' hψ' hfr'
    have hsatK := hsat'
    rw [hψc', hFr', hRPc] at hsatK
    have hSmemK := hSmem
    rw [hψc', hFr', hRPc] at hSmemK
    have hHFK := hHF.2.1
    rw [hψc', hFr', hRPc] at hHFK
    obtain ⟨-, hmemL⟩ := tgtCall_flatFit hμ ψ ρ Q hdsOk hCf hCb hCc hbf hTf hTb hTc hle hRT3
      hB hFrEq hAbs hW hxl hfsl hcl' hhome' hiD hfc hlps' hul' hmr.formers_noFvar hdsa'
      (by rw [← hψc']; exact hlenP') hsatK hSmemK hHFK hq hrk hrank hMh (by
        rw [hcal]; rw [hψc'] at hidsLen; exact hidsLen) bs hbs
    rw [hcal, ← hψc'] at hmemL
    -- the target is the callee's element at the stage: the predicate holds there
    have hkey : t'' = tupW ((tgtClsD d Dc out c').u
        ((tgtClsD d Dc out c').names.idxOf (tgtMajor out c'').ind) (tgtClsψ cvc out ψ c'))
        ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c' j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))) := by
      rw [hteq, tgtClsTup, tgtClsU, hE1, hE4, hE2]
    have htI'' := (hguard'' ρ xs t'' ht'').2.2.2
    rw [hE1, hE2, hE3, hE4, hkey] at htI''
    have hSm := hmemL
    rw [← hSdef] at hSm
    unfold sepTuple at hSm
    rw [app_graph htI'', mem_sep] at hSm
    rw [hyeq, hkey]
    exact hSm.2 c'' hc'' hS'' hE1 hE2 hE3 hE4 (by rw [← hkey]; exact ht'')

/-- **`TgtClassInd` on the route off the walk** (`targetRouteOf`): the
layers along the family's rank, each inductive from its derivations
(`layerStep_of_der`) — a layer that is not hot by `tgtFlat_der`, a hot
one by the derivations `hhot` supplies (lane NESTHOME's home table); the
calls never climb the rank (`tgtCall_rank_le`). -/
theorem tgtClassInd_of_route (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC d.toLfp (tgtMajor out c).ind)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some (d.ctorsM c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    {names : List Name} (hM : BlockModelAt mpC.base2 names d)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hfl : ConLeche.targetRouteOf pp.toBlockShape (out.map (·.2.1)) = true)
    (ψ : Name → Nat) (ρ : Nat → V)
    (hhot : ∀ n, ConLeche.targetHot pp.toBlockShape (out.map (·.2.1)) n = true →
      ∀ xs c, c < (tgtRs out).length → tgtRank pp.toBlockShape c = n →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ y, y ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) t →
        Der (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (injX := tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (nCt := blockRecNCt (tgtRs out))
          (K := (tgtRs out).length)
          (fit := tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (call := tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
          xs (fun c' => tgtRank pp.toBlockShape c' = n) (tagged c t y)) :
    TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTas.map (·.type)) out d Dc mc cvc
      ψ ρ :=
  graphInd_of_layers (r := tgtRank pp.toBlockShape) fun n =>
    layerStep_of_der
      (fun _ c hc hrc j hj _ _ _ _ hcall => by
        rw [← hrc]; exact tgtCall_rank_le h R hc hj hcall)
      (by
        cases hn : ConLeche.targetHot pp.toBlockShape (out.map (·.2.1)) n
        · exact tgtFlat_der hμ hcov h R hcls hsel hdR hN hS hcore hctorsAs hmr hM hlfp hfl ψ ρ n hn
        · exact hhot n hn)

end Flat

end ConLeche.Model
