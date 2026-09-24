module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetIndTransport
import ConLeche.Model.Inductives.BlockRecGraph
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.StructBits

public section

/-!
# The target recursor model's rows: the induction (B4): the calls at the SEPARATED tuple (lane RECLIB)

A row of `tgtRecPre_graph` (`TargetGraph.lean`), stated at the target
check's data (`TargetIhData.lean`).
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
theorem inferTypeCore_bvar_absurd {mode : CheckMode} {env : Env} {F d i : Nat} {t : Expr}
    (h : ConLeche.inferTypeCore mode env F d (.bvar i) = .ok t) : False := by
  cases F with
  | zero =>
    simp [ConLeche.inferTypeCore, ConLeche.pureFns, ConLeche.coreKnot, throw, throwThe,
      MonadExceptOf.throw] at h
  | succ F => exact ConLeche.Rules.inferTypeCore_bvar_inv h

section Rows

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

/-- **Row: the induction** (B4) — from the recorded lfp clause, class
agnostic: at a call, the field's typing on the member-abstracted terms
(K1) at the hole valuation of the SEPARATED tuple puts the call's
target in the property. -/
theorem tgtGraphInd_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTas ctorsAs (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hC : LfpClause mpC.base2.acval d.toLfp)
    (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet (tgtRs out).length (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt xs) (blockRecCr d ψ ρ pp.toBlockShape.recTgtAt xs) →
        (∃ e, blockGraphDecF d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt (blockRecNCt (tgtRs out)) (tgtRs out).length
            (blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt) xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt (tgtRs out).length (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ d ρ) xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet (tgtRs out).length (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt xs) (blockRecCr d ψ ρ pp.toBlockShape.recTgtAt xs) →
        P u := by
  intro P hP u hu
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r →
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  generalize hdd : blockDataOf V pp.toBlockShape env₀ ctorsAs pk uOfD ppsOf = d at *
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain ⟨hparFit, -⟩ := blockRecIs_fits hi
  have hsat := d.satOfSpine hparFit
  have hmK : ∀ c', c' < (tgtRs out).length → pp.toBlockShape.recTgtAt c' < d.k := fun c' hc' =>
    (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc') ψ).2.1
  have hmN : ∀ c', c' < (tgtRs out).length → pp.toBlockShape.recTgtAt c' < d.N := fun c' hc' =>
    Nat.lt_of_lt_of_le (hmK c' hc') (Nat.le_add_right _ _)
  -- the property, per MEMBER: every class of it, at every major
  let P' : Nat → V → V → Prop := fun m t y => ∀ c', c' < (tgtRs out).length →
    pp.toBlockShape.recTgtAt c' = m →
    tagged c' t y ∈ˢ unionSet (tgtRs out).length
      (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
        pp.toBlockShape.recTgtAt xs)
      (blockRecCr d ψ ρ pp.toBlockShape.recTgtAt xs) →
    P (tagged c' t y)
  obtain ⟨hparI, hprefI⟩ := blockRecIs_fits hi
  rw [blockRecIs_pos hparI hprefI] at hi
  refine hC.ind hsat P' ?_ (pp.toBlockShape.recTgtAt c) (hmN c hc) i hi x hx c hc rfl hu
  intro m _ t ht j fs hfitS c' hc' hmem hu'
  subst hmem
  have hjl : j < (d.ctorsM (pp.toBlockShape.recTgtAt c')).length := hfitS.1
  obtain ⟨-, htI, -⟩ := tagged_mem_unionSet_iff.mp hu'
  obtain ⟨hpar', hpref'⟩ := blockRecIs_fits htI
  rw [blockRecIs_pos hpar' hpref'] at htI
  have hr : (tgtRs out)[c']? = some (tgtRs out)[c'] := List.getElem?_eq_getElem hc'
  have hjr : j < (tgtRs out)[c'].2.2.2.length := by rw [← hctM c' _ hr]; exact hjl
  obtain ⟨cA, hcA⟩ : ∃ cA, (tgtRs out)[c'].2.2.2[j]? = some cA :=
    ⟨_, List.getElem?_eq_getElem hjr⟩
  have hcj : (d.ctorsM (pp.toBlockShape.recTgtAt c'))[j]? = some cA := by
    rw [hctM c' _ hr]; exact hcA
  have hmemk := (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 _ j cA hcj
  -- the fields fit at the CARRIER (the hole fit grows with the tuple), there
  -- as stored (the override law)
  have hfitH : blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt xs c' t j fs :=
    hC.fitsMono ψ _ hsat _ _ (sepTuple_mem _ _ _ _ P') (lfpTuple_mem _ _ _ _)
      (sepTuple_le _ _ _ _ _) _ (hmN c' hc') t j fs hfitS
  have hfitC := (hM.carrier ψ _ hsat _ (hmN c' hc') t htI j fs).mp hfitH
  have hsepH := hfitS
  have hjn : j < blockRecNCt (tgtRs out) c' := by
    rw [← (blockRecNCt_seam (V := V) (env₀ := env₀) (pk := pk) (uOfD := uOfD)
      (ppsOf := ppsOf) h c' hc').1, hdd]; exact hjl
  refine hP _ hu' ⟨(c', j, fs), ⟨hc', hjn, t, ?_, hfitH, rfl⟩, fun v hv => ?_⟩
  · rw [blockRecIs_pos hpar' hpref']; exact htI
  obtain ⟨hvU, key, hkm, bs, hbs, rfl⟩ := mem_blockGraphPred.mp hv
  -- the key: an `ih` variable of the rule and its callee
  obtain ⟨r, hrl, rfl⟩ : ∃ r, r < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type))
      (tgtRs out) c' j).length ∧ key = (r, ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type))
        (tgtRs out) c' j).getD r default).callee) := by
    simp only [tgtKeys, List.mem_map, List.mem_range] at hkm
    obtain ⟨r, hr, rfl⟩ := hkm
    exact ⟨r, hr, rfl⟩
  obtain ⟨hcal, -, -⟩ := tagged_mem_unionSet_iff.mp hvU
  -- the rule's prefix and fields fit (a slot read: `blockKitSpF_run`)
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, (tgtRs out)[c'].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  have hspF := blockKitSpF_run hμ h hcore hmr hmr.1 hctM ψ hbnd ρ
    (tgtRs out).length xs c' hc' hpar' hpref' j hjn t fs htI hfitC
  rw [blockRecFdomsK_eq_of_bounded hbnd hr hcA hrhs] at hspF
  have hxs : xs.length = pp.toBlockShape.rulePrefixAt c' :=
    hpref'.length_eq.trans (blockRulePdomsAV_length hμ mpC h hr ψ)
  have hfsl : fs.length = cA.2 := by
    obtain ⟨xs₁, fs₁, heq, h1, hfsR⟩ := spineFit_append_split hspF
    have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hpref'.length_eq]
    obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
    rw [hfsR.length_eq, blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ]
  -- the called field is a field of the constructor
  obtain ⟨rc, rhs0, M, Q, -, -, -, -, -, -, -, hAbs, -, -⟩ := targetRuleAt R hr hcA hrhs
  have hihMem : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c' j).getD r
      default ∈ Q.ihs.toList := by
    have hl : Q.ihs.toList = tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c' j := by
      rw [tgtIhL, ← hAbs]
    rw [hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl, Option.getD_some]
    exact List.getElem_mem hrl
  obtain ⟨C⟩ := Q.call hihMem
  have hfi : ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c' j).getD r
      default).field < cA.2 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hlenF : Q.fvsF.length = cA.2 := ConLeche.Model.openPisAtFvars_length _ Q.hfld
    have hg : Q.fvsF.getD ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c'
        j).getD r default).field default = .bvar 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h0 := C.hfld
    rw [hg] at h0
    exact inferTypeCore_bvar_absurd h0
  -- the hole values of the SEPARATED tuple
  have hcl : ∀ (n : Name) (ψ' : Name → Nat) (ρ₁ ρ₂ : Nat → V),
      interp V ρ₁ (mpC.base2.acval n ψ') = interp V ρ₂ (mpC.base2.acval n ψ') :=
    fun n ψ' ρ₁ ρ₂ => acval_interp_closed mpC.base2 n ψ' ρ₁ ρ₂
  have hvget : ∀ t', t' < d.k →
      ((List.range d.k).map (d.toLfp.holeVal ψ (consList (xs.take d.nP) ρ)
        (sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
          (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P'))).getD t' pt
        = d.toLfp.holeVal ψ (consList (xs.take d.nP) ρ)
          (sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
            (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P') t' := by
    intro t' ht'
    simp [List.getD_eq_getElem?_getD, List.getElem?_range ht']
  have hvTy : ∀ t', t' < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ 0 (cvTas.getD t' default).type = some T ∧
      ((List.range d.k).map (d.toLfp.holeVal ψ (consList (xs.take d.nP) ρ)
        (sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
          (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P'))).getD t' pt ∈ˢ interp V ρ T := by
    intro t' ht'
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t']? = some cvTb := ⟨_, List.getElem?_eq_getElem ht'⟩
    obtain ⟨-, -, -, hfv, -, hFD⟩ := hmr.2.2.2.1 t' cvTb hcvb
    have hgt : cvTas.getD t' default = cvTb := by rw [List.getD_eq_getElem?_getD, hcvb]; rfl
    rw [hgt]
    refine ⟨_, hFD.read ψ, ?_⟩
    have htk : t' < d.k := by rw [← hN.2.2]; exact ht'
    rw [hvget t' htk]
    have hmemT := LfpDatum.holeVal_mem (D := d.toLfp) (ρp := consList (xs.take d.nP) ρ) hC.kN
      (sepTuple_mem (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
        (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P') htk
      (ab := d.ppsM t' ψ) (by
        show _ = ((d.ppsM t' ψ).take d.nP).map (·.2.2) ++ ((d.ppsM t' ψ).drop d.nP).map (·.2.2)
        rw [← List.map_append, List.take_append_drop]) (hFD.bits ψ)
    have hT : FRen (fun _ _ => False) cvTb.type cvTb.type :=
      FRen.refl_of_fvarsBelow (d := 0) (fun i h => absurd h (Nat.not_lt_zero _))
        (Expr.WScoped.of_not_hasFvar hfv).fvarsBelow
    rw [denoteMeta_fren_interp hcl hT 0 0 ρ
      (shiftE (d.toLfp.pars t' ψ).length 0 (consList (xs.take d.nP) ρ))
      (fun _ _ h => h.elim) (hFD.read ψ) (hFD.read ψ)]
    exact hmemT
  have hm' := hmK _ hcal
  have hlaw : ∀ is : List V,
      SpineFit (consList (xs.take d.nP) ρ)
        (d.IdsM (pp.toBlockShape.recTgtAt ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type))
          (tgtRs out) c' j).getD r default).callee) ψ) is →
      (xs.take d.nP ++ is).foldl SetTheory.app
          (((List.range d.k).map (d.toLfp.holeVal ψ (consList (xs.take d.nP) ρ)
            (sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
              (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P'))).getD
            (pp.toBlockShape.recTgtAt ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type))
              (tgtRs out) c' j).getD r default).callee) pt)
        = app (sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
              (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P'
              (pp.toBlockShape.recTgtAt ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type))
                (tgtRs out) c' j).getD r default).callee))
            (d.tup ψ (pp.toBlockShape.recTgtAt ((tgtIhL μ F fe pp.toBlockShape
              (cvTas.map (·.type)) (tgtRs out) c' j).getD r default).callee) is) := by
    intro is his
    rw [hvget _ hm']
    have hsP : Sat V (d.toLfp.pars (pp.toBlockShape.recTgtAt ((tgtIhL μ F fe pp.toBlockShape
        (cvTas.map (·.type)) (tgtRs out) c' j).getD r default).callee) ψ).reverse
        (consList (xs.take d.nP) ρ) := (hmr.2.2.2.2.2.2 _ hm' ψ _).mpr hsat
    have hxsT : (xs.take d.nP).length = d.nP := by
      rw [List.length_take, hxs]
      exact Nat.min_eq_left (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).1
    have hlenP : (d.toLfp.pars (pp.toBlockShape.recTgtAt ((tgtIhL μ F fe pp.toBlockShape
        (cvTas.map (·.type)) (tgtRs out) c' j).getD r default).callee) ψ).length = d.nP := by
      show (List.map _ (List.take _ _)).length = _
      rw [List.length_map, List.length_take, hS.lenPps _ ψ hm']; omega
    have hfx := LfpDatum.holeVal_app (D := d.toLfp) (ψ := ψ)
      (X := sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
        (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P') hsP his
    have hfI : ConLeche.Semantics.frameIdx d.nP (consList (xs.take d.nP) ρ) = xs.take d.nP := by
      have := frameIdx_consList' (xs.take d.nP) ρ
      rwa [hxsT] at this
    rw [hlenP, hfI] at hfx
    exact hfx
  have hcoreT := tgtCall_core hμ h R hdR' hN hS hcore hmr hM hnd ψ ρ hc' hjn hspF hxs hrl
    ((List.range d.k).map (d.toLfp.holeVal ψ (consList (xs.take d.nP) ρ)
      (sepTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ))
        (d.toLfp.Φ ψ (consList (xs.take d.nP) ρ)) P')))
    (by rw [List.length_map, List.length_range, hN.2.2]) hvTy _ hlaw
    (fun Aty hA => tgtField_transport hμ h R hdR' hN hcore hmr hr hcA hrhs ψ ρ hxs hfsl
      (by simp only [List.length_map, List.length_range]; rfl) hsepH.2.1 hfi Aty hA) bs hbs
  obtain ⟨hidx, hin⟩ := hcoreT
  simp only [sepTuple] at hin
  rw [app_graph (show _ ∈ˢ d.toLfp.idx ψ (consList (xs.take d.nP) ρ) _ from hidx)] at hin
  exact (mem_sep.mp hin).2 _ hcal rfl hvU

end Rows

end ConLeche.Model
