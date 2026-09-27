module

public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.EnvBound

public section

/-!
# Every class, read at its home's record (PRIMREC, lane MEMBER)

The route off the walk (`targetFlatRouteOf`) lets a cycle run inside ONE
home: an older block's members at one instance (lane FLATHOME), or the
installing block's own members (lane MEMBER).  Its completeness proof
(`TargetFlatInd.lean`) is ONE argument for both — the home's own lfp
induction at the class's frame — once every class is seen the same way:
`tgtCls_view` reads class `c` at its recorded clause (`tgtClsD`), its
component (`tgtClsM`), its level assignment (`tgtClsψ`) and its frame
(`tgtClsFr`), with the facts an outside class's `TgtOutCls` record and
`tgtOutSat` supply.  At an outside class they are those; at a member
class the record is the block's own (`tgtMemCls`: the installing block
is stored, recorded and covered like any other), its level assignment
the identity instantiation (`substFn_param_self`), and its key frame the
prefix's parameters (`tgtMemDsa`: a member's parameters are the
recursor's first binders).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- A spine of arguments that all read is read by their readings. -/
theorem denoteMetaSpine_map_of {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr}, (∀ a ∈ as, (denoteMeta acval env φ d a).isSome = true) →
      DenoteMetaSpine acval env φ d as (as.map fun x => (denoteMeta acval env φ d x).getD default)
  | [], _ => .nil
  | a :: as, h => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
    rw [List.map_cons, hv, Option.getD_some]
    exact .cons hv (denoteMetaSpine_map_of fun b hb => h b (List.mem_cons_of_mem _ hb))

section View

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}

/-- **A member class at the block's own record**: the member's former is
stored, recorded as component `recTgtAt c` of `d.toLfp`, which owns its
constructors (the ones the check read); its home is the block. -/
theorem tgtMemCls (hcov : LfpCover mpC [])
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some (d.ctorsM c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    {c : Nat} (hc : c < (tgtRs out).length) (hm : (tgtMajor out c).member.isSome = true) :
    ∃ cvI : ConstantVal,
      TgtOutCls mpC (tgtMajor out c) d.toLfp (pp.toBlockShape.recTgtAt c) cvI ∧
      cvI.levelParams = pp.toBlockShape.lps ∧
      (tgtMajor out c).lvls = pp.toBlockShape.lps.map .param ∧
      (tgtMajor out c).home = d.toLfp.names ∧
      (tgtMajor out c).nPc = pp.toBlockShape.nP ∧
      ∀ ψ : Name → Nat, (d.toLfp.params ψ).length = pp.toBlockShape.nP ∧
        (d.toLfp.ids (pp.toBlockShape.recTgtAt c) ψ).length = (tgtMajor out c).nIdx := by
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  obtain ⟨ms, -, hms, hnIdx, hnPc, hctors, hcvTa, -, -⟩ := E.member_facts_of hm
  obtain ⟨ms', hms', hind, hhome, hlvls⟩ := E.member_home_of hm
  obtain rfl : ms = ms' := Option.some.inj (hms.symm.trans hms')
  have htgt : pp.toBlockShape.recTgtAt c = rc.tgt := by
    simp [ConLeche.BlockShape.recTgtAt, List.getD_eq_getElem?_getD, hrc]
  rw [htgt]
  obtain ⟨hnm, hlpsT, ⟨caps, hfind⟩, -, -, hFD⟩ := hmr.2.2.2.1 rc.tgt E.cvTP hcvTa
  have hname := (hmr.2.2.2.2.1 rc.tgt ms hms).1
  have hnIdxT := (hmr.2.2.2.2.1 rc.tgt ms hms).2
  have hindT : (tgtMajor out c).ind = E.cvTP.name := by rw [hind, ← hname, hnm]
  have hk : rc.tgt < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k := by
    rw [← hmr.2.2.1]; exact (List.getElem?_eq_some_iff.mp hcvTa).1
  have hmem : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).toLfp.member rc.tgt
      = (tgtMajor out c).ind := by
    rw [hindT, ← hnm]; rfl
  obtain ⟨cv', caps', hf', hnd⟩ := (hcov.own _ hlfp).lvlNodup rc.tgt hk
  rw [hmem, hindT, hfind] at hf'
  obtain ⟨rfl, rfl⟩ : E.cvTP = cv' ∧ caps = caps' := by simpa using hf'
  have hctl : rc.tgt < ctorsAs.length := (List.getElem?_eq_some_iff.mp hctors).1
  have hctE : (tgtMajor out c).ctors
      = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM rc.tgt :=
    Option.some.inj (hctors.symm.trans (hctorsAs _ hctl))
  refine ⟨E.cvTP, ⟨hlfp, hk, hmem, ⟨caps, by rw [hindT]; exact hfind⟩, hnd, hcov.nodup _ hlfp,
    hcov.len _ hlfp, by rw [hctE]; rfl, ?_⟩, hlpsT, hlvls, ?_, hnPc, fun ψ => ⟨?_, ?_⟩⟩
  · intro j hj
    have hcA : ((tgtRs out)[c]).2.2.2[j]? = some ((tgtMajor out c).ctors[j]) := by
      rw [tgtRs_ctors hr]; exact List.getElem?_eq_getElem hj
    have hfc := tgtRecCtor_find R hN hcore hctorsAs hcov c _ hr j _ hcA
    have hcn : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).toLfp.ctorName rc.tgt j
        = ((tgtMajor out c).ctors[j]).1.name := by
      show (((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM rc.tgt).getD j
        default).1.name = _
      rw [← hctE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hcn]
    exact hfc
  · rw [hhome]
    have hkN := hcov.len _ hlfp
    apply List.ext_getElem
    · rw [hkN]
      show (pp.toBlockShape.members.map (·.cvT.name)).length = _
      rw [List.length_map, ← hmr.2.1]; rfl
    · intro m h1 h2
      have hm' : m < pp.toBlockShape.members.length := by
        simpa [ConLeche.BlockShape.memberNames] using h1
      have hmsm := (hmr.2.2.2.2.1 m _ (List.getElem?_eq_getElem hm')).1
      have hg : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).toLfp.names[m]
          = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).memberName m := by
        have h2' : m < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).memberNames.length :=
          h2
        show (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).memberNames[m]'h2' = _
        simp only [BlockData.memberName, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem h2', Option.getD_some]
      rw [hg, hmsm]
      simp [ConLeche.BlockShape.memberNames]
  · -- the parameters: member `0`'s former's first `nP` binders
    have h0 : 0 < cvTas.length := by
      have := (List.getElem?_eq_some_iff.mp hcvTa).1; omega
    obtain ⟨-, -, -, -, -, hFD0⟩ := hmr.2.2.2.1 0 _ (List.getElem?_eq_getElem h0)
    show ((((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM 0 ψ).take
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).nP).map (·.2.2)).length = _
    rw [List.length_map, List.length_take, hFD0.len ψ, hmr.1]; omega
  · show ((((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM rc.tgt ψ).drop
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).nP).map (·.2.2)).length = _
    rw [List.length_map, List.length_drop, hFD.len ψ, hnIdx, ← hnIdxT]; omega

/-- **A member class's parameters are the prefix's first variables**:
they read at the rule prefix, as many as the block's parameters, and
the key frame at a prefix spine is the spine's parameter part. -/
theorem tgtMemDsa
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) (hm : (tgtMajor out c).member.isSome = true)
    (ψ : Name → Nat) :
    DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtMajor out c).ds
        (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c) ∧
      (tgtMajor out c).ds.length = pp.toBlockShape.nP ∧
      ∀ (ρ : Nat → V) (xs : List V), xs.length = tgtRP pp.toBlockShape c →
        keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
            (tgtRP pp.toBlockShape c) (consList xs ρ)
          = consList (xs.take pp.toBlockShape.nP) ρ := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape c = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hds := E.ds_eq_of hm
  have hlen := openPisAtFvars_length _ E.hopen
  have hnP : pp.toBlockShape.nP ≤ rc.rP := E.hroom
  have hmI : rc.rP ≤ rc.mI := E.hle
  -- the parameters: the openers `0 … nP-1`
  have hfv : ∀ i (hi : i < (tgtMajor out c).ds.length), ∃ ty,
      (tgtMajor out c).ds[i] = .fvar i ty ∧ i < pp.toBlockShape.nP := by
    intro i hi
    have hi' : i < pp.toBlockShape.nP := by rw [hds, List.length_take] at hi; omega
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ 0 E.hopen i _
      (List.getElem?_eq_getElem (by omega))
    refine ⟨ty, ?_, hi'⟩
    simp only [hds, List.getElem_take]
    simpa using hty
  have hdl : (tgtMajor out c).ds.length = pp.toBlockShape.nP := by
    rw [hds, List.length_take]; omega
  refine ⟨denoteMetaSpine_map_of fun a ha => ?_, hdl, fun ρ xs hxl => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hty, -⟩ := hfv i hi
    rw [hty, denoteMeta_fvar]; rfl
  · unfold keyFrame
    congr 1
    · apply List.ext_getElem
      · simp [tgtOutDsa, hdl, hxl, hRP]; omega
      · intro i h1 h2
        have hi : i < (tgtMajor out c).ds.length := by simpa [tgtOutDsa] using h1
        obtain ⟨ty, hty, hiP⟩ := hfv i hi
        simp only [tgtOutDsa, List.getElem_map, hty, denoteMeta_fvar, Option.getD_some,
          interp_bvar, List.getElem_take]
        rw [consList_getD_of_lt _ _ _ (by rw [hxl, hRP]; omega), List.getD_eq_getElem?_getD,
          show xs.length - 1 - (tgtRP pp.toBlockShape c - 1 - i) = i by rw [hxl, hRP]; omega,
          List.getElem?_eq_getElem (by rw [hxl, hRP]; omega), Option.getD_some]
    · funext j
      rw [← hxl, consList_apply_add]

/-- **Every class, read at its home's record** (see the module
docstring): the class's recorded clause, component and level assignment
carry a `TgtOutCls` record, its home is the clause's block, its
parameters read at the rule prefix, and an element of its index set
lies at the clause's index set at the class's frame — the key frame of
those readings, where the clause's parameters are satisfied. -/
theorem tgtCls_view (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some (d.ctorsM c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks) (ψ : Name → Nat)
    {c : Nat} (hc : c < (tgtRs out).length) :
    ∃ cvI : ConstantVal,
      TgtOutCls mpC (tgtMajor out c) (tgtClsD d Dc out c) (tgtClsM mc pp.toBlockShape out c)
        cvI ∧
      tgtClsψ cvc out ψ c = Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls ∧
      (tgtMajor out c).home = (tgtClsD d Dc out c).names ∧
      (tgtMajor out c).ds.length = (tgtMajor out c).nPc ∧
      (tgtMajor out c).lvls.length = cvI.levelParams.length ∧
      DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtMajor out c).ds
        (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c) ∧
      ((tgtClsD d Dc out c).params (tgtClsψ cvc out ψ c)).length = (tgtMajor out c).ds.length ∧
      ((tgtClsD d Dc out c).ids (tgtClsM mc pp.toBlockShape out c)
        (tgtClsψ cvc out ψ c)).length = (tgtMajor out c).nIdx ∧
      ∀ (ρ : Nat → V) (xs : List V) (t : V),
        t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs ∧
        tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
          = keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
              (tgtRP pp.toBlockShape c) (consList xs ρ) ∧
        Sat V ((tgtClsD d Dc out c).params (tgtClsψ cvc out ψ c)).reverse
          (tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) ∧
        t ∈ˢ (tgtClsD d Dc out c).idx (tgtClsψ cvc out ψ c)
          (tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
          (tgtClsM mc pp.toBlockShape out c) := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  cases hmb : (tgtMajor out c).member with
  | some tm =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    obtain ⟨cvI, hcl, hlpsI, hlvls, hhome, hnPc, hlens⟩ :=
      tgtMemCls hcov R hdR hN hcore hctorsAs hmr hlfp hc hm
    obtain ⟨hdsa, hdl, hkf⟩ := tgtMemDsa (mpC := mpC) R hc hm ψ
    have hD : tgtClsD d Dc out c = d.toLfp := by simp only [tgtClsD, hm, if_true]
    have hM : tgtClsM mc pp.toBlockShape out c = pp.toBlockShape.recTgtAt c := by
      simp only [tgtClsM, hm, if_true]
    have hψ : tgtClsψ cvc out ψ c = ψ := by simp only [tgtClsψ, hm, if_true]
    have hψ' : Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls = ψ := by
      rw [hlpsI, hlvls, Level.substFn_param_self]
    rw [hD, hM, hψ]
    refine ⟨cvI, hcl, hψ'.symm, hhome, by rw [hdl, hnPc], by rw [hlvls, hlpsI, List.length_map],
      hdsa, by rw [(hlens ψ).1, hdl], (hlens ψ).2, fun ρ xs t ht => ?_⟩
    have hFr : tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
        = consList (xs.take d.nP) ρ := by simp only [tgtClsFr, hm, if_true]
    rw [tgtClsIs_mem hm] at ht
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits ht
    have hxl : xs.length = tgtRP pp.toBlockShape c :=
      hpref.length_eq.trans (blockRulePdomsAV_length hμ mpC h hr ψ)
    refine ⟨hpref, by rw [hFr, hkf ρ xs hxl, hmr.1], ?_, ?_⟩
    · rw [hFr]
      have := sat_of_spineFit (Δ₀ := []) (fun _ _ h => nomatch h) hpar
      simp only [List.append_nil] at this
      exact this
    · rw [hFr]
      have ht' := ht
      rw [blockRecIs_pos hpar hpref] at ht'
      exact ht'
  | none =>
    have hcl := hcls c hc hmb
    have hm : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    have hD : tgtClsD d Dc out c = Dc c := by simp only [tgtClsD, hm]; rfl
    have hM : tgtClsM mc pp.toBlockShape out c = mc c := by simp only [tgtClsM, hm]; rfl
    have hψ : tgtClsψ cvc out ψ c
        = Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls := by
      simp only [tgtClsψ, hm]; rfl
    rw [hD, hM, hψ]
    obtain ⟨dsa, hdsa, hul, -, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hmb hcl ψ
    have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c :=
      denoteMetaSpine_eq_map hdsa
    subst hdsaE
    obtain ⟨rc, u, -, ⟨E⟩⟩ := targetEntryAt R hr
    obtain ⟨-, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hmb
    have hhome : (tgtMajor out c).home = (Dc c).names := by
      rw [E.home_of hmb]
      obtain ⟨caps, hfI⟩ := hcl.hfind
      rw [ConLeche.mkFEnv_find?, hfI]
      exact hcov.all _ hcl.hD (mc c) hcl.hmm _ caps (by rw [hcl.hmem]; exact hfI)
    refine ⟨cvc c, hcl, rfl, hhome, hdsLen, hul, hdsa, hlenP,
      tgtOutIdx_len R hr hmb hcl ψ hlenP, fun ρ xs t ht => ?_⟩
    have hpref := tgtClsIs_out_fits hmb ht
    have hFr : tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
        = keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
            (tgtRP pp.toBlockShape c) (consList xs ρ) := by
      simp only [tgtClsFr, hm]; rfl
    rw [hFr]
    refine ⟨hpref, rfl, hsatF ρ xs hpref, ?_⟩
    rw [← tgtClsIs_out_pos hmb hpref]; exact ht

/-- **Two classes joined around a cycle share their recorded clause**:
both members (the block's own), or both outside classes whose home is
one recorded block (the selected one, `lfpSel`). -/
theorem tgtClsD_edge (hcov : LfpCover mpC [])
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC d.toLfp (tgtMajor out c).ind)
    {c c' : Nat} (hc : c < (tgtRs out).length) (hc' : c' < (tgtRs out).length)
    (hmn : (tgtMajor out c).member.isNone = (tgtMajor out c').member.isNone)
    (hhomeC : (tgtMajor out c).home.contains (tgtMajor out c').ind = true)
    (hhome : (tgtMajor out c).home = (tgtClsD d Dc out c).names) :
    tgtClsD d Dc out c' = tgtClsD d Dc out c := by
  cases hmb : (tgtMajor out c).member with
  | some _ =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hm' : (tgtMajor out c').member.isSome = true := by
      rw [hmb] at hmn
      cases hx : (tgtMajor out c').member with
      | none => rw [hx] at hmn; exact nomatch hmn
      | some _ => rfl
    simp only [tgtClsD, hm, hm', if_true]
  | none =>
    have hm : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    have hmb' : (tgtMajor out c').member = none := by
      rw [hmb] at hmn
      cases hx : (tgtMajor out c').member with
      | none => rfl
      | some _ => rw [hx] at hmn; exact nomatch hmn
    have hm' : (tgtMajor out c').member.isSome = false := by rw [hmb']; rfl
    simp only [tgtClsD, hm, hm']
    simp only [tgtClsD, hm, Bool.false_eq_true, if_false] at hhome
    have hcl := hcls c hc hmb
    have hin : (tgtMajor out c).ind ∈ (Dc c).names := by
      rw [← hcl.hmem]
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hcl.hkN]; exact hcl.hmm),
        Option.getD_some]
      exact List.getElem_mem _
    have hin' : (tgtMajor out c').ind ∈ (Dc c).names := by
      rw [← hhome]; exact List.contains_iff_mem.mp hhomeC
    rw [hsel c' hc' hmb', hsel c hc hmb]
    rw [hsel c hc hmb] at hcl
    exact lfpSel_eq_of_mem hcov d.toLfp hcl.hD (by rw [← hsel c hc hmb]; exact hin)
      (by rw [← hsel c hc hmb]; exact hin')

end View

end ConLeche.Model
