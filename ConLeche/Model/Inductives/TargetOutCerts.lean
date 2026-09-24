module

public import ConLeche.Model.Inductives.TargetOutGrade
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.FixRuleData
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# The rule certificates at an OUTSIDE class (lane NESTIND, session 7)

`graphRecPre_core`'s `hcerts` at a recursor whose major is an outside
container: `BlockRuleCerts` at the target check's rule data
(`tgtFdomsAV`, `tgtIhdomsAV`, `tgtRbAV`, `tgtCaAV`).  The member row is
`tgtRuleCertsW_run` (`TargetRowCertsW.lean`); the frame-level facts are
shared (`targetFrame_facts`, `targetRule_reads`, `targetIh_scope`, over
the major's parameters scoped at the prefix, `TgtDsOk`); what differs
at an outside class is

* `tgtOutDsOk` — the major's parameters are the arguments of the
  recursor type's major domain: scoped at the prefix, naming stored
  constants, drawing their leaves from the prefix openers;
* the fields' readings and grading — the instantiated constructor's
  (`tgtOutOpen`, `tgtOutCrestWd`);
* the conclusion `Ca` — its peel at the target spellings (`tgtOutCaAt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Certs

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {outside nested : Bool} {block : List ConstantInfo}

/-- **An outside major's parameters are scoped at the prefix** (`TgtDsOk`):
the arguments of the recursor type's major domain, bounded below the
block's parameter count, naming stored constants, their leaves prefix
openers. -/
theorem tgtOutDsOk {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none) :
    TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds := by
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  obtain ⟨hw0, -⟩ := recStage_tyClosed h hr
  obtain ⟨-, -, hTres, -, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  have hTc : ConstsBound envC r.1.type := constsBound_of_constsResolve _ hTres
  have hsc := outsideDs_scoped E hMo hw0
  obtain ⟨-, -, -, -, -, -, hdsE, -, -, -, -⟩ := E.outside_of hMo
  -- the prefix openers are the major opening's first `rP`
  obtain ⟨o', hop'⟩ := ConLeche.openPisAtFvars_prefix rc.rP (rc.mI + 1) r.1.type 0
    (by have := E.hle; omega) E.hopen
  have hPref : tgtPrefFvs pp.toBlockShape out j = E.fvs.take rc.rP := by
    rw [tgtPrefFvs, tgtRecTy_at hr, hRP, hop']; rfl
  rw [hRP, hPref]
  -- the major is an opener, so its type names stored constants
  have hcbMaj : ConstsBound envC E.maj.fvarTypeD := by
    obtain ⟨tyM, hmajE⟩ := ConLeche.openPisAtFvars_index _ _ _ E.hopen rc.mI E.maj E.hmaj
    have hc := (openPisAtFvars_constsBound _ hTc E.hopen).1 E.maj (List.mem_of_getElem? E.hmaj)
    rw [hmajE] at hc ⊢
    simpa [ConstsBound, Expr.fvarTypeD] using hc
  intro a ha
  obtain ⟨hwa, hba, hla⟩ := hsc a ha
  have hroom := E.hroom
  refine ⟨Expr.WScoped.mono hroom hwa, hba, ?_, fun l hl => ?_⟩
  · rw [hdsE] at ha
    exact constsBound_getAppArgs _ hcbMaj a (List.mem_of_mem_take ha)
  · obtain ⟨hlt, hmem⟩ := hla l hl
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hmem
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ E.hopen k _ hk
    injection hty with hk1 _
    rw [Nat.zero_add] at hk1
    rw [List.mem_iff_getElem?]
    exact ⟨k, by rw [List.getElem?_take, if_pos (by omega)]; exact hk⟩

set_option maxHeartbeats 2000000 in
/-- **The rule's conclusion FITS the recursor's tower at an outside
class** (`blockRuleConclFitW_run`'s twin at the target spellings, via the
outside `hrule`, `tgtOutRuleK` at `K = 0`): at every frame satisfying
the rule's context, the peel's arguments read along the recursor type's
Π-tower. -/
theorem tgtOutConclFit (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (I : List AnnotTerm) :
    ∀ σ : Nat → V,
      Sat V (I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).reverse) σ →
      ∃ rest, TeleFitPA V σ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
        (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length + I.length)
          ++ (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).map (·.liftN I.length 0)
          ++ [(tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i).liftN I.length 0]) rest := by
  intro σ hsat
  have hL : I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).reverse
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i ++ I).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i ++ I).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hab
  have hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length :=
    hxs.length_eq
  have hfl : fs.length = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length :=
    hfs.length_eq
  have hwl : ws.length = I.length := hws.length_eq
  -- the outside `hrule`, at `K = 0`
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        ++ tgtFdomsK 0 mpC.base2.acval envC pp.toBlockShape out ψ j i) (xs ++ fs) := by
    rw [chainFrame_zero, tgtFdomsK, liftDomsK_zero]
    exact hab
  have hfire := tgtOutRuleK hμ hcov h R hr hcA hrhs hMo hcl ψ 0 (fun _ => pt) σ₀ hxl hsp0
  have hEs := tgtEsAV_outside hμ hcov h R hr hcA hrhs hMo hcl ψ
  have hlE : ∀ n (es : List AnnotTerm), liftEsK 0 n es = es := fun n es => by
    rw [liftEsK]
    exact (List.map_congr_left fun e _ => AnnotTerm.liftN_zero e _).trans (List.map_id _)
  rw [hlE, ← hEs, tgtMkK, AnnotTerm.liftN_zero, chainFrame_zero] at hfire
  -- the recursor's tower, and its binder data's bounds
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  obtain ⟨hbndR, -⟩ := recStage_tyBounds hμ mpC h hr ψ
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hLlen : (xs ++ fs ++ ws).length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
        + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length + I.length := by
    rw [List.length_append, List.length_append, hxl, hfl, hwl]
  have hpb : (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
        ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
          + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length + I.length)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀)) = xs := by
    rw [map_bvarAt_take (nP := (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
      (tgtRs out) ψ j).length) hLlen.symm (by rw [hLlen]; omega), List.append_assoc,
      List.take_left' hxl]
  have hes : ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).map
        (·.liftN I.length 0)).map (interp V (consList (xs ++ fs ++ ws) σ₀))
      = (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).map
        (interp V (consList (xs ++ fs) σ₀)) := by
    rw [List.map_map]
    refine List.map_congr_left fun e _ => ?_
    show interp V (consList (xs ++ fs ++ ws) σ₀) (e.liftN I.length 0) = _
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals e
  have hmk : interp V (consList (xs ++ fs ++ ws) σ₀)
        ((tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i).liftN I.length 0)
      = interp V (consList (xs ++ fs) σ₀) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i) := by
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals _
  have hbnd : ∀ l, l < ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
      (fun b : Nat × Nat × AnnotTerm => b.2.2)).length →
      Term.bvarsBelow l ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
        (fun b : Nat × Nat × AnnotTerm => b.2.2)).getD l default).erase) := by
    intro l hl
    rw [List.length_map] at hl
    have hq := hbndR l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hq
    exact hq
  have hfitσ := spineFit_frame_of_bounded (σ' := consList (xs ++ fs ++ ws) σ₀) hbnd hfire
  rw [hTyE]
  refine teleFitPA_mkPisAV_of_spineFit ?_ ?_
  · have hq := hfire.length_eq
    simp only [List.length_map, List.length_append, List.length_singleton] at hq
    simp only [List.length_append, List.length_map, paramBvarsAt_length, List.length_singleton]
    omega
  · rw [List.map_append, List.map_append, hpb, hes, List.map_cons, List.map_nil, hmk]
    rw [← List.append_assoc] at hfitσ
    exact hfitσ

set_option maxHeartbeats 4000000 in
/-- **The rule conclusion's peel arguments are graded at an outside
class** (`blockRuleConclArgsW_run`'s twin): at every frame satisfying the
rule's context, the prefix entries are bound variables; an index
expression is a substituted recorded result index, an argument of the
instantiated constructor's graded conclusion (`tgtOutCrestWd`); the
fired spine is the constructor's leaf applied to the parameters (which
fit its stored type, `tgtOutCtorFit`) and the fields (which fit the
instantiated constructor). -/
theorem tgtOutConclArgs (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (I : List AnnotTerm) :
    ∀ σ : Nat → V,
      Sat V (I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).reverse) σ →
      ∀ a ∈ paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length + I.length)
          ++ (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).map (·.liftN I.length 0)
          ++ [(tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i).liftN I.length 0],
        WellDenotedV V σ a := by
  intro σ hsat
  have hL : I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).reverse
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i ++ I).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i ++ I).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab', ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hab
  have hwl : ws.length = I.length := hws.length_eq
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hdrop : ∀ e : AnnotTerm,
      WellDenotedV V (consList (xs ++ fs ++ ws) σ₀) (e.liftN I.length 0)
        ↔ WellDenotedV V (consList (xs ++ fs) σ₀) e := by
    intro e
    rw [WellDenotedV_liftN, hframe, ← hwl, shiftE_consList]
  -- the class's reading and the instantiated constructor
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatW⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  obtain ⟨-, hdsaW⟩ := hsatW σ₀ xs hxs
  obtain ⟨-, -, -, ab, -, -, -, -, hlab, hfdE, -, hcrR⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  have hcw := tgtOutCrestWd hμ hcov h R hr hcA hrhs hMo hcl ψ σ₀ hxs hcrR
  have hfs' := hfs
  rw [hfdE] at hfs'
  have hfsl : fs.length = cA.2 := by
    rw [hfs'.length_eq, List.length_map, substTele_length, hlab]
  have hxsl : xs.length = tgtRP pp.toBlockShape j := by
    rw [hxs.length_eq, blockRulePdomsAV_length hμ mpC h hr ψ]; rfl
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · -- a prefix variable
      simp only [paramBvarsAt, List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      exact ⟨trivial, trivial⟩
    · -- an index expression: a substituted result index, an argument of the conclusion
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [hdrop]
      rw [tgtEsAV_outside hμ hcov h R hr hcA hrhs hMo hcl ψ, tgtOutEs] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
        rw [← tgtRs_ctors hr]; exact hcA
      rw [List.getD_eq_getElem?_getD, hcAM, Option.getD_some]
      have hB := wdV_mkPisAV_body hcw fs hfs'
      rw [AnnotTerm.substAV_mkAppN] at hB
      have hargs := WellDenotedV_mkAppN_args _ hB
      rw [consList_append]
      exact hargs _ (List.mem_map.mpr ⟨e0, List.mem_append_right _ he0, rfl⟩)
  · -- the fired constructor application
    rw [List.mem_singleton] at ha
    subst ha
    rw [hdrop]
    obtain ⟨T0, pps, b0, hcons, hlpsI, hT0, hT0E, hplen, hT0wd, hT0cl, hfit⟩ :=
      tgtOutCtorFit hμ hcov h R hr hcA hrhs hMo hcl ψ σ₀ hxs
    have hTF := hfit _ hcrR
    rw [(tgtOutMkAV_eq hμ hcov h R hr hcA hrhs hMo hcl ψ).2, annotMkAppN_append]
    -- the leaf at the parameters: graded, in the instantiated constructor
    have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length = pps.length := by
      rw [← DenoteMetaSpine.length_eq hdsa, hplen]
      obtain ⟨rc, u, -, ⟨E⟩⟩ := targetEntryAt R hr
      obtain ⟨-, -, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
      exact hdsLen
    have hpc : Rules.PiChain (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length T0 := by
      have hpcA : ∀ (qs : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
          Rules.PiChain qs.length (mkPisAV qs b) := by
        intro qs b
        induction qs with
        | nil => trivial
        | cons _ qs ih => exact ih
      rw [hdl, hT0E]; exact hpcA pps b0
    have hTF' := Rules.teleFit_of_teleFitPA hpc hTF
    have hmapD : ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
          (AnnotTerm.liftN cA.2 · 0)).map (interp V (consList (xs ++ fs) σ₀))
        = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
          (interp V (consList xs σ₀)) := by
      rw [List.map_map]
      refine List.map_congr_left fun x _ => ?_
      show interp V (consList (xs ++ fs) σ₀) (x.liftN cA.2 0) = _
      rw [consList_append, ← hfsl, interp_liftN_consList]
    have hmem : interp V (consList (xs ++ fs) σ₀)
          (mpC.base2.acval cA.1.name (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
        ∈ˢ interp V (consList xs σ₀) T0 := by
      have hm := mpC.mem_type _ hcons _ T0 (by rw [show (ConstantInfo.ctorInfo cA.1
        (tgtMajor out j).nPc cA.2).toConstantVal.type = cA.1.type from rfl]; exact hT0)
        (consList (xs ++ fs) σ₀)
      rw [show (ConstantInfo.ctorInfo cA.1 (tgtMajor out j).nPc cA.2).name = cA.1.name
        from rfl] at hm
      rw [interp_congr_below (V := V) T0 0 (consList xs σ₀) (consList (xs ++ fs) σ₀) hT0cl
        (fun k hk => absurd hk (Nat.not_lt_zero _))]
      exact hm
    have hA := Rules.wellDenotedV_mkAppN_of_fit
      ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map (AnnotTerm.liftN cA.2 · 0))
      (hT0wd (consList xs σ₀))
      ⟨mpC.base2.acval_wellDenoted _ _ _, mpC.acval_validV _ _ _⟩
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        rw [WellDenotedV_liftN, consList_append, ← hfsl, shiftE_consList]
        exact hdsaW y hy)
      hmem (by rw [hmapD]; exact hTF')
    -- the fields: they fit the instantiated constructor
    have hvF : ((List.range cA.2).map fun k => AnnotTerm.bvar (tgtRP pp.toBlockShape j + cA.2 - 1
        - (tgtRP pp.toBlockShape j + k))).map (interp V (consList (xs ++ fs) σ₀)) = fs :=
      map_fieldBvars hxsl hfsl
    have hTFf := teleFit_mkPisAV_of_spineFit
      (B := AnnotTerm.substAV (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP pp.toBlockShape j)
          (tgtMajor out j).ds)
        (AnnotTerm.mkAppN (.bvar (cA.2 + (D.k - 1 - mm)))
          ((List.range (tgtMajor out j).ds.length).map
              (fun q => AnnotTerm.bvar ((tgtMajor out j).ds.length + D.k + cA.2 - 1 - q))
            ++ D.resIdx (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i)) cA.2) hfs'
    rw [← hvF] at hTFf
    exact (Rules.wellDenotedV_mkAppN_of_fit _ hcw hA.1 (fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨trivial, trivial⟩) hA.2 hTFf).1

end Certs

end ConLeche.Model
