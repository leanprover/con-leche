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
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetRowCertsRun
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Capstone
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.IndFrame
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
  {nested : Bool} {block : List ConstantInfo}

/-- **An outside major's parameters are scoped at the prefix** (`TgtDsOk`):
the arguments of the recursor type's major domain, bounded below the
block's parameter count, naming stored constants, their leaves prefix
openers. -/
theorem tgtOutDsOk {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
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
  obtain ⟨-, -, -, -, -, hdsE, -, -, -, -⟩ := E.outside_of hMo
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
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
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
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
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
      obtain ⟨-, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
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

set_option maxHeartbeats 8000000 in
/-- **Row `hcerts` at an outside class** (`tgtRuleCertsW_run`'s twin at
the target spellings): the certificates of the `(j, i)`-th rule of a
recursor whose major is an outside container, at the base frame.  The
prefix, the `ih` openers, the residue and the typing runs are the target
run's, as at a member; the fields are the instantiated constructor's
(read by `tgtOutOpen`, graded by `tgtOutCrestWd`), the conclusion the
peel at the target spellings (`tgtOutCaAt`, `tgtOutConclFit`,
`tgtOutConclArgs`). -/
theorem tgtOutCertsW (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)
    (hformer : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false) (ψ : Name → Nat)
    {i : Nat} (hi : i < blockRecNCt (tgtRs out) j) :
    BlockRuleCerts V mpC F ψ (pp.toBlockShape.rulePrefixAt j)
      (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length
      (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ j i).length
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)
      (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ j i)
      (tgtRbAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ j i)
      (tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ j i) := by
  -- the rule at `(j, i)`
  have hjr : i < r.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hi; exact hi
  obtain ⟨cA, hcA⟩ : ∃ cA, r.2.2.2[i]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  -- the class's reading and the instantiated constructor
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatW⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  obtain ⟨-, -, -, ab, -, -, -, -, hlab, hfdE, hfdR, hcrR⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  have hdsOk0 := tgtOutDsOk h R hr hMo
  -- the target rule's run
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, hPref, hQcr, hFld, -, -, hAbs⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hrP : rc.rP = pp.toBlockShape.rulePrefixAt j := hRP.symm
  have hdsOk : TgtDsOk envC rc.rP Q.fvsPref (tgtMajor out j).ds := by
    rw [hRP, ← hPref] at hdsOk0; exact hdsOk0
  -- the constructor
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfc0)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hct : ConLeche.targetCtorAt (tgtMajor out j) cA.1
      = cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls := by
    simp [ConLeche.targetCtorAt, hMo]
  have hCf' : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false := by
    rw [hct, Expr.hasFvar_instantiateLevelParams]; exact hCf
  have hCb' : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true := by
    rw [hct, Expr.looseBVarsBounded_instantiateLevelParams]; exact hCb
  have hCc' : ConstsBound envC (ConLeche.targetCtorAt (tgtMajor out j) cA.1) := by
    rw [hct]
    refine constsBound_of_constsResolve _ ?_
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
    exact hwfC.2.2.1
  -- the stored family's facts
  obtain ⟨hTf, -, hTres, hTb, hallRhs⟩ :=
    ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  have hTc : ConstsBound envC r.1.type := constsBound_of_constsResolve _ hTres
  have hbf : Q.body.hasFvar = false :=
    (stripLams_not_hasFvar _ Q.hstrip (hallRhs rhs (List.mem_of_getElem? hrhs)).1).2
  obtain ⟨hle, hRT3⟩ := tgtFam_facts h
  obtain ⟨hw₁, -⟩ := recStage_tyClosed h hr
  -- the frame
  obtain ⟨hFr, hlbFQ, hcbFQ, hherQ⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf' hCb' hCc'
  have hscope := fun ih (hih : ih ∈ Q.ihs.toList) =>
    targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hherQ hcbFQ hformer (fun c' => (hRT3 c').1) hih
  have hwf : TargetIhWF (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
      Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large))) (rc.rP + cA.2) Q.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ Q.habs).2 (fun r hr => absurd hr (by simp))
  have hfvEq := ihs_fv_eq hwf
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  have hin := Rules.RulesInputs.ofSem mpC ψ
  -- the target data, named
  have hihL : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out j i
      = Q.ihs.toList := by rw [tgtIhL, ← hAbs]
  have hBc : tgtB pp.toBlockShape out j i = pp.toBlockShape.rulePrefixAt j + cA.2 :=
    tgtB_at hr hcA
  have hIdE : tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval envC ψ j i = ihDomsLifted (ihTyReads mpC.base2.acval envC ψ
      (pp.toBlockShape.rulePrefixAt j + cA.2) Q.ihs.toList) := by
    rw [tgtIhdomsAV, hBc, hihL]
  have hIlen : (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval envC ψ j i).length = Q.ihs.size := by
    rw [hIdE, ihDomsLifted_length]; simp [ihTyReads]
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
      = pp.toBlockShape.rulePrefixAt j := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length = cA.2 := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, ← hFld]
    exact openPisAtFvars_length _ Q.hfld
  have hTyLen : (Q.ihs.toList.map (·.ty)).length = Q.ihs.size := by simp
  -- the openings at the rule prefix
  have h₁ : ConLeche.openPisAtFvars (pp.toBlockShape.rulePrefixAt j) r.1.type 0
      = some (Q.fvsPref, Q.oPref) := by rw [← hrP]; exact Q.hpref
  have h₂ : ConLeche.openPisAtFvars cA.2 Q.crest (pp.toBlockShape.rulePrefixAt j)
      = some (Q.fvsF, Q.cbody) := by rw [← hrP]; exact Q.hfld
  -- the constructor at the major's instantiation: scoped, bounded, prefix-leaved
  have hcr := Q.hcrest
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinstC, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = Q.crest := hcr'
  have hw₂ : Expr.WScoped (pp.toBlockShape.rulePrefixAt j) Q.crest := by
    rw [← hrP]
    exact (instPisAt_WScoped (d := rc.rP) _ _ hinstC (Expr.WScoped.of_not_hasFvar hCf')
      (fun a ha => (hdsOk a ha).1)).2
  have hb₂ : Q.crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb' (fun a ha => (hdsOk a ha).2.1)).2
  have hcrestLeaf := crestLeaf_of_inst hCf' hinstC (fun a ha => (hdsOk a ha).2.2.2)
  -- the conclusion: its reading and peel, at the run's own `concl`
  obtain ⟨hCaR, hcon⟩ := tgtOutCaAt hμ hcov h R hr hcA hrhs hMo hcl ψ Q.ihs.size
  have hcb : tgtCbody pp.toBlockShape out j i = Q.cbody := by
    rw [tgtCbody, ← hQcr, tgtCtorOf_at hr hcA, hRP, Q.hfld]; rfl
  have hE : tgtConclExpr pp.toBlockShape out j i = Q.concl := by
    rw [tgtConclExpr, ← hPref, hcb, ← hFld, tgtCtorOf_at hr hcA, tgtRecTy_at hr, Q.hconcl]; rfl
  have hCaEq : tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ j i
      = (denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i + Q.ihs.size)
          (tgtConclExpr pp.toBlockShape out j i)).getD default := by
    rw [tgtCaAV, hihL, Array.length_toList]
  obtain ⟨hbC, hleafC⟩ := blockRuleConclClosed_of h₁ h₂ hTf hTb hb₂ hcrestLeaf
    (fun a ha => (hdsOk a ha).2.1) (fun a ha => (hdsOk a ha).2.2.2) Q.hconcl
  -- the residue: its reading and scoping
  obtain ⟨⟨Bv, hBv, -⟩, -, -, hlL, hbT⟩ := targetRule_reads hμ mpC.base2 ψ Q hle hbf hdsOk hTf hTb
    hTc hCf' hCb' hCc' hformer hRT3
  -- the `ih` opening
  have hb₃ : ∀ t ∈ Q.ihs.toList.map (·.ty), t.looseBVarsBounded 0 = true := by
    intro t ht
    obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp ht
    exact (hscope ih hih).2.1
  have h₃ := openPisAtFvars_ihTeleOf hb₃ (pp.toBlockShape.rulePrefixAt j + cA.2)
  rw [hTyLen] at h₃
  have hBB : rc.rP + cA.2 = pp.toBlockShape.rulePrefixAt j + cA.2 := by rw [hrP]
  have hFr' : FvarList (pp.toBlockShape.rulePrefixAt j + cA.2) (Q.fvsPref ++ Q.fvsF).reverse := by
    rw [← hBB]; exact hFr
  have hfvEq' : Q.ihs.toList.map (·.fv)
      = ihFvarsAt (pp.toBlockShape.rulePrefixAt j + cA.2) (Q.ihs.toList.map (·.ty)) := by
    rw [hfvEq, hBB]
  -- the frame's readings
  have hP := blockRulePdomsAV_reads hμ mpC h hr ψ h₁
  have hF : ∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) x.fvarTypeD
        = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
    intro l x hx
    exact hfdR l x (by rw [← hFld]; exact hx)
  have hplQ : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
      = rc.rP := by rw [hpl, hrP]
  have hdoms : ∀ (q : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[q]? = some x →
      denoteMeta mpC.base2.acval envC ψ q (Expr.fvarTypeD x)
        = some (((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
          ++ (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)).reverse.getD
            (rc.rP + cA.2 - 1 - q) default) := by
    intro q x hx
    have hq := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := envC)
      (ψ := ψ) (ihdoms := []) (fvsIh := []) hplQ hfl rfl
      (openPisAtFvars_length _ Q.hpref) (openPisAtFvars_length _ Q.hfld) rfl
      hP (by rw [← hrP] at hF; exact hF)
      (fun l x hx => nomatch hx) q x (by simpa using hx)
    simpa using hq
  -- the frame's grading: the prefix off the recursor type, the fields off the
  -- instantiated constructor (graded at every fitting prefix)
  obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -, hwdTy⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
  have hPgrad : ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
      ψ j).length → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).take l)
        ys →
      WellDenotedV V (consList ys σ)
        ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).getD l
          default) := by
    intro l hl σ ys hys
    have hle' : pp.toBlockShape.rulePrefixAt j
        ≤ (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length := by
      rw [hlenRds]
      have := blockRecHrPle (p := pp) h (List.getElem?_eq_some_iff.mp hr).1
      omega
    exact prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape
      (tgtRs out) ψ j) hle' (fun ρ' => by rw [← hTyE]; exact hwdTy ρ') (by rwa [hpl] at hl) hys
  have hFgrad : ∀ q, q < (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length →
      ∀ (σ : Nat → V) (zs ys : List V),
      SpineFit σ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) zs →
      SpineFit (consList zs σ) ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take q)
        ys →
      WellDenotedV V (consList ys (consList zs σ))
        ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD q default) := by
    intro q hq σ zs ys hzs hys
    have hcw := tgtOutCrestWd hμ hcov h R hr hcA hrhs hMo hcl ψ σ hzs hcrR
    rw [hfdE] at hq hys ⊢
    exact wdV_mkPisAV_dom hcw q (by simpa using hq) ys hys
  have hokPF := hokA_of_two hPgrad hFgrad
  have hPFlen : ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      ++ (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)).length
        = pp.toBlockShape.rulePrefixAt j + cA.2 := by
    rw [List.length_append, hpl, hfl]
  have hokΔ : ∀ q, q < rc.rP + cA.2 → ∀ ρ' : Nat → V,
      Sat V ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
        ++ (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)).reverse ρ' →
      WellDenotedV V (fun l => ρ' (l + (rc.rP + cA.2 - 1 - q) + 1))
        (((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
          ++ (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)).reverse.getD
            (rc.rP + cA.2 - 1 - q) default) := by
    intro q hq ρ' hsat
    have hk := blockRuleHokΔ_of (V := V) (ihdoms := []) hplQ hfl rfl
      (fun l hl σ' ys hys => by
        have := hokPF l (by simp only [List.length_nil, Nat.add_zero] at hl; omega) σ' ys
          (by simpa using hys)
        simpa using this) q (by simpa using hq) ρ' (by simpa using hsat)
    simpa using hk
  have h₃0 : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rc.rP + cA.2)
      = some ([], Expr.sort .zero) := rfl
  -- an `ih` type's reading, named
  have hTs : ∀ q (hq : q < Q.ihs.size) (T : AnnotTerm),
      denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + cA.2) Q.ihs[q].ty
        = some T →
      (ihTyReads mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + cA.2)
        Q.ihs.toList).getD q default = T := by
    intro q hq T hT
    rw [ihTyReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem hq]
    simp [hT]
  have hTsLen : (ihTyReads mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + cA.2)
      Q.ihs.toList).length = Q.ihs.size := by simp [ihTyReads]
  rw [hfl, hIlen]
  refine BlockRuleCerts.of_segments mpC h₁ h₂ h₃ hw₁ hw₂ ?_ ?_ ?_ ?_ hpl hfl hIlen hP hF
    ?_ ?_ (by rw [← hBB]; exact Q.hty) (by rw [← hBB]; exact Q.hdeq) hbT hbC
    ?_ (fun l hl => List.mem_append_left _ (hleafC l hl)) ?_ ?_ ?_
  · -- hw₃
    refine ihTeleOf_WScoped fun t ht => ?_
    obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp ht
    exact wscoped_of_leaves_mem hFr' _ (hscope ih hih).1
  · -- hlbF
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hlbFQ x hx
    · obtain ⟨i', ty, rfl, hty⟩ := mem_ihFvarsAt hx
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hty
      exact (hscope ih hih).2.1
  · -- hcbF
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hcbFQ x hx
    · obtain ⟨i', ty, rfl, hty⟩ := mem_ihFvarsAt hx
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hty
      have hc : ConstsBound envC ih.ty := (hscope ih hih).2.2.1
      simpa [ConstsBound] using hc
  · -- hclF
    intro x hx l hl
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hherQ x hx l hl)
    · obtain ⟨i', ty, rfl, hty⟩ := mem_ihFvarsAt hx
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hty
      exact List.mem_append_left _ (List.mem_reverse.mp ((hscope ih hih).1 l hl))
  · -- hI
    intro l x hx
    have hlen : l < (Q.ihs.toList.map (·.ty)).length := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simpa [ihFvarsAt] using this
    have hl' : l < Q.ihs.size := by simpa using hlen
    have hx' : x = Expr.fvar (pp.toBlockShape.rulePrefixAt j + cA.2 + l) Q.ihs[l].ty := by
      simp only [ihFvarsAt, List.getElem?_map, List.getElem?_range hlen, Option.map_some,
        Option.some.injEq] at hx
      rw [← hx]
      simp [hl']
    subst hx'
    have hih : Q.ihs[l] ∈ Q.ihs.toList := Array.getElem_mem_toList hl'
    obtain ⟨C⟩ := Q.call hih
    obtain ⟨hlT, hbT', -, -, -, -⟩ := hscope _ hih
    obtain ⟨T, hT⟩ := targetCall_ihTy_reads mpC.base2 ψ C (wscoped_of_leaves_mem hFr _ hlT) hbT'
      (fun l hl => hlbFQ _ (List.mem_reverse.mp (hlT l hl)))
    rw [hBB] at hT
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := envC) (φ := ψ) hacl l
      (pp.toBlockShape.rulePrefixAt j + cA.2) Q.ihs[l].ty 0 [] [] (leaf_lt_of_mem hFr' hlT)
      (LocList.nil _) (LocList.nil _)
    simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero] at hd
    rw [hIdE, ihDomsLifted_getD (by rw [hTsLen]; exact hl'), hTs l hl' T hT]
    show denoteMeta _ _ _ _ Q.ihs[l].ty = _
    rw [hd, hT]
    rfl
  · -- hokA
    intro l hl σ ys hys
    refine hokA_of_two (fun l hl σ ys hys => hokPF l (by rw [List.length_append] at hl; exact hl)
        σ ys hys)
      (fun q hq σ zs ys hzs hys => ?_) l (by rw [hPFlen, hIlen]; exact hl) σ ys hys
    have hq' : q < Q.ihs.size := by rwa [hIlen] at hq
    have hyl : ys.length = q := by
      rw [hys.length_eq, List.length_take, hIlen]; omega
    have hih : Q.ihs[q] ∈ Q.ihs.toList := Array.getElem_mem_toList hq'
    obtain ⟨C⟩ := Q.call hih
    obtain ⟨hlT, hbT', -, -, -, -⟩ := hscope _ hih
    have hsp : SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
        ++ (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)) (zs ++ []) := by
      rw [List.append_nil]; exact hzs
    have hW0 := walkCtx_blockFrame (V := V) (mT := mpC.base2) (ψ := ψ) (ihdoms := [])
      (ihvals := []) Q.hpref Q.hfld h₃0 hplQ hfl rfl
      (by simpa using hdoms) (by simpa using hokΔ)
      (by simpa using hlbFQ) (by simpa using hcbFQ) (by simpa using hherQ) hsp (by simp [SpineFit])
    simp only [List.append_nil, List.reverse_nil, List.nil_append, consList_nil,
      Nat.add_zero] at hW0
    obtain ⟨T, hT, hG⟩ := targetCall_ihTy_graded hμ hacl hin C hFr hW0 hlT hbT'
    rw [hBB] at hT
    rw [hIdE, ihDomsLifted_getD (by rw [hTsLen]; exact hq'), hTs q hq' T hT, WellDenotedV_liftN,
      ← hyl, shiftE_consList]
    exact hG _ hW0.2.1
  · -- hleafR
    intro l hl
    have hm := hlL l hl
    rw [targetFrameIh, List.mem_reverse, hfvEq'] at hm
    exact hm
  · -- hRb
    have hBv' : denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + Q.ihs.size) Q.bodyO = some Bv :=
      hBv
    rw [tgtRbAV, ← hAbs, hBc]
    simp only
    rw [← hBB, hBv', Option.getD_some]
  · -- hCa
    rw [hCaEq, ← hE, ← hBc]
    exact hCaR
  · -- hokC
    rw [hCaEq]
    have hfit := tgtOutConclFit hμ hcov h R hr hcA hrhs hMo hcl ψ
      (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ j i)
    have hargs := tgtOutConclArgs hμ hcov h R hr hcA hrhs hMo hcl ψ
      (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ j i)
    rw [hpl, hfl, hIlen] at hfit hargs
    exact blockRuleHokC_of_run hμ mpC h hr ψ hcon hfit hargs

end Certs

end ConLeche.Model
