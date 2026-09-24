module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockKitRuleRun
public import ConLeche.Model.Inductives.BlockRuleCaRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.BlockLfpHoles

public section

/-!
# The rule certificates at the run — `hcertsW` produced

`blockRuleCerts_of_run` (`BlockRecPreRun.lean` §40.13) states the
certificate bundle at ONE rule from some thirty inputs.  At the pinned
data every one of them is a fact of the run:

* the stored types' closedness and constants — the environment's
  well-formedness (`recStage_facts`, the constructor's own `wf`);
* stage (c)'s peel — `blockRuleResidueData_runP` (the opening, the two
  typing runs, the conclusion's `instPisAtLift`) and
  `blockRuleOpenedFull_run` (the generated tower's scoping, closedness,
  leaves and constants, and the opened residue's reading, which IS the
  pinned `Rb0 = blockRuleRbAV`);
* the conclusion's reading and peel at the pinned `Ca = blockRuleCaAV`
  (`blockRuleCaAV_run`): `hCa` and `hpeel`;
* the two segments' reading existences — `blockRuleFdomsAV_eq` (fields)
  and `blockRuleIhReads_run` (the `ih` openers);
* the record group and the per-key `ih` data — `blockRuleRecord_run`
  (`BlockRuleGrading.lean`, factored out of the grading producer);
* `hokC`'s fit — `blockRuleConclFit_run` — and its
  arguments' grading, §1 here.

§2 assembles them: `blockRuleCertsW_run` is the `hcertsW` row at the
pinned `Ca`, which `declBlock_run` consumes.

**The frame.**  Everything is at the BASE frame: the rule's own
context `ihdoms.reverse ++ (pdoms ++ fdoms).reverse` with the base
components (`blockRuleFdomsAV`, `blockRuleIhdomsAV`).  The seam lifts
the family past the chain with `blockRuleCertsChain_eq`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-! ## 0. The rule's conclusion FITS the recursor's tower -/

section ConclFit

/-- **The rule's conclusion FITS the recursor's tower** at every frame
satisfying the rule's context: the peel's arguments — the prefix
bvars, the constructor's result index readings and the fired spine,
each lifted past the `ih` block — read along the recursor type's
Π-tower.  It is `blockRuleCerts_of_run`'s `hfit`, at the peel's own argument
list. -/
theorem blockRuleConclFitW_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c)
    (I : List AnnotTerm) :
    ∀ σ : Nat → V,
      Sat V (I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse) σ →
      ∃ rest, TeleFitPA V σ (blockRecTyAV mpC.base2.acval envC rs ψ c)
        (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
              + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
              + I.length)
          ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (·.liftN I.length 0)
          ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
              I.length 0]) rest := by
  intro σ hsat
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  -- the context's values, split into the prefix, the fields and the `ih` block
  have hL : I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ I).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      ++ I).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hab
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  have hfl : fs.length = (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length :=
    hfs.length_eq
  have hwl : ws.length = I.length :=
    hws.length_eq
  -- the kit's fired-spine fit, at `K = 0`
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]
    exact hab
  have hfire := blockKitRule_run hμ h hcore hmr hM hdnP hctM ψ 0 (fun _ => pt) σ₀
    c hc j hj xs fs hxl hsp0
  rw [chainFrame_zero] at hfire
  -- the recursor's tower, and its binder data's bounds
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  obtain ⟨hbndR, -⟩ := recStage_tyBounds hμ mpC h hr ψ
  -- the argument list reads to the fired spine's values
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hpb : (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
          + I.length)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀)) = xs := by
    have hLlen : (xs ++ fs ++ ws).length
        = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
          + I.length := by
      rw [List.length_append, List.length_append, hxl, hfl, hwl]
    rw [map_bvarAt_take (nP := (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length)
      hLlen.symm (by rw [hLlen]; omega), List.append_assoc, List.take_left' hxl]
  have hes : ((blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (·.liftN I.length 0)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀))
      = (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (interp V (consList (xs ++ fs) σ₀)) := by
    rw [List.map_map]
    refine List.map_congr_left fun e _ => ?_
    show interp V (consList (xs ++ fs ++ ws) σ₀)
      (e.liftN I.length 0) = _
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals e
  have hmk : interp V (consList (xs ++ fs ++ ws) σ₀)
        ((blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
          I.length 0)
      = interp V (consList (xs ++ fs) σ₀)
          (blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) := by
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals _
  -- the tower's binder data is closed below its own entries, so the fit
  -- moves from the base frame to the context's
  have hbnd : ∀ l, l < ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (fun b : Nat × Nat × AnnotTerm => b.2.2)).length →
      Term.bvarsBelow l ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
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


end ConclFit

/-! ## 1. `hokC`'s arguments are graded -/

section ConclArgs

/-- **The rule conclusion's peel arguments are graded** at every frame
satisfying the rule's context — `blockRuleCerts_of_run`'s `hargs`, at
the argument list `blockRuleConclFit_run` fits.  The prefix entries are
bound variables; an index reading is the constructor's own
(`blockRuleSpine_peel`'s `es0`), graded at the constructor's field frame
(`blockCtorEs_wdV`) and lifted twice; the fired spine is graded at the
rule's base frame (`blockRuleMkAV_wdV`).  The `ih` block is lifted over
(`WellDenotedV_liftN`, `shiftE_consList_ih`). -/
theorem blockRuleConclArgsW_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {envI : Env}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c)
    (I : List AnnotTerm) :
    ∀ σ : Nat → V,
      Sat V (I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse) σ →
      ∀ a ∈ paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
              + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
              + I.length)
          ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (·.liftN I.length 0)
          ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
              I.length 0],
        WellDenotedV V σ a := by
  intro σ hsat
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  -- the context's values, split into the prefix, the fields and the `ih` block
  have hL : I.reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ I).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      ++ I).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, -⟩ := spineFit_append_split hab
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  have hwl : ws.length = I.length :=
    hws.length_eq
  -- the rule's own spine, peeled to the constructor's datum (at `K = 0`)
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]
    exact hab
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, -, hpre, -, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hcore hmr rfl hctM hr hj hxl hsp0
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 :=
    blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ
  -- the constructor's parameter fit (the hop through the member's former)
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hcvTa := TE.hcvTa
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
  have hframes := (hS.frames _ hmemk j cA hcj).1 ψ
  have hcd := hcf.2.2
  have hpc := blockRuleParamFit_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
    (hcd.len ψ) hframes (spineFit_take_any hpre p.nP)
  -- the frame, with the `ih` block on top
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hdrop : ∀ e : AnnotTerm,
      WellDenotedV V (consList (xs ++ fs ++ ws) σ₀)
          (e.liftN I.length 0)
        ↔ WellDenotedV V (consList (xs ++ fs) σ₀) e := by
    intro e
    rw [WellDenotedV_liftN, hframe, ← hwl,
      show consList ws (consList (xs ++ fs) σ₀)
        = consList ([] : List V) (consList ws (consList (xs ++ fs) σ₀)) from rfl,
      shiftE_consList_ih (d := 0) (locals := ([] : List V)) (ihvals := ws) rfl rfl]
    rfl
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · -- a prefix variable
      simp only [paramBvarsAt, List.mem_map] at ha
      obtain ⟨k, -, rfl⟩ := ha
      exact ⟨trivial, trivial⟩
    · -- an index reading, lifted past the fields' cutoff and the `ih` block
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      rw [hdrop]
      rw [blockRecEsK] at he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      rw [hes] at he'
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he'
      rw [hpl, hfl]
      exact (wellDenotedV_liftN_rule (K := 0) (a := fun _ => (pt : V)) hxs' hfsl E).mpr
        (blockCtorEs_wdV hcf hcj hpc hfb E hE)
  · -- the fired constructor application
    rw [List.mem_singleton] at ha
    rw [ha, hdrop, blockRecMkK, AnnotTerm.liftN_zero]
    exact blockRuleMkAV_wdV h hr hcA hrhs hcf hcj rfl hnP hxs' hfsl hpc hfb

end ConclArgs

/-! ## 2. The certificate family, at the pinned `Ca` -/

section Certs

end Certs

end ConLeche.Model
