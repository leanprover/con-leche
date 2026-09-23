module

import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockKitRuleRun
public import ConLeche.Model.Inductives.BlockRuleCaRun
import ConLeche.Model.Inductives.BlockIndRuleRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Annot.BitInst

public section

/-!
# The rule certificates at the run — `hcertsW` produced

`blockRuleCerts_of_run` (`BlockRecPreRun.lean` §40.13) states the
certificate bundle at ONE rule from some thirty inputs.  At the pinned
data every one of them is a fact of the run:

* the stored types' closedness and constants — the environment's
  well-formedness (`checkBlockRecK_facts`, the constructor's own `wf`);
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
theorem blockRuleConclArgs_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c) :
    ∀ σ : Nat → V,
      Sat V ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse) σ →
      ∀ a ∈ paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
              + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
              + (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length)
          ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (·.liftN (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0)
          ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
              (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0],
        WellDenotedV V σ a := by
  intro σ hsat
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  -- the context's values, split into the prefix, the fields and the `ih` block
  have hL : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, -⟩ := spineFit_append_split hab
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  have hwl : ws.length = (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length :=
    hws.length_eq
  -- the rule's own spine, peeled to the constructor's datum (at `K = 0`)
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]
    exact hab
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, -, hpre, -, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj hxl hsp0
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 :=
    blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ
  -- the constructor's parameter fit (the hop through the member's former)
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
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
          (e.liftN (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0)
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

/-- **`hcertsW` AT THE RUN** — `blockRuleCerts_of_run` at every
(recursor, constructor) pair of the run, at the base frame, at the
pinned `ih` openers' domains `blockRuleIhdomsAV`, the pinned residue
`blockRuleRbAV` and the pinned conclusion `blockRuleCaAV`.  Every input
is the run's (module docstring). -/
theorem blockRuleCertsW_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) :
    ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j)
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleRbAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleCaAV p rs mpC.base2.acval envC ψ c j) := by
  intro ψ c hc j hj
  have hfit := blockRuleConclFit_run (mpC := mpC) hμ h hkLen hcore hmr hM hN
    (by obtain ⟨_, _, _, _, rfl⟩ := hdR; rfl)
    (by
      obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
      intro c r hr
      obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
      show ctorsAs.getD _ [] = _
      rw [List.getD_eq_getElem?_getD, hctA]; rfl) ψ hc hj
  have hargs := blockRuleConclArgs_run hμ h hkLen hdR hS hcore hmr ψ hc hj
  have hexI := fun (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
      (hr : rs[c]? = some r) (cA : ConstantVal × Nat) (hcA : r.2.2.2[j]? = some cA) =>
    blockRuleIhReads_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ
  have hrec := blockRuleRecord_run hμ h hkLen hdR hN hS hcore hmr hM
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  have hctM : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c) = rs[c].2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c))[j]? = some cA := by rw [hctM]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hcdP := hcd
  rw [show (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP = p.nP
    from rfl] at hcdP
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hcbC : ConstsBound envC cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hnP := TE.nP_le
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  -- the constructor's opened telescope: `hstripC`, `hksLen`
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).fvsPF
            (p.toBlockShape.recTgtAt c) j
          ++ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xFvsF
            (p.toBlockShape.recTgtAt c) j,
          (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xrestF
            (p.toBlockShape.recTgtAt c) j) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hks : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ksF
      (p.toBlockShape.recTgtAt c) j = (blockRuleKsOf p c j).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hksLen : (blockRuleKsOf p c j).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  -- the stored recursor type
  obtain ⟨hf₁, -, -, -, -⟩ := ConLeche.checkBlockRecK_facts h rs[c] (List.mem_of_getElem? hr)
  have hcT : ConstsBound envC rs[c].1.type :=
    constsBound_of_constsResolve _ (ConLeche.checkBlockRecK_facts h rs[c]
      (List.mem_of_getElem? hr)).2.2.1
  -- stage (c)'s peel
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, h₁, hinstC, -, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  have hc₂ : ConstsBound envC (blockRuleCrest p.toBlockShape rs c j) :=
    constsBound_instPisAt _ hinstC hcbC
      (fun a ha => (openPisAtFvars_constsBound _ hcT h₁).1 a (List.mem_of_mem_take ha))
  obtain ⟨rbs, ty, concl, -, -, -, hopen, hinf, hconcl, hdeq⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨-, -, -, -, -, -, -, hbodyO, -, -, -, hw₃, hreadAll, hb₃, hfv₃, hc₃⟩ :=
    blockRuleOpenedFull_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  have hRb : denoteMeta mpC.base2.acval envC ψ
      (p.toBlockShape.rulePrefixAt c + cA.2 + (blockRuleFrameAt p rs c j).nR)
      (blockRuleBodyOAt p rs c j) = some (blockRuleRbAV p rs mpC.base2.acval envC ψ c j) := by
    obtain ⟨B, hB⟩ := hreadAll ψ
    rw [blockRuleRbAV, hct, ← hbodyO, hB]
    rfl
  -- the pinned conclusion: its reading and its peel
  obtain ⟨hCaR, hcon⟩ := blockRuleCaAV_run hμ h hr hcA hrhs hcdP hCf hCb hfindC hlpsC hnP ψ
  -- the record group and the per-key `ih` data
  obtain ⟨cvTa, caps, nFull, resSort, pps, dsC, bodyC, hcvTa, hfT, hFD, hle, hwd, hlenD, hframes,
    ho, hFE, hIlen, hIent⟩ := hrec c rs[c] hr j cA hcA ψ
  -- the base components' spellings
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 :=
    blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ
  have hIdE : blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j
      = readOpenedDoms mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2)
          (blockRuleFvsIhAt p rs c j) := by
    rw [blockRuleIhdomsAV, hct]
  rw [hpl, hfl, hIlen] at hfit hargs
  rw [hIdE] at hfit hargs hIent
  rw [hfl, hIlen, hIdE]
  exact blockRuleCerts_of_run hμ mpC h hr ψ hcA hrhs hf₁ hCf hCb hcT hc₂ hopen hw₃ hb₃ hfv₃ hc₃
    hinf hdeq hconcl hRb (hCaR concl hconcl)
    (fun l x hx => ⟨_, (blockRuleFdomsAV_eq h hr hcA hrhs hcdP hCf hnP ψ).2 l x hx⟩)
    (hexI rs[c] hr cA hcA)
    hcvTa hfT hFD hle hwd hlenD hframes ho hFE hIent hcon hfit hargs


/-- **The certificate family at a CHAIN frame** — `blockRuleCertsW_run`
past `K` chain binders: the field and `ih` domains' `K` lifts are the
identity and so is the residue's (`blockRuleCertsChain_eq`).  At the
pinned `ihdoms := blockRecIhdomsK K` and `Ca := blockRuleCaAV` this is
the kit arms' `hcerts` row verbatim (`K := rs.length` for WF, `K := 1`
for SQ); with the residue lifted (`blockRuleCertsChain_eq`'s third
component) it is regime IND's certificate conjunct. -/
theorem blockRuleCertsK_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (K : Nat) :
    ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        (blockRecIhdomsK K p mpC.base2.acval envC rs ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j)
        (blockRecIhdomsK K p mpC.base2.acval envC rs ψ c j)
        (blockRuleRbAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleCaAV p rs mpC.base2.acval envC ψ c j) := by
  intro ψ c hc j hj
  have hW := blockRuleCertsW_run hμ h hkLen hdR hN hS hcore hmr hM ψ c hc j hj
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨e1, e2, -⟩ := blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj K
  rw [e1, e2]
  exact hW

end Certs

end ConLeche.Model
