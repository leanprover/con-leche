module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetSeam
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Semantics.Tower.BlockRecI

public section

/-!
# The nested recursors' stage: the ι equations' validity and grading (lane RECREST)

`NestedRecRest.eqV` (bit validity) and `NestedRecRest.hEq` (truth values
and grading, the family premise's equation half), at the target check's
rule data at EVERY major — the same row split as `eqB` (`tgtRowB`):

* the frame's grading on the prefix and the fields (`tgtHokPF`): a
  member's by the constructors' record (`blockRuleHokPF_run`), a
  container's off the recursor type's prefix and the instantiated
  constructor (`tgtOutCrestWd`, `tgtOutOpen`);
* the field readings (`tgtHdF`): `blockRuleHdF_seam` / `tgtOutOpen`;
* the conclusion's arguments graded (`tgtConclArgsW`):
  `blockRuleConclArgsW_run` / `tgtOutConclArgs`;
* the `ih` terms and the residue graded (`tgtRule_wdVG`, any major);
* for `hEq`'s left-hand side, the rule's spine fitting the recursor's
  binder data at every class (`tgtCls_hrule`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Rows

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}

/-- **The target equation list, at the chain spelling** (moved from
`NestedRecStage.lean`): the prefix domains are closed
(`blockRecPdomsK_run`), and the chain lifts keep the field domains'
lengths (`liftDomsK_length`). -/
theorem tgtClsEqs_eq (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat) :
    iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (fun c j => liftEsK (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
          mpC.base2.acval envC ψ)
        (fun c j => (tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type))
            out mpC.base2.acval envC ψ c j).liftN (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c
              j).length
            + (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ c j).length))
      = blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type))
            out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type))
            out mpC.base2.acval envC ψ') ψ := by
  show _ = iotaEqsAV _ _ _ _ _ _ _ _
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c _ j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ _).symm
  · simp only [tgtFdomsK, liftDomsK_length]

set_option maxHeartbeats 1000000 in
/-- **The frame's grading on the prefix and the fields, at ANY major**
(`hokPF` at the target data): a member's by the constructors' record
(`blockRuleHokPF_run`); a container's prefix off the recursor type's
graded tower, its fields off the instantiated constructor, graded at
every fitting prefix (`tgtOutCrestWd`, read by `tgtOutOpen`). -/
theorem tgtHokPF (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.toBlockShape cvTas)
    (hmem : ∀ c, (tgtMajor out c).member.isSome = true → memR c) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
  intro j r hr i cA hcA ψ
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [recStage_rulesLen h hr]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
  cases hmb : (tgtMajor out j).member with
  | some t =>
    have hm : (tgtMajor out j).member.isSome = true := by rw [hmb]; rfl
    rw [tgtFdomsAV_eq_block R hr hcA hrhs hm]
    exact blockRuleHokPF_run hμ h ⟨pk, uOfD, ppsOf, rfl⟩ hS hcore hmr j r (hmem j hm) hr i cA
      hcA ψ
  | none =>
    obtain ⟨rc', u', -, ⟨E⟩⟩ := targetEntryAt R hr
    obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hmb
    obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R hr hmb hcl ψ
    obtain ⟨-, -, -, ab, -, -, -, -, -, hfdE, -, hcrR⟩ :=
      tgtOutOpen R hr hcA hrhs hmb hcl hul hds ψ hdsa hlenP
    obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -, hwdTy⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
    have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
        = pp.toBlockShape.rulePrefixAt j := blockRulePdomsAV_length hμ mpC h hr ψ
    have hfl : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length = cA.2 :=
      tgtFdomsAV_length (fe := ConLeche.mkFEnv envC) h R _ _ ψ j r hr i cA hcA
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
        SpineFit (consList zs σ)
          ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take q) ys →
        WellDenotedV V (consList ys (consList zs σ))
          ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD q default) := by
      intro q hq σ zs ys hzs hys
      have hcw := tgtOutCrestWd hμ hcov h R hr hcA hrhs hmb hcl ψ σ hzs hcrR
      rw [hfdE] at hq hys ⊢
      exact wdV_mkPisAV_dom hcw q (by simpa using hq) ys hys
    intro l hl
    exact hokA_of_two hPgrad hFgrad l (by rw [hpl, hfl]; exact hl)

/-- **The field readings, at ANY major** (`hdF` at the target data): a
member's by the constructors' record (`blockRuleHdF_seam`), a
container's by the instantiated constructor's opening (`tgtOutOpen`). -/
theorem tgtHdF (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hmem : ∀ c, (tgtMajor out c).member.isSome = true → memR c) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → ∀ (ψ : Name → Nat) (l : Nat) (x : Expr),
      (tgtFieldFvs pp.toBlockShape out j i)[l]? = some x →
        denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
  intro j r hr i cA rhs hcA hrhs ψ
  cases hmb : (tgtMajor out j).member with
  | some t =>
    have hm : (tgtMajor out j).member.isSome = true := by rw [hmb]; rfl
    obtain ⟨-, -, hfv, -⟩ := tgtMember_eq_block R hr hcA hrhs hm
    rw [hfv, tgtFdomsAV_eq_block R hr hcA hrhs hm]
    exact blockRuleHdF_seam (fe := ConLeche.mkFEnv envC) (mpC := mpC) h hcore j r (hmem j hm) hr
      i cA rhs hcA hrhs ψ
  | none =>
    obtain ⟨rc', u', -, ⟨E⟩⟩ := targetEntryAt R hr
    obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hmb
    obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R hr hmb hcl ψ
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hfdR, -⟩ :=
      tgtOutOpen R hr hcA hrhs hmb hcl hul hds ψ hdsa hlenP
    exact hfdR

set_option maxHeartbeats 1000000 in
/-- **The conclusion's arguments are graded, at ANY major**: at a spine
fitting the rule's prefix and field domains, the index expressions and
the fired spine are `WellDenotedV` (`blockRuleConclArgsW_run` at a
member, `tgtOutConclArgs` at a container, both at `I = []`). -/
theorem tgtConclArgsW (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.toBlockShape cvTas)
    (hmem : ∀ c, (tgtMajor out c).member.isSome = true → memR c) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) ys →
      (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i,
        WellDenotedV V (consList ys ρ) e) ∧
      WellDenotedV V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i) := by
  intro j r hr i cA rhs hcA hrhs ys hys
  have hsat0 := (spineFit_iff_sat hys.length_eq).mp hys
  cases hmb : (tgtMajor out j).member with
  | some t =>
    have hm : (tgtMajor out j).member.isSome = true := by rw [hmb]; rfl
    have hc : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
    have hrj : (tgtRs out)[j] = r := (List.getElem?_eq_some_iff.mp hr).2
    have hj : i < blockRecNCt (tgtRs out) j := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some]
      exact (List.getElem?_eq_some_iff.mp hcA).1
    rw [tgtFdomsAV_eq_block R hr hcA hrhs hm] at hsat0
    have H := blockRuleConclArgsW_run hμ h ⟨pk, uOfD, ppsOf, rfl⟩ hS hcore hmr ψ (hmem j hm) hc hj
      [] (consList ys ρ) (by simpa using hsat0)
    rw [tgtEsAV_eq_block R hr hcA hrhs hm, tgtMkAV_eq_block R hr hcA hrhs hm]
    refine ⟨fun e he => ?_, ?_⟩
    · have hmemE : e ∈ blockRecEsK 0 mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j i := by
        simp only [blockRecEsK, AnnotTerm.liftN_zero, List.map_id']; exact he
      have := H (e.liftN 0 0) (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨e, hmemE, rfl⟩)))
      simpa [AnnotTerm.liftN_zero] using this
    · have := H _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      simpa [blockRecMkK, AnnotTerm.liftN_zero] using this
  | none =>
    obtain ⟨rc', u', -, ⟨E⟩⟩ := targetEntryAt R hr
    obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hmb
    have H := tgtOutConclArgs hμ hcov h R hr hcA hrhs hmb hcl ψ [] (consList ys ρ)
      (by simpa using hsat0)
    refine ⟨fun e he => ?_, ?_⟩
    · have := H (e.liftN 0 0) (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨e, he, rfl⟩)))
      simpa [AnnotTerm.liftN_zero] using this
    · have := H _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      simpa [AnnotTerm.liftN_zero] using this

set_option maxHeartbeats 1000000 in
/-- **`eqV` at every major** — the equation list at the target data is
bit-valid at every typed tuple (`annotValid_blockIotaEqsAV`): the frame
off its grading (`tgtHokPF`), the index expressions and the fired spine
off the conclusion's arguments (`tgtConclArgsW`), the `ih` terms and the
residue off `tgtRule_wdVG`. -/
theorem tgtRecEqs_validAny (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.toBlockShape cvTas)
    (hmem : ∀ c, (tgtMajor out c).member.isSome = true → memR c) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
      (∀ mm, mm < (tgtRs out).length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ mm)) →
      ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ') ψ), AnnotValid V (consList tup ρ) e := by
  intro ψ ρ tup hlen htyp
  have hcf := consList_eq_chainFrame hlen ρ
  have hformer := tgtFormer_facts (fe := ConLeche.mkFEnv envC) hmr
  have hokPF := tgtHokPF hμ hcov h R hS hcore hmr hmem
  rw [hcf]
  refine annotValid_blockIotaEqsAV (a := fun c => tup.getD c pt) (ρ := ρ)
    (fun c hc j hj => ?_) (fun c hc j hj ys hys => ?_)
  all_goals
    obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
    have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  · -- the frame, off the grading
    dsimp only
    have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
    have hfl := tgtFdomsAV_length (fe := ConLeche.mkFEnv envC) h R mpC.base2.acval envC ψ c _ hr
      j cA hcA
    refine fieldsValid_of_grading _ (fun l hl ys hys => ?_)
    have hl' : l < pp.toBlockShape.rulePrefixAt c + cA.2 := by
      rw [List.length_append, hpl, hfl] at hl; exact hl
    exact (hokPF c _ hr j cA hcA ψ l hl' ρ ys hys).2
  · dsimp only at hys ⊢
    obtain ⟨hE, hMk⟩ := tgtConclArgsW hμ hcov h R hS hcore hmr hmem ψ ρ c _ hr j cA rhs hcA hrhs
      ys hys
    obtain ⟨hCf, hCb, hCc⟩ := tgtCtorAt_closed R hN hcore hctorsAs hcov hr hcA
    obtain ⟨hI, hRb⟩ := tgtRule_wdVG (fe := ConLeche.mkFEnv envC) hμ mpC h R hformer ψ hr hcA hrhs
      (tgtDsOk_any R h hr) hCf hCb hCc (tgtHdF hμ hcov h R hcore hmem c _ hr j cA rhs hcA hrhs ψ)
      (hokPF c _ hr j cA hcA ψ) ρ tup hlen htyp ys hys
    refine ⟨fun e he => (hE e he).2, hMk.2, fun v hv => ?_, ?_⟩
    · rw [← hcf]; exact (hI v hv).2
    · rw [← hcf]; exact hRb.2

set_option maxHeartbeats 4000000 in
/-- **`hEq` at every major** — the ι equations at the target data are
truth values and graded at every typed tuple (`hEq_iotaEqsAV_of` at the
chain spelling, `tgtClsEqs_eq`): the frame off its grading
(`tgtHokPF`), the left-hand side an application chain along the
recursor's own type (the rule's spine fits it at every class,
`tgtCls_hrule`; its arguments graded by `tgtConclArgsW`), the residue
off `tgtRule_wdVG`. -/
theorem tgtRecEqs_hEqAny (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM c))
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.toBlockShape cvTas)
    {names : List Name}
    (hM : BlockModelAt mpC.base2 names (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf))
    (hmem : ∀ c, (tgtMajor out c).member.isSome = true → ConLeche.tgtMemAt out c) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        tup.getD c pt ∈ˢ interp V ρ ((blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ) c)) →
      ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ') ψ),
        interp V (consList tup ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList tup ρ) e := by
  intro ψ ρ tup hlen htyp
  have hformer := tgtFormer_facts (fe := ConLeche.mkFEnv envC) hmr
  have hokPF := tgtHokPF hμ hcov h R hS hcore hmr hmem
  have hB := tgtRowB hμ R hN hcore hctorsAs hcov hformer h hmem ψ
  rw [← tgtClsEqs_eq hμ h ψ]
  refine hEq_iotaEqsAV_of (fun as hl ht c hc j hj => ?_) tup hlen htyp
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl := tgtFdomsAV_length (fe := ConLeche.mkFEnv envC) h R mpC.base2.acval envC ψ c _ hr
    j cA hcA
  obtain ⟨hFB, -, -, -, -⟩ := hB c _ hr j cA rhs hcA hrhs
  -- the chain lift of the fields is the identity
  have hfdK : tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j
      = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j := by
    rw [tgtFdomsK, hpl]
    exact liftDomsK_eq_self_of_bounded _ _ (fieldsBelow_getD hFB)
  have hch := consList_eq_chainFrame (V := V) hl ρ
  refine ⟨?_, fun ys hys => ?_⟩
  · -- the frame, off the grading
    rw [hfdK]
    refine fieldsOkB_zero_of_spineGrading _ (fun l hl' ys hys => ?_)
    have hl2 : l < pp.toBlockShape.rulePrefixAt c + cA.2 := by
      rw [List.length_append, hpl, hfl] at hl'; exact hl'
    exact (hokPF c _ hr j cA hcA ψ l hl2 (consList as ρ) ys hys).1
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl := hxs.length_eq
  have hfsl : fs.length = cA.2 := by rw [hfs.length_eq, hfdK, hfl]
  have hsp : SpineFit (chainFrame (tgtRs out).length (fun c => as.getD c pt) ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
      (xs ++ fs) := by rw [← hch]; exact hys
  have hpK : liftDomsK (tgtRs out).length 0
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
      = blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c :=
    blockRecPdomsK_run (V := V) hμ mpC h hr ψ _
  have hbase : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) :=
    chainFit_base hpK hxl hsp
  obtain ⟨hE, hMk⟩ := tgtConclArgsW hμ hcov h R hS hcore hmr hmem ψ ρ c _ hr j cA rhs hcA hrhs
    (xs ++ fs) hbase
  refine ⟨?_, ?_⟩
  · -- the left-hand side: an application chain along the recursor's type
    have hfit := tgtCls_hrule hμ hcov h R hcls ⟨pk, uOfD, ppsOf, rfl⟩ hcore hmr hM ψ
      (tgtRs out).length (fun c => as.getD c pt) ρ c hc j hj xs fs hxl hsp
    have hflK : (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
        = fs.length := by rw [hfdK, hfl, hfsl]
    have hwl : (xs ++ fs).length
        = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length := by
      rw [List.length_append, hxl, hfl, hfsl]
    have hpv : (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length).map
          (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length (fun c => as.getD c pt) ρ)))
        = xs := by
      rw [hflK]; exact interp_prefVarsAV hxl
    have hhead : interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
          (fun c => as.getD c pt) ρ))
        (.bvar ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c))) = as.getD c pt := by
      show consList (xs ++ fs) _ _ = _
      rw [show (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c) = ((tgtRs out).length - 1 - c) + (xs ++ fs).length from by
            rw [List.length_append, hxl, hflK]; omega,
        consList_apply_add, chainFrame_apply hc]
    obtain ⟨-, -, -, -, hTyE, -, -, -, -, hwdTy⟩ := recStage_tyPis hμ mpC h hr ψ
    have hTF := teleFit_mkPisAV_of_spineFit
      (B := blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) hfit
    rw [← hTyE] at hTF
    have hvals : (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          ++ liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
          ++ [tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j]).map
          (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
            (fun c => as.getD c pt) ρ)))
        = xs ++ ((liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
              (fun c => as.getD c pt) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
              (fun c => as.getD c pt) ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)]) := by
      rw [List.map_append, List.map_append, hpv, List.map_cons, List.map_nil, List.append_assoc]
    rw [← hvals] at hTF
    have hmem' : interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
          (fun c => as.getD c pt) ρ))
        (.bvar ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c)))
        ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) := by
      rw [hhead]; exact ht c hc
    rw [← hch] at hTF hmem'
    refine (Rules.wellDenotedV_mkAppN_of_fit _
      (f := .bvar ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c))) (hwdTy ρ) ⟨trivial, trivial⟩ (fun x hx => ?_)
      hmem' hTF).1.1
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨trivial, trivial⟩
      · -- an index expression, lifted past the chain
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        rw [hch, ← hwl, wellDenotedV_liftN_chainFrame]
        exact hE e he
    · -- the fired spine, lifted past the chain
      rw [List.mem_singleton] at hx
      rw [hx, tgtMkK, hch, ← hwl, wellDenotedV_liftN_chainFrame]
      exact hMk
  · -- the residue, at the `ih` values
    obtain ⟨hCf, hCb, hCc⟩ := tgtCtorAt_closed R hN hcore hctorsAs hcov hr hcA
    obtain ⟨hIv, hRv⟩ := tgtRule_wdVG (fe := ConLeche.mkFEnv envC) hμ mpC h R hformer ψ hr hcA
      hrhs (tgtDsOk_any R h hr) hCf hCb hCc
      (tgtHdF hμ hcov h R hcore hmem c _ hr j cA rhs hcA hrhs ψ)
      (hokPF c _ hr j cA hcA ψ) ρ as hl ht (xs ++ fs) hbase
    have hIv' : ∀ v ∈ tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type))
        out mpC.base2.acval envC ψ c j, WellDenotedV V (consList (xs ++ fs) (consList as ρ)) v :=
      hIv
    have hRv' : WellDenotedV V (consList ((tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape
        (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j).map
          (interp V (consList (xs ++ fs) (consList as ρ)))) (consList (xs ++ fs) ρ))
        (tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
          mpC.base2.acval envC ψ c j) := hRv
    rw [wd_instsAV (fun v hv => (hIv' v hv).1)]
    have key := (wellDenotedV_liftN_chainFrame (K := (tgtRs out).length)
      (a := fun c => as.getD c pt) (ρ := ρ)
      ((xs ++ fs) ++ (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type))
        out mpC.base2.acval envC ψ c j).map (interp V (consList (xs ++ fs) (consList as ρ))))
      (tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ c j)).mpr (by simpa only [consList_append] using hRv')
    rw [← hch] at key
    simp only [consList_append, List.length_append, List.length_map] at key ⊢
    rw [← hxl, ← hfs.length_eq]
    exact key.1

end Rows

end ConLeche.Model
