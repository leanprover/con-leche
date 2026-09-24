module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreHpre
public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The target recursor model's rows: the ι equations graded at the target data (lane RECLIB)

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

section Rows

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

/-- **Row: the ι equations are truth values and graded** at the target
data (`hwd`, B3 (e) 8).  `hEq_iotaEqsAV_of` at the base spelling
(`blockRecEqs_base`): the domains' `FieldsOkB` and the left-hand side
are the prefix-and-fields grading (`blockRuleHokPF_run` through
`blockGradeHokA_chain`) and `blockGradeLhs_run`; the residue at
the target data is `tgtRule_wdV`'s `WellDenoted` halves, carried past
the chain by `wd_instsAV` and `wellDenotedV_liftN_chainFrame`. -/
theorem tgtRecEqs_hEq (hμ : μ.verifiedChecks = true)
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
    (hM : BlockModelAt mpC.base2 names d) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        tup.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ c)) →
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ') ψ,
        interp V (consList tup ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList tup ρ) e := by
  intro ψ ρ tup hlen htyp
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the frame's grading on its prefix and fields, and the left-hand side
  have hPF := blockRuleHokPF_run hμ h hdR' hS hcore hmr
  have hlhs := blockGradeLhs_run hμ h hdR' hN hS hcore hmr hM
  have hokA := blockGradeHokA_chain hμ h (blockRuleDoms_bounded_at hμ h hcore) hPF
  -- the stored constructor types' scoping and the formers' closedness
  have hformer : ∀ cv ∈ cvTas, cv.type.hasFvar = false := by
    intro cv hcv
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  rw [← blockRecEqs_base (V := V)
    (ihs := fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ')
    (Rb0 := fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ') hμ mpC h ψ]
  refine hEq_iotaEqsAV_of (fun as hl ht c hc j hj => ?_) tup hlen htyp
  refine ⟨fieldsOkB_zero_of_spineGrading _ (hokA ψ ρ as hl ht c hc j hj),
    fun ys hys => ⟨hlhs ψ ρ as hl ht c hc j hj ys hys, ?_⟩⟩
  -- the residue: the target rows at the base frame
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hjr : j < (tgtRs out)[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, (tgtRs out)[c].2.2.2[j]? = some cA :=
    ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, (tgtRs out)[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  -- the constructor's record
  obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hcd := blockCtorData_of_core hcore hcj
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hdF := fun ψ' => (blockRuleFdomsAV_eq h hr hcA hrhs hcd hwfC.1 TE.nP_le ψ').2
  -- the spine, at the base frame
  have hch := consList_eq_chainFrame (V := V) hl ρ
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl0 := hxs.length_eq
  have hxsρ : SpineFit ρ
      (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) xs := by
    rw [hch, ← blockRecPdomsK_run hμ mpC h hr ψ (tgtRs out).length, blockRecPdomsK] at hxs
    exact (spineFit_liftDomsK (K := (tgtRs out).length) (ρ := ρ) _ [] xs).mp hxs
  have hfsρ : SpineFit (consList xs ρ)
      (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j) fs := by
    rw [hch, blockRecFdomsK, ← hxl0] at hfs
    exact (spineFit_liftDomsK (K := (tgtRs out).length) (ρ := ρ) _ xs fs).mp hfs
  have hysρ := SpineFit.append hxsρ hfsρ
  obtain ⟨hIv, hRv⟩ := tgtRule_wdV hμ mpC h R hformer ψ hr hcA hrhs hwfC.1 hwfC.2.2.2.1
    (constsBound_of_constsResolve _ hwfC.2.2.1) (hdF ψ) (hPF c _ hr j cA hcA ψ) ρ as hl ht
    (xs ++ fs) hysρ
  rw [wd_instsAV (fun v hv => (hIv v hv).1)]
  have key := (wellDenotedV_liftN_chainFrame (K := (tgtRs out).length)
    (a := fun c => as.getD c pt) (ρ := ρ)
    ((xs ++ fs) ++ (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ c j).map (interp V (consList (xs ++ fs) (consList as ρ))))
    (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
      fe.env ψ c j)).mpr (by simpa only [consList_append] using hRv)
  rw [← hch] at key
  simp only [consList_append, List.length_append, List.length_map] at key ⊢
  rw [← hxl0, ← hfs.length_eq]
  exact key.1

end Rows

end ConLeche.Model
