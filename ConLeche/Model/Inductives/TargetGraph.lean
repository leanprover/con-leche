module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetRowCerts
import ConLeche.Model.Inductives.TargetRowCall
import ConLeche.Model.Inductives.TargetRowInd
import ConLeche.Model.Inductives.TargetRowEq

public section

/-!
# The recursor model at the TARGET data (lane RECLIB, B3 (e) + B4)

`declBlock_target`'s last premise, `hpreT`, is the family's recursor
model at the target check's rule data: `blockRecPre_graph_gen`
(`BlockRecGraph.lean`) at the target keys (`TargetIhData.lean`) and the
lfp clause's HOLE fit (`blockHoleFitRel`).  The fit's two translations
to the stored fit are the representation's `carrier` (the override law
at the least tuple); the rows are the target run's.
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

/-! ## The hole fit against the stored fit -/

section Fit

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}

/-- **The hole fit IS the stored fit** at the carrier, at fitting
parameters and an index tuple of the component (`BlockModelAt.carrier`,
the override law). -/
theorem blockHoleFitRel_iff (hM : BlockModelAt mo names d) {ψ : Name → Nat} {ρ : Nat → V}
    {mem : Nat → Nat} {xs : List V} {c : Nat} {i : V} {j : Nat} {fs : List V}
    (hpar : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hmN : mem c < d.N)
    (hi : i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c)) :
    blockHoleFitRel d ψ ρ mem xs c i j fs ↔ blockStoredFitRel d ψ ρ mem xs c i j fs :=
  hM.carrier ψ _ (d.satOfSpine hpar) (mem c) hmN i hi j fs

end Fit


/-! ## THE PRODUCER at the target data -/

section Producer

set_option maxHeartbeats 2000000 in
/-- **THE RECURSOR MODEL AT THE TARGET DATA** — `declBlock_target`'s
`hpreT`: `blockRecPre_graph_gen` at the target keys and the hole fit,
its rows the target run's (`tgtRuleCerts_run`, `tgtGraphIhF_run`,
`tgtKitCaB_run`, `tgtGraphIhChain_run`, `tgtGraphInd_run`,
`tgtRecEqs_hEq`), the fit's translations the recorded clause's `holes`
(`blockHoleFitRel_iff`). -/
theorem tgtRecPre_graph (hμ : μ.verifiedChecks = true) {F : Nat}
    (fe : FEnv) (envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat))) (nested : Bool) (blk : List ConstantInfo)
    (out : List (ConstantVal × TargetMajor × List Expr)) (mpC : EnvModelM V μ fe.env)
    (isRecR : Bool) (A : Nat → (Name → Nat) → AnnotTerm)
    (env₀ : Env)
    (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTasR ctorsAsR out)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTasR ctorsAsR (tgtRs out))
    (hnd : pp.toBlockShape.memberNames.Nodup)
    (hfresh : ∀ n ∈ (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).memberNames,
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).env₀.find? n = none)
    (hnames : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) cvTasR)
    (hstage : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) pp.lps cvTasR
      pp.toBlockShape isRecR A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) pp.lps cvTasR
      pp.toBlockShape isRecR A
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).toLfp
      ∈ mpC.lfpBlocks)
    (s : (Name → Nat) → Nat)
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
      interp V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ c) ∈ˢ (univ (s ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ c)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ') ψ) ρ := by
  have hdR : ∃ (env₀' : Env) (pk' : Nat → BlockMemberPick)
      (uOfD' : Nat → (Name → Nat) → Nat)
      (ppsOf' : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf
        = blockDataOf V pp.toBlockShape env₀' ctorsAsR pp.kinds pk' uOfD' ppsOf' :=
    ⟨env₀, pk, uOfD, ppsOf, rfl⟩
  have hmr := blockMembersRun_seam hnames hstage hcore
  have hM := blockModelAt_seam h hnames hstage hcore hlfp
  have hC := (mpC.lfp_ok _ hlfp).1
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r →
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    show ctorsAsR.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hmN : ∀ (ψ : Name → Nat) c, c < (tgtRs out).length → pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).N := fun ψ c hc =>
    Nat.lt_of_lt_of_le
      (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1
      (Nat.le_add_right _ _)
  have hgen := @blockRecPre_graph_gen V _ μ fe.env mpC pp cvTasR ctorsAsR (tgtRs out) F
    (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).memberNames
    (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) hμ isRecR A envI
    h hdR hnames hstage hcore hmr hM s hTy
    (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ')
    (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ')
    (fun ψ' => tgtIhdomsAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ')
    (fun ψ' => tgtCaAV μ F fe (cvTasR.map (·.type)) (tgtRs out) mpC.base2.acval fe.env pp ψ')
    (fun ψ' ρ' => tgtIhv μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ'
      (Level.eval ψ' (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) ρ')
    (fun ψ' ρ' => tgtCall μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ'
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) ρ')
    (fun ψ' ρ' => blockHoleFitRel
      (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) ψ' ρ'
      pp.toBlockShape.recTgtAt)
  refine hgen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ψ' ρ' xs c i j fs hc hpar hi hf =>
      (blockHoleFitRel_iff hM hpar (hmN ψ' c hc) hi).mp hf
  · exact fun ψ' ρ' xs c i j fs hc _ hpar hi hf =>
      (blockHoleFitRel_iff hM hpar (hmN ψ' c hc) hi).mpr hf
  · exact tgtRecEqs_hEq hμ h R hdR hnames hstage hcore hmr hM
  · exact tgtRuleCerts_run hμ h R hdR hnames hstage hcore hmr hM
  · exact fun ψ' ρ' xs => tgtGraphIhF_run hμ h R hdR hnames hstage hcore hmr hM hC hnd ψ' ρ' xs
  · exact fun ψ' ρ' xs => tgtKitCaB_run hμ h R hcore hmr hM rfl hctM ψ' ρ' xs
  · exact fun ψ' ρ' xs => tgtGraphInd_run hμ h R hdR hnames hstage hcore hmr hM hC hnd hfresh ψ' ρ' xs
  · exact fun ψ' ρ' a xs r hfold => tgtGraphIhChain_run hμ h R hdR hnames hstage hcore hmr
      hM hC hnd ψ' ρ' a xs r hfold

end Producer

end ConLeche.Model
