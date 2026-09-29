module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetGraph
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockRuleGrading

public section

/-!
# The seam's conjuncts at the target check's rule data

The recursors' stage's seam facts at `ihs := tgtIhsAV`, `Rb0 := tgtRbAV`
(`TargetRuleData.lean`): the formers' facts, the rule's field readings,
and the `ℓ = 0` arm (`tgtRuleRaZ_seam`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Seam

variable {fe : FEnv} {envI : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ fe.env} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
 
  {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {nested : Bool} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}

/-- The formers' types are closed — off the members' run record. -/
theorem tgtFormer_facts
    (hmr : BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.toBlockShape cvTas) :
    ∀ cv ∈ cvTas, cv.type.hasFvar = false := by
  intro cv hcv
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
  exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1

/-- The rule's field readings — off the constructors' record
(`blockRuleFdomsAV_eq`, kind-free). -/
theorem blockRuleHdF_seam {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs rs memR)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k) :
    ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), memR c →
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ (ψ : Name → Nat) (l : Nat) (x : Expr),
      (blockRuleFieldFvs pp.toBlockShape rs c j)[l]? = some x →
        denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval fe.env ψ c j).getD l
              default) := by
  intro c r hm hr j cA rhs hcA hrhs ψ
  obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt (hm := hm) h hr
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hcd := blockCtorData_of_core hcore hcj
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  exact (blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hwfC.1 TE.nP_le ψ).2

omit [SetTheory V] in
/-- The indexed bare-recursor cons carries the plain one's environment. -/
theorem consBlockRecsBareF_env (q : ConLeche.BlockShape) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (fe' : FEnv),
      (ConLeche.consBlockRecsBareF q m cvRas fe').env = ConLeche.consBlockRecsBare q m cvRas fe'.env
  | _, [], _ => rfl
  | m, (cvRa, nIdx) :: rest, fe' => by
    simp only [ConLeche.consBlockRecsBareF, ConLeche.consBlockRecsBare]
    exact consBlockRecsBareF_env q (m + 1) rest _

end Seam

end ConLeche.Model
