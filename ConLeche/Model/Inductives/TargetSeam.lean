module

public import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Inductives.BlockRecInv

public section

/-!
# The seam's conjuncts at the target check's rule data (lane RECLIB, B3 (d))

`declBlock_data`'s existential (`BlockRecData.lean` §A.18) at
`ihs := tgtIhsAV`, `Rb0 := tgtRbAV` (`TargetRuleData.lean`) and today's
four syntactic components, for blocks where both checks ran
(`checkBlockRecK … = .ok (tgtRs out)` and a `TargetRecRun … out`).
Each conjunct is today's producer made generic in `ihs`/`Rb0`
(`…_gen`, `BlockDeclRun.lean`) fed the target rows.
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
  {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)}
  {env₀ : Env} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {nested : Bool} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The stored constructor types' scoping, at every stored rule — off
the constructors' core record at the member the recursor's list is. -/
theorem tgtCtor_facts {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat), r.2.2.2[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true ∧
        ConstsBound fe.env cA.1.type := by
  intro c r hr j cA hcA
  obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  exact ⟨hwfC.1, hwfC.2.2.2.1, constsBound_of_constsResolve _ hwfC.2.2.1⟩

/-- The formers' types are closed — off the members' run record. -/
theorem tgtFormer_facts
    (hmr : BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.toBlockShape cvTas) :
    ∀ cv ∈ cvTas, cv.type.hasFvar = false := by
  intro cv hcv
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
  exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1

/-- **`heqB` at the target data** — `blockRecEqs_below_gen` with the two
target rows (`tgtRule_below`). -/
theorem tgtRecEqs_below_seam (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hmr : BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.toBlockShape cvTas)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length) :
    ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ') ψ,
        Term.bvarsBelow (tgtRs out).length e.erase := by
  have hC := tgtCtor_facts (mpC := mpC) h hcore
  have hformer := tgtFormer_facts hmr
  refine blockRecEqs_below_gen hμ h hcore hkLen
    (fun ψ c r hr j cA rhs hcA hrhs => ?_) (fun ψ c r hr j cA rhs hcA hrhs => ?_)
  all_goals obtain ⟨hCf, hCb, hCc⟩ := hC c r hr j cA hcA
  · exact (tgtRule_below hμ mpC.base2 h R hformer ψ hr hcA hrhs hCf hCb hCc).1
  · exact (tgtRule_below hμ mpC.base2 h R hformer ψ hr hcA hrhs hCf hCb hCc).2

end Seam

end ConLeche.Model
