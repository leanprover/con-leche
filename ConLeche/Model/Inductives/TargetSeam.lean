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

/-- The rule's field readings — off the constructors' record (today's
`blockRuleFdomsAV_eq`, kind-free). -/
theorem blockRuleHdF_seam {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ (ψ : Name → Nat) (l : Nat) (x : Expr),
      (blockRuleFieldFvs pp.toBlockShape rs c j)[l]? = some x →
        denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval fe.env ψ c j).getD l
              default) := by
  intro c r hr j cA rhs hcA hrhs ψ
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
  have hcd := blockCtorData_of_core hcore hcj
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  exact (blockRuleFdomsAV_eq h hr hcA hrhs hcd hwfC.1 TE.nP_le ψ).2

/-- **`heqV` at the target data** — `blockRecEqs_valid_gen` with the two
target rows (`tgtRule_valid`); the frame's grading is today's
(`hokA`, restricted to the prefix and the fields by
`blockRuleHokPF_of`). -/
theorem tgtRecEqs_valid_seam (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A fssZ envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hmr : BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.toBlockShape cvTas)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hokA : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2
          + (blockRuleFrameAt pp (tgtRs out) j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i
            ++ blockRuleIhdomsAV pp (tgtRs out) mpC.base2.acval fe.env ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i
            ++ blockRuleIhdomsAV pp (tgtRs out) mpC.base2.acval fe.env ψ j i).getD l default)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
      (∀ mm, mm < (tgtRs out).length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ mm)) →
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ') ψ,
        AnnotValid V (consList tup ρ) e := by
  have hC := tgtCtor_facts (mpC := mpC) h hcore
  have hformer := tgtFormer_facts hmr
  have hPF := blockRuleHokPF_of hμ h hkLen hokA
  have hdF := blockRuleHdF_seam (mpC := mpC) h hcore
  refine blockRecEqs_valid_gen hμ h hN hS hcore hkLen hPF
    (fun ψ ρ tup hlen htyp c r hr j cA rhs hcA hrhs ys hys => ?_)
    (fun ψ ρ tup hlen htyp c r hr j cA rhs hcA hrhs ys hys => ?_)
  all_goals obtain ⟨hCf, hCb, hCc⟩ := hC c r hr j cA hcA
  · exact (tgtRule_valid hμ mpC h R hformer ψ hr hcA hrhs hCf hCb hCc
      (hdF c r hr j cA rhs hcA hrhs ψ) (hPF c r hr j cA hcA ψ) ρ tup hlen htyp ys hys).1
  · exact (tgtRule_valid hμ mpC h R hformer ψ hr hcA hrhs hCf hCb hCc
      (hdF c r hr j cA rhs hcA hrhs ψ) (hPF c r hr j cA hcA ψ) ρ tup hlen htyp ys hys).2

end Seam

end ConLeche.Model
