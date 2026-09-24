module

import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.InstList
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.StructLaws
import ConLeche.Model.Inductives.BlockRuleGrading

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

/-- **`heqP`'s equation half at the target data** —
`blockRecEqs_params_gen` with the two target rows (`tgtRule_params`). -/
theorem tgtRecEqs_params_seam (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ') ψ₁
          = blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ') ψ₂ :=
  blockRecEqs_params_gen hμ h hcore hkLen
    (fun _ _ hr _ _ _ hcA hrhs _ _ hq => (tgtRule_params mpC.base2 h R hr hcA hrhs hq).1)
    (fun _ _ hr _ _ _ hcA hrhs _ _ hq => (tgtRule_params mpC.base2 h R hr hcA hrhs hq).2)

/-- **THE RULE CONTRACT at the target data** — `blockRuleDataB_seam_gen`
with its residue conjunct `tgtRuleResidueB`, fed today's field readings
(`blockRuleHdF_seam`) and the frame's grading at the prefix and the
fields (`blockRuleHokPF_of`). -/
theorem tgtRuleDataB_seam (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hndM : pp.toBlockShape.memberNames.Nodup)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A fssZ envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).toLfp
      ∈ mpC.lfpBlocks)
    (hmr : BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.toBlockShape cvTas)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some
      ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM c))
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    {s : (Name → Nat) → Nat}
    (heqB : ∀ ψ : Name → Nat, ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ, Term.bvarsBelow (tgtRs out).length e.erase)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
      (∀ mm, mm < (tgtRs out).length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ mm)) →
      ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ, AnnotValid V (consList tup ρ) e)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ₁ = (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ₂)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ) ρ)
    -- the frame's grading (today's, `blockRuleGrading_run`)
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
    ∀ m₃ : EnvModel V (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env),
      m₃.acval = blockRecAcv mpC.base2.acval fe.env (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) →
    ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), (tgtRs out)[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        BlockRuleDataB (V := V) mpC pp (tgtRs out) s (blockRecNCt (tgtRs out))
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ')
          (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ')
          (blockRecCtorTy mpC.base2.acval fe.env (tgtRs out) j i) φ j i r cA
          (ConLeche.recRuleBits fe.env.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
              fire := .plain, rhs := rhs, paramsBlind := true }) rhs := by
  have hC := tgtCtor_facts (mpC := mpC) h hcore
  have hformer := tgtFormer_facts hmr
  have hPF := blockRuleHokPF_of hμ h hkLen hokA
  have hdF := blockRuleHdF_seam (mpC := mpC) h hcore
  refine blockRuleDataB_seam_gen hμ h hndM hN hS hcore hlfp hctorsAs heqB heqV heqP hpre ?_
  intro m₃ hac φ j r hr i cA rhs hcA hrhs hread hsp
  obtain ⟨hCf, hCb, hCc⟩ := hC j r hr i cA hcA
  exact tgtRuleResidueB hμ h R hndM hr hcA hrhs hac (blockRecLeafAV_closed hμ mpC h heqB) hpre
    hCf hCb hCc hformer (hdF j r hr i cA rhs hcA hrhs) (hPF j r hr i cA hcA) hread hsp


omit [SetTheory V] in
/-- The indexed bare-recursor cons carries the plain one's environment. -/
theorem consBlockRecsBareF_env (q : ConLeche.BlockShape) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (fe' : FEnv),
      (ConLeche.consBlockRecsBareF q m cvRas fe').env = ConLeche.consBlockRecsBare q m cvRas fe'.env
  | _, [], _ => rfl
  | m, (cvRa, nIdx) :: rest, fe' => by
    simp only [ConLeche.consBlockRecsBareF, ConLeche.consBlockRecsBare]
    exact consBlockRecsBareF_env q (m + 1) rest _

/-- **The `ℓ = 0` arm at a rule binding no variable, at the target data**
— the rule is its own residue (no field, no call: `targetAbstract_noFields`),
so the family's ι law at the empty spine says it reads as the recursor's
value, which is the point there. -/
theorem tgtRuleRaZ_empty (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {s : (Name → Nat) → Nat} {es0 : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ) ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hz : pp.toBlockShape.rulePrefixAt j + cA.2 = 0)
    {ψ : Name → Nat} {Ra : AnnotTerm}
    (hread : denoteMeta (blockRecAcv mpC.base2.acval fe.env (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')))
      (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env) ψ 0 rhs = some Ra)
    (hℓ : Level.eval ψ
      (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0)
    (ρ : Nat → V) : interp V ρ Ra = pt := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
    exact (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs⟩ := tgtRuleAt_facts h R hr hcA hrhs
  -- the stored rule: closed, fvar-free
  obtain ⟨-, -, -, -, hrhsF⟩ := ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hrf, -, hres, hrb⟩ := hrhsF rhs (List.mem_of_getElem? hrhs)
  -- an empty telescope: the body is the rule, and nothing is abstracted
  have hrP0 : rc.rP = 0 := by omega
  have hnF0 : cA.2 = 0 := by omega
  have hbody : Q.body = rhs := by
    have key : ∀ (n : Nat) (bs : List (Expr × ConLeche.BinderMeta)) (b : Expr),
        ConLeche.Expr.stripLams n rhs = some (bs, b) → n = 0 → b = rhs := by
      intro n bs b hs hn
      subst hn
      simp only [ConLeche.Expr.stripLams, Option.some.injEq] at hs
      exact (Prod.mk.inj hs).2.symm
    exact key _ _ _ Q.hstrip (by omega)
  have hfvsP : Q.fvsPref = [] :=
    List.eq_nil_of_length_eq_zero (by rw [openPisAtFvars_length _ Q.hpref, hrP0])
  have hfvsF : Q.fvsF = [] :=
    List.eq_nil_of_length_eq_zero (by rw [openPisAtFvars_length _ Q.hfld, hnF0])
  have hmono : ∀ n : Name,
      ((ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe).env.find? n).isSome = true →
      (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
        Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large))).recNames.contains n = false →
      (fe.env.find? n).isSome = true := by
    intro n hn hnot
    rw [consBlockRecsBareF_env] at hn
    rcases find?_consBlockRecsBare_isSome 0 _ fe.env n hn with hm | hm
    · have hnames : (tgtFam pp.toBlockShape (tgtRs out)).recNames = (tgtRs out).map (·.1.name) :=
        checkBlockRecK_recNamesEq h
      simp only [ConLeche.targetFrameOf] at hnot
      rw [hnames] at hnot
      rw [List.map_map] at hm
      exact absurd (List.contains_iff_mem.mpr hm) (by simpa using hnot)
    · exact hm
  have hab := Q.habs
  rw [hbody] at hab
  have hinst : rhs.instantiateList (Q.fvsPref ++ Q.fvsF).reverse = rhs := by
    rw [hfvsP, hfvsF]; exact ConLeche.Expr.instantiateList_nil rhs 0
  rw [hinst] at hab
  obtain ⟨hbO, hihs, hcbT⟩ := targetAbstract_noFields (B := rc.rP + cA.2)
    (by simp only [ConLeche.targetFrameOf]; exact hfvsF) hle hmono 0 rhs #[] _ _ hab hrf
  have hcb : ConstsBound fe.env rhs := hcbT (by
    rw [consBlockRecsBareF_env]; exact constsBound_of_constsResolve _ hres)
  have hreadC : denoteMeta mpC.base2.acval fe.env ψ 0 rhs = some Ra :=
    (blockRecDenote_cross_eq h ψ 0 rhs hcb).trans hread
  have hRacl : Term.bvarsBelow 0 Ra.erase :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hrf) hrb hreadC
  -- the target residue IS the rule, and there is no `ih` term
  have hRb : tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
      fe.env ψ j i = Ra := by
    rw [tgtRbAV, ← hAbs, hB]
    simp only
    rw [hbO, hihs, hrP0, hnF0]
    simp only [Array.size_empty, Nat.add_zero]
    rw [hreadC]; rfl
  have hIh : tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
      fe.env ψ j i = [] := by
    rw [tgtIhsAV, ← hAbs]
    simp only
    rw [hihs]; rfl
  -- the ι law at the empty spine
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j).length
      = 0 := by
    rw [blockRulePdomsAV_length hμ mpC h hr ψ]; omega
  have hfl : (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).length
      = 0 := by
    rw [blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ]; omega
  obtain ⟨a, ha, hlaw⟩ := blockRecAV_iota (hpre ψ ρ)
  have ha0 : a j = pt :=
    eq_pt_of_mem_univZero (blockRecTyZ_run hμ mpC h j hj ψ ρ hℓ) (ha j hj).1
  have hsp : SpineFit (chainFrame (tgtRs out).length a ρ)
      (liftDomsK (tgtRs out).length 0
          (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j)
        ++ liftDomsK (tgtRs out).length
          (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j).length
          (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i)) ([] ++ []) := by
    rw [List.eq_nil_of_length_eq_zero hpl, List.eq_nil_of_length_eq_zero hfl]
    trivial
  have hlawE := hlaw j hj i hi [] [] (by simp [hpl]) hsp
  dsimp only at hlawE
  rw [ha0, List.nil_append, foldl_app_pt, hRb, hIh, liftN_eq_self_of_closed hRacl,
    interp_closed V hRacl _ ρ] at hlawE
  exact hlawE.symm

/-- **THE `ℓ = 0` ARM'S RIGHT SIDE at the target data**: every stored
rule reads as the point where the checked elimination level is zero —
by its head binder's datum (`blockRuleRaZ_run`, kind-free) or, binding
no variable, by the ι law (`tgtRuleRaZ_empty`). -/
theorem tgtRuleRaZ_seam (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {s : (Name → Nat) → Nat} {es0 : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')) ψ) ρ) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
        denoteMeta (blockRecAcv mpC.base2.acval fe.env (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ')))
          (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env) ψ 0 rhs
            = some Ra →
        Level.eval ψ
          (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
        ∀ ρ : Nat → V, interp V ρ Ra = pt := by
  intro j r hr i cA rhs hcA hrhs ψ Ra hread hℓ ρ
  by_cases hz : pp.toBlockShape.rulePrefixAt j + cA.2 = 0
  · exact tgtRuleRaZ_empty hμ h R hpre hr hcA hrhs hz hread hℓ ρ
  · exact blockRuleRaZ_run (V := V) h hr hcA hrhs (Nat.pos_of_ne_zero hz) hread hℓ ρ

end Seam

/-! ## The composition at the target data

`declBlock_data` (`BlockRecData.lean` §A.18) with every seam conjunct at
the TARGET rule data, for blocks where both checks ran (`htgt`: the
target check's run at the constructors' environment, its stored family
today's).  One premise is left, `hpreT`: the family's recursor model at
the target data — the graph producer (`blockRecPre_graph`) re-instanced
at the target `ih` terms (its predecessor relation read off the calls,
B4's induction). -/

section Compose

set_option maxHeartbeats 1000000 in
/-- **`declBlock` at the target data, the recursor model owed.** -/
theorem declBlock_target (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : ConLeche.BlockParts}
    (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env p₀ env₂)
    -- both checks ran: the target check's run, its family today's
    (htgt : ∀ (envC : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat)))
        (rsR : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))),
        ConLeche.checkBlockRecK (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp cvTasR
          ctorsAsR = .ok rsR →
        ∃ (fe : FEnv) (nested : Bool) (blk : List ConstantInfo)
          (out : List (ConstantVal × TargetMajor × List Expr)),
          fe.env = envC ∧ rsR = tgtRs out ∧
          Nonempty (ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTasR ctorsAsR out))
    -- OWED (B3 (e) + B4): the recursor model at the target data
    (hpreT : ∀ (fe : FEnv) (envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat))) (nested : Bool) (blk : List ConstantInfo)
        (out : List (ConstantVal × TargetMajor × List Expr)) (mpC : EnvModelM V μ fe.env)
        (isRecR : Bool) (A : Nat → (Name → Nat) → AnnotTerm)
        (fssZ : (Name → Nat) → Nat → List (List AnnotTerm)) (env₀ : Env)
        (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
        ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTasR ctorsAsR out →
        ConLeche.checkBlockRecK (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) fe.env pp cvTasR
          ctorsAsR = .ok (tgtRs out) →
        pp.toBlockShape.memberNames.Nodup →
        BlockNamesOk (V := V)
          (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) cvTasR →
        BlockCtorsStage (V := V) μ F
          (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) pp.lps cvTasR
          pp.toBlockShape isRecR A fssZ envI pp.ctorNamesAt →
        BlockCtorsCore mpC.base2
          (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) pp.lps cvTasR
          pp.toBlockShape isRecR A
          (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).k →
        (blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf).toLfp
          ∈ mpC.lfpBlocks →
        (∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAsR[c]? = some ctorsA →
          (pp.kinds.getD c []).length = ctorsA.length) →
        ∀ s : (Name → Nat) → Nat,
        (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
          interp V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ c) ∈ˢ (univ (s ψ) : V) ∧
            WellDenoted V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ c)) →
        ∀ (ψ : Name → Nat) (ρ : Nat → V),
          ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
            (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
                (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
                (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
                (fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
                (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
                  mpC.base2.acval fe.env ψ')
                (fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
                (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
                  mpC.base2.acval fe.env ψ')) ψ) ρ) :
    Nonempty (EnvModelM V μ env₂) :=
  declBlock_data hμ mp hE hdp hrun
    fun envC envI pp cvTasR ctorsAsR rsR mpC dR isRecR A fssZ hrec hnd hnames hstage hcore
        hctorsAs hctorsIn hdR hlfp hkLen => by
      obtain ⟨fe, nested, blk, out, hfe, hrs, ⟨R⟩⟩ := htgt envC pp cvTasR ctorsAsR rsR hrec
      subst hfe hrs
      obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) hμ hrec
      obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
      have hmr := blockMembersRun_seam hnames hstage hcore
      have hM := blockModelAt_seam hrec hnames hstage hcore hlfp
      have hokA := blockRuleGrading_run hμ hrec hkLen ⟨env₀, pk, uOfD, ppsOf, rfl⟩ hnames hstage
        hcore hmr hM
      have heqB := tgtRecEqs_below_seam hμ hrec R hcore hmr hkLen
      have heqV := tgtRecEqs_valid_seam hμ hrec R hnames hstage hcore hmr hkLen hokA
      have heqP := fun i r hr ψ₁ ψ₂ hq =>
        And.intro (hsP i r hr ψ₁ ψ₂ hq) (tgtRecEqs_params_seam hμ hrec R hcore hkLen i r hr ψ₁ ψ₂ hq)
      have hpre := hpreT fe envI pp cvTasR ctorsAsR nested blk out mpC isRecR A fssZ env₀ pk uOfD
        ppsOf R hrec hnd hnames hstage hcore hlfp hkLen s hTy
      refine ⟨s, blockRecNCt (tgtRs out),
        fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ',
        fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ',
        fun ψ' => blockRuleEsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ',
        fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
          mpC.base2.acval fe.env ψ',
        fun ψ' => blockRuleMkAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ',
        fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTasR.map (·.type)) (tgtRs out)
          mpC.base2.acval fe.env ψ',
        blockRecCtorTy mpC.base2.acval fe.env (tgtRs out),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact heqB
      · exact heqV
      · exact heqP
      · exact hpre
      · exact fun j r hr => blockRecNCt_ge hr
      · exact fun ψ j r hr => blockRulePdomsAV_length hμ mpC hrec hr ψ
      · exact blockRecCtor_seam hrec hnames hcore hctorsAs
      · exact tgtRuleDataB_seam hμ hrec R hnd hnames hstage hcore hlfp hmr hctorsAs hkLen heqB
          heqV heqP hpre hokA
      · exact blockRecTyZ_run hμ mpC hrec
      · exact tgtRuleRaZ_seam hμ hrec R hpre

end Compose

end ConLeche.Model
