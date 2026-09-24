module

public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockDeclRun

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
  {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}

/-- **Row: the ι equations are truth values and graded** at the target
data (`hwd`, B3 (e) 8). -/
theorem tgtRecEqs_hEq (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A fssZ envI
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
  sorry

end Rows

end ConLeche.Model
