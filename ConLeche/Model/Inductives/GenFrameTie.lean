module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetNodeList

public section

/-!
# The frame half of the class tie at the generated stage (lane GENREC-B2)

`genNodeFrameTie` — `NodeFrameTie` from the generated stage's run.  Every
class is checked over the block's CANONICAL parameters (`R.ctx.params`,
the positivity context's `fvsP`), so the class match's defeq soundness
(`params_read_eq`) runs at the parameters' own walk context (the first
former's parameter telescope at the prefix's first `nP` values, which fit
the block's parameters by `hparG`), and the two readings move to the rule
prefix's depth (`tgtRP`) unchanged: both spines name only the parameters.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  GenRecRun fueledOps mkFEnv NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The frame tie at the generated stage** (see the module docstring). -/
theorem genNodeFrameTie (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : NestState} {nested : Bool}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR cvTasR
      block ctorsAsR out)
    (h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (ConLeche.tgtRs out) (fun _ => False))
    (hparG : ∀ c, c < (ConLeche.tgtRs out).length → ∀ (ψ : Name → Nat) (ρ : Nat → V)
      (xs : List V),
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (ConLeche.tgtRs out) ψ c)
        xs → SpineFit ρ (dR.params ψ) (xs.take dR.nP))
    {fvsP : List Expr} (hctxR : R.ctx = pp.nestCtx fvsP envI.find? envI.consts)
    (ns : List ConLeche.PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    NodeFrameTie mpC.base2.acval (pp.nestCtx fvsP envI.find? envI.consts) pp.toBlockShape out ns
      ψ ρ xs envC F (cvTasR.map (·.type)) := by
  sorry

end ConLeche.Model
