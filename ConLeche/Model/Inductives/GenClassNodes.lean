module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetNodePres
public import ConLeche.Model.Inductives.TargetNodeList

public section

/-!
# The class induction at the GENERATED calls (lane GENREC-B2)

`genClassInd` — `GenClassInd` (`GenRecAssembly.lean`) over the old node
route: the node presentation over the positivity derivation's node list
(`TgtNodePres`, generic over the call relation), its calls re-proved for
the generated calls (`genCallT`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The generated stage's context holds the shared one. -/
theorem GenRecCtx.base {F : Nat} {block : List ConstantInfo} {envC envI : Env}
    {pp : BlockParts} {cvTasR : List ConstantVal} {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (h : GenRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      posR) :
    RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- `GenClassInd` is the generic class induction at the generated calls. -/
theorem genClassInd_iff {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env} {p : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    {ihd : Nat → Nat → List IhDatum} {ψ : Name → Nat} {ρ : Nat → V} :
    GenClassInd acval envC p out d Dc mc cvc ihd ψ ρ ↔
      TgtClassIndG envC acval p out d Dc mc cvc ψ ρ
        (genCallT (tgtClsTup d Dc mc cvc p out ψ) ρ ihd) := Iff.rfl

end ConLeche.Model
