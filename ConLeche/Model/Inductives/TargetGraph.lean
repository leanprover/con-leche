module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetRowCerts

public section

/-!
# The hole fit against the stored fit (lane RECLIB, B3 (e) + B4)

The lfp clause's HOLE fit (`blockHoleFitRel`) is the stored fit at the
carrier: the representation's `carrier` (the override law at the least
tuple).
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

end ConLeche.Model
