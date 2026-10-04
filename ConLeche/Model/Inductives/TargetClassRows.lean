module

public import ConLeche.Model.Inductives.TargetClasses

public section

/-!
# The graph kit's two `ih` rows at every class

`tgtRecPre_cls`'s premises `hihF` (the graph-built `ih` values fit the
`ih` domains) and `hchain` (the `ih` chain), at the classes: at the frame
of ANY class (`tgtFrame_cls`) and with the call's target a major of the
callee's class read off the callee spine's fit (`tgtKey_cls`) by the
classes' own `hsplit` and `hconcl` rows.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **THE INDUCTION OVER THE RECURSOR CLASSES, at a call relation**
`call` (`hind`): at every parameter tuple `xs`, the union of the classes'
carriers is well-founded under the graph's predecessor relation — the
recursor family's calls from a major's decoding at its class.  The call
relation is a parameter; the recursors' stage uses it at the generated
calls (`GenClassInd`, `GenRecAssembly.lean`). -/
@[expose] def TgtClassIndG (envC : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
    (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
    (ψ : Name → Nat) (ρ : Nat → V) (call : List V → Nat → Nat → List V → V → Prop) : Prop :=
  ∀ xs : List V, ∀ P : V → Prop,
    (∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) →
      (∃ e, graphDecG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
          (tgtClsInj d Dc mc cvc p out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length
          (tgtClsFit d Dc mc cvc acval envC p out ψ ρ) xs u e ∧
        ∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
            (tgtClsCr d Dc mc cvc acval envC p out ψ ρ)
            (tgtRs out).length call xs e →
          P v) → P u) →
    ∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) → P u

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {names : List Name} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- A class's index set lives under the prefix guard. -/
theorem tgtClsIs_pref {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape}
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {c : Nat} {i : V}
    (hi : i ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c) :
    SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs := by
  classical
  unfold tgtClsIs at hi
  by_cases hG : tgtClsG d acval envC p out ψ ρ xs c
  · unfold tgtClsG at hG
    split at hG
    · exact hG.2
    · exact hG
  · rw [ite_eq_right hG] at hi; exact absurd hi (not_mem_empty _)

end Rows

end ConLeche.Model
