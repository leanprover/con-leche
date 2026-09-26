module

public import ConLeche.SetModel.NestRecCls
public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.BlockCover

public section

/-!
# The node kit's core (lane NESTIND, session 16)

`NestedClassIndOwed` (`NestedRecStage.lean`) asks `TgtClassInd`: the
induction principle of the recursor family's majors, over every class.
F13 (coordinator's ruling): the kit's classes are the positivity
derivation's NODES — one instantiation may be visited at several nodes,
and the visits' nesting orders the induction.  F14 and the coordinator's
ruling (i): the positivity walk will cover OFFICIAL's auxiliary set
(N2-eager: a container's whole mutual group; the syntactic, pre-whnf
container occurrences), so EVERY recursor class is a node.

* `TgtNodeCore` — the node kit at a prefix spine WITHOUT the tie of the
  classes to nodes: an induction over node majors (`NestNodeInd`), a
  relation `Rel c b` (node `b` visits recursor class `c`), and at every
  related pair the class's data are the node's and its calls land at
  related nodes.  It is built from a node presentation
  (`TgtNodePres.core`, `TargetNodePres.lean`), where `NestedClassNodesOwed`
  lives.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The node kit -/

section Kit

variable {μ : CheckMode} {F : Nat} {envC : Env}
  {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape} {formerTys : List Expr}
  {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
  {ψ : Name → Nat} {ρ : Nat → V}

/-- **The node kit at a prefix spine, without the classes' tie** (F13's
ruling: the kit's classes are the positivity derivation's NODES): an
induction `K` over node majors (`NestNodeInd` — `NestKit.toNodeInd`), a relation `Rel c b` — node `b`
is a visit of recursor class `c`, at the node clause's component
`mOf c b` — and at every related pair the recursor class's index set,
carrier, injection, constructor count, decoding fit and call targets are
the node's (`hpredR`: which node a call lands at depends on the caller's
node — the caller, an enclosing node, or a kid). -/
structure TgtNodeCore (μ : CheckMode) (F : Nat) (envC : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape) (formerTys : List Expr)
    (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
    (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) where
  K : NestNodeInd V (Nat → V)
  Rel : Nat → Nat → Prop
  mOf : Nat → Nat → Nat
  hb : ∀ c b, c < (tgtRs out).length → Rel c b → b < K.nC
  hm : ∀ c b, c < (tgtRs out).length → Rel c b → mOf c b < (K.cl b).N
  hIs : ∀ c b, c < (tgtRs out).length → Rel c b →
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c = (K.cl b).Is (mOf c b)
  hCr : ∀ c b, c < (tgtRs out).length → Rel c b →
    tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c = K.KT b (mOf c b)
  hinj : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ j fs,
    tgtClsInj d Dc mc cvc p out ψ c j fs = (K.cl b).inj (mOf c b) j fs
  hnCt : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → j < blockRecNCt (tgtRs out) c
  hfit : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs,
    (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs →
      tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs c t j fs
  hpredR : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs, t ∈ˢ (K.cl b).Is (mOf c b) →
    (K.cl b).Fits (K.fr b) (K.KT b) t (mOf c b) j fs → ∀ v,
    v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
        (tgtCall μ F (mkFEnv envC) p formerTys out
          acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs (c, j, fs) →
      ∃ c' t' y, c' < (tgtRs out).length ∧ v = tagged c' t' y ∧ ∃ b', Rel c' b' ∧
        nenc b' (mOf c' b') t' y ∈ˢ K.pred ⟨b, mOf c b, t, j, fs⟩

end Kit

end ConLeche.Model
