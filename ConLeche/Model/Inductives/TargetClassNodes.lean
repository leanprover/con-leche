module

public import ConLeche.SetModel.NestRecCls
public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.TargetClassBridge

public section

/-!
# The node kit's core, and `dField_mem`'s premises at an outside class (lane NESTIND, session 16)

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
* `dField_prems_of_outCls` — the (D) bridge's group and freshness
  premises at an outside class.
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
induction `K` over node majors (`NestNodeInd` — `NestKitB.toNodeInd` at
`w ≠ 0`, `NestKit.toNodeInd` at `w = 0`), a relation `Rel c b` — node `b`
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

/-! ## `dField_mem`'s `hXfix`, from the block's freshness -/

/-- **A container's constructor names no member**: a constructor stored
at `envC` concluding in a NON-member inductive was stored in the older
environment (`BlockOverEnv`), where it resolves and no member is stored. -/
theorem ctorTy_fresh_of_over {envC : Env} {names : List Name}
    (hover : BlockOverEnv envC names) {n : Name} {cv : ConstantVal} {nPc nF : Nat}
    (hf : envC.find? n = some (.ctorInfo cv nPc nF)) {bs : List (Expr × ConLeche.BinderMeta)}
    {args : List Expr} {I : Name} {us : List Level}
    (hconcl : cv.type.stripPis (nPc + nF) = some (bs, Expr.mkAppN (.const I us) args))
    (hI : I ∉ names) :
    ∃ env₀ : Env, (∀ n ∈ names, env₀.find? n = none) ∧ cv.type.constsResolve env₀ = true := by
  obtain ⟨env₀, hwf, hfr, hback⟩ := hover
  refine ⟨env₀, hfr, ?_⟩
  rcases hback n _ hf with h0 | ⟨cv', caps, h⟩ | ⟨cv', nP', nF', bs', body, us', m, h, hs, hhd, hm⟩
  · exact (hwf _ (ConLeche.Semantics.Env.find?_mem h0)).2.2.1
  · exact nomatch h
  · obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj h
    rw [hconcl] at hs
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
    rw [getAppFn_mkAppN_const] at hhd
    obtain ⟨rfl, -⟩ := Expr.const.inj hhd
    exact absurd hm hI

omit [SetTheory V] in
/-- **`hXfix` at a recorded container's constructor**: the constructor of
member `c` of a recorded datum `D`, where `D.member c` is no member of the
block, at any levels, its container group replaced by variables, is fixed
by the member abstraction. -/
theorem hXfix_of_over {envC : Env} {names : List Name} (hover : BlockOverEnv envC names)
    {D : LfpDatum V} (hown : LfpOwn envC D) {c j : Nat} (hc : c < D.k) (hj : j < D.nctors c)
    (hout : D.member c ∉ names) {cv : ConstantVal} {nPc nF : Nat}
    (hf : envC.find? (D.ctorName c j) = some (.ctorInfo cv nPc nF))
    (lvls : List Level) (holes : List Expr) (us : List Level) (hi : Nat)
    (grp : List (Name × Expr)) :
    ConLeche.targetAbs names lvls holes
        ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts (ConLeche.grpSub us hi grp))
      = (cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
          (ConLeche.grpSub us hi grp) := by
  obtain ⟨cv', nPc', nF', hf', bs, args, hs, -⟩ := hown.ctorConcl c hc j hj
  rw [hf] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hf')
  obtain ⟨env₀, hfr, hres⟩ := ctorTy_fresh_of_over hover hf hs hout
  refine targetAbs_replaceConsts_fresh grpSub_fvar hfr _ ?_
  rw [Expr.constsResolve_instantiateLevelParams]
  exact hres

/-- **`dField_mem`'s named premises at an outside class** (`TgtOutCls`):
the (D) group is the container's whole recorded block (`hgrpN`, `hgrpM`,
`hfull`), and every constructor of the container's member, at any levels
and group substitution, is fixed by the member abstraction (`hXfix`) —
from coverage and the block's freshness (`BlockOverEnv`). -/
theorem dField_prems_of_outCls {envC : Env} {mpC : EnvModelM V μ envC}
    (hcov : LfpCover mpC []) {names : List Name} (hover : BlockOverEnv envC names)
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (h : TgtOutCls mpC M D mm cvI) (hnm : M.ind ∉ names)
    {fe : FEnv} (hfe : fe.find? = envC.find?) {gtys : List Expr}
    (hg : (ConLeche.targetOwnGroup fe M).mapM (ConLeche.targetGrpHoleTy fe M.lvls) = some gtys) :
    ((ConLeche.targetOwnGroup fe M).Nodup ∧
      (∀ n ∈ ConLeche.targetOwnGroup fe M, ∃ mm', mm' < D.k ∧ n = D.member mm') ∧
      ∀ mm', mm' < D.k → InGrp D ((ConLeche.targetOwnGroup fe M).zip gtys) mm') ∧
    ∀ j, j < D.nctors mm → ∀ (cv : ConstantVal) (nPc nF : Nat),
      envC.find? (D.ctorName mm j) = some (.ctorInfo cv nPc nF) →
      ∀ (lvls : List Level) (holes : List Expr) (us : List Level) (hi : Nat)
        (grp : List (Name × Expr)),
      ConLeche.targetAbs names lvls holes
          ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
            (ConLeche.grpSub us hi grp))
        = (cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
            (ConLeche.grpSub us hi grp) := by
  obtain ⟨caps, hf⟩ := h.hfind
  rw [← h.hmem] at hf
  refine ⟨dField_grp_of_cover hfe h.hmm h.hnN h.hkN h.hmem.symm hf
      (hcov.all D h.hD mm h.hmm _ _ hf) hg, fun j hj cv nPc nF hc => ?_⟩
  exact hXfix_of_over hover (hcov.own D h.hD) h.hmm hj (by rw [h.hmem]; exact hnm) hc

end ConLeche.Model
