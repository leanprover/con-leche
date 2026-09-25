module

public import ConLeche.Model.Inductives.NestedRecStage
public import ConLeche.SetModel.NestRecCls
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.TargetClassBridge

public section

/-!
# The class induction as ONE induction over the positivity NODES (lane NESTIND, session 16)

`NestedClassIndOwed` (`NestedRecStage.lean`) asks `TgtClassInd`: the
induction principle of the recursor family's majors, over every class.
F13 (coordinator's ruling): the kit's classes are the positivity
derivation's NODES — one instantiation may be visited at several nodes,
and the visits' nesting orders the induction.  F14 and the coordinator's
ruling (i): the positivity walk will cover OFFICIAL's auxiliary set
(N2-eager: a container's whole mutual group; the syntactic, pre-whnf
container occurrences), so EVERY recursor class is a node; the
reached/unreached split of session 15 is gone.

* `TgtNodeCore` — the node kit at a prefix spine WITHOUT the tie of the
  classes to nodes: an induction over node majors (`NestNodeInd`, either
  kit's — `NestKitB` at `w ≠ 0`, `NestKit` at `w = 0`), a relation
  `Rel c b` (node `b` visits recursor class `c`), and at every related
  pair the class's data are the node's and its calls land at related
  nodes.  This is NESTIND's to build (from `posD_nodes`, the (D) bridge
  `dField_mem` + `targetCall_genD`, `lfpNestKit`/`lfpNestKitB`).
* `TgtNodeKit S` — a core plus the TIE on the classes `S`: every class of
  `S` has a node (`hex`).  At `S` = every class this is exactly what
  ruling (i) supplies (every outside major is a node of the walk).
* `tgtClassIndOn_of_kit` — the property at every major of an `S` class;
  `tgtClassInd_of_kit` — `TgtClassInd` from a kit at every class.
* `NestedClassNodesOwed` — at every nested context, a node kit at every
  class; `nestedClassIndOwed_of_nodes` — it gives `NestedClassIndOwed`.
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

section Classes

variable (μ : CheckMode) (F : Nat) (envC : Env)
  (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape) (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
  (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
  (ψ : Name → Nat) (ρ : Nat → V)

/-- `TgtClassInd`'s closure hypothesis at the prefix spine `xs`: a major
with a decoding whose predecessors all have the property has it. -/
@[expose] def TgtClassStep (xs : List V) (P : V → Prop) : Prop :=
  ∀ u, u ∈ˢ unionSet (tgtRs out).length
      (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) →
    (∃ e, graphDecG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (tgtClsInj d Dc mc cvc p out ψ) (blockRecNCt (tgtRs out))
        (tgtRs out).length
        (tgtClsFit d Dc mc cvc acval envC p out ψ ρ) xs u e ∧
      ∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
          (tgtClsCr d Dc mc cvc acval envC p out ψ ρ)
          (tgtRs out).length
          (tgtCall μ F (mkFEnv envC) p formerTys out
            acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs e →
        P v) → P u

/-- **The class induction on the classes `S`**: the property at every
major of a class of `S`. -/
@[expose] def TgtClassIndOn (S : Nat → Prop) : Prop :=
  ∀ xs : List V, ∀ P : V → Prop, TgtClassStep μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs P →
    ∀ c, c < (tgtRs out).length → S c →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c) t → P (tagged c t x)

/-- On every class, it is `TgtClassInd`. -/
theorem tgtClassInd_of_on
    (h : TgtClassIndOn μ F envC acval p formerTys out d Dc mc cvc ψ ρ fun _ => True) :
    TgtClassInd μ F envC acval p formerTys out d Dc mc cvc ψ ρ := by
  intro xs P hP u hu
  obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hu
  exact h xs P hP c hc trivial t ht x hx

end Classes

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
  hpredR : ∀ c b, c < (tgtRs out).length → Rel c b → ∀ t j fs, ∀ v,
    v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
        (tgtCall μ F (mkFEnv envC) p formerTys out
          acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs (c, j, fs) →
      ∃ c' t' y, c' < (tgtRs out).length ∧ v = tagged c' t' y ∧ ∃ b', Rel c' b' ∧
        nenc b' (mOf c' b') t' y ∈ˢ K.pred ⟨b, mOf c b, t, j, fs⟩

/-- **The node kit on the classes `S`**: a core whose relation gives
every class of `S` a node (`hex`, THE TIE). -/
structure TgtNodeKit (μ : CheckMode) (F : Nat) (envC : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape) (formerTys : List Expr)
    (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
    (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
    (ψ : Name → Nat) (ρ : Nat → V) (S : Nat → Prop) (xs : List V)
    extends TgtNodeCore μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs where
  hex : ∀ c, c < (tgtRs out).length → S c → ∃ b, Rel c b

/-- **The class induction on `S` from a node kit at every prefix spine.** -/
theorem tgtClassIndOn_of_kit {S : Nat → Prop}
    (hK : ∀ xs : List V, Nonempty
      (TgtNodeKit μ F envC acval p formerTys out d Dc mc cvc ψ ρ S xs)) :
    TgtClassIndOn μ F envC acval p formerTys out d Dc mc cvc ψ ρ S := by
  intro xs P hP
  obtain ⟨N⟩ := hK xs
  exact N.K.ind_recNodesOn (tgtRs out).length S N.Rel N.mOf
    (blockRecNCt (tgtRs out)) (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
    (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) (tgtClsInj d Dc mc cvc p out ψ)
    (tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs)
    (graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
      (tgtCall μ F (mkFEnv envC) p formerTys out
        acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs)
    N.hex N.hb N.hm N.hIs N.hCr N.hinj N.hnCt N.hfit
    (fun c b hc hR t j fs v hv => N.hpredR c b hc hR t j fs v hv) P hP

/-- **`TgtClassInd` from a node kit at every class** (ruling (i): every
class is a node). -/
theorem tgtClassInd_of_kit
    (hK : ∀ xs : List V, Nonempty
      (TgtNodeKit μ F envC acval p formerTys out d Dc mc cvc ψ ρ (fun _ => True) xs)) :
    TgtClassInd μ F envC acval p formerTys out d Dc mc cvc ψ ρ :=
  tgtClassInd_of_on _ _ _ _ _ _ _ _ _ _ _ _ _ (tgtClassIndOn_of_kit hK)

end Kit

/-! ## `NestedClassIndOwed` from the node kits -/

/-- **OWED — the node kit at every nested context and every class**
(ruling (i)).  Its one ingredient only (i) supplies is the kit's `hex` at
EVERY class — every recursor class, outside majors included, visited by a
node of the block's positivity derivation; the core (`TgtNodeCore`) is
NESTIND's. -/
@[expose] def NestedClassNodesOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR →
    ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
        Nonempty (TgtNodeKit μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type))
          out dR Dc mc cvc ψ ρ (fun _ => True) xs)

/-- **`NestedClassIndOwed` from the node kits.** -/
theorem nestedClassIndOwed_of_nodes {μ : CheckMode} {F : Nat} {block : List ConstantInfo}
    (h : NestedClassNodesOwed V μ F block) : NestedClassIndOwed V μ F block :=
  fun envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx Dc mc cvc hcls ψ ρ =>
    tgtClassInd_of_kit
      (h envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx Dc mc cvc hcls ψ ρ)

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

end ConLeche.Model
