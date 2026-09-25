module

public import ConLeche.Model.Inductives.NestedRecStage
public import ConLeche.SetModel.NestRecCls

public section

/-!
# The class induction in TWO PHASES (lane NESTIND, session 15; coordinator's ruling (a))

`NestedClassIndOwed` (`NestedRecStage.lean`) asks `TgtClassInd`: the
induction principle of the recursor family's majors, over every class.
POSDERIV found that an outside major need not be a positivity key
(`corner_posderiv_major_delta`, `corner_posderiv_major_group`: official
builds its auxiliary recursors by a SYNTACTIC pre-pass and copies whole
container groups), so the ruling splits the classes:

* the REACHED classes (`TgtReach`): the member classes and every class a
  reached class's rule CALLS — syntactically, by the rules' `ih` lists.
  Their induction is the node kit's (the positivity derivation's nodes,
  `NestKitB.ind_recNodesOn`, `SetModel/NestRecCls.lean`); a reached
  class's calls stay reached, so this phase needs nothing else
  (`TgtClassIndReached`);
* the UNREACHED classes: their induction runs AFTER, with the property
  already at every reached major (`TgtClassIndUnreached`).

`tgtClassInd_of_phases` composes them; `nestedClassIndOwed_of_phases`
restates `NestedClassIndOwed` as the two phases at the reached set.
FINDING F14 (DESIGN): the unreached phase is NOT one recorded clause's
induction at the true frame in general — fixtures
`corner_nestind_unreached_{mates,nested,f13}`.
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

/-! ## The reached classes, syntactically -/

section Reach

variable (μ : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr))

/-- Class `c`'s rule `j` CALLS class `c'`: one of its `ih` variables'
callee (the recursor it recurses into). -/
@[expose] def TgtCallsTo (c c' : Nat) : Prop :=
  ∃ j ih, ih ∈ tgtIhL μ F fe p formerTys out c j ∧ ih.callee = c'

/-- **The reached classes**: the member classes and, closed under the
rules' calls, every class they reach. -/
inductive TgtReach : Nat → Prop
  | member {c : Nat} : c < (tgtRs out).length → (tgtMajor out c).member.isSome →
      TgtReach c
  | call {c c' : Nat} : TgtReach c → c' < (tgtRs out).length →
      TgtCallsTo μ F fe p formerTys out c c' → TgtReach c'

end Reach

/-! ## The two phases -/

section Phases

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

/-- **Phase 1, the REACHED classes**: the property at every major of a
class of `S`. -/
@[expose] def TgtClassIndReached (S : Nat → Prop) : Prop :=
  ∀ xs : List V, ∀ P : V → Prop, TgtClassStep μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs P →
    ∀ c, c < (tgtRs out).length → S c →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c) t → P (tagged c t x)

/-- **Phase 2, the UNREACHED classes**: with the property at every major
of a class of `S`, the property at every major. -/
@[expose] def TgtClassIndUnreached (S : Nat → Prop) : Prop :=
  ∀ xs : List V, ∀ P : V → Prop, TgtClassStep μ F envC acval p formerTys out d Dc mc cvc ψ ρ xs P →
    (∀ c, c < (tgtRs out).length → S c →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c) t → P (tagged c t x)) →
    ∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) → P u

/-- **The class induction from its two phases.** -/
theorem tgtClassInd_of_phases {S : Nat → Prop}
    (h1 : TgtClassIndReached μ F envC acval p formerTys out d Dc mc cvc ψ ρ S)
    (h2 : TgtClassIndUnreached μ F envC acval p formerTys out d Dc mc cvc ψ ρ S) :
    TgtClassInd μ F envC acval p formerTys out d Dc mc cvc ψ ρ :=
  fun xs P hP => h2 xs P hP (h1 xs P hP)

end Phases

/-! ## `NestedClassIndOwed`, in two phases -/

/-- **OWED, phase 1** — the reached classes' induction (the node kit over
the positivity derivation's nodes; POSDERIV-4's reached-major tie). -/
@[expose] def NestedClassReachedOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
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
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        TgtClassIndReached μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type)) out
          dR Dc mc cvc ψ ρ
          (TgtReach μ F (mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out)

/-- **OWED, phase 2** — the unreached classes' induction, the reached
ones done (FINDING F14: not one clause's induction in general). -/
@[expose] def NestedClassUnreachedOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
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
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        TgtClassIndUnreached μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type)) out
          dR Dc mc cvc ψ ρ
          (TgtReach μ F (mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out)

/-- **`NestedClassIndOwed` from its two phases.** -/
theorem nestedClassIndOwed_of_phases {μ : CheckMode} {F : Nat} {block : List ConstantInfo}
    (h1 : NestedClassReachedOwed V μ F block) (h2 : NestedClassUnreachedOwed V μ F block) :
    NestedClassIndOwed V μ F block :=
  fun envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx Dc mc cvc hcls ψ ρ =>
    tgtClassInd_of_phases _ _ _ _ _ _ _ _ _ _ _ _ _
      (h1 envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx Dc mc cvc hcls ψ ρ)
      (h2 envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx Dc mc cvc hcls ψ ρ)

/-! ## Phase 1 from the node kit -/

section Kit

variable {μ : CheckMode} {F : Nat} {envC : Env}
  {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape} {formerTys : List Expr}
  {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
  {ψ : Name → Nat} {ρ : Nat → V}

/-- **The node kit at a prefix spine** (F13's ruling: the kit's classes
are the positivity derivation's NODES): a Route B kit `K` whose classes
are nodes, a relation `Rel c b` — node `b` is a visit of recursor class
`c`, at the node clause's component `mOf c b` — every class of `S` has a
node, and at every related pair the recursor class's index set, carrier,
injection, constructor count, decoding fit and call targets are the
node's (`hpredR`: which node a call lands at depends on the caller's
node — the caller, an enclosing node, or a kid). -/
structure TgtNodeKit (μ : CheckMode) (F : Nat) (envC : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape) (formerTys : List Expr)
    (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
    (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
    (ψ : Name → Nat) (ρ : Nat → V) (S : Nat → Prop) (xs : List V) where
  K : NestKitB V (Nat → V)
  Rel : Nat → Nat → Prop
  mOf : Nat → Nat → Nat
  hpredT : ∀ u, u ∈ˢ K.U → ∀ dd, K.Dec u dd → K.pred dd ⊆ˢ K.U
  hex : ∀ c, c < (tgtRs out).length → S c → ∃ b, Rel c b
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

/-- **Phase 1 from a node kit at every prefix spine.** -/
theorem tgtClassIndReached_of_kit {S : Nat → Prop}
    (hK : ∀ xs : List V, Nonempty
      (TgtNodeKit μ F envC acval p formerTys out d Dc mc cvc ψ ρ S xs)) :
    TgtClassIndReached μ F envC acval p formerTys out d Dc mc cvc ψ ρ S := by
  intro xs P hP
  obtain ⟨N⟩ := hK xs
  exact N.K.ind_recNodesOn N.hpredT (tgtRs out).length S N.Rel N.mOf
    (blockRecNCt (tgtRs out)) (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
    (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) (tgtClsInj d Dc mc cvc p out ψ)
    (tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs)
    (graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
      (tgtClsCr d Dc mc cvc acval envC p out ψ ρ) (tgtRs out).length
      (tgtCall μ F (mkFEnv envC) p formerTys out
        acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs)
    N.hex N.hb N.hm N.hIs N.hCr N.hinj N.hnCt N.hfit
    (fun c b hc hR t j fs v hv => N.hpredR c b hc hR t j fs v hv) P hP

end Kit

end ConLeche.Model
