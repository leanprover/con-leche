module

public import ConLeche.Model.Rules.Motive

public section

/-!
# The environment-level inputs of the soundness (task #305)

What the soundness of a derivation reads about the ENVIRONMENT — the
stored data's readings, gradings and laws — and nothing about the
implementation.  One structure, `RulesInputs`, sorted by the tier that
discharges each field.  Six fields are the laws `EnvModelM` already
carries (`TowerOk`, `RecRules`, `CapsOk` are imported from
`Model/Annot/EnvModelM.lean`; `ConstTy`, `LeafValid`, `NatLeafHeads`,
`DefnReads` restate `Model/Steps/*`'s `ConstType`, `AcvalValid`,
`NatHeads`, `AcvalDefnInst` verbatim so that this module does not
import a file stated over runs).  Two fields are NEW SHAPES:

* `NatSuccRow` / `NatOpRow` — the literal accelerations' semantic
  content, stated at the shapes `reduceNat` fires on with the
  arguments already at literal readings (`rawNatLit?`), and with the
  subject's reading a premise.  Today this content is routed as
  `ReduceNatStep`/`ReduceNatStepPQ` (`Model/Steps/Whnf.lean:220`,
  `DefEq.lean:263`), which are stated over RUNS of `reduceNat` and
  take `WhnfClaim` at the same fuel; `Model/NatStep.lean` proves them
  from `EnvModelM.nat_ops`/`div_mod`.  The recomposition
  (`Recompose.lean`) has only `TierInputsAt`, whose two nat fields are
  those run rows, and derives these from them by instantiating at the
  literal run — see the record.

The row for the `Red.natLit` step (`lit n ↦ natLitToConstructor n`)
needs no input: the reading is invisible to the step
(`denoteMeta_litToCtorIfNat`, `Model/Steps/Major.lean:66`); the string
expansion likewise (`denotePStrLit_of_guard`, `Stuck.lean:540`).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V]

/-- Every stored leaf is bit-valid (`AcvalValid`, `Steps/Infer.lean:119`). -/
@[expose] def LeafValid {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValid V ρ (m.acval n ψ)

/-- A stored constant's instantiated type reads, is graded, and holds
the constant's leaf (`ConstType`, `Steps/Infer.lean:125`). -/
@[expose] def ConstTy {env : Env} (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (n : Name) (ci : ConLeche.ConstantInfo) (us : List Level),
    env.find? n = some ci → ci.isTowerEntry = false →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ ta,
      denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp V ρ ta

/-- The numeral heads (`NatHeads`, `Steps/Infer.lean:525`). -/
@[expose] def NatLeafHeads {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ConLeche.natLitSupported env = true →
  ∀ ρ : Nat → V,
    interp V ρ (m.acval natZeroName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) ∧
    interp V ρ (m.acval natSuccName (Level.substFn φ [] []))
      ∈ˢ piR 1 (interp V ρ (m.acval natName (Level.substFn φ [] [])))
        (fun _ => interp V ρ
          (m.acval natName (Level.substFn φ [] [])))

/-- A stored definition's value reads to the constant's own leaf
(`AcvalDefnInst`, `Steps/Whnf.lean:266`) — the δ step's whole input. -/
@[expose] def DefnReads {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
    (∃ hint : ReducibilityHint,
      ConstantInfo.defnInfo cv value hint ∈ env.consts) →
    denoteMeta m.acval env ψ 0 value = some (m.acval cv.name ψ)

/-- **The successor packing's semantic row**: `Nat.succ w` at a literal
reading of `w` interprets as the packed literal, which reads and is
graded. -/
@[expose] def NatSuccRow {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {d : Nat} {w : Expr} {n : Nat} {Δa : List AnnotTerm} {ea : AnnotTerm},
    ConLeche.natLitSupported env = true →
    ConLeche.rawNatLit? w = some n →
    denoteMeta m.acval env φ d (.app (.const natSuccName []) w) = some ea →
    Graded V Δa ea →
    ∃ ra, denoteMeta m.acval env φ d (.lit (.natVal (n + 1))) = some ra ∧
      Graded V Δa ra ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ra

/-- **The binary acceleration's semantic row**: a stored operation on
two literal readings interprets as `natOpResult`, which reads and is
graded. -/
@[expose] def NatOpRow {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {d : Nat} {c : Name} {wa wb r : Expr} {n₁ n₂ : Nat} {Δa : List AnnotTerm}
    {ea : AnnotTerm},
    c ∈ natBinOpNames → ConLeche.natOpStored env c = true →
    ConLeche.rawNatLit? wa = some n₁ → ConLeche.rawNatLit? wb = some n₂ →
    ConLeche.natOpResult c n₁ n₂ = some r →
    denoteMeta m.acval env φ d (.app (.app (.const c []) wa) wb) = some ea →
    Graded V Δa ea →
    ∃ ra, denoteMeta m.acval env φ d r = some ra ∧
      Graded V Δa ra ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ra

/-- **The environment-level inputs of the rules soundness**, at one
`(env, m, φ)`, sorted by discharging tier. -/
structure RulesInputs (V : Type w) [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop where
  /-- install tier: a stored constant's type row -/
  const_ty : ConstTy m φ
  /-- install tier: leaf bit-validity -/
  leaf_valid : LeafValid m
  /-- install tier: the numeral heads -/
  nat_heads : NatLeafHeads m φ
  /-- install tier: a stored definition's value reads to its leaf -/
  defn : DefnReads m
  /-- install tier: the projection tables' laws -/
  tower_ok : TowerOk m φ
  /-- iota tier: the stored recursors' fired contracts -/
  rec_rules : RecRules m φ
  /-- caps tier: the stored families' capability laws -/
  caps_ok : CapsOk m
  /-- literal tier: successor packing -/
  nat_succ : NatSuccRow m φ
  /-- literal tier: the binary operations -/
  nat_op : NatOpRow m φ

end ConLeche.Model.Rules
