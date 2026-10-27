module

public import ConLeche.Model.Rules.Motive

public section

/-!
# The environment-level inputs of the soundness (task #305)

What the soundness of a derivation reads about the ENVIRONMENT — the
stored data's readings, gradings and laws — and nothing about the
implementation.  One structure, `RulesInputs`, sorted by the tier that
discharges each field.

Eight fields are the laws `EnvModelM` already carries: `ConstType`,
`NatHeads`, `AcvalDefnInst`, `TowerOk`, `RecRules`,
`CapsOk` and `IndFibLaw`, all of them `Model/Env/Laws.lean`'s (re-exported by
`Model/Env/EnvModelM.lean`).  `RulesInputs.ofEnvModelM` below reads
each of them off the fold's invariant.

Three fields are NEW SHAPES:

* `NatSuccRow` / `NatOpRow` — the literal accelerations' semantic
  content, stated at the shapes `reduceNat` fires on with the
  arguments already at literal readings (`rawNatLit?`), and with the
  subject's reading a premise;
* `NatOpHead` — a fired operation's head is a function over the `Nat`
  leaf (its pinned type), whence its arguments' domain.

The three are proved in `Model/NatStep.lean` from
`EnvModelM.nat_ops`/`div_mod`, which is where the content lives; they stay
ARGUMENTS of `ofEnvModelM` because that file sits above this one
(`Model/Capstone.lean`'s `RulesInputs.ofSem` supplies them).

The row for the `Red.natLit` step (`lit n ↦ natLitToConstructor n`)
needs no input: the reading is invisible to the step
(`denote_natLitToConstructor`); the string expansion likewise
(`denote_strLitToConstructor`).
-/
namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The successor packing's semantic row**: `Nat.succ w` at a literal
reading of `w` interprets as the packed literal, which reads and is
graded. -/
@[expose] def NatSuccRow {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {d : Nat} {w : Expr} {n : Nat} {ea : Term},
    ConLeche.natLitSupported env = true →
    ConLeche.rawNatLit? w = some n →
    denote m.acval env φ d (.app (.const natSuccName []) w) = some ea →
    ∃ ra, denote m.acval env φ d (.lit (.natVal (n + 1))) = some ra ∧
      ∀ ρ : Nat → V, WellDenoted V ρ ea →
        WellDenoted V ρ ra ∧ interp V ρ ea = interp V ρ ra

/-- **The binary acceleration's semantic row**: a stored operation on
two literal readings interprets as `natOpResult`, which reads and is
graded. -/
@[expose] def NatOpRow {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {d : Nat} {c : Name} {wa wb r : Expr} {n₁ n₂ : Nat} {ea : Term},
    c ∈ natBinOpNames → ConLeche.natOpStored env c = true →
    ConLeche.rawNatLit? wa = some n₁ → ConLeche.rawNatLit? wb = some n₂ →
    ConLeche.natOpResult c n₁ n₂ = some r →
    denote m.acval env φ d (.app (.app (.const c []) wa) wb) = some ea →
    ∃ ra, denote m.acval env φ d r = some ra ∧
      ∀ ρ : Nat → V, WellDenoted V ρ ea →
        WellDenoted V ρ ra ∧ interp V ρ ea = interp V ρ ra

/-- **The binary acceleration's head**: a stored operation the rule fires
on is read over the `Nat` leaf, a function on `Nat` of a function on `Nat`
(its stored type is pinned at install, `natOpTyPinned`), and the literal
basis is stored.  `Red.natOp_sound` reads the domains off it: the redex is
not the point, so neither is the head, whose graph fixes its domain
(`piR_dom_unique`, task #342 L12). -/
@[expose] def NatOpHead {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {c : Name}, c ∈ natBinOpNames → ConLeche.natOpStored env c = true →
    ConLeche.natLitSupported env = true ∧
    ∀ {d : Nat} {ca : Term},
      denote m.acval env φ d (.const c []) = some ca →
      ∀ ρ : Nat → V, ∃ (b₁ b₂ : Nat) (X : V),
        interp V ρ ca ∈ˢ piR b₁ (interp V ρ (m.acval natName (Level.substFn φ [] [])))
          (fun _ => piR b₂ (interp V ρ (m.acval natName (Level.substFn φ [] [])))
            (fun _ => X))

/-- **The semantic content of `Infer.bvUnsat`** (task #368): where the `bv_decide` closure is the pinned one,
at a closed formula `E` whose reading lies in `⟦BVLogicalExpr⟧` and
evaluates to `⟦false⟧` at every quoted assignment, the theorem
`unsat_of_verifyBVExpr_eq_true` reads as the point and `Unsat E` holds
it.  Proved from the fold's invariant in `Model/BVUnsat.lean` (the
least fixpoint of the stored `RArray` block, the `Eq` law, the stored
types and definitions); a field here because the rules tier's master
induction reads the environment through `RulesInputs` alone. -/
@[expose] def BVUnsatSemLaw {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ConLeche.BVUnsat.pinsOk env.find? env.findProj? = true →
  ∀ {d : Nat} {E : Expr} {eT : Term} (ρ : Nat → V),
    E.looseBVarsBounded 0 = true → E.hasFvar = false →
    denote m.acval env φ d E = some eT → WellDenoted V ρ eT →
    (∀ BA, denote m.acval env φ d (.const bvLogicalExprName []) = some BA →
      interp V ρ eT ∈ˢ interp V ρ BA) →
    (∀ (x : Std.Tactic.BVDecide.BVExpr.Assignment) (rx fa : Term),
      denote m.acval env φ d (.app (.app (.const bvEvalName []) (quoteAssign x)) E)
        = some rx →
      WellDenoted V ρ rx → interp V ρ rx ≠ pt →
      denote m.acval env φ d (.const ConLeche.boolFalseName []) = some fa →
      interp V ρ rx = interp V ρ fa) →
    (∀ (k : Nat) (pk lk : Term),
      denote m.acval env φ d (pow2E (.lit (.natVal k))) = some pk →
      WellDenoted V ρ pk → interp V ρ pk ≠ pt →
      denote m.acval env φ d (.lit (.natVal (2 ^ k))) = some lk →
      interp V ρ pk = interp V ρ lk) →
    ∃ uT unsT,
      denote m.acval env φ d (.const ConLeche.unsatThmName []) = some uT ∧
      denote m.acval env φ d (.const ConLeche.bvUnsatName []) = some unsT ∧
      WellDenoted V ρ uT ∧ interp V ρ uT = pt ∧
      WellDenotedTy V ρ (.app unsT eT) ∧ (pt : V) ∈ˢ interp V ρ (.app unsT eT)

/-- **The environment-level inputs of the rules soundness**, at one
`(env, m, φ)`, sorted by discharging tier. -/
structure RulesInputs (V : Type w) [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop where
  /-- install tier: a stored constant's type row -/
  const_ty : ConstType m φ
  /-- install tier: the numeral heads -/
  nat_heads : NatHeads m φ
  /-- install tier: a stored definition's value reads to its leaf -/
  defn : AcvalDefnInst m
  /-- install tier: the projection tables' laws -/
  tower_ok : TowerOk m φ
  /-- iota tier: the stored recursors' fired contracts -/
  rec_rules : RecRules m φ
  /-- caps tier: the stored families' capability laws -/
  caps_ok : CapsOk m
  /-- iota tier: the stored families' fibres — truth values where the
  stored sort is `0`, strict elsewhere (task #342 L7; the case-2 ι
  case split's input) -/
  ind_fib : IndFibLaw m φ
  /-- literal tier: successor packing -/
  nat_succ : NatSuccRow m φ
  /-- literal tier: the binary operations -/
  nat_op : NatOpRow m φ
  /-- literal tier: the binary operations' heads, over `Nat` -/
  nat_op_head : NatOpHead m φ
  /-- bv_decide tier: the semantic content of `Infer.bvUnsat` -/
  bv_unsat : BVUnsatSemLaw m φ

/-- **The env-tier inputs, from the fold's invariant**: every field but
the three literal rows is an `EnvModelM` projection; the rows stay
arguments because `natSuccRow_of`/`natOpRow_of`/`natOpHead_of` (`Model/NatStep.lean`)
sit above this file — `Model/Capstone.lean`'s `RulesInputs.ofSem`
supplies them. -/
theorem RulesInputs.ofEnvModelM {env : Env} {φ : Name → Nat}
    (mp : EnvModelM V μ env)
    (hsucc : NatSuccRow mp.base2 φ) (hop : NatOpRow mp.base2 φ)
    (hhead : NatOpHead mp.base2 φ) (hq : BVUnsatSemLaw mp.base2 φ) :
    RulesInputs V mp.base2 φ where
  const_ty := mp.constType
  nat_heads := mp.nat_heads φ
  defn := mp.defn_reads
  tower_ok := mp.tower_ok φ
  rec_rules := mp.rec_rules φ
  caps_ok := mp.caps_ok
  ind_fib := mp.indFibLaw φ
  nat_succ := hsucc
  nat_op := hop
  nat_op_head := hhead
  bv_unsat := hq

end ConLeche.Model.Rules
