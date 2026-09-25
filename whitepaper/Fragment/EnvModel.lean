module

public import Fragment.WellDenoted

@[expose] public section

/-!
# The environment invariant

A model of an environment is an assignment `M` of a set to every
constant at every list of concrete levels, together with the laws the
env-free soundness proof (`Sound.lean`) reads about the stored
constants:

* **`type_ok`** — every stored constant's declared type, at every
  level instantiation, is well-denoted, and the constant's set is a
  member of it (con-leche's `mem_type`/`type_wellDenotedV`,
  `ConLeche/Model/Annot/EnvModelM.lean`);
* **`unfold`** — a definition's value denotes the constant's set, and
  is well-denoted (con-leche's `AcvalDefnInst`);
* **`rec_rules`** — every recursor rule's ι equation holds in the
  model, and its right-hand side applied is well-denoted (con-leche's
  `RecRuleLaw`, `ConLeche/Model/Annot/Laws.lean`).

The proof against these laws is the env-free part of the paper.  That
the empty environment has a model, and that adding a definition or
installing an inductive block preserves having one, is the
environment section's business (part 2), which must construct `M` for
the new constants and discharge the three laws.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V]

/-- **Semantic fit of a spine to a telescope**: each argument is a
member of the domain it meets, the domains instantiated along the
spine (the semantic content of a telescope certificate; the syntactic
walk is `Expr.piDomains`). -/
def TeleFit (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) :
    Expr → List Expr → Prop
  | _, [] => True
  | .pi A _ B, a :: as => interp M φ ρ a ∈ˢ interp M φ ρ A ∧ TeleFit M φ ρ (B.inst a) as
  | _, _ :: _ => False

/-- **The ι law of one recursor rule** (con-leche's `RecRuleLaw`).  For
the recursor `c` (stored as `ci`, with `numParams` parameters and
`numBefore = numParams + numMotives + numMinors` arguments before the
indices, the major at `majorIdx`) and its rule `rl` for the
constructor stored as `cij`: whenever a spine `xs` of arguments up to
the major, all well-denoted, together with a constructor application
`rl.ctor usj ys` as the major, fits the recursor's telescope, and `ys`
(all well-denoted) fits the constructor's telescope, then the applied
recursor denotes what the rule's right-hand side, applied to the
parameters, motives, minors and the fields, denotes — and that
reduct is well-denoted.

**The three comparisons** `Red.iota` makes besides the certificates
are premises too, in their semantic form: the constructor's levels
evaluate as the recursor's last `usj.length` ones, its parameters
denote the recursor's, and the index expressions of its residual type
(`Expr.piResidual`, the family at the constructor's parameters and
index expressions with the fields substituted in) denote the
recursor's index arguments.

**Part 2's obligation, named.**  Where the family is a *type*, the
law follows from the **fixpoint's inversion** alone: the recursor's
certificate puts the major `⟦rl.ctor usj ys⟧` — a tagged tuple of the
fields — in the family at the RECURSOR's parameters and indices, and a
member of the family built by `rl.ctor` has its fields in the
constructor's field telescope at THOSE parameters, which is what the
right-hand side's β steps need and what the recursion equation of the
model's recursor is stated over.  Where the family is a *proposition*
the major denotes the point and the certificates say only that the
fibre is inhabited; the three comparisons are then what relates the
fields the right-hand side receives (`ys`) to the recursor's own
parameters and indices, and the subsingleton criterion is what makes
the recursor's value at the point the value at those fields
(`Install.lean`). -/
def RecRuleLaw (M : Name → List Nat → V) (c : Name) (ci : ConstInfo)
    (numParams numBefore majorIdx : Nat) (rl : RecRule) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us usj : List Level) (xs ys : List Expr),
    us.length = ci.lparams.length → usj.length = cij.lparams.length →
    xs.length = majorIdx → ys.length = numParams + rl.nfields →
    (∀ x ∈ xs, WellDenoted M φ ρ x) → (∀ y ∈ ys, WellDenoted M φ ρ y) →
    TeleFit M φ ρ (ci.type.instL ci.lparams us)
      (xs ++ [Expr.mkAppN (.const rl.ctor usj) ys]) →
    TeleFit M φ ρ (cij.type.instL cij.lparams usj) ys →
    ∀ (residual : Expr) (I : Name) (lsI : List Level) (rps ridx : List Expr),
    usj.map (Level.eval φ) = (us.drop (us.length - usj.length)).map (Level.eval φ) →
    (∀ p ∈ (ys.take numParams).zip (xs.take numParams),
      interp M φ ρ p.1 = interp M φ ρ p.2) →
    Expr.piResidual (cij.type.instL cij.lparams usj) ys = some residual →
    residual = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = numParams →
    (∀ p ∈ ridx.zip (xs.drop numBefore), interp M φ ρ p.1 = interp M φ ρ p.2) →
    interp M φ ρ (Expr.mkAppN (.const c us) (xs ++ [Expr.mkAppN (.const rl.ctor usj) ys]))
      = interp M φ ρ (Expr.mkAppN (rl.rhs.instL ci.lparams us)
          (xs.take numBefore ++ ys.drop numParams)) ∧
    WellDenoted M φ ρ (Expr.mkAppN (rl.rhs.instL ci.lparams us)
      (xs.take numBefore ++ ys.drop numParams))

/-- **A model of an environment**: the assignment and the three laws. -/
structure EnvModel (V : Type u) [SetLib V] (env : Env) where
  /-- The set of every constant at every list of concrete levels. -/
  M : Name → List Nat → V
  /-- Every stored constant's type, instantiated, is well-denoted, and
  the constant is a member of it — at every valuation and every
  environment (the types are closed, so `ρ` is irrelevant, and stating
  it for all `ρ` saves a closedness lemma). -/
  type_ok : ∀ (c : Name) (ci : ConstInfo), env.find? c = some ci →
    ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WellDenoted M φ ρ (ci.type.instL ci.lparams ls) ∧
      M c (ls.map (Level.eval φ)) ∈ˢ interp M φ ρ (ci.type.instL ci.lparams ls)
  /-- A definition's value, instantiated, is well-denoted and denotes
  the constant. -/
  unfold : ∀ (c : Name) (ci : ConstInfo) (v : Expr), env.find? c = some ci →
    ci.value? = some v →
    ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WellDenoted M φ ρ (v.instL ci.lparams ls) ∧
      interp M φ ρ (v.instL ci.lparams ls) = M c (ls.map (Level.eval φ))
  /-- Every rule of every stored recursor satisfies its ι law. -/
  rec_rules : ∀ (c : Name) (ci : ConstInfo) (numParams numMotives numMinors numIndices : Nat)
    (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, ∀ cij : ConstInfo, env.find? rl.ctor = some cij →
      RecRuleLaw M c ci numParams (numParams + numMotives + numMinors)
        (numParams + numMotives + numMinors + numIndices) rl cij

/-- The empty environment has a model: any assignment, vacuous laws. -/
def EnvModel.empty (M : Name → List Nat → V) : EnvModel V Env.empty where
  M := M
  type_ok := fun _ _ h => by simp at h
  unfold := fun _ _ _ h => by simp at h
  rec_rules := fun _ _ _ _ _ _ _ h => by simp at h

end Fragment
