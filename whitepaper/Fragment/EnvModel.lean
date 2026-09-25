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
  model, on values, and its right-hand side is well-denoted with a
  well-formed application chain (con-leche's `RecRuleLaw`,
  `ConLeche/Model/Annot/Laws.lean`).

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

/-- `f v₁ … vₙ` on sets. -/
def appList (f : V) (vs : List V) : V := vs.foldl app f

@[simp] theorem appList_nil (f : V) : appList f [] = f := rfl
@[simp] theorem appList_cons (f v : V) (vs : List V) : appList f (v :: vs) = appList (app f v) vs := rfl

theorem appList_append (f : V) (vs ws : List V) :
    appList f (vs ++ ws) = appList (appList f vs) ws := by
  simp [appList, List.foldl_append]

/-- **Semantic fit of values to a telescope**: each value is a member
of the domain it meets, the body read under the values so far
(`TeleFit` with the arguments' denotations in place of the arguments
— the environment grows instead of the type being substituted into). -/
def TeleFitV (M : Name → List Nat → V) (φ : Name → Nat) : (Nat → V) → Expr → List V → Prop
  | _, _, [] => True
  | ρ, .pi A _ B, v :: vs => v ∈ˢ interp M φ ρ A ∧ TeleFitV M φ (cons v ρ) B vs
  | _, _, _ :: _ => False

theorem TeleFitV_nil (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) (e : Expr) :
    TeleFitV M φ ρ e [] := by
  cases e <;> exact trivial

theorem TeleFitV_pi_cons (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) (A : Expr) (pw : PropWhen) (B : Expr) (v : V)
    (vs : List V) :
    TeleFitV M φ ρ (.pi A pw B) (v :: vs) ↔ v ∈ˢ interp M φ ρ A ∧ TeleFitV M φ (cons v ρ) B vs :=
  Iff.rfl

/-- The body a telescope leaves after a list of values, together with
the environment the values build (the value form of
`Expr.piResidual`, which substitutes instead). -/
def piBodyV : (Nat → V) → Expr → List V → Option (Expr × (Nat → V))
  | ρ, T, [] => some (T, ρ)
  | ρ, .pi _ _ B, v :: vs => piBodyV (cons v ρ) B vs
  | _, _, _ :: _ => none

omit [SetLib V] in
theorem piBodyV_nil (ρ : Nat → V) (T : Expr) : piBodyV ρ T [] = some (T, ρ) := by
  cases T <;> rfl

/-- **A well-formed application chain on values**: at each step the
function is a member of some product whose domain holds the argument
(and, at a proposition, whose fibres are truth values) — the
invariant's application clause (`WellDenoted`, `app`) along a spine,
on values. -/
def SpineOk : V → List V → Prop
  | _, [] => True
  | f, v :: vs =>
    (∃ (p : Bool) (A : V) (B : V → V),
      f ∈ˢ piR p A B ∧ v ∈ˢ A ∧ (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)) ∧
    SpineOk (app f v) vs

/-- **The ι law of one recursor rule** (con-leche's `RecRuleLaw`,
`ConLeche/Model/Annot/Laws.lean`), stated on **values**.  For the
recursor `c` (stored as `ci`, with `numParams` parameters,
`numBefore = numParams + numMotives + numMinors` arguments before the
indices, the major at `majorIdx`) and its rule `rl` for the
constructor stored as `cij`: whenever values `xs` up to the major,
together with the constructor's set applied to values `ys` as the
major, fit the recursor's telescope, `ys` fit the constructor's
telescope, and the three comparisons of `Red.iota` hold in their
semantic form — the constructor's levels evaluate as the recursor's
last `usj.length` ones, its parameters ARE the recursor's, and the
index expressions of its residual type (`piBodyV`: the family at the
constructor's parameters and index expressions, read under the fields)
denote the recursor's index arguments — then the recursor's set
applied to the spine is the rule's right-hand side's set applied to
the parameters, motives, minors and the fields; and the right-hand
side is well-denoted, with a well-formed application chain along
those values (which is what makes the reduct well-denoted,
`WellDenoted_mkAppN_of_spineOk`).

Values rather than terms so that the law mentions the model only at
the STORED terms (the two types and the right-hand side): extending
the environment by a fresh constant then leaves every old law intact
(`Install.lean`), where a law over arbitrary argument terms would have
to be re-proved for the terms that mention the new name.  The ι rule's
soundness converts its term-level certificates to this form
(`Tele.lean`).

**Part 2's obligation, named.**  Where the family is a *type*, the
law follows from the **fixpoint's inversion** alone: the recursor's
fit puts the major — a tagged tuple of the fields — in the family at
the RECURSOR's parameters and indices, and a member of the family
built by `rl.ctor` has its fields in the constructor's field
telescope at THOSE parameters, which is what the right-hand side's β
steps need and what the recursion equation of the model's recursor is
stated over.  Where the family is a *proposition* the major denotes
the point and the fits say only that the fibre is inhabited; the
three comparisons then relate the fields `ys` to the recursor's own
parameters and indices, and the subsingleton criterion makes the
recursor's value at the point the value at those fields. -/
def RecRuleLaw (M : Name → List Nat → V) (c : Name) (ci : ConstInfo)
    (numParams numBefore majorIdx : Nat) (rl : RecRule) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us usj : List Level) (xs ys : List V),
    us.length = ci.lparams.length → usj.length = cij.lparams.length →
    xs.length = majorIdx → ys.length = numParams + rl.nfields →
    TeleFitV M φ ρ (ci.type.instL ci.lparams us)
      (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) →
    TeleFitV M φ ρ (cij.type.instL cij.lparams usj) ys →
    usj.map (Level.eval φ) = (us.drop (us.length - usj.length)).map (Level.eval φ) →
    ys.take numParams = xs.take numParams →
    (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
      B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = numParams →
      ∀ p ∈ (ridx.map (interp M φ ρ')).zip (xs.drop numBefore), p.1 = p.2) →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys])
      = appList (interp M φ ρ (rl.rhs.instL ci.lparams us))
          (xs.take numBefore ++ ys.drop numParams) ∧
    WellDenoted M φ ρ (rl.rhs.instL ci.lparams us) ∧
    SpineOk (interp M φ ρ (rl.rhs.instL ci.lparams us)) (xs.take numBefore ++ ys.drop numParams)

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
