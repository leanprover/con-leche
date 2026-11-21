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
  member of it (con-leche's `mem_type`/`type_wellDenotedTy`,
  `ConLeche/Model/Env/EnvModelM.lean`);
* **`unfold`** — a definition's value denotes the constant's set, and
  is well-denoted (con-leche's `AcvalDefnInst`);
* **`rec_rules`** — every recursor rule's ι equation holds in the
  model, on values, and its right-hand side is well-denoted with a
  well-formed application chain (con-leche's `RecRuleLaw`,
  `ConLeche/Model/Env/Laws.lean`);
* **`ind_fib`** — every stored inductive family has truth values as
  fibres where its stored sort evaluates to zero, and strict fibres (not
  the point, and without it) where it does not (`IndFibLaw`), the fact
  the ι of a family that is not always `Prop` needs to go without
  certificates (`Red.iotaStrict`, `Red.iotaSlot`);
* **`rec_rules_k`** — every rule flagged K (`RecRule.k`) satisfies the K
  law (`RecRuleLawK`): at any major value in the recursor's domain the
  recursor is the rule's right-hand side at its parameters, motives and
  minors, the fact `Red.iotaK` needs to fire with no constructor and no
  certificate;
* **`rec_rules_slot`** — where a recursor's major is the point, the
  recursor's application or the rule's constructor is
  (`RecRuleSlotLaw`), the fact `Red.iotaSlot` needs to go without a
  slot certificate and without a premise linking the major's domain to
  the constructor's family.

The proof against these laws is the env-free part of the paper.  That
the empty environment has a model, and that adding a definition or
installing an inductive block preserves having one, is the
environment section's business (part 2), which must construct `M` for
the new constants and discharge the laws.

This is the proof's internal invariant, not the statement: the main
theorem (`model_exists`, `Main.lean`) speaks of the input's constants
and of `ModelOf` (`IsModel.lean`), which reads a recursor's rules off
its own type, unconditionally.  The conditional ι laws here are what
the reduction rules consume; the installation proves both
(`Holds.lean`).
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
  | .pi A B, a :: as => interp M φ ρ a ∈ˢ interp M φ ρ A ∧ TeleFit M φ ρ (B.inst a) as
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
  | ρ, .pi A B, v :: vs => v ∈ˢ interp M φ ρ A ∧ TeleFitV M φ (cons v ρ) B vs
  | _, _, _ :: _ => False

theorem TeleFitV_nil (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) (e : Expr) :
    TeleFitV M φ ρ e [] := by
  cases e <;> exact trivial

theorem TeleFitV_pi_cons (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) (A : Expr) (B : Expr) (v : V)
    (vs : List V) :
    TeleFitV M φ ρ (.pi A B) (v :: vs) ↔ v ∈ˢ interp M φ ρ A ∧ TeleFitV M φ (cons v ρ) B vs :=
  Iff.rfl

/-- The body a telescope leaves after a list of values, together with
the environment the values build (the value form of
`Expr.piResidual`, which substitutes instead). -/
def piBodyV : (Nat → V) → Expr → List V → Option (Expr × (Nat → V))
  | ρ, T, [] => some (T, ρ)
  | ρ, .pi _ B, v :: vs => piBodyV (cons v ρ) B vs
  | _, _, _ :: _ => none

omit [SetLib V] in
theorem piBodyV_nil (ρ : Nat → V) (T : Expr) : piBodyV ρ T [] = some (T, ρ) := by
  cases T <;> rfl

/-- **A well-formed application chain on values**: at each step the
argument is in the function's domain (`AppliesTo`: the function is the
point, or a graph whose domain is a type holding the argument) — the
invariant's application clause (`WellDenoted`, `app`) along a spine,
on values. -/
def SpineOk : V → List V → Prop
  | _, [] => True
  | f, v :: vs => AppliesTo f v ∧ SpineOk (app f v) vs

/-- **The ι law of one recursor rule** (con-leche's `RecRuleLaw`,
`ConLeche/Model/Env/Laws.lean`), stated on **values**.  For the
recursor `c` (stored as `ci`, with `numParams` parameters,
`numBefore = numParams + numMotives + numMinors` arguments before the
indices, the major at `majorIdx`) and its rule `rl` for the
constructor stored as `cij`: whenever values `xs` up to the major,
together with the constructor's set applied to values `ys` as the
major, fit the recursor's telescope, `ys` fit the constructor's
telescope, and the three comparisons of `Red.iota` hold in their
semantic form — the constructor's levels evaluate as the recursor's
last `usj.length` ones, its parameters equal the recursor's and the
index expressions of its residual type (`piBodyV`: the family at the
constructor's parameters and index expressions, read under the fields)
denote the recursor's index arguments, **each where neither side is
the point** (as `DefEq` claims them) — and the recursor's application
is **not the point** (as `Red` claims ι), then the recursor's set
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

**The installation's obligation, named.**  The conditional comparisons
become the equalities the recursion equation needs because the
recursor's and the constructor's telescopes are generated from one
parameter and index context: under equal earlier values the two sides
of each comparison lie in one type, whose members are all the point or
none (`IsTy.eq_of_ne_pt`).  Where the family is a *type*, the law then
follows from the **fixpoint's inversion**: the recursor's fit puts the
major — a tagged tuple of the fields — in the family at the RECURSOR's
parameters and indices, and a member of the family built by `rl.ctor`
has its fields in the constructor's field telescope at THOSE
parameters.  Where the family is a *proposition* the major denotes the
point and the fits say only that the fibre is inhabited; the
comparisons then relate the fields `ys` to the recursor's own
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
    (∀ p ∈ (ys.take numParams).zip (xs.take numParams), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
    (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
      B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = numParams →
      ∀ p ∈ (ridx.map (interp M φ ρ')).zip (xs.drop numBefore),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) ≠ pt →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys])
      = appList (interp M φ ρ (rl.rhs.instL ci.lparams us))
          (xs.take numBefore ++ ys.drop numParams) ∧
    WellDenoted M φ ρ (rl.rhs.instL ci.lparams us) ∧
    SpineOk (interp M φ ρ (rl.rhs.instL ci.lparams us)) (xs.take numBefore ++ ys.drop numParams)

/-- **The ι law of a K rule** (the `EnvModel` field
`rec_rules_k`, proved by the installer as
`IndSpec.rec_rule_lawK`).
For a recursor `c` whose one rule `rl` fires on a constructor with no
fields of a family of sort `Prop` (Lean's K: `Eq`, `HEq`, `True`): at
**any** values `vs` fitting the recursor's whole telescope — the
major's value included, whatever term produced it — an application
that is not the point equals the rule's right-hand side applied to the
parameters, motives and minors alone.  In the inductive model this is
the plain law at the recursor's own parameters plus **inversion of the
least fixed point**: the major's value lies in the fibre at the
recursor's indices, a fibre is inhabited only at the indices of the
unique constructor applied to those parameters (the family "inhabited
exactly there" is closed under the constructor, so it contains the
least one), and the constructor's value there is the point, as the
major's is.  The constructor application the checker fabricates (or
finds) is not mentioned: the reduct does not contain it. -/
def RecRuleLawK (M : Name → List Nat → V) (c : Name) (ci : ConstInfo)
    (numBefore majorIdx : Nat) (rl : RecRule) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us : List Level) (vs : List V),
    us.length = ci.lparams.length → vs.length = majorIdx + 1 →
    TeleFitV M φ ρ (ci.type.instL ci.lparams us) vs →
    appList (M c (us.map (Level.eval φ))) vs ≠ pt →
    appList (M c (us.map (Level.eval φ))) vs
        = appList (interp M φ ρ (rl.rhs.instL ci.lparams us)) (vs.take numBefore) ∧
      WellDenoted M φ ρ (rl.rhs.instL ci.lparams us) ∧
      SpineOk (interp M φ ρ (rl.rhs.instL ci.lparams us)) (vs.take numBefore)

/-- **The ι law of a nested rule** (`Red.iotaNested`): for the
recursor `c` with `numParams` parameters and a rule `rl` firing on a
constructor `cij` of the block's container, with `nPc` parameters of
its own — the comparisons against the stored instantiation are
*checked* by the ι step, but the law does not consume them: the
constructor's fields are pinned by the major's membership in the
class (the recursor's telescope fit), as tags and tuples are
injective, and the elimination level of a nested block whose sort may
be `Prop` is `Prop` (`blockLargeElimAllowed`, `BlockRec.lean:82`),
where the recursor's application is the point and nothing is asked.
The index comparisons are conditional on the point, as in
`RecRuleLaw`.  Otherwise as `RecRuleLaw`. -/
def RecRuleLawN (M : Name → List Nat → V) (c : Name) (ci : ConstInfo)
    (nPc numBefore majorIdx : Nat) (rl : RecRule) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us usj : List Level) (xs ys : List V),
    us.length = ci.lparams.length → usj.length = cij.lparams.length →
    xs.length = majorIdx → ys.length = nPc + rl.nfields →
    TeleFitV M φ ρ (ci.type.instL ci.lparams us)
      (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) →
    TeleFitV M φ ρ (cij.type.instL cij.lparams usj) ys →
    (∀ (B : Expr) (ρ' : Nat → V) (I : Name) (lsI : List Level) (rps ridx : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) ys = some (B, ρ') →
      B = Expr.mkAppN (.const I lsI) (rps ++ ridx) → rps.length = nPc →
      ∀ p ∈ (ridx.map (interp M φ ρ')).zip (xs.drop numBefore),
        p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys]) ≠ pt →
    appList (M c (us.map (Level.eval φ)))
        (xs ++ [appList (M rl.ctor (usj.map (Level.eval φ))) ys])
      = appList (interp M φ ρ (rl.rhs.instL ci.lparams us))
          (xs.take numBefore ++ ys.drop nPc) ∧
    WellDenoted M φ ρ (rl.rhs.instL ci.lparams us) ∧
    SpineOk (interp M φ ρ (rl.rhs.instL ci.lparams us)) (xs.take numBefore ++ ys.drop nPc)

/-- **The point in the major's slot** (the installer fact
behind `Red.iotaSlot`/`Red.iotaNestedSlot`): for a recursor `c` and its
rule `rl` firing on the constructor stored as `cij`, wherever the
recursor's telescope holds the point as the major (after values `xs`
fitting it), either the recursor's application there is the point or
the rule's constructor, applied to anything, is — provided, for a rule
of the block's own constructors (`rl.inst = none`), that the
constructor's levels evaluate as the recursor's last ones (the level
comparison ι runs).  On generated recursors: the major's domain is the
family at the recursor's own levels; where its sort evaluates to zero
the constructor (of the same family, at the same levels) is the point,
and where it does not the domain is strict and holds no point.  On a
nested block the family is `Prop` only where the eliminator is
(`blockLargeElimAllowed`), so there the recursor's application is the
point.  This is what lets the ι rules with no slot certificate go
without a premise linking the major's domain to the constructor's
family. -/
def RecRuleSlotLaw (M : Name → List Nat → V) (c : Name) (ci : ConstInfo) (majorIdx : Nat)
    (rl : RecRule) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us usj : List Level) (xs ys : List V),
    us.length = ci.lparams.length → usj.length = cij.lparams.length →
    xs.length = majorIdx →
    TeleFitV M φ ρ (ci.type.instL ci.lparams us) (xs ++ [pt]) →
    (rl.inst = none →
      usj.map (Level.eval φ) = (us.drop (us.length - usj.length)).map (Level.eval φ)) →
    appList (M c (us.map (Level.eval φ))) (xs ++ [pt]) = pt ∨
      appList (M rl.ctor (usj.map (Level.eval φ))) ys = pt

/-- **The fibres' regime follows the stored sort** (used by
the ι case test): for a stored inductive type former
`I` (stored as `ci`, with `nP` parameters and `nI` indices and its
block's specification `S`), the family applied to any values fitting
its telescope is a **truth value** where the family's stored sort
`S.sort`, instantiated at the use's levels, evaluates to zero, and a
**strict** set — not the point, and without the point as a member —
where it does not (`Fib`).  Every `Sort (n+1)` holds truth values as
well (`typeU`), so the universe does not say the second; the
inductive model does: above a proposition a fibre is a set of tagged
values (`IndSem.Fam_mem_typeU`), and a family read through a former's
graph is admissible (`IndCommon.adm`), so strict
(`IndCommon.strict_adm`).  Stated on values, like `RecRuleLaw`. -/
def IndFibLaw (M : Name → List Nat → V) (I : Name) (ci : ConstInfo) (nP nI : Nat) (S : IndSpec) :
    Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level) (vs : List V),
    ls.length = ci.lparams.length → vs.length = nP + nI →
    TeleFitV M φ ρ (ci.type.instL ci.lparams ls) vs →
    Fib (Level.eval φ (S.sort.subst ci.lparams ls) == 0) (appList (M I (ls.map (Level.eval φ))) vs)

/-- **A model of an environment**: the assignment and the laws. -/
structure EnvModel (V : Type u) [SetLib V] (env : Env) where
  /-- The set of every constant at every list of concrete levels. -/
  M : Name → List Nat → V
  /-- Every stored constant's type, instantiated, is well-denoted and a
  type, and the constant is a member of it — at every valuation and every
  environment (the types are closed, so `ρ` is irrelevant, and stating
  it for all `ρ` saves a closedness lemma). -/
  type_ok : ∀ (c : Name) (ci : ConstInfo), env.find? c = some ci →
    ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WellDenoted M φ ρ (ci.type.instL ci.lparams ls) ∧
      IsTy (interp M φ ρ (ci.type.instL ci.lparams ls)) ∧
      M c (ls.map (Level.eval φ)) ∈ˢ interp M φ ρ (ci.type.instL ci.lparams ls)
  /-- A definition's value, instantiated, is well-denoted and denotes
  the constant. -/
  unfold : ∀ (c : Name) (ci : ConstInfo) (v : Expr), env.find? c = some ci →
    ci.value? = some v →
    ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
      WellDenoted M φ ρ (v.instL ci.lparams ls) ∧
      interp M φ ρ (v.instL ci.lparams ls) = M c (ls.map (Level.eval φ))
  /-- Every plain rule of every stored recursor satisfies its ι law. -/
  rec_rules : ∀ (c : Name) (ci : ConstInfo) (numParams numMotives numMinors numIndices : Nat)
    (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, rl.inst = none → ∀ cij : ConstInfo, env.find? rl.ctor = some cij →
      RecRuleLaw M c ci numParams (numParams + numMotives + numMinors)
        (numParams + numMotives + numMinors + numIndices) rl cij
  /-- Every nested rule of every stored recursor satisfies its ι law,
  at its constructor's own parameter count. -/
  rec_rules_nested : ∀ (c : Name) (ci : ConstInfo) (numParams numMotives numMinors numIndices : Nat)
    (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, ∀ (lvs : List Level) (pinst : List Expr), rl.inst = some (lvs, pinst) →
      ∀ (cij : ConstInfo) (I : Name) (nPc nf : Nat), env.find? rl.ctor = some cij →
        cij.kind = .ctor I nPc nf →
        RecRuleLawN M c ci nPc (numParams + numMotives + numMinors)
          (numParams + numMotives + numMinors + numIndices) rl cij
  /-- Every stored inductive family's fibres are truth values where its
  stored sort evaluates to zero and strict where it does not.
  No guard is needed: the stage of an installation that gives the
  former an arbitrary family (`mIndF`) takes it in the universe and
  admissible, which is strict above a proposition. -/
  ind_fib : ∀ (I : Name) (ci : ConstInfo) (nP nI : Nat) (ctors : List Name) (S : IndSpec),
    env.find? I = some ci → ci.kind = .induct nP nI ctors S → IndFibLaw M I ci nP nI S
  /-- Every rule of every stored recursor satisfies the slot law:
  where the major is the point, the recursor's application or
  the rule's constructor is. -/
  rec_rules_slot : ∀ (c : Name) (ci : ConstInfo) (numParams numMotives numMinors numIndices : Nat)
    (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, ∀ cij : ConstInfo, env.find? rl.ctor = some cij →
      RecRuleSlotLaw M c ci (numParams + numMotives + numMinors + numIndices) rl cij
  /-- Every rule flagged K of every stored recursor satisfies the K law:
  inversion of the least fixed point plus the plain law
  at the recursor's own parameters (`IndSpec.rec_rule_lawK`). -/
  rec_rules_k : ∀ (c : Name) (ci : ConstInfo) (numParams numMotives numMinors numIndices : Nat)
    (rules : List RecRule),
    env.find? c = some ci →
    ci.kind = .recursor numParams numMotives numMinors numIndices rules →
    ∀ rl ∈ rules, rl.k = true →
      RecRuleLawK M c ci (numParams + numMotives + numMinors)
        (numParams + numMotives + numMinors + numIndices) rl

/-- The empty environment has a model: any assignment, vacuous laws. -/
def EnvModel.empty (M : Name → List Nat → V) : EnvModel V Env.empty where
  M := M
  type_ok := fun _ _ h => by simp at h
  unfold := fun _ _ _ h => by simp at h
  rec_rules := fun _ _ _ _ _ _ _ h => by simp at h
  rec_rules_nested := fun _ _ _ _ _ _ _ h => by simp at h
  ind_fib := fun _ _ _ _ _ _ h => by simp at h
  rec_rules_k := fun _ _ _ _ _ _ _ h => by simp at h
  rec_rules_slot := fun _ _ _ _ _ _ _ h => by simp at h

end Fragment
