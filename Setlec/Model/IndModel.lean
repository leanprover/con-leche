import Setlec.Kernel.Basis
import Setlec.SetTheory.Basic
import Setlec.Model.BasisVal

/-!
# Semantic requirements on stored inductive-kind constants

`IndOk env val` states, per inductive-kind constant the environment
stores, exactly the semantic facts the checker functions' soundness
needs — abstractly over the valuation, independent of which concrete
model realizes them.  `whnf`/`inferType`/`isDefEq` soundness consumes
only these; the *installation* of a basis block proves them from the
hand-written values (`Setlec.Model.BasisVal`).  The predicate grows on
demand, like the `SetTheory` interface itself.
-/

namespace Setlec

variable (V : Type u) [SetTheory V]

open SetTheory

/-- What the projection rules need from the pair type former's value at
one level assignment (`u`, `v` the assigned levels): partial
applications determine their argument domains, and the full application
is a sigma set. -/
structure PairTyFacts (pv : V) (u v : Nat) : Prop where
  dom₀ : ∀ {vE : Nat} {A₀ : V} {B₀ : V → V} {x : V},
    pv ∈ˢ pi vE A₀ B₀ → x ∈ˢ A₀ → x ∈ˢ univ u
  dom₁ : ∀ {vA : V} {vE : Nat} {A₁ : V} {B₁ : V → V} {x : V},
    vA ∈ˢ univ u → app pv vA ∈ˢ pi vE A₁ B₁ →
    x ∈ˢ A₁ → x ∈ˢ pi (v + 1) vA fun _ => univ v
  fold : ∀ {vA vB : V}, vA ∈ˢ univ u →
    vB ∈ˢ pi (v + 1) vA (fun _ => univ v) →
    app (app pv vA) vB = sigmaSet (Nat.max u v) vA fun x => app vB x

/-- What the projection rules need from the pair constructor's value:
away from the Prop collapse, partial applications determine their
argument domains; the full application is the pair (or the proof point
under the collapse). -/
structure PairMkFacts (pv : V) (u v : Nat) : Prop where
  dom₀ : Nat.max u v ≠ 0 →
    ∀ {vE : Nat} {A₀ : V} {B₀ : V → V} {x : V},
    pv ∈ˢ pi vE A₀ B₀ → x ∈ˢ A₀ → x ∈ˢ univ u
  dom₁ : Nat.max u v ≠ 0 →
    ∀ {vA : V} {vE : Nat} {A₁ : V} {B₁ : V → V} {x : V},
    vA ∈ˢ univ u → app pv vA ∈ˢ pi vE A₁ B₁ →
    x ∈ˢ A₁ → x ∈ˢ pi (v + 1) vA fun _ => univ v
  dom₂ : Nat.max u v ≠ 0 →
    ∀ {vA vB : V} {vE : Nat} {A₂ : V} {B₂ : V → V} {x : V},
    vA ∈ˢ univ u → vB ∈ˢ pi (v + 1) vA (fun _ => univ v) →
    app (app pv vA) vB ∈ˢ pi vE A₂ B₂ →
    x ∈ˢ A₂ → x ∈ˢ vA
  dom₃ : Nat.max u v ≠ 0 →
    ∀ {vA vB va : V} {vE : Nat} {A₃ : V} {B₃ : V → V} {x : V},
    vA ∈ˢ univ u → vB ∈ˢ pi (v + 1) vA (fun _ => univ v) →
    va ∈ˢ vA →
    app (app (app pv vA) vB) va ∈ˢ pi vE A₃ B₃ →
    x ∈ˢ A₃ → x ∈ˢ app vB va
  fold : ∀ {vA vB va vb : V}, vA ∈ˢ univ u →
    vB ∈ˢ pi (v + 1) vA (fun _ => univ v) →
    va ∈ˢ vA → vb ∈ˢ app vB va →
    app (app (app (app pv vA) vB) va) vb =
      (if Nat.max u v = 0 then pt else spair va vb)
  /-- At the Prop collapse the constructor's full application is the
  proof point unconditionally (no membership needed: the value itself
  is the proof point). -/
  zero : Nat.max u v = 0 → ∀ x y z w' : V,
    app (app (app (app pv x) y) z) w' = pt

/-- Left fold of set application along a value spine. -/
def SpineFold (v : V) (xs : List V) : V := xs.foldl SetTheory.app v

theorem SpineFold_nil (v : V) : SpineFold V v [] = v := rfl

theorem SpineFold_cons (v x : V) (xs : List V) :
    SpineFold V v (x :: xs) = SpineFold V (SetTheory.app v x) xs := rfl

theorem SpineFold_append (v : V) (xs ys : List V) :
    SpineFold V v (xs ++ ys) = SpineFold V (SpineFold V v xs) ys := by
  simp [SpineFold, List.foldl_append]

/-- One `AnnotOk`-app typing slot: the function value sits in a pi whose
domain contains the argument, with the fibres in the tag's universe. -/
def AppSlot (f a : V) : Prop :=
  ∃ vE A B, f ∈ˢ pi vE A (B : V → V) ∧ a ∈ˢ A ∧
    ∀ x, x ∈ˢ A → B x ∈ˢ univ vE

/-- Typing slots along a whole application spine. -/
def ChainSlots (v : V) : List V → Prop
  | [] => True
  | x :: xs => AppSlot V v x ∧ ChainSlots (SetTheory.app v x) xs

theorem ChainSlots_append (v : V) (xs ys : List V) :
    ChainSlots V v (xs ++ ys) ↔
      ChainSlots V v xs ∧ ChainSlots V (SpineFold V v xs) ys := by
  induction xs generalizing v with
  | nil => simp [ChainSlots, SpineFold]
  | cons x xs ih =>
    simp only [List.cons_append, ChainSlots, SpineFold_cons, ih,
      and_assoc]

/-- Block completeness: whenever a pinned basis *recursor* is stored,
the other members of its block are stored (pinned) too.  This holds
because blocks install as a unit with the recursor last; iota soundness
uses it to resolve the constants a rule right-hand side mentions. -/
def BasisBlocks (env : Env) : Prop :=
  (∀ cv mI rP rules,
    env.find? (eqName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? eqName = some eqA ∧ env.find? eqReflName = some eqReflA) ∧
  (∀ cv mI rP rules,
    env.find? (natName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? natName = some natA ∧ env.find? natZeroName = some natZeroA ∧
    env.find? natSuccName = some natSuccA) ∧
  (∀ cv mI rP rules,
    env.find? (psigmaName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA) ∧
  (∀ cv mI rP rules,
    env.find? (punitName.str "rec") = some (.recInfo cv mI rP rules) →
    env.find? punitName = some punitA ∧
    env.find? punitUnitName = some punitUnitA)

/-- Every stored recursor rule's constructor is itself stored: blocks
carry their constructors, and the recursor is installed after them. -/
def RecCtorsStored (env : Env) : Prop :=
  ∀ n cv mI rP rules,
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, ∃ cvj cnP cnF,
      env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)

theorem RecCtorsStored.empty : RecCtorsStored Env.empty := by
  intro n cv mI rP rules h
  simp [Env.find?, Env.empty] at h

/-- The environment's inductive-kind constants have models: every fact
here is what some checker rule's soundness consumes.  Grows on demand as
rules land (iota equations come with the recursor rules). -/
def IndOk (env : Env) (val : ConstVal V) : Prop :=
  (∀ cv caps, env.find? psigmaName = some (.indInfo cv caps) →
    cv.levelParams = [uN, vN] ∧
    ∀ ψ : Name → Nat, PairTyFacts V (val psigmaName ψ) (ψ uN) (ψ vN)) ∧
  (∀ cv nP nF, env.find? psigmaMkName = some (.ctorInfo cv nP nF) →
    nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
    ∀ ψ : Name → Nat, PairMkFacts V (val psigmaMkName ψ) (ψ uN) (ψ vN)) ∧
  (∀ cv caps, env.find? punitName = some (.indInfo cv caps) →
    ∀ (ψ : Name → Nat) (x : V), x ∈ˢ val punitName ψ → x = pt) ∧
  (∀ n ci, env.find? n = some ci → ConstantInfo.isBasis ci = true →
    reservedBasisNames.contains n = true →
    ci = pinnedInfo n ∧ ∀ ψ : Name → Nat, val n ψ = pinnedVal V n ψ) ∧
  BasisBlocks env ∧
  RecCtorsStored env ∧
  (∀ (ψ : Name → Nat) (x : V), x ∈ˢ val emptyName ψ → False)

theorem BasisBlocks.empty : BasisBlocks Env.empty := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro cv mI rP rules h; simp [Env.find?, Env.empty] at h)

theorem IndOk.empty (val : ConstVal V)
    (hE : ∀ (ψ : Name → Nat) (x : V), x ∈ˢ val emptyName ψ → False) :
    IndOk V Env.empty val := by
  refine ⟨?_, ?_, ?_, ?_, BasisBlocks.empty, RecCtorsStored.empty, hE⟩
  · intro cv caps h
    simp [Env.find?, Env.empty] at h
  · intro cv nP nF h
    simp [Env.find?, Env.empty] at h
  · intro cv caps h
    simp [Env.find?, Env.empty] at h
  · intro n ci h
    simp [Env.find?, Env.empty] at h

end Setlec
