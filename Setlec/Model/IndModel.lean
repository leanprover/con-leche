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

/-- The environment's inductive-kind constants have models: every fact
here is what some checker rule's soundness consumes.  Grows on demand as
rules land (iota equations come with the recursor rules). -/
def IndOk (env : Env) (val : ConstVal V) : Prop :=
  (∀ cv, env.find? psigmaName = some (.indInfo cv) →
    ∀ ψ : Name → Nat, PairTyFacts V (val psigmaName ψ) (ψ uN) (ψ vN)) ∧
  (∀ cv nP nF, env.find? psigmaMkName = some (.ctorInfo cv nP nF) →
    nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
    ∀ ψ : Name → Nat, PairMkFacts V (val psigmaMkName ψ) (ψ uN) (ψ vN))

theorem IndOk.empty (val : ConstVal V) : IndOk V Env.empty val := by
  constructor
  · intro cv h
    simp [Env.find?, Env.empty] at h
  · intro cv nP nF h
    simp [Env.find?, Env.empty] at h

end Setlec
