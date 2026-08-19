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

/-- What the projection rules need from the pair type former's value:
partial applications determine their argument domains, and the full
application is a sigma set. -/
structure PairTyFacts (val : ConstVal V) (ψ : Name → Nat) : Prop where
  dom₀ : ∀ {vE : Nat} {A₀ : V} {B₀ : V → V} {x : V},
    val psigmaName ψ ∈ˢ pi vE A₀ B₀ → x ∈ˢ A₀ → x ∈ˢ univ (ψ uN)
  dom₁ : ∀ {vA : V} {vE : Nat} {A₁ : V} {B₁ : V → V} {x : V},
    vA ∈ˢ univ (ψ uN) → app (val psigmaName ψ) vA ∈ˢ pi vE A₁ B₁ →
    x ∈ˢ A₁ → x ∈ˢ pi (ψ vN + 1) vA fun _ => univ (ψ vN)
  fold : ∀ {vA vB : V}, vA ∈ˢ univ (ψ uN) →
    vB ∈ˢ pi (ψ vN + 1) vA (fun _ => univ (ψ vN)) →
    app (app (val psigmaName ψ) vA) vB =
      sigmaSet (Nat.max (ψ uN) (ψ vN)) vA fun x => app vB x

/-- What the projection rules need from the pair constructor's value:
away from the Prop collapse, partial applications determine their
argument domains; the full application is the pair (or the proof point
under the collapse). -/
structure PairMkFacts (val : ConstVal V) (ψ : Name → Nat) : Prop where
  dom₀ : Nat.max (ψ uN) (ψ vN) ≠ 0 →
    ∀ {vE : Nat} {A₀ : V} {B₀ : V → V} {x : V},
    val psigmaMkName ψ ∈ˢ pi vE A₀ B₀ → x ∈ˢ A₀ → x ∈ˢ univ (ψ uN)
  dom₁ : Nat.max (ψ uN) (ψ vN) ≠ 0 →
    ∀ {vA : V} {vE : Nat} {A₁ : V} {B₁ : V → V} {x : V},
    vA ∈ˢ univ (ψ uN) → app (val psigmaMkName ψ) vA ∈ˢ pi vE A₁ B₁ →
    x ∈ˢ A₁ → x ∈ˢ pi (ψ vN + 1) vA fun _ => univ (ψ vN)
  dom₂ : Nat.max (ψ uN) (ψ vN) ≠ 0 →
    ∀ {vA vB : V} {vE : Nat} {A₂ : V} {B₂ : V → V} {x : V},
    vA ∈ˢ univ (ψ uN) → vB ∈ˢ pi (ψ vN + 1) vA (fun _ => univ (ψ vN)) →
    app (app (val psigmaMkName ψ) vA) vB ∈ˢ pi vE A₂ B₂ →
    x ∈ˢ A₂ → x ∈ˢ vA
  dom₃ : Nat.max (ψ uN) (ψ vN) ≠ 0 →
    ∀ {vA vB va : V} {vE : Nat} {A₃ : V} {B₃ : V → V} {x : V},
    vA ∈ˢ univ (ψ uN) → vB ∈ˢ pi (ψ vN + 1) vA (fun _ => univ (ψ vN)) →
    va ∈ˢ vA →
    app (app (app (val psigmaMkName ψ) vA) vB) va ∈ˢ pi vE A₃ B₃ →
    x ∈ˢ A₃ → x ∈ˢ app vB va
  fold : ∀ {vA vB va vb : V}, vA ∈ˢ univ (ψ uN) →
    vB ∈ˢ pi (ψ vN + 1) vA (fun _ => univ (ψ vN)) →
    va ∈ˢ vA → vb ∈ˢ app vB va →
    app (app (app (app (val psigmaMkName ψ) vA) vB) va) vb =
      (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair va vb)

/-- The environment's inductive-kind constants have models: every fact
here is what some checker rule's soundness consumes.  Grows on demand as
rules land (iota equations come with the recursor rules). -/
def IndOk (env : Env) (val : ConstVal V) : Prop :=
  (∀ cv, env.find? psigmaName = some (.indInfo cv) →
    ∀ ψ : Name → Nat, PairTyFacts V val ψ) ∧
  (∀ cv nP nF, env.find? psigmaMkName = some (.ctorInfo cv nP nF) →
    nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
    ∀ ψ : Name → Nat, PairMkFacts V val ψ)

/-- Transport pair-former facts along valuation agreement at the name. -/
theorem PairTyFacts.of_agree {val val' : ConstVal V} {ψ : Name → Nat}
    (hag : val' psigmaName ψ = val psigmaName ψ)
    (h : PairTyFacts V val ψ) : PairTyFacts V val' ψ where
  dom₀ hp hx := h.dom₀ (by rw [← hag]; exact hp) hx
  dom₁ hA hp hx := h.dom₁ hA (by rw [← hag]; exact hp) hx
  fold hA hB := by rw [hag]; exact h.fold hA hB

/-- Transport pair-constructor facts along valuation agreement. -/
theorem PairMkFacts.of_agree {val val' : ConstVal V} {ψ : Name → Nat}
    (hag : val' psigmaMkName ψ = val psigmaMkName ψ)
    (h : PairMkFacts V val ψ) : PairMkFacts V val' ψ where
  dom₀ := by
    intro hw vE A₀ B₀ x hp hx
    exact h.dom₀ hw (by rw [← hag]; exact hp) hx
  dom₁ := by
    intro hw vA vE A₁ B₁ x hA hp hx
    exact h.dom₁ hw hA (by rw [← hag]; exact hp) hx
  dom₂ := by
    intro hw vA vB vE A₂ B₂ x hA hB hp hx
    exact h.dom₂ hw hA hB (by rw [← hag]; exact hp) hx
  dom₃ := by
    intro hw vA vB va vE A₃ B₃ x hA hB ha hp hx
    exact h.dom₃ hw hA hB ha (by rw [← hag]; exact hp) hx
  fold := by
    intro vA vB va vb hA hB ha hb
    rw [hag]
    exact h.fold hA hB ha hb

theorem IndOk.empty (val : ConstVal V) : IndOk V Env.empty val := by
  constructor
  · intro cv h
    simp [Env.find?, Env.empty] at h
  · intro cv nP nF h
    simp [Env.find?, Env.empty] at h

end Setlec
