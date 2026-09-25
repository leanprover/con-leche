module

public import Fragment.Rules
public import Fragment.EnvModel

@[expose] public section

/-!
# The three claims

One motive per relation, in the currency of the model: `interp`
equality, membership, and the invariant `WellDenoted`.  Each is
stated at a model `m` of the environment, a valuation `φ`, and for
every environment `ρ` satisfying the context:

* **`RedSem`** — a reduction of a well-denoted term yields a
  well-denoted term with the same denotation;
* **`DefEqSem`** — two well-denoted terms the checker calls equal have
  equal denotations;
* **`InferSem`** — an inferred term is well-denoted, its type is
  well-denoted, and the term's denotation is a member of the type's.

These are the claims of `ConLeche/Model/Claims.lean`, in the shape of
`ConLeche/Model/Rules/Motive.lean`.  Two of that file's three
strengthenings are unnecessary here — there is no reading to
establish (the interpretation is total) and no frame to carry (no
free variables) — and the third is the single grade: `InferSem`
always *establishes* the subject's invariant, never consumes it.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] {env : Env}

/-- **`Red`'s claim**: reduction preserves the invariant and the
denotation. -/
def RedSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (e e' : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ e →
    WellDenoted m.M φ ρ e' ∧ interp m.M φ ρ e = interp m.M φ ρ e'

/-- **`DefEq`'s claim**: equal denotations. -/
def DefEqSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (a b : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ → WellDenoted m.M φ ρ a → WellDenoted m.M φ ρ b →
    interp m.M φ ρ a = interp m.M φ ρ b

/-- **`Infer`'s claim**: the term and its type are well-denoted, and
the term's denotation is a member of the type's. -/
def InferSem (m : EnvModel V env) (φ : Name → Nat) (Γ : List Expr) (e T : Expr) : Prop :=
  ∀ ρ : Nat → V, Sat m.M φ Γ ρ →
    WellDenoted m.M φ ρ e ∧ WellDenoted m.M φ ρ T ∧ interp m.M φ ρ e ∈ˢ interp m.M φ ρ T

end Fragment
