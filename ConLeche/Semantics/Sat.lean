module

public import ConLeche.Semantics.Interp

@[expose] public section

/-!
# `Sat` — the annotated context's satisfaction, and its transitivity kit

`Sat` with its introduction lemmas.  It is model-free (a
`List AnnotTerm`, a valuation, and `interp`), and the model states its
context currency with it.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

section
variable (V : Type w) [SetTheory V]

/-- `ρ` satisfies an annotated context over `interp` — the `Sat`
transpose. -/
def Sat (Δa : List AnnotTerm) (ρ : Nat → V) : Prop :=
  ∀ i Aa, Δa[i]? = some Aa →
    ρ i ∈ˢ interp V (fun j => ρ (j + i + 1)) Aa

theorem Sat_nil (ρ : Nat → V) : Sat V [] ρ := by
  intro i Aa hi
  cases hi

theorem Sat_cons {Δa : List AnnotTerm} {Aa : AnnotTerm} {ρ : Nat → V} {x : V}
    (hρ : Sat V Δa ρ) (hx : x ∈ˢ interp V ρ Aa) :
    Sat V (Aa :: Δa) (cons x ρ) := by
  intro i Aa' hi
  cases i with
  | zero =>
    obtain rfl : Aa = Aa' := by simpa using hi
    exact hx
  | succ i =>
    have h := hρ i Aa' (by simpa using hi)
    exact h

end

section
variable {V : Type w} [SetTheory V]

/-- The tail of a satisfying valuation satisfies the tail context —
`Sat_cons`'s inverse, and what every weakening step consumes. -/
theorem Sat_tail {Δa : List AnnotTerm} {Ba : AnnotTerm} {ρ : Nat → V}
    (hρ : Sat V (Ba :: Δa) ρ) : Sat V Δa (fun j => ρ (j + 1)) := by
  intro i Aa hi
  exact hρ (i + 1) Aa (by simpa using hi)

/-- Dropping entries shifts the valuation. -/
theorem Sat_drop {Δ : List AnnotTerm} {ρ : Nat → V} (h : Sat V Δ ρ)
    (m : Nat) : Sat V (Δ.drop m) (fun j => ρ (j + m)) := by
  intro i Aa hi
  rw [List.getElem?_drop] at hi
  have h1 := h (m + i) Aa hi
  show ρ (i + m) ∈ˢ interp V (fun j => ρ (j + i + 1 + m)) Aa
  have e : (fun j => ρ (j + i + 1 + m)) = fun j => ρ (j + (m + i) + 1) := by
    funext j; congr 1; omega
  rw [e, Nat.add_comm i m]
  exact h1

end

end ConLeche.Semantics
