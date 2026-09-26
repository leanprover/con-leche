module

public import ConLeche.Semantics.Interp

@[expose] public section

/-!
# `SetBase/Sat` — the annotated context's satisfaction, and its
transitivity kit

`Sat` with its introduction lemmas, re-based at THE SEPARATION's S2
(task #161).  It lived in `Annot/EnvModel.lean` beside the
`EnvS`-containing invariant; it is model-free (a `List AnnotTerm`, a valuation, and
`interp`), and both lanes state their context currency with it.

Statements verbatim, namespace (`ConLeche.SetR.Interp`) unchanged.
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

end

end ConLeche.Semantics
