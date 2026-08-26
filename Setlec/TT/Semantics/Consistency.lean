import Setlec.TT.Semantics.Soundness

/-!
# Consistency

The theorem is **absolute**: there is no side condition about a
satisfiable context, because the layer has no global context to satisfy.
Every constant the checker accepts either has a value (definitions,
theorems, `opaque`s, the compiler-trust family), or has a checked model
artifact that plays the role of a value (modeled inductives, direct
structures), or is one of the finitely many pinned standard axioms; the
first two unfold at denotation time and the last are built in.  So the
statement reads simply: *no closed term has type `Empty`*.

As everywhere in this project, the result is parametric in a model of
the `SetTheory` interface — the "extra assumption for cardinality
reasons".
-/

namespace Setlec.TT

open SetTheory

universe w

/-- The canonical environment for closed terms (its values are never
read). -/
noncomputable def rho0 (V : Type w) [SetTheory V] : Nat → V :=
  fun _ => SetTheory.empty

/-- A closed derivation lands in the interpretation of its type. -/
theorem closed_sound (V : Type w) [SetTheory V] {e A : VExpr}
    (h : HasType [] e A) : interp V (rho0 V) e ∈ˢ interp V (rho0 V) A :=
  h.sound V (rho0 V) (Sat_nil V _)

/-- No closed derivation targets a type whose interpretation is empty. -/
theorem not_hasType_of_interp_empty (V : Type w) [SetTheory V] {e A : VExpr}
    (hA : interp V (rho0 V) A = SetTheory.empty) (h : HasType [] e A) : False :=
  not_mem_empty _ (hA ▸ closed_sound V h)

/-- **Consistency.**  No closed term of the declarative type theory has
type `Empty` — at any universe level, so in particular none has type
`False = Empty.{0}`. -/
theorem no_proof_of_empty (V : Type w) [SetTheory V] {u : Nat} {e : VExpr}
    (h : HasType [] e (emptyT u)) : False :=
  not_hasType_of_interp_empty V rfl h

/-- The `Prop`-level instance: no closed proof of `False`. -/
theorem no_proof_of_false (V : Type w) [SetTheory V] {e : VExpr}
    (h : HasType [] e (emptyT 0)) : False :=
  no_proof_of_empty V h

/-- …and the theory is not vacuous: `Sort 0` is derivable, so the
absence of a proof of `Empty` is a real fact about a real theory. -/
theorem sort_zero_hasType : HasType [] (.sort 0) (.sort 1) := .sort

end Setlec.TT
