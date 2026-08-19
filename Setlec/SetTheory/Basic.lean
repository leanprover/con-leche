/-!
# The target set theory

Interface to the Tarski–Grothendieck set theory in which the checker's
soundness model lives.  All consistency proofs are parametric in a type `V`
carrying a `SetTheory` instance, so the final result reads:

> Assuming Tarski–Grothendieck set theory has a model, every environment
> accepted by the checker has a model; in particular no proof of `Empty`
> is ever accepted.

The instance existence is the "extra assumption for cardinality reasons"
mentioned in the design: inside Lean one can construct such a `V` from
`ZFSet`-style constructions plus universe assumptions (cf. lean4lean-model),
but the checker's verification does not depend on how `V` is obtained.

Axioms/operations are added to this interface on demand, as checker features
require them.  Keeping the interface minimal makes it evident what the
consistency proof actually assumes.
-/

namespace Setlec

/-- A model of (a growing fragment of) Tarski–Grothendieck set theory. -/
class SetTheory (V : Type u) where
  /-- Set membership. -/
  Mem : V → V → Prop
  /-- The empty set. -/
  empty : V
  /-- Nothing is a member of the empty set. -/
  not_mem_empty : ∀ x, ¬ Mem x empty

namespace SetTheory

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

end SetTheory

end Setlec
