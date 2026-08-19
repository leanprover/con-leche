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
  /-- The interpretation of `Sort n`: `univ 0` is the set of truth values
  `{∅, {∅}}` interpreting `Prop`, and `univ (n+1)` is (essentially) the
  `n`-th Grothendieck universe. -/
  univ : Nat → V
  /-- Each sort is an element of the next one: `⟦Sort n⟧ ∈ ⟦Sort (n+1)⟧`,
  the model-side counterpart of `Sort n : Sort (n+1)`. -/
  univ_mem_univ : ∀ n, Mem (univ n) (univ (n + 1))
  /-- The dependent product over `A` with fibre family `B`, where `v` is the
  (evaluated) sort level of the codomain.  Following the standard model
  (Carneiro, *The Type Theory of Lean*, §6.2), the interpretation splits on
  the codomain living in `Prop`:

  * `v = 0`: the truth value `[∀ x ∈ A, B x inhabited]` — a subset of the
    fixed singleton, which is what makes `Prop` impredicative and proof
    irrelevance immediate;
  * `v > 0`: the set of set-theoretic dependent functions on `A`.

  The level must be passed in because it is not recoverable from the sets
  alone (e.g. `⟦True⟧ = ⟦PUnit⟧` as sets). -/
  pi : Nat → V → (V → V) → V
  /-- Formation: `Π` lands in the universe given by the `imax` rule.
  Realizable: for `v = 0` a truth value is in `univ 0`; for `v > 0` this is
  Grothendieck universe closure under dependent products. -/
  pi_mem_univ : ∀ {u v : Nat} {A : V} {B : V → V}, Mem A (univ u) →
    (∀ x, Mem x A → Mem (B x) (univ v)) →
    Mem (pi v A B) (univ (if v = 0 then 0 else Nat.max u v))
  /-- `pi` only depends on the fibre family's values on `A`. -/
  pi_congr : ∀ {v : Nat} {A : V} {B B' : V → V},
    (∀ x, Mem x A → B x = B' x) → pi v A B = pi v A B'

namespace SetTheory

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

end SetTheory

end Setlec
