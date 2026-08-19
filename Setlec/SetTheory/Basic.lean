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
  /-- Set-theoretic function abstraction over `A`, at codomain sort `v`:
  for `v > 0` the function graph `{⟨x, F x⟩ : x ∈ A}`, for `v = 0` the
  proof point `•` (proofs are degenerate). -/
  lam : Nat → V → (V → V) → V
  /-- Set-theoretic application: `⋃ {y : ⟨a, y⟩ ∈ f}` — on graphs the
  value, on the proof point again the proof point. -/
  app : V → V → V
  /-- `lam` only depends on the function's values on `A`. -/
  lam_congr : ∀ {v : Nat} {A : V} {F F' : V → V},
    (∀ x, Mem x A → F x = F' x) → lam v A F = lam v A F'
  /-- Introduction: a function with fibre-wise members abstracts into the
  dependent product.  (No fibre-universe premise: for `v = 0` the premise
  itself witnesses every fibre inhabited.) -/
  lam_mem : ∀ {v : Nat} {A : V} {F B : V → V},
    (∀ x, Mem x A → Mem (F x) (B x)) → Mem (lam v A F) (pi v A B)
  /-- Elimination: application stays in the fibre.  The fibre-universe
  premise makes the `v = 0` case realizable (fibres are then truth
  values, so the inhabited fibre is the singleton of `•`). -/
  app_mem : ∀ {v : Nat} {A f a : V} {B : V → V},
    Mem f (pi v A B) → Mem a A → (∀ x, Mem x A → Mem (B x) (univ v)) →
    Mem (app f a) (B a)
  /-- Beta: conditional on membership, as set-theoretic functions have set
  domains. -/
  app_lam : ∀ {v : Nat} {A a : V} {F B : V → V},
    Mem a A → (∀ x, Mem x A → Mem (F x) (B x)) →
    (∀ x, Mem x A → Mem (B x) (univ v)) →
    app (lam v A F) a = F a
  /-- The *tagged proof point* `pt := {∅}`: the canonical inhabitant of
  every true proposition.  Chosen to never be a function graph (a graph's
  elements are Kuratowski pairs, which are nonempty, so `{∅}` is not a
  set of pairs) — this tag is what lets beta soundness rule out
  Prop/Type mismatches by contradiction instead of by typing metatheory
  (see DESIGN.md). -/
  pt : V
  /-- Propositions have at most the proof point as element. -/
  mem_univ_zero : ∀ {T x : V}, Mem T (univ 0) → Mem x T → x = pt
  /-- Inhabitants of Prop-valued `pi`s are the proof point (`pi 0 A B` is
  a truth value, i.e. a subset of `{pt}`). -/
  mem_pi_zero : ∀ {A f : V} {B : V → V}, Mem f (pi 0 A B) → f = pt
  /-- Type-valued functions are graphs, never the proof point. -/
  lam_ne_pt : ∀ {v : Nat} {A : V} {F : V → V}, v ≠ 0 → lam v A F ≠ pt
  /-- Graphs determine their domains: membership in a type-valued `pi`
  pins the abstraction's domain. -/
  lam_dom : ∀ {v' v : Nat} {A A' : V} {F : V → V} {B : V → V},
    Mem (lam v' A F) (pi v A' B) → v ≠ 0 → v' ≠ 0 →
    ∀ x, Mem x A' → Mem x A
  /-- Truth values for equality: `eqv x y` is `{pt}` if `x = y` and `∅`
  otherwise (classically definable). -/
  eqv : V → V → V
  eqv_mem_univ : ∀ x y, Mem (eqv x y) (univ 0)
  mem_eqv : ∀ {a x y : V}, Mem a (eqv x y) → x = y
  pt_mem_eqv_self : ∀ x, Mem pt (eqv x x)
  /-- The canonical singleton `{pt}` (the model of `PUnit` at every
  level, and the true truth value). -/
  unitSet : V
  pt_mem_unitSet : Mem pt unitSet
  mem_unitSet : ∀ {x : V}, Mem x unitSet → x = pt
  unitSet_mem_univ : ∀ u, Mem unitSet (univ u)
  /-- The finite ordinals (the model of `Nat`). -/
  omega : V
  omega_mem_univ : Mem omega (univ 1)
  natzero : V
  natzero_mem : Mem natzero omega
  natsucc : V → V
  natsucc_mem : ∀ {n : V}, Mem n omega → Mem (natsucc n) omega
  /-- Set-theoretic recursion on omega: `natrec z s n` with the minor
  premise `s` applied as a set-theoretic (curried) function.  The
  equations are conditional on typing where realizability requires it;
  `natrec_mem` is the recursion theorem plus induction. -/
  natrec : V → V → V → V
  natrec_zero : ∀ z s, natrec z s natzero = z
  natrec_succ : ∀ z s {n}, Mem n omega →
    natrec z s (natsucc n) = app (app s n) (natrec z s n)
  natrec_mem : ∀ {M z s n : V},
    Mem z (app M natzero) →
    (∀ k, Mem k omega → ∀ ih, Mem ih (app M k) →
      Mem (app (app s k) ih) (app M (natsucc k))) →
    Mem n omega → Mem (natrec z s n) (app M n)
  /-- Dependent pairs.  `sigmaSet w A B` is, for `w ≠ 0`, the set of
  Kuratowski pairs `⟨a, b⟩` with `a ∈ A`, `b ∈ B a`; for `w = 0` the
  truth value `[∃ a ∈ A, B a inhabited]` (Prop collapse).  `spair`,
  `sfst`, `ssnd` are pairing and projections, with `pt` mapped to `pt`
  (realizable: `pt = {∅}` is not a pair). -/
  sigmaSet : Nat → V → (V → V) → V
  spair : V → V → V
  sfst : V → V
  ssnd : V → V
  sigma_congr : ∀ {w : Nat} {A : V} {B B' : V → V},
    (∀ x, Mem x A → B x = B' x) → sigmaSet w A B = sigmaSet w A B'
  sigma_mem_univ : ∀ {u v : Nat} {A : V} {B : V → V}, Mem A (univ u) →
    (∀ x, Mem x A → Mem (B x) (univ v)) →
    Mem (sigmaSet (Nat.max u v) A B) (univ (Nat.max u v))
  spair_mem : ∀ {w : Nat} {A : V} {B : V → V} {a b : V}, w ≠ 0 →
    Mem a A → Mem b (B a) → Mem (spair a b) (sigmaSet w A B)
  pt_mem_sigma : ∀ {A : V} {B : V → V} {a b : V},
    Mem a A → Mem b (B a) → Mem pt (sigmaSet 0 A B)
  mem_sigma_elim : ∀ {w : Nat} {A : V} {B : V → V} {t : V},
    Mem t (sigmaSet w A B) →
    ∃ a b, Mem a A ∧ Mem b (B a) ∧ (w = 0 → t = pt) ∧ (w ≠ 0 → t = spair a b)
  sfst_spair : ∀ a b, sfst (spair a b) = a
  ssnd_spair : ∀ a b, ssnd (spair a b) = b
  sfst_pt : sfst pt = pt
  ssnd_pt : ssnd pt = pt

namespace SetTheory

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

end SetTheory

end Setlec
