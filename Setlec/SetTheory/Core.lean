/-!
# The axiomatic core: Tarski–Grothendieck set theory

The `SetTheory` class below is the *entire* axiomatic interface of the
consistency proof; every operator and law the model construction uses
(`Setlec/SetTheory/Basic.lean`) is *derived* from it in
`Setlec/SetTheory/Derive/*`, never assumed.

The set-theoretic axioms are those of Tarski–Grothendieck set theory
(Tarski's Axiom A over ZF minus Infinity; cf. the Mizar axiomatics,
A. Trybulec, *Tarski Grothendieck Set Theory*, Formalized Mathematics
1(1), 1990): **extensionality, pairing, union, power set, regularity,
the replacement scheme, and Tarski's Axiom A** (A. Tarski, *Über
unerreichbare Kardinalzahlen*, Fund. Math. 30 (1938), 68–89)
**strengthened with a transitivity clause**, making the universes it
postulates Grothendieck universes (SGA 4, Exp. I, Appendix).  Infinity
and choice are derivable and therefore absent.  Deliberate deviations
from a first-order presentation:

* **Replacement** is a Lean-level scheme: the image operator takes an
  arbitrary function `V → V`.  This is the usual strengthening when the
  ambient logic can quantify over class functions; `V_κ` for `κ`
  inaccessible still satisfies it.
* **Choice is not a field.**  A first-order axiomatization must assert
  choice (Tarski–Grothendieck theory usually derives a strong form from
  Axiom A); here the ambient logic is Lean with `Classical.choice`, and
  every set-level form of choice over `V` (the global selector
  `schoice`, and the Jech-form choice-function statement, *Set Theory*,
  §5) is a *theorem* — replacement applied to a classically chosen
  selector.  See `Setlec/SetTheory/Derive/Choice.lean`.  Asserting it
  here would add redundant axiomatic content; global choice is supplied
  by the meta-logic, not by this class.
* **`nonempty`** makes explicit what first-order logic assumes of every
  domain; without it all fields are vacuously satisfiable by an empty
  `V` and not even the empty set would be derivable.

Everything else — the empty set, separation, ordered pairs, infinity,
function graphs, the universe tower, quotients — is constructed in
`Setlec/SetTheory/Derive/*`.

**Known further weakening (not yet done).**  `tarski` gives a universe
above *every* set, i.e. a proper class of inaccessibles; the checker
only ever consumes the ω-indexed tower `univ 0, univ 1, univ 2, …`, so
the axiom could be weakened to an ω-chain of universes — the
"ω-many inaccessibles" hypothesis of Carneiro's consistency analysis of
Lean (*The Type Theory of Lean*, §1.2).  `tarski` is kept as a single
cleanly isolated field so that this swap stays local to this file and
`Setlec/SetTheory/Derive/Universe.lean`.
-/

namespace Setlec

universe u

/-- `y` and `u` are equinumerous: some (meta-level) function restricts to
a bijection from the members of `y` onto the members of `u`.  This is the
notion Tarski's Axiom A is stated with; using a Lean-level function keeps
ordered pairs out of the core (a first-order presentation instead
describes set-level bijections by formulas).  For the intended models this is
equivalent: a set-level bijection yields a meta-level one by choice, and
the axiom's disjunction is only ever *used* by refuting this side via a
diagonal argument (`Derive/Universe.lean`). -/
def Equinumerous {V : Type u} (mem : V → V → Prop) (y u : V) : Prop :=
  ∃ f : V → V,
    (∀ z, mem z y → mem (f z) u) ∧
    (∀ z z', mem z y → mem z' y → f z = f z' → z = z') ∧
    (∀ w, mem w u → ∃ z, mem z y ∧ f z = w)

/-- The matrix of Tarski's Axiom A (Tarski 1938), strengthened with the
transitivity clause: `u` is a Grothendieck universe (SGA 4, Exp. I,
Appendix).  The four clauses, in order:

1. *transitivity*: members of members are members — the clause that
   distinguishes a Grothendieck universe from a bare Tarski one, and
   what makes the empty set fall out of regularity;
2. *subsets of members are members*;
3. *power sets stay inside*: some member contains all subsets of a
   member (with clause 2 this makes `power y` itself a member);
4. *inaccessibility*: a subset of `u` is equinumerous with `u` or a
   member.  Dropping the equinumerosity disjunct is **inconsistent**
   (`u ⊆ u` would force `u ∈ u`, against regularity). -/
def IsTGUniverse {V : Type u} (mem : V → V → Prop) (u : V) : Prop :=
  (∀ y z, mem y u → mem z y → mem z u) ∧
  (∀ y z, mem y u → (∀ w, mem w z → mem w y) → mem z u) ∧
  (∀ y, mem y u → ∃ p, mem p u ∧ ∀ z, (∀ w, mem w z → mem w y) → mem z p) ∧
  (∀ y, (∀ w, mem w y → mem w u) → Equinumerous mem y u ∨ mem y u)

/-- A model of Tarski–Grothendieck set theory, axiomatized minimally:
membership, the seven set axioms (extensionality, pairing, union, power
set, regularity, Lean-level replacement, Tarski's Axiom A with
transitivity), and domain nonemptiness.  Choice is inherited from the
meta-logic (`Classical.choice`); see the module docstring. -/
class SetTheory (V : Type u) where
  /-- Set membership. -/
  Mem : V → V → Prop
  /-- First-order logic's nonempty domain, made explicit. -/
  nonempty : Nonempty V
  /-- Extensionality: sets with the same members are equal. -/
  ext : ∀ {x y : V}, (∀ z, Mem z x ↔ Mem z y) → x = y
  /-- Pairing: the unordered pair. -/
  upair : V → V → V
  /-- Characterization of the unordered pair. -/
  mem_upair : ∀ {z a b : V}, Mem z (upair a b) ↔ z = a ∨ z = b
  /-- Union: the union of the members. -/
  sUnion : V → V
  /-- Characterization of the union. -/
  mem_sUnion : ∀ {z x : V}, Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y
  /-- Power set. -/
  power : V → V
  /-- Characterization of the power set: members are the subsets. -/
  mem_power : ∀ {z x : V}, Mem z (power x) ↔ ∀ w, Mem w z → Mem w x
  /-- Regularity: every nonempty set has an `∈`-minimal member. -/
  regularity : ∀ x : V, (∃ y, Mem y x) → ∃ y, Mem y x ∧ ¬ ∃ z, Mem z y ∧ Mem z x
  /-- Replacement, as a Lean-level scheme: the image of a set under an
  arbitrary function `V → V`. -/
  image : (V → V) → V → V
  /-- Characterization of the replacement image. -/
  mem_image : ∀ {f : V → V} {a z : V}, Mem z (image f a) ↔ ∃ w, Mem w a ∧ z = f w
  /-- Tarski's Axiom A, strengthened with transitivity: every set is a
  member of a Grothendieck universe (`IsTGUniverse`). -/
  tarski : ∀ x : V, ∃ u : V, Mem x u ∧ IsTGUniverse Mem u

namespace SetTheory

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

variable {V : Type u} [SetTheory V]

/-- Subset, from membership. -/
protected def Subset (x y : V) : Prop := ∀ z, z ∈ˢ x → z ∈ˢ y

@[inherit_doc] scoped infix:50 " ⊆ˢ " => SetTheory.Subset

theorem Subset.refl (x : V) : x ⊆ˢ x := fun _ hz => hz

theorem Subset.trans {x y z : V} (h₁ : x ⊆ˢ y) (h₂ : y ⊆ˢ z) : x ⊆ˢ z :=
  fun w hw => h₂ w (h₁ w hw)

theorem Subset.antisymm {x y : V} (h₁ : x ⊆ˢ y) (h₂ : y ⊆ˢ x) : x = y :=
  ext fun z => ⟨h₁ z, h₂ z⟩

theorem mem_power_iff_subset {z x : V} : z ∈ˢ power x ↔ z ⊆ˢ x := mem_power

end SetTheory

end Setlec
