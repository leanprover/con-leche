module

public import ConLeche.SetTheory.Formula

@[expose] public section

/-!
# The axiomatic core: first-order ZFC⁻ plus an ω-chain of Grothendieck universes

The `SetTheory` class below is the *entire* axiomatic interface of the
consistency proof; every operator and law the model construction uses
(`ConLeche/SetTheory/Basic.lean`) is *derived* from it in
`ConLeche/SetTheory/Derive/*`, never assumed.

The set-theoretic axioms are **strictly first-order**: extensionality,
pairing, union, power set, regularity, the first-order replacement schema
(over `Formula : Nat → Type 0` with value parameters `Fin p → V`),
Jech-form choice (`IsChoiceFn`), and an ω-chain of Grothendieck
universes `univChain 0 ∈ univChain 1 ∈ …` stated by the four
first-order SGA4 clauses of `IsGrothendieck` (SGA 4, Exp. I, Appendix).

Its consistency strength is that of `ZFC` plus `n` inaccessible cardinals for
every `n`; it has a model under `OmegaInaccessibles` (Mario Carneiro, *The Type
Theory of Lean*, master's thesis, Carnegie Mellon University, 2019, §1.2).
Everything else — the empty set, separation, ordered pairs, infinity,
function graphs, the universe tower, quotients — is constructed in
`ConLeche/SetTheory/Derive/*`.
-/

namespace ConLeche

universe u

/-- Relational unordered pair: `p = {a, b}` in `(V, Mem)`. -/
def IsUpair {V : Type u} (Mem : V → V → Prop) (p a b : V) : Prop :=
  ∀ z, Mem z p ↔ z = a ∨ z = b

/-- Relational Kuratowski ordered pair: `p = {{a}, {a, b}}` in `(V, Mem)`. -/
def IsKPair {V : Type u} (Mem : V → V → Prop) (p a b : V) : Prop :=
  ∃ s t, IsUpair Mem s a a ∧ IsUpair Mem t a b ∧ IsUpair Mem p s t

/-- Relational function graph: `g ⊆ dom × cod` is single-valued and total
on `dom` in `(V, Mem)`. -/
def IsFunGraph {V : Type u} (Mem : V → V → Prop) (g dom cod : V) : Prop :=
  (∀ p, Mem p g → ∃ x y, Mem x dom ∧ Mem y cod ∧ IsKPair Mem p x y) ∧
  (∀ x, Mem x dom → ExistsUnique fun y => Mem y cod ∧ ∃ p, Mem p g ∧ IsKPair Mem p x y)

/-- Jech-form choice function: `f` is a function graph on `x` picking a
member `y ∈ a` for each `a ∈ x`. -/
def IsChoiceFn {V : Type u} (Mem : V → V → Prop) (f x : V) : Prop :=
  (∀ p, Mem p f → ∃ a y, Mem a x ∧ Mem y a ∧ IsKPair Mem p a y) ∧
  (∀ a, Mem a x → ExistsUnique fun y => Mem y a ∧ ∃ p, Mem p f ∧ IsKPair Mem p a y)

/-- Grothendieck universe (SGA 4, Exp. I, Appendix): four first-order
conditions over `Mem`. -/
structure IsGrothendieck {V : Type u} (Mem : V → V → Prop) (u : V) : Prop where
  /-- *Transitivity*: members of members are members. -/
  transitivity : ∀ y z, Mem y u → Mem z y → Mem z u
  /-- *Pairing*: unordered pairs of members are members. -/
  pairing : ∀ a b, Mem a u → Mem b u → ∃ p, Mem p u ∧ IsUpair Mem p a b
  /-- *Power sets*: power sets of members are members. -/
  powerSet : ∀ y, Mem y u → ∃ p, Mem p u ∧ ∀ z, Mem z p ↔ ∀ w, Mem w z → Mem w y
  /-- *Indexed union*: the union of the range of any internal function graph
  `g : I → u` with `I ∈ u` is a member of `u`. -/
  indexedUnion : ∀ I g, Mem I u → IsFunGraph Mem g I u →
    ∃ w, Mem w u ∧ ∀ z, Mem z w ↔
      ∃ i y p, Mem i I ∧ Mem y u ∧ Mem p g ∧ IsKPair Mem p i y ∧ Mem z y

/-- A strictly first-order model of set theory of the strength the
checker needs: membership, extensionality, pairing, union, power set,
regularity, the first-order replacement schema, Jech-form choice, and
an ω-chain of SGA4 Grothendieck universes. -/
class SetTheory (V : Type u) where
  /-- Set membership. -/
  Mem : V → V → Prop
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
  /-- First-order replacement schema: for any formula `φ` in `2 + p` free
  variables and parameters `params : Fin p → V`, if `φ` is functional on
  `a` (relating each `x ∈ a` to a unique `y`), the image exists as a set.
  Index `0` is `y` and index `1` is `x`, aligning with `DefFun 1`. -/
  replacement : ∀ {p : Nat} (φ : Formula (2 + p)) (params : Fin p → V) (a : V),
    (∀ x, Mem x a →
      ExistsUnique fun y => φ.eval Mem (fappend (fcons y (fcons x Fin.elim0)) params)) →
    ∃ b : V, ∀ z, Mem z b ↔
      ∃ x, Mem x a ∧ φ.eval Mem (fappend (fcons z (fcons x Fin.elim0)) params)
  /-- Axiom of Choice (Jech form): every set of nonempty sets admits a
  set-level choice function. -/
  choice : ∀ x : V, (∀ a, Mem a x → ∃ y, Mem y a) → ∃ f : V, IsChoiceFn Mem f x
  /-- An ω-chain of Grothendieck universes: the sets interpreting the
  universe tower (intended model `V_{κ n}`). -/
  univChain : Nat → V
  /-- The chain increases strictly: each universe is a member of the next. -/
  univChain_mem : ∀ n : Nat, Mem (univChain n) (univChain (n + 1))
  /-- Each chain member is a Grothendieck universe (`IsGrothendieck`). -/
  univChain_grothendieck : ∀ n : Nat, IsGrothendieck Mem (univChain n)

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

/-- Proof-carrying predicate asserting that the image `{f w : w ∈ a}`
exists as a set in `V`. -/
def HasImage (f : V → V) (a : V) : Prop :=
  ∃ b : V, ∀ z, z ∈ˢ b ↔ ∃ w, w ∈ˢ a ∧ z = f w

/-- Proof-carrying, zero-junk replacement image `{f w : w ∈ a}`. -/
noncomputable def image (f : V → V) (a : V) (h : HasImage f a) : V :=
  Classical.choose h

theorem mem_image {f : V → V} {a z : V} {h : HasImage f a} :
    z ∈ˢ image f a h ↔ ∃ w, w ∈ˢ a ∧ z = f w :=
  Classical.choose_spec h z

theorem HasImage.congr {a : V} {f g : V → V}
    (hfg : ∀ x, x ∈ˢ a → f x = g x) (hf : HasImage f a) : HasImage g a := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨b, fun z => (hb z).trans ?_⟩
  exact ⟨fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (hfg w hw)⟩,
         fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (hfg w hw).symm⟩⟩

theorem HasImage.ext {a b : V} {f g : V → V} (hab : a = b)
    (hfg : ∀ x, x ∈ˢ a → f x = g x) (hf : HasImage f a) : HasImage g b :=
  hab ▸ hf.congr hfg

theorem image_congr {a : V} {f g : V → V} (hf : HasImage f a) (hg : HasImage g a)
    (h : ∀ x, x ∈ˢ a → f x = g x) : image f a hf = image g a hg :=
  ext fun z => by
    rw [mem_image (h := hf), mem_image (h := hg)]
    exact ⟨fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (h w hw)⟩,
           fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (h w hw).symm⟩⟩

theorem image_ext {a b : V} {f g : V → V} (hab : a = b)
    (hf : HasImage f a) (hg : HasImage g b)
    (h : ∀ x, x ∈ˢ a → f x = g x) : image f a hf = image g b hg := by
  subst hab
  exact image_congr hf hg h

attribute [irreducible] image

end SetTheory

/-- **Model existence (consistency / non-vacuity assumption).**
There exists a model `(V, SetTheory V)` of our strictly first-order set theory
(`ZFC⁻` + an ω-chain of SGA4 Grothendieck universes).

Because `SetTheory` is strictly first-order (`Formula`, `IsGrothendieck`,
Jech-form `choice`), model existence is essentially the consistency of this
set theory: classically, by Gödel's completeness theorem, a first-order theory
has a model iff it is syntactically consistent (and by downward
Löwenheim–Skolem already at `Type 0`).  The `*_no_False` theorems take
`ModelExists` explicitly — rather than an unused `(V : Type w) [SetTheory V]`
parameter — because we need the background set theory to be non-vacuous
(consistent) for those theorems to be meaningful. -/
def ModelExists : Prop :=
  Nonempty (Σ V : Type u, SetTheory V)

end ConLeche
