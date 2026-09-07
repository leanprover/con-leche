import Lech.SetTheory.Core

/-!
# Aczel's sets-as-trees: a realizability leaf for the `SetTheory` core

This module demonstrates what the whole development assumes.  It builds
Aczel's encoding of sets as well-founded trees from scratch — core Lean
only, no external libraries — and discharges **every field of the
minimal `SetTheory` class** (`Lech/SetTheory/Core.lean`) on the
quotient type `V₀`, *except* the universe chain, which stays a
parameter (`UnivChain`).  The headline:

> **The residual assumption of the entire development is that the pSet
> model over `Type u` contains a strictly increasing ω-chain of Tarski
> universes** — precisely the ω-many-inaccessibles hypothesis of Mario
> Carneiro's consistency analysis (*The Type Theory of Lean*, master's
> thesis, Carnegie Mellon University, 2019; the `OmegaInaccessibles`
> form: `∃ κ : ℕ → Cardinal, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible`).

The correspondence: under that hypothesis, `univChain n` is realized by
the universe of `V_{κ n}`-ranked encodings — the trees whose
hereditary branching is bounded by the `n`-th inaccessible (there is no
need to formalize cardinals here; the chain is simply a parameter of
`SetTheory.ofAczelChain`).

The construction is Aczel's sets-as-trees interpretation (P. Aczel,
*The type theoretic interpretation of constructive set theory*, 1978;
see also B. Werner, *Sets in types, types in sets*, 1997): a set is a
type-indexed family of sets (`PSet`), two trees are equal as sets when
each child of either has an extensionally equivalent child of the other
(`PSet.Equiv`), and `V₀` is the quotient.  Highlights:

* **Extensionality** is what the quotient is for: same members means
  equivalent representatives (`PSet.equiv_of_mem`), so `Quot.sound`
  closes `ext`.
* **Regularity** comes from the *structural* well-foundedness of the
  encoding: `∈`-induction on `V₀` (`mem_induction`) is just structural
  recursion along `PSet.mk` — no ordinal theory involved.
* **Replacement** (`image`) is validated for **arbitrary Lean
  functions** `V₀ → V₀`, which is exactly what the interface's
  Lean-level replacement scheme asks for — stronger than first-order
  replacement, which only quantifies over definable class functions.
  The Aczel model absorbs the difference through `Classical.choice`:
  to form the image of `⟦PSet.mk α f⟧` under `F : V₀ → V₀` we must
  re-index by *representatives*, choosing for each `a : α` a tree
  denoting `F ⟦f a⟧` (`Aczel.out`, via `Quotient.exists_rep`).  This is
  the analog of the `allDefinable` step in Mathlib's `ZFSet`
  development: with choice, every meta-level class function is
  "definable enough" to fall under replacement.  This retroactively
  justifies the interface's deviation from a first-order presentation
  (see the `Lech/SetTheory/Core.lean` module doc).
* `upair`, `sUnion`, `power` are the standard Aczel constructions;
  `power` re-indexes by `α → Prop` (classical subsets), the one place
  besides `image` where the ambient classical logic shows.

**This module is evidence about the interface, not part of the trusted
development**: nothing in the checker or the consistency path imports
it; it is only reachable from the root `Lech.lean` so that it builds
by default.  The closing `#print axioms` guard pins the assumption
footprint of `SetTheory.ofAczelChain` to Lean's three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Lech

universe u v

namespace Aczel

/-- Aczel's pre-sets: well-founded trees, a set as a `Type u`-indexed
family of sets.  The intended meaning of `mk α f` is `{f a | a : α}`. -/
inductive PSet : Type (u + 1) where
  | mk (α : Type u) (f : α → PSet)

namespace PSet

/-- The index type of a tree's children. -/
def Ty : PSet.{u} → Type u
  | mk α _ => α

/-- The children family of a tree. -/
def Fn : (x : PSet.{u}) → x.Ty → PSet.{u}
  | mk _ f => f

/-- Extensional equivalence: every child on either side has an
equivalent child on the other side. -/
def Equiv : PSet.{u} → PSet.{u} → Prop
  | mk _ f, mk _ g =>
      (∀ a, ∃ b, Equiv (f a) (g b)) ∧ (∀ b, ∃ a, Equiv (f a) (g b))

theorem equiv_mk {α β : Type u} {f : α → PSet.{u}} {g : β → PSet.{u}} :
    Equiv (mk α f) (mk β g) ↔
      ((∀ a, ∃ b, Equiv (f a) (g b)) ∧ (∀ b, ∃ a, Equiv (f a) (g b))) := by
  rw [Equiv]

theorem Equiv.refl : ∀ x : PSet.{u}, Equiv x x
  | mk _ f =>
      equiv_mk.mpr
        ⟨fun a => ⟨a, Equiv.refl (f a)⟩, fun a => ⟨a, Equiv.refl (f a)⟩⟩

theorem Equiv.symm : ∀ {x y : PSet.{u}}, Equiv x y → Equiv y x
  | mk _ _f, mk _ _g, h =>
    let ⟨h₁, h₂⟩ := equiv_mk.mp h
    equiv_mk.mpr
      ⟨fun b => let ⟨a, ha⟩ := h₂ b; ⟨a, Equiv.symm ha⟩,
       fun a => let ⟨b, hb⟩ := h₁ a; ⟨b, Equiv.symm hb⟩⟩

theorem Equiv.trans : ∀ {x y z : PSet.{u}}, Equiv x y → Equiv y z → Equiv x z
  | mk _ _f, mk _ _g, mk _ _, hxy, hyz =>
    let ⟨p₁, p₂⟩ := equiv_mk.mp hxy
    let ⟨q₁, q₂⟩ := equiv_mk.mp hyz
    equiv_mk.mpr
      ⟨fun a =>
        let ⟨b, hb⟩ := p₁ a
        let ⟨c, hc⟩ := q₁ b
        ⟨c, Equiv.trans hb hc⟩,
       fun c =>
        let ⟨b, hb⟩ := q₂ c
        let ⟨a, ha⟩ := p₂ b
        ⟨a, Equiv.trans ha hb⟩⟩

/-- Extensional equivalence is an equivalence relation; `V₀` is the
quotient by this setoid. -/
instance setoid : Setoid PSet.{u} :=
  ⟨Equiv, ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩⟩

/-- Membership on pre-sets: `x` is equivalent to some child of `y`. -/
protected def Mem (x y : PSet.{u}) : Prop := ∃ b, Equiv x (y.Fn b)

theorem mem_mk {x : PSet.{u}} {β : Type u} {g : β → PSet.{u}} :
    PSet.Mem x (mk β g) ↔ ∃ b, Equiv x (g b) := Iff.rfl

theorem Mem.congr_left {x x' y : PSet.{u}} (h : Equiv x x') :
    PSet.Mem x y ↔ PSet.Mem x' y :=
  ⟨fun ⟨b, hb⟩ => ⟨b, h.symm.trans hb⟩, fun ⟨b, hb⟩ => ⟨b, h.trans hb⟩⟩

theorem Mem.congr_right {y y' : PSet.{u}} (h : Equiv y y') {x : PSet.{u}} :
    PSet.Mem x y ↔ PSet.Mem x y' := by
  cases y with | mk β g =>
  cases y' with | mk β' g' =>
  obtain ⟨h₁, h₂⟩ := equiv_mk.mp h
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb'⟩ := h₁ b
    exact ⟨b', hb.trans hb'⟩
  · rintro ⟨b', hb'⟩
    obtain ⟨b, hb⟩ := h₂ b'
    exact ⟨b, hb'.trans hb.symm⟩

/-- The converse of extensionality at the pre-set level: same members
(up to `Equiv`) means equivalent.  This is what discharges `ext` on the
quotient. -/
theorem equiv_of_mem : ∀ {x y : PSet.{u}},
    (∀ z, PSet.Mem z x ↔ PSet.Mem z y) → Equiv x y
  | mk _ f, mk _ g, h =>
    equiv_mk.mpr
      ⟨fun a => (h (f a)).mp ⟨a, Equiv.refl (f a)⟩,
       fun b =>
        let ⟨a, ha⟩ := (h (g b)).mpr ⟨b, Equiv.refl (g b)⟩
        ⟨a, ha.symm⟩⟩

/-! ### The pre-set constructions: pair, union, power set -/

/-- The unordered pair `{x, y}`, indexed by (the `u`-lift of) `Bool`. -/
protected def upair (x y : PSet.{u}) : PSet.{u} :=
  mk (ULift Bool) fun b => cond b.down x y

theorem mem_upair {z x y : PSet.{u}} :
    PSet.Mem z (PSet.upair x y) ↔ Equiv z x ∨ Equiv z y := by
  constructor
  · rintro ⟨⟨b⟩, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    · exact ⟨⟨true⟩, h⟩
    · exact ⟨⟨false⟩, h⟩

theorem upair_congr {x x' y y' : PSet.{u}} (hx : Equiv x x') (hy : Equiv y y') :
    Equiv (PSet.upair x y) (PSet.upair x' y') :=
  equiv_of_mem fun z => by
    rw [mem_upair, mem_upair]
    exact ⟨fun h => h.imp (·.trans hx) (·.trans hy),
           fun h => h.imp (·.trans hx.symm) (·.trans hy.symm)⟩

/-- The union of the members: children of children, indexed by the
dependent sum of the index types. -/
protected def sUnion : PSet.{u} → PSet.{u}
  | mk α f => mk (Σ a : α, (f a).Ty) fun p => (f p.1).Fn p.2

theorem mem_sUnion {z x : PSet.{u}} :
    PSet.Mem z x.sUnion ↔ ∃ y, PSet.Mem y x ∧ PSet.Mem z y := by
  cases x with | mk α f =>
  constructor
  · rintro ⟨⟨a, b⟩, hb⟩
    exact ⟨f a, ⟨a, Equiv.refl (f a)⟩, ⟨b, hb⟩⟩
  · rintro ⟨y, ⟨a, ha⟩, hz⟩
    obtain ⟨b, hb⟩ := (Mem.congr_right ha).mp hz
    exact ⟨⟨a, b⟩, hb⟩

theorem sUnion_congr {x x' : PSet.{u}} (h : Equiv x x') :
    Equiv x.sUnion x'.sUnion :=
  equiv_of_mem fun z => by
    rw [mem_sUnion, mem_sUnion]
    exact ⟨fun ⟨y, hy, hz⟩ => ⟨y, (Mem.congr_right h).mp hy, hz⟩,
           fun ⟨y, hy, hz⟩ => ⟨y, (Mem.congr_right h).mpr hy, hz⟩⟩

/-- The power set: subsets of `mk α f` are re-indexed by predicates
`α → Prop` — the classical reading of "subset", the trick that makes
the Aczel `power` work with `propext`/`Classical.choice` in the
ambient logic. -/
protected def power : PSet.{u} → PSet.{u}
  | mk α f => mk (α → Prop) fun p => mk { a : α // p a } fun a => f a.1

theorem mem_power {z x : PSet.{u}} :
    PSet.Mem z x.power ↔ ∀ w, PSet.Mem w z → PSet.Mem w x := by
  cases x with | mk α f =>
  constructor
  · rintro ⟨p, hp⟩ w hw
    obtain ⟨⟨a, _⟩, ha⟩ := (Mem.congr_right hp).mp hw
    exact ⟨a, ha⟩
  · intro h
    cases z with | mk β g =>
    refine ⟨fun a => ∃ b, Equiv (g b) (f a), equiv_mk.mpr ⟨?_, ?_⟩⟩
    · intro b
      obtain ⟨a, ha⟩ := h (g b) ⟨b, Equiv.refl (g b)⟩
      exact ⟨⟨a, b, ha⟩, ha⟩
    · rintro ⟨a, b, hb⟩
      exact ⟨b, hb⟩

theorem power_congr {x x' : PSet.{u}} (h : Equiv x x') :
    Equiv x.power x'.power :=
  equiv_of_mem fun z => by
    rw [mem_power, mem_power]
    exact ⟨fun hz w hw => (Mem.congr_right h).mp (hz w hw),
           fun hz w hw => (Mem.congr_right h).mpr (hz w hw)⟩

end PSet

/-! ### The quotient `V₀` and its membership -/

/-- The Aczel universe: pre-set trees up to extensional equivalence. -/
def V₀ : Type (u + 1) := Quotient PSet.setoid.{u}

/-- The class of a tree in `V₀`. -/
def mkV (s : PSet.{u}) : V₀.{u} := Quotient.mk PSet.setoid s

@[inherit_doc] scoped notation:max "⟦" s "⟧" => Aczel.mkV s

theorem sound {s t : PSet.{u}} (h : PSet.Equiv s t) : ⟦s⟧ = ⟦t⟧ :=
  Quotient.sound h

theorem exact {s t : PSet.{u}} (h : ⟦s⟧ = ⟦t⟧) : PSet.Equiv s t :=
  Quotient.exact h

/-- Membership on the quotient (`PSet.Mem` respects `Equiv` on both
sides; `propext` turns the two `Iff`s into the `Prop`-valued equality
`Quotient.lift₂` asks for). -/
def AczelMem : V₀.{u} → V₀.{u} → Prop :=
  Quotient.lift₂ PSet.Mem fun _ _ _ _ hx hy =>
    propext ((PSet.Mem.congr_left hx).trans (PSet.Mem.congr_right hy))

/-- Members of a quotiented tree are exactly the classes of its
children. -/
theorem mem_mk {z : V₀.{u}} {β : Type u} {g : β → PSet.{u}} :
    AczelMem z ⟦PSet.mk β g⟧ ↔ ∃ b, z = ⟦g b⟧ := by
  induction z using Quotient.inductionOn with
  | _ s =>
    exact ⟨fun ⟨b, hb⟩ => ⟨b, Aczel.sound hb⟩,
           fun ⟨b, hb⟩ => ⟨b, Aczel.exact hb⟩⟩

/-- Extensionality — the field the quotient exists for. -/
theorem ext {x y : V₀.{u}} (h : ∀ z, AczelMem z x ↔ AczelMem z y) : x = y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ s t => exact Quotient.sound (PSet.equiv_of_mem fun z => h ⟦z⟧)

/-! ### Pairing, union, power set on `V₀` -/

/-- The unordered pair. -/
def upair : V₀.{u} → V₀.{u} → V₀.{u} :=
  Quotient.lift₂ (fun x y => ⟦PSet.upair x y⟧) fun _ _ _ _ hx hy =>
    Quotient.sound (PSet.upair_congr hx hy)

theorem mem_upair {z x y : V₀.{u}} :
    AczelMem z (upair x y) ↔ z = x ∨ z = y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ s t =>
    induction z using Quotient.inductionOn with
    | _ w =>
      exact ⟨fun h => (PSet.mem_upair.mp h).imp Aczel.sound Aczel.sound,
             fun h => PSet.mem_upair.mpr (h.imp Aczel.exact Aczel.exact)⟩

/-- The union of the members. -/
def sUnion : V₀.{u} → V₀.{u} :=
  Quotient.lift (fun x => ⟦x.sUnion⟧) fun _ _ h =>
    Quotient.sound (PSet.sUnion_congr h)

theorem mem_sUnion {z x : V₀.{u}} :
    AczelMem z (sUnion x) ↔ ∃ y, AczelMem y x ∧ AczelMem z y := by
  induction x, z using Quotient.inductionOn₂ with
  | _ s t =>
    constructor
    · intro h
      obtain ⟨y, hy, hz⟩ := PSet.mem_sUnion.mp h
      exact ⟨⟦y⟧, hy, hz⟩
    · rintro ⟨y, hy, hz⟩
      induction y using Quotient.inductionOn with
      | _ w => exact PSet.mem_sUnion.mpr ⟨w, hy, hz⟩

/-- The power set. -/
def power : V₀.{u} → V₀.{u} :=
  Quotient.lift (fun x => ⟦x.power⟧) fun _ _ h =>
    Quotient.sound (PSet.power_congr h)

theorem mem_power {z x : V₀.{u}} :
    AczelMem z (power x) ↔ ∀ w, AczelMem w z → AczelMem w x := by
  induction x, z using Quotient.inductionOn₂ with
  | _ s t =>
    constructor
    · intro h w hw
      induction w using Quotient.inductionOn with
      | _ v => exact PSet.mem_power.mp h v hw
    · intro h
      exact PSet.mem_power.mpr fun w hw => h ⟦w⟧ hw

/-! ### Regularity, from structural well-foundedness -/

/-- `∈`-induction on `V₀`: the encoding is well-founded *by
construction*, so `∈`-induction is plain structural recursion along
`PSet.mk` — no ordinal theory, no rank. -/
theorem mem_induction {P : V₀.{u} → Prop}
    (h : ∀ x, (∀ y, AczelMem y x → P y) → P x) : ∀ x, P x := by
  have aux : ∀ s : PSet.{u}, P ⟦s⟧ := by
    intro s
    induction s with
    | mk α f ih =>
      refine h _ fun y hy => ?_
      obtain ⟨b, rfl⟩ := mem_mk.mp hy
      exact ih b
  intro x
  induction x using Quotient.inductionOn with
  | _ s => exact aux s

/-- Regularity: every nonempty set has an `∈`-minimal member.
Classically contraposed through `mem_induction`: if no member of `x`
were minimal, `∈`-induction would show every set avoids `x`. -/
theorem regularity (x : V₀.{u}) (h : ∃ y, AczelMem y x) :
    ∃ y, AczelMem y x ∧ ¬ ∃ z, AczelMem z y ∧ AczelMem z x := by
  refine Classical.byContradiction fun hn => ?_
  have key : ∀ y : V₀.{u}, ¬ AczelMem y x :=
    mem_induction fun y ih hyx =>
      have ⟨z, hzy, hzx⟩ :=
        Classical.byContradiction fun hno => hn ⟨y, hyx, hno⟩
      ih z hzy hzx
  obtain ⟨y, hy⟩ := h
  exact key y hy

/-! ### Replacement over arbitrary Lean functions -/

/-- A choice of representative (`Quotient.exists_rep` +
`Classical.choose`).  This is the engine of `image`: replacement over
an *arbitrary* `F : V₀ → V₀` needs, for each child `f a` of the
representative tree, some tree denoting `F ⟦f a⟧` — the analog of
Mathlib's `allDefinable` step (with choice, every meta-level class
function falls under replacement). -/
noncomputable def out (x : V₀.{u}) : PSet.{u} :=
  Classical.choose (Quotient.exists_rep x)

theorem out_eq (x : V₀.{u}) : ⟦out x⟧ = x :=
  Classical.choose_spec (Quotient.exists_rep x)

theorem out_equiv_of_eq {x y : V₀.{u}} (h : x = y) :
    PSet.Equiv (out x) (out y) :=
  Aczel.exact (by rw [out_eq, out_eq, h])

/-- Replacement, as a Lean-level scheme: the image of a set under an
arbitrary function `V₀ → V₀`.  Noncomputable — the re-indexing by
representatives goes through `out`. -/
noncomputable def image (F : V₀.{u} → V₀.{u}) : V₀.{u} → V₀.{u} :=
  Quotient.lift (fun s => ⟦PSet.mk s.Ty fun a => out (F ⟦s.Fn a⟧)⟧)
    fun s t h => Quotient.sound <| by
      cases s with | mk α f =>
      cases t with | mk β g =>
      obtain ⟨h₁, h₂⟩ := PSet.equiv_mk.mp h
      refine PSet.equiv_mk.mpr ⟨?_, ?_⟩
      · intro a
        obtain ⟨b, hb⟩ := h₁ a
        exact ⟨b, out_equiv_of_eq (congrArg F (Aczel.sound hb))⟩
      · intro b
        obtain ⟨a, ha⟩ := h₂ b
        exact ⟨a, out_equiv_of_eq (congrArg F (Aczel.sound ha))⟩

theorem mem_image {F : V₀.{u} → V₀.{u}} {x z : V₀.{u}} :
    AczelMem z (image F x) ↔ ∃ w, AczelMem w x ∧ z = F w := by
  induction x using Quotient.inductionOn with
  | _ s =>
    cases s with | mk α f =>
    constructor
    · intro h
      obtain ⟨a, rfl⟩ := mem_mk.mp h
      exact ⟨⟦f a⟧, mem_mk.mpr ⟨a, rfl⟩, out_eq _⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, rfl⟩ := mem_mk.mp hw
      exact mem_mk.mpr ⟨a, (out_eq _).symm⟩

end Aczel

/-! ### The residual assumption, bundled -/

/-- A strictly increasing ω-chain of Grothendieck universes over an
arbitrary membership relation — the universe-chain fields of the
`SetTheory` core, detached from the class so they can stay a
*parameter* of the Aczel realization.  For the pSet model this is
precisely the ω-many-inaccessibles hypothesis of Mario Carneiro's
consistency analysis (op. cit. in the module doc): `univChain n` is
realized by the universe of `V_{κ n}`-ranked encodings. -/
structure UnivChain (V : Type v) (Mem : V → V → Prop) where
  /-- The chain of universes. -/
  univChain : Nat → V
  /-- The chain increases strictly: each universe is a member of the
  next. -/
  univChain_mem : ∀ n, Mem (univChain n) (univChain (n + 1))
  /-- Each chain member is a Grothendieck universe (Tarski's Axiom A
  matrix with transitivity, `IsTGUniverse`). -/
  univChain_tg : ∀ n, IsTGUniverse Mem (univChain n)

open Aczel in
set_option warn.classDefReducibility false in
/-- The Aczel realization of the `SetTheory` core: every set-theoretic
field is *discharged* on `V₀`; only the universe chain is assumed.  So
the residual assumption of the entire development is: **the pSet model
over `Type u` contains a strictly increasing ω-chain of Tarski
universes** (see the module doc for the correspondence with Carneiro's
`OmegaInaccessibles`). -/
noncomputable def SetTheory.ofAczelChain (c : UnivChain V₀.{u} AczelMem) :
    SetTheory V₀.{u} where
  Mem := AczelMem
  ext := Aczel.ext
  upair := Aczel.upair
  mem_upair := Aczel.mem_upair
  sUnion := Aczel.sUnion
  mem_sUnion := Aczel.mem_sUnion
  power := Aczel.power
  mem_power := Aczel.mem_power
  regularity := Aczel.regularity
  image := Aczel.image
  mem_image := Aczel.mem_image
  univChain := c.univChain
  univChain_mem := c.univChain_mem
  univChain_tg := c.univChain_tg

/--
info: 'Lech.SetTheory.ofAczelChain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SetTheory.ofAczelChain

end Lech
