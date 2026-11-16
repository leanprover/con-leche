module

public import Fragment.Level

@[expose] public section

/-!
# The set-theoretic library

Everything the fragment's proof uses of set theory, stated
declaratively as ONE class: sets and membership with extensionality
and separation, a point `pt` with its singleton, dependent function
spaces with graphs and application and their β/η/extensionality laws,
a universe chain with its closure laws, and three laws of the point
(it is not a truth value, it has at most one member, no graph is its
member; true of `pt := {{∅}}`).  There is no construction here, and
nothing beyond these laws is used — every theorem of the fragment is
proved against the class.

The truth values are not laws but an abbreviation: a proposition `P`
denotes `truthVal P`, the members of `{pt}` that satisfy `P` — the
singleton if `P` holds, empty if not — and its membership law is a
theorem of separation.

Con-leche derives all of this from a much smaller axiomatic core
(`ConLeche/SetTheory/Core.lean`: ZF⁻ plus an ω-chain of Grothendieck
universes; `ConLeche/SetTheory/Derive/*` builds the operators).  The
fragment takes the derived surface as its interface, which is what the
proof reads anyway.

Below the class, the **two-regime operators** `piR`/`lamR` of
`ConLeche/SetModel/Ops.lean`: the function space and abstraction at
a `Bool` saying whether the body is a proposition — a truth value and
the one proof when it is, a graph space and a graph when it is not.

Then the **universes of types** (`typeU`): what a sort denotes — the
truth values at `0`, above it the members of the universe that are
**types** (truth values, or sets neither the point nor containing it).
The universe chain `univ` sizes things; `typeU` is what the typing
reads.

Last, the **value-driven regimes** `piV`/`lamV` (task #344), which the
interpretation applies at every binder: the regime is read off the
values — a function space is propositional exactly when every fibre is
a truth value, an abstraction is the point exactly when every body value
is.  Over an empty domain both read "proposition": the function space is
`{pt}` and the abstraction the point, whatever the body's sort; that
`{pt}` is then a member of the positive sorts too is why `typeU (n+1)`
admits the truth values.
-/

namespace Fragment

universe u

/-- **The set theory we assume.**  A type of sets `V` with the
operators and laws the fragment's proof uses.  The theory is stated in
Lean's logic, so separation is available for every predicate of that
logic, and the function-space laws quantify over functions on the
sets. -/
class SetLib (V : Type u) where
  /-- Membership. -/
  Mem : V → V → Prop
  /-- Extensionality. -/
  ext : ∀ {x y : V}, (∀ z, Mem z x ↔ Mem z y) → x = y
  /-- Separation: the members of `A` that satisfy `P`. -/
  sep : V → (V → Prop) → V
  /-- The members of a separation. -/
  mem_sep : ∀ {A : V} {P : V → Prop} {z : V}, Mem z (sep A P) ↔ Mem z A ∧ P z
  /-- A distinguished set, subject to the point's three laws below.  It
  is the one proof of every true proposition. -/
  pt : V
  /-- The one-element set `{pt}`. -/
  one : V
  /-- The members of `{pt}`. -/
  mem_one : ∀ {z : V}, Mem z one ↔ z = pt
  /-- The universe chain: `univ n` sizes `Sort n`, which denotes the
  types among its members, `typeU n`. -/
  univ : Nat → V
  /-- `univ 0` is the set of subsets of `{pt}` — the truth values. -/
  mem_univ_zero : ∀ {T : V}, Mem T (univ 0) ↔ ∀ z, Mem z T → z = pt
  /-- Each universe is a member of the next. -/
  univ_mem_succ : ∀ n : Nat, Mem (univ n) (univ (n + 1))
  /-- Cumulativity. -/
  univ_mono : ∀ {m n : Nat} {x : V}, m ≤ n → Mem x (univ m) → Mem x (univ n)
  /-- The graph of a function on a domain. -/
  graph : (V → V) → V → V
  /-- The dependent function space: the graphs over `A` with values
  in the fibres `B`. -/
  piSet : V → (V → V) → V
  /-- Application.  On the point it is the point (a proof applied to
  anything is a proof); on a graph it reads the graph. -/
  app : V → V → V
  /-- A proof applied is the proof. -/
  app_pt : ∀ a : V, app pt a = pt
  /-- β: a graph applied on its domain computes. -/
  app_graph : ∀ {F : V → V} {A a : V}, Mem a A → app (graph F A) a = F a
  /-- A graph is never the point. -/
  graph_ne_pt : ∀ {F : V → V} {A : V}, graph F A ≠ pt
  /-- A graph depends only on the function's values on the domain. -/
  graph_congr : ∀ {F F' : V → V} {A : V}, (∀ x, Mem x A → F x = F' x) → graph F A = graph F' A
  /-- A function space depends only on the fibres over the domain. -/
  piSet_congr : ∀ {A : V} {B B' : V → V}, (∀ x, Mem x A → B x = B' x) → piSet A B = piSet A B'
  /-- Introduction: fibre-wise members abstract into the space. -/
  graph_mem_piSet : ∀ {A : V} {F B : V → V},
    (∀ x, Mem x A → Mem (F x) (B x)) → Mem (graph F A) (piSet A B)
  /-- Elimination. -/
  app_mem_piSet : ∀ {A f a : V} {B : V → V}, Mem f (piSet A B) → Mem a A → Mem (app f a) (B a)
  /-- η: a member of a function space is the graph of its applications. -/
  graph_app_eq : ∀ {A f : V} {B : V → V}, Mem f (piSet A B) → graph (fun x => app f x) A = f
  /-- A graph determines its domain. -/
  graph_dom_unique : ∀ {F F' : V → V} {A A' : V}, graph F A = graph F' A' → A = A'
  /-- Closure of the positive universes under dependent function
  spaces. -/
  piSet_mem_univ : ∀ {n : Nat} {A : V} {B : V → V}, n ≠ 0 →
    Mem A (univ n) → (∀ x, Mem x A → Mem (B x) (univ n)) → Mem (piSet A B) (univ n)
  /-- Closure of the universes under separation. -/
  sep_mem_univ : ∀ {n : Nat} {A : V} {P : V → Prop}, Mem A (univ n) → Mem (sep A P) (univ n)
  /-- **The point's laws** (1): the point is not a truth value — it has
  a member other than itself. -/
  pt_not_mem_univ_zero : ¬ Mem pt (univ 0)
  /-- (2): the point has at most one member. -/
  pt_subsingleton : ∀ {x y : V}, Mem x pt → Mem y pt → x = y
  /-- (3): no graph is a member of the point. -/
  graph_not_mem_pt : ∀ {F : V → V} {A : V}, ¬ Mem (graph F A) pt

namespace SetLib

@[inherit_doc] scoped infix:50 " ∈ˢ " => Mem

variable {V : Type u} [SetLib V]

theorem mem_sep_of {A : V} {P : V → Prop} {x : V} (hx : x ∈ˢ A) (hp : P x) : x ∈ˢ sep A P :=
  mem_sep.mpr ⟨hx, hp⟩

/-! ## Truth values

An abbreviation, not a law: the truth value of a proposition is the
separation of `{pt}` by it. -/

/-- The truth value of a proposition: `{pt}` if it holds, `∅` if
not. -/
def truthVal (P : Prop) : V := sep one (fun _ => P)

/-- The members of a truth value. -/
theorem mem_truthVal {p : Prop} {z : V} : z ∈ˢ truthVal p ↔ z = pt ∧ p := by
  unfold truthVal; rw [mem_sep, mem_one]

theorem pt_mem_truthVal {p : Prop} (hp : p) : (pt : V) ∈ˢ truthVal p :=
  mem_truthVal.mpr ⟨rfl, hp⟩

theorem of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ truthVal p) : p :=
  (mem_truthVal.mp hz).2

theorem eq_pt_of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ truthVal p) : z = pt :=
  (mem_truthVal.mp hz).1

theorem truthVal_mem_univ_zero (p : Prop) : (truthVal p : V) ∈ˢ univ 0 :=
  mem_univ_zero.mpr fun _ hz => eq_pt_of_mem_truthVal hz

theorem eq_pt_of_mem_univ_zero {T x : V} (hT : T ∈ˢ univ 0) (hx : x ∈ˢ T) : x = pt :=
  mem_univ_zero.mp hT x hx

/-- An inhabited truth value is `{pt}`. -/
theorem eq_one_of_mem_univ_zero {T x : V} (hT : T ∈ˢ univ 0) (hx : x ∈ˢ T) : T = one :=
  ext fun z => ⟨fun hz => mem_one.mpr (eq_pt_of_mem_univ_zero hT hz),
    fun hz => by rw [mem_one.mp hz, ← eq_pt_of_mem_univ_zero hT hx]; exact hx⟩

theorem one_mem_univ_zero : (one : V) ∈ˢ univ 0 :=
  mem_univ_zero.mpr fun _ hz => mem_one.mp hz

theorem truthVal_congr {p q : Prop} (h : p ↔ q) : (truthVal p : V) = truthVal q :=
  ext fun z => by rw [mem_truthVal, mem_truthVal, h]

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) : f ≠ pt := by
  rw [← graph_app_eq hf]; exact graph_ne_pt

/-- **Domain uniqueness** for function spaces: a member of two function
spaces is one graph (η), and a graph determines its domain. -/
theorem piSet_dom_unique {A A' f : V} {B B' : V → V}
    (h1 : f ∈ˢ piSet A B) (h2 : f ∈ˢ piSet A' B') : A = A' :=
  graph_dom_unique ((graph_app_eq h1).trans (graph_app_eq h2).symm)

/-! ## The two regimes

`piR`/`lamR` read a `Bool` — "is the body a proposition here?" — and
nothing else; the interpretation computes it from the values
(`piV`/`lamV`, below). -/

/-- **The propositional function space** `Π₀(A, B)`: the truth value "every
fibre is `{pt}`".  When the fibres are truth values it is their
intersection `⋂ x ∈ A, B x` (the empty intersection being `{pt}`):
`{pt}` exactly when every fibre is, `∅` otherwise — the function space of
subsets of a singleton.  Reducible, so proofs that unfold `piR true`
keep working. -/
abbrev piProp (A : V) (B : V → V) : V := truthVal (∀ x, x ∈ˢ A → B x = one)

/-- The function space at regime `p`: the propositional function space
when `p`, the graph space above it. -/
def piR (p : Bool) (A : V) (B : V → V) : V :=
  if p then piProp A B else piSet A B

/-- Abstraction at regime `p`: the point when `p`, the graph above it. -/
def lamR (p : Bool) (A : V) (F : V → V) : V :=
  if p then pt else graph F A

theorem piR_true {A : V} {B : V → V} :
    piR true A B = truthVal (∀ x, x ∈ˢ A → B x = one) := rfl
theorem piR_false {A : V} {B : V → V} : piR false A B = piSet A B := rfl
theorem lamR_true {A : V} {F : V → V} : lamR true A F = (pt : V) := rfl
theorem lamR_false {A : V} {F : V → V} : lamR false A F = graph F A := rfl

theorem piR_congr {p : Bool} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piR p A B = piR p A B' := by
  cases p
  · exact piSet_congr h
  · exact truthVal_congr
      ⟨fun hi x hx => (h x hx).symm.trans (hi x hx), fun hi x hx => (h x hx).trans (hi x hx)⟩

theorem lamR_congr {p : Bool} {A : V} {F F' : V → V}
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR p A F = lamR p A F' := by
  cases p
  · exact graph_congr h
  · rfl

/-- Introduction: fibre-wise members abstract into the function space.  The
fibre premise is used only at a proposition, where the fibres must be
truth values for the inhabited ones to be `{pt}`. -/
theorem lamR_mem {p : Bool} {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB : p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) : lamR p A F ∈ˢ piR p A B := by
  cases p
  · exact graph_mem_piSet hF
  · exact pt_mem_truthVal fun x hx => eq_one_of_mem_univ_zero (hB rfl x hx) (hF x hx)

/-- **Proof irrelevance at function spaces**: an inhabitant of a
propositional function space is the point. -/
theorem eq_pt_of_mem_piR_true {A f : V} {B : V → V} (hf : f ∈ˢ piR true A B) :
    f = pt := eq_pt_of_mem_truthVal hf

/-- Elimination.  At a proposition the member is the point and the
fibre is `{pt}`: no premise on the fibres is needed. -/
theorem app_mem_piR {p : Bool} {A f a : V} {B : V → V}
    (hf : f ∈ˢ piR p A B) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  cases p
  · exact app_mem_piSet hf ha
  · rw [eq_pt_of_mem_piR_true hf, app_pt, of_mem_truthVal hf a ha]
    exact mem_one.mpr rfl

/-- β, conditional on domain membership. -/
theorem app_lamR {p : Bool} {A a : V} {F B : V → V}
    (ha : a ∈ˢ A) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB : p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
    app (lamR p A F) a = F a := by
  cases p
  · exact app_graph ha
  · rw [lamR_true, app_pt]
    exact (eq_pt_of_mem_univ_zero (hB rfl a ha) (hF a ha)).symm

/-- **β in the graph regime**: no typing premise whatsoever. -/
theorem app_lamR_false {A a : V} {F : V → V} (ha : a ∈ˢ A) :
    app (lamR false A F) a = F a := app_graph ha

/-- A graph-regime abstraction is never the point. -/
theorem lamR_false_ne_pt {A : V} {F : V → V} : lamR false A F ≠ (pt : V) := graph_ne_pt

/-- η: a member of a function space is the abstraction of its applications. -/
theorem lamR_eta {p : Bool} {A f : V} {B : V → V} (hf : f ∈ˢ piR p A B) :
    lamR p A (fun x => app f x) = f := by
  cases p
  · exact graph_app_eq hf
  · rw [lamR_true, eq_pt_of_mem_piR_true hf]

/-- **Impredicativity**: a function space landing in `Prop` is a truth value,
whatever its domain. -/
theorem piR_true_mem_univ_zero {A : V} {B : V → V} :
    piR true A B ∈ˢ (univ 0 : V) := truthVal_mem_univ_zero _

/-- The graph regime's universe membership. -/
theorem piR_false_mem_univ {n : Nat} {A : V} {B : V → V} (hn : n ≠ 0)
    (hA : A ∈ˢ univ n) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ n) :
    piR false A B ∈ˢ (univ n : V) := piSet_mem_univ hn hA hB

/-! ## The universes of types

`univ` sizes things; what a sort *denotes* is `typeU`: `Sort 0` the
truth values, `Sort (n+1)` the members of `univ (n+1)` that are
**types**.  A type is a truth value or a **strict** set (not the point,
and the point not a member); its members are all the point (a truth
value) or none of them (a strict set) — `IsTy.eq_of_ne_pt`, which is
what the soundness proof reads.  The point itself is no type, so no
sort holds it (the stored `c : Sort 1` of `UniformBeta.lean`, whose
value is the point, has no model).  A positive sort holds the truth
values as well (task #344): a function space over an empty domain is `{pt}`
whatever its body's sort. -/

/-- A **strict** set: not the point, and the point is not a member. -/
def Strict (X : V) : Prop := X ≠ pt ∧ ¬ pt ∈ˢ X

/-- A **type**: a truth value, or a strict set. -/
def IsTy (X : V) : Prop := X ∈ˢ univ 0 ∨ Strict X

/-- **What `Sort n` denotes**: the truth values at `0`, the members of
`univ n` that are types above. -/
def typeU (n : Nat) : V := if n = 0 then univ 0 else sep (univ n) IsTy

/-- The regime of a fibre: a truth value at a proposition, strict above. -/
def Fib : Bool → V → Prop
  | true, X => X ∈ˢ univ 0
  | false, X => Strict X

@[simp] theorem Fib_true {X : V} : Fib true X ↔ X ∈ˢ univ 0 := Iff.rfl
@[simp] theorem Fib_false {X : V} : Fib false X ↔ Strict X := Iff.rfl

theorem ne_pt_of_mem_univ_zero {T : V} (h : T ∈ˢ univ 0) : T ≠ pt := by
  rintro rfl; exact pt_not_mem_univ_zero h

theorem IsTy.ne_pt {T : V} (h : IsTy T) : T ≠ pt := by
  rcases h with h | h
  · exact ne_pt_of_mem_univ_zero h
  · exact h.1

theorem IsTy_of_Fib {p : Bool} {X : V} (h : Fib p X) : IsTy X := by
  cases p
  · exact Or.inr h
  · exact Or.inl h

theorem Fib.ne_pt {p : Bool} {X : V} (h : Fib p X) : X ≠ pt := (IsTy_of_Fib h).ne_pt

theorem mem_typeU_zero {T : V} : T ∈ˢ typeU 0 ↔ T ∈ˢ univ 0 := by
  simp [typeU]

theorem mem_typeU_pos {n : Nat} (hn : n ≠ 0) {T : V} :
    T ∈ˢ typeU n ↔ T ∈ˢ univ n ∧ IsTy T := by
  simp only [typeU, hn, ↓reduceIte]
  exact mem_sep

theorem mem_univ_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) : T ∈ˢ univ n := by
  by_cases hn : n = 0
  · subst hn; exact mem_typeU_zero.mp h
  · exact ((mem_typeU_pos hn).mp h).1

theorem IsTy_of_mem_typeU {n : Nat} {T : V} (h : T ∈ˢ typeU n) : IsTy T := by
  by_cases hn : n = 0
  · subst hn; exact Or.inl (mem_typeU_zero.mp h)
  · exact ((mem_typeU_pos hn).mp h).2

/-- A strict member of `univ n`, `n` positive, is a member of
`typeU n`. -/
theorem mem_typeU_of_strict {n : Nat} (hn : n ≠ 0) {T : V} (hT : T ∈ˢ univ n)
    (hs : Strict T) : T ∈ˢ typeU n :=
  (mem_typeU_pos hn).mpr ⟨hT, Or.inr hs⟩

/-- **(P)**: a member of a strict set is not the point. -/
theorem ne_pt_of_mem_strict {T x : V} (hT : Strict T) (hx : x ∈ˢ T) : x ≠ pt := by
  rintro rfl; exact hT.2 hx

/-- The members of a type are all the point or none of them. -/
theorem IsTy.eq_of_ne_pt {T x y : V} (hT : IsTy T) (hx : x ∈ˢ T) (hy : y ∈ˢ T)
    (h : x ≠ pt → y ≠ pt → x = y) : x = y := by
  rcases hT with hT | hT
  · rw [eq_pt_of_mem_univ_zero hT hx, eq_pt_of_mem_univ_zero hT hy]
  · exact h (ne_pt_of_mem_strict hT hx) (ne_pt_of_mem_strict hT hy)

/-! ### The point's neighbours -/

theorem pt_ne_truthVal_false : (pt : V) ≠ truthVal False := by
  intro h
  apply pt_not_mem_univ_zero (V := V)
  rw [h]
  exact truthVal_mem_univ_zero False

theorem exists_mem_pt : ∃ z, z ∈ˢ (pt : V) :=
  Classical.byContradiction fun h => pt_ne_truthVal_false (ext fun z =>
    ⟨fun hz => absurd ⟨z, hz⟩ h, fun hz => absurd (of_mem_truthVal hz) id⟩)

theorem ne_pt_of_two {X a b : V} (ha : a ∈ˢ X) (hb : b ∈ˢ X) (hab : a ≠ b) : X ≠ pt := by
  rintro rfl; exact hab (pt_subsingleton ha hb)

theorem one_ne_truthVal_false : (one : V) ≠ truthVal False := by
  intro h
  have : (pt : V) ∈ˢ one := mem_one.mpr rfl
  rw [h] at this
  exact of_mem_truthVal this

theorem univ_zero_ne_pt : (univ 0 : V) ≠ pt :=
  ne_pt_of_two one_mem_univ_zero (truthVal_mem_univ_zero False) one_ne_truthVal_false

theorem strict_univ_zero : Strict (univ 0 : V) := ⟨univ_zero_ne_pt, pt_not_mem_univ_zero⟩

theorem strict_truthVal_false : Strict (truthVal False : V) :=
  ⟨pt_ne_truthVal_false.symm, fun h => of_mem_truthVal h⟩

/-- `Sort n` is strict. -/
theorem strict_typeU (n : Nat) : Strict (typeU n : V) := by
  by_cases hn : n = 0
  · subst hn; simpa [typeU] using strict_univ_zero
  · refine ⟨?_, fun h => ((mem_typeU_pos hn).mp h).2.ne_pt rfl⟩
    -- `typeU n` has two distinct members, the point at most one
    have h1 : (truthVal False : V) ∈ˢ typeU n :=
      (mem_typeU_pos hn).mpr ⟨univ_mono (Nat.zero_le n) (truthVal_mem_univ_zero False),
        Or.inr strict_truthVal_false⟩
    have h2 : (univ 0 : V) ∈ˢ typeU n :=
      (mem_typeU_pos hn).mpr ⟨univ_mono (by omega) (univ_mem_succ 0), Or.inr strict_univ_zero⟩
    refine ne_pt_of_two h1 h2 fun h => ?_
    have h3 : (one : V) ∈ˢ univ 0 := one_mem_univ_zero
    rw [← h] at h3
    exact of_mem_truthVal h3

theorem IsTy_typeU (n : Nat) : IsTy (typeU n : V) := Or.inr (strict_typeU n)

/-- `Sort n : Sort (n+1)`. -/
theorem typeU_mem_typeU_succ (n : Nat) : (typeU n : V) ∈ˢ typeU (n + 1) := by
  refine (mem_typeU_pos (Nat.succ_ne_zero n)).mpr ⟨?_, IsTy_typeU n⟩
  by_cases hn : n = 0
  · subst hn; simpa [typeU] using univ_mem_succ 0
  · simp only [typeU, hn, ↓reduceIte]
    exact sep_mem_univ (univ_mem_succ n)

/-- A function space is strict: its members are graphs, and the point's
member is not one. -/
theorem strict_piSet {A : V} {B : V → V} : Strict (piSet A B) := by
  refine ⟨?_, fun h => graph_ne_pt (graph_app_eq h)⟩
  intro he
  obtain ⟨z, hz⟩ := exists_mem_pt (V := V)
  have hz' : z ∈ˢ piSet A B := by rw [he]; exact hz
  have := graph_app_eq hz'
  rw [← this] at hz
  exact graph_not_mem_pt hz

theorem IsTy_piR {p : Bool} {A : V} {B : V → V} : IsTy (piR p A B) := by
  cases p
  · exact Or.inr strict_piSet
  · exact Or.inl piR_true_mem_univ_zero

theorem Fib_piR {p : Bool} {A : V} {B : V → V} : Fib p (piR p A B) := by
  cases p
  · exact strict_piSet
  · exact piR_true_mem_univ_zero

/-! ### What a value may be applied to

The semantic invariant's application clause, on values: the point may
be applied to anything (`app_pt`), a graph whose domain is a type to
the members of its domain (`app_graph`), and any other set to nothing.
It is well-defined, as a graph determines its domain
(`graph_dom_unique`). -/

/-- **`f` applies to `a`**: `f` is the point, or a graph whose domain is a
type holding `a`. -/
def AppliesTo (f a : V) : Prop :=
  f = pt ∨ ∃ (F : V → V) (A : V), f = graph F A ∧ IsTy A ∧ a ∈ˢ A

theorem appliesTo_pt (a : V) : AppliesTo (pt : V) a := Or.inl rfl

theorem appliesTo_graph {F : V → V} {A a : V} :
    AppliesTo (graph F A) a ↔ IsTy A ∧ a ∈ˢ A := by
  refine ⟨fun h => ?_, fun h => Or.inr ⟨F, A, rfl, h⟩⟩
  rcases h with h | ⟨F', A', he, h⟩
  · exact absurd h graph_ne_pt
  · exact graph_dom_unique he ▸ h

/-- A member of a function space whose domain is a type applies to the
members of the domain. -/
theorem appliesTo_of_mem_piSet {A f a : V} {B : V → V} (hf : f ∈ˢ piSet A B)
    (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo f a := by
  rw [← graph_app_eq hf]; exact appliesTo_graph.mpr ⟨hA, ha⟩

/-- The same at either regime: a member of a propositional function space
is the point. -/
theorem appliesTo_of_mem_piR {p : Bool} {A f a : V} {B : V → V} (hf : f ∈ˢ piR p A B)
    (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo f a := by
  cases p
  · exact appliesTo_of_mem_piSet hf hA ha
  · rw [eq_pt_of_mem_piR_true hf]; exact appliesTo_pt a

/-- A member of a function space that applies to `a`: the space's domain
is a type holding `a`. -/
theorem AppliesTo.dom {A f a : V} {B : V → V} (h : AppliesTo f a) (hf : f ∈ˢ piSet A B) :
    IsTy A ∧ a ∈ˢ A := by
  rw [← graph_app_eq hf] at h; exact appliesTo_graph.mp h

/-- A graph that applies to `a`, in a function space: the space's domain
holds `a`. -/
theorem AppliesTo.mem {A f a : V} {B : V → V} (h : AppliesTo f a) (hf : f ∈ˢ piSet A B) :
    a ∈ˢ A := (h.dom hf).2

/-- **`∀`-formation in the universes of types.** -/
theorem piR_mem_typeU {u v : Nat} {p : Bool} {A : V} {B : V → V}
    (hp : p = true ↔ v = 0) (hA : A ∈ˢ typeU u) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ typeU v) :
    piR p A B ∈ˢ typeU (Level.imaxNat u v) := by
  by_cases hv : v = 0
  · rw [(Level.imaxNat_eq_zero_iff u v).mpr hv, hp.mpr hv, mem_typeU_zero]
    exact piR_true_mem_univ_zero
  · have hpf : p = false := by cases p <;> simp_all
    rw [Level.imaxNat_of_ne_zero hv, hpf, mem_typeU_pos (by omega)]
    refine ⟨piR_false_mem_univ (by omega) (univ_mono (Nat.le_max_left _ _)
      (mem_univ_of_mem_typeU hA)) fun x hx => univ_mono (Nat.le_max_right _ _)
      (mem_univ_of_mem_typeU (hB x hx)), Or.inr strict_piSet⟩

/-- A truth value that is strict has no member. -/
theorem not_mem_of_univ_zero_strict {T z : V} (h0 : T ∈ˢ univ 0) (hs : Strict T) :
    ¬ z ∈ˢ T := fun hz => hs.2 (eq_pt_of_mem_univ_zero h0 hz ▸ hz)

/-! ## The value-driven regimes (task #344)

The interpretation's binder cases (`Interp.lean`).  The regime is no
datum but a property of the values: a function space is propositional
exactly when every fibre over the domain is a truth value (`propB`), an
abstraction is the point exactly when every body value over the domain
is (`ptB`).  Over a nonempty domain they say whether the body is a
proof; over an empty domain both read "proposition" — the function
space is `{pt}`, the abstraction the point. -/

open Classical in
/-- Is every fibre over the domain a truth value? -/
noncomputable def propB (A : V) (B : V → V) : Bool := decide (∀ x, x ∈ˢ A → B x ∈ˢ univ 0)

open Classical in
/-- Is every body value over the domain the point? -/
noncomputable def ptB (A : V) (F : V → V) : Bool := decide (∀ x, x ∈ˢ A → F x = pt)

/-- **The function space, regime read off the fibres.** -/
noncomputable def piV (A : V) (B : V → V) : V := piR (propB A B) A B

/-- **The abstraction, regime read off the body values.** -/
noncomputable def lamV (A : V) (F : V → V) : V := lamR (ptB A F) A F

/-- **A typed application meets the application clause** (point, or η). -/
theorem appliesTo_of_mem_piV {A f a : V} {B : V → V} (hf : f ∈ˢ piV A B)
    (hA : IsTy A) (ha : a ∈ˢ A) : AppliesTo f a :=
  appliesTo_of_mem_piR hf hA ha

open Classical in
theorem propB_eq_true {A : V} {B : V → V} :
    propB A B = true ↔ ∀ x, x ∈ˢ A → B x ∈ˢ univ 0 := by
  unfold propB; exact decide_eq_true_iff

open Classical in
theorem ptB_eq_true {A : V} {F : V → V} :
    ptB A F = true ↔ ∀ x, x ∈ˢ A → F x = pt := by
  unfold ptB; exact decide_eq_true_iff

theorem propB_congr {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    propB A B = propB A B' := by
  rw [Bool.eq_iff_iff, propB_eq_true, propB_eq_true]
  exact ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩

theorem ptB_congr {A : V} {F F' : V → V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    ptB A F = ptB A F' := by
  rw [Bool.eq_iff_iff, ptB_eq_true, ptB_eq_true]
  exact ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩

theorem piV_congr {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    piV A B = piV A B' := by
  unfold piV; rw [propB_congr h]; exact piR_congr h

theorem lamV_congr {A : V} {F F' : V → V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    lamV A F = lamV A F' := by
  unfold lamV; rw [ptB_congr h]; exact lamR_congr h

/-- **β, on the domain, with no other premise.** -/
theorem app_lamV {A a : V} {F : V → V} (ha : a ∈ˢ A) : app (lamV A F) a = F a := by
  unfold lamV
  cases h : ptB A F
  · exact app_graph ha
  · rw [lamR_true, app_pt]; exact ((ptB_eq_true.mp h) a ha).symm

/-- An abstraction all of whose body values are the point is the point. -/
theorem lamV_eq_pt {A : V} {F : V → V} (h : ∀ x, x ∈ˢ A → F x = pt) : lamV A F = pt := by
  unfold lamV; rw [ptB_eq_true.mpr h]; rfl

/-- An abstraction that is not the point is the graph. -/
theorem lamV_eq_graph {A : V} {F : V → V} (h : lamV A F ≠ pt) : lamV A F = graph F A := by
  unfold lamV at h ⊢
  cases hb : ptB A F
  · rfl
  · rw [hb, lamR_true] at h; exact absurd rfl h

/-- An abstraction that is not the point is never the point (a graph). -/
theorem lamV_ne_pt_of {A : V} {F : V → V} {x : V} (hx : x ∈ˢ A) (h : F x ≠ pt) :
    lamV A F ≠ pt := by
  unfold lamV
  cases hb : ptB A F
  · exact graph_ne_pt
  · exact absurd ((ptB_eq_true.mp hb) x hx) h

theorem IsTy_piV {A : V} {B : V → V} : IsTy (piV A B) := IsTy_piR

/-- A member of a function space that is not the point is a member of
the graph space. -/
theorem mem_piSet_of_mem_piV {A f : V} {B : V → V} (hf : f ∈ˢ piV A B) (hn : f ≠ pt) :
    f ∈ˢ piSet A B := by
  unfold piV at hf
  cases hb : propB A B
  · rw [hb] at hf; exact hf
  · rw [hb] at hf; exact absurd (eq_pt_of_mem_piR_true hf) hn

/-- Elimination. -/
theorem app_mem_piV {A f a : V} {B : V → V} (hf : f ∈ˢ piV A B) (ha : a ∈ˢ A) :
    app f a ∈ˢ B a := app_mem_piR hf ha

/-- **Introduction**: body values in fibres that are types abstract into
the function space.  Where every fibre is a truth value every body value is
the point, and so is the abstraction; where one fibre is not, it is
strict, its body value is not the point, and the abstraction is the
graph. -/
theorem lamV_mem {A : V} {F B : V → V} (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB : ∀ x, x ∈ˢ A → IsTy (B x)) : lamV A F ∈ˢ piV A B := by
  unfold piV
  cases hp : propB A B
  · -- some fibre is no truth value: strict, so its body value is not the point
    have : ¬ ∀ x, x ∈ˢ A → B x ∈ˢ univ 0 := fun h => by
      rw [propB_eq_true.mpr h] at hp; exact nomatch hp
    obtain ⟨x₀, hx₀, hB₀⟩ : ∃ x, x ∈ˢ A ∧ ¬ B x ∈ˢ univ 0 :=
      Classical.byContradiction fun hne => this fun x hx =>
        Classical.byContradiction fun h => hne ⟨x, hx, h⟩
    have hs : Strict (B x₀) := (hB x₀ hx₀).resolve_left hB₀
    rw [lamV_eq_graph (lamV_ne_pt_of hx₀ (ne_pt_of_mem_strict hs (hF x₀ hx₀)))]
    exact graph_mem_piSet hF
  · have h0 := propB_eq_true.mp hp
    rw [lamV_eq_pt fun x hx => eq_pt_of_mem_univ_zero (h0 x hx) (hF x hx)]
    exact pt_mem_truthVal fun x hx => eq_one_of_mem_univ_zero (h0 x hx) (hF x hx)

/-- **η**: a member of a function space whose fibres are types is the
abstraction of its applications. -/
theorem lamV_eta {A f : V} {B : V → V} (hf : f ∈ˢ piV A B) (hB : ∀ x, x ∈ˢ A → IsTy (B x)) :
    lamV A (fun x => app f x) = f := by
  by_cases hn : f = pt
  · subst hn
    exact lamV_eq_pt fun x _ => app_pt x
  · have hf' := mem_piSet_of_mem_piV hf hn
    have hp : propB A B = false := by
      cases h : propB A B
      · rfl
      · unfold piV at hf; rw [h] at hf; exact absurd (eq_pt_of_mem_piR_true hf) hn
    have : ¬ ∀ x, x ∈ˢ A → B x ∈ˢ univ 0 := fun h => by
      rw [propB_eq_true.mpr h] at hp; exact nomatch hp
    obtain ⟨x₀, hx₀, hB₀⟩ : ∃ x, x ∈ˢ A ∧ ¬ B x ∈ˢ univ 0 :=
      Classical.byContradiction fun hne => this fun x hx =>
        Classical.byContradiction fun h => hne ⟨x, hx, h⟩
    have hs : Strict (B x₀) := (hB x₀ hx₀).resolve_left hB₀
    rw [lamV_eq_graph (lamV_ne_pt_of hx₀ (ne_pt_of_mem_strict hs (app_mem_piSet hf' hx₀)))]
    exact graph_app_eq hf'

/-- **`∀`-formation in the sorts' sets `typeU`**, with no regime
premise: over fibres in `Sort 0` the function space is a truth value; over
fibres in a positive sort it is a truth value or a strict function
space, a type either way. -/
theorem piV_mem_typeU {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ typeU u) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ typeU v) :
    piV A B ∈ˢ typeU (Level.imaxNat u v) := by
  by_cases hv : v = 0
  · subst hv
    have hp : propB A B = true :=
      propB_eq_true.mpr fun x hx => mem_typeU_zero.mp (hB x hx)
    rw [(Level.imaxNat_eq_zero_iff u 0).mpr rfl, mem_typeU_zero]
    unfold piV; rw [hp]; exact piR_true_mem_univ_zero
  · rw [Level.imaxNat_of_ne_zero hv, mem_typeU_pos (by omega)]
    refine ⟨?_, IsTy_piV⟩
    unfold piV
    cases propB A B
    · exact piR_false_mem_univ (by omega) (univ_mono (Nat.le_max_left _ _)
        (mem_univ_of_mem_typeU hA)) fun x hx => univ_mono (Nat.le_max_right _ _)
        (mem_univ_of_mem_typeU (hB x hx))
    · exact univ_mono (Nat.zero_le _) piR_true_mem_univ_zero

/-- A member of a function space whose fibres hold only the point is
the point. -/
theorem eq_pt_of_mem_piV {A f : V} {B : V → V} (hB : ∀ x, x ∈ˢ A → ∀ y, y ∈ˢ B x → y = pt)
    (hf : f ∈ˢ piV A B) : f = pt := by
  have hp : propB A B = true := propB_eq_true.mpr fun x hx => mem_univ_zero.mpr (hB x hx)
  unfold piV at hf; rw [hp] at hf
  exact eq_pt_of_mem_piR_true hf

/-- Over an empty domain the function space is `{pt}`. -/
theorem piV_of_empty {A : V} {B : V → V} (h : ∀ x, ¬ x ∈ˢ A) : piV A B = one := by
  unfold piV
  rw [propB_eq_true.mpr fun x hx => absurd hx (h x), piR_true]
  exact ext fun z => by
    rw [mem_truthVal, mem_one]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', fun x hx => absurd hx (h x)⟩⟩

/-- Over an empty domain the abstraction is the point. -/
theorem lamV_of_empty {A : V} {F : V → V} (h : ∀ x, ¬ x ∈ˢ A) : lamV A F = pt :=
  lamV_eq_pt fun x hx => absurd hx (h x)

end SetLib

end Fragment
