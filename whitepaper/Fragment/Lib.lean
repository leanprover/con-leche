module

@[expose] public section

/-!
# The set-theoretic library

Everything the fragment's proof uses of set theory, stated
declaratively as ONE class: sets and membership with extensionality
and separation, a point `pt` with its singleton, dependent function
spaces with graphs and application and their β/η/extensionality laws,
and a universe chain with its closure laws.  There is no construction
here, and nothing beyond these laws is used — every theorem of the
fragment is proved against the class.

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
`ConLeche/SetModel/Ops.lean`: the dependent product and abstraction at
a `Bool` saying whether the body is a proposition — a truth value and
the one proof when it is, a graph space and a graph when it is not.
The interpretation (`Interp.lean`) applies them to the annotation's
readout, and nowhere else does the regime enter.
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
  /-- A distinguished set; any set would do.  It is the one proof of
  every true proposition. -/
  pt : V
  /-- The one-element set `{pt}`. -/
  one : V
  /-- The members of `{pt}`. -/
  mem_one : ∀ {z : V}, Mem z one ↔ z = pt
  /-- The universe chain: `univ n` interprets `Sort n`. -/
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
  piSet_dom_unique : ∀ {A A' f : V} {B B' : V → V},
    Mem f (piSet A B) → Mem f (piSet A' B') → A = A'
  /-- Closure of the positive universes under dependent function
  spaces. -/
  piSet_mem_univ : ∀ {n : Nat} {A : V} {B : V → V}, n ≠ 0 →
    Mem A (univ n) → (∀ x, Mem x A → Mem (B x) (univ n)) → Mem (piSet A B) (univ n)

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

theorem truthVal_congr {p q : Prop} (h : p ↔ q) : (truthVal p : V) = truthVal q :=
  ext fun z => by rw [mem_truthVal, mem_truthVal, h]

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} (hf : f ∈ˢ piSet A B) : f ≠ pt := by
  rw [← graph_app_eq hf]; exact graph_ne_pt

/-! ## The two regimes

`piR`/`lamR` read a `Bool` — "is the body a proposition here?", the
annotation's readout at the current valuation — and nothing else. -/

/-- The dependent product at regime `p`: the truth value "every fibre
is inhabited" when `p`, the graph space above it. -/
def piR (p : Bool) (A : V) (B : V → V) : V :=
  if p then truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) else piSet A B

/-- Abstraction at regime `p`: the point when `p`, the graph above it. -/
def lamR (p : Bool) (A : V) (F : V → V) : V :=
  if p then pt else graph F A

theorem piR_true {A : V} {B : V → V} :
    piR true A B = truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) := rfl
theorem piR_false {A : V} {B : V → V} : piR false A B = piSet A B := rfl
theorem lamR_true {A : V} {F : V → V} : lamR true A F = (pt : V) := rfl
theorem lamR_false {A : V} {F : V → V} : lamR false A F = graph F A := rfl

theorem piR_congr {p : Bool} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : piR p A B = piR p A B' := by
  cases p
  · exact piSet_congr h
  · exact truthVal_congr
      ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩

theorem lamR_congr {p : Bool} {A : V} {F F' : V → V}
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lamR p A F = lamR p A F' := by
  cases p
  · exact graph_congr h
  · rfl

/-- Introduction: fibre-wise members abstract into the product.  At a
proposition the premise itself witnesses every fibre inhabited. -/
theorem lamR_mem {p : Bool} {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lamR p A F ∈ˢ piR p A B := by
  cases p
  · exact graph_mem_piSet hF
  · exact pt_mem_truthVal fun x hx => ⟨F x, hF x hx⟩

/-- **Proof irrelevance at products**: an inhabitant of a
propositional product is the point. -/
theorem eq_pt_of_mem_piR_true {A f : V} {B : V → V} (hf : f ∈ˢ piR true A B) :
    f = pt := eq_pt_of_mem_truthVal hf

/-- Elimination.  The fibre premise is used only at a proposition,
where the fibres must be truth values for the point to be the member. -/
theorem app_mem_piR {p : Bool} {A f a : V} {B : V → V}
    (hf : f ∈ˢ piR p A B) (ha : a ∈ˢ A)
    (hB : p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) : app f a ∈ˢ B a := by
  cases p
  · exact app_mem_piSet hf ha
  · have hfp : f = pt := eq_pt_of_mem_piR_true hf
    obtain ⟨y, hy⟩ := of_mem_truthVal hf a ha
    rw [hfp, app_pt]
    rwa [eq_pt_of_mem_univ_zero (hB rfl a ha) hy] at hy

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

/-- η: a member of a product is the abstraction of its applications. -/
theorem lamR_eta {p : Bool} {A f : V} {B : V → V} (hf : f ∈ˢ piR p A B) :
    lamR p A (fun x => app f x) = f := by
  cases p
  · exact graph_app_eq hf
  · rw [lamR_true, eq_pt_of_mem_piR_true hf]

/-- **Domain uniqueness** in the graph regime: a graph determines its
domain. -/
theorem piR_dom_unique {A A' f : V} {B B' : V → V}
    (h1 : f ∈ˢ piR false A B) (h2 : f ∈ˢ piR false A' B') : A = A' :=
  piSet_dom_unique h1 h2

/-- **Impredicativity**: a product landing in `Prop` is a truth value,
whatever its domain. -/
theorem piR_true_mem_univ_zero {A : V} {B : V → V} :
    piR true A B ∈ˢ (univ 0 : V) := truthVal_mem_univ_zero _

/-- The graph regime's universe membership. -/
theorem piR_false_mem_univ {n : Nat} {A : V} {B : V → V} (hn : n ≠ 0)
    (hA : A ∈ˢ univ n) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ n) :
    piR false A B ∈ˢ (univ n : V) := piSet_mem_univ hn hA hB

end SetLib

end Fragment
