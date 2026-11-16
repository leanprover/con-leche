module

public import ConLeche.SetTheory.Derive.Graphs
public import ConLeche.SetTheory.Derive.Tg

@[expose] public section

/-!
# Strict sets, types, and the two universes over `tg` (task #342)

A **strict** set is neither the proof point nor contains it; a **type**
is a truth value or a strict set.  Its members are all the point (a
truth value) or none of them (a strict set): a member of a strict set
is never the point (`ne_pt_of_mem_strict`).

Two universes are carved out of the axiomatic chain `tg`
(`Derive/Tg.lean`), equal at `0` (the truth values, `univZero`):
* **`tyU n`**, the universe of types (task #344's `typeU`): the members
  of `tg n` that are types.  It is cumulative (`tyU_mono`): a truth value
  is a type at every level.  This is what a sort denotes: `univ := tyU`
  (`Derive/Univ.lean`, ruling R2).
* **`strictU n`**, the strict universe (task #340's `typeU`): above `0`
  the strict members of `tg n`.  It is not cumulative from `0`
  (`{pt} ∉ strictU 1`), but it is closed under the unions and the `∅`
  adjunction the least fixed points need (`Derive/LfpFam.lean`), which
  `tyU` is not (`{pt} ∪ ω` is no type).  It is the fibre space of the
  inductive families and tuples.

Also here, the last point law: `pt ∉ ω` (the others are in
`Derive/Pt.lean` and `Derive/Graphs.lean`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The point is not a natural number -/

/-- `pt ∉ ω`: every nonzero von Neumann numeral has `∅` as a member,
and the point's one member `ptTag` is not `∅` (it has `∅` as a member). -/
theorem pt_not_mem_omega : ¬ (pt : V) ∈ˢ omega := by
  intro h
  obtain ⟨k, hk⟩ := mem_omega_iff.mp h
  match k, hk with
  | 0, hk => exact pt_ne_empty hk
  | k + 1, hk =>
    have h0 : (vnat 0 : V) ∈ˢ pt := hk ▸ vnat_mem_vnat_of_lt (Nat.succ_pos k)
    have h1 : (empty : V) = ptTag := mem_pt.mp h0
    have h2 := empty_mem_ptTag (V := V)
    rw [← h1] at h2
    exact not_mem_empty _ h2

/-! ## Strict sets, types, fibres -/

/-- A **strict** set: not the point, and the point is not a member. -/
def Strict (X : V) : Prop := X ≠ pt ∧ ¬ pt ∈ˢ X

/-- A **type**: a truth value, or a strict set. -/
def IsTy (X : V) : Prop := X ∈ˢ univZero ∨ Strict X

/-- The regime of a fibre: a truth value at a proposition, strict above. -/
def Fib : Bool → V → Prop
  | true, X => X ∈ˢ univZero
  | false, X => Strict X

@[simp] theorem Fib_true {X : V} : Fib true X ↔ X ∈ˢ univZero := Iff.rfl
@[simp] theorem Fib_false {X : V} : Fib false X ↔ Strict X := Iff.rfl

open Classical in
/-- **The strict universe**: the truth values at `0`, the strict
members of the axiomatic level `tg n` above (the fibre space of the
least fixed points). -/
noncomputable def strictU (n : Nat) : V := if n = 0 then tg 0 else sep (tg n) Strict

theorem strictU_zero : (strictU 0 : V) = univZero := by
  unfold strictU; rw [ite_eq_left rfl, tg_zero]

theorem mem_strictU_zero {T : V} : T ∈ˢ (strictU 0 : V) ↔ T ∈ˢ univZero := by
  rw [strictU_zero]

theorem mem_strictU_pos {n : Nat} (hn : n ≠ 0) {T : V} :
    T ∈ˢ (strictU n : V) ↔ T ∈ˢ tg n ∧ Strict T := by
  unfold strictU; rw [ite_eq_right hn]; exact mem_sep

theorem strictU_subset_tg (n : Nat) : (strictU n : V) ⊆ˢ tg n := by
  by_cases hn : n = 0
  · subst hn; intro T hT; rw [tg_zero]; exact mem_strictU_zero.mp hT
  · intro T hT; exact ((mem_strictU_pos hn).mp hT).1

theorem mem_tg_of_mem_strictU {n : Nat} {T : V} (h : T ∈ˢ (strictU n : V)) : T ∈ˢ tg n :=
  strictU_subset_tg n T h

theorem ne_pt_of_mem_univZero {T : V} (h : T ∈ˢ (univZero : V)) : T ≠ pt := by
  rintro rfl; exact pt_not_mem_univZero h

theorem IsTy.ne_pt {T : V} (h : IsTy T) : T ≠ pt := by
  rcases h with h | h
  · exact ne_pt_of_mem_univZero h
  · exact h.1

theorem IsTy_of_Fib {p : Bool} {X : V} (h : Fib p X) : IsTy X := by
  cases p
  · exact Or.inr h
  · exact Or.inl h

theorem IsTy_of_mem_strictU {n : Nat} {T : V} (h : T ∈ˢ (strictU n : V)) : IsTy T := by
  by_cases hn : n = 0
  · subst hn; exact Or.inl (mem_strictU_zero.mp h)
  · exact Or.inr ((mem_strictU_pos hn).mp h).2

/-- **(P)**: a member of a strict set is not the point. -/
theorem ne_pt_of_mem_strict {T x : V} (hT : Strict T) (hx : x ∈ˢ T) : x ≠ pt := by
  rintro rfl; exact hT.2 hx

/-- The members of a type are all the point or none of them. -/
theorem IsTy.eq_of_ne_pt {T x y : V} (hT : IsTy T) (hx : x ∈ˢ T) (hy : y ∈ˢ T)
    (h : x ≠ pt → y ≠ pt → x = y) : x = y := by
  rcases hT with hT | hT
  · rw [eq_pt_of_mem_univZero hT hx, eq_pt_of_mem_univZero hT hy]
  · exact h (ne_pt_of_mem_strict hT hx) (ne_pt_of_mem_strict hT hy)

/-! ## Strict sets -/

/-- A set with two distinct members is not the point. -/
theorem ne_pt_of_two {X a b : V} (ha : a ∈ˢ X) (hb : b ∈ˢ X) (hab : a ≠ b) : X ≠ pt := by
  rintro rfl; exact hab (eq_of_mem_pt ha hb)

/-- A set whose members are all Kuratowski pairs (tagged values) is
strict: the point's one member `ptTag` is not a pair, and the point
itself is not a pair. -/
theorem strict_of_kpairs {X : V} (h : ∀ z, z ∈ˢ X → ∃ a b, z = kpair a b) : Strict X := by
  refine ⟨?_, fun hp => ?_⟩
  · rintro rfl
    obtain ⟨a, b, hab⟩ := h ptTag ptTag_mem_pt
    exact ptTag_ne_kpair a b hab
  · obtain ⟨a, b, hab⟩ := h pt hp
    exact pt_ne_kpair a b hab

theorem strict_empty : Strict (empty : V) :=
  ⟨pt_ne_empty.symm, not_mem_empty _⟩

theorem univZero_ne_pt : (univZero : V) ≠ pt :=
  ne_pt_of_two (mem_univZero.mpr (Subset.refl _)) (mem_univZero.mpr (empty_subset _))
    unitSet_ne_empty

theorem strict_univZero : Strict (univZero : V) := ⟨univZero_ne_pt, pt_not_mem_univZero⟩

theorem strict_omega : Strict (omega : V) := by
  refine ⟨?_, pt_not_mem_omega⟩
  refine ne_pt_of_two empty_mem_omega (vsucc_mem_omega empty_mem_omega) ?_
  exact fun h => vsucc_ne_empty _ h.symm

/-- A function space is strict: its members are graphs, and the point's
member is not one. -/
theorem strict_piSet {A : V} {B : V → V} : Strict (piSet A B) := by
  refine ⟨?_, fun h => ne_pt_of_mem_piSet h rfl⟩
  intro he
  have hz : (ptTag : V) ∈ˢ piSet A B := he ▸ ptTag_mem_pt
  have h1 := eq_graph_app_of_mem_piSet hz
  have h2 : graph (fun x => app ptTag x) A ∈ˢ (pt : V) := by rw [h1]; exact ptTag_mem_pt
  exact graph_not_mem_pt h2

/-- A dependent pair set is strict: its members are pairs. -/
theorem strict_sigmaPairs {A : V} {B : V → V} : Strict (sigmaPairs A B) :=
  strict_of_kpairs fun z hz => by
    obtain ⟨x, -, y, -, rfl⟩ := mem_sigmaPairs.mp hz
    exact ⟨x, y, rfl⟩

theorem IsTy_of_strict {X : V} (h : Strict X) : IsTy X := Or.inr h

/-! ## The sorts themselves -/

theorem univZero_mem_tg_succ (n : Nat) : (univZero : V) ∈ˢ tg (n + 1) := by
  have h := tg_mem_tg (V := V) 0
  rw [tg_zero] at h
  exact tg_mono (Nat.succ_le_succ (Nat.zero_le n)) _ h

/-- `ω` is a type of every positive sort. -/
theorem omega_mem_strictU_succ (n : Nat) : (omega : V) ∈ˢ strictU (n + 1) :=
  (mem_strictU_pos (Nat.succ_ne_zero n)).mpr ⟨omega_mem_tg_succ n, strict_omega⟩

/-- The empty type is a type of every sort. -/
theorem empty_mem_strictU (n : Nat) : (empty : V) ∈ˢ strictU n := by
  by_cases hn : n = 0
  · subst hn; exact mem_strictU_zero.mpr (mem_univZero.mpr (empty_subset _))
  · exact (mem_strictU_pos hn).mpr ⟨empty_mem_tg n, strict_empty⟩

theorem unitSet_mem_strictU_zero : (unitSet : V) ∈ˢ strictU 0 :=
  mem_strictU_zero.mpr (mem_univZero.mpr (Subset.refl _))

/-! ## The universe of types (task #342 stage S1, task #344's `typeU`) -/

open Classical in
/-- **The universe of types at level `n`**: the truth values at `0`,
above the members of the axiomatic level `tg n` that are types. -/
noncomputable def tyU (n : Nat) : V := if n = 0 then tg 0 else sep (tg n) IsTy

theorem tyU_zero : (tyU 0 : V) = univZero := by
  unfold tyU; rw [ite_eq_left rfl, tg_zero]

/-- Membership, uniformly in the level: at `0` every truth value is a
type, so `tyU 0` is `sep (tg 0) IsTy` too. -/
theorem mem_tyU {n : Nat} {T : V} : T ∈ˢ (tyU n : V) ↔ T ∈ˢ tg n ∧ IsTy T := by
  by_cases hn : n = 0
  · subst hn; rw [tyU_zero, tg_zero]
    exact ⟨fun h => ⟨h, Or.inl h⟩, fun h => h.1⟩
  · unfold tyU; rw [ite_eq_right hn]; exact mem_sep

theorem mem_tg_of_mem_tyU {n : Nat} {T : V} (h : T ∈ˢ (tyU n : V)) : T ∈ˢ tg n :=
  (mem_tyU.mp h).1

theorem IsTy_of_mem_tyU {n : Nat} {T : V} (h : T ∈ˢ (tyU n : V)) : IsTy T :=
  (mem_tyU.mp h).2

/-- **Cumulativity.** -/
theorem tyU_mono {m n : Nat} (h : m ≤ n) : (tyU m : V) ⊆ˢ tyU n := fun _ hT =>
  mem_tyU.mpr ⟨tg_mono h _ (mem_tg_of_mem_tyU hT), IsTy_of_mem_tyU hT⟩

/-- A strict type is a type. -/
theorem strictU_subset_tyU (n : Nat) : (strictU n : V) ⊆ˢ tyU n := fun _ hT =>
  mem_tyU.mpr ⟨mem_tg_of_mem_strictU hT, IsTy_of_mem_strictU hT⟩

/-- A member of `tyU` that is strict is a member of `strictU`. -/
theorem mem_strictU_of_strict {n : Nat} {T : V} (hT : T ∈ˢ (tyU n : V)) (hs : Strict T) :
    T ∈ˢ (strictU n : V) := by
  by_cases hn : n = 0
  · subst hn; rw [strictU_zero]; rw [tyU_zero] at hT; exact hT
  · exact (mem_strictU_pos hn).mpr ⟨mem_tg_of_mem_tyU hT, hs⟩

theorem mem_tyU_of_IsTy {n : Nat} {T : V} (hT : T ∈ˢ tg n) (h : IsTy T) : T ∈ˢ (tyU n : V) :=
  mem_tyU.mpr ⟨hT, h⟩

theorem mem_tyU_of_strict {n : Nat} {T : V} (hT : T ∈ˢ tg n) (h : Strict T) :
    T ∈ˢ (tyU n : V) := mem_tyU_of_IsTy hT (IsTy_of_strict h)

/-- A truth value is a type of every level. -/
theorem mem_tyU_of_mem_univZero {n : Nat} {T : V} (hT : T ∈ˢ (univZero : V)) :
    T ∈ˢ (tyU n : V) :=
  tyU_mono (Nat.zero_le n) _ (by rw [tyU_zero]; exact hT)

theorem strict_tyU (n : Nat) : Strict (tyU n : V) := by
  by_cases hn : n = 0
  · subst hn; rw [tyU_zero]; exact strict_univZero
  · refine ⟨?_, fun h => (IsTy_of_mem_tyU h).ne_pt rfl⟩
    refine ne_pt_of_two (mem_tyU_of_strict (empty_mem_tg n) strict_empty)
      (mem_tyU_of_strict (V := V) (n := n) ?_ strict_univZero) ?_
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact univZero_mem_tg_succ m
    · intro h
      have h3 : (unitSet : V) ∈ˢ univZero := mem_univZero.mpr (Subset.refl _)
      rw [← h] at h3
      exact not_mem_empty _ h3

theorem tyU_mem_tg_succ (n : Nat) : (tyU n : V) ∈ˢ tg (n + 1) := by
  by_cases hn : n = 0
  · subst hn; rw [tyU_zero]; exact univZero_mem_tg_succ 0
  · unfold tyU; rw [ite_eq_right hn]
    exact (tg_isTGUniverse (Nat.succ_ne_zero n)).sep_mem (tg_mem_tg n)

/-- `Sort n : Sort (n+1)`. -/
theorem tyU_mem_tyU_succ (n : Nat) : (tyU n : V) ∈ˢ tyU (n + 1) :=
  mem_tyU_of_strict (tyU_mem_tg_succ n) (strict_tyU n)

/- `strictU` and `tyU` are opaque operators; their laws are the lemmas
above. -/
attribute [irreducible] strictU tyU

end ConLeche.SetTheory
