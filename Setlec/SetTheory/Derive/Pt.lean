import Setlec.SetTheory.Derive.Universe

/-!
# The proof point, truth values, `univ 0`, and `eqv`

* `pt := {∅}` — the tagged proof point: the canonical inhabitant of
  every true proposition.  Its element `∅` is empty, while every
  element of a Kuratowski pair is nonempty, so `pt` is never an
  ordered pair and (since graphs are sets of pairs, and nonempty ones
  at that) never a function graph — the tag `Derive/Graphs.lean`
  exploits.
* `unitSet := {pt}` — the true truth value, and the model of `PUnit`.
* `univZero := power unitSet = {∅, {pt}}` — the set of truth values,
  Carneiro's `U₀ = {∅, {•}}`; stating it as a power set makes
  "members of `univ 0` are subsets of `{pt}`" definitional, and
  propositional extensionality one application of `ext`.
* `truthVal p` — the truth value of a meta-level proposition, `{pt}`
  if `p` holds and `∅` otherwise (classical); `eqv x y` is
  `truthVal (x = y)`.
-/

namespace Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The proof point `pt = {∅}`. -/
noncomputable def pt : V := sing empty

theorem mem_pt {z : V} : z ∈ˢ (pt : V) ↔ z = empty := mem_sing

theorem pt_ne_empty : (pt : V) ≠ empty :=
  ne_empty_of_mem (mem_pt.mpr rfl)

/-- `pt` is not a Kuratowski pair: its element is empty, a pair's
elements are not. -/
theorem pt_ne_kpair (a b : V) : (pt : V) ≠ kpair a b := by
  intro h
  obtain ⟨w, hw⟩ := mem_kpair_nonempty (h ▸ mem_pt.mpr rfl)
  exact not_mem_empty w hw

/-- The canonical singleton `{pt}`: the true truth value. -/
noncomputable def unitSet : V := sing pt

theorem mem_unitSet_iff {z : V} : z ∈ˢ (unitSet : V) ↔ z = pt := mem_sing

theorem pt_mem_unitSet : (pt : V) ∈ˢ unitSet := mem_unitSet_iff.mpr rfl

theorem unitSet_ne_empty : (unitSet : V) ≠ empty :=
  ne_empty_of_mem pt_mem_unitSet

/-- The interpretation of `Sort 0`: the set `{∅, {pt}}` of truth
values, stated as the power set of `{pt}`. -/
noncomputable def univZero : V := power unitSet

theorem mem_univZero {T : V} : T ∈ˢ (univZero : V) ↔ T ⊆ˢ unitSet :=
  mem_power_iff_subset

/-- Members of `univ 0` have at most the proof point as element. -/
theorem eq_pt_of_mem_univZero {T x : V} (hT : T ∈ˢ (univZero : V))
    (hx : x ∈ˢ T) : x = pt :=
  mem_unitSet_iff.mp (mem_univZero.mp hT x hx)

/-- Propositional extensionality: truth values with the same
`pt`-membership are equal. -/
theorem univZero_ext {A B : V} (hA : A ∈ˢ (univZero : V))
    (hB : B ∈ˢ (univZero : V)) (hab : pt ∈ˢ A → pt ∈ˢ B)
    (hba : pt ∈ˢ B → pt ∈ˢ A) : A = B :=
  ext fun z =>
    ⟨fun hz => by
       have h := eq_pt_of_mem_univZero hA hz; subst h; exact hab hz,
     fun hz => by
       have h := eq_pt_of_mem_univZero hB hz; subst h; exact hba hz⟩

open Classical in
/-- The truth value of a meta-level proposition: `{pt}` if it holds,
`∅` otherwise. -/
noncomputable def truthVal (p : Prop) : V := if p then unitSet else empty

theorem mem_truthVal {p : Prop} {z : V} :
    z ∈ˢ (truthVal p : V) ↔ p ∧ z = pt := by
  unfold truthVal
  split
  · next hp => exact ⟨fun hz => ⟨hp, mem_unitSet_iff.mp hz⟩, fun ⟨_, hz⟩ => hz ▸ pt_mem_unitSet⟩
  · next hp =>
    exact ⟨fun hz => absurd hz (not_mem_empty z), fun ⟨h, _⟩ => absurd h hp⟩

theorem pt_mem_truthVal {p : Prop} (hp : p) : (pt : V) ∈ˢ truthVal p :=
  mem_truthVal.mpr ⟨hp, rfl⟩

theorem of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ (truthVal p : V)) : p :=
  (mem_truthVal.mp hz).1

theorem eq_pt_of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ˢ (truthVal p : V)) :
    z = pt :=
  (mem_truthVal.mp hz).2

theorem truthVal_eq_unitSet {p : Prop} (hp : p) : (truthVal p : V) = unitSet := by
  unfold truthVal; exact if_pos hp

theorem truthVal_eq_empty {p : Prop} (hp : ¬ p) : (truthVal p : V) = empty := by
  unfold truthVal; exact if_neg hp

theorem truthVal_congr {p q : Prop} (h : p ↔ q) :
    (truthVal p : V) = truthVal q := by
  rcases Classical.em p with hp | hp
  · rw [truthVal_eq_unitSet hp, truthVal_eq_unitSet (h.mp hp)]
  · rw [truthVal_eq_empty hp, truthVal_eq_empty (fun hq => hp (h.mpr hq))]

theorem truthVal_mem_univZero (p : Prop) :
    (truthVal p : V) ∈ˢ univZero := by
  rcases Classical.em p with hp | hp
  · rw [truthVal_eq_unitSet hp]
    exact mem_univZero.mpr (Subset.refl _)
  · rw [truthVal_eq_empty hp]
    exact mem_univZero.mpr (empty_subset _)

/-- Every member of `univ 0` is the truth value of its own
inhabitedness. -/
theorem mem_univZero_eq_truthVal {T : V} (hT : T ∈ˢ (univZero : V)) :
    T = truthVal (pt ∈ˢ T) := by
  rcases Classical.em ((pt : V) ∈ˢ T) with hp | hp
  · rw [truthVal_eq_unitSet hp]
    exact ext fun z => ⟨fun hz => eq_pt_of_mem_univZero hT hz ▸ pt_mem_unitSet,
      fun hz => mem_unitSet_iff.mp hz ▸ hp⟩
  · rw [truthVal_eq_empty hp]
    exact eq_empty fun z hz => hp (eq_pt_of_mem_univZero hT hz ▸ hz)

/-- The truth value of an equality. -/
noncomputable def eqv (x y : V) : V := truthVal (x = y)

theorem eqv_mem_univZero (x y : V) : eqv x y ∈ˢ (univZero : V) :=
  truthVal_mem_univZero _

theorem eq_of_mem_eqv {a x y : V} (h : a ∈ˢ eqv x y) : x = y :=
  of_mem_truthVal h

theorem pt_mem_eqv_self (x : V) : (pt : V) ∈ˢ eqv x x :=
  pt_mem_truthVal rfl

/-- `pt`, `unitSet`, `univZero` and truth values live in every
(inhabited) Grothendieck universe. -/
theorem _root_.Setlec.IsTGUniverse.pt_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : (pt : V) ∈ˢ U :=
  hU.sing_mem hy (hU.empty_mem hy)

theorem _root_.Setlec.IsTGUniverse.unitSet_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : (unitSet : V) ∈ˢ U :=
  hU.sing_mem hy (hU.pt_mem hy)

theorem _root_.Setlec.IsTGUniverse.univZero_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) : (univZero : V) ∈ˢ U :=
  hU.power_mem (hU.unitSet_mem hy)

theorem _root_.Setlec.IsTGUniverse.truthVal_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ˢ U) (p : Prop) :
    (truthVal p : V) ∈ˢ U :=
  hU.transitive (hU.univZero_mem hy) (truthVal_mem_univZero p)

/- Compiler stubs (see `Derive/Empty.lean`): never executed, no logical
content. -/
private unsafe def ptImpl {V : Type u} [SetTheory V] : V := unsafeCast ()
private unsafe def unitSetImpl {V : Type u} [SetTheory V] : V := unsafeCast ()
private unsafe def eqvImpl {V : Type u} [SetTheory V] (_x _y : V) : V := unsafeCast ()

attribute [implemented_by ptImpl] pt
attribute [implemented_by unitSetImpl] unitSet
attribute [implemented_by eqvImpl] eqv

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] pt unitSet eqv

end Setlec.SetTheory
