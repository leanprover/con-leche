module

public import ConLeche.Verify.Modular.Store
public import ConLeche.Cached.ModIso
import Std.Data.HashMap.Lemmas

public section

/-!
# The store of a set of units, in the proof only (task #374)

An isolated run (`--modular=isolated`) builds no store: every module
reads the units of the modules it loads and nothing else.  The proof
that its checks are the local checks goes through the store-run's
theorems all the same, at a store built from the published units
**in the proof**: `ghostStore slots`, whose name index lists every
constant of every unit under its name, in module order, and whose list of
names stored twice is complete.  Nothing at runtime computes it.

* `ghostStore_idxOk` — its index is complete (`IdxOk`);
* `ghostStore_dupsOk` — its list of names stored twice is complete;
* `ghostStore_slot`, `ghostStore_lvl` — its units are the run's, every
  module's levels those its unit records.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- The names a unit holds at position `j`: its installed constant's and
its exported presentation's. -/
@[expose] def posNames (s : ModSlot) (j : Nat) : List Name :=
  ((s.prv.priv[j]?).map (·.name)).toList ++ (((s.exp.at1[j]?).join).map (·.name)).toList

/-- Every position of every unit, in module order. -/
@[expose] def ghostPos (slots : Array (Thunk ModSlot)) : List (Nat × Nat) :=
  (List.range slots.size).flatMap fun h =>
    (List.range (max (slotOf slots h).prv.priv.size (slotOf slots h).exp.at1.size)).map
      fun j => (h, j)

/-- The positions holding a name, in module order. -/
@[expose] def ghostAlts (slots : Array (Thunk ModSlot)) (n : Name) : List (Nat × Nat) :=
  (ghostPos slots).filter fun p => (posNames (slotOf slots p.1) p.2).contains n

/-- Every name the units hold. -/
@[expose] def ghostNames (slots : Array (Thunk ModSlot)) : List Name :=
  (ghostPos slots).flatMap fun p => posNames (slotOf slots p.1) p.2

/-- The name index of the units. -/
@[expose] def ghostMap (slots : Array (Thunk ModSlot)) : Std.HashMap Name (List (Nat × Nat)) :=
  (ghostNames slots).foldl (fun m n => m.insert n (ghostAlts slots n)) {}

/-- **The store of a set of units** (the proof's, never built): their name
index, their names stored twice, the units, every module's levels as its
unit records them. -/
@[expose] def ghostStore (slots : Array (Thunk ModSlot)) : Store :=
  { idx := #[ghostMap slots]
    dups := ((ghostNames slots).filter fun n => 2 ≤ (ghostAlts slots n).length).toArray
    slots
    lvls := Array.ofFn fun i : Fin slots.size => (slotOf slots i).prv.lvl }

theorem ghostStore_slot (slots : Array (Thunk ModSlot)) (h : Nat) :
    (ghostStore slots).slot h = slotOf slots h := rfl

theorem ghostStore_lvl {slots : Array (Thunk ModSlot)} {h : Nat} (hh : h < slots.size) :
    (ghostStore slots).lvl h = (slotOf slots h).prv.lvl := by
  unfold Store.lvl ghostStore
  simp [hh]

theorem foldl_insert_getElem? {β : Type} (f : Name → β) (n : Name) :
    ∀ (l : List Name) (m : Std.HashMap Name β),
      (l.foldl (fun m x => m.insert x (f x)) m)[n]? = if n ∈ l then some (f n) else m[n]?
  | [], m => by simp
  | x :: l, m => by
    rw [List.foldl_cons, foldl_insert_getElem? f n l]
    by_cases hl : n ∈ l
    · simp [hl]
    · simp only [hl, ↓reduceIte, List.mem_cons, or_false, Std.HashMap.getElem?_insert]
      by_cases hx : x = n
      · subst hx; simp
      · have : (x == n) = false := beq_false_of_ne hx
        simp [this, Ne.symm hx]

theorem mem_ghostNames {slots : Array (Thunk ModSlot)} {n : Name} (h : ghostAlts slots n ≠ []) :
    n ∈ ghostNames slots := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
  unfold ghostAlts at hp
  rw [List.mem_filter] at hp
  unfold ghostNames
  rw [List.mem_flatMap]
  exact ⟨p, hp.1, List.contains_iff_mem.mp hp.2⟩

theorem ghostMap_getElem? (slots : Array (Thunk ModSlot)) (n : Name) :
    (ghostMap slots)[n]? =
      if n ∈ ghostNames slots then some (ghostAlts slots n) else none := by
  unfold ghostMap
  rw [foldl_insert_getElem?]
  simp

/-- **The store's alternates of a name are the units' positions holding
it.** -/
theorem ghostStore_alts (slots : Array (Thunk ModSlot)) (n : Name) :
    (ghostStore slots).alts n = ghostAlts slots n := by
  unfold Store.alts MBase.alts Store.mb ghostStore
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
  have h0 : baseShard n 1 = 0 := by unfold baseShard; exact Nat.mod_one _
  rw [h0]
  simp only [List.getElem?_toArray, List.getElem?_cons_zero]
  rw [Std.HashMap.getD_eq_getD_getElem?, ghostMap_getElem?]
  split
  · rfl
  · rename_i hn
    simp only [Option.getD_none]
    cases hg : ghostAlts slots n with
    | nil => rfl
    | cons p ps => exact absurd (mem_ghostNames (by rw [hg]; exact List.cons_ne_nil p ps)) hn

theorem ghostPos_pairwise (slots : Array (Thunk ModSlot)) : (ghostPos slots).Pairwise lexLt := by
  unfold ghostPos
  rw [List.pairwise_flatMap]
  refine ⟨fun h _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun hj => .inr ⟨rfl, hj⟩
  · refine List.pairwise_lt_range.imp ?_
    intro h h' hh x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    exact .inl hh

theorem mem_ghostPos {slots : Array (Thunk ModSlot)} {h j : Nat} (hh : h < slots.size)
    (hj : j < (slotOf slots h).prv.priv.size ∨ j < (slotOf slots h).exp.at1.size) :
    (h, j) ∈ ghostPos slots := by
  unfold ghostPos
  rw [List.mem_flatMap]
  refine ⟨h, List.mem_range.mpr hh, List.mem_map.mpr ⟨j, List.mem_range.mpr ?_, rfl⟩⟩
  omega

/-- **The store of a set of units lists every constant of every unit
under its name, in module order.** -/
theorem ghostStore_idxOk (slots : Array (Thunk ModSlot)) : IdxOk (ghostStore slots) := by
  refine ⟨fun n => ?_, fun h j c hh hc => ?_, fun h j c hh hc => ?_⟩
  · rw [ghostStore_alts]
    exact (ghostPos_pairwise slots).filter _
  · rw [ghostStore_alts]
    rw [ghostStore_slot] at hc
    unfold ghostAlts
    have hj : j < (slotOf slots h).prv.priv.size := by
      rcases Nat.lt_or_ge j (slotOf slots h).prv.priv.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hc; cases hc
    refine List.mem_filter.mpr ⟨mem_ghostPos hh (.inl hj), ?_⟩
    unfold posNames
    simp [hc]
  · rw [ghostStore_alts]
    rw [ghostStore_slot] at hc
    unfold ghostAlts
    have hj : j < (slotOf slots h).exp.at1.size := by
      rcases Nat.lt_or_ge j (slotOf slots h).exp.at1.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hc; cases hc
    refine List.mem_filter.mpr ⟨mem_ghostPos hh (.inr hj), ?_⟩
    unfold posNames
    simp [hc]

/-- **The store of a set of units lists its names stored twice.** -/
theorem ghostStore_dupsOk (slots : Array (Thunk ModSlot)) : dupsOk (ghostStore slots) = true := by
  unfold dupsOk
  rw [Array.all_eq_true]
  intro k hk
  have hk0 : k = 0 := by
    simp [ghostStore] at hk; omega
  subst hk0
  show ((ghostMap slots).toList.all fun (n, l) => l.length < 2 || _) = true
  rw [List.all_eq_true]
  rintro ⟨n, l⟩ hm
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ghostMap_getElem?] at hm
  split at hm
  · rename_i hn
    cases hm
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hl : (ghostAlts slots n).length < 2
    · exact .inl hl
    · refine .inr ?_
      show ((ghostNames slots).filter fun n => 2 ≤ (ghostAlts slots n).length).toArray.contains n
      rw [Array.contains_iff_mem, List.mem_toArray, List.mem_filter]
      exact ⟨hn, by simp; omega⟩
  · cases hm

end ConLeche.Cached.Mod
