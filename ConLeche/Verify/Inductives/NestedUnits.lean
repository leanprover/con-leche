module

public import ConLeche.Verify.Inductives.NestedOrder

public section

/-!
# The fold's UNITS: a root container's recursor family, and the fold over units (task #279 M-C″, DESIGN §M.58)

Task #312 refuted `BridgeSyntax` at the run: a container that is
ITSELF nested (`P4C`, `TaggedText`, `PersistentArrayNode`) puts a
transport cycle among the pins minted from it, cut by `copyRefB`'s
sub-term conjunct only, so ψ as a fold along `nestedTopoOrder` cannot
exist there.  The repair (the maintainer's, 2026-09-15) is a change of
GROUPING: the unit of the forward fold is one container's RECURSOR
FAMILY at the pin's parameters — the root pin `J Ds` together with the
pins `(I Es)[Ds]` of `J`'s own mimic motives `J.rec_1, J.rec_2, …` —
and the unit's terms are ONE application of that family, the copies'
carriers as its motives; a singleton unit (a non-nested container's
mint group) is today's case.  This module states the units' vocabulary
once, shared with the kernel's K.25 record:

* `NestedUnit` — a root pin and its members in the root container's
  recursor MOTIVE order (the mint group first, then the mimic motives'
  pins at the root's parameters);
* `unitOwns units u j` — pin `j` is a member of unit `u`;
* `UnitTable n units` — what the fold consumes of K.25's U1: the units'
  members are pairwise disjoint, every pin is owned, members are pins,
  a root is its own member;
* `UnitRef k st units u u'` — unit `u` refers to unit `u'`: a processed
  constructor of a copy of `u` mentions the aux name of a pin of `u'`
  (the group-wide mention of K.15 (1), over the unit; NO sub-term
  conjunct);
* `unitFold` — a left fold over a list of units whose step writes a
  whole unit's entries, with `orderFold`'s three lemmas over it:
  `unitFold_spec`/`TopoOrder.unitFold_all` (every owned entry has the
  per-entry property the step establishes from the referenced units')
  and `TopoOrder.unitFold_eq_step` (an owned entry is the step at the
  FINAL table — what the round trips consume).
-/

namespace ConLeche

/-- **A unit of the forward fold**: a root pin and the pins of its
container's recursor family at the root's parameters, in the
recursor's MOTIVE order (K.25 U2: the mint group first, `members[t] =
grpBase + t`, then one pin per mimic motive). -/
structure NestedUnit where
  root : Nat
  members : List Nat
  deriving Repr, Inhabited

/-- Pin `j` is a member of unit `u`. -/
@[expose] def unitOwns (units : List NestedUnit) (u j : Nat) : Prop :=
  ∃ U : NestedUnit, units[u]? = some U ∧ j ∈ U.members

/-- **The unit table's facts the fold consumes** (K.25 U1, read at the
run): the members of distinct units are disjoint and a unit's members
are distinct, every pin below `n` is owned, every member is a pin, and
a root is a member of its own unit. -/
structure UnitTable (n : Nat) (units : List NestedUnit) : Prop where
  disj : ∀ u u' j, unitOwns units u j → unitOwns units u' j → u = u'
  nodupU : ∀ U ∈ units, U.members.Nodup
  complete : ∀ j, j < n → ∃ u, unitOwns units u j
  bounded : ∀ U ∈ units, ∀ j ∈ U.members, j < n
  root : ∀ U ∈ units, U.root ∈ U.members

/-- **Unit `u` refers to unit `u'`** (DESIGN §M.58 (b), the unit order's
relation): `u ≠ u'` and a processed constructor of a copy of `u`
mentions the aux name of a pin of `u'`.  The mention ranges over the
whole unit (ψ at a unit folds every member's constructors); there is
no sub-term conjunct. -/
@[expose] def UnitRef (k : Nat) (st : ElimState) (units : List NestedUnit) (u u' : Nat) : Prop :=
  u ≠ u' ∧ ∃ (U U' : NestedUnit), units[u]? = some U ∧ units[u']? = some U' ∧
    ∃ s ∈ U.members, ∃ t : AuxType, st.types[k + s]? = some t ∧ ∃ c ∈ t.ctors,
      ∃ s' ∈ U'.members, ∃ q' : NestedPin, st.pins[s']? = some q' ∧
        (c.2.1).mentionsConst q'.aux = true

/-! ## The fold over units -/

/-- The table after the listed units, in order: the step at unit `u`
writes the WHOLE table (its own entries; the frame condition
`hframe` below says it leaves the others alone). -/
def unitFold {α : Type} (step : (Nat → α) → Nat → (Nat → α)) : List Nat → (Nat → α) → (Nat → α)
  | [], tbl => tbl
  | u :: rest, tbl => unitFold step rest (step tbl u)

/-- **The fold's invariant** (`orderFold_spec` over units): a per-entry
property `P` that each unit's step establishes at its OWN entries from
the property at the entries of the units it refers to holds of every
owned entry of the folded table.  `owns u j` is the ownership relation
(disjoint across units), `hframe` the step's frame condition. -/
theorem unitFold_spec {α : Type} {R : Nat → Nat → Prop} {n : Nat}
    (step : (Nat → α) → Nat → (Nat → α)) (P : Nat → α → Prop) (owns : Nat → Nat → Prop)
    (hdisj : ∀ u u' j, owns u j → owns u' j → u = u')
    (hframe : ∀ (tbl : Nat → α) (u j : Nat), ¬ owns u j → step tbl u j = tbl j)
    (hstep : ∀ (tbl : Nat → α) (u : Nat), (∀ u', R u u' → ∀ j, owns u' j → P j (tbl j)) →
      ∀ j, owns u j → P j (step tbl u j)) :
    ∀ {pre rest : List Nat} (tbl : Nat → α), TopoOrder R n (pre ++ rest) →
      (∀ u ∈ pre, ∀ j, owns u j → P j (tbl j)) →
      ∀ u ∈ pre ++ rest, ∀ j, owns u j → P j (unitFold step rest tbl j) := by
  intro pre rest
  induction rest generalizing pre with
  | nil =>
    intro tbl _ hpre u hu
    rw [List.append_nil] at hu
    exact hpre u hu
  | cons u₀ rest ih =>
    intro tbl h hpre
    have hsplit : pre ++ u₀ :: rest = (pre ++ [u₀]) ++ rest := by simp
    rw [hsplit] at h ⊢
    have hu₀ : (pre ++ [u₀] ++ rest)[pre.length]? = some u₀ := by
      rw [List.getElem?_append_left (by simp), List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hnotin : u₀ ∉ pre := by
      intro hmem
      have hnd := h.nodup
      rw [List.append_assoc, List.nodup_append] at hnd
      exact hnd.2.2 u₀ hmem u₀ (List.mem_append_left rest (List.mem_singleton.mpr rfl)) rfl
    show ∀ u ∈ pre ++ [u₀] ++ rest, ∀ j, owns u j → P j (unitFold step rest (step tbl u₀) j)
    refine ih (pre := pre ++ [u₀]) _ h ?_
    intro u hu j hj
    rw [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · have hne : u ≠ u₀ := fun heq => hnotin (heq ▸ hu)
      have hnot : ¬ owns u₀ j := fun h₀ => hne (hdisj u u₀ j hj h₀)
      rw [hframe tbl u₀ j hnot]
      exact hpre u hu j hj
    · refine hstep tbl u (fun u' hR j' hj' => ?_) j hj
      have hmem := h.ref_mem_take hu₀ hR
      rw [List.take_append_of_le_length (by simp), List.take_left' rfl] at hmem
      exact hpre u' hmem j' hj'

/-- **Every owned entry of the folded table has the property**
(`unitFold_spec` at `pre = []`, over the order's completeness). -/
theorem TopoOrder.unitFold_all {α : Type} {R : Nat → Nat → Prop} {n : Nat} {order : List Nat}
    (h : TopoOrder R n order) (step : (Nat → α) → Nat → (Nat → α)) (P : Nat → α → Prop)
    (owns : Nat → Nat → Prop)
    (hdisj : ∀ u u' j, owns u j → owns u' j → u = u')
    (hframe : ∀ (tbl : Nat → α) (u j : Nat), ¬ owns u j → step tbl u j = tbl j)
    (hstep : ∀ (tbl : Nat → α) (u : Nat), (∀ u', R u u' → ∀ j, owns u' j → P j (tbl j)) →
      ∀ j, owns u j → P j (step tbl u j))
    (tbl₀ : Nat → α) : ∀ u, u < n → ∀ j, owns u j → P j (unitFold step order tbl₀ j) := by
  intro u hu j hj
  have := unitFold_spec step P owns hdisj hframe hstep (pre := []) (rest := order) tbl₀
    (by simpa using h) (fun _ h => nomatch h) u (by simpa using h.complete u hu) j hj
  simpa using this

/-- An entry no listed unit owns is untouched by the fold. -/
theorem unitFold_notOwned {α : Type} (step : (Nat → α) → Nat → (Nat → α)) (owns : Nat → Nat → Prop)
    (hframe : ∀ (tbl : Nat → α) (u j : Nat), ¬ owns u j → step tbl u j = tbl j) :
    ∀ (l : List Nat) (tbl : Nat → α) (j : Nat), (∀ u ∈ l, ¬ owns u j) →
      unitFold step l tbl j = tbl j
  | [], _, _, _ => rfl
  | u₀ :: rest, tbl, j, hj => by
    simp only [unitFold]
    rw [unitFold_notOwned step owns hframe rest _ j (fun u hu => hj u (List.mem_cons_of_mem _ hu)),
      hframe tbl u₀ j (hj u₀ List.mem_cons_self)]

/-- The fold over an appended list is the fold over the second part
from the first part's table. -/
theorem unitFold_append {α : Type} (step : (Nat → α) → Nat → (Nat → α)) :
    ∀ (l₁ l₂ : List Nat) (tbl : Nat → α),
      unitFold step (l₁ ++ l₂) tbl = unitFold step l₂ (unitFold step l₁ tbl)
  | [], _, _ => rfl
  | u :: l₁, l₂, tbl => by
    simp only [List.cons_append, unitFold]
    exact unitFold_append step l₁ l₂ _

/-- **An owned entry of the folded table is the step at the FINAL
table** (`orderFold_eq_step` over units), when the step at a unit
reads only the entries the units it refers to own (`hdep`): the entry
is set once by its owner and never touched again (disjointness and
`nodup`), and the entries it reads are earlier in the order, so
already final. -/
theorem TopoOrder.unitFold_eq_step {α : Type} {R : Nat → Nat → Prop} {n : Nat} {order : List Nat}
    (h : TopoOrder R n order) (step : (Nat → α) → Nat → (Nat → α)) (owns : Nat → Nat → Prop)
    (hdisj : ∀ u u' j, owns u j → owns u' j → u = u')
    (hframe : ∀ (tbl : Nat → α) (u j : Nat), ¬ owns u j → step tbl u j = tbl j)
    (tbl₀ : Nat → α) {u j : Nat} (hu : u < n) (hj : owns u j)
    (hdep : ∀ (tbl tbl' : Nat → α), (∀ u', R u u' → ∀ j', owns u' j' → tbl j' = tbl' j') →
      step tbl u j = step tbl' u j) :
    unitFold step order tbl₀ j = step (unitFold step order tbl₀) u j := by
  obtain ⟨pre, rest, hsplit⟩ := List.append_of_mem (h.complete u hu)
  have hnd := h.nodup
  rw [hsplit] at hnd
  obtain ⟨-, hndR, hdisjL⟩ := List.nodup_append.mp hnd
  have huR : u ∉ rest := (List.nodup_cons.mp hndR).1
  have huP : u ∉ pre := fun hm => hdisjL u hm u List.mem_cons_self rfl
  -- an entry `u` owns is owned by no other unit
  have hown : ∀ u', u' ≠ u → ¬ owns u' j := fun u' hne h' => hne (hdisj u' u j h' hj)
  -- the final table, split at `u`
  have hfinal : unitFold step order tbl₀ = unitFold step rest (step (unitFold step pre tbl₀) u) := by
    rw [hsplit, unitFold_append]
    rfl
  -- the entry at `j` is the step at the table before `u`
  have hj_entry : unitFold step order tbl₀ j = step (unitFold step pre tbl₀) u j := by
    rw [hfinal, unitFold_notOwned step owns hframe rest _ j
      (fun u' hu' => hown u' (fun heq => huR (heq ▸ hu')))]
  rw [hj_entry]
  refine hdep _ _ fun u' hR j' hj' => ?_
  -- a referenced unit is in `pre`, hence its entries are final
  have hpos : order[pre.length]? = some u := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hmem : u' ∈ pre := by
    have := h.ref_mem_take hpos hR
    rwa [hsplit, List.take_left] at this
  -- after `pre` the entry is never written again: `u` and `rest` do not own it
  have hu'ne : u' ≠ u := fun heq => huP (heq ▸ hmem)
  have hnotU : ¬ owns u j' := fun h' => hu'ne (hdisj u' u j' hj' h')
  rw [hfinal, unitFold_notOwned step owns hframe rest _ j'
    (fun u'' hu'' h'' => hdisjL u' hmem u'' (List.mem_cons_of_mem _ hu'') (hdisj u' u'' j' hj' h'')),
    hframe _ u j' hnotU]

end ConLeche
