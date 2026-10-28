module

public import ConLeche.Cached.ModIso
import ConLeche.Verify.EnvBound
import ConLeche.Verify.Modular.IsoCtx
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

/-!
# The isolated context in one pass (tasks #373, #374)

The specification of a module's isolated context is a list: the
presented constants of the units it reads, in module order, each name's
first kept (`isoCtx`); its index is `isoIndex = mkFEnv (isoCtx …)`, its
lookup `isoLook` (a name's first presentation, with its module and
position), its duplicates' check `keysOk` (every presentation of a name
has the first's qualified name).  What runs is one pass over the units
(`isoBuild`), deciding "first of its name" by the index under
construction, recording each kept constant's module and position by
counter and each dropped presentation.  This file proves that it
computes the three:

* `isoBuild_fenv` — its index is `isoIndex` (EQUAL as values: the hash
  maps receive the same insertions in the same order);
* `isoBuild_look` — its lookup is `isoLook`;
* `isoBuild_keysOk` — its check of the dropped presentations is
  `keysOk` (a kept presentation is its name's first, whose qualified name
  is trivially the first's).
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- A presentation's module, position and name. -/
@[expose] def tagOf (e : IsoEntry) : Nat × Nat × Name := (e.h, e.j, e.ci.name)

/-- The presentations dropped by `firstNamedGo`, onto `dr`. -/
@[expose] def droppedGo : List IsoEntry → Std.HashSet Name → List (Nat × Nat × Name) →
    List (Nat × Nat × Name)
  | [], _, dr => dr
  | e :: es, seen, dr =>
    if seen.contains e.ci.name then droppedGo es seen (tagOf e :: dr)
    else droppedGo es (seen.insert e.ci.name) dr

/-- The state `isoBuild` holds after the entries `acc` were kept (newest
first) and `dr` dropped. -/
private def stateOf (acc : List IsoEntry) (dr : List (Nat × Nat × Name)) : IsoAcc :=
  ⟨acc.length, acc.map (·.ci), acc.filterMap (·.tbl), (mkFEnvGo (acc.map (·.ci))).2,
    mkTblsGo (acc.filterMap (·.tbl)), (acc.reverse.map fun e => (e.h, e.j)).toArray, dr⟩

private theorem idxSpec_isSome {n : Name} : ∀ l : List ConstantInfo,
    (idxSpec l n).isSome = true ↔ ∃ c ∈ l, c.name = n
  | [] => by simp [idxSpec]
  | c :: l => by
    rw [idxSpec]
    by_cases h : c.name == n
    · simp only [h, ↓reduceIte, Option.isSome_some, true_iff]
      exact ⟨c, List.mem_cons_self, beq_iff_eq.mp h⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [idxSpec_isSome l]
      constructor
      · rintro ⟨d, hd, hdn⟩; exact ⟨d, List.mem_cons_of_mem _ hd, hdn⟩
      · rintro ⟨d, hd, hdn⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact absurd (beq_iff_eq.mpr hdn) h
        · exact ⟨d, hd, hdn⟩

private theorem stateOf_contains (acc : List IsoEntry) (dr : List (Nat × Nat × Name)) (m : Name) :
    (stateOf acc dr).idx.contains m = true ↔ ∃ e ∈ acc, e.ci.name = m := by
  unfold stateOf
  simp only
  rw [Std.HashMap.contains_eq_isSome_getElem?, mkFEnvGo_snd, idxSpec_isSome]
  constructor
  · rintro ⟨c, hc, hcn⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact ⟨e, he, hcn⟩
  · rintro ⟨e, he, hen⟩
    exact ⟨e.ci, List.mem_map_of_mem he, hen⟩

/-- One entry: `add` is `firstNamedGo`'s and `droppedGo`'s step. -/
private theorem stateOf_add (acc : List IsoEntry) (dr : List (Nat × Nat × Name)) (e : IsoEntry) :
    (stateOf acc dr).add e.h e.j e.ci e.tbl =
      if (stateOf acc dr).idx.contains e.ci.name then stateOf acc (tagOf e :: dr)
      else stateOf (e :: acc) dr := by
  unfold IsoAcc.add
  split
  · rfl
  · unfold stateOf
    cases ht : e.tbl with
    | some t =>
      simp only [List.length_cons, List.map_cons, List.filterMap_cons, ht, mkFEnvGo, mkTblsGo,
        mkFEnvGo_fst, List.length_map, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.push_toArray]
    | none =>
      simp only [List.length_cons, List.map_cons, List.filterMap_cons, ht, mkFEnvGo,
        mkFEnvGo_fst, List.length_map, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.push_toArray]

private theorem foldl_add (es : List IsoEntry) :
    ∀ (seen : Std.HashSet Name) (acc : List IsoEntry) (dr : List (Nat × Nat × Name)),
      (∀ m, seen.contains m = true ↔ ∃ e ∈ acc, e.ci.name = m) →
      es.foldl (fun a e => a.add e.h e.j e.ci e.tbl) (stateOf acc dr) =
        stateOf (firstNamedGo es seen acc) (droppedGo es seen dr) := by
  induction es with
  | nil => intro _ _ _ _; rfl
  | cons e es ih =>
    intro seen acc dr hinv
    rw [List.foldl_cons, stateOf_add]
    unfold firstNamedGo droppedGo
    have hc : (stateOf acc dr).idx.contains e.ci.name = seen.contains e.ci.name := by
      apply Bool.eq_iff_iff.mpr
      rw [stateOf_contains, hinv]
    rw [hc]
    split
    · exact ih seen acc _ hinv
    · apply ih
      intro m
      rw [Std.HashSet.contains_insert]
      simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
      rw [hinv m]

private theorem isoAccModule_eq (lv : ByteArray) (slot : Nat → ModSlot) (a : IsoAcc) (h : Nat) :
    isoAccModule lv slot a h =
      (entriesOf lv h slot).foldl (fun a e => a.add e.h e.j e.ci e.tbl) a := by
  unfold isoAccModule entriesOf
  split
  · rfl
  · simp only
    rw [List.foldl_filterMap]
    congr
    funext a j
    cases presentAt lv (slot h) (lvlAt lv h) j <;> rfl

/-- **The one pass is the specification's lists**: the kept entries are
the context's (`firstNamed`), the dropped ones `droppedGo`'s. -/
private theorem isoBuild_eq (slot : Nat → ModSlot) (lv : ByteArray) :
    isoBuild slot lv =
      stateOf (firstNamed (isoEntries slot lv)) (droppedGo (isoEntries slot lv) {} []) := by
  unfold isoBuild firstNamed
  have h0 : (⟨0, [], [], {}, {}, #[], []⟩ : IsoAcc) = stateOf [] [] := rfl
  rw [h0, ← foldl_add (isoEntries slot lv) {} [] [] (fun m => by simp)]
  unfold isoEntries
  rw [List.foldl_flatMap]
  congr
  funext a h
  exact isoAccModule_eq lv slot a h

/-- **The one pass's index is the canonical index of the context.** -/
theorem isoBuild_fenv (slot : Nat → ModSlot) (lv : ByteArray) :
    (isoBuild slot lv).fenv = isoIndex slot lv := by
  rw [isoBuild_eq]
  unfold stateOf IsoAcc.fenv isoIndex isoCtx mkFEnv
  simp only [mkFEnvGo_fst, List.length_map]

/-! ## The lookup -/

/-- The index's answer for a name is its first entry, at its position
from the bottom. -/
private theorem idxSpec_entries (n : Name) : ∀ acc : List IsoEntry,
    match idxSpec (acc.map (·.ci)) n with
    | some (c, ci) => ∃ e, acc.reverse[c]? = some e ∧ e.ci = ci ∧
        acc.find? (·.ci.name == n) = some e
    | none => acc.find? (·.ci.name == n) = none
  | [] => by simp [idxSpec]
  | e :: rest => by
    simp only [List.map_cons, idxSpec, List.find?_cons, List.reverse_cons]
    by_cases hn : e.ci.name == n
    · simp only [hn, ↓reduceIte]
      refine ⟨e, ?_, rfl, rfl⟩
      rw [List.getElem?_append_right (by simp)]
      simp
    · simp only [hn, Bool.false_eq_true, ↓reduceIte]
      have ih := idxSpec_entries n rest
      revert ih
      cases hs : idxSpec (rest.map (·.ci)) n with
      | none => exact id
      | some x =>
        obtain ⟨c, ci⟩ := x
        rintro ⟨e', he', hci, hf⟩
        have hlt : c < rest.length := by
          have := idxSpec_lt hs; simpa using this
        refine ⟨e', ?_, hci, hf⟩
        rw [List.getElem?_append_left (by simpa using hlt)]
        exact he'

/-- **The one pass's lookup is the context's.** -/
theorem isoBuild_look (slot : Nat → ModSlot) (lv : ByteArray) :
    (isoBuild slot lv).look = isoLook slot lv := by
  funext n
  rw [isoBuild_eq]
  unfold IsoAcc.look stateOf isoLook
  simp only
  rw [mkFEnvGo_snd, ← firstNamed_find?]
  have key := idxSpec_entries n (firstNamed (isoEntries slot lv))
  revert key
  cases idxSpec ((firstNamed (isoEntries slot lv)).map (·.ci)) n with
  | none => intro h; rw [h]; rfl
  | some x =>
    obtain ⟨c, ci⟩ := x
    rintro ⟨e, he, rfl, hf⟩
    rw [hf]
    simp only [List.getElem?_toArray, List.getElem?_map, he, Option.map_some]

/-! ## The duplicates -/

private theorem sub_firstNamedGo :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (acc : List IsoEntry) (e : IsoEntry),
      e ∈ acc → e ∈ firstNamedGo es seen acc
  | [], _, _, _, h => h
  | x :: es, seen, acc, e, h => by
    unfold firstNamedGo
    split
    · exact sub_firstNamedGo es seen acc e h
    · exact sub_firstNamedGo es _ _ e (List.mem_cons_of_mem _ h)

private theorem sub_droppedGo :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (dr : List (Nat × Nat × Name)) x,
      x ∈ dr → x ∈ droppedGo es seen dr
  | [], _, _, _, h => h
  | e :: es, seen, dr, x, h => by
    unfold droppedGo
    split
    · exact sub_droppedGo es seen _ x (List.mem_cons_of_mem _ h)
    · exact sub_droppedGo es _ dr x h

/-- A dropped presentation is one of the entries'. -/
private theorem mem_droppedGo :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (dr : List (Nat × Nat × Name)) x,
      x ∈ droppedGo es seen dr → x ∈ dr ∨ ∃ e ∈ es, x = tagOf e
  | [], _, _, _, h => .inl h
  | e :: es, seen, dr, x, h => by
    unfold droppedGo at h
    split at h
    · rcases mem_droppedGo es seen _ x h with h | ⟨e', he', rfl⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr ⟨e, List.mem_cons_self, rfl⟩
        · exact .inl h
      · exact .inr ⟨e', List.mem_cons_of_mem _ he', rfl⟩
    · rcases mem_droppedGo es _ dr x h with h | ⟨e', he', rfl⟩
      · exact .inl h
      · exact .inr ⟨e', List.mem_cons_of_mem _ he', rfl⟩

/-- Every entry is kept or dropped. -/
private theorem kept_or_dropped :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (acc : List IsoEntry)
      (dr : List (Nat × Nat × Name)) (e : IsoEntry), e ∈ es →
      e ∈ firstNamedGo es seen acc ∨ tagOf e ∈ droppedGo es seen dr
  | [], _, _, _, _, h => by cases h
  | x :: es, seen, acc, dr, e, h => by
    unfold firstNamedGo droppedGo
    rcases List.mem_cons.mp h with rfl | h
    · split
      · exact .inr (sub_droppedGo es seen _ _ List.mem_cons_self)
      · exact .inl (sub_firstNamedGo es _ _ _ List.mem_cons_self)
    · split
      · exact kept_or_dropped es seen acc _ e h
      · exact kept_or_dropped es _ _ dr e h

/-- **The one pass's duplicates check decides `keysOk`.** -/
theorem isoBuild_keysOk (slot : Nat → ModSlot) (lv : ByteArray) :
    (isoBuild slot lv).keysOk slot = keysOk slot lv := by
  have hlook := isoBuild_look slot lv
  unfold IsoAcc.keysOk
  rw [hlook]
  rw [isoBuild_eq]
  unfold stateOf keysOk
  simp only
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro hd e he
    rcases kept_or_dropped (isoEntries slot lv) {} [] [] e he with hk | hdr
    · -- a kept entry is its name's first
      have hnd := firstNamed_nodup (isoEntries slot lv)
      have hf := find?_of_nodup_mem hnd hk
      rw [firstNamed_find?] at hf
      unfold isoLook
      rw [hf]
      simp
    · exact hd _ hdr
  · intro he x hx
    rcases mem_droppedGo _ _ _ x hx with h | ⟨e, he', rfl⟩
    · cases h
    · exact he e he'

end ConLeche.Cached.Mod
