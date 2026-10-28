module

public import ConLeche.Verify.Modular.IsoCtx
import ConLeche.Verify.EnvBound
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

/-!
# The isolated context's index, in one pass (task #373)

The specification of a module's isolated index is the canonical index
of its context (`isoIndex = mkFEnv (isoCtx …)`): the presented
constants listed, each name's first kept, then indexed.  The index that
runs (`isoIndexFast`) builds the same index in one pass over the units,
deciding "first of its name" by the index under construction and
inserting in the same order, so the two are EQUAL (`isoIndex_eq_fast`,
`@[csimp]`): the hash maps' insertions are the same sequence.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- The state `isoIndexFast` holds after the entries `acc` were kept
(newest first). -/
@[expose] def stateOf (acc : List IsoEntry) : IsoAcc :=
  ⟨acc.length, acc.map (·.ci), acc.filterMap (·.tbl), (mkFEnvGo (acc.map (·.ci))).2,
    mkTblsGo (acc.filterMap (·.tbl))⟩

theorem idxSpec_isSome {n : Name} : ∀ l : List ConstantInfo,
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

theorem stateOf_contains (acc : List IsoEntry) (m : Name) :
    (stateOf acc).idx.contains m = true ↔ ∃ e ∈ acc, e.ci.name = m := by
  unfold stateOf
  simp only
  rw [Std.HashMap.contains_eq_isSome_getElem?, mkFEnvGo_snd, idxSpec_isSome]
  constructor
  · rintro ⟨c, hc, hcn⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact ⟨e, he, hcn⟩
  · rintro ⟨e, he, hen⟩
    exact ⟨e.ci, List.mem_map_of_mem he, hen⟩

/-- One entry: `add` is `firstNamedGo`'s step. -/
theorem stateOf_add (acc : List IsoEntry) (e : IsoEntry) :
    (stateOf acc).add e.ci e.tbl =
      if (stateOf acc).idx.contains e.ci.name then stateOf acc else stateOf (e :: acc) := by
  unfold IsoAcc.add
  split
  · rfl
  · unfold stateOf
    cases ht : e.tbl with
    | some t =>
      simp only [List.length_cons, List.map_cons, List.filterMap_cons, ht, mkFEnvGo, mkTblsGo,
        mkFEnvGo_fst, List.length_map]
    | none =>
      simp only [List.length_cons, List.map_cons, List.filterMap_cons, ht, mkFEnvGo,
        mkFEnvGo_fst, List.length_map]

theorem foldl_add (es : List IsoEntry) :
    ∀ (seen : Std.HashSet Name) (acc : List IsoEntry),
      (∀ m, seen.contains m = true ↔ ∃ e ∈ acc, e.ci.name = m) →
      es.foldl (fun a e => a.add e.ci e.tbl) (stateOf acc) = stateOf (firstNamedGo es seen acc) := by
  induction es with
  | nil => intro _ _ _; rfl
  | cons e es ih =>
    intro seen acc hinv
    rw [List.foldl_cons, stateOf_add]
    unfold firstNamedGo
    have hc : (stateOf acc).idx.contains e.ci.name = seen.contains e.ci.name := by
      apply Bool.eq_iff_iff.mpr
      rw [stateOf_contains, hinv]
    rw [hc]
    split
    · exact ih seen acc hinv
    · rename_i hs
      apply ih
      intro m
      rw [Std.HashSet.contains_insert]
      simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
      rw [hinv m]

theorem isoAccModule_eq (lv : ByteArray) (slot : Nat → ModSlot) (a : IsoAcc) (h : Nat) :
    isoAccModule lv slot a h = (entriesOf lv h slot).foldl (fun a e => a.add e.ci e.tbl) a := by
  unfold isoAccModule entriesOf
  split
  · rfl
  · rw [List.foldl_filterMap]
    congr
    funext a j
    cases presentAt lv (slot h) (lvlAt lv h) j <;> rfl

/-- **The one-pass index is the canonical index of the context.** -/
@[csimp] theorem isoIndex_eq_fast : @isoIndex = @isoIndexFast := by
  funext slot lv
  unfold isoIndex isoIndexFast isoCtx firstNamed
  have h0 : (⟨0, [], [], {}, {}⟩ : IsoAcc) = stateOf [] := rfl
  rw [h0]
  have hf : (List.range lv.size).foldl (isoAccModule lv slot) (stateOf []) =
      stateOf (firstNamedGo (isoEntries slot lv) {} []) := by
    rw [← foldl_add (isoEntries slot lv) {} [] (fun m => by simp)]
    unfold isoEntries
    rw [List.foldl_flatMap]
    congr
    funext a h
    exact isoAccModule_eq lv slot a h
  simp only [hf]
  unfold stateOf mkFEnv
  simp only [mkFEnvGo_fst, List.length_map]

end ConLeche.Cached.Mod
