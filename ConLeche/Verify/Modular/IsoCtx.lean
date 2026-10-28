module

public import ConLeche.Verify.Modular.IsoFold
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

/-!
# A module's context from its imports' units has its view's lookups (task #373)

The isolated specification builds module `M`'s context from `M`'s
imports' units alone (`isoCtx`, `ConLeche/Cached/ModIso.lean`): every
constant of every module `M` loads, as `M`'s level presents it, in module
order, each name once.  The store run reads the same constants through
`M`'s view of the store: a name's alternates in the name index, the
first `M` sees (`MBase.pick?`).  When the index lists every unit
constant under its name, in module order (`IdxOk`, decided by `idxOk`),
the two answer alike:

* `pick?_iso` — the view's choice of a name is the context's first
  presentation of it: the same module, the same position, the same
  constant;
* `baseLike_isoCtx` — the context has the view's base lookups
  (`BaseLike`, so `checkDeclsAt_over` applies: the isolated check is the
  view's check);
* `isoCtx_nodup`, `isoCtx_tables_mem` — the context stores each name
  once, and every table of it is found under its structure.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-! ## Positions -/

/-- The lexicographic order on positions (module, position in its unit). -/
@[expose] def lexLt (x y : Nat × Nat) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

theorem lexLt_irrefl (x : Nat × Nat) : ¬ lexLt x x := by
  unfold lexLt; omega

theorem lexLt_trans {x y z : Nat × Nat} (h₁ : lexLt x y) (h₂ : lexLt y z) : lexLt x z := by
  unfold lexLt at *; omega

theorem lexLt_asymm {x y : Nat × Nat} (h₁ : lexLt x y) (h₂ : lexLt y x) : False := by
  unfold lexLt at *; omega

theorem sortedLex_pairwise : ∀ l : List (Nat × Nat), sortedLex l = true → l.Pairwise lexLt
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [sortedLex, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    have ih := sortedLex_pairwise (b :: rest) h.2
    have hab : lexLt a b := h.1
    refine List.Pairwise.cons ?_ ih
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hab
    · exact lexLt_trans hab ((List.pairwise_cons.mp ih).1 y hy)

/-- **The first satisfying element of a strictly sorted list is its
least.** -/
theorem find?_sorted_min {p : Nat × Nat → Bool} :
    ∀ {L : List (Nat × Nat)} {x : Nat × Nat}, L.Pairwise lexLt → L.find? p = some x →
      ∀ y ∈ L, p y = true → x = y ∨ lexLt x y
  | [], _, _, h, _, _, _ => by cases h
  | a :: L, x, hs, h, y, hy, hp => by
    rw [List.find?_cons] at h
    have hs' := List.pairwise_cons.mp hs
    cases ha : p a
    · rw [ha] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [ha] at hp; cases hp
      · exact find?_sorted_min hs'.2 h y hy hp
    · rw [ha] at h
      cases h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact .inl rfl
      · exact .inr (hs'.1 y hy)

/-! ## The index -/

/-- **The store's name index lists every unit constant under its name, in
module order** (decided by `idxOk`). -/
structure IdxOk (S : Store) : Prop where
  sorted : ∀ n, (S.alts n).Pairwise lexLt
  priv : ∀ h j c, h < S.slots.size → (S.slot h).prv.priv[j]? = some c → (h, j) ∈ S.alts c.name
  exp : ∀ h j c, h < S.slots.size → ((S.slot h).exp.at1[j]?).join = some c →
    (h, j) ∈ S.alts c.name

theorem idxOk_spec {S : Store} (hI : idxOk S = true) : IdxOk S := by
  unfold idxOk at hI
  simp only [Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, List.mem_range] at hI
  obtain ⟨hs, hc⟩ := hI
  refine ⟨fun n => ?_, fun h j c hh hj => ?_, fun h j c hh hj => ?_⟩
  · show ((S.mb 0).alts n).Pairwise lexLt
    unfold MBase.alts
    show (match S.idx[baseShard n S.idx.size]? with
      | some m => m.getD n []
      | none => []).Pairwise lexLt
    cases hm : S.idx[baseShard n S.idx.size]? with
    | none => exact .nil
    | some m =>
      simp only
      rw [Std.HashMap.getD_eq_getD_getElem?]
      cases hv : m[n]? with
      | none => exact .nil
      | some v =>
        simp only [Option.getD_some]
        have hm' : m ∈ S.idx := Array.mem_of_getElem? hm
        have := hs m hm' (n, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv)
        exact sortedLex_pairwise v this
  · have hj' : j < (S.slot h).prv.priv.size := by
      rcases Nat.lt_or_ge j (S.slot h).prv.priv.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hj; cases hj
    have := (hc h hh).1 j hj'
    rw [hj] at this
    exact List.contains_iff_mem.mp this
  · have hj' : j < (S.slot h).exp.at1.size := by
      rcases Nat.lt_or_ge j (S.slot h).exp.at1.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hj; cases hj
    have := (hc h hh).2 j hj'
    rw [hj] at this
    exact List.contains_iff_mem.mp this

/-! ## A view's constant is the unit's presentation -/

/-- The unit a store holds for module `h`. -/
@[expose] def _root_.ConLeche.MBase.slotAt (b : MBase) (h : Nat) : ModSlot := ((b.slots[h]?).map Thunk.get).getD {}

theorem MBase.gateOk_eq (b : MBase) (g : Array (Nat × UInt8)) : b.gateOk g = gateOpen b.lvl g := by
  rfl

theorem presentAt_empty (lv : ByteArray) (l : UInt8) (j : Nat) :
    presentAt lv ({} : ModSlot) l j = none := by
  unfold presentAt
  simp

/-- **A view's constant at a position is the unit's presentation at the
viewer's level.** -/
theorem MBase.at?_eq_presentAt (b : MBase) (h j : Nat) :
    b.at? h j = presentAt b.lvl (b.slotAt h) (lvlAt b.lvl h) j := by
  unfold MBase.at? lvlAt MBase.slotAt
  by_cases hl : h < b.lvl.size
  · simp only [hl, ↓reduceDIte]
    by_cases hs : h < b.slots.size
    · simp only [hs, ↓reduceDIte, Array.getElem?_eq_getElem hs, Option.map_some, Option.getD_some]
      unfold presentAt
      split
      · rfl
      · split
        · rw [MBase.gateOk_eq, MBase.gateOk_eq]
          rfl
        · rfl
    · simp only [hs, ↓reduceDIte, Array.getElem?_eq_none (Nat.not_lt.mp hs), Option.map_none,
        Option.getD_none, presentAt_empty]
      split <;> (try split) <;> rfl
  · simp only [hl, ↓reduceDIte]
    unfold presentAt
    simp

theorem Store.mb_slotAt (S : Store) (i h : Nat) : (S.mb i).slotAt h = S.slot h := rfl

theorem Store.mb_lvl_iso (S : Store) (i : Nat) : (S.mb i).lvl = S.lvl i := rfl

theorem Store.mb_alts (S : Store) (i : Nat) (n : Name) : (S.mb i).alts n = S.alts n := rfl

theorem ConstantInfo.name_axiomInfo (ci : ConstantInfo) :
    (ConstantInfo.axiomInfo ci.toConstantVal).name = ci.name := rfl

/-- A presentation is of a constant the unit has at that position, under
its name: an installed constant, or an exported presentation (the
constant or the assumption of its statement). -/
theorem presentAt_some {lv : ByteArray} {s : ModSlot} {l : UInt8} {j : Nat} {c : ConstantInfo}
    (h : presentAt lv s l j = some c) :
    j < posCount s l ∧
      ((l = 2 ∧ s.prv.priv[j]? = some c) ∨
       (l ≠ 2 ∧ ∃ ci, (s.exp.at1[j]?).join = some ci ∧ c.name = ci.name)) := by
  unfold presentAt at h
  unfold posCount
  by_cases h2 : l = 2
  · subst h2
    have h' : s.prv.priv[j]? = some c := h
    have hj : j < s.prv.priv.size := by
      rcases Nat.lt_or_ge j s.prv.priv.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at h'; cases h'
    exact ⟨hj, .inl ⟨rfl, h'⟩⟩
  · have h2' : (l == 2) = false := beq_false_of_ne h2
    simp only [h2', Bool.false_eq_true, ↓reduceIte] at h ⊢
    split at h
    · cases ha : (s.exp.at1[j]?).join with
      | none => rw [ha] at h; cases h
      | some ci =>
        rw [ha] at h
        simp only at h
        have hj : j < s.exp.at1.size := by
          rcases Nat.lt_or_ge j s.exp.at1.size with hl | hl
          · exact hl
          · rw [Array.getElem?_eq_none hl] at ha; cases ha
        refine ⟨hj, .inr ⟨h2, ci, rfl, ?_⟩⟩
        split at h
        · split at h
          · cases h; rfl
          · cases h; rfl
        · cases h
    · cases h

/-- **Every constant a view sees at a position is an alternate of its
name.** -/
theorem IdxOk.mem_alts {S : Store} (hI : IdxOk S) {i h j : Nat} {c : ConstantInfo}
    (hat : (S.mb i).at? h j = some c) : (h, j) ∈ S.alts c.name := by
  have hs : h < S.slots.size := by
    rcases Nat.lt_or_ge h S.slots.size with hl | hl
    · exact hl
    · exfalso
      rw [MBase.at?_eq_presentAt] at hat
      have : (S.mb i).slotAt h = {} := by
        show (Option.map Thunk.get S.slots[h]?).getD {} = {}
        rw [Array.getElem?_eq_none hl]; rfl
      rw [this, presentAt_empty] at hat
      cases hat
  rw [MBase.at?_eq_presentAt, Store.mb_slotAt] at hat
  rcases (presentAt_some hat).2 with ⟨-, hp⟩ | ⟨-, ci, ha, hn⟩
  · exact hI.priv h j c hs hp
  · rw [hn]; exact hI.exp h j ci hs ha

/-! ## The view's choice -/

/-- Does the viewer see a constant named `n` at a position. -/
@[expose] def selP (b : MBase) (n : Name) (x : Nat × Nat) : Bool :=
  match b.at? x.1 x.2 with
  | some c => c.name == n
  | none => false

theorem pickIn_eq (b : MBase) (n : Name) :
    ∀ L : List (Nat × Nat), b.pickIn n L =
      (L.find? (selP b n)).bind fun x => (b.at? x.1 x.2).map fun c => (x.1, x.2, c)
  | [] => rfl
  | (h, j) :: rest => by
    unfold MBase.pickIn
    rw [List.find?_cons]
    unfold selP
    simp only
    cases hat : b.at? h j with
    | none => simp only; exact pickIn_eq b n rest
    | some ci =>
      simp only
      by_cases hn : (ci.name == n) = true
      · simp [hn, hat]
      · simp only [Bool.not_eq_true] at hn
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
        exact pickIn_eq b n rest

/-! ## The entries -/

theorem mem_isoEntries {slot : Nat → ModSlot} {lv : ByteArray} {e : IsoEntry} :
    e ∈ isoEntries slot lv ↔ e.h < lv.size ∧ e.j < posCount (slot e.h) (lvlAt lv e.h) ∧
      presentAt lv (slot e.h) (lvlAt lv e.h) e.j = some e.ci ∧
      e.tbl = entryTbl e.ci (presentTbl (slot e.h) (lvlAt lv e.h) e.j) := by
  obtain ⟨h, j, ci, tbl⟩ := e
  unfold isoEntries entriesOf
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h', hh', j', hj', ci', hp, he⟩
    cases he
    exact ⟨hh', hj', hp, rfl⟩
  · rintro ⟨hh, hj, hp, ht⟩
    exact ⟨h, hh, j, hj, ci, hp, by rw [ht]⟩

theorem isoEntries_sorted (slot : Nat → ModSlot) (lv : ByteArray) :
    (isoEntries slot lv).Pairwise fun e e' => lexLt (e.h, e.j) (e'.h, e'.j) := by
  unfold isoEntries
  rw [List.pairwise_flatMap]
  refine ⟨fun h _ => ?_, ?_⟩
  · unfold entriesOf
    rw [List.pairwise_filterMap]
    refine List.pairwise_lt_range.imp ?_
    intro a a' ha b hb b' hb'
    simp only [Option.map_eq_some_iff] at hb hb'
    obtain ⟨_, _, rfl⟩ := hb
    obtain ⟨_, _, rfl⟩ := hb'
    exact .inr ⟨rfl, ha⟩
  · refine List.pairwise_lt_range.imp ?_
    intro h h' hh x hx y hy
    unfold entriesOf at hx hy
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at hx hy
    obtain ⟨_, _, _, _, rfl⟩ := hx
    obtain ⟨_, _, _, _, rfl⟩ := hy
    exact .inl hh

/-- **The first entry of a name is the least position the viewer sees it
at.** -/
theorem find?_isoEntries_min {slot : Nat → ModSlot} {lv : ByteArray} {n : Name} {e : IsoEntry}
    (h : (isoEntries slot lv).find? (·.ci.name == n) = some e) :
    ∀ e' ∈ isoEntries slot lv, e'.ci.name = n → (e.h, e.j) = (e'.h, e'.j) ∨
      lexLt (e.h, e.j) (e'.h, e'.j) := by
  have key : ∀ (L : List IsoEntry), L.Pairwise (fun e e' => lexLt (e.h, e.j) (e'.h, e'.j)) →
      L.find? (·.ci.name == n) = some e →
      ∀ e' ∈ L, e'.ci.name = n → (e.h, e.j) = (e'.h, e'.j) ∨ lexLt (e.h, e.j) (e'.h, e'.j) := by
    intro L
    induction L with
    | nil => intro _ h; cases h
    | cons a L ih =>
      intro hs hf e' he' hn
      rw [List.find?_cons] at hf
      have hs' := List.pairwise_cons.mp hs
      by_cases ha : (a.ci.name == n) = true
      · rw [ha] at hf
        cases hf
        rcases List.mem_cons.mp he' with rfl | he'
        · exact .inl rfl
        · exact .inr (hs'.1 e' he')
      · simp only [Bool.not_eq_true] at ha
        rw [ha] at hf
        rcases List.mem_cons.mp he' with rfl | he'
        · rw [hn] at ha; simp at ha
        · exact ih hs'.2 hf e' he' hn
  exact key _ (isoEntries_sorted slot lv) h

/-- A position the viewer sees a constant at is an entry. -/
theorem entry_of_at? {S : Store} {i h j : Nat} {c : ConstantInfo}
    (hat : (S.mb i).at? h j = some c) :
    ⟨h, j, c, entryTbl c (presentTbl (S.slot h) (lvlAt (S.lvl i) h) j)⟩ ∈
      isoEntries S.slot (S.lvl i) := by
  rw [MBase.at?_eq_presentAt, Store.mb_slotAt, Store.mb_lvl_iso] at hat
  refine mem_isoEntries.mpr ⟨?_, (presentAt_some hat).1, hat, rfl⟩
  rcases Nat.lt_or_ge h (S.lvl i).size with hl | hl
  · exact hl
  · have : lvlAt (S.lvl i) h = 0 := by unfold lvlAt; simp [Nat.not_lt.mpr hl]
    rw [this] at hat
    unfold presentAt at hat
    simp at hat

/-- An entry is a position the viewer sees its constant at. -/
theorem at?_of_entry {S : Store} {i : Nat} {e : IsoEntry} (he : e ∈ isoEntries S.slot (S.lvl i)) :
    (S.mb i).at? e.h e.j = some e.ci := by
  rw [MBase.at?_eq_presentAt, Store.mb_slotAt, Store.mb_lvl_iso]
  exact (mem_isoEntries.mp he).2.2.1

/-- **The view's choice of a name is the first presentation of it in the
viewer's context**: the same module, position and constant. -/
theorem pick?_iso {S : Store} (hI : IdxOk S) (i : Nat) (n : Name) :
    (S.mb i).pick? n = ((isoEntries S.slot (S.lvl i)).find? (·.ci.name == n)).map
      fun e => (e.h, e.j, e.ci) := by
  unfold MBase.pick?
  rw [pickIn_eq, Store.mb_alts]
  cases hA : (S.alts n).find? (selP (S.mb i) n) with
  | none =>
    cases hB : (isoEntries S.slot (S.lvl i)).find? (·.ci.name == n) with
    | none => rfl
    | some e =>
      exfalso
      have he := List.mem_of_find?_eq_some hB
      have hn : e.ci.name = _ := beq_iff_eq.mp (by simpa using List.find?_some hB)
      have hat := at?_of_entry he
      have hm : (e.h, e.j) ∈ S.alts n := hn ▸ hI.mem_alts hat
      have := List.find?_eq_none.mp hA _ hm
      apply this
      unfold selP; simp only; rw [hat]; exact beq_iff_eq.mpr hn
  | some x =>
    have hx := List.mem_of_find?_eq_some hA
    have hpx := List.find?_some hA
    unfold selP at hpx
    cases hat : (S.mb i).at? x.1 x.2 with
    | none => rw [hat] at hpx; cases hpx
    | some c =>
      rw [hat] at hpx
      have hcn := beq_iff_eq.mp hpx
      have hex := entry_of_at? hat
      cases hB : (isoEntries S.slot (S.lvl i)).find? (·.ci.name == n) with
      | none =>
        exfalso
        exact List.find?_eq_none.mp hB _ hex (beq_iff_eq.mpr hcn)
      | some e =>
        have he := List.mem_of_find?_eq_some hB
        have hn : e.ci.name = _ := beq_iff_eq.mp (by simpa using List.find?_some hB)
        have hate := at?_of_entry he
        -- x is least among the alternates, e among the entries
        have h₁ := find?_sorted_min (hI.sorted n) hA (e.h, e.j)
          (hn ▸ hI.mem_alts hate) (by unfold selP; simp only; rw [hate]; exact beq_iff_eq.mpr hn)
        have h₂ := find?_isoEntries_min hB _ hex hcn
        have hxe : x = (e.h, e.j) := by
          rcases h₁ with h₁ | h₁
          · exact h₁
          · rcases h₂ with h₂ | h₂
            · exact h₂.symm
            · exact (lexLt_asymm h₁ h₂).elim
        subst hxe
        simp only [Option.bind_some, Option.map_some]
        rw [hate]
        rfl

/-! ## Each name once -/

theorem firstNamedGo_find? :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (acc : List IsoEntry),
      (∀ m, seen.contains m = true ↔ ∃ e ∈ acc, e.ci.name = m) → ∀ n,
      (firstNamedGo es seen acc).find? (·.ci.name == n) =
        if seen.contains n then acc.find? (·.ci.name == n) else es.find? (·.ci.name == n)
  | [], seen, acc, hinv, n => by
    unfold firstNamedGo
    split
    · rfl
    · rename_i hn
      show _ = none
      rw [List.find?_eq_none]
      intro e he hen
      exact hn ((hinv n).mpr ⟨e, he, beq_iff_eq.mp hen⟩)
  | e :: es, seen, acc, hinv, n => by
    unfold firstNamedGo
    split
    · rename_i hs
      rw [firstNamedGo_find? es seen acc hinv n]
      split
      · rfl
      · rename_i hn
        rw [List.find?_cons]
        have : (e.ci.name == n) = false := by
          refine beq_false_of_ne fun h => hn ?_
          rw [← h]; exact hs
        rw [this]
    · rename_i hs
      have hinv' : ∀ m, (seen.insert e.ci.name).contains m = true ↔
          ∃ e' ∈ e :: acc, e'.ci.name = m := by
        intro m
        rw [Std.HashSet.contains_insert]
        simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
        rw [hinv m]
      rw [firstNamedGo_find? es _ _ hinv' n, Std.HashSet.contains_insert]
      by_cases hn : e.ci.name = n
      · subst hn
        simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, List.find?_cons]
        simp [hs]
      · have hne : (e.ci.name == n) = false := beq_false_of_ne hn
        simp only [hne, Bool.false_or, List.find?_cons]

theorem firstNamedGo_nodup :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (acc : List IsoEntry),
      (∀ m, seen.contains m = true ↔ ∃ e ∈ acc, e.ci.name = m) →
      (acc.map (·.ci.name)).Nodup → ((firstNamedGo es seen acc).map (·.ci.name)).Nodup
  | [], _, _, _, hnd => hnd
  | e :: es, seen, acc, hinv, hnd => by
    unfold firstNamedGo
    split
    · exact firstNamedGo_nodup es seen acc hinv hnd
    · rename_i hs
      have hinv' : ∀ m, (seen.insert e.ci.name).contains m = true ↔
          ∃ e' ∈ e :: acc, e'.ci.name = m := by
        intro m
        rw [Std.HashSet.contains_insert]
        simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, exists_eq_or_imp]
        rw [hinv m]
      refine firstNamedGo_nodup es _ _ hinv' ?_
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => hs ?_, hnd⟩
      obtain ⟨e', he', hen⟩ := List.mem_map.mp hm
      exact (hinv _).mpr ⟨e', he', hen⟩

theorem mem_firstNamedGo :
    ∀ (es : List IsoEntry) (seen : Std.HashSet Name) (acc : List IsoEntry) (e : IsoEntry),
      e ∈ firstNamedGo es seen acc → e ∈ acc ∨ e ∈ es
  | [], _, _, _, h => .inl h
  | x :: es, seen, acc, e, h => by
    unfold firstNamedGo at h
    split at h
    · rcases mem_firstNamedGo es seen acc e h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases mem_firstNamedGo es _ _ e h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem firstNamed_find? (es : List IsoEntry) (n : Name) :
    (firstNamed es).find? (·.ci.name == n) = es.find? (·.ci.name == n) := by
  unfold firstNamed
  rw [firstNamedGo_find? es {} [] (fun m => by simp) n]
  simp

theorem firstNamed_nodup (es : List IsoEntry) : ((firstNamed es).map (·.ci.name)).Nodup :=
  firstNamedGo_nodup es {} [] (fun m => by simp) List.nodup_nil

theorem mem_firstNamed {es : List IsoEntry} {e : IsoEntry} (h : e ∈ firstNamed es) : e ∈ es := by
  rcases mem_firstNamedGo es {} [] e h with h | h
  · cases h
  · exact h

/-! ## The tables -/

theorem entryTbl_name {ci : ConstantInfo} {t : Option ProjTable} {t' : ProjTable}
    (h : entryTbl ci t = some t') : t'.structName = ci.name := by
  unfold entryTbl at h
  split at h
  · obtain ⟨_, ht⟩ := Option.filter_eq_some_iff.mp h
    exact beq_iff_eq.mp ht
  · cases h

theorem isoEntries_tbl {slot : Nat → ModSlot} {lv : ByteArray} {e : IsoEntry}
    (he : e ∈ isoEntries slot lv) {t : ProjTable} (ht : e.tbl = some t) : t.structName = e.ci.name := by
  rw [(mem_isoEntries.mp he).2.2.2] at ht
  exact entryTbl_name ht

/-- In a list of distinct names whose tables are named by their entry,
a table's lookup is the table of the entry of its name. -/
theorem filterMap_tbl_find? (T : Name) :
    ∀ (L : List IsoEntry), (L.map (·.ci.name)).Nodup →
      (∀ e ∈ L, ∀ t, e.tbl = some t → t.structName = e.ci.name) →
      (L.filterMap (·.tbl)).find? (·.structName == T) = (L.find? (·.ci.name == T)).bind (·.tbl)
  | [], _, _ => rfl
  | e :: L, hnd, hn => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := filterMap_tbl_find? T L hnd.2 fun e' he' => hn e' (List.mem_cons_of_mem _ he')
    rw [List.filterMap_cons, List.find?_cons]
    cases ht : e.tbl with
    | none =>
      simp only
      rw [ih]
      by_cases heT : e.ci.name = T
      · simp only [heT, beq_self_eq_true, Option.bind_some, ht]
        have : L.find? (·.ci.name == T) = none := by
          rw [List.find?_eq_none]
          intro x hx hxT
          exact hnd.1 (List.mem_map.mpr ⟨x, hx, (beq_iff_eq.mp hxT).trans heT.symm⟩)
        rw [this]; rfl
      · simp [beq_false_of_ne heT]
    | some t =>
      have htn := hn e List.mem_cons_self t ht
      simp only [List.find?_cons, htn]
      by_cases heT : e.ci.name = T
      · simp [heT, ht]
      · simp only [beq_false_of_ne heT]
        exact ih

/-! ## The context -/

theorem isoCtx_find? (slot : Nat → ModSlot) (lv : ByteArray) (n : Name) :
    (isoCtx slot lv).find? n = ((isoEntries slot lv).find? (·.ci.name == n)).map (·.ci) := by
  unfold isoCtx Env.find?
  simp only
  rw [List.find?_map]
  exact congrArg _ (firstNamed_find? _ n)

theorem isoCtx_tables_find? (slot : Nat → ModSlot) (lv : ByteArray) (T : Name) :
    (isoCtx slot lv).tables.find? (·.structName == T) =
      ((isoEntries slot lv).find? (·.ci.name == T)).bind (·.tbl) := by
  unfold isoCtx
  simp only
  rw [filterMap_tbl_find? T _ (firstNamed_nodup _)
    (fun e he t ht => isoEntries_tbl (mem_firstNamed he) ht), firstNamed_find?]

/-- **The context stores each name once.** -/
theorem isoCtx_nodup (slot : Nat → ModSlot) (lv : ByteArray) :
    ((isoCtx slot lv).consts.map (·.name)).Nodup := by
  unfold isoCtx
  simp only [List.map_map]
  exact firstNamed_nodup _

theorem find?_of_nodup_mem {L : List IsoEntry} (hnd : (L.map (·.ci.name)).Nodup) {e : IsoEntry}
    (he : e ∈ L) : L.find? (·.ci.name == e.ci.name) = some e := by
  induction L with
  | nil => cases he
  | cons a L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have hne : (a.ci.name == e.ci.name) = false :=
        beq_false_of_ne fun h => hnd.1 (List.mem_map.mpr ⟨e, he, h.symm⟩)
      rw [hne]
      exact ih hnd.2 he

/-- **Every table of the context is found under its structure.** -/
theorem isoCtx_tables_mem (slot : Nat → ModSlot) (lv : ByteArray) :
    ∀ t ∈ (isoCtx slot lv).tables, (isoCtx slot lv).findTable? t.structName = some t := by
  intro t ht
  unfold isoCtx at ht
  simp only [List.mem_filterMap] at ht
  obtain ⟨e, he, het⟩ := ht
  have hes := mem_firstNamed he
  have htn := isoEntries_tbl hes het
  have hnd := firstNamed_nodup (isoEntries slot lv)
  have hf := find?_of_nodup_mem hnd he
  rw [firstNamed_find?] at hf
  unfold Env.findTable?
  rw [isoCtx_find?, isoCtx_tables_find?, htn, hf]
  simp [het]

/-- **The context from the imports' units has the view's base
lookups.** -/
theorem baseLike_isoCtx {S : Store} (hI : IdxOk S) (i : Nat) :
    BaseLike (isoCtx S.slot (S.lvl i)) (S.mb i) := by
  refine ⟨fun n => ?_, fun T => ?_⟩
  · rw [isoCtx_find?]
    unfold MBase.find?
    rw [pick?_iso hI]
    cases (isoEntries S.slot (S.lvl i)).find? (·.ci.name == n) <;> rfl
  · rw [isoCtx_tables_find?]
    unfold MBase.findTable?
    rw [pick?_iso hI]
    cases hB : (isoEntries S.slot (S.lvl i)).find? (·.ci.name == T) with
    | none => rfl
    | some e =>
      have he := List.mem_of_find?_eq_some hB
      have hn : e.ci.name = _ := beq_iff_eq.mp (by simpa using List.find?_some hB)
      obtain ⟨hh, -, hp, ht⟩ := mem_isoEntries.mp he
      simp only [Option.map_some, Option.bind_some]
      rw [ht]
      have hs : e.h < S.slots.size := by
        rcases Nat.lt_or_ge e.h S.slots.size with hl | hl
        · exact hl
        · exfalso
          have : S.slot e.h = {} := by
            unfold Store.slot; rw [Array.getElem?_eq_none hl]; rfl
          rw [this, presentAt_empty] at hp
          cases hp
      have hl : e.h < (S.mb i).lvl.size := hh
      cases hci : e.ci with
      | indInfo cv caps =>
        have hs' : e.h < (S.mb i).slots.size := hs
        simp only [hs', ↓reduceDIte, hl]
        unfold entryTbl presentTbl lvlAt
        rw [← hci, hn]
        simp only [Store.mb_lvl_iso] at hl
        simp only [hl, ↓reduceDIte]
        have hsl : S.slot e.h = (S.slots[e.h]'hs).get := by
          unfold Store.slot; rw [Array.getElem?_eq_getElem hs]; rfl
        rw [hsl]
        show _ = (match (if (S.lvl i)[e.h] == 2 then (S.slots[e.h]'hs).get.prv.tbls[e.j]?
            else (S.slots[e.h]'hs).get.exp.tbls[e.j]?).join with
          | some t => if (t.structName == T) = true then some t else none
          | none => none)
        by_cases h2 : ((S.lvl i)[e.h] == 2) = true
        · simp only [h2, ↓reduceIte]
          cases ((S.slots[e.h]'hs).get.prv.tbls[e.j]?).join <;> simp [Option.filter, hci]
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          cases ((S.slots[e.h]'hs).get.exp.tbls[e.j]?).join <;> simp [Option.filter, hci]
      | _ =>
        unfold entryTbl
        simp only

end ConLeche.Cached.Mod

namespace ConLeche.Cached.Mod

open ConLeche

/-- **The one-store-many-views check is the isolated check**: when the
store's name index lists every unit constant under its name in module
order, module `i` checked at its view of the store and checked in
isolation — the declaration fold from the canonical index of the
context built from its imports' units alone — give the same verdict:
the same error at the same position, or the same installed constants and
tables (over that context). -/
theorem checkAtView_isolated {S : Store} (hI : IdxOk S) (mode : CheckMode)
    (pins : List NatOpPinSet) (i : Nat) (ds : Array Declaration) :
    checkModuleIsolated mode pins S.slot (S.lvl i) ds =
      (checkAtView mode pins (S.mb i) ds).map (Env.over · (isoCtx S.slot (S.lvl i))) :=
  checkDeclsAt_over (baseLike_isoCtx hI i) ds

end ConLeche.Cached.Mod
