module

public import ConLeche.Cached.ModStore

public section

/-!
# A module's context, read off the store (task #370)

A modular run's view of module `i` (`Mod.Store.view`) answers lookups
from the store (`MBase.find?`); this file names the environment those
lookups are the lookups of — `ctxOf`, the module's **context** in the
sense of `ConLeche.Modular.Module` — and proves the agreement:

* `ctxOf_find?` — the context's `Env.find?` is the store's lookup;
* `ctxOf_tables_find?` — its table list answers as the store's table
  lookup, and `ctxOf_findTable?` gated as `Env.findTable?` gates;
* `ctxOf_nodup`, `ctxOf_tables_mem` — every name once, every table
  found under its structure's name.

The context is a list over the store's name index (`shardNames`): every
name of a shard that the shard's hash says lies there, once.  It is a
logical object: nothing computes it.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- The names of the store's index, each in the shard its hash names,
each once. -/
def shardNames (idx : Shards) : List Name :=
  (List.range idx.size).flatMap fun s =>
    ((idx[s]?.map (·.keys)).getD []).filter (fun n => baseShard n idx.size == s)

/-- **The context a store presents to a viewer**: the visible constant of
every name of the index, and the visible table of every name. -/
def ctxOf (mb : MBase) : Env :=
  ⟨(shardNames mb.idx).filterMap mb.find?, (shardNames mb.idx).filterMap mb.findTable?⟩

/-! ## The lookups -/

theorem MBase.pickIn_some {mb : MBase} {n : Name} :
    ∀ {l : List (Nat × Nat)} {h j : Nat} {ci : ConstantInfo}, mb.pickIn n l = some (h, j, ci) →
      ci.name = n ∧ (h, j) ∈ l ∧ mb.at? h j = some ci
  | [], _, _, _, hp => by simp [MBase.pickIn] at hp
  | (h', j') :: rest, h, j, ci, hp => by
    unfold MBase.pickIn at hp
    split at hp
    · rename_i ci' hat
      split at hp
      · rename_i hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        exact ⟨beq_iff_eq.mp hn, List.mem_cons_self, hat⟩
      · obtain ⟨h1, h2, h3⟩ := MBase.pickIn_some hp
        exact ⟨h1, List.mem_cons_of_mem _ h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := MBase.pickIn_some hp
      exact ⟨h1, List.mem_cons_of_mem _ h2, h3⟩

theorem MBase.pick?_some {mb : MBase} {n : Name} {h j : Nat} {ci : ConstantInfo}
    (hp : mb.pick? n = some (h, j, ci)) :
    ci.name = n ∧ (h, j) ∈ mb.alts n ∧ mb.at? h j = some ci :=
  MBase.pickIn_some hp

theorem MBase.find?_some {mb : MBase} {n : Name} {ci : ConstantInfo}
    (hf : mb.find? n = some ci) : ∃ h j, mb.pick? n = some (h, j, ci) := by
  unfold MBase.find? at hf
  split at hf
  · rename_i h j ci' hp
    cases hf
    exact ⟨h, j, hp⟩
  · cases hf

theorem MBase.find?_name {mb : MBase} {n : Name} {ci : ConstantInfo}
    (hf : mb.find? n = some ci) : ci.name = n := by
  obtain ⟨h, j, hp⟩ := MBase.find?_some hf
  exact (MBase.pick?_some hp).1

theorem MBase.find?_eq_none_of_pick? {mb : MBase} {n : Name} (hp : mb.pick? n = none) :
    mb.find? n = none := by
  unfold MBase.find?
  rw [hp]

theorem MBase.findTable?_some {mb : MBase} {T : Name} {t : ProjTable}
    (hf : mb.findTable? T = some t) : t.structName = T ∧ (mb.find? T).isSome = true := by
  unfold MBase.findTable? at hf
  split at hf
  · rename_i h j ci hp
    split at hf
    · split at hf
      · rename_i t' _
        split at hf
        · rename_i hT
          cases hf
          refine ⟨beq_iff_eq.mp hT, ?_⟩
          unfold MBase.find?
          rw [hp]
          rfl
        · cases hf
      · cases hf
    · cases hf
  · cases hf

/-! ## The names -/

theorem shardNames_nodup (idx : Shards) : (shardNames idx).Nodup := by
  unfold shardNames List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun s _ => ?_, ?_⟩
  · cases hs : idx[s]? with
    | none => simp
    | some m => exact (Std.HashMap.nodup_keys (m := m)).filter _
  · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro s s' _ _ hne n h1 m h2 hnm
    subst hnm
    have e1 := (List.mem_filter.mp h1).2
    have e2 := (List.mem_filter.mp h2).2
    simp only [beq_iff_eq] at e1 e2
    exact hne (e1.symm.trans e2)

theorem mem_shardNames_of_alts {mb : MBase} {n : Name} {x : Nat × Nat} (hx : x ∈ mb.alts n) :
    n ∈ shardNames mb.idx := by
  unfold MBase.alts at hx
  unfold shardNames
  split at hx
  · rename_i m hm
    have hs : baseShard n mb.idx.size < mb.idx.size := by
      rcases Nat.lt_or_ge (baseShard n mb.idx.size) mb.idx.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hm; cases hm
    refine List.mem_flatMap.mpr ⟨baseShard n mb.idx.size, List.mem_range.mpr hs, ?_⟩
    rw [hm]
    refine List.mem_filter.mpr ⟨?_, by simp⟩
    have hc : n ∈ m := by
      rw [Std.HashMap.mem_iff_contains]
      cases hc : m.contains n
      · rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false hc] at hx
        cases hx
      · rfl
    exact Std.HashMap.mem_keys.mpr hc
  · cases hx

theorem mem_shardNames_of_pick? {mb : MBase} {n : Name} {h j : Nat} {ci : ConstantInfo}
    (hp : mb.pick? n = some (h, j, ci)) : n ∈ shardNames mb.idx :=
  mem_shardNames_of_alts (MBase.pick?_some hp).2.1

/-! ## Lists of named things -/

/-- In a list of distinct keys, the named results of a partial map are
found under their key. -/
theorem find?_filterMap_named {β : Type} (key : β → Name) (f : Name → Option β)
    (hf : ∀ m b, f m = some b → key b = m) :
    ∀ (L : List Name), L.Nodup → ∀ n,
      (L.filterMap f).find? (fun b => key b == n) = if n ∈ L then f n else none
  | [], _, n => by simp
  | m :: L, hnd, n => by
    have hnd' := List.nodup_cons.mp hnd
    rw [List.filterMap_cons]
    cases hfm : f m with
    | none =>
      simp only
      rw [find?_filterMap_named key f hf L hnd'.2 n]
      by_cases hn : n = m
      · subst hn; simp [hnd'.1, hfm]
      · simp [hn]
    | some b =>
      simp only
      have hk := hf m b hfm
      rw [List.find?_cons]
      by_cases hn : n = m
      · subst hn
        simp [hk, hfm]
      · have hkn : (key b == n) = false := by rw [hk]; exact beq_false_of_ne (Ne.symm hn)
        rw [hkn]
        simp only
        rw [find?_filterMap_named key f hf L hnd'.2 n]
        simp [hn]

/-! ## The context -/

/-- **The context's lookup is the store's.** -/
theorem ctxOf_find? (mb : MBase) (n : Name) : (ctxOf mb).find? n = mb.find? n := by
  unfold ctxOf Env.find?
  simp only
  rw [find?_filterMap_named ConstantInfo.name mb.find?
    (fun _ _ h => MBase.find?_name h) _ (shardNames_nodup _) n]
  split
  · rfl
  · rename_i hn
    cases hf : mb.find? n with
    | none => rfl
    | some ci =>
      obtain ⟨h, j, hp⟩ := MBase.find?_some hf
      exact absurd (mem_shardNames_of_pick? hp) hn

/-- **The context's tables answer as the store's table lookup.** -/
theorem ctxOf_tables_find? (mb : MBase) (T : Name) :
    (ctxOf mb).tables.find? (·.structName == T) = mb.findTable? T := by
  unfold ctxOf
  simp only
  rw [find?_filterMap_named ProjTable.structName mb.findTable?
    (fun _ _ h => (MBase.findTable?_some h).1) _ (shardNames_nodup _) T]
  split
  · rfl
  · rename_i hn
    cases hf : mb.findTable? T with
    | none => rfl
    | some t =>
      have := (MBase.findTable?_some hf).2
      cases hp : mb.find? T with
      | none => rw [hp] at this; cases this
      | some ci =>
        obtain ⟨h, j, hp'⟩ := MBase.find?_some hp
        exact absurd (mem_shardNames_of_pick? hp') hn

/-- The context's gated table lookup is the store's. -/
theorem ctxOf_findTable? (mb : MBase) (T : Name) :
    (ctxOf mb).findTable? T = mb.findTable? T := by
  unfold Env.findTable?
  rw [ctxOf_find?, ctxOf_tables_find?]
  split
  · rfl
  · rename_i hn
    cases hf : mb.findTable? T with
    | none => rfl
    | some t => exact absurd (MBase.findTable?_some hf).2 hn

/-- **Every name of the context once.** -/
theorem ctxOf_nodup (mb : MBase) : ((ctxOf mb).consts.map (·.name)).Nodup := by
  unfold ctxOf
  simp only
  have key : ∀ (L : List Name), L.Nodup → ((L.filterMap mb.find?).map (·.name)).Nodup := by
    intro L hL
    induction L with
    | nil => simp
    | cons m L ih =>
      have hL' := List.nodup_cons.mp hL
      rw [List.filterMap_cons]
      cases hf : mb.find? m with
      | none => exact ih hL'.2
      | some ci =>
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih hL'.2⟩
        rw [MBase.find?_name hf]
        intro hm
        obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hm
        obtain ⟨m', hm', hfm'⟩ := List.mem_filterMap.mp hc
        rw [MBase.find?_name hfm'] at hcn
        exact hL'.1 (hcn ▸ hm')
  exact key _ (shardNames_nodup _)

/-- **Every table of the context is found under its structure.** -/
theorem ctxOf_tables_mem (mb : MBase) :
    ∀ t ∈ (ctxOf mb).tables, (ctxOf mb).findTable? t.structName = some t := by
  intro t ht
  unfold ctxOf at ht
  obtain ⟨m, _, hm⟩ := List.mem_filterMap.mp ht
  rw [ctxOf_findTable?, (MBase.findTable?_some hm).1]
  exact hm

end ConLeche.Cached.Mod
