module

public import ConLeche.Frontend.Olean.Merge
import Std.Data.HashMap.Lemmas

/-!
# The merge of a closure's constants

`mergeAll_ok`: where the merge succeeds, every constant of every module stands in the
merged map, itself or a constant that may stand for it (`Stands`: `subsumesInfo`'s rule,
of the same name and statement); every constant in the map is a module's, under its own
name; and the order lists the map's names, each once.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-- What Lean's `subsumesInfo` lets a kind stand for: a theorem for a theorem of its
block, a theorem for its axiom, an axiom for an axiom. -/
@[expose] def KindStands (n : Name) : CKind → CKind → Prop
  | .thm _ a, .thm _ a' => a = a'
  | .thm _ a, .ax u => a = [n] ∧ u = false
  | .ax u, .ax u' => u = u'
  | _, _ => False

/-- **`c'` may stand for `c`**: it is `c`, or a constant of its name and statement whose
kind may stand for `c`'s. -/
@[expose] def Stands (c' c : CEntry) : Prop :=
  c' = c ∨ (c'.name = c.name ∧ c'.type = c.type ∧ c'.levelParams = c.levelParams ∧
    KindStands c.name c'.kind c.kind)

theorem Stands.refl (c : CEntry) : Stands c c := .inl rfl

theorem KindStands.trans {n : Name} {a b c : CKind} (h1 : KindStands n a b) (h2 : KindStands n b c) :
    KindStands n a c := by
  cases a <;> cases b <;> cases c <;> simp_all [KindStands]

theorem Stands.trans {a b c : CEntry} (h1 : Stands a b) (h2 : Stands b c) : Stands a c := by
  rcases h1 with rfl | ⟨n1, t1, l1, k1⟩
  · exact h2
  rcases h2 with rfl | ⟨n2, t2, l2, k2⟩
  · exact .inr ⟨n1, t1, l1, k1⟩
  · refine .inr ⟨n1.trans n2, t1.trans t2, l1.trans l2, ?_⟩
    rw [n2] at k1
    exact k1.trans k2

theorem subsumes_stands {m : Std.HashMap Name CEntry} {a b : CEntry} (h : subsumes m a b = true) :
    Stands a b := by
  simp only [subsumes, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, ht⟩, hl⟩, hk⟩ := h
  refine .inr ⟨hn, ht, hl, ?_⟩
  revert hk
  cases a.kind <;> cases b.kind <;> simp [KindStands] <;> intros <;> simp_all

/-- What the merge keeps, of the constants `seen` so far. -/
structure MergeInv (seen : List CEntry) (mg : Merged) : Prop where
  names : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n
  order : ∀ n : Name, n ∈ mg.order ↔ mg.map.contains n = true
  nodup : mg.order.toList.Nodup
  keep : ∀ c : CEntry, c ∈ seen → ∃ c', mg.map[c.name]? = some c' ∧ Stands c' c
  source : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c ∈ seen

theorem MergeInv.empty : MergeInv [] ({} : Merged) where
  names n c h := by simp at h
  order n := by simp
  nodup := by simp
  keep c h := by simp at h
  source n c h := by simp at h

theorem contains_of_getElem {m : Std.HashMap Name CEntry} {n : Name} {c : CEntry}
    (h : m[n]? = some c) : m.contains n = true := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, h]
  rfl

/-- One constant merged. -/
theorem MergeInv.step {seen : List CEntry} {mg mg' : Merged} {c : CEntry} (hi : MergeInv seen mg)
    (h : mergeEntry mg c = .ok mg') : MergeInv (seen ++ [c]) mg' := by
  obtain ⟨map, order⟩ := mg
  unfold mergeEntry at h
  simp only at h
  split at h
  · -- a new name
    rename_i hn
    cases h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n x hx
      simp only [Std.HashMap.getElem?_insert] at hx
      split at hx
      · cases hx; exact eq_of_beq ‹_›
      · exact hi.names n x hx
    · intro n
      simp only [Array.mem_push, Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hi.order n]
      constructor
      · rintro (h | h)
        · exact .inr h
        · exact .inl h.symm
      · rintro (h | h)
        · exact .inr h.symm
        · exact .inl h
    · have hc : c.name ∉ order := by
        intro hm
        have := (hi.order _).1 hm
        rw [Std.HashMap.contains_eq_isSome_getElem?, hn] at this
        cases this
      simp only [Array.toList_push]
      rw [List.nodup_append]
      refine ⟨hi.nodup, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      rintro rfl
      exact hc (by simpa using hx)
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨c', h1, h2⟩ := hi.keep d hd
        refine ⟨c', ?_, h2⟩
        have hne : (c.name == d.name) = false := by
          cases he : (c.name == d.name)
          · rfl
          · have := eq_of_beq he
            rw [← this, hn] at h1
            cases h1
        simp only [Std.HashMap.getElem?_insert, hne, Bool.false_eq_true, ↓reduceIte]
        exact h1
      · simp only [List.mem_singleton] at hd
        subst hd
        exact ⟨d, by simp, Stands.refl _⟩
    · intro n x hx
      simp only [Std.HashMap.getElem?_insert] at hx
      split at hx
      · cases hx; simp
      · exact List.mem_append_left _ (hi.source n x hx)
  · -- a name stored before
    rename_i prev hn
    split at h
    · rename_i hs
      cases h
      refine ⟨?_, ?_, hi.nodup, ?_, ?_⟩
      · intro n x hx
        simp only [Std.HashMap.getElem?_insert] at hx
        split at hx
        · cases hx; exact eq_of_beq ‹_›
        · exact hi.names n x hx
      · intro n
        simp only [hi.order n, Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
        constructor
        · exact .inr
        · rintro (rfl | h)
          · exact contains_of_getElem hn
          · exact h
      · intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · obtain ⟨c', h1, h2⟩ := hi.keep d hd
          by_cases he : c.name = d.name
          · refine ⟨c, by simp [he], ?_⟩
            rw [← he, hn] at h1
            cases h1
            exact (subsumes_stands hs).trans h2
          · refine ⟨c', ?_, h2⟩
            simp only [Std.HashMap.getElem?_insert, beq_iff_eq, he, ↓reduceIte]
            exact h1
        · simp only [List.mem_singleton] at hd
          subst hd
          exact ⟨d, by simp, Stands.refl _⟩
      · intro n x hx
        simp only [Std.HashMap.getElem?_insert] at hx
        split at hx
        · cases hx; simp
        · exact List.mem_append_left _ (hi.source n x hx)
    · split at h
      · rename_i hs
        cases h
        refine ⟨hi.names, hi.order, hi.nodup, ?_, ?_⟩
        · intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hi.keep d hd
          · simp only [List.mem_singleton] at hd
            subst hd
            exact ⟨prev, hn, subsumes_stands hs⟩
        · intro n x hx
          exact List.mem_append_left _ (hi.source n x hx)
      · cases h

theorem MergeInv.fold {cs : List CEntry} :
    ∀ {seen : List CEntry} {mg mg' : Merged}, MergeInv seen mg → cs.foldlM mergeEntry mg = .ok mg' →
      MergeInv (seen ++ cs) mg' := by
  induction cs with
  | nil =>
    intro seen mg mg' hi h
    cases h
    simpa using hi
  | cons c cs ih =>
    intro seen mg mg' hi h
    simp only [List.foldlM_cons] at h
    cases hc : mergeEntry mg c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok m =>
      simp only [hc, bind, Except.bind] at h
      have := ih (hi.step hc) h
      simpa using this

theorem MergeInv.foldMods {ls : List Loaded} :
    ∀ {seen : List CEntry} {mg mg' : Merged}, MergeInv seen mg →
      ls.foldlM (fun mg l => l.constants.foldlM mergeEntry mg) mg = .ok mg' →
      MergeInv (seen ++ ls.flatMap (·.constants.toList)) mg' := by
  induction ls with
  | nil =>
    intro seen mg mg' hi h
    cases h
    simpa using hi
  | cons l ls ih =>
    intro seen mg mg' hi h
    simp only [List.foldlM_cons] at h
    cases hc : l.constants.foldlM mergeEntry mg with
    | error e => simp [hc, bind, Except.bind] at h
    | ok m =>
      simp only [hc, bind, Except.bind] at h
      rw [← Array.foldlM_toList] at hc
      have := ih (hi.fold hc) h
      simpa using this

/-- **The merge keeps every constant.**  Where it succeeds: every constant of every
module stands in the map, itself or a constant that may stand for it; every constant in
the map is a module's, under its own name; and the order lists the map's names, each
once. -/
theorem mergeAll_ok {ls : Array Loaded} {mg : Merged} (h : mergeAll ls = .ok mg) :
    (∀ l ∈ ls, ∀ c ∈ l.constants, ∃ c', mg.map[c.name]? = some c' ∧ Stands c' c) ∧
      (∀ n c, mg.map[n]? = some c → c.name = n ∧ ∃ l ∈ ls, c ∈ l.constants) ∧
      (∀ n, n ∈ mg.order ↔ mg.map.contains n = true) ∧ mg.order.toList.Nodup := by
  unfold mergeAll at h
  rw [← Array.foldlM_toList] at h
  have hi := MergeInv.empty.foldMods h
  simp only [List.nil_append] at hi
  refine ⟨fun l hl c hc => hi.keep c ?_, fun n c hc => ⟨hi.names n c hc, ?_⟩, hi.order, hi.nodup⟩
  · exact List.mem_flatMap.mpr ⟨l, by simpa using hl, by simpa using hc⟩
  · obtain ⟨l, hl, hm⟩ := List.mem_flatMap.mp (hi.source n c hc)
    exact ⟨l, by simpa using hl, by simpa using hm⟩

end ConLeche.Frontend.Olean
