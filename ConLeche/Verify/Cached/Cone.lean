module

public import ConLeche.Cached.Justify

/-!
# The justification's cone, read

`justifyWhy J fe cv = none` says: the sidecar has a constant of `cv`'s name with `cv`'s statement
up to level names, and there is a set of names, holding everything `cv`'s type reads, each of
whose names is the same constant in both indices (`ConeGood`) and whose constants' laws, tables
and record mates read only names of the set (`ConeClosed`).  The model's step for a justified
axiom reads the sidecar model's values on that set.
-/

public section

namespace ConLeche.Cached

open ConLeche

/-- **A name the two indices share**: the input's copy is the sidecar's (`refinesB`), with the
same projection table. -/
@[expose] def ConeGood (J : Sidecar) (find : Name → Option ConstantInfo)
    (findT : Name → Option ProjTable) (n : Name) : Prop :=
  ∃ ci ci', find n = some ci ∧ J.idx.find? n = some ci' ∧ refinesB ci ci' = true ∧
    tableBeqP (findT n) (J.idx.findTable? n) = true

/-- **A shared cone**: every name of `T` is shared, and what its constant follows reads only names
of `T`. -/
@[expose] def ConeClosed (J : Sidecar) (find : Name → Option ConstantInfo)
    (findT : Name → Option ProjTable) (T : Name → Prop) : Prop :=
  ∀ n, T n → ConeGood J find findT n ∧
    ∀ ci, find n = some ci → ∀ m ∈ entryNeeds J.mates findT ci, T m

/-- **The walk's accept, read** (generalized over the names already compared). -/
theorem coneGo_none_gen (J : Sidecar) (find : Name → Option ConstantInfo)
    (findT : Name → Option ProjTable) :
    ∀ (fuel : Nat) (seen : Std.HashSet Name) (work : List Name),
      coneGo J find findT fuel seen work = none →
      ∃ T : Name → Prop, (∀ n ∈ work, seen.contains n = true ∨ T n) ∧
        ∀ n, T n → ConeGood J find findT n ∧
          ∀ ci, find n = some ci → ∀ m ∈ entryNeeds J.mates findT ci,
            seen.contains m = true ∨ T m := by
  intro fuel seen work
  induction fuel, seen, work using coneGo.induct (J := J) (find := find) (findT := findT) with
  | case1 fuel seen =>
    intro _
    exact ⟨fun _ => False, ⟨fun _ h => absurd h List.not_mem_nil, fun _ (h : False) => h.elim⟩⟩
  | case2 fuel seen n work hs ih =>
    intro h
    rw [coneGo.eq_def] at h
    simp only [hs, ↓reduceIte] at h
    obtain ⟨T, hw, hT⟩ := ih h
    refine ⟨T, fun x hx => ?_, hT⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl hs
    · exact hw x hx
  | case3 seen n work hs =>
    intro h
    rw [coneGo.eq_def] at h
    simp only [hs] at h
    exact nomatch h
  | case4 seen n work hs fuel ci ci' hf' hf hok ih =>
    intro h
    rw [coneGo.eq_def] at h
    simp only [hs, hf, hf', hok, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨T, hw, hT⟩ := ih h
    have hins : ∀ x, (seen.insert n).contains x = true → seen.contains x = true ∨ x = n := by
      intro x hx
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true_iff.mp hx with hx | hx
      · exact .inr (eq_of_beq hx).symm
      · exact .inl hx
    refine ⟨fun x => T x ∨ x = n, fun x hx => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inr (.inr rfl)
      · rcases hw x (List.mem_append_right _ hx) with h' | h'
        · rcases hins x h' with h'' | rfl
          · exact .inl h''
          · exact .inr (.inr rfl)
        · exact .inr (.inl h')
    · rcases hx with hx | rfl
      · obtain ⟨hg, hc⟩ := hT x hx
        refine ⟨hg, fun c hc' m hm => ?_⟩
        rcases hc c hc' m hm with h' | h'
        · rcases hins m h' with h'' | rfl
          · exact .inl h''
          · exact .inr (.inr rfl)
        · exact .inr (.inl h')
      · simp only [Bool.and_eq_true] at hok
        refine ⟨⟨ci, ci', hf, hf', hok.1, hok.2⟩, fun c hc m hm => ?_⟩
        rw [hf] at hc
        obtain rfl := Option.some.inj hc
        rcases hw m (List.mem_append_left _ (Array.mem_toList_iff.mpr hm)) with h' | h'
        · rcases hins m h' with h'' | rfl
          · exact .inl h''
          · exact .inr (.inr rfl)
        · exact .inr (.inl h')
  | case5 seen n work hs fuel ci ci' hf' hf hok =>
    intro h
    rw [coneGo.eq_def] at h
    simp only [hs, hf, hf', Bool.false_eq_true, ↓reduceIte] at h
    simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
    exact nomatch h
  | case6 seen n work hs fuel hne =>
    intro h
    rw [coneGo.eq_def] at h
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    exact nomatch h

/-- **A justified statement**: the sidecar's constant of its name, the same statement up to level
names, and a shared cone holding everything its type reads. -/
theorem justifyWhy_cone {J : Sidecar} {fe : FEnv} {cv : ConstantVal}
    (h : justifyWhy J fe cv = none) :
    ∃ cS, J.idx.find? cv.name = some cS ∧ sameCvUpToLevels cv cS.toConstantVal = true ∧
      ∃ T : Name → Prop, ConeClosed J fe.find? fe.findTable? T ∧
        ∀ n ∈ (needsGo {} #[] cv.type).2, T n := by
  unfold justifyWhy at h
  split at h
  · exact nomatch h
  · next cS hf =>
    split at h
    · exact nomatch h
    · next hs =>
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hs
      split at h
      · next hc =>
        obtain ⟨T, hw, hT⟩ := coneGo_none_gen J fe.find? fe.findTable? _ _ _ hc
        have he : ∀ x, ({} : Std.HashSet Name).contains x = false := fun x => by simp
        refine ⟨cS, hf, by simpa using hs, T, fun n hn => ?_, fun n hn => ?_⟩
        · obtain ⟨hg, hcl⟩ := hT n hn
          refine ⟨hg, fun ci hci m hm => ?_⟩
          rcases hcl ci hci m hm with h' | h'
          · rw [he] at h'; exact nomatch h'
          · exact h'
        · rcases hw n (Array.mem_toList_iff.mpr hn) with h' | h'
          · rw [he] at h'; exact nomatch h'
          · exact h'
      · exact nomatch h

end ConLeche.Cached
