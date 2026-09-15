module

public import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# The nested block's recursor names are pairwise distinct (task #279)

A nested block stores one recursor per member, under the member's own
`T.rec`, and one per mimic, under `<first member>.rec_1`, `.rec_2`, …
(`NestedParts.mimicRecName`, `ConLeche/Kernel/Inductives/NestedParts.lean`).
The model lane installs those records one after the other, so it needs
to know that the names it installs are *distinct* — the list it folds
over has no duplicates.

Everything here comes from the `Name` arithmetic:

* **decimal notation is injective** (`Nat.toDigits_ten_inj`,
  `Nat.repr_inj`) — read off core's `Nat.ofDigitChars_ten_toDigits`,
  the left inverse of `Nat.toDigits 10`;
* **the index is recoverable** (`Name.appendIndexAfter_inj`): appending
  `_i` to a name's last string component is injective in `i`;
* **an indexed name is never a `.rec`** (`Name.appendIndexAfter_ne_str_rec`):
  its last component contains an underscore, and `"rec"` does not;
* hence the mimics' names are pairwise distinct and distinct from the
  members' own recursor names (`NestedParts.mimicRecName_inj`,
  `NestedParts.mimicRecName_ne_str_rec`,
  `NestedParts.mimicRecNames_nodup`, `nestedRecNames_nodup`).
-/

namespace ConLeche

/-! ## Decimal notation is injective -/

/-- A digit below ten is determined by its character: `digitChar` shifts
it by `'0'` (core's `Nat.toNat_digitChar_of_lt_ten`). -/
theorem Nat.digitChar_inj {a b : Nat} (ha : a < 10) (hb : b < 10)
    (h : Nat.digitChar a = Nat.digitChar b) : a = b := by
  have h' := congrArg Char.toNat h
  rw [Nat.toNat_digitChar_of_lt_ten ha, Nat.toNat_digitChar_of_lt_ten hb] at h'
  omega

/-- **Decimal digit lists are injective**: `Nat.ofDigitChars 10 · 0` is a
left inverse of `Nat.toDigits 10` (core's `Nat.ofDigitChars_ten_toDigits`). -/
theorem Nat.toDigits_ten_inj {m n : Nat} (h : Nat.toDigits 10 m = Nat.toDigits 10 n) : m = n := by
  have h' := congrArg (fun l => Nat.ofDigitChars 10 l 0) h
  simpa using h'

/-- **Decimal notation is injective**: a natural number is determined by
its `repr` — equivalently by `toString`, which is `repr` by `rfl`. -/
theorem Nat.repr_inj {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n :=
  Nat.toDigits_ten_inj (by rw [← Nat.toList_repr, ← Nat.toList_repr, h])

/-- The index appended to a fixed string prefix is recoverable. -/
theorem Nat.toString_append_inj {t : String} {i j : Nat}
    (h : t ++ toString i = t ++ toString j) : i = j :=
  Nat.repr_inj ((String.append_right_inj t).mp h)

/-! ## The indexed names -/

/-- **The appended index is recoverable**: `Name.appendIndexAfter` glues
`"_" ++ toString i` onto the last string component, and decimal notation
is injective. -/
theorem Name.appendIndexAfter_inj {n : Name} {i j : Nat}
    (h : Name.appendIndexAfter n i = Name.appendIndexAfter n j) : i = j := by
  cases n with
  | anonymous =>
    simp only [Name.appendIndexAfter, Name.str.injEq, true_and] at h
    exact Nat.toString_append_inj (t := "_") h
  | str p s =>
    simp only [Name.appendIndexAfter, Name.str.injEq, true_and] at h
    exact Nat.toString_append_inj (t := s ++ "_") h
  | num p k =>
    simp only [Name.appendIndexAfter, Name.str.injEq, true_and] at h
    exact Nat.toString_append_inj (t := "_") h

/-- An underscore in the prefix survives the appended index. -/
theorem Nat.underscore_mem_append_toString {t : String} (i : Nat) (ht : '_' ∈ t.toList) :
    '_' ∈ (t ++ toString i).toList := by
  simp only [String.toList_append, List.mem_append]
  exact Or.inl ht

/-- **An indexed name is never a recursor name**: its last component
contains the underscore `Name.appendIndexAfter` glued in, and `"rec"`
does not. -/
theorem Name.appendIndexAfter_ne_str_rec (n T : Name) (i : Nat) :
    Name.appendIndexAfter n i ≠ T.str "rec" := by
  have key : ∀ {t : String}, '_' ∈ t.toList → t ++ toString i ≠ "rec" := by
    intro t ht h
    exact absurd (h ▸ Nat.underscore_mem_append_toString i ht) (by decide)
  cases n with
  | anonymous =>
    simp only [ne_eq, Name.appendIndexAfter, Name.str.injEq, not_and]
    exact fun _ => key (by decide)
  | str p s =>
    simp only [ne_eq, Name.appendIndexAfter, Name.str.injEq, not_and]
    exact fun _ => key (by simp [String.toList_append])
  | num p k =>
    simp only [ne_eq, Name.appendIndexAfter, Name.str.injEq, not_and]
    exact fun _ => key (by decide)

/-! ## The mimic recursors' names -/

/-- **The mimics' names are distinct**: `T₁.rec_j` determines `j`. -/
theorem NestedParts.mimicRecName_inj (p : NestedParts) {i j : Nat}
    (h : p.mimicRecName i = p.mimicRecName j) : i = j := by
  simp only [NestedParts.mimicRecName] at h
  have := Name.appendIndexAfter_inj h
  omega

/-- **A mimic's name is never a member's own recursor name**: it carries
the appended index. -/
theorem NestedParts.mimicRecName_ne_str_rec (p : NestedParts) (T : Name) (j : Nat) :
    p.mimicRecName j ≠ T.str "rec" := by
  simp only [NestedParts.mimicRecName]
  exact Name.appendIndexAfter_ne_str_rec _ _ _

/-- The mimics' names, taken over an initial segment of the indices, are
pairwise distinct. -/
theorem NestedParts.mimicRecNames_nodup (p : NestedParts) (n : Nat) :
    (((List.range n).map p.mimicRecName)).Nodup :=
  List.pairwise_map.mpr (List.nodup_range.imp (fun h heq => h (p.mimicRecName_inj heq)))

/-- **The stored recursor names have no duplicates**: the members' own
`T.rec` (distinct because the members are) followed by the mimics'
(distinct by `mimicRecName_inj`, and never a `.rec` by
`mimicRecName_ne_str_rec`). -/
theorem nestedRecNames_nodup {p : NestedParts} {names : List Name}
    (hnd : names.Nodup) (n : Nat) :
    (names.map (fun T => T.str "rec") ++ (List.range n).map p.mimicRecName).Nodup := by
  refine List.nodup_append.mpr ⟨?_, p.mimicRecNames_nodup n, ?_⟩
  · exact List.pairwise_map.mpr
      (hnd.imp (fun h heq => h ((Name.str.injEq _ _ _ _ ▸ heq : _ ∧ _)).1))
  · intro a ha b hb
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact fun heq => p.mimicRecName_ne_str_rec T j heq.symm

end ConLeche
