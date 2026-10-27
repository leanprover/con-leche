module

public import ConLeche.Frontend.Olean.Fast

public section

/-!
# The fast olean decoder's memo (task #371)

The laws of the marks and of `DS` (`ConLeche/Frontend/Olean/Fast.lean`):
fresh marks mark nothing; a mark adds exactly its slot and kind; a value
update changes its own slot of its own array.  `Sized st n` is the
invariant the building pass keeps: every array of the memo is `n` long.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Bytes -/

theorem rdU8_eq (b : ByteArray) (i : Nat) : rdU8 b i = (b.data[i]?).getD 0 := by
  unfold rdU8
  split
  · rename_i h
    have h' : i < b.data.size := h
    rw [ByteArray.getElem_eq_getElem_data, Array.getElem?_eq_getElem h']; rfl
  · rename_i h
    have h' : ¬ i < b.data.size := h
    rw [Array.getElem?_eq_none (by omega)]; rfl

theorem data_zeros (n : Nat) : (zeros n).data = Array.replicate n 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold zeros
    split
    · subst_vars; rfl
    · have := ih (n / 2) (by omega)
      split
      · show ((zeros (n / 2) ++ zeros (n / 2)).data.push 0) = _
        rw [ByteArray.data_append, this, Array.replicate_append_replicate,
          ← Array.replicate_succ]
        congr 1; omega
      · rw [ByteArray.data_append, this, Array.replicate_append_replicate]
        congr 1; omega

theorem size_zeros (n : Nat) : (zeros n).size = n := by
  simp [ByteArray.size, data_zeros]

theorem rdU8_zeros (n i : Nat) : rdU8 (zeros n) i = 0 := by
  rw [rdU8_eq, data_zeros]
  by_cases h : i < n <;> simp [h]

theorem rdU8_set! (b : ByteArray) (s i : Nat) (x : UInt8) :
    rdU8 (b.set! s x) i = if s = i ∧ s < b.size then x else rdU8 b i := by
  cases b with
  | mk d =>
    simp only [rdU8_eq, ByteArray.set!, Array.set!_eq_setIfInBounds, ByteArray.size]
    by_cases h : s < d.size
    · by_cases hi : s = i
      · subst hi; simp [h]
      · simp [hi, Array.getElem?_setIfInBounds_ne hi]
    · simp [h, Array.setIfInBounds]

/-! ## Kinds -/

/-- The four kinds, as mark bits. -/
@[expose] def IsKind (k : UInt8) : Prop := k = kName ∨ k = kLevel ∨ k = kExpr ∨ k = kLevels

theorem kind_and {k k' : UInt8} (hk : IsKind k) (hk' : IsKind k') :
    (k' &&& k != 0) = (k' == k) := by
  unfold IsKind kName kLevel kExpr kLevels at *
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl <;> decide

theorem or_and_ne (m a b : UInt8) :
    ((m ||| a) &&& b != 0) = ((m &&& b != 0) || (a &&& b != 0)) := by
  have : (m ||| a) &&& b = (m &&& b) ||| (a &&& b) := by
    apply UInt8.toBitVec_inj.mp; simp [BitVec.and_or_distrib_right]
  rw [this]
  cases h1 : (m &&& b != 0) <;> cases h2 : (a &&& b != 0) <;> simp_all

/-! ## The marks -/

theorem marked_eq (m : ByteArray) (k : UInt8) (s : Nat) :
    marked m k s = (rdU8 m s &&& k != 0) := rfl

theorem marked_zeros (n : Nat) (k : UInt8) (s : Nat) : marked (zeros n) k s = false := by
  simp [marked_eq, rdU8_zeros]

theorem size_mark (m : ByteArray) (k : UInt8) (s : Nat) : (mark m k s).size = m.size := by
  simp [mark]

theorem marked_mark (m : ByteArray) {k k' : UInt8} (hk : IsKind k)
    (hk' : IsKind k') (s s' : Nat) :
    marked (mark m k s) k' s' =
      (marked m k' s' || (s == s' && k == k' && decide (s < m.size))) := by
  simp only [marked_eq, mark, marksAt, rdU8_set!]
  by_cases e : s = s'
  · subst e
    by_cases hs : s < m.size
    · simp [hs, or_and_ne, kind_and hk' hk]
    · simp [hs]
  · simp [e]

/-! ## The failure bit -/

theorem kind_and_fail {k : UInt8} (hk : IsKind k) : (k &&& 0x80 != 0) = false := by
  unfold IsKind kName kLevel kExpr kLevels at hk
  rcases hk with rfl | rfl | rfl | rfl <;> decide

theorem failedM_mark (m : ByteArray) {k : UInt8} (hk : IsKind k) (s : Nat) :
    failedM (mark m k s) = failedM m := by
  simp only [failedM, mark, marksAt, rdU8_set!]
  by_cases e : s = 0
  · subst e
    by_cases hs : 0 < m.size
    · simp [hs, or_and_ne, kind_and_fail hk]
    · simp [hs]
  · simp [e]

theorem failedM_failM {m : ByteArray} (h : 0 < m.size) : failedM (failM m) = true := by
  simp only [failedM, failM, marksAt, rdU8_set!, h, and_self, ite_true]
  decide

theorem size_failM (m : ByteArray) : (failM m).size = m.size := by
  simp [failM]

theorem failedM_zeros (n : Nat) : failedM (zeros n) = false := by
  simp [failedM, marksAt, rdU8_zeros]

/-! ## The values -/

/-- Every array of the memo is `n` long. -/
structure DS.Sized (st : DS) (n : Nat) : Prop where
  names : st.names.size = n
  levels : st.levels.size = n
  exprs : st.exprs.size = n
  lists : st.lists.size = n

theorem DS.fresh_sized (n : Nat) : (DS.fresh n).Sized n :=
  ⟨by simp [DS.fresh], by simp [DS.fresh], by simp [DS.fresh], by simp [DS.fresh]⟩

theorem DS.setName_sized {st : DS} {n : Nat} (h : st.Sized n) (s : Nat) (v : Name) :
    (st.setName s v).Sized n :=
  ⟨by simp [DS.setName, h.names], h.levels, h.exprs, h.lists⟩
theorem DS.setLevel_sized {st : DS} {n : Nat} (h : st.Sized n) (s : Nat) (v : Level) :
    (st.setLevel s v).Sized n :=
  ⟨h.names, by simp [DS.setLevel, h.levels], h.exprs, h.lists⟩
theorem DS.setExpr_sized {st : DS} {n : Nat} (h : st.Sized n) (s : Nat) (v : Expr) :
    (st.setExpr s v).Sized n :=
  ⟨h.names, h.levels, by simp [DS.setExpr, h.exprs], h.lists⟩
theorem DS.setLevels_sized {st : DS} {n : Nat} (h : st.Sized n) (s : Nat) (v : List Level) :
    (st.setLevels s v).Sized n :=
  ⟨h.names, h.levels, h.exprs, by simp [DS.setLevels, h.lists]⟩

theorem getD_set! {α : Type} (a : Array α) (s i : Nat) (v d : α) :
    (a.set! s v).getD i d = if s = i ∧ s < a.size then v else a.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds]
  by_cases h : s = i
  · subst h
    by_cases hs : s < a.size
    · simp [hs]
    · simp [hs, Array.setIfInBounds]
  · simp [h, Array.getElem?_setIfInBounds_ne h]

end ConLeche.Frontend.Olean
