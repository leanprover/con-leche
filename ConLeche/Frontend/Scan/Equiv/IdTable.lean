module

public import ConLeche.Frontend.Scan.Naive
import Std.Data.HashMap.Lemmas

public section

/-!
# The stream-index table against its naive map (task #261)

`IdTable.get?` is the abstraction of the dense-plus-sparse table to the
partial map it represents, and the three laws below say the table's
operations are the naive map's (`naiveBind`, `naiveSingleton` in
`ConLeche/Frontend/Scan/Naive.lean`): nothing about the dense frontier
or the overflow map is visible through `get?`.  These are the only
facts the semantic layer (`applyLine`) uses about the table.
-/

namespace ConLeche.Frontend

theorem IdTable.get?_empty (i : Nat) : ({} : IdTable α).get? i = none := by
  simp [IdTable.get?]

theorem IdTable.get?_singleton (x : α) (i : Nat) :
    (IdTable.singleton x).get? i = naiveSingleton x i := by
  simp [IdTable.get?, IdTable.singleton, naiveSingleton, naiveBind]

theorem IdTable.get?_insert (t : IdTable α) (i : Nat) (x : α) (j : Nat) :
    (t.insert i x).get? j = naiveBind t.get? i x j := by
  unfold IdTable.insert naiveBind
  by_cases hi : i = t.dense.size
  · subst hi
    simp only [BEq.rfl, ↓reduceIte, IdTable.get?, Array.size_push]
    by_cases hj : j < t.dense.size + 1
    · rw [dif_pos hj, Array.getElem_push]
      by_cases hj' : j < t.dense.size
      · simp [hj', Nat.ne_of_lt hj']
      · have : j = t.dense.size := by omega
        simp [this]
    · have h1 : j ≠ t.dense.size := by omega
      have h2 : ¬ j < t.dense.size := by omega
      simp [hj, h1, h2]
  · have hne : (i == t.dense.size) = false := by simp [hi]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : i < t.dense.size
    · simp only [hlt, ↓reduceDIte, IdTable.get?, Array.size_set]
      by_cases hj : j < t.dense.size
      · simp only [hj, ↓reduceDIte, Array.getElem_set]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji, Ne.symm hji]
      · have : j ≠ i := by omega
        simp [hj, this]
    · simp only [hlt, ↓reduceDIte, IdTable.get?]
      by_cases hj : j < t.dense.size
      · have : j ≠ i := by omega
        simp [hj, this]
      · rw [dif_neg hj, dif_neg hj, Std.HashMap.getElem?_insert]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji, Ne.symm hji]

end ConLeche.Frontend
