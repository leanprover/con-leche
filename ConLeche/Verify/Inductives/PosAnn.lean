module

public import ConLeche.Verify.Inductives.PosNodes

public section

/-!
# A forest flattened with PARENT POINTERS (lane NESTIND, session 27)

The node presentation indexes its classes by positions in a flat node
list.  The calls' landing needs every OCCURRENCE of a node to know its
parent occurrence: a hole of a node's frame stack is owned by one
ancestor occurrence, and a kid visited from its parent must inherit the
parent's owners — a flat list of trees cannot tell two occurrences of one
tree apart.  `PosTree.annF` flattens a forest in preorder, each entry the
node and the (1-based) position of its parent entry (`0` at a root):

* `annF_fst` — the nodes are the forest's;
* `annF_spec` — an entry's parent entry is an earlier one having it as a
  kid (or the entry is a root), and every kid of an entry has an entry
  whose parent is it.
-/

namespace ConLeche

mutual
/-- A tree flattened in preorder, the root's parent `par`, the root at
index `off` (so its kids' parent position is `off + 1`). -/
@[expose] def PosTree.ann (par off : Nat) : PosTree → List (PosTree × Nat)
  | .node occ anc key grp kids =>
    (.node occ anc key grp kids, par) :: PosTree.annF (off + 1) (off + 1) kids
/-- A forest flattened in preorder, every root's parent `par`, the first
entry at index `off`. -/
@[expose] def PosTree.annF (par off : Nat) : List PosTree → List (PosTree × Nat)
  | [] => []
  | t :: ts => PosTree.ann par off t ++ PosTree.annF par (off + t.nodes.length) ts
end

mutual
theorem PosTree.ann_fst (par off : Nat) : ∀ (t : PosTree), (t.ann par off).map (·.1) = t.nodes
  | .node occ anc key grp kids => by
    simp only [PosTree.ann, List.map_cons, PosTree.nodes, PosTree.annF_fst]
theorem PosTree.annF_fst (par off : Nat) :
    ∀ (ts : List PosTree), (PosTree.annF par off ts).map (·.1) = PosTree.forest ts
  | [] => rfl
  | t :: ts => by
    simp only [PosTree.annF, List.map_append, PosTree.ann_fst, PosTree.annF_fst, PosTree.forest]
end

theorem PosTree.ann_length (par off : Nat) (t : PosTree) :
    (t.ann par off).length = t.nodes.length := by
  rw [← PosTree.ann_fst par off t, List.length_map]

/-- An entry's parent: a root of the segment, or an earlier entry of the
segment having it as a kid. -/
@[expose] def AnnParOk (par off : Nat) (roots : List PosTree) (S : List (PosTree × Nat)) : Prop :=
  ∀ (q : Nat) (u : PosTree) (p : Nat), S[q]? = some (u, p) →
    (p = par ∧ u ∈ roots) ∨
    (off < p ∧ p ≤ off + q ∧ ∃ e : PosTree × Nat, S[p - 1 - off]? = some e ∧ u ∈ e.1.kids)

/-- Every kid of an entry has a later entry whose parent is it. -/
@[expose] def AnnKidsOk (off : Nat) (S : List (PosTree × Nat)) : Prop :=
  ∀ (q : Nat) (u : PosTree) (p : Nat), S[q]? = some (u, p) → ∀ k ∈ u.kids,
    ∃ q' : Nat, S[q']? = some (k, off + q + 1)

theorem PosTree.height_pos' (t : PosTree) : 0 < t.height := by
  cases t with
  | node occ anc key grp kids => simp [PosTree.height]

/-- A root of a forest has its entry, at the forest's parent. -/
theorem PosTree.annF_root (par off : Nat) : ∀ (ts : List PosTree) (k : PosTree), k ∈ ts →
    ∃ q : Nat, (PosTree.annF par off ts)[q]? = some (k, par)
  | [], _, h => nomatch h
  | t :: ts, k, h => by
    simp only [PosTree.annF]
    rcases List.mem_cons.mp h with rfl | h
    · cases k with
      | node occ anc key grp kids => exact ⟨0, by simp [PosTree.ann]⟩
    · obtain ⟨q, hent⟩ := PosTree.annF_root par (off + t.nodes.length) ts k h
      refine ⟨q + (t.ann par off).length, ?_⟩
      rw [List.getElem?_append_right (by omega), show q + (t.ann par off).length
        - (t.ann par off).length = q by omega]
      exact hent

/-- **The segment facts**, by induction on a height bound. -/
theorem PosTree.ann_spec : ∀ (n : Nat),
    (∀ (t : PosTree), t.height ≤ n → ∀ par off,
      AnnParOk par off [t] (t.ann par off) ∧ AnnKidsOk off (t.ann par off)) ∧
    (∀ (ts : List PosTree), PosTree.forestHeight ts ≤ n → ∀ par off,
      AnnParOk par off ts (PosTree.annF par off ts) ∧ AnnKidsOk off (PosTree.annF par off ts))
  | 0 => by
    refine ⟨fun t ht => ?_, fun ts hts => ?_⟩
    · have := PosTree.height_pos' t; omega
    · cases ts with
      | nil =>
        intro par off
        simp only [PosTree.annF]
        exact ⟨fun q u p h => by simp at h, fun q u p h => by simp at h⟩
      | cons t ts =>
        have := PosTree.height_pos' t
        simp only [PosTree.forestHeight] at hts
        omega
  | n + 1 => by
    obtain ⟨-, ihF⟩ := PosTree.ann_spec n
    have tree : ∀ (t : PosTree), t.height ≤ n + 1 → ∀ par off,
        AnnParOk par off [t] (t.ann par off) ∧ AnnKidsOk off (t.ann par off) := by
      intro t ht par off
      cases t with
      | node occ anc key grp kids =>
        have hk : PosTree.forestHeight kids ≤ n := by simp [PosTree.height] at ht; omega
        obtain ⟨hP, hK⟩ := ihF kids hk (off + 1) (off + 1)
        simp only [PosTree.ann]
        refine ⟨fun q u p h => ?_, fun q u p h k hkm => ?_⟩
        · cases q with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Or.inl ⟨rfl, List.mem_singleton_self _⟩
          | succ q =>
            simp only [List.getElem?_cons_succ] at h
            rcases hP q u p h with ⟨h1, h2⟩ | ⟨h1, h2, e, he, h4⟩
            · subst h1
              refine Or.inr ⟨by omega, by omega, (.node occ anc key grp kids, par), by simp, ?_⟩
              simpa [PosTree.kids] using h2
            · refine Or.inr ⟨by omega, by omega, e, ?_, h4⟩
              rw [show p - 1 - off = (p - 1 - (off + 1)) + 1 by omega, List.getElem?_cons_succ]
              exact he
        · cases q with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨q', hent⟩ := PosTree.annF_root (off + 1) (off + 1) kids k
              (by simpa [PosTree.kids] using hkm)
            exact ⟨q' + 1, by simpa using hent⟩
          | succ q =>
            simp only [List.getElem?_cons_succ] at h
            obtain ⟨q', hent⟩ := hK q u p h k hkm
            exact ⟨q' + 1, by
              rw [List.getElem?_cons_succ, hent]; congr 2; omega⟩
    refine ⟨tree, fun ts hts => ?_⟩
    induction ts with
    | nil =>
      intro par off
      simp only [PosTree.annF]
      exact ⟨fun q u p h => by simp at h, fun q u p h => by simp at h⟩
    | cons t ts ih =>
      intro par off
      simp only [PosTree.forestHeight] at hts
      obtain ⟨hPt, hKt⟩ := tree t (by omega) par off
      obtain ⟨hPs, hKs⟩ := ih (by omega) par (off + t.nodes.length)
      have hlt := PosTree.ann_length par off t
      simp only [PosTree.annF]
      refine ⟨fun q u p h => ?_, fun q u p h k hkm => ?_⟩
      · by_cases hq1 : q < (t.ann par off).length
        · rw [List.getElem?_append_left hq1] at h
          rcases hPt q u p h with ⟨h1, h2⟩ | ⟨h1, h2, e, he, h4⟩
          · exact Or.inl ⟨h1, by simp at h2; simp [h2]⟩
          · refine Or.inr ⟨h1, h2, e, ?_, h4⟩
            rw [List.getElem?_append_left (by
              have := (List.getElem?_eq_some_iff.mp he).1; omega)]
            exact he
        · rw [List.getElem?_append_right (by omega)] at h
          rcases hPs (q - (t.ann par off).length) u p h with ⟨h1, h2⟩ | ⟨h1, h2, e, he, h4⟩
          · exact Or.inl ⟨h1, List.mem_cons_of_mem _ h2⟩
          · refine Or.inr ⟨by omega, by omega, e, ?_, h4⟩
            rw [List.getElem?_append_right (by omega),
              show p - 1 - off - (t.ann par off).length = p - 1 - (off + t.nodes.length) by omega]
            exact he
      · by_cases hq1 : q < (t.ann par off).length
        · rw [List.getElem?_append_left hq1] at h
          obtain ⟨q', hent⟩ := hKt q u p h k hkm
          exact ⟨q', by
            rw [List.getElem?_append_left (by
              have := (List.getElem?_eq_some_iff.mp hent).1; omega)]
            exact hent⟩
        · rw [List.getElem?_append_right (by omega)] at h
          obtain ⟨q', hent⟩ := hKs (q - (t.ann par off).length) u p h k hkm
          refine ⟨q' + (t.ann par off).length, ?_⟩
          rw [List.getElem?_append_right (by omega), show q' + (t.ann par off).length
            - (t.ann par off).length = q' by omega, hent]
          congr 2
          omega

/-- **The flattened forest's facts**: the entries' nodes are the forest's,
an entry's parent is a root or an earlier entry having it as a kid, and
every kid of an entry has an entry whose parent is it. -/
theorem PosTree.annF_spec (ts : List PosTree) :
    (PosTree.annF 0 0 ts).map (·.1) = PosTree.forest ts ∧
    AnnParOk 0 0 ts (PosTree.annF 0 0 ts) ∧ AnnKidsOk 0 (PosTree.annF 0 0 ts) :=
  ⟨PosTree.annF_fst 0 0 ts, (PosTree.ann_spec _).2 ts (Nat.le_refl _) 0 0⟩

end ConLeche
