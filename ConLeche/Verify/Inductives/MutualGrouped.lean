module

public import ConLeche.Verify.Inductives.MutualInv

public section

/-!
# The mutual block's constructors, member by member (task #315)

Pure list facts about `MutualBlock.ownCtors`
(`ConLeche/Kernel/Inductives/MutualInstall.lean`), the constructors of
one member of a mutual block together with their GLOBAL indices into
`b.ctors`.

Two readings of that list.  Unconditionally it is a *selection*: a pair
`(J, c)` is in it exactly when `c` sits at `J` in `b.ctors` and names
the member (`ownCtors_mem_iff`).  Under the shape guard the install
checks (`mutualCtorsGrouped b.ctors`, the members non-decreasing along
`b.ctors`) it is moreover a contiguous *run*: member `mm`'s
constructors occupy `b.ctors` positions `ownOffset mm` onwards, where
`MutualBlock.ownOffset mm` counts the constructors of all members
before `mm` — members with no constructor contributing `0`
(`ownCtors_getElem?_idx`, `ownCtors_of_ctors`).  With every member in
range (`c.member < b.k`) the runs exhaust `b.ctors` (`ownOffset_k`).
-/

namespace ConLeche

/-- The number of constructors the members before `mm` contribute: the
offset of member `mm`'s own run in `b.ctors` (under the block's
grouping guard, `ownCtors_getElem?_idx`). -/
@[expose] def MutualBlock.ownOffset (b : MutualBlock) (mm : Nat) : Nat :=
  ((List.range mm).map fun t => (b.ownCtors t).length).sum

/-! ## The selection over a plain list -/

/-- `MutualBlock.ownCtors` over a plain constructor list whose global
indices start at `s`. -/
private def ownAt (l : List MutualCtor) (s mm : Nat) : List (Nat × MutualCtor) :=
  ((l.zipIdx s).map fun (c, J) => (J, c)).filter fun (_, c) => c.member == mm

private theorem ownCtors_eq_ownAt (b : MutualBlock) (mm : Nat) :
    b.ownCtors mm = ownAt b.ctors 0 mm := by rfl

private theorem ownAt_nil (s mm : Nat) : ownAt [] s mm = [] := by rfl

private theorem ownAt_cons_pos {c : MutualCtor} {l : List MutualCtor} {s mm : Nat}
    (h : c.member = mm) : ownAt (c :: l) s mm = (s, c) :: ownAt l (s + 1) mm := by
  simp [ownAt, List.zipIdx_cons, h]

private theorem ownAt_cons_neg {c : MutualCtor} {l : List MutualCtor} {s mm : Nat}
    (h : c.member ≠ mm) : ownAt (c :: l) s mm = ownAt l (s + 1) mm := by
  simp [ownAt, List.zipIdx_cons, h]

/-- Whatever `ownAt` selects sits in the list and names the member. -/
private theorem mem_ownAt {mm J : Nat} {c : MutualCtor} :
    ∀ (l : List MutualCtor) (s : Nat), (J, c) ∈ ownAt l s mm → c ∈ l ∧ c.member = mm := by
  intro l
  induction l with
  | nil => intro s h; rw [ownAt_nil] at h; simp at h
  | cons d l ih =>
    intro s h
    by_cases hd : d.member = mm
    · rw [ownAt_cons_pos hd] at h
      rcases List.mem_cons.mp h with h' | h'
      · have e : c = d := congrArg Prod.snd h'
        subst e
        exact ⟨List.mem_cons_self .., hd⟩
      · exact ⟨List.mem_cons_of_mem _ (ih (s + 1) h').1, (ih (s + 1) h').2⟩
    · rw [ownAt_cons_neg hd] at h
      exact ⟨List.mem_cons_of_mem _ (ih (s + 1) h).1, (ih (s + 1) h).2⟩

/-! ## Counting -/

/-- The number of constructors naming member `mm`. -/
private def cntOf (l : List MutualCtor) (mm : Nat) : Nat :=
  (l.filter fun c => c.member == mm).length

private theorem ownAt_length (l : List MutualCtor) (s mm : Nat) :
    (ownAt l s mm).length = cntOf l mm := by
  induction l generalizing s with
  | nil => rfl
  | cons c l ih =>
    by_cases h : c.member = mm
    · rw [ownAt_cons_pos h]; simp [cntOf, h, ih (s + 1)]
    · rw [ownAt_cons_neg h]; simp [cntOf, h, ih (s + 1)]

/-- The offset of member `mm`'s run, over a plain list. -/
private def offOf (l : List MutualCtor) (mm : Nat) : Nat :=
  ((List.range mm).map fun t => cntOf l t).sum

private theorem sum_range_add (mm : Nat) (f g : Nat → Nat) :
    ((List.range mm).map fun t => f t + g t).sum
      = ((List.range mm).map f).sum + ((List.range mm).map g).sum := by
  induction mm with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ih]
    omega

private theorem sum_range_ite (mm a : Nat) :
    ((List.range mm).map fun t => if a = t then 1 else 0).sum = if a < mm then 1 else 0 := by
  induction mm with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ih]
    by_cases h1 : a < n
    · rw [if_pos h1, if_pos (Nat.lt_succ_of_lt h1), if_neg (by omega)]
      omega
    · by_cases h2 : a = n
      · rw [if_neg h1, if_pos h2, if_pos (by omega)]
        omega
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]
        omega

private theorem sum_range_zero : ∀ (mm : Nat) (f : Nat → Nat), (∀ t, t < mm → f t = 0) →
    ((List.range mm).map f).sum = 0 := by
  intro mm
  induction mm with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro f h
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ih f (fun t ht => h t (Nat.lt_succ_of_lt ht)),
      h n (Nat.lt_succ_self n)]
    omega

private theorem offOf_cons (c : MutualCtor) (l : List MutualCtor) (mm : Nat) :
    offOf (c :: l) mm = offOf l mm + (if c.member < mm then 1 else 0) := by
  have h : ∀ t ∈ List.range mm,
      cntOf (c :: l) t = cntOf l t + (if c.member = t then 1 else 0) := by
    intro t _
    by_cases ht : c.member = t
    · simp [cntOf, ht]
    · simp [cntOf, ht]
  show ((List.range mm).map fun t => cntOf (c :: l) t).sum = _
  rw [List.map_congr_left h,
    sum_range_add mm (fun t => cntOf l t) (fun t => if c.member = t then 1 else 0),
    sum_range_ite mm c.member]
  rfl

private theorem offOf_eq_zero {l : List MutualCtor} {mm : Nat}
    (h : ∀ c ∈ l, mm ≤ c.member) : offOf l mm = 0 := by
  refine sum_range_zero mm _ (fun t ht => ?_)
  have e : (l.filter fun c => c.member == t) = [] := by
    refine List.filter_eq_nil_iff.mpr (fun c hc => ?_)
    have := h c hc
    simp only [beq_iff_eq]
    omega
  simp [cntOf, e]

private theorem offOf_all_lt : ∀ (l : List MutualCtor) (k : Nat),
    (l.all fun c => c.member < k) = true → offOf l k = l.length := by
  intro l
  induction l with
  | nil => intro k _; exact sum_range_zero k _ (fun t _ => by simp [cntOf])
  | cons d l ih =>
    intro k hall
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    rw [offOf_cons, ih k hall.2, if_pos hall.1]
    simp

/-! ## The grouping guard -/

private theorem grouped_tail {c : MutualCtor} {l : List MutualCtor}
    (h : mutualCtorsGrouped (c :: l) = true) : mutualCtorsGrouped l = true := by
  cases l with
  | nil => rfl
  | cons d l =>
    simp only [mutualCtorsGrouped, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

private theorem grouped_le_of_mem {c' : MutualCtor} :
    ∀ (l : List MutualCtor) (c : MutualCtor),
      mutualCtorsGrouped (c :: l) = true → c' ∈ l → c.member ≤ c'.member := by
  intro l
  induction l with
  | nil => intro _ _ hm; simp at hm
  | cons d l ih =>
    intro c hg hm
    have h1 : c.member ≤ d.member := by
      simp only [mutualCtorsGrouped, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact hg.1
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact h1
    · exact Nat.le_trans h1 (ih d (grouped_tail hg) hm')

/-- The heart: under the grouping guard the `j`-th selected constructor
of member `mm` sits at `offOf l mm + j`. -/
private theorem ownAt_getElem?_idx {mm : Nat} :
    ∀ (l : List MutualCtor), mutualCtorsGrouped l = true →
      ∀ (s j J : Nat) (c : MutualCtor), (ownAt l s mm)[j]? = some (J, c) →
        J = s + offOf l mm + j := by
  intro l
  induction l with
  | nil => intro _ s j J c h; rw [ownAt_nil] at h; simp at h
  | cons d l ih =>
    intro hg s j J c h
    by_cases hd : d.member = mm
    · rw [ownAt_cons_pos hd] at h
      have hz : offOf l mm = 0 :=
        offOf_eq_zero (fun c' hc' => by
          have := grouped_le_of_mem l d hg hc'
          omega)
      have hoff : offOf (d :: l) mm = 0 := by
        rw [offOf_cons, hz, if_neg (by omega)]
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero] at h
        have h1 : (s, d) = (J, c) := Option.some.inj h
        have h2 : s = J := congrArg Prod.fst h1
        rw [hoff]; omega
      | succ j =>
        rw [List.getElem?_cons_succ] at h
        have h' := ih (grouped_tail hg) (s + 1) j J c h
        rw [hoff]; omega
    · rw [ownAt_cons_neg hd] at h
      obtain ⟨-, hc2⟩ := mem_ownAt l (s + 1) (List.mem_of_getElem? h)
      have hle : d.member ≤ c.member :=
        grouped_le_of_mem l d hg (mem_ownAt l (s + 1) (List.mem_of_getElem? h)).1
      have h' := ih (grouped_tail hg) (s + 1) j J c h
      rw [offOf_cons, if_pos (show d.member < mm by omega)]
      omega

/-! ## The block's own constructors -/

private theorem ownOffset_eq_offOf (b : MutualBlock) (mm : Nat) :
    b.ownOffset mm = offOf b.ctors mm :=
  congrArg List.sum (List.map_congr_left fun t _ => by
    rw [ownCtors_eq_ownAt, ownAt_length])

/-- `ownCtors` is the selection of the constructors naming the member,
with their global indices. -/
theorem ownCtors_mem_iff {b : MutualBlock} {mm J : Nat} {c : MutualCtor} :
    (J, c) ∈ b.ownCtors mm ↔ b.ctors[J]? = some c ∧ c.member = mm := by
  constructor
  · intro h
    have h' := List.mem_filter.mp h
    obtain ⟨⟨c', J'⟩, hmem, heq⟩ := List.mem_map.mp h'.1
    have e1 : J' = J := congrArg Prod.fst heq
    have e2 : c' = c := congrArg Prod.snd heq
    subst e1; subst e2
    refine ⟨List.mk_mem_zipIdx_iff_getElem?.mp hmem, ?_⟩
    have := h'.2
    simpa using this
  · rintro ⟨h1, h2⟩
    refine List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨(c, J), List.mk_mem_zipIdx_iff_getElem?.mpr h1, rfl⟩, ?_⟩
    simp [h2]

theorem ownCtors_getElem?_ctors {b : MutualBlock} {mm j J : Nat} {c : MutualCtor}
    (h : (b.ownCtors mm)[j]? = some (J, c)) : b.ctors[J]? = some c ∧ c.member = mm :=
  ownCtors_mem_iff.mp (List.mem_of_getElem? h)

/-- Under the grouping guard member `mm`'s constructors are the run of
`b.ctors` starting at `b.ownOffset mm`. -/
theorem ownCtors_getElem?_idx {b : MutualBlock} (hg : mutualCtorsGrouped b.ctors = true)
    {mm j J : Nat} {c : MutualCtor} (h : (b.ownCtors mm)[j]? = some (J, c)) :
    J = b.ownOffset mm + j := by
  rw [ownCtors_eq_ownAt] at h
  have := ownAt_getElem?_idx b.ctors hg 0 j J c h
  rw [ownOffset_eq_offOf]
  omega

/-- The converse reading: every constructor of `b.ctors` is found in
its own member's run, at the index its position dictates. -/
theorem ownCtors_of_ctors {b : MutualBlock} (hg : mutualCtorsGrouped b.ctors = true)
    {J : Nat} {c : MutualCtor} (h : b.ctors[J]? = some c) :
    b.ownOffset c.member ≤ J ∧
      (b.ownCtors c.member)[J - b.ownOffset c.member]? = some (J, c) := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem (ownCtors_mem_iff.mpr ⟨h, rfl⟩)
  have hJ := ownCtors_getElem?_idx hg hj
  refine ⟨by omega, ?_⟩
  rw [show J - b.ownOffset c.member = j by omega]
  exact hj

/-- The runs are consecutive. -/
theorem ownOffset_succ (b : MutualBlock) (mm : Nat) :
    b.ownOffset (mm + 1) = b.ownOffset mm + (b.ownCtors mm).length := by
  show ((List.range (mm + 1)).map fun t => (b.ownCtors t).length).sum = _
  rw [List.range_succ]
  simp [MutualBlock.ownOffset]

private theorem ownOffset_le_add (b : MutualBlock) (mm d : Nat) :
    b.ownOffset mm ≤ b.ownOffset (mm + d) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    rw [show mm + (d + 1) = (mm + d) + 1 by omega, ownOffset_succ]
    omega

/-- With every constructor naming a member of the block, the runs
exhaust `b.ctors`. -/
theorem ownOffset_k {b : MutualBlock} (hlt : b.ctors.all (fun c => c.member < b.k) = true) :
    b.ownOffset b.k = b.ctors.length := by
  rw [ownOffset_eq_offOf]
  exact offOf_all_lt b.ctors b.k hlt

theorem ownOffset_add_length_le {b : MutualBlock}
    (hlt : b.ctors.all (fun c => c.member < b.k) = true) {mm : Nat} (h : mm < b.k) :
    b.ownOffset mm + (b.ownCtors mm).length ≤ b.ctors.length := by
  rw [← ownOffset_succ, ← ownOffset_k hlt]
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd]
  exact ownOffset_le_add b (mm + 1) d
