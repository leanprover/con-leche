module

public import ConLeche.Kernel.Inductives.NestedElim

public section

/-!
# The copies' order: what the kernel's computation guarantees (task #279 K.6)

`nestedTopoOrder` (`ConLeche/Kernel/Inductives/NestedElim.lean`) emits a
topological order of the copies along their reference relation, and
CHECKS its own result against `topoOrderOk` before returning it.  This
file reads the four conjuncts of that check back out, ONE PER LEMMA, in
exactly the shape the model lane's `structure TopoOrder` asks for
(`agent/nested-279m:ConLeche/Verify/Inductives/NestedOrder.lean`):

    nodup      : order.Nodup
    complete   : ∀ j, j < n → j ∈ order
    bounded    : ∀ j ∈ order, j < n
    lt_of_ref  : ∀ j j', R j j' → j' ∈ order ∧ order.idxOf j' < order.idxOf j

**Why the fields and not `TopoOrder` itself.**  `TopoOrder` and
`CopyRef` are the model lane's definitions and its file is not on
`inductives`; stating the conjunct in terms of them would mean
duplicating that file here.  So the run relation records the kernel's
Bool equation (`DeclNestedRun`'s `nestedTopoOrder … = .ok order`) and
this file turns it into the four fields at `R := fun j j' => copyRefB
(ElimState.grp st) k st j j' = true`.  **What the lane owes to close the
gap is one lemma about its own `Prop` and this `Bool`**:
`CopyRef grp k st j j' ↔ copyRefB grp k st j j' = true` — the two are
clause-for-clause the same, with `Expr.subB` deciding `Expr.Sub` — the
eleven introduction lemmas (`subB_self` … `subB_proj`, one per
constructor of `Expr.Sub`) and the elimination `subB_cases` are here, so
that lemma is a two-line induction on either side — and then
`TopoOrder R n order` is `⟨nodup, complete, bounded, lt_of_ref⟩`.

`lt_of_ref` takes `j < n` as a hypothesis: the lane's `CopyRef` supplies
it from its own first conjunct (`st.types[k + j]? = some t`) together
with the ledger fact `st.types.length = k + st.pins.length`, which is
its bookkeeping and not this file's.
-/

namespace ConLeche

/-! ## `subB` decides `Sub` -/

/-- The subterm decision is the model lane's relation, on the nose.
Stated as the two implications over the walk's positions; the lane's
`Expr.Sub` is the inductive family with exactly these constructors. -/
theorem subB_self (pat : Expr) : Expr.subB pat pat = true := by
  cases pat <;> simp [Expr.subB]

theorem subB_app_left {pat f a : Expr} (h : Expr.subB pat f = true) :
    Expr.subB pat (.app f a) = true := by simp [Expr.subB, h]

theorem subB_app_right {pat f a : Expr} (h : Expr.subB pat a = true) :
    Expr.subB pat (.app f a) = true := by simp [Expr.subB, h]

theorem subB_lam_dom {pat ty b : Expr} {m : BinderMeta} (h : Expr.subB pat ty = true) :
    Expr.subB pat (.lam ty b m) = true := by simp [Expr.subB, h]

theorem subB_lam_body {pat ty b : Expr} {m : BinderMeta} (h : Expr.subB pat b = true) :
    Expr.subB pat (.lam ty b m) = true := by simp [Expr.subB, h]

theorem subB_pi_dom {pat ty b : Expr} {m : BinderMeta} (h : Expr.subB pat ty = true) :
    Expr.subB pat (.forallE ty b m) = true := by simp [Expr.subB, h]

theorem subB_pi_body {pat ty b : Expr} {m : BinderMeta} (h : Expr.subB pat b = true) :
    Expr.subB pat (.forallE ty b m) = true := by simp [Expr.subB, h]

theorem subB_let_ty {pat ty v b : Expr} (h : Expr.subB pat ty = true) :
    Expr.subB pat (.letE ty v b) = true := by simp [Expr.subB, h]

theorem subB_let_val {pat ty v b : Expr} (h : Expr.subB pat v = true) :
    Expr.subB pat (.letE ty v b) = true := by simp [Expr.subB, h]

theorem subB_let_body {pat ty v b : Expr} (h : Expr.subB pat b = true) :
    Expr.subB pat (.letE ty v b) = true := by simp [Expr.subB, h]

theorem subB_proj {pat x : Expr} {s : Name} {i : Nat} (h : Expr.subB pat x = true) :
    Expr.subB pat (.proj s i x) = true := by simp [Expr.subB, h]

/-- The converse: a `true` answer comes from the term itself or from one
of the walk's positions.  Together with the constructors above this is
`Expr.subB pat e = true ↔ Expr.Sub pat e` once the lane's inductive is
in scope. -/
theorem subB_cases {pat e : Expr} (h : Expr.subB pat e = true) :
    pat = e ∨
      (∃ f a, e = .app f a ∧ (Expr.subB pat f = true ∨ Expr.subB pat a = true)) ∨
      (∃ ty b m, e = .lam ty b m ∧ (Expr.subB pat ty = true ∨ Expr.subB pat b = true)) ∨
      (∃ ty b m, e = .forallE ty b m ∧ (Expr.subB pat ty = true ∨ Expr.subB pat b = true)) ∨
      (∃ ty v b, e = .letE ty v b ∧ (Expr.subB pat ty = true ∨ Expr.subB pat v = true ∨
        Expr.subB pat b = true)) ∨
      (∃ s i x, e = .proj s i x ∧ Expr.subB pat x = true) := by
  cases e with
  | app f a =>
    rw [Expr.subB] at h
    rcases (by simpa using h : (pat = Expr.app f a ∨ Expr.subB pat f = true) ∨
        Expr.subB pat a = true) with h' | h'
    case inl => rcases h' with h' | h'
                · exact Or.inl h'
                · exact Or.inr (Or.inl ⟨f, a, rfl, Or.inl h'⟩)
    case inr => exact Or.inr (Or.inl ⟨f, a, rfl, Or.inr h'⟩)
  | lam ty b m =>
    rw [Expr.subB] at h
    rcases (by simpa using h : (pat = Expr.lam ty b m ∨ Expr.subB pat ty = true) ∨
        Expr.subB pat b = true) with h' | h'
    case inl => rcases h' with h' | h'
                · exact Or.inl h'
                · exact Or.inr (Or.inr (Or.inl ⟨ty, b, m, rfl, Or.inl h'⟩))
    case inr => exact Or.inr (Or.inr (Or.inl ⟨ty, b, m, rfl, Or.inr h'⟩))
  | forallE ty b m =>
    rw [Expr.subB] at h
    rcases (by simpa using h : (pat = Expr.forallE ty b m ∨ Expr.subB pat ty = true) ∨
        Expr.subB pat b = true) with h' | h'
    case inl => rcases h' with h' | h'
                · exact Or.inl h'
                · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, b, m, rfl, Or.inl h'⟩)))
    case inr => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, b, m, rfl, Or.inr h'⟩)))
  | letE ty v b =>
    rw [Expr.subB] at h
    rcases (by simpa using h : ((pat = Expr.letE ty v b ∨ Expr.subB pat ty = true) ∨
        Expr.subB pat v = true) ∨ Expr.subB pat b = true) with h' | h'
    case inl =>
      rcases h' with h' | h'
      · rcases h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, v, b, rfl, Or.inl h'⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, v, b, rfl, Or.inr (Or.inl h')⟩))))
    case inr =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, v, b, rfl, Or.inr (Or.inr h')⟩))))
  | proj s i x =>
    rw [Expr.subB] at h
    rcases (by simpa using h : pat = Expr.proj s i x ∨ Expr.subB pat x = true)
      with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, i, x, rfl, h'⟩))))
  | bvar i => exact Or.inl (by simpa [Expr.subB] using h)
  | fvar i ty => exact Or.inl (by simpa [Expr.subB] using h)
  | sort u => exact Or.inl (by simpa [Expr.subB] using h)
  | const n us => exact Or.inl (by simpa [Expr.subB] using h)
  | lit l => exact Or.inl (by simpa [Expr.subB] using h)

/-! ## The four fields of the emitted order -/

variable {refs : Nat → List Nat} {n : Nat} {order : List Nat}

/-- Every conjunct of the check, read off a `true`. -/
theorem topoOrderOk_inv (h : topoOrderOk refs n order = true) :
    order.Nodup ∧
    (∀ j, j < n → order.contains j = true) ∧
    (∀ j ∈ order, j < n) ∧
    (∀ j ∈ order, ∀ j' ∈ refs j,
      order.contains j' = true ∧ order.idxOf j' < order.idxOf j) := by
  unfold topoOrderOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hnd, hcomp⟩, hbd⟩, href⟩ := h
  refine ⟨of_decide_eq_true hnd, ?_, ?_, ?_⟩
  · intro j hj
    exact List.all_eq_true.mp hcomp j (List.mem_range.mpr hj)
  · intro j hj
    exact of_decide_eq_true (List.all_eq_true.mp hbd j hj)
  · intro j hj j' hj'
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp href j hj) j' hj'
    rw [Bool.and_eq_true] at h2
    exact ⟨h2.1, of_decide_eq_true h2.2⟩

/-- **`TopoOrder.nodup`.** -/
theorem nestedTopoOrder_nodup {grp : Nat → Nat × Nat} {k : Nat} {st : ElimState}
    (h : nestedTopoOrder grp k st = .ok order) : order.Nodup := by
  unfold nestedTopoOrder at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i o ho
    split at h
    · rename_i hok
      obtain rfl : o = order := by cases h; rfl
      exact (topoOrderOk_inv hok).1
    · exact absurd h (by simp)

/-- **`TopoOrder.complete`.** -/
theorem nestedTopoOrder_complete {grp : Nat → Nat × Nat} {k : Nat} {st : ElimState}
    (h : nestedTopoOrder grp k st = .ok order) :
    ∀ j, j < st.pins.length → j ∈ order := by
  unfold nestedTopoOrder at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i o ho
    split at h
    · rename_i hok
      obtain rfl : o = order := by cases h; rfl
      intro j hj
      exact List.mem_of_elem_eq_true ((topoOrderOk_inv hok).2.1 j hj)
    · exact absurd h (by simp)

/-- **`TopoOrder.bounded`.** -/
theorem nestedTopoOrder_bounded {grp : Nat → Nat × Nat} {k : Nat} {st : ElimState}
    (h : nestedTopoOrder grp k st = .ok order) :
    ∀ j ∈ order, j < st.pins.length := by
  unfold nestedTopoOrder at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i o ho
    split at h
    · rename_i hok
      obtain rfl : o = order := by cases h; rfl
      exact (topoOrderOk_inv hok).2.2.1
    · exact absurd h (by simp)

/-- **`TopoOrder.lt_of_ref`**, at the kernel's `Bool` relation: every
reference of a copy in the order points to an EARLIER entry.  `j < n`
is the lane's, from `CopyRef`'s own first conjunct. -/
theorem nestedTopoOrder_ref {grp : Nat → Nat × Nat} {k : Nat} {st : ElimState}
    (h : nestedTopoOrder grp k st = .ok order) {j j' : Nat}
    (hj : j < st.pins.length) (hj' : j' < st.pins.length)
    (hR : copyRefB grp k st j j' = true) :
    j' ∈ order ∧ order.idxOf j' < order.idxOf j := by
  have hjm : j ∈ order := nestedTopoOrder_complete h j hj
  have hmem : j' ∈ copyRefsOf grp k st st.pins.length j := by
    unfold copyRefsOf
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hj', hR⟩
  unfold nestedTopoOrder at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i o ho
    split at h
    · rename_i hok
      obtain rfl : o = order := by cases h; rfl
      obtain ⟨hc, hlt⟩ := (topoOrderOk_inv hok).2.2.2 j hjm j' hmem
      exact ⟨List.mem_of_elem_eq_true hc, hlt⟩
    · exact absurd h (by simp)

end ConLeche
