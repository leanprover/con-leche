module

public import ConLeche.Frontend.Rounds
public import ConLeche.Verify.Frontend.StateEquiv

public section

/-!
# Increasing streams (task #329)

The facts about the serial apply the rounds parse rests on, for a
stream whose every table binds its indices in increasing order (each
above the last; lean4export leaves no gaps, other exporters may).  The
tables are partial maps `Tabs`; a parse state *holds* tables `T` cut at
counters `c` when its lookups answer `T` below `c` and nothing above
(`Holds`).

* **An increasing stream never rebinds** (`applyLine_name_holds` and its
  siblings): at a state holding `T` cut at `c`, a line binding an index
  at or above its table's counter passes the rebinding test, and the
  state after it holds `T` cut one past that index — as long as `T`
  binds nothing in between (the gap the line skips).
* **The characterisation** (`applyList_of_allOK`): over a list of lines
  each of which, at the final tables cut at the counters before it,
  binds its index above the counter with nothing in the gap, and whose
  builder yields the final table's entry (`AllOK`), the serial fold
  succeeds and holds the final tables cut at the final counters, its
  records pushed (`declsAlong`).  The condition is per line, so the
  rounds can establish it in any order.
-/

namespace ConLeche.Frontend

open ConLeche

/-- A parse state holds tables `T` cut at counters `c`. -/
structure Holds (st : StateD) (T : Tabs) (c : Ctr) : Prop where
  n : ∀ j, st.names.get? j = if j < c.n then T.n j else none
  l : ∀ j, st.levels.get? j = if j < c.l then T.l j else none
  e : ∀ j, st.exprs.get? j = if j < c.e then T.e j else none

theorem Holds.lk {st : StateD} {T : Tabs} {c : Ctr} (h : Holds st T c) : st.lk = cutLk T c := by
  have hn : st.name = (cutLk T c).name := funext fun j => by
    simp only [StateD.name, cutLk, h.n j]; rfl
  have hl : st.level = (cutLk T c).level := funext fun j => by
    simp only [StateD.level, cutLk, h.l j]; rfl
  have he : st.expr = (cutLk T c).expr := funext fun j => by
    simp only [StateD.expr, cutLk, h.e j]; rfl
  simp only [StateD.lk, hn, hl, he]

theorem Holds.equiv {a b : StateD} {T : Tabs} {c : Ctr} (ha : Holds a T c) (hb : Holds b T c)
    (hd : a.decls = b.decls) : a.Equiv b :=
  ⟨fun j => (ha.n j).trans (hb.n j).symm, fun j => (ha.l j).trans (hb.l j).symm,
   fun j => (ha.e j).trans (hb.e j).symm, hd⟩

/-- Binding index `i ≥ k` with value `x`, where the table `t` answers
`T` below `k` and `T` binds nothing in `[k, i)` and `x` at `i`: the
table answers `T` below `i + 1`. -/
theorem get?_insert_cut {t : IdTable α} {f : Nat → Option α} {k i : Nat} {x : α}
    (ht : ∀ j, t.get? j = if j < k then f j else none) (hki : k ≤ i)
    (hgap : ∀ j, k ≤ j → j < i → f j = none) (hx : f i = some x) (j : Nat) :
    (t.insert i x).get? j = if j < i + 1 then f j else none := by
  rw [IdTable.get?_insert, ht j]
  by_cases hji : j = i
  · subst hji; simp [hx]
  · simp only [hji, ↓reduceIte]
    by_cases hjk : j < k
    · simp [hjk, show j < i + 1 by omega]
    · simp only [hjk, ↓reduceIte]
      by_cases hj : j < i
      · simp [show j < i + 1 by omega, hgap j (by omega) hj]
      · simp [show ¬ j < i + 1 by omega]

theorem bound_cut {t : IdTable α} {f : Nat → Option α} {k i : Nat}
    (ht : ∀ j, t.get? j = if j < k then f j else none) (hki : k ≤ i) : t.bound i = false := by
  rw [IdTable.bound_eq, ht i]; simp [show ¬ i < k by omega]

/-! ## An increasing stream never rebinds -/

/-- **One line is right**: a table line binds an index at or above its
table's counter, its table binds nothing in the gap, and its builder,
at the final tables cut before it, yields the final table's entry; a
declaration line's builder yields a record. -/
@[expose] def LineOK (T : Tabs) (c : Ctr) : LineRec → Prop
  | .name i r => c.n ≤ i ∧ (∀ j, c.n ≤ j → j < i → T.n j = none) ∧
      ∃ v, T.n i = some v ∧ nameOf (cutLk T c) r = .ok v
  | .level i r => c.l ≤ i ∧ (∀ j, c.l ≤ j → j < i → T.l j = none) ∧
      ∃ v, T.l i = some v ∧ levelOf (cutLk T c) r = .ok v
  | .expr i r => c.e ≤ i ∧ (∀ j, c.e ≤ j → j < i → T.e j = none) ∧
      ∃ v, T.e i = some v ∧ exprOf (cutLk T c) r = .ok v
  | .decl d => ∃ x, declOf (cutLk T c) d = .ok (.inl x)
  | .header => True
  | .blank => True

/-- The record a declaration line yields at its counters. -/
@[expose] def lineDecl (T : Tabs) (c : Ctr) : LineRec → Option Declaration
  | .decl d => match declOf (cutLk T c) d with
    | .ok (.inl x) => some x
    | _ => none
  | _ => none

/-- A right line, applied at a state holding the final tables cut at
its counters: the state after it holds them cut at the next counters,
with the line's record pushed. -/
theorem applyRecord_of_lineOK {T : Tabs} {c : Ctr} {r : LineRec} {st : StateD}
    (hok : LineOK T c r) (hst : Holds st T c) :
    ∃ st', applyRecord st r = .ok (.inl st') ∧ Holds st' T (c.step r) ∧
      st'.decls = (match lineDecl T c r with | some x => st.decls.push x | none => st.decls) := by
  cases r with
  | name i x =>
    obtain ⟨hki, hgap, v, hv, hx⟩ := hok
    refine ⟨{ st with names := st.names.insert i v }, ?_, ?_, rfl⟩
    · simp only [applyRecord, parseNameEntryD, hst.lk, hx, StateD.freshName,
        bound_cut hst.n hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨get?_insert_cut hst.n hki hgap hv, hst.l, hst.e⟩
  | level i x =>
    obtain ⟨hki, hgap, v, hv, hx⟩ := hok
    refine ⟨{ st with levels := st.levels.insert i v }, ?_, ?_, rfl⟩
    · simp only [applyRecord, parseLevelEntryD, hst.lk, hx, StateD.freshLevel,
        bound_cut hst.l hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨hst.n, get?_insert_cut hst.l hki hgap hv, hst.e⟩
  | expr i x =>
    obtain ⟨hki, hgap, v, hv, hx⟩ := hok
    refine ⟨{ st with exprs := st.exprs.insert i v }, ?_, ?_, rfl⟩
    · simp only [applyRecord, parseExprEntryD, hst.lk, hx, StateD.freshExpr,
        bound_cut hst.e hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨hst.n, hst.l, get?_insert_cut hst.e hki hgap hv⟩
  | decl d =>
    obtain ⟨x, hx⟩ := hok
    refine ⟨pushDecl st x, ?_, ⟨hst.n, hst.l, hst.e⟩, ?_⟩
    · simp only [applyRecord, applyDeclD, processLineCoreD, hst.lk, hx, bind, Except.bind, pure,
        Except.pure]
    · simp only [lineDecl, hx, pushDecl]
  | header => exact ⟨st, rfl, hst, rfl⟩
  | blank => exact ⟨st, rfl, hst, rfl⟩

/-! ## The characterisation -/

/-- Every line of a list is right, each at its own counters, and stands
where it may, `n` lines before the list (`LineRec.placed`). -/
@[expose] def AllOK (T : Tabs) : Ctr → Nat → List LineRec → Prop
  | _, _, [] => True
  | c, n, r :: rs => r.placed (n == 0) = true ∧ LineOK T c r ∧ AllOK T (c.step r) (n + 1) rs

/-- The records of a list of lines, pushed in order. -/
@[expose] def declsAlong (T : Tabs) : Ctr → List LineRec → Array Declaration → Array Declaration
  | _, [], acc => acc
  | c, r :: rs, acc => declsAlong T (c.step r) rs
      (match lineDecl T c r with
       | some x => acc.push x
       | none => acc)

/-- **The characterisation**: every line right at the final tables makes
the serial fold succeed, holding the final tables cut at the final
counters, with the lines' records pushed. -/
theorem applyList_of_allOK (T : Tabs) :
    ∀ (c : Ctr) (rs : List LineRec) (st : StateD) (k : Nat), AllOK T c k rs → Holds st T c →
    ∃ st', applyList st rs k = .ok (st', k + rs.length) ∧ Holds st' T (c.stepAll rs) ∧
      st'.decls = declsAlong T c rs st.decls := by
  intro c rs
  induction rs generalizing c with
  | nil => intro st k _ h; exact ⟨st, rfl, h, rfl⟩
  | cons r rs ih =>
    intro st k hok hst
    obtain ⟨hp, hr, hrs⟩ := hok
    obtain ⟨st₁, h1, hst₁, hd₁⟩ := applyRecord_of_lineOK hr hst
    rw [← show applyLine st r k = applyRecord st r by simp only [applyLine, hp, ↓reduceIte]]
      at h1
    obtain ⟨st', h2, hst', hd'⟩ := ih (c.step r) st₁ (k + 1) hrs hst₁
    refine ⟨st', ?_, hst', ?_⟩
    · simp only [applyList, h1, List.length_cons]; rw [h2]; congr 2; omega
    · rw [hd', hd₁]; rfl

theorem Ctr.stepAll_append (c : Ctr) (l₁ l₂ : List LineRec) :
    c.stepAll (l₁ ++ l₂) = (c.stepAll l₁).stepAll l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons r l ih => exact ih (c.step r)

/-! ## The characterisation, the other way -/

/-- Every line of a list binds an index at or above its table's
counter. -/
@[expose] def IncAll : Ctr → List LineRec → Prop
  | _, [] => True
  | c, r :: rs => c.fits r = true ∧ IncAll (c.step r) rs

end ConLeche.Frontend
