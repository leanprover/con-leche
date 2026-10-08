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
* **The characterisation** (`applyList_of_allOK`, and the converse
  `allOK_of_applyList`): over a list of lines
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
theorem applyLine_of_lineOK {T : Tabs} {c : Ctr} {r : LineRec} {st : StateD}
    (hok : LineOK T c r) (hst : Holds st T c) :
    ∃ st', applyLine st r = .ok (.inl st') ∧ Holds st' T (c.step r) ∧
      st'.decls = (match lineDecl T c r with | some x => st.decls.push x | none => st.decls) := by
  cases r with
  | name i x =>
    obtain ⟨hki, hgap, v, hv, hx⟩ := hok
    refine ⟨{ st with names := st.names.insert i v }, ?_, ?_, rfl⟩
    · simp only [applyLine, parseNameEntryD, hst.lk, hx, StateD.freshName,
        bound_cut hst.n hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨get?_insert_cut hst.n hki hgap hv, hst.l, hst.e⟩
  | level i x =>
    obtain ⟨hki, hgap, v, hv, hx⟩ := hok
    refine ⟨{ st with levels := st.levels.insert i v }, ?_, ?_, rfl⟩
    · simp only [applyLine, parseLevelEntryD, hst.lk, hx, StateD.freshLevel,
        bound_cut hst.l hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨hst.n, get?_insert_cut hst.l hki hgap hv, hst.e⟩
  | expr i x =>
    obtain ⟨hki, hgap, v, hv, hx⟩ := hok
    refine ⟨{ st with exprs := st.exprs.insert i v }, ?_, ?_, rfl⟩
    · simp only [applyLine, parseExprEntryD, hst.lk, hx, StateD.freshExpr,
        bound_cut hst.e hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨hst.n, hst.l, get?_insert_cut hst.e hki hgap hv⟩
  | decl d =>
    obtain ⟨x, hx⟩ := hok
    refine ⟨pushDecl st x, ?_, ⟨hst.n, hst.l, hst.e⟩, ?_⟩
    · simp only [applyLine, applyDeclD, processLineCoreD, hst.lk, hx, bind, Except.bind, pure,
        Except.pure]
    · simp only [lineDecl, hx, pushDecl]
  | header => exact ⟨st, rfl, hst, rfl⟩
  | blank => exact ⟨st, rfl, hst, rfl⟩

/-! ## The characterisation -/

/-- Every line of a list is right, each at its own counters. -/
@[expose] def AllOK (T : Tabs) : Ctr → List LineRec → Prop
  | _, [] => True
  | c, r :: rs => LineOK T c r ∧ AllOK T (c.step r) rs

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
    ∀ (c : Ctr) (rs : List LineRec) (st : StateD) (k : Nat), AllOK T c rs → Holds st T c →
    ∃ st', applyList st rs k = .ok (st', k + rs.length) ∧ Holds st' T (c.stepAll rs) ∧
      st'.decls = declsAlong T c rs st.decls := by
  intro c rs
  induction rs generalizing c with
  | nil => intro st k _ h; exact ⟨st, rfl, h, rfl⟩
  | cons r rs ih =>
    intro st k hok hst
    obtain ⟨hr, hrs⟩ := hok
    obtain ⟨st₁, h1, hst₁, hd₁⟩ := applyLine_of_lineOK hr hst
    obtain ⟨st', h2, hst', hd'⟩ := ih (c.step r) st₁ (k + 1) hrs hst₁
    refine ⟨st', ?_, hst', ?_⟩
    · simp only [applyList, h1, List.length_cons]; rw [h2]; congr 2; omega
    · rw [hd', hd₁]; rfl

/-- `AllOK` over a concatenation. -/
theorem AllOK.append {T : Tabs} :
    ∀ {c : Ctr} {l₁ l₂ : List LineRec}, AllOK T c l₁ → AllOK T (c.stepAll l₁) l₂ →
    AllOK T c (l₁ ++ l₂) := by
  intro c l₁ l₂ h₁ h₂
  induction l₁ generalizing c with
  | nil => exact h₂
  | cons r l ih => exact ⟨h₁.1, ih h₁.2 h₂⟩

theorem Ctr.stepAll_append (c : Ctr) (l₁ l₂ : List LineRec) :
    c.stepAll (l₁ ++ l₂) = (c.stepAll l₁).stepAll l₂ := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons r l ih => exact ih (c.step r)

theorem declsAlong_append (T : Tabs) :
    ∀ (c : Ctr) (l₁ l₂ : List LineRec) (acc : Array Declaration),
    declsAlong T c (l₁ ++ l₂) acc = declsAlong T (c.stepAll l₁) l₂ (declsAlong T c l₁ acc) := by
  intro c l₁ l₂ acc
  induction l₁ generalizing c acc with
  | nil => rfl
  | cons r l ih => exact ih _ _


/-! ## The characterisation, the other way -/

/-- Every line of a list binds an index at or above its table's
counter. -/
@[expose] def IncAll : Ctr → List LineRec → Prop
  | _, [] => True
  | c, r :: rs => c.fits r = true ∧ IncAll (c.step r) rs

/-- A state's own tables, as partial maps. -/
@[expose] def Tabs.ofState (st : StateD) : Tabs := ⟨st.names.get?, st.levels.get?, st.exprs.get?⟩

/-- A state binds nothing at or above counters `c`. -/
structure Above (st : StateD) (c : Ctr) : Prop where
  n : ∀ j, c.n ≤ j → st.names.get? j = none
  l : ∀ j, c.l ≤ j → st.levels.get? j = none
  e : ∀ j, c.e ≤ j → st.exprs.get? j = none

theorem Above.holds {st : StateD} {c : Ctr} (h : Above st c) : Holds st (Tabs.ofState st) c := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩ <;> simp only [Tabs.ofState] <;> split
  · rfl
  · exact h.n j (by omega)
  · rfl
  · exact h.l j (by omega)
  · rfl
  · exact h.e j (by omega)

/-- A one-index change of a table, seen below a counter it lies at or
above. -/
theorem get?_insert_below {t : IdTable α} {i k j : Nat} {x : α} (hki : k ≤ i) (hj : j < k) :
    (t.insert i x).get? j = t.get? j := by
  rw [IdTable.get?_insert]; simp [show j ≠ i by omega]

/-- **The characterisation, the other way**: a serial fold over an
increasing list, from a state binding nothing at or above the
counters, that succeeds has every line right at its final tables, and
holds them. -/
theorem allOK_of_applyList :
    ∀ (c : Ctr) (rs : List LineRec) (st : StateD) (k : Nat) (st' : StateD) (k' : Nat),
    IncAll c rs → Above st c → applyList st rs k = .ok (st', k') →
    AllOK (Tabs.ofState st') c rs ∧ Holds st (Tabs.ofState st') c ∧
      Above st' (c.stepAll rs) ∧ st'.decls = declsAlong (Tabs.ofState st') c rs st.decls := by
  intro c rs
  induction rs generalizing c with
  | nil =>
    intro st k st' k' _ ha h
    simp only [applyList, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, ha.holds, ha, rfl⟩
  | cons r rs ih =>
    intro st k st' k' hinc ha h
    obtain ⟨hfit, hrs⟩ := hinc
    simp only [applyList] at h
    cases r with
    | name i x =>
      simp only [Ctr.fits, decide_eq_true_eq] at hfit
      have hb : st.names.bound i = false := by rw [IdTable.bound_eq, ha.n i hfit]; rfl
      cases hx : nameOf st.lk x with
      | error m =>
        simp [applyLine, parseNameEntryD, hx, bind, Except.bind] at h
      | ok v =>
        simp only [applyLine, parseNameEntryD, hx, StateD.freshName, hb, bind, Except.bind,
          pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at h
        have ha1 : Above { st with names := st.names.insert i v } (c.step (.name i x)) :=
          ⟨fun j hj => by
            simp only [Ctr.step] at hj
            rw [IdTable.get?_insert]; simp [show j ≠ i by omega, ha.n j (by omega)],
           ha.l, ha.e⟩
        obtain ⟨hok, hh1, ha', hd⟩ := ih _ _ _ _ _ hrs ha1 h
        have hT : ∀ j, j < i + 1 → (Tabs.ofState st').n j =
            (st.names.insert i v).get? j := fun j hj => by
          have := hh1.n j; simp only [Ctr.step, hj, ↓reduceIte] at this; exact this.symm
        have hst : Holds st (Tabs.ofState st') c :=
          ⟨fun j => by
            split
            · rw [hT j (by omega), get?_insert_below hfit (by omega)]
            · exact ha.n j (by omega),
           hh1.l,
           hh1.e⟩
        refine ⟨⟨⟨hfit, fun j h1 h2 => ?_, v, ?_, ?_⟩, hok⟩, hst, ha', ?_⟩
        · rw [hT j (by omega), get?_insert_below (k := i) (Nat.le_refl _) h2]; exact ha.n j h1
        · rw [hT i (by omega), IdTable.get?_insert]; simp
        · rw [← hst.lk]; exact hx
        · rw [hd]; rfl
    | level i x =>
      simp only [Ctr.fits, decide_eq_true_eq] at hfit
      have hb : st.levels.bound i = false := by rw [IdTable.bound_eq, ha.l i hfit]; rfl
      cases hx : levelOf st.lk x with
      | error m =>
        simp [applyLine, parseLevelEntryD, hx, StateD.freshLevel, hb, bind, Except.bind, pure, Except.pure] at h
      | ok v =>
        simp only [applyLine, parseLevelEntryD, hx, StateD.freshLevel, hb, bind, Except.bind,
          pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at h
        have ha1 : Above { st with levels := st.levels.insert i v } (c.step (.level i x)) :=
          ⟨ha.n, fun j hj => by
            simp only [Ctr.step] at hj
            rw [IdTable.get?_insert]; simp [show j ≠ i by omega, ha.l j (by omega)],
           ha.e⟩
        obtain ⟨hok, hh1, ha', hd⟩ := ih _ _ _ _ _ hrs ha1 h
        have hT : ∀ j, j < i + 1 → (Tabs.ofState st').l j =
            (st.levels.insert i v).get? j := fun j hj => by
          have := hh1.l j; simp only [Ctr.step, hj, ↓reduceIte] at this; exact this.symm
        have hst : Holds st (Tabs.ofState st') c :=
          ⟨hh1.n,
           fun j => by
            split
            · rw [hT j (by omega), get?_insert_below hfit (by omega)]
            · exact ha.l j (by omega),
           hh1.e⟩
        refine ⟨⟨⟨hfit, fun j h1 h2 => ?_, v, ?_, ?_⟩, hok⟩, hst, ha', ?_⟩
        · rw [hT j (by omega), get?_insert_below (k := i) (Nat.le_refl _) h2]; exact ha.l j h1
        · rw [hT i (by omega), IdTable.get?_insert]; simp
        · rw [← hst.lk]; exact hx
        · rw [hd]; rfl
    | expr i x =>
      simp only [Ctr.fits, decide_eq_true_eq] at hfit
      have hb : st.exprs.bound i = false := by rw [IdTable.bound_eq, ha.e i hfit]; rfl
      cases hx : exprOf st.lk x with
      | error m =>
        simp [applyLine, parseExprEntryD, hx, StateD.freshExpr, hb, bind, Except.bind, pure, Except.pure] at h
      | ok v =>
        simp only [applyLine, parseExprEntryD, hx, StateD.freshExpr, hb, bind, Except.bind,
          pure, Except.pure, Bool.false_eq_true, ↓reduceIte] at h
        have ha1 : Above { st with exprs := st.exprs.insert i v } (c.step (.expr i x)) :=
          ⟨ha.n, ha.l, fun j hj => by
            simp only [Ctr.step] at hj
            rw [IdTable.get?_insert]; simp [show j ≠ i by omega, ha.e j (by omega)]⟩
        obtain ⟨hok, hh1, ha', hd⟩ := ih _ _ _ _ _ hrs ha1 h
        have hT : ∀ j, j < i + 1 → (Tabs.ofState st').e j =
            (st.exprs.insert i v).get? j := fun j hj => by
          have := hh1.e j; simp only [Ctr.step, hj, ↓reduceIte] at this; exact this.symm
        have hst : Holds st (Tabs.ofState st') c :=
          ⟨hh1.n,
           hh1.l,
           fun j => by
            split
            · rw [hT j (by omega), get?_insert_below hfit (by omega)]
            · exact ha.e j (by omega)⟩
        refine ⟨⟨⟨hfit, fun j h1 h2 => ?_, v, ?_, ?_⟩, hok⟩, hst, ha', ?_⟩
        · rw [hT j (by omega), get?_insert_below (k := i) (Nat.le_refl _) h2]; exact ha.e j h1
        · rw [hT i (by omega), IdTable.get?_insert]; simp
        · rw [← hst.lk]; exact hx
        · rw [hd]; rfl
    | decl d =>
      cases hx : declOf st.lk d with
      | error m => simp [applyLine, applyDeclD, processLineCoreD, hx, bind, Except.bind] at h
      | ok y =>
        cases y with
        | inr w => simp [applyLine, applyDeclD, processLineCoreD, hx, bind, Except.bind, pure,
            Except.pure] at h
        | inl x =>
          simp only [applyLine, applyDeclD, processLineCoreD, hx, bind, Except.bind, pure,
            Except.pure] at h
          have ha1 : Above (pushDecl st x) c := ⟨ha.n, ha.l, ha.e⟩
          obtain ⟨hok, hh1, ha', hd⟩ := ih _ _ _ _ _ hrs ha1 h
          have hst : Holds st (Tabs.ofState st') c := ⟨hh1.n, hh1.l, hh1.e⟩
          have hx' : declOf (cutLk (Tabs.ofState st') c) d = .ok (.inl x) := by
            rw [← hst.lk]; exact hx
          refine ⟨⟨⟨x, hx'⟩, hok⟩, hst, ha', ?_⟩
          rw [hd]; simp only [declsAlong, lineDecl, hx', Ctr.step, pushDecl]
    | header =>
      simp only [applyLine, pure, Except.pure] at h
      obtain ⟨hok, hh1, ha', hd⟩ := ih _ _ _ _ _ hrs ha h
      exact ⟨⟨trivial, hok⟩, hh1, ha', hd⟩
    | blank =>
      simp only [applyLine, pure, Except.pure] at h
      obtain ⟨hok, hh1, ha', hd⟩ := ih _ _ _ _ _ hrs ha h
      exact ⟨⟨trivial, hok⟩, hh1, ha', hd⟩

end ConLeche.Frontend
