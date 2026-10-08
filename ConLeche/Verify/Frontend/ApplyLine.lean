module

public import ConLeche.Frontend.ExportC
import ConLeche.Verify.ExceptBind

public section

/-!
# What one line does to the parse state (task #290)

The file theorem reads three facts off the parse state — a name index
bound to `False`, an expression index bound to the constant `False`, a
theorem record pushed with that type — and carries each across every
other line of the file.  This module proves what it needs of
`applyLine`, line by line:

* **the frame of a declaration record** (`Frame`): the index tables
  are untouched and the record list only grows.
  `processLineCoreD_frame`:
  every kind is `declOf` — which returns no state — followed by one
  `pushDecl`.
* **preservation across any line** (`applyLine_keeps`): a bound index
  stays bound to its entry (a rebinding is a parse error since task
  #290) and a pushed record stays.
* **the two table lines of the template** (`applyLine_nameFalse`,
  `applyLine_constFalse`): what the name entry and the expression
  entry do.  The theorem record is `ThmLine.lean`'s.
-/

namespace ConLeche.Frontend

/-! ## The frame of a declaration record -/

/-- What a declaration record leaves alone, and the record list it only
extends. -/
structure Frame (st st' : StateD) : Prop where
  names : st'.names = st.names
  levels : st'.levels = st.levels
  exprs : st'.exprs = st.exprs
  decls : ∀ d ∈ st.decls, d ∈ st'.decls

/-- Pushing a record. -/
theorem push_frame (st : StateD) (x : Declaration) :
    Frame st { st with decls := st.decls.push x } :=
  ⟨rfl, rfl, rfl, fun _ h => Array.mem_push.mpr (.inl h)⟩

theorem pushDecl_frame (st : StateD) (d : Declaration) : Frame st (pushDecl st d) :=
  push_frame _ _

/-- A declaration record that succeeds pushes the record its builder
returns, and nothing else. -/
theorem processLineCoreD_ok {st st' : StateD} {d : DeclRec}
    (h : processLineCoreD st d = .ok (.inl st')) :
    ∃ x, declOf st.lk d = .ok (.inl x) ∧ st' = pushDecl st x := by
  unfold processLineCoreD at h
  obtain ⟨r, hr, h⟩ := exceptBind_ok h
  cases r with
  | inl x =>
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h
    exact ⟨x, hr, h.symm⟩
  | inr v => simp [pure, Except.pure] at h

theorem processLineCoreD_frame {st st' : StateD} {d : DeclRec}
    (h : processLineCoreD st d = .ok (.inl st')) : Frame st st' := by
  obtain ⟨x, _, rfl⟩ := processLineCoreD_ok h
  exact pushDecl_frame _ _

/-- A declaration record IS its semantics (task #292: no pre-scan). -/
theorem applyDeclD_frame {st st' : StateD} {d : DeclRec}
    (h : applyDeclD st d = .ok (.inl st')) : Frame st st' :=
  processLineCoreD_frame h

/-! ## What any line keeps -/

/-- What every successful line keeps of the state: bound entries and
pushed records. -/
structure Keeps (st st' : StateD) : Prop where
  names : ∀ i n, st.names.get? i = some n → st'.names.get? i = some n
  exprs : ∀ i e, st.exprs.get? i = some e → st'.exprs.get? i = some e
  decls : ∀ d ∈ st.decls, d ∈ st'.decls

theorem Keeps.refl (st : StateD) : Keeps st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩

theorem Keeps.trans {st st₁ st₂ : StateD} (h₁ : Keeps st st₁) (h₂ : Keeps st₁ st₂) :
    Keeps st st₂ :=
  ⟨fun i n h => h₂.names i n (h₁.names i n h), fun i e h => h₂.exprs i e (h₁.exprs i e h),
   fun d h => h₂.decls d (h₁.decls d h)⟩

theorem Keeps.of_frame {st st' : StateD} (f : Frame st st') : Keeps st st' :=
  ⟨fun i n h => by rw [f.names]; exact h, fun i e h => by rw [f.exprs]; exact h, f.decls⟩

/-- A fresh index is unbound. -/
theorem fresh_none {t : IdTable α} {i : Nat} (h : t.bound i = false) : t.get? i = none := by
  rw [IdTable.bound_eq] at h
  cases hg : t.get? i with
  | none => rfl
  | some _ => rw [hg] at h; simp at h

/-- Binding a fresh index keeps every bound entry. -/
theorem get?_insert_fresh {t : IdTable α} {i : Nat} {x : α} (h : t.bound i = false)
    {j : Nat} {y : α} (hj : t.get? j = some y) : (t.insert i x).get? j = some y := by
  rw [IdTable.get?_insert]
  split
  · rename_i hji; subst hji; rw [fresh_none h] at hj; simp at hj
  · exact hj

theorem StateD.freshName_ok {st : StateD} {i : Nat} (h : st.freshName i = .ok ()) :
    st.names.bound i = false := by
  unfold StateD.freshName at h
  split at h
  · cases h
  · rename_i hb; simpa using hb

theorem StateD.freshExpr_ok {st : StateD} {i : Nat} (h : st.freshExpr i = .ok ()) :
    st.exprs.bound i = false := by
  unfold StateD.freshExpr at h
  split at h
  · cases h
  · rename_i hb; simpa using hb

/-- A name entry: the name table gains a fresh binding, nothing else moves. -/
theorem parseNameEntryD_spec {st st' : StateD} {i : Nat} {r : NameRec}
    (h : parseNameEntryD st i r = .ok st') :
    st.names.bound i = false ∧ ∃ n, st' = { st with names := st.names.insert i n } := by
  cases r with
  | str pre s =>
    unfold parseNameEntryD at h
    obtain ⟨p, _, h⟩ := exceptBind_ok h
    obtain ⟨_, hf, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨StateD.freshName_ok hf, _, h.symm⟩
  | num pre n =>
    unfold parseNameEntryD at h
    obtain ⟨p, _, h⟩ := exceptBind_ok h
    obtain ⟨_, hf, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨StateD.freshName_ok hf, _, h.symm⟩

/-- A level entry: the level table gains a binding, nothing else moves. -/
theorem parseLevelEntryD_spec {st st' : StateD} {i : Nat} {r : LevelRec}
    (h : parseLevelEntryD st i r = .ok st') :
    ∃ l, st' = { st with levels := st.levels.insert i l } := by
  unfold parseLevelEntryD at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨l, _, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨l, h.symm⟩

/-- An expression entry: the expression table gains a fresh binding,
nothing else moves. -/
theorem parseExprEntryD_spec {st st' : StateD} {i : Nat} {r : ExprRec}
    (h : parseExprEntryD st i r = .ok st') :
    st.exprs.bound i = false ∧ ∃ e, st' = { st with exprs := st.exprs.insert i e } := by
  unfold parseExprEntryD at h
  obtain ⟨_, hf, h⟩ := exceptBind_ok h
  refine ⟨StateD.freshExpr_ok hf, ?_⟩
  obtain ⟨e, _, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨e, h.symm⟩

theorem applyLine_keeps {st st' : StateD} {r : LineRec} (h : applyLine st r = .ok (.inl st')) :
    Keeps st st' := by
  cases r with
  | header =>
    simp only [applyLine, pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    exact Keeps.refl _
  | blank =>
    simp only [applyLine, pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    exact Keeps.refl _
  | name i r =>
    simp only [applyLine] at h
    obtain ⟨st₁, hn, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    obtain ⟨hfresh, n, rfl⟩ := parseNameEntryD_spec hn
    exact ⟨fun j y hj => get?_insert_fresh hfresh hj, fun _ _ h => h, fun _ h => h⟩
  | level i r =>
    simp only [applyLine] at h
    obtain ⟨st₁, hl, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    obtain ⟨l, rfl⟩ := parseLevelEntryD_spec hl
    exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩
  | expr i r =>
    simp only [applyLine] at h
    obtain ⟨st₁, he, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    obtain ⟨hfresh, e, rfl⟩ := parseExprEntryD_spec he
    exact ⟨fun _ _ h => h, fun j y hj => get?_insert_fresh hfresh hj, fun _ h => h⟩
  | decl d =>
    simp only [applyLine] at h
    exact Keeps.of_frame (applyDeclD_frame h)

/-! ## The two table lines of the template -/

/-- `{"in":i,"str":{"pre":0,"str":"False"}}`: index `i` is `False`. -/
theorem applyLine_nameFalse {st st' : StateD} {i : Nat}
    (h : applyLine st (.name i (.str 0 "False")) = .ok (.inl st'))
    (h0 : st.names.get? 0 = some .anonymous) : st'.names.get? i = some falseName := by
  simp only [applyLine] at h
  obtain ⟨st₁, hn, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
  unfold parseNameEntryD at hn
  obtain ⟨p, hp, hn⟩ := exceptBind_ok hn
  obtain ⟨_, _, hn⟩ := exceptBind_ok hn
  simp only [pure, Except.pure, Except.ok.injEq] at hn; subst hn
  have hp' : p = falseName := by
    simp only [nameOf, StateD.lk, StateD.name, h0, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hp
    exact hp.symm
  subst hp'
  simp only [IdTable.get?_insert, ↓reduceIte]

/-- `{"ie":j,"const":{"name":i,"us":[]}}`: index `j` is the constant
`False`. -/
theorem applyLine_constFalse {st st' : StateD} {i j : Nat}
    (h : applyLine st (.expr j (.const i [])) = .ok (.inl st'))
    (hi : st.names.get? i = some falseName) :
    st'.exprs.get? j = some (Expr.mkConst falseName []) := by
  simp only [applyLine] at h
  obtain ⟨st₁, he, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
  unfold parseExprEntryD at he
  obtain ⟨_, _, he⟩ := exceptBind_ok he
  -- the entry is `mkConst False []`: the name, the (empty) levels, the node
  obtain ⟨e, hex, he⟩ := exceptBind_ok he
  simp only [exprOf, StateD.lk, StateD.name, hi, List.mapM_nil, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq] at hex
  subst hex
  simp only [pure, Except.pure, Except.ok.injEq] at he; subst he
  simp [IdTable.get?_insert]

end ConLeche.Frontend
