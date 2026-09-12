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
  `processLineCoreD_frame` is the case analysis over the six kinds;
  the inductive kind is `validateIndD` — which returns no state —
  followed by `installIndD`, whose pushes go through `pushDecl`,
  `pushGenList` and the projection-owner registration.
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

theorem Frame.refl (st : StateD) : Frame st st :=
  ⟨rfl, rfl, rfl, fun _ h => h⟩

theorem Frame.trans {st st₁ st₂ : StateD} (h₁ : Frame st st₁) (h₂ : Frame st₁ st₂) :
    Frame st st₂ :=
  ⟨h₂.names.trans h₁.names, h₂.levels.trans h₁.levels, h₂.exprs.trans h₁.exprs,
   fun d hd => h₂.decls d (h₁.decls d hd)⟩

/-- A state update that touches none of the framed fields. -/
theorem Frame.of_eq {st st' : StateD} (hn : st'.names = st.names) (hl : st'.levels = st.levels)
    (he : st'.exprs = st.exprs) (hd : st'.decls = st.decls) : Frame st st' :=
  ⟨hn, hl, he, fun _ h => hd ▸ h⟩

theorem noteDecl_frame (st : StateD) (d : Declaration) : Frame st (noteDecl st d) :=
  Frame.of_eq rfl rfl rfl rfl

/-- Pushing a record. -/
theorem push_frame (st : StateD) (x : Declaration) :
    Frame st { st with decls := st.decls.push x } :=
  ⟨rfl, rfl, rfl, fun _ h => Array.mem_push.mpr (.inl h)⟩

theorem pushDecl_frame (st : StateD) (d : Declaration) : Frame st (pushDecl st d) :=
  (push_frame _ _).trans (noteDecl_frame _ _)

theorem noteProjIota_frame (st : StateD) (cv : ConstantVal) : Frame st (noteProjIota st cv) := by
  unfold noteProjIota
  split
  · split
    · exact Frame.of_eq rfl rfl rfl rfl
    · exact Frame.refl _
  · exact Frame.refl _

theorem pushGenD_frame (st : StateD) (d : Declaration) : Frame st (pushGenD st d) := by
  unfold pushGenD
  split
  · exact (noteProjIota_frame _ _).trans (pushDecl_frame _ _)
  · exact pushDecl_frame _ _

theorem noteGen_frame (st : StateD) (d : Declaration) (T0 : Name) :
    Frame st (noteGen st d T0) := by
  unfold noteGen
  exact Frame.of_eq rfl rfl rfl rfl

theorem pushGenList_frame (st : StateD) (gen : List Declaration) (T0 : Name) :
    Frame st (pushGenList st gen T0) := by
  induction gen generalizing st with
  | nil => exact Frame.refl _
  | cons d ds ih =>
    exact ((pushGenD_frame _ _).trans (noteGen_frame _ _ _)).trans (ih _)

theorem registerProjOwners_frame {st st' : StateD} {tys cts rcs block}
    (h : registerProjOwners st tys cts rcs block = .ok st') : Frame st st' := by
  unfold registerProjOwners at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  try dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact Frame.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact Frame.of_eq rfl rfl rfl rfl

theorem installIndD_frame {st st' : StateD} {tys cts rcs nPd}
    (h : installIndD st tys cts rcs nPd = .ok (.inl st')) : Frame st st' := by
  unfold installIndD at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  try dsimp only at h
  obtain ⟨st₁, hreg, h⟩ := exceptBind_ok h
  have hf₁ := registerProjOwners_frame hreg
  refine hf₁.trans ?_
  try dsimp only at h
  obtain ⟨b, _, h⟩ := exceptBind_ok h
  try dsimp only at h
  refine (Frame.of_eq (st := st₁) (st' := { st₁ with indBlocks :=
    (b.types.foldl (fun m t => m.insert t.cv.name b) st₁.indBlocks) })
    rfl rfl rfl rfl).trans ?_
  split at h
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
        refine (Frame.of_eq ?_ ?_ ?_ ?_).trans (pushDecl_frame _ _) <;> rfl
      · exact absurd h (by simp [pure, Except.pure])
    · rename_i gen _
      simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      refine Frame.trans ?_ (pushDecl_frame _ _)
      exact ⟨(pushGenList_frame _ gen _).names, (pushGenList_frame _ gen _).levels,
        (pushGenList_frame _ gen _).exprs, fun d hd => (pushGenList_frame _ gen _).decls d hd⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    exact pushDecl_frame _ _

theorem processLineCoreD_frame {st st' : StateD} {d : DeclRec}
    (h : processLineCoreD st d = .ok (.inl st')) : Frame st st' := by
  cases d with
  | ax cvr isUnsafe =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · exact absurd h (by simp [pure, Except.pure])
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact pushDecl_frame _ _
  | defn cvr value hints safety =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · obtain ⟨vl, _, h⟩ := exceptBind_ok h
      try dsimp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
        exact (pushDecl_frame _ _).trans (Frame.of_eq rfl rfl rfl rfl)
      · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
        exact pushDecl_frame _ _
    · exact absurd h (by simp [pure, Except.pure])
  | thm cvr value =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    obtain ⟨vl, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact (pushDecl_frame _ _).trans (Frame.of_eq rfl rfl rfl rfl)
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact pushDecl_frame _ _
  | opaq cvr value isUnsafe =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · exact absurd h (by simp [pure, Except.pure])
    · obtain ⟨vl, _, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact pushDecl_frame _ _
  | quot cvr kind =>
    unfold processLineCoreD at h
    obtain ⟨cv, _, h⟩ := exceptBind_ok h
    simp only at h
    -- the kind: four constructors and the unknown-kind throw
    split at h <;> (obtain ⟨qk, hqk, h⟩ := exceptBind_ok h) <;> cases hqk <;>
      (simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
       exact pushDecl_frame _ _)
  | ind tys cts rcs =>
    unfold processLineCoreD at h
    obtain ⟨v, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · exact absurd h (by simp [pure, Except.pure])
    · exact (Frame.of_eq (st := st) (st' := { st with indCount := st.indCount + 1 }) rfl rfl rfl
        rfl).trans (installIndD_frame h)

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
  simp only at h
  cases r <;> (repeat (obtain ⟨_, _, h⟩ := exceptBind_ok h)) <;>
    simp only [pure, Except.pure, Except.ok.injEq] at h <;> exact ⟨_, h.symm⟩

/-- An expression entry: the expression table gains a fresh binding,
nothing else moves. -/
theorem parseExprEntryD_spec {st st' : StateD} {i : Nat} {r : ExprRec}
    (h : parseExprEntryD st i r = .ok st') :
    st.exprs.bound i = false ∧ ∃ e, st' = { st with exprs := st.exprs.insert i e } := by
  unfold parseExprEntryD at h
  obtain ⟨_, hf, h⟩ := exceptBind_ok h
  simp only at h
  refine ⟨StateD.freshExpr_ok hf, ?_⟩
  -- every kind: its reads, then the entry
  cases r <;> (repeat (obtain ⟨_, _, h⟩ := exceptBind_ok h))
  all_goals (injection h with h; subst h; exact ⟨_, rfl⟩)

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
  have hp' : p = .anonymous := by
    unfold StateD.name at hp; rw [h0] at hp
    simp only [pure, Except.pure, Except.ok.injEq] at hp; exact hp.symm
  subst hp'
  simp only [IdTable.get?_insert, ↓reduceIte]
  rfl

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
  simp only at he
  -- the entry is `mkConst False []`: the name, the (empty) levels, the node
  obtain ⟨nm, hnm, he⟩ := exceptBind_ok he
  have hnm' : nm = falseName := by
    unfold StateD.name at hnm; rw [hi] at hnm
    simp only [pure, Except.pure, Except.ok.injEq] at hnm; exact hnm.symm
  subst hnm'
  obtain ⟨ls, hls, he⟩ := exceptBind_ok he
  have hls' : ls = [] := by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hls; exact hls.symm
  subst hls'
  obtain ⟨e, hex, he⟩ := exceptBind_ok he
  simp only [pure, Except.pure, Except.ok.injEq] at hex; subst hex
  simp only [pure, Except.pure, Except.ok.injEq] at he; subst he
  simp [IdTable.get?_insert]

end ConLeche.Frontend
