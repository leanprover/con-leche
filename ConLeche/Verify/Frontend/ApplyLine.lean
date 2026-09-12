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

* **the frame of a declaration record** (`Frame`): the index tables,
  the taint tables and the prelude are untouched, and the record list
  only grows.  `processLineCoreD_frame` is the case analysis over the
  six kinds; the inductive kind is `validateIndD` — which returns no
  state — followed by `installIndD`, whose pushes go through
  `pushDecl`, `pushGenList` and the projection-owner registration.
* **preservation across any line** (`applyLine_*`): a bound index stays
  bound to its entry (a rebinding is a parse error since task #290), a
  pushed record stays, the taint skips only grow, and the two taint
  invariants the theorem tracks hold up.
* **the three lines themselves** (`applyLine_nameFalse`,
  `applyLine_constFalse`, `applyLine_thmFalse`): what the name entry,
  the expression entry and the theorem record of the template do.
-/

namespace ConLeche.Frontend

open ConLeche.Cached (DeclC ExprC)

/-! ## The frame of a declaration record -/

/-- What a declaration record leaves alone, and the record list it only
extends. -/
structure Frame (st st' : StateD) : Prop where
  names : st'.names = st.names
  levels : st'.levels = st.levels
  exprs : st'.exprs = st.exprs
  tainted : st'.tainted = st.tainted
  taintedNames : st'.taintedNames = st.taintedNames
  taintSkipped : st'.taintSkipped = st.taintSkipped
  prelude : st'.prelude = st.prelude
  decls : ∀ d ∈ st.decls, d ∈ st'.decls

theorem Frame.refl (st : StateD) : Frame st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

theorem Frame.trans {st st₁ st₂ : StateD} (h₁ : Frame st st₁) (h₂ : Frame st₁ st₂) :
    Frame st st₂ :=
  ⟨h₂.names.trans h₁.names, h₂.levels.trans h₁.levels, h₂.exprs.trans h₁.exprs,
   h₂.tainted.trans h₁.tainted, h₂.taintedNames.trans h₁.taintedNames,
   h₂.taintSkipped.trans h₁.taintSkipped, h₂.prelude.trans h₁.prelude,
   fun d hd => h₂.decls d (h₁.decls d hd)⟩

/-- A state update that touches none of the framed fields. -/
theorem Frame.of_eq {st st' : StateD} (hn : st'.names = st.names) (hl : st'.levels = st.levels)
    (he : st'.exprs = st.exprs) (ht : st'.tainted = st.tainted)
    (htn : st'.taintedNames = st.taintedNames) (hts : st'.taintSkipped = st.taintSkipped)
    (hp : st'.prelude = st.prelude) (hd : st'.decls = st.decls) : Frame st st' :=
  ⟨hn, hl, he, ht, htn, hts, hp, fun _ h => hd ▸ h⟩

theorem noteDecl_frame (st : StateD) (d : DeclC) : Frame st (noteDecl st d) :=
  Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl

/-- Pushing a record. -/
theorem push_frame (st : StateD) (x : DeclC) : Frame st { st with decls := st.decls.push x } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => Array.mem_push.mpr (.inl h)⟩

theorem pushDecl_frame {st st' : StateD} {d : DeclC} (h : pushDecl st d = .inl st') :
    Frame st st' := by
  unfold pushDecl at h
  split at h
  · split at h
    · simp only [Sum.inl.injEq] at h; subst h
      exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl
    · simp only [Sum.inl.injEq] at h; subst h
      exact (push_frame _ _).trans (noteDecl_frame _ _)
  · split at h
    · simp only [Sum.inl.injEq] at h; subst h
      exact (push_frame _ _).trans (noteDecl_frame _ _)
    · split at h
      · simp only [Sum.inl.injEq] at h; subst h
        exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl
      · exact absurd h (by simp)

theorem noteProjIota_frame (st : StateD) (cv : ConstantVal) : Frame st (noteProjIota st cv) := by
  unfold noteProjIota
  split
  · split
    · exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl
    · exact Frame.refl _
  · exact Frame.refl _

theorem pushGenD_frame {st st' : StateD} {d : DeclC} (h : pushGenD st d = .inl st') :
    Frame st st' := by
  unfold pushGenD at h
  split at h
  · exact (noteProjIota_frame _ _).trans (pushDecl_frame h)
  · exact pushDecl_frame h

theorem noteGen_frame (st : StateD) (d : DeclC) (T0 : Name) : Frame st (noteGen st d T0) := by
  unfold noteGen
  exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl

theorem pushGenList_frame {st st' : StateD} {T0 : Name} :
    ∀ {gen : List DeclC}, pushGenList st gen T0 = .inl st' → Frame st st' := by
  intro gen
  induction gen generalizing st with
  | nil => intro h; simp only [pushGenList, Sum.inl.injEq] at h; subst h; exact Frame.refl _
  | cons d ds ih =>
    intro h
    simp only [pushGenList] at h
    split at h
    · rename_i st₁ hpush
      refine (pushGenD_frame hpush).trans ?_
      split at h
      · exact (noteGen_frame _ _ _).trans (ih h)
      · exact ih h
    · rename_i hne
      exact (hne _ h).elim

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
    exact Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl

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
  split at h
  · -- a basis pin
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact (Frame.of_eq (st := st₁) (st' := { st₁ with punitSeen := true }) rfl rfl rfl rfl rfl
        rfl rfl rfl).trans (pushDecl_frame h)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact pushDecl_frame h
  · obtain ⟨b, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    refine (Frame.of_eq (st := st₁) (st' := { st₁ with indBlocks :=
      (b.types.foldl (fun m t => m.insert t.cv.name b) st₁.indBlocks) })
      rfl rfl rfl rfl rfl rfl rfl rfl).trans ?_
    split at h
    · split at h
      · split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          refine (Frame.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans (pushDecl_frame h) <;> rfl
        · exact absurd h (by simp [pure, Except.pure])
      · split at h
        · exact absurd h (by simp [pure, Except.pure])
        · rename_i st₂ hgen
          simp only [pure, Except.pure, Except.ok.injEq] at h
          refine ((pushGenList_frame hgen).trans
            (Frame.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)).trans (pushDecl_frame h) <;> rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact pushDecl_frame h

/-- `Sum.map` lands in `inl` only from `inl`. -/
theorem Sum.map_inl_eq {α β γ δ : Type} {f : α → γ} {g : β → δ} {x : α ⊕ β} {y : γ}
    (h : Sum.map f g x = .inl y) : ∃ a, x = .inl a ∧ y = f a := by
  cases x with
  | inl a => exact ⟨a, rfl, by simpa [Sum.map] using h.symm⟩
  | inr b => simp [Sum.map] at h

theorem processLineCoreD_frame {st st' : StateD} {d : DeclRec}
    (h : processLineCoreD st d = .ok (.inl st')) : Frame st st' := by
  cases d with
  | ax cvr isUnsafe =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · exact absurd h (by simp [pure, Except.pure])
    · split at h
      · split at h
        · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
          exact Frame.refl _
        · exact absurd h (by simp [pure, Except.pure])
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact pushDecl_frame h
  | defn cvr value hints safety =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · obtain ⟨vl, _, h⟩ := exceptBind_ok h
      try dsimp only at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨s, hs, rfl⟩ := Sum.map_inl_eq h
        exact (pushDecl_frame hs).trans (Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact pushDecl_frame h
    · exact absurd h (by simp [pure, Except.pure])
  | thm cvr value =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    obtain ⟨vl, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨s, hs, rfl⟩ := Sum.map_inl_eq h
      exact (pushDecl_frame hs).trans (Frame.of_eq rfl rfl rfl rfl rfl rfl rfl rfl)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact pushDecl_frame h
  | opaq cvr value isUnsafe =>
    unfold processLineCoreD at h
    obtain ⟨cvp, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · exact absurd h (by simp [pure, Except.pure])
    · obtain ⟨vl, _, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact pushDecl_frame h
  | quot cvr kind =>
    unfold processLineCoreD at h
    obtain ⟨cv, _, h⟩ := exceptBind_ok h
    simp only at h
    split at h
    all_goals try
      obtain ⟨slot, hs, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hs
      subst hs
    all_goals first
      | cases h
      | (split at h
         · split at h
           · simp only [pure, Except.pure, Except.ok.injEq] at h
             exact pushDecl_frame h
           · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
             exact Frame.refl _
         · exact absurd h (by simp [pure, Except.pure]))
  | ind tys cts rcs =>
    unfold processLineCoreD at h
    obtain ⟨v, _, h⟩ := exceptBind_ok h
    try dsimp only at h
    split at h
    · exact absurd h (by simp [pure, Except.pure])
    · exact (Frame.of_eq (st := st) (st' := { st with indCount := st.indCount + 1 }) rfl rfl rfl
        rfl rfl rfl rfl rfl).trans (installIndD_frame h)

/-! ## What any line preserves -/

/-- The taint invariant: a tainted name that is not a tolerated axiom's
came from a skipped declaration, so the skips are non-empty. -/
def TaintInv (st : StateD) : Prop :=
  ∀ n, n ∉ toleratedAxiomNames → st.taintedNames[n]?.isSome → st.taintSkipped ≠ #[]

-- The common tail of `applyDeclD` after its tolerated-axiom test: the
-- taint pre-scan, then the record's own semantics (the join points
-- already inlined by `simp only`).  Unhygienic: names `h`.
set_option hygiene false in
macro "applyDecl_tail" : tactic => `(tactic| (
  split at h
  · obtain ⟨p, _, h⟩ := exceptBind_ok h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact .inr (.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun hx => by
        have := congrArg Array.size hx; simp at this⟩)
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
        exact .inl (processLineCoreD_frame ‹_›)
      · split at h
        · exact absurd h (by simp [pure, Except.pure])
        · cases h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact .inl (processLineCoreD_frame ‹_›)
    · split at h
      · exact absurd h (by simp [pure, Except.pure])
      · cases h))

/-- A declaration record: the frame, or a skip (then the skips are
non-empty and nothing else of interest moved), or a tolerated axiom's
name recorded. -/
theorem applyDeclD_cases {st st' : StateD} {d : DeclRec}
    (h : applyDeclD st d = .ok (.inl st')) :
    Frame st st' ∨
    (st'.names = st.names ∧ st'.levels = st.levels ∧ st'.exprs = st.exprs ∧
      st'.tainted = st.tainted ∧ st'.prelude = st.prelude ∧ st'.decls = st.decls ∧
      st'.taintSkipped ≠ #[]) ∨
    (∃ name, name ∈ toleratedAxiomNames ∧ st'.names = st.names ∧ st'.levels = st.levels ∧
      st'.exprs = st.exprs ∧ st'.tainted = st.tainted ∧ st'.prelude = st.prelude ∧
      st'.decls = st.decls ∧ st'.taintSkipped = st.taintSkipped ∧
      st'.taintedNames = st.taintedNames.insert name name) := by
  cases d with
  | ax cvr u =>
    unfold applyDeclD at h
    simp only at h
    obtain ⟨name, _, h⟩ := exceptBind_ok h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      refine .inr (.inr ⟨name, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      rename_i hmem
      exact List.contains_iff_mem.mp hmem
    · applyDecl_tail
  | defn cvr value hints safety => unfold applyDeclD at h; simp only at h; applyDecl_tail
  | thm cvr value => unfold applyDeclD at h; simp only at h; applyDecl_tail
  | opaq cvr value u => unfold applyDeclD at h; simp only at h; applyDecl_tail
  | quot cvr kind => unfold applyDeclD at h; simp only at h; applyDecl_tail
  | ind tys cts rcs => unfold applyDeclD at h; simp only at h; applyDecl_tail


/-! ## What any line keeps -/

/-- What every successful line keeps of the state: bound entries, pushed
records, the prelude, and non-empty taint skips.  (The last clause goes
with the parser's taint skip, task #292.) -/
structure Keeps (st st' : StateD) : Prop where
  names : ∀ i n, st.names.get? i = some n → st'.names.get? i = some n
  exprs : ∀ i e, st.exprs.get? i = some e → st'.exprs.get? i = some e
  decls : ∀ d ∈ st.decls, d ∈ st'.decls
  prelude : st'.prelude = st.prelude
  skips : st.taintSkipped ≠ #[] → st'.taintSkipped ≠ #[]

theorem Keeps.refl (st : StateD) : Keeps st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, rfl, id⟩

theorem Keeps.of_frame {st st' : StateD} (f : Frame st st') : Keeps st st' :=
  ⟨fun i n h => by rw [f.names]; exact h, fun i e h => by rw [f.exprs]; exact h, f.decls,
   f.prelude, fun h => by rw [f.taintSkipped]; exact h⟩

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
the taint table possibly a mark at that index, nothing else moves. -/
theorem parseExprEntryD_spec {st st' : StateD} {i : Nat} {r : ExprRec}
    (h : parseExprEntryD st i r = .ok st') :
    st.exprs.bound i = false ∧ ∃ e,
      (st' = { st with exprs := st.exprs.insert i e } ∨
       ∃ root, st' = { st with exprs := st.exprs.insert i e, tainted := st.tainted.insert i root }) := by
  unfold parseExprEntryD at h
  obtain ⟨_, hf, h⟩ := exceptBind_ok h
  simp only at h
  refine ⟨StateD.freshExpr_ok hf, ?_⟩
  -- every kind: its reads (a `const` reads the taint table between
  -- them), then the pair, then the taint mark
  cases r <;> (repeat' (first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | (try simp only at h
       split at h)))
  all_goals (injection h with h; subst h; first | exact ⟨_, .inl rfl⟩ | exact ⟨_, .inr ⟨_, rfl⟩⟩)

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
    exact ⟨fun j y hj => get?_insert_fresh hfresh hj, fun _ _ h => h, fun _ h => h, rfl, id⟩
  | level i r =>
    simp only [applyLine] at h
    obtain ⟨st₁, hl, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    obtain ⟨l, rfl⟩ := parseLevelEntryD_spec hl
    exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, rfl, id⟩
  | expr i r =>
    simp only [applyLine] at h
    obtain ⟨st₁, he, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    obtain ⟨hfresh, e, hst | ⟨root, hst⟩⟩ := parseExprEntryD_spec he <;> subst hst <;>
      exact ⟨fun _ _ h => h, fun j y hj => get?_insert_fresh hfresh hj, fun _ h => h, rfl, id⟩
  | decl d =>
    simp only [applyLine] at h
    rcases applyDeclD_cases h with f | ⟨hn, hl, he, ht, hp, hd, hs⟩ |
      ⟨name, hmem, hn, hl, he, ht, hp, hd, hs, htn⟩
    · exact Keeps.of_frame f
    · exact ⟨fun i n h => by rw [hn]; exact h, fun i e h => by rw [he]; exact h,
        fun d h => by rw [hd]; exact h, hp, fun _ => hs⟩
    · exact ⟨fun i n h => by rw [hn]; exact h, fun i e h => by rw [he]; exact h,
        fun d h => by rw [hd]; exact h, hp, fun h => by rw [hs]; exact h⟩

/-! ## The three lines of the template -/

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
    st'.exprs.get? j = some (ExprC.mkConst falseName []) := by
  simp only [applyLine] at h
  obtain ⟨st₁, he, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
  unfold parseExprEntryD at he
  obtain ⟨_, _, he⟩ := exceptBind_ok he
  simp only at he
  -- the entry is `mkConst False []`: the name, the (empty) levels, the taint, the pair
  obtain ⟨nm, hnm, he⟩ := exceptBind_ok he
  have hnm' : nm = falseName := by
    unfold StateD.name at hnm; rw [hi] at hnm
    simp only [pure, Except.pure, Except.ok.injEq] at hnm; exact hnm.symm
  subst hnm'
  obtain ⟨ls, hls, he⟩ := exceptBind_ok he
  have hls' : ls = [] := by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hls; exact hls.symm
  subst hls'
  -- the taint read, the pair, the mark: both branches of the read alike
  split at he <;> (
    obtain ⟨tc, _, he⟩ := exceptBind_ok he
    obtain ⟨p, hp, he⟩ := exceptBind_ok he
    simp only [pure, Except.pure, Except.ok.injEq] at hp; subst hp
    try simp only at he
    split at he <;> simp only [pure, Except.pure, Except.ok.injEq] at he <;> subst he <;>
      simp [IdTable.get?_insert])

end ConLeche.Frontend
