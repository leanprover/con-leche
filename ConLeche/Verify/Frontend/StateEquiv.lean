module

public import ConLeche.Frontend.Pipeline

public section

/-!
# The parse sees its tables as partial maps (task #329)

Two parse states whose tables answer every lookup alike and whose
records agree (`StateD.Equiv`) give the same parse of whatever follows:
the same error, or states that agree again, and in the end the same
records (`parseChunks.go_equiv`).  The serial parse keeps its tables
as a dense array with an overflow map; the rounds parse builds the same
partial maps another way, and `Reached.equiv` carries the streaming
invariant across.
-/

namespace ConLeche.Frontend

open ConLeche

/-- Two states with the same tables, as partial maps, and the same
records. -/
structure StateD.Equiv (a b : StateD) : Prop where
  names : ∀ j, a.names.get? j = b.names.get? j
  levels : ∀ j, a.levels.get? j = b.levels.get? j
  exprs : ∀ j, a.exprs.get? j = b.exprs.get? j
  decls : a.decls = b.decls

theorem StateD.Equiv.refl (a : StateD) : a.Equiv a := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem StateD.Equiv.symm {a b : StateD} (h : a.Equiv b) : b.Equiv a :=
  ⟨fun j => (h.names j).symm, fun j => (h.levels j).symm, fun j => (h.exprs j).symm, h.decls.symm⟩

theorem StateD.Equiv.trans {a b c : StateD} (h : a.Equiv b) (h' : b.Equiv c) : a.Equiv c :=
  ⟨fun j => (h.names j).trans (h'.names j), fun j => (h.levels j).trans (h'.levels j),
   fun j => (h.exprs j).trans (h'.exprs j), h.decls.trans h'.decls⟩

theorem StateD.Equiv.lk {a b : StateD} (h : a.Equiv b) : a.lk = b.lk := by
  have hn : a.name = b.name := funext fun j => by simp only [StateD.name, h.names j]
  have hl : a.level = b.level := funext fun j => by simp only [StateD.level, h.levels j]
  have he : a.expr = b.expr := funext fun j => by simp only [StateD.expr, h.exprs j]
  simp only [StateD.lk, hn, hl, he]

theorem IdTable.get?_insert_congr {t u : IdTable α} (h : ∀ j, t.get? j = u.get? j) (i : Nat)
    (x : α) (j : Nat) : (t.insert i x).get? j = (u.insert i x).get? j := by
  rw [IdTable.get?_insert, IdTable.get?_insert, h j]

theorem IdTable.bound_congr {t u : IdTable α} (h : ∀ j, t.get? j = u.get? j) (i : Nat) :
    t.bound i = u.bound i := by
  rw [IdTable.bound_eq, IdTable.bound_eq, h i]

/-- Results of a line, related. -/
def ResRel : Except String (StateD ⊕ RecordVerdict) → Except String (StateD ⊕ RecordVerdict) → Prop
  | .error e, .error e' => e = e'
  | .ok (.inl s), .ok (.inl s') => s.Equiv s'
  | .ok (.inr v), .ok (.inr v') => v = v'
  | _, _ => False

theorem applyLine_equiv {a b : StateD} (h : a.Equiv b) (r : LineRec) :
    ResRel (applyLine a r) (applyLine b r) := by
  cases r with
  | name i x =>
    simp only [applyLine, parseNameEntryD, h.lk, StateD.freshName]
    rw [IdTable.bound_congr h.names i]
    cases nameOf b.lk x with
    | error e => simp [bind, Except.bind, ResRel]
    | ok n =>
      cases b.names.bound i
      · simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
        exact ⟨IdTable.get?_insert_congr h.names i n, h.levels, h.exprs, h.decls⟩
      · simp [bind, Except.bind, ResRel, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  | level i x =>
    simp only [applyLine, parseLevelEntryD, h.lk, StateD.freshLevel]
    rw [IdTable.bound_congr h.levels i]
    cases b.levels.bound i
    · cases levelOf b.lk x with
      | error e => simp [bind, Except.bind, ResRel, pure, Except.pure]
      | ok l =>
        simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
        exact ⟨h.names, IdTable.get?_insert_congr h.levels i l, h.exprs, h.decls⟩
    · simp [bind, Except.bind, ResRel, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  | expr i x =>
    simp only [applyLine, parseExprEntryD, h.lk, StateD.freshExpr]
    rw [IdTable.bound_congr h.exprs i]
    cases b.exprs.bound i
    · cases exprOf b.lk x with
      | error e => simp [bind, Except.bind, ResRel, pure, Except.pure]
      | ok e =>
        simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
        exact ⟨h.names, h.levels, IdTable.get?_insert_congr h.exprs i e, h.decls⟩
    · simp [bind, Except.bind, ResRel, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  | decl d =>
    simp only [applyLine, applyDeclD, processLineCoreD, h.lk]
    cases declOf b.lk d with
    | error e => simp [bind, Except.bind, ResRel]
    | ok y =>
      cases y with
      | inl x =>
        simp only [bind, Except.bind, pure, Except.pure]
        exact ⟨h.names, h.levels, h.exprs, by simp [pushDecl, h.decls]⟩
      | inr v => simp [bind, Except.bind, pure, Except.pure, ResRel]
  | header => exact h
  | blank => exact h

/-- Results of a chunk feed, related. -/
def FeedRel : Except (CheckError × Nat) (StateD × Nat × USize) →
    Except (CheckError × Nat) (StateD × Nat × USize) → Prop
  | .error e, .error e' => e = e'
  | .ok (s, n, i), .ok (s', n', i') => s.Equiv s' ∧ n = n' ∧ i = i'
  | _, _ => False

theorem feedChunk_equiv (buf : ByteArray) (i : USize) (n : Nat) :
    ∀ (a b : StateD), a.Equiv b → FeedRel (feedChunk a buf i n) (feedChunk b buf i n) := by
  intro a
  induction a, i, n using feedChunk.induct buf with
  | case1 st i n h e he hnl =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hnl]; exact rfl
  | case2 st i n h e he hnl =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hnl]
    exact ⟨hb, rfl, rfl⟩
  | case3 st i n h r j he hj =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hj, ↓reduceIte]
    exact ⟨hb, rfl, rfl⟩
  | case4 st i n h r j he hj msg happ =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hj]
    have := applyLine_equiv hb r; rw [happ] at this
    revert this; cases applyLine b r with
    | error e => intro h'; simp only [ResRel] at h'; subst h'; simp [happ, FeedRel]
    | ok y => cases y <;> intro h' <;> simp [ResRel] at h'
  | case5 st i n h r j he hj v happ =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hj]
    have := applyLine_equiv hb r; rw [happ] at this
    revert this; cases applyLine b r with
    | error e => intro h'; simp [ResRel] at h'
    | ok y => cases y with
      | inl s => intro h'; simp [ResRel] at h'
      | inr v' => intro h'; simp only [ResRel] at h'; subst h'; simp [happ, FeedRel]
  | case6 st i n h r j he hj st' happ hij ih =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hj]
    have := applyLine_equiv hb r; rw [happ] at this
    revert this; cases applyLine b r with
    | error e => intro h'; simp [ResRel] at h'
    | ok y => cases y with
      | inl s => intro h'; simp only [ResRel] at h'; simp only [happ, hij, ↓reduceDIte]; exact ih s h'
      | inr v' => intro h'; simp [ResRel] at h'
  | case7 st i n h r j he hj st' happ hij =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte, he, hj]
    have := applyLine_equiv hb r; rw [happ] at this
    revert this; cases applyLine b r with
    | error e => intro h'; simp [ResRel] at h'
    | ok y => cases y with
      | inl s => intro h'; simp [happ, hij, FeedRel]
      | inr v' => intro h'; simp [ResRel] at h'
  | case8 st i n h =>
    intro b hb; rw [feedChunk, feedChunk]; simp only [h, ↓reduceDIte]; exact ⟨hb, rfl, rfl⟩

theorem applyFinalLine_equiv {a b : StateD} (h : a.Equiv b) (buf : ByteArray) (i : USize)
    (n : Nat) :
    match applyFinalLine a buf i n, applyFinalLine b buf i n with
    | .error e, .error e' => e = e'
    | .ok s, .ok s' => s.Equiv s'
    | _, _ => False := by
  simp only [applyFinalLine]
  cases scanLineSpec buf i with
  | err e => rfl
  | ok r j =>
    have := applyLine_equiv h r
    simp only []
    revert this
    cases applyLine a r with
    | error e => cases applyLine b r with
      | error e' => intro h'; simp only [ResRel] at h'; subst h'; rfl
      | ok y => cases y <;> simp [ResRel]
    | ok x => cases x with
      | inl s => cases applyLine b r with
        | error e' => simp [ResRel]
        | ok y => cases y with
          | inl s' => intro h'; exact h'
          | inr v => simp [ResRel]
      | inr v => cases applyLine b r with
        | error e' => simp [ResRel]
        | ok y => cases y with
          | inl s' => simp [ResRel]
          | inr v' => intro h'; simp only [ResRel] at h'; subst h'; rfl

theorem chunkFinish_equiv {a b : StateD} (h : a.Equiv b) (carry : ByteArray) (n : Nat) :
    chunkFinish a carry n = chunkFinish b carry n := by
  simp only [chunkFinish]
  split
  · simp [ParseResultD.ofState, h.decls]
  · have := applyFinalLine_equiv h carry 0 (n + 1)
    revert this
    cases applyFinalLine a carry 0 (n + 1) <;> cases applyFinalLine b carry 0 (n + 1) <;>
      simp only [] <;> intro h'
    · subst h'; rfl
    · exact h'.elim
    · exact h'.elim
    · simp [ParseResultD.ofState, h'.decls]

theorem parseChunks.go_equiv : ∀ (cs : List ByteArray) (a b : StateD) (carry : ByteArray)
    (n t : Nat), a.Equiv b → parseChunks.go a carry n t cs = parseChunks.go b carry n t cs := by
  intro cs
  induction cs with
  | nil => intro a b carry n t h; exact chunkFinish_equiv h carry n
  | cons c cs ih =>
    intro a b carry n t h
    simp only [parseChunks.go, chunkStep]
    by_cases hsz : t + c.size ≥ USize.size
    · simp only [hsz, ↓reduceIte]
    · simp only [hsz, ↓reduceIte]
      have := feedChunk_equiv (if carry.isEmpty then c else carry ++ c) 0 n a b h
      revert this
      generalize feedChunk a (if carry.isEmpty then c else carry ++ c) 0 n = fa
      generalize feedChunk b (if carry.isEmpty then c else carry ++ c) 0 n = fb
      cases fa with
      | error e => cases fb with
        | error e' => intro h'; simp only [FeedRel] at h'; subst h'; rfl
        | ok y => simp [FeedRel]
      | ok x => cases fb with
        | error e' => simp [FeedRel]
        | ok y =>
          obtain ⟨s, n', i'⟩ := x; obtain ⟨s', n'', i''⟩ := y
          intro h'; obtain ⟨hs, hn, hi⟩ := h'
          subst hn; subst hi
          exact ih s s' _ _ _ hs

/-- The streaming invariant does not see how the tables are kept. -/
theorem Reached.equiv {a b : StateD} {carry : ByteArray} {n t : Nat}
    (h : Reached a carry n t) (he : a.Equiv b) : Reached b carry n t := by
  obtain ⟨done, hd⟩ := h
  exact ⟨done, fun rest => (hd rest).trans (parseChunks.go_equiv rest a b carry n t he)⟩

end ConLeche.Frontend
