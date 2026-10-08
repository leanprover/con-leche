module

public import ConLeche.Frontend.Rounds
import ConLeche.Verify.ExceptBind

public section

/-!
# Dense streams (task #329)

The facts about the serial apply the rounds parse rests on.

* **A dense stream never rebinds** (`applyLine_name_dense` and its
  siblings): on a state whose tables are dense arrays, a line binding
  the next index of its table passes the rebinding test, and its entry
  is pushed.
* **The characterisation** (`applyList_of_allOK`, `allOK_of_applyList`):
  the serial fold over a dense list of lines succeeds with final
  tables `NA`/`LA`/`EA` exactly when every line's builder, reading the
  final tables cut at the counts before the line (`cutLk`), yields the
  line's own entry — a property of each line separately, which the
  rounds establish in any order.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Dense tables -/

theorem IdTable.ofDense_get? (a : Array α) (i : Nat) : (IdTable.ofDense a).get? i = a[i]? := by
  simp only [IdTable.ofDense, IdTable.get?]
  by_cases h : i < a.size
  · simp [h]
  · simp only [h, ↓reduceDIte]
    simp; omega

theorem IdTable.ofDense_bound_size (a : Array α) : (IdTable.ofDense a).bound a.size = false := by
  simp [IdTable.bound, IdTable.ofDense]

theorem IdTable.ofDense_insert_size (a : Array α) (x : α) :
    (IdTable.ofDense a).insert a.size x = IdTable.ofDense (a.push x) := by
  simp only [IdTable.insert, IdTable.ofDense, BEq.rfl, ↓reduceIte]

theorem extract_push_getElem (a : Array α) (k : Nat) (h : k < a.size) :
    (a.extract 0 k).push a[k] = a.extract 0 (k + 1) := by
  rw [Array.push_extract_getElem h, Nat.min_eq_left (Nat.zero_le _)]

/-! ## A dense stream never rebinds -/

section
variable (na : Array Name) (la : Array Level) (ea : Array Expr) (ds : Array Declaration)

theorem freshName_dense : (StateD.ofDense na la ea ds).freshName na.size = .ok () := by
  simp [StateD.freshName, StateD.ofDense, IdTable.ofDense_bound_size, pure, Except.pure]

theorem freshLevel_dense : (StateD.ofDense na la ea ds).freshLevel la.size = .ok () := by
  simp [StateD.freshLevel, StateD.ofDense, IdTable.ofDense_bound_size, pure, Except.pure]

theorem freshExpr_dense : (StateD.ofDense na la ea ds).freshExpr ea.size = .ok () := by
  simp [StateD.freshExpr, StateD.ofDense, IdTable.ofDense_bound_size, pure, Except.pure]

/-- A name line binding the next name: its builder's value, pushed. -/
theorem applyLine_name_dense (r : NameRec) :
    applyLine (StateD.ofDense na la ea ds) (.name na.size r) =
      match nameOf (StateD.ofDense na la ea ds).lk r with
      | .ok x => .ok (.inl (StateD.ofDense (na.push x) la ea ds))
      | .error m => .error m := by
  simp only [applyLine, parseNameEntryD]
  cases nameOf (StateD.ofDense na la ea ds).lk r with
  | error m => rfl
  | ok x =>
    simp only [bind, Except.bind, freshName_dense, pure, Except.pure]
    simp only [StateD.ofDense, IdTable.ofDense_insert_size]

theorem applyLine_level_dense (r : LevelRec) :
    applyLine (StateD.ofDense na la ea ds) (.level la.size r) =
      match levelOf (StateD.ofDense na la ea ds).lk r with
      | .ok x => .ok (.inl (StateD.ofDense na (la.push x) ea ds))
      | .error m => .error m := by
  simp only [applyLine, parseLevelEntryD, bind, Except.bind, freshLevel_dense]
  cases levelOf (StateD.ofDense na la ea ds).lk r with
  | error m => rfl
  | ok x =>
    simp only [pure, Except.pure]
    simp only [StateD.ofDense, IdTable.ofDense_insert_size]

theorem applyLine_expr_dense (r : ExprRec) :
    applyLine (StateD.ofDense na la ea ds) (.expr ea.size r) =
      match exprOf (StateD.ofDense na la ea ds).lk r with
      | .ok x => .ok (.inl (StateD.ofDense na la (ea.push x) ds))
      | .error m => .error m := by
  simp only [applyLine, parseExprEntryD, bind, Except.bind, freshExpr_dense]
  cases exprOf (StateD.ofDense na la ea ds).lk r with
  | error m => rfl
  | ok x =>
    simp only [pure, Except.pure]
    simp only [StateD.ofDense, IdTable.ofDense_insert_size]

theorem applyLine_decl_dense (d : DeclRec) :
    applyLine (StateD.ofDense na la ea ds) (.decl d) =
      match declOf (StateD.ofDense na la ea ds).lk d with
      | .ok (.inl x) => .ok (.inl (StateD.ofDense na la ea (ds.push x)))
      | .ok (.inr v) => .ok (.inr v)
      | .error m => .error m := by
  simp only [applyLine, applyDeclD, processLineCoreD, bind, Except.bind]
  cases declOf (StateD.ofDense na la ea ds).lk d with
  | error m => rfl
  | ok x => cases x <;> rfl

end

/-! ## The characterisation -/

/-- The lookups a line at counters `c` reads: the final tables, cut at
the counts before the line. -/
def cutLk (na : Array Name) (la : Array Level) (ea : Array Expr) (c : Ctr) : Lk String :=
  (StateD.ofDense (na.extract 0 c.n) (la.extract 0 c.l) (ea.extract 0 c.e) #[]).lk

/-- **One line is right**: a table line binds the next index of its
table, and its builder, at the final tables cut before it, yields the
final table's entry there; a declaration line's builder yields a
record. -/
def LineOK (na : Array Name) (la : Array Level) (ea : Array Expr) (c : Ctr) : LineRec → Prop
  | .name i r => i = c.n ∧ ∃ h : c.n < na.size, nameOf (cutLk na la ea c) r = .ok na[c.n]
  | .level i r => i = c.l ∧ ∃ h : c.l < la.size, levelOf (cutLk na la ea c) r = .ok la[c.l]
  | .expr i r => i = c.e ∧ ∃ h : c.e < ea.size, exprOf (cutLk na la ea c) r = .ok ea[c.e]
  | .decl d => ∃ x, declOf (cutLk na la ea c) d = .ok (.inl x)
  | .header => True
  | .blank => True

/-- Every line of a list is right, each at its own counters. -/
def AllOK (na : Array Name) (la : Array Level) (ea : Array Expr) : Ctr → List LineRec → Prop
  | _, [] => True
  | c, r :: rs => LineOK na la ea c r ∧ AllOK na la ea (c.step r) rs

/-- The record a declaration line yields at its counters. -/
def lineDecl (na : Array Name) (la : Array Level) (ea : Array Expr) (c : Ctr) :
    LineRec → Option Declaration
  | .decl d => match declOf (cutLk na la ea c) d with
    | .ok (.inl x) => some x
    | _ => none
  | _ => none

/-- The records of a list of lines, pushed in order. -/
def declsAlong (na : Array Name) (la : Array Level) (ea : Array Expr) :
    Ctr → List LineRec → Array Declaration → Array Declaration
  | _, [], acc => acc
  | c, r :: rs, acc => declsAlong na la ea (c.step r) rs
      (match lineDecl na la ea c r with
       | some x => acc.push x
       | none => acc)

theorem lk_ofDense (na : Array Name) (la : Array Level) (ea : Array Expr)
    (ds ds' : Array Declaration) :
    (StateD.ofDense na la ea ds).lk = (StateD.ofDense na la ea ds').lk := rfl

/-- The state at counters `c`, over final tables `na`/`la`/`ea`. -/
abbrev cutState (na : Array Name) (la : Array Level) (ea : Array Expr) (c : Ctr)
    (ds : Array Declaration) : StateD :=
  StateD.ofDense (na.extract 0 c.n) (la.extract 0 c.l) (ea.extract 0 c.e) ds

/-- **The characterisation, one way**: every line right at the final
tables makes the serial fold succeed, with the final tables cut at the
final counters and the lines' records pushed. -/
theorem applyList_of_allOK (na : Array Name) (la : Array Level) (ea : Array Expr) :
    ∀ (c : Ctr) (rs : List LineRec) (ds : Array Declaration) (k : Nat),
    AllOK na la ea c rs → c.n ≤ na.size → c.l ≤ la.size → c.e ≤ ea.size →
    applyList (cutState na la ea c ds) rs k =
      .ok (cutState na la ea (c.stepAll rs) (declsAlong na la ea c rs ds), k + rs.length) := by
  intro c rs
  induction rs generalizing c with
  | nil => intro ds k _ _ _ _; simp [applyList, Ctr.stepAll, declsAlong]
  | cons r rs ih =>
    intro ds k hok hn hl he
    obtain ⟨hr, hrs⟩ := hok
    cases r with
    | name i x =>
      obtain ⟨rfl, hlt, hx⟩ := hr
      have hsz : (na.extract 0 c.n).size = c.n := by simp; omega
      have := applyLine_name_dense (na.extract 0 c.n) (la.extract 0 c.l) (ea.extract 0 c.e) ds x
      rw [hsz, lk_ofDense _ _ _ ds #[]] at this
      simp only [applyList, cutState]
      rw [this]
      simp only [cutLk] at hx
      rw [hx]; simp only []
      rw [extract_push_getElem _ _ hlt]
      have := ih { c with n := c.n + 1 } ds (k + 1) hrs hlt hl he
      simp only [cutState] at this
      simp only [Ctr.stepAll, Ctr.step, declsAlong, lineDecl, this, List.length_cons]
      congr 2; omega
    | level i x =>
      obtain ⟨rfl, hlt, hx⟩ := hr
      have hsz : (la.extract 0 c.l).size = c.l := by simp; omega
      have := applyLine_level_dense (na.extract 0 c.n) (la.extract 0 c.l) (ea.extract 0 c.e) ds x
      rw [hsz, lk_ofDense _ _ _ ds #[]] at this
      simp only [applyList, cutState]
      rw [this]
      simp only [cutLk] at hx
      rw [hx]; simp only []
      rw [extract_push_getElem _ _ hlt]
      have := ih { c with l := c.l + 1 } ds (k + 1) hrs hn hlt he
      simp only [cutState] at this
      simp only [Ctr.stepAll, Ctr.step, declsAlong, lineDecl, this, List.length_cons]
      congr 2; omega
    | expr i x =>
      obtain ⟨rfl, hlt, hx⟩ := hr
      have hsz : (ea.extract 0 c.e).size = c.e := by simp; omega
      have := applyLine_expr_dense (na.extract 0 c.n) (la.extract 0 c.l) (ea.extract 0 c.e) ds x
      rw [hsz, lk_ofDense _ _ _ ds #[]] at this
      simp only [applyList, cutState]
      rw [this]
      simp only [cutLk] at hx
      rw [hx]; simp only []
      rw [extract_push_getElem _ _ hlt]
      have := ih { c with e := c.e + 1 } ds (k + 1) hrs hn hl hlt
      simp only [cutState] at this
      simp only [Ctr.stepAll, Ctr.step, declsAlong, lineDecl, this, List.length_cons]
      congr 2; omega
    | decl d =>
      obtain ⟨x, hx⟩ := hr
      have := applyLine_decl_dense (na.extract 0 c.n) (la.extract 0 c.l) (ea.extract 0 c.e) ds d
      rw [lk_ofDense _ _ _ ds #[]] at this
      simp only [applyList, cutState]
      rw [this]
      simp only [cutLk] at hx
      rw [hx]; simp only []
      have := ih c (ds.push x) (k + 1) hrs hn hl he
      simp only [cutState] at this
      simp only [Ctr.stepAll, Ctr.step, declsAlong, lineDecl, cutLk, hx, this, List.length_cons]
      congr 2; omega
    | header =>
      have := ih c ds (k + 1) hrs hn hl he
      simp only [applyList, applyLine, pure, Except.pure, cutState] at this ⊢
      simp only [Ctr.stepAll, Ctr.step, declsAlong, lineDecl, this, List.length_cons]
      congr 2; omega
    | blank =>
      have := ih c ds (k + 1) hrs hn hl he
      simp only [applyList, applyLine, pure, Except.pure, cutState] at this ⊢
      simp only [Ctr.stepAll, Ctr.step, declsAlong, lineDecl, this, List.length_cons]
      congr 2; omega

/-- Every line of a list binds the next index of its table. -/
def DenseAll : Ctr → List LineRec → Prop
  | _, [] => True
  | c, r :: rs => c.fits r = true ∧ DenseAll (c.step r) rs

theorem cutLk_eq {na : Array Name} {la : Array Level} {ea : Array Expr} {c : Ctr}
    {na0 la0 ea0} (hn : na.extract 0 c.n = na0) (hl : la.extract 0 c.l = la0)
    (he : ea.extract 0 c.e = ea0) (ds : Array Declaration) :
    cutLk na la ea c = (StateD.ofDense na0 la0 ea0 ds).lk := by
  rw [cutLk, hn, hl, he]; rfl

/-- The prefix of a pushed array, and its last entry. -/
theorem extract_of_push {a b : Array α} {x : α} {k : Nat} (h : a.extract 0 (k + 1) = b.push x)
    (hb : b.size = k) : a.extract 0 k = b ∧ ∃ hk : k < a.size, a[k] = x := by
  have hs : (a.extract 0 (k + 1)).size = k + 1 := by rw [h]; simp [hb]
  simp only [Array.size_extract] at hs
  have hk : k < a.size := by omega
  refine ⟨?_, hk, ?_⟩
  · have := congrArg (fun y => y.extract 0 k) h
    simp only [Array.extract_extract, Nat.zero_add] at this
    rw [show min k (k + 1) = k by omega] at this
    rw [this, ← hb, Array.extract_push_of_le (Nat.le_refl _), Array.extract_size]
  · have := congrArg (fun y => y[k]?) h
    simp only [Array.getElem?_extract, Array.getElem?_push] at this
    simp [hb, hk] at this
    exact this.2

/-- **The characterisation, the other way**: a serial fold over a
dense list that succeeds has every line right at its final tables. -/
theorem allOK_of_applyList :
    ∀ (c : Ctr) (rs : List LineRec) (na0 : Array Name) (la0 : Array Level) (ea0 : Array Expr)
      (ds : Array Declaration) (k : Nat) (st' : StateD) (k' : Nat),
    DenseAll c rs → na0.size = c.n → la0.size = c.l → ea0.size = c.e →
    applyList (StateD.ofDense na0 la0 ea0 ds) rs k = .ok (st', k') →
    ∃ na la ea, na.extract 0 c.n = na0 ∧ la.extract 0 c.l = la0 ∧ ea.extract 0 c.e = ea0 ∧
      na.size = (c.stepAll rs).n ∧ la.size = (c.stepAll rs).l ∧ ea.size = (c.stepAll rs).e ∧
      AllOK na la ea c rs ∧ st' = StateD.ofDense na la ea (declsAlong na la ea c rs ds) := by
  intro c rs
  induction rs generalizing c with
  | nil =>
    intro na0 la0 ea0 ds k st' k' _ hn hl he h
    simp only [applyList, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨na0, la0, ea0, ?_, ?_, ?_, ?_, ?_, ?_, trivial, rfl⟩ <;>
      simp [Ctr.stepAll, *]
  | cons r rs ih =>
    intro na0 la0 ea0 ds k st' k' hd hn hl he h
    obtain ⟨hfit, hrs⟩ := hd
    cases r with
    | name i x =>
      simp only [Ctr.fits, beq_iff_eq] at hfit; subst hfit
      simp only [applyList] at h
      rw [← hn, applyLine_name_dense] at h
      cases hx : nameOf (StateD.ofDense na0 la0 ea0 ds).lk x with
      | error m => rw [hx] at h; simp at h
      | ok y =>
        rw [hx] at h; simp only [] at h
        obtain ⟨na, la, ea, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
          ih { c with n := c.n + 1 } (na0.push y) la0 ea0 ds (k + 1) st' k' hrs
            (by simp [hn]) hl he h
        dsimp only at h1 h2 h3
        obtain ⟨hpre, hlt, hval⟩ := extract_of_push h1 hn
        refine ⟨na, la, ea, hpre, h2, h3, h4, h5, h6, ⟨⟨rfl, hlt, ?_⟩, h7⟩, ?_⟩
        · rw [cutLk_eq hpre h2 h3 ds, hx, hval]
        · rw [h8]; rfl
    | level i x =>
      simp only [Ctr.fits, beq_iff_eq] at hfit; subst hfit
      simp only [applyList] at h
      rw [← hl, applyLine_level_dense] at h
      cases hx : levelOf (StateD.ofDense na0 la0 ea0 ds).lk x with
      | error m => rw [hx] at h; simp at h
      | ok y =>
        rw [hx] at h; simp only [] at h
        obtain ⟨na, la, ea, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
          ih { c with l := c.l + 1 } na0 (la0.push y) ea0 ds (k + 1) st' k' hrs
            hn (by simp [hl]) he h
        dsimp only at h1 h2 h3
        obtain ⟨hpre, hlt, hval⟩ := extract_of_push h2 hl
        refine ⟨na, la, ea, h1, hpre, h3, h4, h5, h6, ⟨⟨rfl, hlt, ?_⟩, h7⟩, ?_⟩
        · rw [cutLk_eq h1 hpre h3 ds, hx, hval]
        · rw [h8]; rfl
    | expr i x =>
      simp only [Ctr.fits, beq_iff_eq] at hfit; subst hfit
      simp only [applyList] at h
      rw [← he, applyLine_expr_dense] at h
      cases hx : exprOf (StateD.ofDense na0 la0 ea0 ds).lk x with
      | error m => rw [hx] at h; simp at h
      | ok y =>
        rw [hx] at h; simp only [] at h
        obtain ⟨na, la, ea, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
          ih { c with e := c.e + 1 } na0 la0 (ea0.push y) ds (k + 1) st' k' hrs
            hn hl (by simp [he]) h
        dsimp only at h1 h2 h3
        obtain ⟨hpre, hlt, hval⟩ := extract_of_push h3 he
        refine ⟨na, la, ea, h1, h2, hpre, h4, h5, h6, ⟨⟨rfl, hlt, ?_⟩, h7⟩, ?_⟩
        · rw [cutLk_eq h1 h2 hpre ds, hx, hval]
        · rw [h8]; rfl
    | decl d =>
      simp only [applyList] at h
      rw [applyLine_decl_dense] at h
      cases hx : declOf (StateD.ofDense na0 la0 ea0 ds).lk d with
      | error m => rw [hx] at h; simp at h
      | ok y =>
        cases y with
        | inr v => rw [hx] at h; simp at h
        | inl x =>
          rw [hx] at h; simp only [] at h
          obtain ⟨na, la, ea, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
            ih c na0 la0 ea0 (ds.push x) (k + 1) st' k' hrs hn hl he h
          refine ⟨na, la, ea, h1, h2, h3, h4, h5, h6, ⟨⟨x, ?_⟩, h7⟩, ?_⟩
          · rw [cutLk_eq h1 h2 h3 ds, hx]
          · rw [h8]; simp only [declsAlong, lineDecl, Ctr.step, cutLk_eq h1 h2 h3 ds, hx]
    | header =>
      simp only [applyList, applyLine, pure, Except.pure] at h
      obtain ⟨na, la, ea, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        ih c na0 la0 ea0 ds (k + 1) st' k' hrs hn hl he h
      exact ⟨na, la, ea, h1, h2, h3, h4, h5, h6, ⟨trivial, h7⟩, h8⟩
    | blank =>
      simp only [applyList, applyLine, pure, Except.pure] at h
      obtain ⟨na, la, ea, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        ih c na0 la0 ea0 ds (k + 1) st' k' hrs hn hl he h
      exact ⟨na, la, ea, h1, h2, h3, h4, h5, h6, ⟨trivial, h7⟩, h8⟩

end ConLeche.Frontend
