module

public import ConLeche.Verify.Frontend.Dense

public section

/-!
# Good entries (task #329)

The rounds parse (`ConLeche/Frontend/RoundsWork.lean`) builds a window's
table entries in whatever order its rounds find them.  What makes the
result the serial parse's is one property of every entry it stores and
reads: the entry is GOOD for the index it is stored at (`Good`) —

* an entry of the finished tables below the window's start, or
* the value the builder of the window line binding that index yields
  over lookups that answer only good entries, and only at indices the
  serial parse may read at that line (below the window's start, or
  below the line's counters).

`Good` speaks of the lines of the window and nothing else: not of how
the rounds keep their tables, nor in what order they ran.

**Good as an invariant, not as a subtype.**  Every entry an owner
builds or publishes is good; the property is carried by invariants of
the round functions (`TBI`, `LateOK`, `WinInv`,
`ConLeche/Verify/Frontend/RoundsWork.lean` and `Rounds.lean`), proved
once, rather than as `{e // Good j e}` on each array element.  An
element's index is not stored with it — it is computed from its slot's
key — so a per-element subtype would have to carry the index at run
time, and moving an array of subtypes from one window's context to the
next would copy it.  The invariants cost nothing at run time, as a
subtype would not: they are proofs about the arrays as they are.

**The characterisation from good tables** (`allOK_of_good`).  If the
window binds each table's indices in increasing order (`IncAll`), and
tables `T` agree with the finished tables below the window's start,
hold only good entries above it, and hold an entry at every index a
window line binds, then every line is right at `T` (`AllOK`): the
serial fold over the window succeeds with exactly these tables
(`applyList_of_allOK`, `ConLeche/Verify/Frontend/Dense.lean`).  The
proof is an induction along the window: a good entry's lookups answer
good entries of earlier lines, which by induction are `T`'s, so the
builder over the serial parse's own lookups (`cutLk T`) yields the same
value (`nameOfF_mono` and its siblings: a builder that succeeds over
some lookups succeeds alike over lookups that answer at least as much);
and an index has one good entry, the one its line's builder yields.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Builders over more answers -/

theorem mapM_mono {ε ε' : Type} {f : β → Except ε α} {g : β → Except ε' α}
    (h : ∀ x w, f x = .ok w → g x = .ok w) :
    ∀ {l : List β} {v : List α}, l.mapM f = .ok v → l.mapM g = .ok v := by
  intro l
  induction l with
  | nil => intro v hv; simpa [List.mapM_nil, pure, Except.pure] using hv
  | cons x xs ih =>
    intro v hv
    simp only [List.mapM_cons, bind, Except.bind] at hv ⊢
    cases hx : f x with
    | error e => rw [hx] at hv; cases hv
    | ok w =>
      rw [hx] at hv
      rw [h x w hx]
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at hv; cases hv
      | ok ws =>
        rw [hxs] at hv
        rw [ih hxs]
        simpa [pure, Except.pure] using hv

/-- Lookups `ℓ'` answer at least what `ℓ` answers. -/
def Ext {ε ε' : Type} (ℓ : Nat → Except ε α) (ℓ' : Nat → Except ε' α) : Prop :=
  ∀ j w, ℓ j = .ok w → ℓ' j = .ok w

/-- A lookup, then the rest, carried over. -/
theorem bind_mono {ε ε' : Type} {a : Except ε α} {a' : Except ε' α} {f : α → Except ε β}
    {f' : α → Except ε' β} (ha : ∀ w, a = .ok w → a' = .ok w)
    (hf : ∀ x v, f x = .ok v → f' x = .ok v) {v : β} (h : (a >>= f) = .ok v) :
    (a' >>= f') = .ok v := by
  simp only [bind, Except.bind] at h ⊢
  cases a with
  | error e => cases h
  | ok w => rw [ha w rfl]; exact hf w v h

theorem pure_mono {ε ε' : Type} {x v : α} (h : (pure x : Except ε α) = .ok v) :
    (pure x : Except ε' α) = .ok v := by
  simpa [pure, Except.pure] using h

theorem pwOfF_mono {ε ε' : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {nm' : Nat → Except ε' Name} {lv' : Nat → Except ε' Level}
    {ex' : Nat → Except ε' Expr} (hn : Ext nm nm') {r : PwRec} {v : PropWhen}
    (h : pwOfF nm lv ex r = .ok v) : pwOfF nm' lv' ex' r = .ok v := by
  cases r with
  | never => exact pure_mono h
  | ifAllZero ns =>
    simp only [pwOfF] at h ⊢
    exact bind_mono (fun w hw => mapM_mono hn hw) (fun _ _ hx => pure_mono hx) h

theorem nameOfF_mono {ε ε' : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {nm' : Nat → Except ε' Name} {lv' : Nat → Except ε' Level}
    {ex' : Nat → Except ε' Expr} (hn : Ext nm nm') {r : NameRec} {v : Name}
    (h : nameOfF nm lv ex r = .ok v) : nameOfF nm' lv' ex' r = .ok v := by
  cases r <;> simp only [nameOfF] at h ⊢ <;>
    exact bind_mono (fun w hw => hn _ _ hw) (fun _ _ hx => pure_mono hx) h

theorem levelOfF_mono {ε ε' : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {nm' : Nat → Except ε' Name} {lv' : Nat → Except ε' Level}
    {ex' : Nat → Except ε' Expr} (hn : Ext nm nm') (hl : Ext lv lv') {r : LevelRec} {v : Level}
    (h : levelOfF nm lv ex r = .ok v) : levelOfF nm' lv' ex' r = .ok v := by
  cases r <;> simp only [levelOfF] at h ⊢
  · exact bind_mono (fun w hw => hl _ _ hw) (fun _ _ hx => pure_mono hx) h
  · exact bind_mono (fun w hw => hl _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => hl _ _ hw) (fun _ _ hy => pure_mono hy) hx) h
  · exact bind_mono (fun w hw => hl _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => hl _ _ hw) (fun _ _ hy => pure_mono hy) hx) h
  · exact bind_mono (fun w hw => hn _ _ hw) (fun _ _ hx => pure_mono hx) h

theorem exprOfF_mono {ε ε' : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {nm' : Nat → Except ε' Name} {lv' : Nat → Except ε' Level}
    {ex' : Nat → Except ε' Expr} (hn : Ext nm nm') (hl : Ext lv lv') (he : Ext ex ex')
    {r : ExprRec} {v : Expr} (h : exprOfF nm lv ex r = .ok v) : exprOfF nm' lv' ex' r = .ok v := by
  cases r with
  | bvar k => exact pure_mono h
  | natVal n => exact pure_mono h
  | strVal s => exact pure_mono h
  | sort u =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => hl _ _ hw) (fun _ _ hx => pure_mono hx) h
  | const n us =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => hn _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => mapM_mono hl hw) (fun _ _ hy => pure_mono hy) hx) h
  | app f a =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => he _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => he _ _ hw) (fun _ _ hy => pure_mono hy) hx) h
  | lam ty bd pw =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => he _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => he _ _ hw)
        (fun _ _ hy => bind_mono (fun w hw => pwOfF_mono hn hw) (fun _ _ hz => pure_mono hz) hy)
        hx) h
  | forallE ty bd pw =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => he _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => he _ _ hw)
        (fun _ _ hy => bind_mono (fun w hw => pwOfF_mono hn hw) (fun _ _ hz => pure_mono hz) hy)
        hx) h
  | letE ty vl bd =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => he _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => he _ _ hw)
        (fun _ _ hy => bind_mono (fun w hw => he _ _ hw) (fun _ _ hz => pure_mono hz) hy) hx) h
  | proj tn ix s =>
    simp only [exprOfF] at h ⊢
    exact bind_mono (fun w hw => hn _ _ hw)
      (fun _ _ hx => bind_mono (fun w hw => he _ _ hw) (fun _ _ hy => pure_mono hy) hx) h

/-! ## Tables, generically -/

/-- The three tables. -/
inductive Tb where
  | n
  | l
  | e
  deriving DecidableEq

/-- A table's counter. -/
@[expose] def Ctr.at (c : Ctr) : Tb → Nat
  | .n => c.n
  | .l => c.l
  | .e => c.e

/-- The index a line binds in a table. -/
@[expose] def LineRec.idAt : LineRec → Tb → Option Nat
  | .name i _, .n => some i
  | .level i _, .l => some i
  | .expr i _, .e => some i
  | _, _ => none

theorem Ctr.step_at (c : Ctr) (r : LineRec) (t : Tb) :
    (c.step r).at t = match r.idAt t with
      | some i => i + 1
      | none => c.at t := by
  cases r <;> cases t <;> rfl

theorem Ctr.fits_iff {c : Ctr} {r : LineRec} :
    c.fits r = true ↔ ∀ t i, r.idAt t = some i → c.at t ≤ i := by
  constructor
  · intro h t i hi
    cases r <;> cases t <;> simp_all [Ctr.fits, LineRec.idAt, Ctr.at]
  · intro h
    cases r with
    | name i _ => simpa [Ctr.fits, Ctr.at] using h .n i rfl
    | level i _ => simpa [Ctr.fits, Ctr.at] using h .l i rfl
    | expr i _ => simpa [Ctr.fits, Ctr.at] using h .e i rfl
    | _ => rfl

theorem LineRec.idAt_unique {r : LineRec} {t t' : Tb} {i i' : Nat} (h : r.idAt t = some i)
    (h' : r.idAt t' = some i') : t = t' ∧ i = i' := by
  cases r <;> cases t <;> cases t' <;> simp_all [LineRec.idAt]

/-! ## Increasing streams: where an index is bound -/

/-- The counters before line `p` of a list. -/
@[expose] def ctrAt (c : Ctr) (rs : List LineRec) (p : Nat) : Ctr := c.stepAll (rs.take p)

theorem ctrAt_succ (c : Ctr) (rs : List LineRec) (p : Nat) (h : p < rs.length) :
    ctrAt c rs (p + 1) = (ctrAt c rs p).step rs[p] := by
  simp only [ctrAt]
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, Ctr.stepAll_append]
  rfl

theorem ctrAt_le_succ {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) :
    ∀ p t, (ctrAt c rs p).at t ≤ (ctrAt c rs (p + 1)).at t := by
  induction rs generalizing c with
  | nil => intro p t; simp [ctrAt, Ctr.stepAll]
  | cons r rs ih =>
    intro p t
    obtain ⟨hf, hrs⟩ := hi
    cases p with
    | zero =>
      simp only [ctrAt, List.take_zero, List.take_succ_cons, Ctr.stepAll]
      rw [Ctr.step_at]
      cases h : r.idAt t with
      | none => exact Nat.le_refl _
      | some i => have := Ctr.fits_iff.mp hf t i h; simp only []; omega
    | succ p =>
      have := ih hrs p t
      simpa [ctrAt, List.take_succ_cons, Ctr.stepAll] using this

theorem ctrAt_mono {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) {p q : Nat} (h : p ≤ q)
    (t : Tb) : (ctrAt c rs p).at t ≤ (ctrAt c rs q).at t := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (ctrAt_le_succ hi _ t)

theorem ctrAt_zero (c : Ctr) (rs : List LineRec) : ctrAt c rs 0 = c := by
  simp [ctrAt, Ctr.stepAll]

theorem IncAll.get {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) :
    ∀ p (h : p < rs.length), (ctrAt c rs p).fits rs[p] = true := by
  induction rs generalizing c with
  | nil => intro p h; simp at h
  | cons r rs ih =>
    intro p h
    obtain ⟨hf, hrs⟩ := hi
    cases p with
    | zero => simpa [ctrAt, Ctr.stepAll] using hf
    | succ p =>
      have := ih hrs p (by simpa using h)
      simpa [ctrAt, List.take_succ_cons, Ctr.stepAll] using this

/-- A line binds at or above its counter, and one below the next. -/
theorem IncAll.bind {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) {p : Nat}
    (h : p < rs.length) {t : Tb} {i : Nat} (hb : rs[p].idAt t = some i) :
    (ctrAt c rs p).at t ≤ i ∧ (ctrAt c rs (p + 1)).at t = i + 1 := by
  refine ⟨Ctr.fits_iff.mp (hi.get p h) t i hb, ?_⟩
  rw [ctrAt_succ c rs p h, Ctr.step_at, hb]

/-- An index below line `p`'s counter is bound, if at all, before `p`. -/
theorem IncAll.before {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) {p q : Nat}
    (hq : q < rs.length) {t : Tb} {j : Nat} (hb : rs[q].idAt t = some j)
    (hj : j < (ctrAt c rs p).at t) : q < p := by
  rcases Nat.lt_or_ge q p with h | h
  · exact h
  · have h1 := ctrAt_mono hi h t
    have h2 := (hi.bind hq hb).1
    omega

/-- An index is bound by at most one line. -/
theorem IncAll.unique {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) {p q : Nat}
    (hp : p < rs.length) (hq : q < rs.length) {t : Tb} {j : Nat}
    (hbp : rs[p].idAt t = some j) (hbq : rs[q].idAt t = some j) : p = q := by
  rcases Nat.lt_trichotomy p q with h | h | h
  · have h1 := (hi.bind hp hbp).2
    have h2 := ctrAt_mono hi (show p + 1 ≤ q by omega) t
    have h3 := (hi.bind hq hbq).1
    omega
  · exact h
  · have h1 := (hi.bind hq hbq).2
    have h2 := ctrAt_mono hi (show q + 1 ≤ p by omega) t
    have h3 := (hi.bind hp hbp).1
    omega

/-- No line binds an index in the gap a line skips. -/
theorem IncAll.gap {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) {p q : Nat}
    (hp : p < rs.length) (hq : q < rs.length) {t : Tb} {i j : Nat}
    (hbp : rs[p].idAt t = some i) (hbq : rs[q].idAt t = some j)
    (h1 : (ctrAt c rs p).at t ≤ j) (h2 : j < i) : False := by
  rcases Nat.lt_trichotomy q p with h | h | h
  · have a := (hi.bind hq hbq).2
    have b := ctrAt_mono hi (show q + 1 ≤ p by omega) t
    omega
  · subst h; rw [hbp] at hbq; cases hbq; omega
  · have a := (hi.bind hp hbp).2
    have b := ctrAt_mono hi (show p + 1 ≤ q by omega) t
    have d := (hi.bind hq hbq).1
    omega

/-- The window's counters never fall below its start. -/
theorem IncAll.ge_start {c : Ctr} {rs : List LineRec} (hi : IncAll c rs) (p : Nat) (t : Tb) :
    c.at t ≤ (ctrAt c rs p).at t := by
  have := ctrAt_mono hi (Nat.zero_le p) t
  rwa [ctrAt_zero] at this

/-- `AllOK` line by line. -/
theorem allOK_of_forall {T : Tabs} :
    ∀ {c : Ctr} {rs : List LineRec},
    (∀ p (h : p < rs.length), LineOK T (ctrAt c rs p) rs[p]) → AllOK T c rs := by
  intro c rs
  induction rs generalizing c with
  | nil => intro _; trivial
  | cons r rs ih =>
    intro h
    have h0 := h 0 (by simp)
    rw [List.getElem_cons_zero, ctrAt_zero] at h0
    refine ⟨h0, ih fun p hp => ?_⟩
    have := h (p + 1) (by simpa using hp)
    simpa [ctrAt, List.take_succ_cons, Ctr.stepAll] using this

/-! ## Good entries -/

/-- A window, as the proofs see it: the finished tables before it, the
counters at its start, its lines. -/
structure WCtx where
  P : Prior
  c0 : Ctr
  rs : List LineRec

/-- The counters before line `p` of the window. -/
@[expose] def WCtx.ctr (Γ : WCtx) (p : Nat) : Ctr := ctrAt Γ.c0 Γ.rs p

/-- A table entry, tagged with its table. -/
inductive TV where
  | n (x : Name)
  | l (x : Level)
  | e (x : Expr)

/-- The table an entry belongs to. -/
@[expose] def TV.tb : TV → Tb
  | .n _ => .n
  | .l _ => .l
  | .e _ => .e

/-- Tables `T` hold something at index `j` of table `t`. -/
@[expose] def Tabs.at (T : Tabs) : Tb → Nat → Option TV
  | .n, j => (T.n j).map .n
  | .l, j => (T.l j).map .l
  | .e, j => (T.e j).map .e

theorem Tabs.at_tb {T : Tabs} {t : Tb} {j : Nat} {v : TV} (h : T.at t j = some v) : v.tb = t := by
  cases t <;> simp only [Tabs.at, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl

/-! ### One table, named

The proofs about the three tables are written once, over a table `S`
(`Sel`): its tag, how its entries are tagged, and where a table record
keeps it. -/

/-- One of the three tables, with its entry type. -/
inductive Sel : Type → Type where
  | n : Sel Name
  | l : Sel Level
  | e : Sel Expr

/-- The table's tag. -/
@[expose] def Sel.tb : Sel α → Tb
  | .n => .n
  | .l => .l
  | .e => .e

/-- An entry of the table, tagged. -/
@[expose] def Sel.inj : Sel α → α → TV
  | .n => .n
  | .l => .l
  | .e => .e

/-- The table, in three tables as partial maps. -/
@[expose] def Sel.tab : Sel α → Tabs → Nat → Option α
  | .n => Tabs.n
  | .l => Tabs.l
  | .e => Tabs.e

/-- The table, in the finished tables. -/
@[expose] def Sel.pages : Sel α → Prior → Pages α
  | .n => Prior.n
  | .l => Prior.l
  | .e => Prior.e

/-- The table's entries have a filler. -/
@[expose, reducible] def Sel.inh : Sel α → Inhabited α
  | .n => inferInstance
  | .l => inferInstance
  | .e => inferInstance

/-- Every table has its `Sel`. -/
theorem Tb.exSel (t : Tb) : ∃ (α : Type) (S : Sel α), S.tb = t := by
  cases t
  · exact ⟨_, .n, rfl⟩
  · exact ⟨_, .l, rfl⟩
  · exact ⟨_, .e, rfl⟩

theorem Sel.inj_tb (S : Sel α) (x : α) : (S.inj x).tb = S.tb := by cases S <;> rfl

theorem Sel.inj_inj (S : Sel α) {x y : α} (h : S.inj x = S.inj y) : x = y := by
  cases S <;> cases h <;> rfl

theorem Sel.at (S : Sel α) (T : Tabs) (j : Nat) : T.at S.tb j = (S.tab T j).map S.inj := by
  cases S <;> rfl

theorem Sel.at_some {S : Sel α} {T : Tabs} {j : Nat} {x : α} :
    T.at S.tb j = some (S.inj x) ↔ S.tab T j = some x := by
  rw [S.at]
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.mp h
    rw [S.inj_inj he] at hy; exact hy
  · intro h; rw [h]; rfl

/-- Two tables agree at a slot of the table if they do tagged. -/
theorem Sel.inj_inj_opt (S : Sel α) {T T' : Tabs} {j : Nat} (h : T.at S.tb j = T'.at S.tb j) :
    S.tab T j = S.tab T' j := by
  rw [S.at, S.at] at h
  exact Option.map_injective (fun _ _ e => S.inj_inj e) h

theorem Sel.prior_tab (S : Sel α) (P : Prior) : S.tab P.tabs = (S.pages P).get := by
  cases S <;> rfl

/-- An entry of table `t` is some table's entry. -/
theorem TV.sel {t : Tb} {v : TV} (h : v.tb = t) :
    (t = .n ∧ ∃ x, v = Sel.n.inj x) ∨ (t = .l ∧ ∃ x, v = Sel.l.inj x) ∨
      (t = .e ∧ ∃ x, v = Sel.e.inj x) := by
  cases v <;> subst h <;> simp [Sel.inj, TV.tb]

/-- The table, in a parse state. -/
@[expose] def Sel.st : Sel α → StateD → Nat → Option α
  | .n => fun st => st.names.get?
  | .l => fun st => st.levels.get?
  | .e => fun st => st.exprs.get?

theorem Holds.sel {st : StateD} {T : Tabs} {c : Ctr} (h : Holds st T c) (S : Sel α) (j : Nat) :
    S.st st j = if j < c.at S.tb then S.tab T j else none := by
  cases S
  · exact h.n j
  · exact h.l j
  · exact h.e j

theorem Holds.ofSel {st : StateD} {T : Tabs} {c : Ctr}
    (h : ∀ {α : Type} (S : Sel α) j, S.st st j = if j < c.at S.tb then S.tab T j else none) :
    Holds st T c :=
  ⟨h .n, h .l, h .e⟩

/-! ### A line's lookups and its value -/

/-- A line's three lookups, as one over the tables, tagged. -/
@[expose] def lkAt {ε : Type} (nm : Nat → Except ε Name) (lv : Nat → Except ε Level)
    (ex : Nat → Except ε Expr) : Tb → Nat → Option TV
  | .n, i => match nm i with | .ok w => some (.n w) | .error _ => none
  | .l, i => match lv i with | .ok w => some (.l w) | .error _ => none
  | .e, i => match ex i with | .ok w => some (.e w) | .error _ => none

/-- A property of everything the three lookups answer, from one per
table. -/
theorem lkAt_forall {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {Q : Tb → Nat → TV → Prop}
    (hn : ∀ i w, nm i = .ok w → Q .n i (.n w)) (hl : ∀ i w, lv i = .ok w → Q .l i (.l w))
    (he : ∀ i w, ex i = .ok w → Q .e i (.e w)) :
    ∀ t i v, lkAt nm lv ex t i = some v → Q t i v := by
  intro t i v h
  cases t <;> simp only [lkAt] at h <;> split at h <;> cases h
  · exact hn _ _ ‹_›
  · exact hl _ _ ‹_›
  · exact he _ _ ‹_›

theorem lkAt_n {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {i : Nat} {w : Name} (h : nm i = .ok w) :
    lkAt nm lv ex .n i = some (.n w) := by simp [lkAt, h]
theorem lkAt_l {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {i : Nat} {w : Level} (h : lv i = .ok w) :
    lkAt nm lv ex .l i = some (.l w) := by simp [lkAt, h]
theorem lkAt_e {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {i : Nat} {w : Expr} (h : ex i = .ok w) :
    lkAt nm lv ex .e i = some (.e w) := by simp [lkAt, h]

/-- Lookups `ℓ'` answer at least what `ℓ` answers, in every table. -/
@[expose] def ExtAt {ε ε' : Type} (nm : Nat → Except ε Name) (lv : Nat → Except ε Level)
    (ex : Nat → Except ε Expr) (nm' : Nat → Except ε' Name) (lv' : Nat → Except ε' Level)
    (ex' : Nat → Except ε' Expr) : Prop :=
  ∀ t i v, lkAt nm lv ex t i = some v → lkAt nm' lv' ex' t i = some v

theorem ExtAt.split {ε ε' : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {nm' : Nat → Except ε' Name} {lv' : Nat → Except ε' Level}
    {ex' : Nat → Except ε' Expr} (h : ExtAt nm lv ex nm' lv' ex') :
    Ext nm nm' ∧ Ext lv lv' ∧ Ext ex ex' := by
  refine ⟨fun i w hw => ?_, fun i w hw => ?_, fun i w hw => ?_⟩
  · have := h .n i _ (lkAt_n hw); simp only [lkAt] at this; split at this <;> cases this; assumption
  · have := h .l i _ (lkAt_l hw); simp only [lkAt] at this; split at this <;> cases this; assumption
  · have := h .e i _ (lkAt_e hw); simp only [lkAt] at this; split at this <;> cases this; assumption

/-- The value a table line's builder yields, tagged with its table. -/
@[expose] def lineVal {ε : Type} (nm : Nat → Except ε Name) (lv : Nat → Except ε Level)
    (ex : Nat → Except ε Expr) : LineRec → Option (Except ε TV)
  | .name _ x => some (TV.n <$> nameOfF nm lv ex x)
  | .level _ x => some (TV.l <$> levelOfF nm lv ex x)
  | .expr _ x => some (TV.e <$> exprOfF nm lv ex x)
  | _ => none

theorem map_ok {ε : Type} {f : α → TV} {e : Except ε α} {v : TV}
    (h : (f <$> e) = .ok v) : ∃ a, e = .ok a ∧ v = f a := by
  cases e with
  | error => cases h
  | ok a => exact ⟨a, rfl, by cases h; rfl⟩

theorem lineVal_mono {ε ε' : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {nm' : Nat → Except ε' Name} {lv' : Nat → Except ε' Level}
    {ex' : Nat → Except ε' Expr} (h : ExtAt nm lv ex nm' lv' ex') {r : LineRec} {v : TV}
    (hv : lineVal nm lv ex r = some (.ok v)) : lineVal nm' lv' ex' r = some (.ok v) := by
  obtain ⟨h1, h2, h3⟩ := h.split
  cases r <;> simp only [lineVal, Option.some.injEq, reduceCtorEq] at hv ⊢
  · obtain ⟨a, ha, rfl⟩ := map_ok hv
    rw [nameOfF_mono h1 ha]; rfl
  · obtain ⟨a, ha, rfl⟩ := map_ok hv
    rw [levelOfF_mono h1 h2 ha]; rfl
  · obtain ⟨a, ha, rfl⟩ := map_ok hv
    rw [exprOfF_mono h1 h2 h3 ha]; rfl

theorem lineVal_tb {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {r : LineRec} {t : Tb} {j : Nat} (hr : r.idAt t = some j) {v : TV}
    (hv : lineVal nm lv ex r = some (.ok v)) : v.tb = t := by
  cases r <;> cases t <;> simp only [LineRec.idAt, reduceCtorEq] at hr <;>
    simp only [lineVal, Option.some.injEq] at hv <;>
    obtain ⟨a, _, rfl⟩ := map_ok hv <;> rfl

/-! ### Good entries -/

/-- **A good entry for index `j`**: an entry of the finished tables
below the window's start, or the value the builder of the window line
binding `j` yields over lookups that answer only good entries at
indices the serial parse may read there (below the window's start, or
below the line's counters). -/
inductive Good (Γ : WCtx) : Nat → TV → Prop where
  | prior {t : Tb} {j : Nat} {v : TV} : j < Γ.c0.at t → Γ.P.tabs.at t j = some v → Good Γ j v
  | line {ε : Type} {p j : Nat} {r : LineRec} {t : Tb} {v : TV} (nm : Nat → Except ε Name)
      (lv : Nat → Except ε Level) (ex : Nat → Except ε Expr) :
      Γ.rs[p]? = some r → r.idAt t = some j →
      (∀ t' i w, lkAt nm lv ex t' i = some w → Good Γ i w) →
      (∀ t' i w, lkAt nm lv ex t' i = some w → i < Γ.c0.at t' ∨ i < (Γ.ctr p).at t') →
      lineVal nm lv ex r = some (.ok v) → Good Γ j v

/-- An entry of the finished tables below the window's start is good. -/
theorem Good.ofPrior {Γ : WCtx} (S : Sel α) {j : Nat} {x : α} (h1 : j < Γ.c0.at S.tb)
    (h2 : (S.pages Γ.P).get j = some x) : Good Γ j (S.inj x) :=
  .prior h1 (Sel.at_some.mpr (by rw [Sel.prior_tab]; exact h2))

/-- Tables `T` hold entry `v` at `j`. -/
@[expose] def Tabs.has (T : Tabs) (j : Nat) (v : TV) : Prop := T.at v.tb j = some v

/-- **What the window's final tables must be** for the window to be
the serial parse: increasing; the finished tables below the window's
start; good entries above it; an entry wherever a window line binds. -/
structure GoodTabs (Γ : WCtx) (T : Tabs) : Prop where
  inc : IncAll Γ.c0 Γ.rs
  keep : ∀ t j, j < Γ.c0.at t → T.at t j = Γ.P.tabs.at t j
  good : ∀ t j v, Γ.c0.at t ≤ j → T.at t j = some v → Good Γ j v
  full : ∀ t p (h : p < Γ.rs.length) i, Γ.rs[p].idAt t = some i → (T.at t i).isSome

theorem getElem?_eq_some_iff' {l : List α} {p : Nat} {x : α} :
    l[p]? = some x ↔ ∃ h : p < l.length, l[p] = x := by
  rw [List.getElem?_eq_some_iff]

/-- The lookups of the serial parse at counters `c`, as one. -/
theorem lkAt_cut (T : Tabs) (c : Ctr) (t : Tb) (i : Nat) :
    lkAt (cutLk T c).name (cutLk T c).level (cutLk T c).expr t i =
      if i < c.at t then T.at t i else none := by
  cases t
  · by_cases hi : i < c.n <;> cases hT : T.n i <;>
      simp [lkAt, cutLk, Tabs.at, Ctr.at, hi, hT] <;> rfl
  · by_cases hi : i < c.l <;> cases hT : T.l i <;>
      simp [lkAt, cutLk, Tabs.at, Ctr.at, hi, hT] <;> rfl
  · by_cases hi : i < c.e <;> cases hT : T.e i <;>
      simp [lkAt, cutLk, Tabs.at, Ctr.at, hi, hT] <;> rfl

section
variable {Γ : WCtx} {T : Tabs} (hT : GoodTabs Γ T)
include hT

/-- A line's lookups that answer only good entries of earlier lines,
answered alike by the serial parse's lookups at the line, given that
the good entries of those lines are `T`'s. -/
theorem ext_cut {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {p : Nat}
    (hb : ∀ t i w, lkAt nm lv ex t i = some w → i < Γ.c0.at t ∨ i < (Γ.ctr p).at t)
    (hq : ∀ t i w, lkAt nm lv ex t i = some w → T.at t i = some w) :
    ExtAt nm lv ex (cutLk T (Γ.ctr p)).name (cutLk T (Γ.ctr p)).level
      (cutLk T (Γ.ctr p)).expr := by
  intro t i w h
  have hlt : i < (Γ.ctr p).at t := by
    rcases hb t i w h with h1 | h1
    · have := hT.inc.ge_start p t; simp only [WCtx.ctr] at this ⊢; omega
    · exact h1
  rw [lkAt_cut, ite_eq_left hlt]; exact hq t i w h

/-- An index a good entry's lookups read is bound, if in the window,
before the line the entry is the builder's of. -/
theorem good_ref_before {p : Nat} {t : Tb} {i : Nat}
    (hb : i < Γ.c0.at t ∨ i < (Γ.ctr p).at t) :
    ∀ q (hq : q < Γ.rs.length), Γ.rs[q].idAt t = some i → q < p := by
  intro q hq hbq
  rcases hb with h | h
  · have h1 := (hT.inc.bind hq hbq).1
    have h2 := hT.inc.ge_start q t
    omega
  · exact hT.inc.before hq hbq h

/-- Every line binding `j` in table `t` lies before `n`. -/
def BoundBefore (Γ : WCtx) (t : Tb) (j n : Nat) : Prop :=
  ∀ q (hq : q < Γ.rs.length), Γ.rs[q].idAt t = some j → q < n

/-- The lookups of a good entry's line at `p ≤ n`, carried over to the
serial parse's lookups at the line, when every good entry bound before
`n` is `T`'s. -/
theorem refs_ext {n : Nat}
    (ih : ∀ j v, Good Γ j v → BoundBefore Γ v.tb j n → T.has j v)
    {ε : Type} {p : Nat} (hpn : p ≤ n) {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr}
    (hg : ∀ t i w, lkAt nm lv ex t i = some w → Good Γ i w)
    (hb : ∀ t i w, lkAt nm lv ex t i = some w → i < Γ.c0.at t ∨ i < (Γ.ctr p).at t) :
    ExtAt nm lv ex (cutLk T (Γ.ctr p)).name (cutLk T (Γ.ctr p)).level
      (cutLk T (Γ.ctr p)).expr := by
  refine ext_cut hT hb fun t i w h => ?_
  have htb : w.tb = t := by
    cases t <;> simp only [lkAt] at h <;> split at h <;> cases h <;> rfl
  have := ih i w (hg t i w h) fun q hq hbq =>
    Nat.lt_of_lt_of_le (good_ref_before hT (hb t i w h) q hq (htb ▸ hbq)) hpn
  simpa [Tabs.has, htb] using this

/-- A good entry for an index line `p` binds in table `t`, held by `T`
at that index: the line's value over the serial parse's lookups. -/
theorem good_line {n : Nat}
    (ih : ∀ j v, Good Γ j v → BoundBefore Γ v.tb j n → T.has j v)
    {p : Nat} (hpl : p < Γ.rs.length) (hpn : p ≤ n) {t : Tb} {j : Nat}
    (hid : Γ.rs[p].idAt t = some j) {v : TV} (hg : Good Γ j v) (hvt : v.tb = t) :
    lineVal (cutLk T (Γ.ctr p)).name (cutLk T (Γ.ctr p)).level (cutLk T (Γ.ctr p)).expr Γ.rs[p] =
      some (.ok v) := by
  cases hg with
  | prior h1 h2 =>
    have := Tabs.at_tb h2; subst hvt; subst this
    have h3 := (hT.inc.bind hpl hid).1; have h4 := hT.inc.ge_start p v.tb
    omega
  | @line ε p' _ r' t' _ nm lv ex hp' hr' hg' hb' hx =>
    obtain ⟨hpl', hrr⟩ := getElem?_eq_some_iff'.mp hp'
    have ht : t' = t := (lineVal_tb hr' hx).symm.trans hvt
    subst ht
    have hpp : p' = p := hT.inc.unique hpl' hpl (by rw [hrr]; exact hr') hid
    subst hpp
    rw [hrr]
    exact lineVal_mono (refs_ext hT ih hpn hg' hb') hx

/-- **A good entry is the tables' entry**, by induction along the
window: for every `n`, a good entry whose index no line at or after `n`
binds. -/
theorem good_has : ∀ n j v, Good Γ j v → BoundBefore Γ v.tb j n → T.has j v := by
  intro n
  induction n with
  | zero =>
    intro j v hg hbb
    cases hg with
    | prior h1 h2 =>
      show T.at v.tb j = some v; rw [Tabs.at_tb h2, hT.keep _ j h1, h2]
    | line _ _ _ hp hr =>
      obtain ⟨hp, hr'⟩ := getElem?_eq_some_iff'.mp hp
      exact absurd (hbb _ hp (by rw [hr', lineVal_tb hr ‹_›]; exact hr)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro j v hg hbb
    cases hg with
    | prior h1 h2 =>
      show T.at v.tb j = some v; rw [Tabs.at_tb h2, hT.keep _ j h1, h2]
    | @line ε p j r t v nm lv ex hp hr hgr hbr hx =>
      obtain ⟨hpl, hrr⟩ := getElem?_eq_some_iff'.mp hp
      have hvt := lineVal_tb hr hx
      have hid : Γ.rs[p].idAt t = some j := by rw [hrr]; exact hr
      have hpn : p ≤ n := Nat.le_of_lt_succ (hbb p hpl (by rw [hvt]; exact hid))
      have hb := lineVal_mono (refs_ext hT ih hpn hgr hbr) hx
      have hge0 : Γ.c0.at t ≤ j := by
        have h1 := (hT.inc.bind hpl hid).1; have h2 := hT.inc.ge_start p t
        omega
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp (hT.full t p hpl j hid)
      have hb' := good_line hT ih hpl hpn hid (hT.good t j v' hge0 hv') (Tabs.at_tb hv')
      rw [hrr, hb] at hb'; cases hb'
      show T.at v.tb j = some v; rw [hvt]; exact hv'

/-- No good entry in the gap a line skips. -/
theorem gap_none {p : Nat} (hp : p < Γ.rs.length) {t : Tb} {i : Nat}
    (hb : Γ.rs[p].idAt t = some i) {j : Nat} (h1 : (Γ.ctr p).at t ≤ j) (h2 : j < i) {v : TV}
    (hv : v.tb = t) (hg : Good Γ j v) : False := by
  have hc := hT.inc.ge_start p t
  simp only [WCtx.ctr] at h1
  cases hg with
  | prior h h' => rw [Tabs.at_tb h'] at hv; subst hv; omega
  | line _ _ _ hq hr _ _ hx =>
    obtain ⟨hql, hr'⟩ := getElem?_eq_some_iff'.mp hq
    rw [lineVal_tb hr hx] at hv; subst hv
    exact hT.inc.gap hp hql hb (by rw [hr']; exact hr) h1 h2

/-- Every line binding `j` lies before `p + 1`, if line `p` binds it. -/
theorem boundBefore_self {p : Nat} (hp : p < Γ.rs.length) {t : Tb} {j : Nat}
    (hb : Γ.rs[p].idAt t = some j) : BoundBefore Γ t j (p + 1) := by
  intro q hq hbq
  have := hT.inc.unique hq hp hbq hb
  omega

end

/-- A table line is right when it binds at or above its counter, its
table holds nothing in the gap and its value is the table's entry. -/
theorem lineOK_of_at {T : Tabs} {c : Ctr} {r : LineRec} {t : Tb} {i : Nat}
    (hid : r.idAt t = some i) (h1 : c.at t ≤ i)
    (h2 : ∀ j, c.at t ≤ j → j < i → T.at t j = none) {v : TV} (hv : T.at t i = some v)
    (hx : lineVal (cutLk T c).name (cutLk T c).level (cutLk T c).expr r = some (.ok v)) :
    LineOK T c r := by
  cases r <;> cases t <;> simp only [LineRec.idAt, reduceCtorEq, Option.some.injEq] at hid <;>
    subst hid <;> simp only [lineVal, Option.some.injEq] at hx <;>
    obtain ⟨a, ha, rfl⟩ := map_ok hx <;>
    simp only [Tabs.at, Option.map_eq_some_iff, Option.map_eq_none_iff] at hv h2 <;>
    obtain ⟨b, hb, hab⟩ := hv <;> cases hab <;> exact ⟨h1, h2, _, hb, ha⟩

/-- **The characterisation from good tables**: increasing lines, the
finished tables below the window's start, good entries above it, an
entry wherever a line binds, and a record from every declaration line's
builder: every line is right at `T`. -/
theorem allOK_of_good {Γ : WCtx} {T : Tabs} (hT : GoodTabs Γ T)
    (hD : ∀ p (h : p < Γ.rs.length) d, Γ.rs[p] = .decl d →
      ∃ x, declOf (cutLk T (Γ.ctr p)) d = .ok (.inl x)) :
    AllOK T Γ.c0 Γ.rs := by
  apply allOK_of_forall
  intro p hp
  have hfit := hT.inc.get p hp
  have htab : ∀ t i, Γ.rs[p].idAt t = some i → LineOK T (ctrAt Γ.c0 Γ.rs p) Γ.rs[p] := by
    intro t i hid
    have hfi := Ctr.fits_iff.mp hfit t i hid
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hT.full t p hp i hid)
    have hge0 : Γ.c0.at t ≤ i := by have := hT.inc.ge_start p t; omega
    have hg := hT.good t i v hge0 hv
    refine lineOK_of_at hid hfi (fun j h1 h2 => ?_) hv
      (good_line hT (good_has hT p) hp (Nat.le_refl _) hid hg (Tabs.at_tb hv))
    cases hj : T.at t j with
    | none => rfl
    | some x =>
      exact (gap_none hT hp hid h1 h2 (Tabs.at_tb hj)
        (hT.good t j x (by have := hT.inc.ge_start p t; (try simp only [WCtx.ctr] at *); omega)
          hj)).elim
  cases hr : Γ.rs[p] with
  | name i r => exact hr ▸ htab .n i (by rw [hr]; rfl)
  | level i r => exact hr ▸ htab .l i (by rw [hr]; rfl)
  | expr i r => exact hr ▸ htab .e i (by rw [hr]; rfl)
  | decl d => exact hD p hp d hr
  | header => trivial
  | blank => trivial

end ConLeche.Frontend
