module

public import ConLeche.Verify.Frontend.LazyMono
public import ConLeche.Verify.Frontend.Rounds
import ConLeche.Verify.ExceptBind

public section

/-!
# The lazy parse is the serial parse (task #329)

The lazy check (`checkLineL`, `ConLeche/Frontend/Lazy.lean`) reads the
finished tables `P`, where a lazy entry stands for a line not built.
The serial parse's state at the same counters is related to `P` by
`LHolds`: the same names and levels, the same expressions bound, and
every built entry the serial one.  A line passing the check is one
step of the serial parse that keeps this relation
(`checkLineL_sim`); the run-time record it yields is the serial one
up to a theorem's value (`DRel`: the placeholder `ph vid` stands for
the serial table's entry at `vid`); a lazy line it keeps is one whose
serial entry its builder yields from the entries below it
(`LazyFact`).  `LGOK` carries this from chunk to chunk, and
`buildVal_sound` says a value built from the kept lines is the serial
table's entry.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The relation between the serial state and the finished tables -/

/-- **The serial state `st` and the finished tables `P` at counters
`c`**: the same names and levels below the counters, the same
expression indices bound, and every built entry the serial state's. -/
structure LHolds (st : StateD) (P : Prior) (c : Ctr) : Prop where
  n : ∀ j, st.names.get? j = if j < c.n then P.n.get j else none
  l : ∀ j, st.levels.get? j = if j < c.l then P.l.get j else none
  e : ∀ j, (st.exprs.get? j).isSome = (decide (j < c.e) && (P.e.get j).isSome)
  eb : ∀ j v, j < c.e → P.e.get j = some v → isLazyE v = false → st.exprs.get? j = some v

theorem LHolds.name {st : StateD} {P : Prior} {c : Ctr} (h : LHolds st P c) :
    st.name = lkN P c.n := funext fun j => by
  simp only [StateD.name, lkN, h.n j]; rfl

theorem LHolds.level {st : StateD} {P : Prior} {c : Ctr} (h : LHolds st P c) :
    st.level = lkL P c.l := funext fun j => by
  simp only [StateD.level, lkL, h.l j]; rfl

theorem LHolds.above {st : StateD} {P : Prior} {c : Ctr} (h : LHolds st P c) {j : Nat}
    (hj : c.e ≤ j) : st.exprs.get? j = none := by
  have := h.e j
  simp only [show ¬ j < c.e by omega, decide_false, Bool.false_and] at this
  exact Option.not_isSome_iff_eq_none.mp (by simp [this])

/-- A built entry is the serial state's. -/
theorem LHolds.monoE {st : StateD} {P : Prior} {c : Ctr} (h : LHolds st P c) :
    Mono (lkEB P c.e) st.expr := by
  intro k a hk
  simp only [lkEB] at hk
  split at hk
  · rename_i e he
    split at hk
    · simp [throw, throwThe, MonadExceptOf.throw] at hk
    · rename_i hl
      simp only [pure, Except.pure, Except.ok.injEq] at hk
      subst hk
      split at he
      · rename_i hkc
        simp only [StateD.expr, h.eb k e hkc he (by simpa using hl)]; rfl
      · simp at he
  · simp [throw, throwThe, MonadExceptOf.throw] at hk

/-- A bound index is bound in the serial state. -/
theorem LHolds.bound {st : StateD} {P : Prior} {c : Ctr} (h : LHolds st P c) {j : Nat}
    (hb : boundE P c.e j = true) : ∃ w, st.exprs.get? j = some w := by
  simp only [boundE, Bool.and_eq_true, decide_eq_true_eq] at hb
  have := h.e j
  simp only [hb.1, decide_true, hb.2, Bool.and_self] at this
  exact Option.isSome_iff_exists.mp this

theorem LHolds.boundN' {st : StateD} {P : Prior} {c : Ctr} (h : LHolds st P c) {nd : ByteArray}
    {j : Nat} (hb : boundN P nd c.e j = true) : ∃ w, st.exprs.get? j = some w := by
  unfold boundN at hb
  rw [Bool.and_eq_true] at hb
  exact h.bound hb.1

theorem StateD.expr_of_get {st : StateD} {j : Nat} {w : Expr}
    (h : st.exprs.get? j = some w) : st.expr j = .ok w := by
  simp [StateD.expr, h]; rfl

theorem StateD.get_of_expr {st : StateD} {j : Nat} {w : Expr}
    (h : st.expr j = .ok w) : st.exprs.get? j = some w := by
  simp only [StateD.expr] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; assumption
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Growing states -/

/-- `b` keeps every entry of `a`. -/
structure Ext (a b : StateD) : Prop where
  n : ∀ j v, a.names.get? j = some v → b.names.get? j = some v
  l : ∀ j v, a.levels.get? j = some v → b.levels.get? j = some v
  e : ∀ j v, a.exprs.get? j = some v → b.exprs.get? j = some v

theorem Ext.refl (a : StateD) : Ext a a := ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem Ext.trans {a b c : StateD} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c :=
  ⟨fun j v h => h₂.n j v (h₁.n j v h), fun j v h => h₂.l j v (h₁.l j v h),
   fun j v h => h₂.e j v (h₁.e j v h)⟩

theorem Ext.monoN {a b : StateD} (h : Ext a b) : Mono a.name b.name := by
  intro k v hk
  simp only [StateD.name] at hk ⊢
  split at hk
  · rename_i w hw
    simp only [pure, Except.pure, Except.ok.injEq] at hk; subst hk
    simp [h.n k w hw]; rfl
  · simp [throw, throwThe, MonadExceptOf.throw] at hk

theorem Ext.monoL {a b : StateD} (h : Ext a b) : Mono a.level b.level := by
  intro k v hk
  simp only [StateD.level] at hk ⊢
  split at hk
  · rename_i w hw
    simp only [pure, Except.pure, Except.ok.injEq] at hk; subst hk
    simp [h.l k w hw]; rfl
  · simp [throw, throwThe, MonadExceptOf.throw] at hk

theorem Ext.monoE {a b : StateD} (h : Ext a b) : Mono a.expr b.expr := fun k v hk =>
  StateD.expr_of_get (h.e k v (StateD.get_of_expr hk))

/-- Binding an unbound index keeps everything. -/
theorem ext_insert {t : IdTable α} {i : Nat} {x : α} (hi : t.get? i = none) :
    ∀ j v, t.get? j = some v → (t.insert i x).get? j = some v := by
  intro j v hj
  rw [IdTable.get?_insert]
  split
  · rename_i h; subst h; rw [hi] at hj; exact absurd hj (by simp)
  · exact hj

/-! ## What the store and the records promise -/

/-- An expression lookup below index `j` (what a lazy line's build
reads). -/
@[expose] def exprBelow (G : StateD) (j k : Nat) : Except String Expr :=
  if k < j then G.expr k else throw s!"forward expr index {k}"

/-- **A lazy line `(j, x)` of the store**: the serial state binds `j`
to what the line's builder yields from the entries below `j`. -/
@[expose] def LazyFact (G : StateD) (j : Nat) (x : ExprRec) : Prop :=
  ∃ v, G.exprs.get? j = some v ∧ exprOfF G.name G.level (exprBelow G j) x = .ok v

theorem LazyFact.ext {a b : StateD} (h : Ext a b) {j : Nat} {x : ExprRec}
    (hf : LazyFact a j x) : LazyFact b j x := by
  obtain ⟨v, hv, hx⟩ := hf
  refine ⟨v, h.e j v hv, exprOfF_mono h.monoN h.monoL ?_ hx⟩
  intro k w hk
  simp only [exprBelow] at hk ⊢
  split at hk
  · rw [ite_eq_left (by assumption)]; exact h.monoE k w hk
  · simp [throw, throwThe, MonadExceptOf.throw] at hk

/-- **A run-time record and its serial record**: equal, except that a
theorem's value is the placeholder `ph vid`, `vid` bound to the serial
value. -/
@[expose] def DRel (G : StateD) (d' d : Declaration) : Prop :=
  match d with
  | .thmDecl cv w => ∃ vid hint, d' = .thmDecl cv (ph vid hint) ∧ G.exprs.get? vid = some w
  | _ => d' = d

theorem DRel.ext {a b : StateD} (h : Ext a b) {d' d : Declaration} (hd : DRel a d' d) :
    DRel b d' d := by
  cases d with
  | thmDecl cv w =>
    obtain ⟨vid, hint, h1, h2⟩ := hd
    exact ⟨vid, hint, h1, h.e vid w h2⟩
  | _ => exact hd

/-- Two lists related member by member. -/
@[expose] def Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Pw R as bs
  | _, _ => False

theorem Pw.append {α β : Type} {R : α → β → Prop} :
    ∀ {a₁ : List α} {b₁ : List β} {a₂ : List α} {b₂ : List β},
    Pw R a₁ b₁ → Pw R a₂ b₂ → Pw R (a₁ ++ a₂) (b₁ ++ b₂)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h₁, h₂ => ⟨h₁.1, Pw.append h₁.2 h₂⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem Pw.imp {α β : Type} {R S : α → β → Prop} (hrs : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, Pw R as bs → Pw S as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨hrs _ _ h.1, Pw.imp hrs h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Pw.length {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Pw R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Pw.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Pw.getElem {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Pw R as bs → ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
    R as[i] bs[i]
  | [], [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, h, 0, _, _ => h.1
  | _ :: _, _ :: _, h, i + 1, h₁, h₂ =>
    Pw.getElem h.2 i (by simpa using h₁) (by simpa using h₂)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-- The kept lines' bytes. -/
@[expose] def encLz (L : List (Nat × ExprRec)) : List UInt8 :=
  Flat.encElems Flat.encLine (L.map fun p => LineRec.expr p.1 p.2)

theorem encElems_append {α : Type} (e : α → List UInt8) :
    ∀ (l₁ l₂ : List α), Flat.encElems e (l₁ ++ l₂) = Flat.encElems e l₁ ++ Flat.encElems e l₂
  | [], _ => rfl
  | x :: xs, l₂ => by simp [Flat.encElems, encElems_append e xs l₂]

theorem encLz_append (L : List (Nat × ExprRec)) (i : Nat) (x : ExprRec) :
    encLz (L ++ [(i, x)]) = encLz L ++ Flat.encLine (.expr i x) := by
  simp [encLz, encElems_append, Flat.encElems]

/-- The sparse offsets are line boundaries. -/
@[expose] def SpOK (spOff : Array Nat) (L : List (Nat × ExprRec)) : Prop :=
  ∀ s (h : s < spOff.size), ∃ m, m ≤ L.length ∧ spOff[s] = (encLz (L.take m)).length

/-- A chunk of the store holds the lines `L`. -/
@[expose] def CValid (C : LChunk) (L : List (Nat × ExprRec)) : Prop :=
  C.cd.data.toList = encLz L ∧ SpOK C.spOff L

/-- **The check's accumulator**, against the serial state `G`: the
records related to the serial ones `gds`, the kept lines `L`, each a
`LazyFact`. -/
structure AccOK (G : StateD) (a : LAcc) (gds : List Declaration)
    (L : List (Nat × ExprRec)) : Prop where
  ds : Pw (DRel G) a.ds.toList gds
  cd : a.cd.data.toList = encLz L
  sp : SpOK a.spOff L
  lz : ∀ p ∈ L, LazyFact G p.1 p.2

theorem AccOK.init (G : StateD) : AccOK G LAcc.init [] [] :=
  ⟨trivial, rfl, fun s h => absurd h (by simp [LAcc.init]), fun _ h => absurd h (by simp)⟩

theorem AccOK.ext {a b : StateD} (h : Ext a b) {acc : LAcc} {gds : List Declaration}
    {L : List (Nat × ExprRec)} (ha : AccOK a acc gds L) : AccOK b acc gds L :=
  ⟨Pw.imp (fun _ _ => DRel.ext h) ha.ds, ha.cd, ha.sp, fun p hp => (ha.lz p hp).ext h⟩

theorem AccOK.push {G : StateD} {acc : LAcc} {gds : List Declaration}
    {L : List (Nat × ExprRec)} (ha : AccOK G acc gds L) {d' d : Declaration}
    (hd : DRel G d' d) : AccOK G (acc.push d') (gds ++ [d]) L := by
  obtain ⟨ds, cd, si, so, nl, fr, rg⟩ := acc
  exact ⟨by simpa [LAcc.push] using Pw.append ha.ds (show Pw (DRel G) [d'] [d] from ⟨hd, trivial⟩),
    ha.cd, ha.sp, ha.lz⟩

theorem AccOK.lazy {G : StateD} {acc : LAcc} {gds : List Declaration}
    {L : List (Nat × ExprRec)} (ha : AccOK G acc gds L) {i : Nat} {x : ExprRec}
    (hf : LazyFact G i x) : AccOK G (acc.lazy i x) gds (L ++ [(i, x)]) := by
  obtain ⟨ds, cd, si, so, nl, fr, rg⟩ := acc
  have hcd : (Flat.wLine cd (.expr i x)).data.toList = encLz (L ++ [(i, x)]) := by
    rw [Flat.wLine_spec, encLz_append, ← ha.cd]
  have hsp : ∀ (so' : Array Nat), SpOK so' L → SpOK so' (L ++ [(i, x)]) := by
    intro so' h s hs
    obtain ⟨m, hm, e⟩ := h s hs
    exact ⟨m, by simp; omega, by rw [e, List.take_append_of_le_length hm]⟩
  have hlz : ∀ p ∈ L ++ [(i, x)], LazyFact G p.1 p.2 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ha.lz p hp
    · simp at hp; subst hp; exact hf
  simp only [LAcc.lazy]
  split
  · refine ⟨ha.ds, hcd, ?_, hlz⟩
    intro s hs
    simp only [Array.size_push] at hs
    by_cases hlt : s < so.size
    · obtain ⟨m, hm, e⟩ := hsp so ha.sp s hlt
      exact ⟨m, hm, by simp [Array.getElem_push, hlt, e]⟩
    · have : s = so.size := by omega
      subst this
      refine ⟨L.length, by simp, ?_⟩
      simp only [Array.getElem_push_eq, List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
      have := congrArg List.length ha.cd
      simpa using this
  · exact ⟨ha.ds, hcd, hsp so ha.sp, hlz⟩

/-! ## One line -/

theorem isOk_iff {ε α : Type} {e : Except ε α} : isOk e = true ↔ ∃ a, e = .ok a := by
  cases e <;> simp [isOk]

theorem mapM_ok_of_all {ε α : Type} {f : Nat → Except ε α} :
    ∀ {l : List Nat}, (l.all fun u => isOk (f u)) = true → ∃ r, l.mapM f = .ok r
  | [], _ => ⟨[], rfl⟩
  | k :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨a, ha⟩ := isOk_iff.mp h.1
    obtain ⟨r, hr⟩ := mapM_ok_of_all h.2
    exact ⟨a :: r, by simp [List.mapM_cons, ha, hr, bind, Except.bind, pure, Except.pure]⟩

/-- **A lazy line's references bound make its serial build succeed.** -/
theorem refsOK_ok {st : StateD} {P : Prior} {nd : ByteArray} {c : Ctr} (hst : LHolds st P c)
    {x : ExprRec} (h : refsOK P nd c x = true) :
    ∃ v, exprOfF st.name st.level st.expr x = .ok v := by
  have hb : ∀ j, boundN P nd c.e j = true → ∃ w, st.expr j = .ok w := fun j hj => by
    obtain ⟨w, hw⟩ := hst.boundN' hj; exact ⟨w, StateD.expr_of_get hw⟩
  have hn : ∀ j, isOk (lkN P c.n j) = true → ∃ a, st.name j = .ok a := fun j hj => by
    rw [hst.name]; exact isOk_iff.mp hj
  have hl : ∀ j, isOk (lkL P c.l j) = true → ∃ a, st.level j = .ok a := fun j hj => by
    rw [hst.level]; exact isOk_iff.mp hj
  have hpw : ∀ pw, isOk (pwOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) pw) = true →
      ∃ a, pwOfF st.name st.level st.expr pw = .ok a := fun pw hp => by
    obtain ⟨a, ha⟩ := isOk_iff.mp hp
    rw [hst.name] at ⊢
    exact ⟨a, pwOfF_mono (Mono.refl _) ha⟩
  cases x with
  | bvar k => exact ⟨_, rfl⟩
  | sort u =>
    obtain ⟨a, ha⟩ := hl u h
    exact ⟨_, by simp [exprOfF, ha, bind, Except.bind, pure, Except.pure]; rfl⟩
  | const n us =>
    simp only [refsOK, Bool.and_eq_true] at h
    obtain ⟨a, ha⟩ := hn n h.1
    obtain ⟨r, hr⟩ := mapM_ok_of_all (f := st.level) (by
      rw [hst.level]; exact h.2)
    exact ⟨_, by simp [exprOfF, ha, hr, bind, Except.bind, pure, Except.pure]; rfl⟩
  | app f a =>
    simp only [refsOK, Bool.and_eq_true] at h
    obtain ⟨w1, h1⟩ := hb f h.1
    obtain ⟨w2, h2⟩ := hb a h.2
    exact ⟨_, by simp [exprOfF, h1, h2, bind, Except.bind, pure, Except.pure]; rfl⟩
  | lam ty bd pw =>
    simp only [refsOK, Bool.and_eq_true] at h
    obtain ⟨w1, h1⟩ := hb ty h.1.1
    obtain ⟨w2, h2⟩ := hb bd h.1.2
    obtain ⟨p, hp⟩ := hpw pw h.2
    exact ⟨_, by simp [exprOfF, h1, h2, hp, bind, Except.bind, pure, Except.pure]; rfl⟩
  | forallE ty bd pw =>
    simp only [refsOK, Bool.and_eq_true] at h
    obtain ⟨w1, h1⟩ := hb ty h.1.1
    obtain ⟨w2, h2⟩ := hb bd h.1.2
    obtain ⟨p, hp⟩ := hpw pw h.2
    exact ⟨_, by simp [exprOfF, h1, h2, hp, bind, Except.bind, pure, Except.pure]; rfl⟩
  | letE ty vl bd =>
    simp only [refsOK, Bool.and_eq_true] at h
    obtain ⟨w1, h1⟩ := hb ty h.1.1
    obtain ⟨w2, h2⟩ := hb vl h.1.2
    obtain ⟨w3, h3⟩ := hb bd h.2
    exact ⟨_, by simp [exprOfF, h1, h2, h3, bind, Except.bind, pure, Except.pure]; rfl⟩
  | proj tn ix sx =>
    simp only [refsOK, Bool.and_eq_true] at h
    obtain ⟨a, ha⟩ := hn tn h.1
    obtain ⟨w, hw⟩ := hb sx h.2
    exact ⟨_, by simp [exprOfF, ha, hw, bind, Except.bind, pure, Except.pure]; rfl⟩
  | natVal n => exact ⟨_, rfl⟩
  | strVal s => exact ⟨_, rfl⟩

/-- The relation after binding expression `i`, at or above the counter
with nothing in the gap, to `v`, when the tables hold `w` there and a
built `w` is `v`. -/
theorem LHolds.insertE {st : StateD} {P : Prior} {c : Ctr} (hst : LHolds st P c) {i : Nat}
    {v w : Expr} (hci : c.e ≤ i) (hgap : ∀ j, c.e ≤ j → j < i → P.e.get j = none)
    (hw : P.e.get i = some w) (hwv : isLazyE w = false → w = v) :
    LHolds { st with exprs := st.exprs.insert i v } P { c with e := i + 1 } := by
  refine ⟨hst.n, hst.l, fun j => ?_, fun j u hj hu hl => ?_⟩
  · simp only [IdTable.get?_insert]
    by_cases hji : j = i
    · subst hji; simp [hw]
    · simp only [hji, ↓reduceIte, hst.e j]
      by_cases h1 : j < c.e
      · simp [h1, show j < i + 1 by omega]
      · by_cases h2 : j < i
        · simp [hgap j (by omega) h2]
        · simp [show ¬ j < c.e by omega, show ¬ j < i + 1 by omega]
  · simp only at hj
    simp only [IdTable.get?_insert]
    by_cases hji : j = i
    · subst hji; rw [hw] at hu; cases hu; simp [hwv hl]
    · simp only [hji, ↓reduceIte]
      by_cases h1 : j < c.e
      · exact hst.eb j u h1 hu hl
      · rw [hgap j (by omega) (by omega)] at hu; cases hu

theorem nameOfF_args (nm : Nat → Except ε Name) (lv lv' : Nat → Except ε Level)
    (ex ex' : Nat → Except ε Expr) (x : NameRec) : nameOfF nm lv ex x = nameOfF nm lv' ex' x := by
  cases x <;> rfl

theorem levelOfF_args (nm : Nat → Except ε Name) (lv : Nat → Except ε Level)
    (ex ex' : Nat → Except ε Expr) (x : LevelRec) :
    levelOfF nm lv ex x = levelOfF nm lv ex' x := by
  cases x <;> rfl

/-- **One line passing the lazy check is one serial step**, keeping the
relation, with the records and kept lines the accumulator's. -/
theorem checkLineL_sim {P : Prior} {nd : ByteArray} {c c' : Ctr} {r : LineRec} {a a' : LAcc}
    (h : checkLineL P nd c r a = some (c', a')) {st : StateD} {gds : List Declaration}
    {L : List (Nat × ExprRec)} (hst : LHolds st P c) (hacc : AccOK st a gds L) :
    ∃ st' extra L', applyLine st r = .ok (.inl st') ∧ LHolds st' P c' ∧ Ext st st' ∧
      AccOK st' a' (gds ++ extra) L' ∧ st'.decls.toList = st.decls.toList ++ extra := by
  cases r with
  | name i x =>
    simp only [checkLineL] at h
    split at h
    · rename_i c1 o h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨hki, hgap, v, hv, hx⟩, rfl, -⟩ := checkLine_sound h1
      have hx' : nameOf st.lk x = .ok v := by
        rw [nameOf_eq, cutLk_tabs] at hx
        simp only [nameOf_eq, StateD.lk, hst.name]
        rw [nameOfF_args _ _ (lkL P c.l) _ (lkE P c.e)]; exact hx
      have hni : st.names.get? i = none := by rw [hst.n i]; simp; omega
      let st' : StateD := { st with names := st.names.insert i v }
      have hext : Ext st st' := ⟨ext_insert hni, fun _ _ h => h, fun _ _ h => h⟩
      refine ⟨st', [], L, ?_, ⟨fun j => get?_insert_cut hst.n hki hgap hv j, hst.l, hst.e, hst.eb⟩,
        hext, ?_, by simp [st']⟩
      · simp only [applyLine, parseNameEntryD, hx', StateD.freshName,
          bound_cut hst.n hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
          ↓reduceIte, st']
      · simpa using hacc.ext hext
    · simp at h
  | level i x =>
    simp only [checkLineL] at h
    split at h
    · rename_i c1 o h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨⟨hki, hgap, v, hv, hx⟩, rfl, -⟩ := checkLine_sound h1
      have hx' : levelOf st.lk x = .ok v := by
        simp only [levelOf, cutLk_tabs] at hx
        simp only [levelOf, StateD.lk, hst.name, hst.level]
        rw [levelOfF_args _ _ _ (lkE P c.e)]; exact hx
      have hni : st.levels.get? i = none := by rw [hst.l i]; simp; omega
      let st' : StateD := { st with levels := st.levels.insert i v }
      have hext : Ext st st' := ⟨fun _ _ h => h, ext_insert hni, fun _ _ h => h⟩
      refine ⟨st', [], L, ?_, ⟨hst.n, fun j => get?_insert_cut hst.l hki hgap hv j, hst.e, hst.eb⟩,
        hext, ?_, by simp [st']⟩
      · simp only [applyLine, parseLevelEntryD, hx', StateD.freshLevel,
          bound_cut hst.l hki, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
          ↓reduceIte, st']
      · simpa using hacc.ext hext
    · simp at h
  | expr i x =>
    simp only [checkLineL] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hki, hgap⟩ := hc
      have hgap := Pages.noneIn_sound hgap
      have hni : st.exprs.get? i = none := hst.above hki
      have hbi : st.exprs.bound i = false := by rw [IdTable.bound_eq, hni]; rfl
      split at h
      · rename_i w hw
        split at h
        · -- a lazy line
          rename_i hlz
          split at h
          · rename_i hrefs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨v, hv⟩ := refsOK_ok hst hrefs
            let st' : StateD := { st with exprs := st.exprs.insert i v }
            have hext : Ext st st' := ⟨fun _ _ h => h, fun _ _ h => h, ext_insert hni⟩
            have hfact : LazyFact st' i x := by
              refine ⟨v, by simp [st', IdTable.get?_insert], ?_⟩
              refine exprOfF_mono (Mono.refl _) (Mono.refl _) ?_ hv
              intro k u hk
              have hk' := StateD.get_of_expr hk
              have hkc : k < c.e := by
                by_cases hh : k < c.e
                · exact hh
                · rw [hst.above (by omega)] at hk'; cases hk'
              simp only [exprBelow, show k < i by omega, ↓reduceIte]
              exact hext.monoE k u hk
            refine ⟨st', [], L ++ [(i, x)], ?_, hst.insertE hki hgap hw (by simp [hlz]), hext,
              by simpa using (hacc.ext hext).lazy hfact, by simp [st']⟩
            simp only [applyLine, parseExprEntryD, StateD.freshExpr, hbi, exprOf, StateD.lk, hv,
              bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte, st']
          · simp at h
        · -- a built line
          rename_i hlz
          split at h
          · rename_i hx
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hv : exprOfF st.name st.level st.expr x = .ok w := by
              rw [hst.name, hst.level]
              exact exprOfF_mono (Mono.refl _) (Mono.refl _) hst.monoE (exprCheck_sound hx)
            let st' : StateD := { st with exprs := st.exprs.insert i w }
            have hext : Ext st st' := ⟨fun _ _ h => h, fun _ _ h => h, ext_insert hni⟩
            refine ⟨st', [], L, ?_, hst.insertE hki hgap hw (fun _ => rfl), hext,
              by simpa using hacc.ext hext, by simp [st']⟩
            simp only [applyLine, parseExprEntryD, StateD.freshExpr, hbi, exprOf, StateD.lk, hv,
              bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte, st']
          · simp at h
      · simp at h
    · simp at h
  | decl d =>
    have key : ∃ d' x, a' = a.push d' ∧ c' = c ∧ declOf st.lk d = .ok (.inl x) ∧ DRel st d' x := by
      have hmn : Mono (lkN P c.n) st.name := by rw [hst.name]; exact Mono.refl _
      have generic : ∀ {d : DeclRec} (_ : ∀ cvr vid, d ≠ .thm cvr vid)
          (_ : declBuilt P c.e d = true → ∀ x, declOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) d =
              .ok (.inl x) → declOf st.lk d = .ok (.inl x)),
          checkLineL P nd c (.decl d) a = some (c', a') →
          ∃ d' x, a' = a.push d' ∧ c' = c ∧ declOf st.lk d = .ok (.inl x) ∧ DRel st d' x := by
        intro d hd hbuild h
        have h' : (if declBuilt P c.e d then
            match declOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) d with
            | .ok (.inl x) => if isThmDecl x then none else some (c, a.push x)
            | _ => none
          else none) = some (c', a') := by
          cases d with
          | thm cvr vid => exact absurd rfl (hd cvr vid)
          | _ => exact h
        split at h'
        · rename_i hb
          split at h'
          · rename_i x hx
            split at h'
            · simp at h'
            · rename_i hnt
              simp only [Option.some.injEq, Prod.mk.injEq] at h'
              obtain ⟨rfl, rfl⟩ := h'
              refine ⟨x, x, rfl, rfl, hbuild hb x hx, ?_⟩
              cases x with
              | thmDecl cv w => simp [isThmDecl] at hnt
              | _ => rfl
          · simp at h'
        · simp at h'
      cases d with
      | thm cvr vid =>
        simp only [checkLineL] at h
        split at h
        · rename_i cv hcv
          split at h
          · rename_i hb
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨w, hw⟩ := hst.boundN' hb
            refine ⟨_, .thmDecl cv w, rfl, rfl, ?_, vid, _, rfl, hw⟩
            have hcv' := cvOfF_mono (lv' := st.level) hmn hst.monoE hcv
            simp [declOf, declOfF, StateD.lk, hcv', StateD.expr_of_get hw, bind, Except.bind,
              pure, Except.pure]
          · simp at h
        · simp at h
      | ind tys cts rcs =>
        refine generic (fun _ _ h => nomatch h) ?_ h
        intro hb x hx
        simp only [declBuilt, List.all_eq_true] at hb
        have he : ∀ j ∈ indExprIds tys cts rcs, lkEB P c.e j = st.expr j := by
          intro j hj
          obtain ⟨u, hu⟩ := isOk_iff.mp (hb j hj)
          rw [hu, hst.monoE j u hu]
        rw [declOfF_ind_congr he, ← hst.name, ← hst.level] at hx
        exact hx
      | ax cvr u =>
        refine generic (fun _ _ h => nomatch h) ?_ h
        intro _ x hx
        rw [← hst.name, ← hst.level] at hx
        exact declOfF_mono hst.monoE (by intro _ _ _ h; cases h) hx
      | defn cvr vl hints safety =>
        refine generic (fun _ _ h => nomatch h) ?_ h
        intro _ x hx
        rw [← hst.name, ← hst.level] at hx
        exact declOfF_mono hst.monoE (by intro _ _ _ h; cases h) hx
      | opaq cvr vl u =>
        refine generic (fun _ _ h => nomatch h) ?_ h
        intro _ x hx
        rw [← hst.name, ← hst.level] at hx
        exact declOfF_mono hst.monoE (by intro _ _ _ h; cases h) hx
      | quot cvr k =>
        refine generic (fun _ _ h => nomatch h) ?_ h
        intro _ x hx
        rw [← hst.name, ← hst.level] at hx
        exact declOfF_mono hst.monoE (by intro _ _ _ h; cases h) hx
    obtain ⟨d', x, rfl, rfl, hx, hrel⟩ := key
    refine ⟨pushDecl st x, [x], L, ?_, ⟨hst.n, hst.l, hst.e, hst.eb⟩, ⟨fun _ _ h => h,
      fun _ _ h => h, fun _ _ h => h⟩, ?_, by simp [pushDecl]⟩
    · simp only [applyLine, applyDeclD, processLineCoreD, hx, bind, Except.bind, pure,
        Except.pure]
    · have hext : Ext st (pushDecl st x) := ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
      exact (hacc.ext hext).push (DRel.ext hext hrel)
  | header =>
    simp only [checkLineL, checkLine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨st, [], L, rfl, hst, Ext.refl _, by simpa using hacc, by simp⟩
  | blank =>
    simp only [checkLineL, checkLine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨st, [], L, rfl, hst, Ext.refl _, by simpa using hacc, by simp⟩

/-! ## A list of lines, a flat chunk -/

theorem checkListL_sim {P : Prior} {nd : ByteArray} :
    ∀ (rs : List LineRec) {c c' : Ctr} {a a' : LAcc} {st : StateD} {gds : List Declaration}
      {L : List (Nat × ExprRec)} (k : Nat),
    checkListL P nd c rs a = some (c', a') → LHolds st P c → AccOK st a gds L →
    ∃ st' extra L', applyList st rs k = .ok (st', k + rs.length) ∧ LHolds st' P c' ∧
      Ext st st' ∧ AccOK st' a' (gds ++ extra) L' ∧ st'.decls.toList = st.decls.toList ++ extra
  | [], c, c', a, a', st, gds, L, k, h, hst, hacc => by
    simp only [checkListL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨st, [], L, rfl, hst, Ext.refl _, by simpa using hacc, by simp⟩
  | r :: rs, c, c', a, a', st, gds, L, k, h, hst, hacc => by
    simp only [checkListL] at h
    split at h
    · rename_i c1 a1 h1
      obtain ⟨st1, ex1, L1, hap1, hst1, hext1, hacc1, hd1⟩ := checkLineL_sim h1 hst hacc
      obtain ⟨st2, ex2, L2, hap2, hst2, hext2, hacc2, hd2⟩ :=
        checkListL_sim rs (k + 1) h hst1 hacc1
      refine ⟨st2, ex1 ++ ex2, L2, ?_, hst2, hext1.trans hext2, by simpa using hacc2, ?_⟩
      · simp only [applyList, hap1, hap2, List.length_cons]; congr 2; omega
      · rw [hd2, hd1]; simp
    · simp at h

theorem checkFlatGoL_eq (P : Prior) (nd : ByteArray) (d : ByteArray) (hd : d.size < USize.size)
    (L : List LineRec) :
    ∀ (c : Ctr) (a : LAcc) (p : USize) (rest : List UInt8),
    d.data.toList.drop p.toNat = Flat.encElems Flat.encLine L ++ rest →
    checkFlatGoL P nd d p L.length c a = checkListL P nd c L a := by
  induction L with
  | nil => intro c a p rest _; rfl
  | cons r L ih =>
    intro c a p rest h
    simp only [Flat.encElems, List.append_assoc] at h
    obtain ⟨q, e, hq⟩ := Flat.withLineU_spec r d hd p _ h
      (fun r q => match checkLineL P nd c r a with
        | some (c', a') => checkFlatGoL P nd d q L.length c' a'
        | none => none)
    have h' := Flat.drop_after h
    rw [← hq] at h'
    rw [List.length_cons, checkFlatGoL]
    refine e.trans ?_
    simp only [checkListL]
    cases checkLineL P nd c r a with
    | none => rfl
    | some p => obtain ⟨c', a'⟩ := p; exact ih _ _ q rest h'

/-- **The flat check is the check of the lines the chunk holds.** -/
theorem checkFlatL_sound {P : Prior} {nd : ByteArray} {fc : FlatChunk} {sc : ScannedChunk}
    (h : fc.Encodes sc) {c : Ctr} {r : Ctr × LAcc} (hc : checkFlatL P nd fc c = some r) :
    checkListL P nd c sc.recs.toList LAcc.init = some r := by
  obtain ⟨hd, hcount, _⟩ := h
  simp only [checkFlatL] at hc
  split at hc
  · rename_i hs
    rw [hcount, ← Array.length_toList,
      checkFlatGoL_eq P nd fc.data hs _ c LAcc.init 0 [] (by simp [hd])] at hc
    exact hc
  · simp at hc

/-! ## The invariant between windows -/

/-- The store's chunks hold lazy lines of the serial state `st`. -/
@[expose] def StoreOK (st : StateD) (S : Array LChunk) : Prop :=
  ∀ C ∈ S.toList, ∃ L, CValid C L ∧ ∀ p ∈ L, LazyFact st p.1 p.2

theorem StoreOK.ext {a b : StateD} (h : Ext a b) {S : Array LChunk} (hs : StoreOK a S) :
    StoreOK b S := fun C hC => by
  obtain ⟨L, hv, hl⟩ := hs C hC
  exact ⟨L, hv, fun p hp => (hl p hp).ext h⟩

/-- **The lazy parse's invariant**: some state the serial parse reaches
after the lines so far, with nothing carried, is related to the
finished tables at the counters, its records to the run-time ones, and
the store's lines to it. -/
def LGOK (g : LGSt) : Prop :=
  ∃ st, Reached st .empty g.lineNo g.total ∧ LHolds st g.P g.c ∧
    Pw (DRel st) g.ds.toList st.decls.toList ∧ StoreOK st g.S

/-- The parse's start. -/
def LGSt.init : LGSt := ⟨Prior.init, ⟨1, 1, 0⟩, #[], 0, 0, #[]⟩

theorem LGOK.init : LGOK LGSt.init := by
  refine ⟨.init, Reached.init, ⟨fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩, trivial, ?_⟩
  · simp only [StateD.init, IdTable.get?_singleton, LGSt.init, Prior.init, Pages.get_eq]
    rcases j with _ | j
    · simp [Sent.isPend]
    · simp
  · simp only [StateD.init, IdTable.get?_singleton, LGSt.init, Prior.init, Pages.get_eq]
    rcases j with _ | j
    · simp [Sent.isPend]
    · simp
  · simp [StateD.init, IdTable.get?_empty, LGSt.init]
  · intro j v hj; simp [LGSt.init] at hj
  · intro C hC; simp [LGSt.init] at hC

/-- **The tables after a window**, when they keep the tables before. -/
theorem LGOK.keep {g : LGSt} (h : LGOK g) {nn nl ne}
    (hk : g.P.keeps g.c nn nl ne = true) : LGOK { g with P := g.P.setFrom g.c nn nl ne } := by
  obtain ⟨st, hr, hh, hd, hs⟩ := h
  simp only [Prior.keeps, Bool.and_eq_true] at hk
  obtain ⟨⟨hn, hl⟩, he⟩ := hk
  refine ⟨st, hr, ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j v hj hv hz => ?_⟩, hd, hs⟩
  · rw [hh.n j]; split
    · exact (Pages.keeps_sound hn j (by assumption)).symm
    · rfl
  · rw [hh.l j]; split
    · exact (Pages.keeps_sound hl j (by assumption)).symm
    · rfl
  · rw [hh.e j]
    by_cases hj : j < g.c.e
    · simp only [Prior.setFrom]; rw [Pages.keeps_sound he j hj]
    · simp [hj]
  · simp only [Prior.setFrom] at hv
    rw [Pages.keeps_sound he j hj] at hv
    exact hh.eb j v hj hv hz

theorem Pw.toList_append {α β : Type} {R : α → β → Prop} {a₁ : Array α} {b₁ : List β}
    {a₂ : Array α} {b₂ : List β} (h₁ : Pw R a₁.toList b₁) (h₂ : Pw R a₂.toList b₂) :
    Pw R (a₁ ++ a₂).toList (b₁ ++ b₂) := by
  rw [Array.toList_append]; exact Pw.append h₁ h₂

/-- **A chunk that passes the lazy check is one more serial step.** -/
theorem LGOK.chunk {g : LGSt} (h : LGOK g) {b : ByteArray} {fc : FlatChunk}
    (henc : fc.Encodes (scanChunk b)) (hfit : chunkFits b fc g.total = true)
    {nd : ByteArray} {c' : Ctr} {a : LAcc} (hc : checkFlatL g.P nd fc g.c = some (c', a)) :
    LGOK { g with c := c', ds := g.ds ++ a.ds, lineNo := g.lineNo + fc.count,
                  total := g.total + b.size, S := g.S.push ⟨a.cd, a.spId, a.spOff⟩ } := by
  obtain ⟨st, hr, hh, hd, hs⟩ := h
  have hl := checkFlatL_sound henc hc
  obtain ⟨st', extra, L, happ, hh', hext, hacc, hdec⟩ :=
    checkListL_sim (scanChunk b).recs.toList g.lineNo hl hh (AccOK.init st)
  simp only [chunkFits] at hfit
  split at hfit
  · rename_i i hstop
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
    obtain ⟨hi, hsz⟩ := hfit
    have hs' : chunkStep st .empty g.lineNo g.total b =
        .ok (st', .empty, g.lineNo + fc.count, g.total + b.size) := by
      rw [← chunkStepF_of_encodes _ _ _ _ _ _ henc]
      have hcount : fc.count = (scanChunk b).recs.toList.length := by
        rw [henc.2.1]; simp
      rw [chunkStepF, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl),
        ite_eq_right (show ¬ (g.total + b.size ≥ USize.size) by omega)]
      rw [applyFlat_eq _ _ _ henc, applyScanned, applyRecs_eq, List.drop_zero, happ]
      rw [← henc.2.2, hstop]
      simp only [hcount, hi, ByteArray.extract_size_self]
    refine ⟨st', hr.step hs', hh', ?_, ?_⟩
    · rw [hdec]
      exact Pw.toList_append (Pw.imp (fun _ _ => DRel.ext hext) hd) (by simpa using hacc.ds)
    · intro C hC
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hC
      rcases hC with hC | rfl
      · exact (hs.ext hext) C hC
      · exact ⟨L, ⟨hacc.cd, hacc.sp⟩, hacc.lz⟩
  · simp at hfit

/-- **The end of the stream**: the serial parse's result, its records
related to the run-time ones, its state to the tables and the store. -/
theorem LGOK.finish {g : LGSt} (h : LGOK g) :
    ∃ cs stF, parseChunks cs = .ok ⟨stF.decls⟩ ∧ LHolds stF g.P g.c ∧
      Pw (DRel stF) g.ds.toList stF.decls.toList ∧ StoreOK stF g.S := by
  obtain ⟨st, hr, hh, hd, hs⟩ := h
  obtain ⟨cs, hcs⟩ := hr.finish
  refine ⟨cs, st, ?_, hh, hd, hs⟩
  rw [hcs, chunkFinish, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl)]
  rfl

/-! ## The builds -/

theorem encLz_take_drop (L : List (Nat × ExprRec)) (m : Nat) :
    encLz L = encLz (L.take m) ++ encLz (L.drop m) := by
  simp only [encLz]
  rw [← encElems_append, ← List.map_append, List.take_append_drop]

theorem withLineU_cases {β : Type} (r : LineRec) (d : ByteArray) (hd : d.size < USize.size)
    (p : USize) (rest : List UInt8) (h : d.data.toList.drop p.toNat = Flat.encLine r ++ rest)
    {k : LineRec → USize → β} {y : β} (hy : Flat.withLineU d p k = y) :
    ∃ q, k r q = y ∧ q.toNat = p.toNat + (Flat.encLine r).length := by
  obtain ⟨q, e, hq⟩ := Flat.withLineU_spec r d hd p rest h k
  exact ⟨q, e ▸ hy, hq⟩

theorem walkTo_sound {L : List (Nat × ExprRec)} {d : ByteArray} (hd : d.size < USize.size)
    (hcd : d.data.toList = encLz L) {j : Nat} {x : ExprRec} :
    ∀ (fuel : Nat) (p : USize) (m : Nat), m ≤ L.length →
      p.toNat = (encLz (L.take m)).length → walkTo d j p fuel = some x → (j, x) ∈ L := by
  intro fuel
  induction fuel with
  | zero => intro p m _ _ h; simp [walkTo] at h
  | succ fuel ih =>
    intro p m hm hp h
    simp only [walkTo] at h
    split at h
    · rename_i hpl
      have hpl' : p.toNat < d.size := by
        have := USize.lt_iff_toNat_lt.mp hpl
        rwa [Flat.usize_eq_size hd] at this
      have hmL : m < L.length := by
        by_cases hh : m < L.length
        · exact hh
        · have : m = L.length := by omega
          subst this
          rw [List.take_length] at hp
          have := congrArg List.length hcd
          simp only [Array.length_toList, ByteArray.size] at this hpl'
          omega
      have hdrop : d.data.toList.drop p.toNat =
          Flat.encLine (.expr (L[m]).1 (L[m]).2) ++ encLz (L.drop (m + 1)) := by
        rw [hcd, encLz_take_drop L m, hp, List.drop_left, List.drop_eq_getElem_cons hmL]
        simp only [encLz, List.map_cons, Flat.encElems]
      split at h
      · obtain ⟨q, h, hq⟩ := withLineU_cases _ d hd p _ hdrop h
        simp only at h
        split at h
        · rename_i hij
          simp only [Option.some.injEq] at h
          subst h
          have : (j, (L[m]).2) = L[m] := by
            simp only [beq_iff_eq] at hij; rw [← hij]
          rw [this]; exact List.getElem_mem hmL
        · simp at h
      · split at h
        · refine ih _ (m + 1) (by omega) ?_ h
          rw [Flat.lineEndU_spec _ d hd p _ hdrop, hp, List.take_add_one,
            List.getElem?_eq_getElem hmL]
          simp only [Option.toList, encLz, List.map_append, encElems_append, List.map_cons,
            List.map_nil, Flat.encElems, List.length_append, List.append_nil]
        · simp at h
    · simp at h

theorem lastLE_lt (a : Array Nat) (j : Nat) :
    ∀ lo hi, lo < hi → lastLE a j lo hi < hi := by
  intro lo hi h
  induction lo, hi using lastLE.induct a j with
  | case1 lo hi hlt mid hle ih => rw [lastLE, ite_eq_left hlt, ite_eq_left hle]; exact ih (by omega)
  | case2 lo hi hlt mid hle ih => rw [lastLE, ite_eq_left hlt, ite_eq_right hle]; exact Nat.lt_trans (ih (by omega)) (by omega)
  | case3 lo hi hlt => rw [lastLE, ite_eq_right hlt]; exact h

theorem lastLE32_lt (a : ByteArray) (j : Nat) :
    ∀ lo hi, lo < hi → lastLE32 a j lo hi < hi := by
  intro lo hi h
  induction lo, hi using lastLE32.induct a j with
  | case1 lo hi hlt mid hle ih => rw [lastLE32, ite_eq_left hlt, ite_eq_left hle]; exact ih (by omega)
  | case2 lo hi hlt mid hle ih =>
    rw [lastLE32, ite_eq_left hlt, ite_eq_right hle]; exact Nat.lt_trans (ih (by omega)) (by omega)
  | case3 lo hi hlt => rw [lastLE32, ite_eq_right hlt]; exact h

theorem LChunk.find_sound {C : LChunk} {L : List (Nat × ExprRec)} (hv : CValid C L) {j : Nat}
    {x : ExprRec} (h : C.find j = some x) : (j, x) ∈ L := by
  simp only [LChunk.find] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨hsz, hsame⟩, hpos⟩ := hc
    have hs' : lastLE32 C.spId j 0 C.spOff.size < C.spOff.size := lastLE32_lt _ j 0 _ hpos
    obtain ⟨m, hm, e⟩ := hv.2 _ hs'
    refine walkTo_sound hsz hv.1 _ _ m hm ?_ h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs', Option.getD_some, ← e]
    simp only [Nat.toUSize, USize.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have h1 : C.cd.data.size = (encLz L).length := by rw [← hv.1]; simp
    have h2 : C.cd.size = C.cd.data.size := rfl
    have hle : (encLz (L.take m)).length ≤ (encLz L).length := by
      rw [encLz_take_drop L m]; simp
    rw [e]
    calc (encLz (L.take m)).length ≤ (encLz L).length := hle
      _ = C.cd.size := by rw [h2, h1]
      _ < USize.size := hsz
  · simp at h

theorem LStore.find_sound {S : LStore} {j : Nat} {x : ExprRec} (h : S.find j = some x) :
    ∃ C ∈ S.chunks.toList, C.find j = some x := by
  simp only [LStore.find] at h
  split at h
  · split at h
    · rename_i hk
      exact ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem hk), h⟩
    · simp at h
  · simp at h

/-- **The store and the serial state**: the same names and levels below
the counters, and every retained expression the serial state's. -/
structure SHolds (G : StateD) (S : LStore) : Prop where
  name : G.name = lkN S.P S.c.n
  level : G.level = lkL S.P S.c.l
  monoE : Mono (rtLk S) G.expr

theorem LStore.findH_sound {S : LStore} {kc j : Nat} {x : ExprRec} (h : S.findH kc j = some x) :
    ∃ C ∈ S.chunks.toList, C.find j = some x := by
  simp only [LStore.findH] at h
  split at h
  · rename_i hk
    split at h
    · exact ⟨_, Array.mem_toList_iff.mpr (Array.getElem_mem hk), h⟩
    · exact LStore.find_sound h
  · exact LStore.find_sound h

/-- The memo's entries are the serial state's. -/
@[expose] def MemoOK (G : StateD) (memo : Memo) : Prop :=
  ∀ k v, memo.get? k = some v → G.exprs.get? k = some v

theorem Memo.empty_ok (G : StateD) : MemoOK G Memo.empty := fun k v h => by
  simp [Memo.empty, Memo.get?] at h

theorem regionMemo_ok (G : StateD) (base vid : Nat) : MemoOK G (regionMemo base vid) := by
  intro k v h
  simp only [regionMemo] at h
  split at h
  · simp only [Memo.get?, Array.getElem_replicate] at h
    split at h
    · split at h
      · simp [isPendE, pendExpr] at h
      · simp at h
    · simp at h
  · simp [Memo.empty, Memo.get?] at h

theorem Memo.get?_insert_ne (m : Memo) {j k : Nat} (v : Expr) (hjk : j ≠ k) :
    (m.insert k v).get? j = m.get? j := by
  obtain ⟨b, arr, map⟩ := m
  have hmap : (map.insert k v).get? j = map.get? j := by
    rw [Std.HashMap.get?_insert]; simp [Ne.symm hjk]
  simp only [Memo.insert]
  split
  · split
    · split
      · rfl
      · simp only [Memo.get?, Array.size_set!]
        split
        · split
          · rename_i _ _ _ hbj hja
            have hne : k - b ≠ j - b := by omega
            simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds_ne hja hne]
          · rfl
        · rfl
    · simp only [Memo.get?, hmap]
  · simp only [Memo.get?, hmap]

theorem Memo.get?_insert_self (m : Memo) (k : Nat) (v : Expr) :
    (m.insert k v).get? k = some v ∨ m.insert k v = m := by
  obtain ⟨b, arr, map⟩ := m
  simp only [Memo.insert]
  split
  · rename_i hbk
    split
    · rename_i hka
      split
      · exact .inr rfl
      · rename_i hnp
        left
        have hka' : k - b < (arr.set! (k - b) v).size := by simpa using hka
        simp only [Memo.get?, hbk, ↓reduceIte, hka', ↓reduceDIte]
        simp [hnp]
    · rename_i hka
      left
      simp [Memo.get?, hbk, hka]
  · rename_i hbk
    left
    simp [Memo.get?, hbk]

/-- A correct entry inserted keeps the memo correct. -/
theorem Memo.insert_ok {G : StateD} {m : Memo} (hm : MemoOK G m) {k : Nat} {v : Expr}
    (hv : G.exprs.get? k = some v) : MemoOK G (m.insert k v) := by
  intro j u hj
  by_cases hjk : j = k
  · subst hjk
    rcases Memo.get?_insert_self m j v with h | h
    · rw [h] at hj; cases hj; exact hv
    · rw [h] at hj; exact hm j u hj
  · rw [Memo.get?_insert_ne m v hjk] at hj
    exact hm j u hj

/-- One line built over the memo: its value is the serial entry. -/
theorem memo_insert_ok {S : LStore} {G : StateD} (hh : SHolds G S) {memo : Memo}
    (hm : MemoOK G memo) {j : Nat} {x : ExprRec} (hf : LazyFact G j x) {v : Expr}
    (hv : exprOfF (lkN S.P S.c.n) (lkL S.P S.c.l) (memoLk S memo j) x = .ok v) :
    MemoOK G (memo.insert j v) := by
  obtain ⟨v₀, hv1, hv2⟩ := hf
  have hmono : exprOfF G.name G.level (exprBelow G j) x = .ok v := by
    refine exprOfF_mono (by rw [hh.name]; exact Mono.refl _)
      (by rw [hh.level]; exact Mono.refl _) ?_ hv
    intro k u hk
    simp only [memoLk] at hk
    simp only [exprBelow]
    split at hk
    · rename_i hkj
      rw [ite_eq_left hkj]
      split at hk
      · rename_i u' hu'
        simp only [pure, Except.pure, Except.ok.injEq] at hk
        subst hk
        exact StateD.expr_of_get (hm k u' hu')
      · exact hh.monoE k u hk
    · simp [throw, throwThe, MonadExceptOf.throw] at hk
  rw [hv2] at hmono
  cases hmono
  exact Memo.insert_ok hm hv1

/-- The lines a build's stack holds, found before: lazy lines of the
store. -/
@[expose] def StackOK (G : StateD) (st : List (Nat × Option ExprRec)) : Prop :=
  ∀ j x, (j, some x) ∈ st → LazyFact G j x

theorem buildGo_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) (kc : Nat) :
    ∀ (fuel : Nat) (stack : List (Nat × Option ExprRec)) (memo : Memo), StackOK G stack →
      MemoOK G memo → MemoOK G (buildGo S kc fuel stack memo) := by
  intro fuel
  induction fuel with
  | zero => intro stack memo _ hm; simpa [buildGo] using hm
  | succ fuel ih =>
    intro stack memo hst hm
    cases stack with
    | nil => simpa [buildGo] using hm
    | cons e rest =>
      obtain ⟨j, ox⟩ := e
      have hrest : StackOK G rest := fun j x h => hst j x (List.mem_cons_of_mem _ h)
      simp only [buildGo]
      split
      · exact ih _ _ hrest hm
      · split
        · exact hm
        · rename_i x hx
          have hfact : LazyFact G j x := by
            cases ox with
            | some y =>
              simp only [Option.some.injEq] at hx; subst hx
              exact hst j y List.mem_cons_self
            | none =>
              simp only at hx
              obtain ⟨C, hC, hf⟩ := LStore.findH_sound hx
              obtain ⟨L, hv, hl⟩ := hs C hC
              exact hl _ (LChunk.find_sound hv hf)
          split
          · rename_i v' hv'
            exact ih _ _ hrest (memo_insert_ok hh hm hfact hv')
          · split
            · exact hm
            · split
              · refine ih _ _ ?_ hm
                intro i y hi
                rcases List.mem_append.mp hi with hi | hi
                · simp at hi
                · rcases List.mem_cons.mp hi with hi | hi
                  · simp only [Prod.mk.injEq, Option.some.injEq] at hi
                    obtain ⟨rfl, rfl⟩ := hi; exact hfact
                  · exact hrest i y hi
              · exact hm

theorem StackOK.nones (G : StateD) (l : List Nat) : StackOK G (l.map (·, none)) := by
  intro j x h; simp at h

theorem regionSlow_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) (kc : Nat) {d : ByteArray} (hd : d.size < USize.size) {p : USize}
    {i : Nat} {x : ExprRec} {rest : List UInt8}
    (hdrop : d.data.toList.drop p.toNat = Flat.encLine (.expr i x) ++ rest)
    (hf : LazyFact G i x) (j : Nat) {memo : Memo} (hm : MemoOK G memo) :
    MemoOK G (regionSlow S kc d p j memo) := by
  simp only [regionSlow]
  generalize hy : Flat.withLineU d p _ = y
  obtain ⟨q, hk, -⟩ := withLineU_cases _ d hd p _ hdrop hy
  rw [← hk]
  simp only
  split
  · rename_i hij
    simp only [beq_iff_eq] at hij
    subst hij
    have hm1 := buildGo_sound hh hs kc buildFuel _ memo
      (StackOK.nones G (missingKids S memo (exprKids x))) hm
    split
    · rename_i v hv; exact memo_insert_ok hh hm1 hf hv
    · exact hm1
  · exact hm

theorem regionGo_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) {L : List (Nat × ExprRec)} (hlz : ∀ p ∈ L, LazyFact G p.1 p.2) {d : ByteArray}
    (hd : d.size < USize.size) (hcd : d.data.toList = encLz L) (kc vid : Nat) :
    ∀ (fuel : Nat) (p : USize) (m : Nat) (memo : Memo), m ≤ L.length →
      p.toNat = (encLz (L.take m)).length → MemoOK G memo →
      MemoOK G (regionGo S kc d vid p fuel memo) := by
  intro fuel
  induction fuel with
  | zero => intro p m memo _ _ hm; exact hm
  | succ fuel ih =>
    intro p m memo hmL hp hm
    simp only [regionGo]
    split
    · rename_i hpl
      have hpl' : p.toNat < d.size := by
        have := USize.lt_iff_toNat_lt.mp hpl
        rwa [Flat.usize_eq_size hd] at this
      have hmL' : m < L.length := by
        by_cases hh' : m < L.length
        · exact hh'
        · have : m = L.length := by omega
          subst this
          rw [List.take_length] at hp
          have := congrArg List.length hcd
          simp only [Array.length_toList, ByteArray.size] at this hpl'
          omega
      have hdrop : d.data.toList.drop p.toNat =
          Flat.encLine (.expr (L[m]).1 (L[m]).2) ++ encLz (L.drop (m + 1)) := by
        rw [hcd, encLz_take_drop L m, hp, List.drop_left, List.drop_eq_getElem_cons hmL']
        simp only [encLz, List.map_cons, Flat.encElems]
      generalize hy : Flat.withLineU d p _ = y
      obtain ⟨q, hk, hq⟩ := withLineU_cases _ d hd p _ hdrop hy
      rw [← hk]
      simp only
      split
      · exact hm
      · have hfact := hlz _ (List.getElem_mem hmL')
        have hm' : MemoOK G (if memo.has (L[m]).1 then memo else
            match exprOfF (lkN S.P S.c.n) (lkL S.P S.c.l) (memoLk S memo (L[m]).1) (L[m]).2 with
            | .ok v => memo.insert (L[m]).1 v
            | .error _ => regionSlow S kc d p (L[m]).1 memo) := by
          split
          · exact hm
          · split
            · rename_i v hv; exact memo_insert_ok hh hm hfact hv
            · exact regionSlow_sound hh hs kc hd hdrop hfact _ hm
        split
        · exact hm'
        · refine ih q (m + 1) _ (by omega) ?_ hm'
          rw [hq, hp, List.take_add_one, List.getElem?_eq_getElem hmL']
          simp only [Option.toList, encLz, List.map_append, encElems_append, List.map_cons,
            List.map_nil, Flat.encElems, List.length_append, List.append_nil]
    · exact hm

theorem regionIn_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) {C : LChunk} {L : List (Nat × ExprRec)} (hv : CValid C L)
    (hl : ∀ p ∈ L, LazyFact G p.1 p.2) (kc vid hint : Nat) :
    MemoOK G (regionIn S kc C vid hint) := by
  simp only [regionIn]
  split
  · rename_i hcond
    obtain ⟨m, hm, e⟩ := hv.2 hint hcond.2
    refine regionGo_sound hh hs hl hcond.1 hv.1 kc vid _ _ m _ hm ?_ (regionMemo_ok G _ _)
    simp only [Nat.toUSize, USize.toNat_ofNat']
    rw [e]
    apply Nat.mod_eq_of_lt
    have h1 : C.cd.data.size = (encLz L).length := by rw [← hv.1]; simp
    have h2 : C.cd.size = C.cd.data.size := rfl
    have hle : (encLz (L.take m)).length ≤ (encLz L).length := by
      rw [encLz_take_drop L m]; simp
    calc (encLz (L.take m)).length ≤ (encLz L).length := hle
      _ = C.cd.size := by rw [h2, h1]
      _ < USize.size := hcond.1
  · exact Memo.empty_ok G

theorem regionOf_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) (vid hint : Nat) : MemoOK G (regionOf S vid hint) := by
  simp only [regionOf]
  split
  · split
    · rename_i hk
      obtain ⟨L, hv, hl⟩ := hs _ (Array.mem_toList_iff.mpr (Array.getElem_mem hk))
      exact regionIn_sound hh hs hv hl _ vid hint
    · exact Memo.empty_ok G
  · exact Memo.empty_ok G

/-- **A value built from the store is the serial table's entry.** -/
theorem buildVal_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) {vid hint : Nat} {v : Expr} (h : buildVal S vid hint = some v) :
    G.exprs.get? vid = some v := by
  simp only [buildVal] at h
  split at h
  · rename_i u hu
    simp only [Option.some.injEq] at h; subst h
    exact StateD.get_of_expr (hh.monoE vid u hu)
  · exact buildGo_sound hh hs 0 _ _ _ (fun j x h => by simp at h)
      (regionOf_sound hh hs vid hint) vid v h

/-! ## The store, the records, the chunks without their bytes -/

theorem StoreOK.ofChunks {G : StateD} {S : Array LChunk} (hs : StoreOK G S) (P : Prior)
    (c : Ctr) (rt : RTab) : StoreOK G (LStore.ofChunks S P c rt).chunks := fun C hC => by
  simp only [LStore.ofChunks] at hC
  have := Array.mem_toList_iff.mp hC
  exact hs C (Array.mem_toList_iff.mpr (Array.mem_filter.mp this).1)

theorem fillDecl_sound {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) {d' d e : Declaration} (hd : DRel G d' d)
    (he : fillDecl S d' = some e) : e = d := by
  cases d with
  | thmDecl cv w =>
    obtain ⟨vid, hint, rfl, hw⟩ := hd
    simp only [fillDecl, phId?, ph, Option.map_eq_some_iff] at he
    obtain ⟨v, hv, rfl⟩ := he
    rw [buildVal_sound hh hs hv] at hw
    cases hw; rfl
  | _ =>
    subst hd
    simp only [fillDecl, Option.some.injEq] at he
    exact he.symm

/-- What a filled range holds. -/
@[expose] def FillInv (S : LStore) (ds : Array Declaration) (lo : Nat) (a : Array Declaration) : Prop :=
  ∀ k (h : k < a.size), fillDecl S ds[lo + k]! = some a[k]

theorem fillRange_spec (S : LStore) (ds : Array Declaration) (lo hi : Nat) :
    ∀ n i acc r, hi - i = n → acc.size = i - lo → lo ≤ i → FillInv S ds lo acc →
    fillRange S ds i hi acc = some r → r.size = max i hi - lo ∧ FillInv S ds lo r := by
  intro n
  induction n with
  | zero =>
    intro i acc r hn hsz _ hinv h
    rw [fillRange, ite_eq_right (by omega)] at h
    cases h
    exact ⟨by omega, hinv⟩
  | succ n ih =>
    intro i acc r hn hsz hlo hinv h
    rw [fillRange, ite_eq_left (by omega)] at h
    split at h
    · rename_i d hd
      have := ih (i + 1) (acc.push d) r (by omega) (by simp; omega) (by omega) ?_ h
      · exact ⟨by omega, this.2⟩
      intro k hk
      simp only [Array.size_push] at hk
      by_cases hka : k < acc.size
      · rw [Array.getElem_push_lt hka]; exact hinv k hka
      · have : k = acc.size := by omega
        subst this
        rw [Array.getElem_push_eq, show lo + acc.size = i by omega]; exact hd
    · cases h

theorem FillInv.append {S : LStore} {ds : Array Declaration} {a b : Array Declaration}
    (ha : FillInv S ds 0 a) (hb : FillInv S ds a.size b) : FillInv S ds 0 (a ++ b) := by
  intro k hk
  rw [Array.size_append] at hk
  by_cases hka : k < a.size
  · rw [Array.getElem_append_left hka]; exact ha k hka
  · rw [Array.getElem_append_right (by omega)]
    have := hb (k - a.size) (by omega)
    rwa [show a.size + (k - a.size) = 0 + k by omega] at this

/-- **The filled records are the serial ones.** -/
theorem fill_eq {S : LStore} {G : StateD} (hh : SHolds G S)
    (hs : StoreOK G S.chunks) {ds e : Array Declaration} {gds : List Declaration}
    (hd : Pw (DRel G) ds.toList gds) (hsz : e.size = ds.size) (hf : FillInv S ds 0 e) :
    e.toList = gds := by
  have hl := Pw.length hd
  simp only [Array.length_toList] at hl
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  have hk : k < ds.size := by simp at h1; omega
  have := hf k (by simpa using h1)
  rw [Nat.zero_add, getElem!_pos ds k hk] at this
  simp only [Array.getElem_toList]
  exact fillDecl_sound hh hs (by
    have := Pw.getElem hd k (by simpa using hk) h2
    simpa using this) this

theorem chunkStepNB_eq {st : StateD} {lineNo total : Nat} {b : ByteArray} {fc : FlatChunk}
    (henc : fc.Encodes (scanChunk b)) {i : USize} (hstop : fc.stop = .tail i)
    (hi : i.toNat = b.size) :
    chunkStepNB st lineNo total b.size fc = chunkStep st .empty lineNo total b := by
  rw [← chunkStepF_of_encodes _ _ _ _ _ _ henc]
  simp only [chunkStepNB, chunkStepF, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl)]
  split
  · rfl
  · cases happ : applyFlat st fc lineNo with
    | error e => rfl
    | ok r =>
      obtain ⟨st', n, t⟩ := r
      have : t = i := by
        simp only [applyFlat] at happ
        split at happ
        · simp at happ
        · rename_i hr
          rw [hstop] at happ
          simp only [Except.ok.injEq, Prod.mk.injEq] at happ
          exact happ.2.2.symm
      subst this
      simp only [hi, ByteArray.extract_size_self]

theorem chunkFitsN_eq (b : ByteArray) (fc : FlatChunk) (t : Nat) :
    chunkFitsN b.size fc t = chunkFits b fc t := rfl

/-! ## The retained table -/

theorem bitGet_out {bm : ByteArray} {j : Nat} (h : bm.size * 8 ≤ j) : bitGet bm j = false := by
  simp only [bitGet]
  rw [dite_eq_right (by omega)]

theorem bitGet_zero {bm : ByteArray} {j : Nat} (h : bm.get! (j / 8) = 0) : bitGet bm j = false := by
  simp only [bitGet]
  split
  · rename_i hb
    rw [Flat.get!_eq_getElem bm _ hb] at h
    rw [h]; simp
  · rfl

/-- **What a validated retained table answers**: built entries of the
finished tables below the counter. -/
@[expose] def RTValid (R : RTab) (P : Prior) (ce : Nat) : Prop :=
  ∀ k v, R.get k = some v → k < ce ∧ P.e.get k = some v ∧ isLazyE v = false

theorem rtValidR_sound {R : RTab} {P : Prior} {ce hi : Nat} :
    ∀ (n j : Nat), hi - j ≤ n → rtValidR R P ce hi j = true →
    ∀ k v, j ≤ k → k < hi → R.get k = some v → k < ce ∧ P.e.get k = some v ∧ isLazyE v = false := by
  intro n
  induction n with
  | zero => intro j hn _ k v hk hkh _; omega
  | succ n ih =>
    intro j hn h k v hk hkh hg
    rw [rtValidR, ite_eq_left (show j < hi by omega)] at h
    split at h
    · rename_i hz
      by_cases hk8 : k < j / 8 * 8 + 8
      · have : k / 8 = j / 8 := by omega
        simp only [beq_iff_eq] at hz
        simp only [RTab.get, bitGet_zero (show R.bits.get! (k / 8) = 0 by rw [this]; exact hz)]
          at hg
        cases hg
      · exact ih (j / 8 * 8 + 8) (by omega) h k v (by omega) hkh hg
    · simp only [Bool.and_eq_true] at h
      by_cases hkj : k = j
      · subst hkj
        have h1 := h.1
        rw [hg] at h1
        simp only at h1
        split at h1
        · rename_i w hw
          simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
          obtain ⟨hl, rfl⟩ := h1
          split at hw
          · rename_i hkc; exact ⟨hkc, hw, hl⟩
          · cases hw
        · cases h1
      · exact ih (j + 1) (by omega) h.2 k v (by omega) hkh hg

/-- **The retained table validated in parts** of `s` ids each, covering
its bitmap. -/
theorem rtValid_parts {R : RTab} {P : Prior} {ce s m : Nat} (hs : 0 < s)
    (hm : R.bits.size * 8 ≤ m * s)
    (h : ∀ i, i < m → rtValidR R P ce (min (R.bits.size * 8) ((i + 1) * s)) (i * s) = true) :
    RTValid R P ce := by
  intro k v hg
  by_cases hk : k < R.bits.size * 8
  · have hi : k / s < m := Nat.div_lt_of_lt_mul (show k < s * m by rw [Nat.mul_comm]; omega)
    refine rtValidR_sound _ _ (Nat.le_refl _) (h (k / s) hi) k v ?_ ?_ hg
    · exact Nat.div_mul_le_self k s
    · have := Nat.lt_div_mul_add (a := k) hs
      simp only [Nat.lt_min]
      refine ⟨hk, ?_⟩
      rw [Nat.add_mul, Nat.one_mul]; exact this
  · simp only [RTab.get, bitGet_out (show R.bits.size * 8 ≤ k by omega)] at hg
    cases hg

/-- The store of a finished parse and the serial state the finished
tables are related to. -/
theorem SHolds.ofChunks {st : StateD} {P : Prior} {c : Ctr} (hh : LHolds st P c)
    (S : Array LChunk) {rt : RTab} (hrt : RTValid rt P c.e) :
    SHolds st (LStore.ofChunks S P c rt) := by
  refine ⟨hh.name, hh.level, fun k v hk => ?_⟩
  simp only [rtLk, LStore.ofChunks] at hk
  split at hk
  · rename_i u hu
    simp only [pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    obtain ⟨hkc, hP, hl⟩ := hrt _ _ hu
    exact StateD.expr_of_get (hh.eb k u hkc hP hl)
  · simp [throw, throwThe, MonadExceptOf.throw] at hk

/-! ## The serial state, materialized -/

theorem matExprs_spec {P : Prior} {S : LStore} {c : Ctr} {st : StateD} (hh : LHolds st P c)
    (hs : StoreOK st S.chunks) :
    ∀ (n j : Nat) (t t' : IdTable Expr), c.e - j = n →
    (∀ k, t.get? k = if k < j then st.exprs.get? k else none) →
    matExprs P S c j t = some t' → ∀ k, t'.get? k = st.exprs.get? k := by
  intro n
  induction n with
  | zero =>
    intro j t t' hn ht h k
    rw [matExprs, ite_eq_right (by omega)] at h
    cases h
    rw [ht k]
    split
    · rfl
    · exact (hh.above (by omega)).symm
  | succ n ih =>
    intro j t t' hn ht h
    rw [matExprs, ite_eq_left (by omega)] at h
    have hstep : ∀ (w : Expr), st.exprs.get? j = some w →
        ∀ k, (t.insert j w).get? k = if k < j + 1 then st.exprs.get? k else none := by
      intro w hw k
      rw [IdTable.get?_insert, ht k]
      by_cases hkj : k = j
      · subst hkj; simp [hw]
      · simp only [hkj, ↓reduceIte]
        by_cases hk : k < j
        · simp [hk, show k < j + 1 by omega]
        · simp [hk, show ¬ k < j + 1 by omega]
    split at h
    · rename_i v hv
      split at h
      · rename_i hlz
        split at h
        · rename_i x hx
          obtain ⟨C, hC, hf⟩ := LStore.find_sound hx
          obtain ⟨L, hvC, hl⟩ := hs C hC
          obtain ⟨u, hu1, hu2⟩ := hl _ (LChunk.find_sound hvC hf)
          split at h
          · rename_i w hw
            have hb : tBelow t j = exprBelow st j := by
              funext k
              simp only [tBelow, exprBelow, StateD.expr]
              split
              · rename_i hk; rw [ht k, ite_eq_left hk]; rfl
              · rfl
            rw [hb, ← hh.name, ← hh.level, hu2] at hw
            cases hw
            exact ih (j + 1) _ _ (by omega) (hstep u hu1) h
          · simp at h
        · simp at h
      · rename_i hlz
        exact ih (j + 1) _ _ (by omega)
          (hstep v (hh.eb j v (by omega) hv (by simpa using hlz))) h
    · rename_i hv
      refine ih (j + 1) _ _ (by omega) (fun k => ?_) h
      rw [ht k]
      by_cases hkj : k = j
      · subst hkj
        have := hh.e k
        simp only [show k < c.e by omega, decide_true, hv, Option.isSome_none,
          Bool.and_false] at this
        have hn : st.exprs.get? k = none := by
          cases hk : st.exprs.get? k with
          | none => rfl
          | some _ => rw [hk] at this; simp at this
        simp [hn]
      · by_cases hk : k < j
        · simp [hk, show k < j + 1 by omega]
        · simp [hk, show ¬ k < j + 1 by omega]

theorem matDecl_spec {t : IdTable Expr} {st : StateD}
    (ht : ∀ k, t.get? k = st.exprs.get? k) {d' d e : Declaration} (hd : DRel st d' d)
    (he : matDecl t d' = some e) : e = d := by
  cases d with
  | thmDecl cv w =>
    obtain ⟨vid, hint, rfl, hw⟩ := hd
    simp only [matDecl, phId?, ph, Option.map_eq_some_iff, ht vid, hw] at he
    obtain ⟨v, hv, rfl⟩ := he
    cases hv; rfl
  | _ =>
    subst hd
    simp only [matDecl, Option.some.injEq] at he
    exact he.symm

theorem matDecls_spec {t : IdTable Expr} {st : StateD}
    (ht : ∀ k, t.get? k = st.exprs.get? k) :
    ∀ {ds' : List Declaration} {ds : List Declaration} {r : List Declaration},
    Pw (DRel st) ds' ds → ds'.mapM (matDecl t) = some r → r = ds
  | [], [], r, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; exact h.symm
  | d' :: ds', d :: ds, r, hp, h => by
    rw [List.mapM_cons] at h
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.pure_def, Option.some.injEq] at h
    subst h
    rw [matDecl_spec ht hp.1 he, matDecls_spec ht hp.2 hr']
  | [], _ :: _, _, hp, _ => hp.elim
  | _ :: _, [], _, hp, _ => hp.elim

/-- **The materialized state is the serial state**: it is reached by
the serial parse of the stream so far. -/
theorem materialize_reached {g : LGSt} (hg : LGOK g) (rt : RTab) {st' : StateD}
    (h : materialize g.P (LStore.ofChunks g.S g.P g.c rt) g.c g.ds = some st') :
    Reached st' .empty g.lineNo g.total := by
  obtain ⟨st, hr, hh, hd, hs⟩ := hg
  simp only [materialize] at h
  split at h
  · rename_i t ht
    split at h
    · rename_i ds' hds
      simp only [Option.some.injEq] at h
      subst h
      have hte := matExprs_spec hh (hs.ofChunks g.P g.c rt) _ 0 {} t rfl
        (fun k => by simp [IdTable.get?_empty]) ht
      have hdl : ds'.toList = st.decls.toList := by
        have := congrArg (Option.map Array.toList) hds
        rw [Array.mapM_eq_mapM_toList] at this
        simp only [Option.map_some] at this
        cases hm : g.ds.toList.mapM (matDecl t) with
        | none => rw [hm] at this; simp at this
        | some r =>
          rw [hm] at this
          simp at this
          rw [← this]
          exact matDecls_spec hte hd hm
      refine hr.equiv (StateD.Equiv.symm ⟨fun j => ?_, fun j => ?_, fun j => hte j, ?_⟩)
      · rw [Pages.toTable_get?, hh.n j]
      · rw [Pages.toTable_get?, hh.l j]
      · exact Array.toList_inj.mp hdl
    · simp at h
  · simp at h

end ConLeche.Frontend
