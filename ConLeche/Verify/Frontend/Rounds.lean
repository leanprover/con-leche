module

public import ConLeche.Frontend.Rounds
public import ConLeche.Verify.Frontend.Dense

public section

/-!
# The rounds parse is the serial parse (task #329)

What the driver of the rounds parse (`ConLeche/Driver/ParParse.lean`)
carries between windows is `GOK g`: some state the serial parse
reaches after the lines before (`Reached`) holds the finished tables
`g.P` cut at the counters `g.c`, with the records `g.ds`.

* `checkLine_sound`/`checkList_sound`: a list of lines passing the
  check at the finished tables is right at them line by line
  (`AllOK`), so the characterisation (`applyList_of_allOK`,
  `ConLeche/Verify/Frontend/Dense.lean`) applies; `checkFlat_sound`
  carries this to the flat chunk the check reads.
* `GOK.keep`: the tables after a window agree with the tables before
  below the window's start (`Prior.keeps`, tested by the driver).
* `GOK.chunk`: a chunk that passes the check is one more serial step
  (`chunkStep`), the counters and records the check returns being the
  serial parse's.
* `GOK.finish` and `GOK.reached`: the end of the stream, and the state
  a window that falls back continues the serial parse from
  (`Prior.toState`).
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The check is sound -/

theorem okIs_iff [BEq α] [LawfulBEq α] {e : Except String α} {v : α} :
    okIs e v = true ↔ e = .ok v := by
  cases e <;> simp [okIs]

theorem nameCheck_sound {nm : Nat → Except String Name} {lv : Nat → Except String Level}
    {ex : Nat → Except String Expr} {r : NameRec} {v : Name} (h : nameCheck nm r v = true) :
    nameOfF nm lv ex r = .ok v := by
  cases r <;> cases v <;> simp only [nameCheck, Bool.and_eq_true, okIs_iff, beq_iff_eq,
    Bool.false_eq_true] at h
  all_goals
    obtain ⟨h1, rfl⟩ := h
    simp [nameOfF, h1, bind, Except.bind, pure, Except.pure]

theorem levelCheck_sound {nm : Nat → Except String Name} {lv : Nat → Except String Level}
    {ex : Nat → Except String Expr} {r : LevelRec} {v : Level}
    (h : levelCheck nm lv r v = true) : levelOfF nm lv ex r = .ok v := by
  cases r <;> cases v <;> simp only [levelCheck, Bool.and_eq_true, okIs_iff,
    Bool.false_eq_true] at h
  all_goals first
    | (simp [levelOfF, h, bind, Except.bind, pure, Except.pure])
    | (obtain ⟨h1, h2⟩ := h; simp [levelOfF, h1, h2, bind, Except.bind, pure, Except.pure])

theorem exprCheck_sound {nm : Nat → Except String Name} {lv : Nat → Except String Level}
    {ex : Nat → Except String Expr} {r : ExprRec} {v : Expr}
    (h : exprCheck nm lv ex r v = true) : exprOfF nm lv ex r = .ok v := by
  cases r <;> cases v <;> simp only [exprCheck, Bool.and_eq_true, okIs_iff, beq_iff_eq] at h
  all_goals first
    | exact h
    | (obtain ⟨⟨h1, h2⟩, h3⟩ := h
       simp only [Except.map] at h3
       split at h3
       · simp at h3
       · rename_i w hw
         simp only [Except.ok.injEq] at h3; subst h3
         simp [exprOfF, h1, h2, hw, bind, Except.bind, pure, Except.pure,
           Expr.mkLam, Expr.mkForallE])
    | (obtain ⟨⟨h1, rfl⟩, h3⟩ := h
       simp [exprOfF, h1, h3, bind, Except.bind, pure, Except.pure, Expr.mkProj])
    | (obtain ⟨⟨h1, h2⟩, h3⟩ := h
       simp [exprOfF, h1, h2, h3, bind, Except.bind, pure, Except.pure, Expr.mkLetE])
    | (obtain ⟨h1, h2⟩ := h
       simp [exprOfF, h1, h2, bind, Except.bind, pure, Except.pure, Expr.mkApp])

theorem Pages.noneIn_sound [Sent α] {P : Pages α} {lo hi : Nat} (h : P.noneIn lo hi = true) :
    ∀ j, lo ≤ j → j < hi → P.get j = none := by
  intro j h1 h2
  obtain ⟨d, rfl⟩ : ∃ d, j = lo + d := ⟨j - lo, by omega⟩
  induction d generalizing lo with
  | zero =>
    rw [Pages.noneIn, ite_eq_left (by omega)] at h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    exact h.1
  | succ d ih =>
    rw [Pages.noneIn, ite_eq_left (by omega)] at h
    simp only [Bool.and_eq_true] at h
    have := ih h.2 (by omega) (by omega)
    rwa [show lo + 1 + d = lo + (d + 1) by omega] at this

theorem nameOf_eq (L : Lk String) (r : NameRec) : nameOf L r = nameOfF L.name L.level L.expr r :=
  rfl

/-- **One line passing the check is right** at the finished tables,
and the check's counters and record are the line's. -/
theorem checkLine_sound {P : Prior} {c c' : Ctr} {r : LineRec} {o : Option Declaration}
    (h : checkLine P c r = some (c', o)) :
    LineOK P.tabs c r ∧ c' = c.step r ∧ o = lineDecl P.tabs c r := by
  cases r with
  | name i x =>
    simp only [checkLine] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      split at h
      · rename_i v hv
        split at h
        · rename_i hx
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨hc.1, Pages.noneIn_sound hc.2, v, hv, nameCheck_sound hx⟩, rfl, rfl⟩
        · simp at h
      · simp at h
    · simp at h
  | level i x =>
    simp only [checkLine] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      split at h
      · rename_i v hv
        split at h
        · rename_i hx
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨hc.1, Pages.noneIn_sound hc.2, v, hv, levelCheck_sound hx⟩, rfl, rfl⟩
        · simp at h
      · simp at h
    · simp at h
  | expr i x =>
    simp only [checkLine] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      split at h
      · rename_i v hv
        split at h
        · rename_i hx
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨hc.1, Pages.noneIn_sound hc.2, v, hv, exprCheck_sound hx⟩, rfl, rfl⟩
        · simp at h
      · simp at h
    · simp at h
  | decl d =>
    simp only [checkLine] at h
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨x, hx⟩, rfl, by simp [lineDecl, declOf, hx]⟩
    · simp at h
  | header =>
    simp only [checkLine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, rfl⟩
  | blank =>
    simp only [checkLine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, rfl⟩

theorem pushOpt_eq (acc : Array Declaration) (o : Option Declaration) :
    pushOpt acc o = (match o with | some x => acc.push x | none => acc) := by
  cases o <;> rfl

/-- **A list passing the check is right** at the finished tables, line
by line; the check's counters and records are the serial ones. -/
theorem checkList_sound {P : Prior} :
    ∀ {c : Ctr} {rs : List LineRec} {acc : Array Declaration} {c' : Ctr}
      {acc' : Array Declaration},
    checkList P c rs acc = some (c', acc') →
    AllOK P.tabs c rs ∧ c.stepAll rs = c' ∧ declsAlong P.tabs c rs acc = acc' := by
  intro c rs
  induction rs generalizing c with
  | nil =>
    intro acc c' acc' h
    simp only [checkList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, rfl⟩
  | cons r rs ih =>
    intro acc c' acc' h
    simp only [checkList] at h
    split at h
    · rename_i c1 o h1
      obtain ⟨hl, rfl, rfl⟩ := checkLine_sound h1
      obtain ⟨ha, hc, hd⟩ := ih h
      refine ⟨⟨hl, ha⟩, hc, ?_⟩
      rw [← hd]; simp only [declsAlong]; cases lineDecl P.tabs c r <;> rfl
    · simp at h

theorem declsAlong_acc (T : Tabs) :
    ∀ (c : Ctr) (rs : List LineRec) (acc : Array Declaration),
    declsAlong T c rs acc = acc ++ declsAlong T c rs #[] := by
  intro c rs
  induction rs generalizing c with
  | nil => intro acc; simp [declsAlong]
  | cons r rs ih =>
    intro acc
    simp only [declsAlong]
    cases lineDecl T c r with
    | none => exact ih _ acc
    | some x => rw [ih _ (acc.push x), ih _ (#[].push x)]; simp

/-! ## The flat check is the check -/

theorem checkFlatGoU_eq (P : Prior) (d : ByteArray) (hd : d.size < USize.size)
    (L : List LineRec) :
    ∀ (c : Ctr) (acc : Array Declaration) (p : USize) (rest : List UInt8),
    d.data.toList.drop p.toNat = Flat.encElems Flat.encLine L ++ rest →
    checkFlatGoU P d p L.length c acc = checkList P c L acc := by
  induction L with
  | nil => intro c acc p rest _; rfl
  | cons r L ih =>
    intro c acc p rest h
    simp only [Flat.encElems, List.append_assoc] at h
    obtain ⟨q, e, hq⟩ := Flat.withLineU_spec r d hd p _ h
      (fun r q => match checkLine P c r with
        | some (c', o) => checkFlatGoU P d q L.length c' (pushOpt acc o)
        | none => none)
    have h' := Flat.drop_after h
    rw [← hq] at h'
    rw [List.length_cons, checkFlatGoU]
    refine e.trans ?_
    simp only [checkList]
    cases checkLine P c r with
    | none => rfl
    | some p => obtain ⟨c', o⟩ := p; exact ih _ _ q rest h'

/-- **The flat check is the check of the lines the chunk holds.** -/
theorem checkFlat_sound {P : Prior} {fc : FlatChunk} {sc : ScannedChunk} (h : fc.Encodes sc)
    {c : Ctr} {r : Ctr × Array Declaration} (hc : checkFlat P fc c = some r) :
    checkList P c sc.recs.toList #[] = some r := by
  obtain ⟨hd, hcount, _⟩ := h
  simp only [checkFlat] at hc
  split at hc
  · rename_i hs
    rw [hcount, ← Array.length_toList,
      checkFlatGoU_eq P fc.data hs _ c #[] 0 [] (by simp [hd])] at hc
    exact hc
  · simp at hc

/-! ## The finished tables -/

theorem Pages.get_eq [Sent α] (P : Pages α) (j : Nat) :
    P.get j = (match (P.pages[j / 4096]?.bind fun pg => pg[j % 4096]?) with
      | some v => if Sent.isPend v then none else some v
      | none => none) := by
  have h1 : j >>> 12 = j / 4096 := by rw [Nat.shiftRight_eq_div_pow]
  have h2 : j &&& 4095 = j % 4096 := by
    have := Nat.and_two_pow_sub_one_eq_mod j 12; simpa using this
  simp only [Pages.get, h1, h2]
  by_cases hp : j / 4096 < P.pages.size
  · simp [hp]; rfl
  · simp [hp]

theorem Pages.setFrom_get [Sent α] (P : Pages α) (p0 : Nat) (news : Array (Array α))
    (hp : p0 ≤ P.pages.size) {j : Nat} (hj : j < p0 * 4096) :
    (P.setFrom p0 news).get j = P.get j := by
  have hjp : j / 4096 < p0 := by omega
  rw [Pages.get_eq, Pages.get_eq, Pages.setFrom]
  have : (P.pages.extract 0 p0 ++ news)[j / 4096]? = P.pages[j / 4096]? := by
    rw [Array.getElem?_append_left (by simp; omega)]
    simp [Array.getElem?_extract]; omega
  rw [this]

theorem Pages.keepsGo_sound [BEq α] [LawfulBEq α] [Sent α] {P P' : Pages α} {j b : Nat}
    (h : Pages.keepsGo P P' j b = true) : ∀ k, j ≤ k → k < b → P'.get k = P.get k := by
  intro k h1 h2
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  induction d generalizing j with
  | zero =>
    rw [Pages.keepsGo, ite_eq_left (by omega)] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  | succ d ih =>
    rw [Pages.keepsGo, ite_eq_left (by omega)] at h
    simp only [Bool.and_eq_true] at h
    have := ih h.2 (by omega) (by omega)
    rwa [show j + 1 + d = j + (d + 1) by omega] at this

/-- **The tables after a window keep the tables before** below the
window's start, when the driver's test says so. -/
theorem Pages.keeps_sound [BEq α] [LawfulBEq α] [Sent α] {P : Pages α}
    {news : Array (Array α)} {b : Nat} (h : P.keeps news b = true) :
    ∀ j, j < b → (P.setFrom (b / 4096) news).get j = P.get j := by
  simp only [Pages.keeps, Bool.and_eq_true, decide_eq_true_eq] at h
  intro j hj
  by_cases hlo : j < b / 4096 * 4096
  · exact Pages.setFrom_get P _ news h.1 hlo
  · exact Pages.keepsGo_sound h.2 j (by omega) hj

theorem IdTable.get?_empty (j : Nat) : ({} : IdTable α).get? j = none := by
  simp [IdTable.get?]

theorem Pages.toTable_get? [Sent α] (P : Pages α) (n j : Nat) :
    (P.toTable n).get? j = if j < n then P.get j else none := by
  have key : ∀ (m i : Nat) (t : IdTable α), i + m = n →
      (∀ k, t.get? k = if k < i then P.get k else none) →
      ∀ k, (Pages.toTable.go P n i t).get? k = if k < n then P.get k else none := by
    intro m
    induction m with
    | zero =>
      intro i t hin ht k
      unfold Pages.toTable.go
      rw [ite_eq_right (by omega), ht k, show i = n by omega]
    | succ m ih =>
      intro i t hin ht k
      unfold Pages.toTable.go
      rw [ite_eq_left (by omega)]
      apply ih (i + 1) _ (by omega)
      intro k'
      split
      · rename_i x hx
        rw [IdTable.get?_insert, ht k']
        by_cases hk : k' = i
        · subst hk; simp [hx]
        · simp only [hk, ↓reduceIte]
          by_cases h1 : k' < i
          · simp [h1, show k' < i + 1 by omega]
          · simp [h1, show ¬ k' < i + 1 by omega]
      · rename_i hx
        rw [ht k']
        by_cases hk : k' = i
        · subst hk; simp [hx]
        · by_cases h1 : k' < i
          · simp [h1, show k' < i + 1 by omega]
          · simp [h1, show ¬ k' < i + 1 by omega]
  exact key n 0 {} (by omega) (fun k => by simp [IdTable.get?_empty]) j

theorem Prior.toState_holds (P : Prior) (c : Ctr) (ds : Array Declaration) :
    Holds (P.toState c ds) P.tabs c :=
  ⟨fun j => Pages.toTable_get? P.n c.n j, fun j => Pages.toTable_get? P.l c.l j,
   fun j => Pages.toTable_get? P.e c.e j⟩

/-! ## The invariant between windows -/

/-- **The rounds parse's invariant**: some state the serial parse
reaches after the lines so far, with nothing carried, holds the
finished tables cut at the counters, with the records so far. -/
def GOK (g : GSt) : Prop :=
  ∃ st, Reached st .empty g.lineNo g.total ∧ Holds st g.P.tabs g.c ∧ st.decls = g.ds

theorem GOK.init : GOK GSt.init := by
  refine ⟨.init, Reached.init, ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩, rfl⟩
  · simp only [StateD.init, IdTable.get?_singleton, GSt.init, Prior.init, Prior.tabs,
      Pages.get_eq]
    rcases j with _ | j
    · simp [Sent.isPend]
    · simp
  · simp only [StateD.init, IdTable.get?_singleton, GSt.init, Prior.init, Prior.tabs,
      Pages.get_eq]
    rcases j with _ | j
    · simp [Sent.isPend]
    · simp
  · simp [StateD.init, IdTable.get?_empty, GSt.init]

/-- The state a window that falls back continues the serial parse
from. -/
theorem GOK.reached {g : GSt} (h : GOK g) :
    Reached (g.P.toState g.c g.ds) .empty g.lineNo g.total := by
  obtain ⟨st, hr, hh, hd⟩ := h
  exact hr.equiv (Holds.equiv hh (Prior.toState_holds g.P g.c g.ds) (by rw [hd]; rfl))

/-- The end of the stream: the records so far are the parse's. -/
theorem GOK.finish {g : GSt} (h : GOK g) : ∃ cs, parseChunks cs = .ok ⟨g.ds⟩ := by
  obtain ⟨st, hr, _, hd⟩ := h
  obtain ⟨cs, hcs⟩ := hr.finish
  refine ⟨cs, ?_⟩
  rw [hcs, chunkFinish, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl)]
  simp [ParseResultD.ofState, hd]

/-- **The tables after a window**, when they keep the tables before. -/
theorem GOK.keep {g : GSt} (h : GOK g) {nn nl ne}
    (hk : g.P.keeps g.c nn nl ne = true) : GOK { g with P := g.P.setFrom g.c nn nl ne } := by
  obtain ⟨st, hr, hh, hd⟩ := h
  simp only [Prior.keeps, Bool.and_eq_true] at hk
  obtain ⟨⟨hn, hl⟩, he⟩ := hk
  refine ⟨st, hr, ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩, hd⟩
  · rw [hh.n j]; split
    · exact (Pages.keeps_sound hn j (by assumption)).symm
    · rfl
  · rw [hh.l j]; split
    · exact (Pages.keeps_sound hl j (by assumption)).symm
    · rfl
  · rw [hh.e j]; split
    · exact (Pages.keeps_sound he j (by assumption)).symm
    · rfl

theorem ByteArray.extract_size_self (b : ByteArray) : b.extract b.size b.size = .empty := by
  ext1; simp [ByteArray.empty, ByteArray.emptyWithCapacity]

/-- **A chunk that passes the check is one more serial step.** -/
theorem GOK.chunk {g : GSt} (h : GOK g) {b : ByteArray} {fc : FlatChunk}
    (henc : fc.Encodes (scanChunk b)) (hfit : chunkFits b fc g.total = true)
    {c' : Ctr} {ds' : Array Declaration} (hc : checkFlat g.P fc g.c = some (c', ds')) :
    GOK { g with c := c', ds := g.ds ++ ds', lineNo := g.lineNo + fc.count,
                 total := g.total + b.size } := by
  obtain ⟨st, hr, hh, hd⟩ := h
  have hl := checkFlat_sound henc hc
  obtain ⟨hok, hstep, hdecl⟩ := checkList_sound hl
  obtain ⟨st', happ, hh', hd'⟩ :=
    applyList_of_allOK g.P.tabs g.c (scanChunk b).recs.toList st g.lineNo hok hh
  simp only [chunkFits] at hfit
  split at hfit
  · rename_i i hstop
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
    obtain ⟨hi, hsz⟩ := hfit
    have hs : chunkStep st .empty g.lineNo g.total b =
        .ok (st', .empty, g.lineNo + fc.count, g.total + b.size) := by
      rw [← chunkStepF_of_encodes _ _ _ _ _ _ henc]
      have hcount : fc.count = (scanChunk b).recs.toList.length := by
        rw [henc.2.1]; simp
      rw [chunkStepF, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl),
        ite_eq_right (show ¬ (g.total + b.size ≥ USize.size) by omega)]
      rw [applyFlat_eq _ _ _ henc, applyScanned, applyRecs_eq, List.drop_zero, happ]
      rw [← henc.2.2, hstop]
      simp only [hcount, hi, ByteArray.extract_size_self]
    refine ⟨st', hr.step hs, ?_, ?_⟩
    · rw [← hstep]; exact hh'
    · rw [hd', hd, declsAlong_acc, hdecl]
  · simp at hfit

end ConLeche.Frontend
