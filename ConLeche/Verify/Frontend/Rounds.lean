module

public import ConLeche.Verify.Frontend.Dense

public section

/-!
# The check of a built line (task #329)

What the lazy check (`ConLeche/Frontend/Lazy.lean`,
`ConLeche/Verify/Frontend/Lazy.lean`) uses of the rounds' check: a
built entry checked against its line without building it is the
line's builder's value (`exprCheck_sound` and its siblings), a name or
level line passing `checkLine` is right at the finished tables
(`checkLine_sound`), and the finished tables after a window keep the
tables before below the window's start when the driver's test says so
(`Pages.keeps_sound`).
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

theorem levelsCheck_sound {lv : Nat → Except String Level} :
    ∀ {us : List Nat} {ls : List Level}, levelsCheck lv us ls = true → us.mapM lv = .ok ls
  | [], [], _ => rfl
  | u :: us, l :: ls, h => by
    simp only [levelsCheck, Bool.and_eq_true, okIs_iff] at h
    simp [List.mapM_cons, h.1, levelsCheck_sound h.2, bind, Except.bind, pure, Except.pure]
  | [], _ :: _, h => by simp [levelsCheck] at h
  | _ :: _, [], h => by simp [levelsCheck] at h

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
       simp [exprOfF, h1, h2, bind, Except.bind, pure, Except.pure, Expr.mkApp]; done)
    | (obtain ⟨h1, h2⟩ := h
       have h3 := levelsCheck_sound h2
       simp only [exprOfF, h1, bind, Except.bind, pure, Except.pure, Expr.mkConst]
       rw [h3])

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
      exact ⟨⟨x, hx⟩, rfl, by simp only [lineDecl, declOf, cutLk_tabs]; rw [hx]⟩
    · simp at h
  | header =>
    simp only [checkLine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, rfl⟩
  | blank =>
    simp only [checkLine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, rfl⟩

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

theorem ByteArray.extract_size_self (b : ByteArray) : b.extract b.size b.size = .empty := by
  ext1; simp [ByteArray.empty, ByteArray.emptyWithCapacity]

end ConLeche.Frontend
