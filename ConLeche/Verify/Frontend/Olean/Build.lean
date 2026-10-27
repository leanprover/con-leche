module

public import ConLeche.Verify.Frontend.Olean.Mark

public section

/-!
# The upward sweep (task #371)

`buildPass` (`ConLeche/Frontend/Olean/Fast.lean`) reads every marked
object with its node function, the objects it leads to taken from the
memo.  Over the marks the downward sweep leaves (`Closed … 0 n`), by
induction on the slot: every marked object below the sweep holds its
specification's value (`Built`), because what it leads to is marked,
lies below it, and so holds its value already (`…Node_congr`).  A node
that does not read is a marked object the specification does not read,
which refutes `A` (`Reach`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The marked object at slot `s`, read as kind `k`, holds its value. -/
@[expose] def ValOK (r : Region) (st : DS) (k : UInt8) (s : Nat) : Prop :=
  (k = kName → nameAt r (8 * s) = some (st.nameV (8 * s))) ∧
  (k = kLevel → levelAt r (8 * s) = some (st.levelV (8 * s))) ∧
  (k = kLevels → levelsAt r (8 * s) = some (st.levelsV (8 * s))) ∧
  (k = kExpr → exprAt r (8 * s) = some (st.exprV (8 * s)))

/-- Every marked object below slot `p` holds its value. -/
@[expose] def Built (r : Region) (m : ByteArray) (st : DS) (p : Nat) : Prop :=
  ∀ s, s < p → ∀ k, IsKind k → marked m k s = true → ValOK r st k s

/-- A kid below the sweep holds its value, read through the memo. -/
theorem kid_val {r : Region} {m : ByteArray} {st : DS} {p n : Nat} (hc : Closed r m 0 n)
    (hb : Built r m st p) (hpn : p < n) {k : UInt8} (hk : IsKind k) (hm : marked m k p = true)
    {k' : UInt8} {c : Nat} (hkid : Kid r k (8 * p) k' c) : ValOK r st k' (c / 8) := by
  have hlt := hkid.lt
  have hmod := hkid.mod
  exact hb (c / 8) (by omega) k' hkid.kind ((hc p (by omega) hpn k hk hm).2 k' c hkid)

theorem eight_div {c : Nat} (h : c % 8 = 0) : 8 * (c / 8) = c := by omega

/-! ## One kind at one slot -/

theorem kid_spec {r : Region} {m : ByteArray} {st : DS} {p n : Nat} (hc : Closed r m 0 n)
    (hb : Built r m st p) (hpn : p < n) {k : UInt8} (hk : IsKind k) (hm : marked m k p = true)
    {k' : UInt8} {c : Nat} (hkid : Kid r k (8 * p) k' c) :
    (k' = kName → nameAt r c = some (st.nameV c)) ∧ (k' = kLevel → levelAt r c = some (st.levelV c)) ∧
    (k' = kLevels → levelsAt r c = some (st.levelsV c)) ∧ (k' = kExpr → exprAt r c = some (st.exprV c)) := by
  have h := kid_val hc hb hpn hk hm hkid
  unfold ValOK at h
  rw [eight_div hkid.mod] at h
  exact h

theorem DS.nameV_set (st : DS) (p c : Nat) (v : Name) :
    (st.setName p v).nameV c = if p = c / 8 ∧ p < st.names.size then v else st.nameV c := by
  simp only [DS.nameV, DS.setName, getD_set!]
theorem DS.levelV_set (st : DS) (p c : Nat) (v : Level) :
    (st.setLevel p v).levelV c = if p = c / 8 ∧ p < st.levels.size then v else st.levelV c := by
  simp only [DS.levelV, DS.setLevel, getD_set!]
theorem DS.levelsV_set (st : DS) (p c : Nat) (v : List Level) :
    (st.setLevels p v).levelsV c = if p = c / 8 ∧ p < st.lists.size then v else st.levelsV c := by
  simp only [DS.levelsV, DS.setLevels, getD_set!]
theorem DS.exprV_set (st : DS) (p c : Nat) (v : Expr) :
    (st.setExpr p v).exprV c = if p = c / 8 ∧ p < st.exprs.size then v else st.exprV c := by
  simp only [DS.exprV, DS.setExpr, getD_set!]

/-- The slot's kinds `ks` are done, and every slot below it. -/
@[expose] def DoneAt (r : Region) (m : ByteArray) (st : DS) (p : Nat) (ks : List UInt8) : Prop :=
  Built r m st p ∧ ∀ k ∈ ks, IsKind k → marked m k p = true → ValOK r st k p

theorem buildName_eq {r : Region} {m : ByteArray} {st : DS} {p n : Nat} (hc0 : Closed r m 0 n)
    (hb : Built r m st p) (hpn : p < n) (hm : marked m kName p = true) :
    buildName r (8 * p) st = nameAt r (8 * p) := by
  have hk : IsKind kName := by unfold IsKind; simp
  rw [nameAt]
  exact nameNode_congr (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).1 rfl).symm)

theorem ValOK_setName {r : Region} {st : DS} {p : Nat} {v : Name} {k : UInt8} {s : Nat}
    (h : k ≠ kName ∨ s ≠ p) : ValOK r (st.setName p v) k s ↔ ValOK r st k s := by
  unfold ValOK
  have e : s ≠ p → (st.setName p v).nameV (8 * s) = st.nameV (8 * s) := by
    intro hsp
    rw [DS.nameV_set]
    have : ¬ p = 8 * s / 8 := by omega
    exact ite_eq_right_iff.mpr (fun h => absurd h.1 this)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · rcases h with h | h
      · exact absurd e' h
      · rw [h1 e', e h]
    · exact h2 e'
    · exact h3 e'
    · exact h4 e'
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · rcases h with h | h
      · exact absurd e' h
      · rw [h1 e', e h]
    · exact h2 e'
    · exact h3 e'
    · exact h4 e'

theorem buildLevel_eq {r : Region} {m : ByteArray} {st : DS} {p n : Nat} (hc0 : Closed r m 0 n)
    (hb : Built r m st p) (hpn : p < n) (hm : marked m kLevel p = true) :
    buildLevel r (8 * p) st = levelAt r (8 * p) := by
  have hk : IsKind kLevel := by unfold IsKind; simp
  rw [levelAt]
  exact levelNode_congr (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).2.1 rfl).symm) (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).1 rfl).symm)

theorem ValOK_setLevel {r : Region} {st : DS} {p : Nat} {v : Level} {k : UInt8} {s : Nat}
    (h : k ≠ kLevel ∨ s ≠ p) : ValOK r (st.setLevel p v) k s ↔ ValOK r st k s := by
  unfold ValOK
  have e : s ≠ p → (st.setLevel p v).levelV (8 * s) = st.levelV (8 * s) := by
    intro hsp
    rw [DS.levelV_set]
    have : ¬ p = 8 * s / 8 := by omega
    exact ite_eq_right_iff.mpr (fun h => absurd h.1 this)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · exact h1 e'
    · rcases h with h | h
      · exact absurd e' h
      · rw [h2 e', e h]
    · exact h3 e'
    · exact h4 e'
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · exact h1 e'
    · rcases h with h | h
      · exact absurd e' h
      · rw [h2 e', e h]
    · exact h3 e'
    · exact h4 e'

theorem buildLevels_eq {r : Region} {m : ByteArray} {st : DS} {p n : Nat} (hc0 : Closed r m 0 n)
    (hb : Built r m st p) (hpn : p < n) (hm : marked m kLevels p = true) :
    buildLevels r (8 * p) st = levelsAt r (8 * p) := by
  have hk : IsKind kLevels := by unfold IsKind; simp
  rw [levelsAt]
  exact levelsNode_congr (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).2.2.1 rfl).symm) (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).2.1 rfl).symm)

theorem ValOK_setLevels {r : Region} {st : DS} {p : Nat} {v : List Level} {k : UInt8} {s : Nat}
    (h : k ≠ kLevels ∨ s ≠ p) : ValOK r (st.setLevels p v) k s ↔ ValOK r st k s := by
  unfold ValOK
  have e : s ≠ p → (st.setLevels p v).levelsV (8 * s) = st.levelsV (8 * s) := by
    intro hsp
    rw [DS.levelsV_set]
    have : ¬ p = 8 * s / 8 := by omega
    exact ite_eq_right_iff.mpr (fun h => absurd h.1 this)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · exact h1 e'
    · exact h2 e'
    · rcases h with h | h
      · exact absurd e' h
      · rw [h3 e', e h]
    · exact h4 e'
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · exact h1 e'
    · exact h2 e'
    · rcases h with h | h
      · exact absurd e' h
      · rw [h3 e', e h]
    · exact h4 e'

theorem buildExpr_eq {r : Region} {m : ByteArray} {st : DS} {p n : Nat} (hc0 : Closed r m 0 n)
    (hb : Built r m st p) (hpn : p < n) (hm : marked m kExpr p = true) :
    buildExpr r (8 * p) st = exprAt r (8 * p) := by
  have hk : IsKind kExpr := by unfold IsKind; simp
  rw [exprAt]
  exact exprNode_congr (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).2.2.2 rfl).symm) (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).1 rfl).symm) (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).2.1 rfl).symm) (fun c hc hkid => ((kid_spec hc0 hb hpn hk hm hkid).2.2.1 rfl).symm)

theorem ValOK_setExpr {r : Region} {st : DS} {p : Nat} {v : Expr} {k : UInt8} {s : Nat}
    (h : k ≠ kExpr ∨ s ≠ p) : ValOK r (st.setExpr p v) k s ↔ ValOK r st k s := by
  unfold ValOK
  have e : s ≠ p → (st.setExpr p v).exprV (8 * s) = st.exprV (8 * s) := by
    intro hsp
    rw [DS.exprV_set]
    have : ¬ p = 8 * s / 8 := by omega
    exact ite_eq_right_iff.mpr (fun h => absurd h.1 this)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · exact h1 e'
    · exact h2 e'
    · exact h3 e'
    · rcases h with h | h
      · exact absurd e' h
      · rw [h4 e', e h]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e' => ?_, fun e' => ?_, fun e' => ?_, fun e' => ?_⟩
    · exact h1 e'
    · exact h2 e'
    · exact h3 e'
    · rcases h with h | h
      · exact absurd e' h
      · rw [h4 e', e h]

theorem buildKind_name_spec {r : Region} {A : Prop} {m : ByteArray} {st : DS} {p n : Nat}
    {ks : List UInt8} (hs : st.Sized n) (hpn : p < n) (hc : Closed r m 0 n) (hr : Reach r A m)
    (hd : DoneAt r m st p ks) :
    ((buildKind r m kName buildName DS.setName p st).2 = false → ¬ A) ∧
    ((buildKind r m kName buildName DS.setName p st).2 = true → (buildKind r m kName buildName DS.setName p st).1.Sized n ∧
      DoneAt r m (buildKind r m kName buildName DS.setName p st).1 p (kName :: ks)) := by
  have hk : IsKind kName := by unfold IsKind; simp
  unfold buildKind
  by_cases hm : marked m kName p = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), buildName_eq hc hd.1 hpn hm]
    cases hv : nameAt r (8 * p) with
    | none =>
      refine ⟨fun _ hA => ?_, fun h => by cases h⟩
      have := (hr kName p hk hm hA).1 rfl
      rw [hv] at this; cases this
    | some v =>
      refine ⟨(fun h => by cases h), fun _ => ⟨DS.setName_sized hs p v, ?_, ?_⟩⟩
      · intro s hsp k' hk' hmk
        exact (ValOK_setName (Or.inr (by omega))).mpr (hd.1 s hsp k' hk' hmk)
      · intro k' hk'm hk' hmk
        by_cases ek : k' = kName
        · subst ek
          exact ⟨fun _ => by rw [hv, DS.nameV_set, ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, by rw [hs.names]; omega⟩ h)],
            fun e => absurd e (by decide),
            fun e => absurd e (by decide),
            fun e => absurd e (by decide)⟩
        · have hk'm' : k' ∈ ks := by
            simp only [List.mem_cons] at hk'm
            exact hk'm.resolve_left ek
          exact (ValOK_setName (Or.inl ek)).mpr (hd.2 k' hk'm' hk' hmk)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    refine ⟨(fun h => by cases h), fun _ => ⟨hs, hd.1, ?_⟩⟩
    intro k' hk'm hk' hmk
    by_cases ek : k' = kName
    · subst ek; exact absurd hmk hm
    · simp only [List.mem_cons] at hk'm
      exact hd.2 k' (hk'm.resolve_left ek) hk' hmk

theorem buildKind_level_spec {r : Region} {A : Prop} {m : ByteArray} {st : DS} {p n : Nat}
    {ks : List UInt8} (hs : st.Sized n) (hpn : p < n) (hc : Closed r m 0 n) (hr : Reach r A m)
    (hd : DoneAt r m st p ks) :
    ((buildKind r m kLevel buildLevel DS.setLevel p st).2 = false → ¬ A) ∧
    ((buildKind r m kLevel buildLevel DS.setLevel p st).2 = true → (buildKind r m kLevel buildLevel DS.setLevel p st).1.Sized n ∧
      DoneAt r m (buildKind r m kLevel buildLevel DS.setLevel p st).1 p (kLevel :: ks)) := by
  have hk : IsKind kLevel := by unfold IsKind; simp
  unfold buildKind
  by_cases hm : marked m kLevel p = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), buildLevel_eq hc hd.1 hpn hm]
    cases hv : levelAt r (8 * p) with
    | none =>
      refine ⟨fun _ hA => ?_, fun h => by cases h⟩
      have := (hr kLevel p hk hm hA).2.1 rfl
      rw [hv] at this; cases this
    | some v =>
      refine ⟨(fun h => by cases h), fun _ => ⟨DS.setLevel_sized hs p v, ?_, ?_⟩⟩
      · intro s hsp k' hk' hmk
        exact (ValOK_setLevel (Or.inr (by omega))).mpr (hd.1 s hsp k' hk' hmk)
      · intro k' hk'm hk' hmk
        by_cases ek : k' = kLevel
        · subst ek
          exact ⟨fun e => absurd e (by decide),
            fun _ => by rw [hv, DS.levelV_set, ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, by rw [hs.levels]; omega⟩ h)],
            fun e => absurd e (by decide),
            fun e => absurd e (by decide)⟩
        · have hk'm' : k' ∈ ks := by
            simp only [List.mem_cons] at hk'm
            exact hk'm.resolve_left ek
          exact (ValOK_setLevel (Or.inl ek)).mpr (hd.2 k' hk'm' hk' hmk)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    refine ⟨(fun h => by cases h), fun _ => ⟨hs, hd.1, ?_⟩⟩
    intro k' hk'm hk' hmk
    by_cases ek : k' = kLevel
    · subst ek; exact absurd hmk hm
    · simp only [List.mem_cons] at hk'm
      exact hd.2 k' (hk'm.resolve_left ek) hk' hmk

theorem buildKind_levels_spec {r : Region} {A : Prop} {m : ByteArray} {st : DS} {p n : Nat}
    {ks : List UInt8} (hs : st.Sized n) (hpn : p < n) (hc : Closed r m 0 n) (hr : Reach r A m)
    (hd : DoneAt r m st p ks) :
    ((buildKind r m kLevels buildLevels DS.setLevels p st).2 = false → ¬ A) ∧
    ((buildKind r m kLevels buildLevels DS.setLevels p st).2 = true → (buildKind r m kLevels buildLevels DS.setLevels p st).1.Sized n ∧
      DoneAt r m (buildKind r m kLevels buildLevels DS.setLevels p st).1 p (kLevels :: ks)) := by
  have hk : IsKind kLevels := by unfold IsKind; simp
  unfold buildKind
  by_cases hm : marked m kLevels p = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), buildLevels_eq hc hd.1 hpn hm]
    cases hv : levelsAt r (8 * p) with
    | none =>
      refine ⟨fun _ hA => ?_, fun h => by cases h⟩
      have := (hr kLevels p hk hm hA).2.2.1 rfl
      rw [hv] at this; cases this
    | some v =>
      refine ⟨(fun h => by cases h), fun _ => ⟨DS.setLevels_sized hs p v, ?_, ?_⟩⟩
      · intro s hsp k' hk' hmk
        exact (ValOK_setLevels (Or.inr (by omega))).mpr (hd.1 s hsp k' hk' hmk)
      · intro k' hk'm hk' hmk
        by_cases ek : k' = kLevels
        · subst ek
          exact ⟨fun e => absurd e (by decide),
            fun e => absurd e (by decide),
            fun _ => by rw [hv, DS.levelsV_set, ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, by rw [hs.lists]; omega⟩ h)],
            fun e => absurd e (by decide)⟩
        · have hk'm' : k' ∈ ks := by
            simp only [List.mem_cons] at hk'm
            exact hk'm.resolve_left ek
          exact (ValOK_setLevels (Or.inl ek)).mpr (hd.2 k' hk'm' hk' hmk)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    refine ⟨(fun h => by cases h), fun _ => ⟨hs, hd.1, ?_⟩⟩
    intro k' hk'm hk' hmk
    by_cases ek : k' = kLevels
    · subst ek; exact absurd hmk hm
    · simp only [List.mem_cons] at hk'm
      exact hd.2 k' (hk'm.resolve_left ek) hk' hmk

theorem buildKind_expr_spec {r : Region} {A : Prop} {m : ByteArray} {st : DS} {p n : Nat}
    {ks : List UInt8} (hs : st.Sized n) (hpn : p < n) (hc : Closed r m 0 n) (hr : Reach r A m)
    (hd : DoneAt r m st p ks) :
    ((buildKind r m kExpr buildExpr DS.setExpr p st).2 = false → ¬ A) ∧
    ((buildKind r m kExpr buildExpr DS.setExpr p st).2 = true → (buildKind r m kExpr buildExpr DS.setExpr p st).1.Sized n ∧
      DoneAt r m (buildKind r m kExpr buildExpr DS.setExpr p st).1 p (kExpr :: ks)) := by
  have hk : IsKind kExpr := by unfold IsKind; simp
  unfold buildKind
  by_cases hm : marked m kExpr p = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm), buildExpr_eq hc hd.1 hpn hm]
    cases hv : exprAt r (8 * p) with
    | none =>
      refine ⟨fun _ hA => ?_, fun h => by cases h⟩
      have := (hr kExpr p hk hm hA).2.2.2 rfl
      rw [hv] at this; cases this
    | some v =>
      refine ⟨(fun h => by cases h), fun _ => ⟨DS.setExpr_sized hs p v, ?_, ?_⟩⟩
      · intro s hsp k' hk' hmk
        exact (ValOK_setExpr (Or.inr (by omega))).mpr (hd.1 s hsp k' hk' hmk)
      · intro k' hk'm hk' hmk
        by_cases ek : k' = kExpr
        · subst ek
          exact ⟨fun e => absurd e (by decide),
            fun e => absurd e (by decide),
            fun e => absurd e (by decide),
            fun _ => by rw [hv, DS.exprV_set, ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, by rw [hs.exprs]; omega⟩ h)]⟩
        · have hk'm' : k' ∈ ks := by
            simp only [List.mem_cons] at hk'm
            exact hk'm.resolve_left ek
          exact (ValOK_setExpr (Or.inl ek)).mpr (hd.2 k' hk'm' hk' hmk)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    refine ⟨(fun h => by cases h), fun _ => ⟨hs, hd.1, ?_⟩⟩
    intro k' hk'm hk' hmk
    by_cases ek : k' = kExpr
    · subst ek; exact absurd hmk hm
    · simp only [List.mem_cons] at hk'm
      exact hd.2 k' (hk'm.resolve_left ek) hk' hmk

/-! ## One slot, and the sweep -/

/-- **The upward sweep**: every marked object ends up holding its
value, or the sweep fails and `A` does not hold. -/
theorem buildPass_spec {r : Region} {A : Prop} {m : ByteArray} {n : Nat}
    (hc : Closed r m 0 n) (hr : Reach r A m) :
    ∀ (p : Nat) (st : DS), st.Sized n → Built r m st p →
    match buildPass r m n st p with
    | none => ¬ A
    | some st' => st'.Sized n ∧ Built r m st' n := by
  intro p
  induction h : n - p generalizing p with
  | zero =>
    intro st hs hb
    unfold buildPass
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact ⟨hs, fun s hsn => hb s (by omega)⟩
  | succ k ih =>
    intro st hs hb
    unfold buildPass
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    by_cases hnz : (marksAt m p != 0) = true
    · simp only [hnz, ↓reduceIte]
      have hpn : p < n := by omega
      have hd0 : DoneAt r m st p [] := ⟨hb, fun _ h => absurd h (by simp)⟩
      obtain ⟨f1, h1⟩ := buildKind_name_spec hs hpn hc hr hd0
      cases e1 : buildKind r m kName buildName DS.setName p st with
      | mk st1 ok1 =>
      simp only [e1] at f1 h1
      cases ok1 with
      | false => exact f1 rfl
      | true =>
      obtain ⟨hs1, hd1⟩ := h1 rfl
      obtain ⟨f2, h2⟩ := buildKind_level_spec hs1 hpn hc hr hd1
      cases e2 : buildKind r m kLevel buildLevel DS.setLevel p st1 with
      | mk st2 ok2 =>
      simp only [e2] at f2 h2
      cases ok2 with
      | false => simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact f2 rfl
      | true =>
      obtain ⟨hs2, hd2⟩ := h2 rfl
      obtain ⟨f3, h3⟩ := buildKind_levels_spec hs2 hpn hc hr hd2
      cases e3 : buildKind r m kLevels buildLevels DS.setLevels p st2 with
      | mk st3 ok3 =>
      simp only [e3] at f3 h3
      cases ok3 with
      | false => simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact f3 rfl
      | true =>
      obtain ⟨hs3, hd3⟩ := h3 rfl
      obtain ⟨f4, h4⟩ := buildKind_expr_spec hs3 hpn hc hr hd3
      cases e4 : buildKind r m kExpr buildExpr DS.setExpr p st3 with
      | mk st4 ok4 =>
      simp only [e4] at f4 h4
      cases ok4 with
      | false => simp only [Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; exact f4 rfl
      | true =>
      obtain ⟨hs4, hd4⟩ := h4 rfl
      simp only [Bool.and_self, ↓reduceIte]
      have hb4 : Built r m st4 (p + 1) := by
        intro s hsp k' hk hmk
        by_cases e : s = p
        · subst e
          exact hd4.2 k' (by unfold IsKind at hk; rcases hk with rfl | rfl | rfl | rfl <;> simp)
            hk hmk
        · exact hd4.1 s (by omega) k' hk hmk
      exact ih (p + 1) (by omega) st4 hs4 hb4
    · simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      have hb' : Built r m st (p + 1) := by
        intro s hsp k' hk hmk
        by_cases e : s = p
        · subst e; rw [marked_of_marksAt_zero hnz k'] at hmk; cases hmk
        · exact hb s (by omega) k' hk hmk
      exact ih (p + 1) (by omega) st hs hb'

end ConLeche.Frontend.Olean
