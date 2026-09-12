module

public import ConLeche.Frontend.Scan.Naive
import ConLeche.Frontend.Scan.Equiv
import ConLeche.Frontend.Scan.Equiv.Scalars

public section

/-!
# A line is read inside its line (task #290)

The naive recogniser (`ConLeche/Frontend/Scan/Naive.lean`) reads one
record off the front of the whole remaining input.  This module proves
the one property of it that a theorem about a FILE needs: **no scanner
of the dialect steps over a newline.**  Stated as `LineLocal`: on an
input `l ++ 10 :: x` whose `l` holds no newline, whether the scanner
succeeds, what it returns and where it stops are the same for every
`x`, and it stops inside `l` or at the newline.  Every scanner of the
naive reference is `LineLocal`, by the same induction the suffix
lemmas of task #261 are proved by, and the line itself
(`naiveLine_local`) then reads `l ++ 10 :: x` as one record ending at
that newline — or fails inside `l` — whatever `x` is.

Two consequences carry the file-level theorem: a line the recogniser
returns with a `some rest` is exactly the input up to its first
newline (`naiveLine_some`), and a line it returns with `none` — the
chunked reader's "incomplete tail" — is an input without a newline
(`naiveLine_none`).  The chunk-independence theorem
(`ConLeche/Verify/Frontend/Chunks.lean`) uses the full independence
of `x`.

The two scanners that used to look past a newline — the `meta`
header's bracket skip, and a string body's escape pair — were closed
at task #290 (`naiveSkipBraced` stops at a newline, `naiveStrBody`
refuses a control byte after a backslash), and the escape decoder is
handed the string body alone, so nothing here depends on it.
-/

namespace ConLeche.Frontend

/-! ## The predicate -/

/-- On `l ++ 10 :: x`, the scanner stops at `r ++ 10 :: x` with the same
verdict for every `x`. -/
def LocalAt (f : List UInt8 → NRes α) (l r : List UInt8) : Prop :=
  (∃ v, ∀ x, f (l ++ 10 :: x) = .ok v (r ++ 10 :: x)) ∨
  (∃ t, ∀ x, f (l ++ 10 :: x) = .err t (r ++ 10 :: x))

/-- A scanner reads at most up to the first newline. -/
def LineLocal (f : List UInt8 → NRes α) : Prop :=
  ∀ l : List UInt8, 10 ∉ l → ∃ r : List UInt8, r <:+ l ∧ LocalAt f l r

/-- A `LineLocal` scanner stays so under `map`. -/
theorem LineLocal.map {f : List UInt8 → NRes α} (hf : LineLocal f) (g : α → β) :
    LineLocal (fun l => (f l).map g) := by
  intro l hl
  obtain ⟨r, hr, h⟩ := hf l hl
  refine ⟨r, hr, ?_⟩
  rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
  · exact .inl ⟨g v, fun x => by simp only [hv x, NRes.map]⟩
  · exact .inr ⟨t, fun x => by simp only [ht x, NRes.map]⟩

/-! ## Newline facts about lists -/

theorem not_mem_of_suffix {l r : List UInt8} (hr : r <:+ l) (hl : 10 ∉ l) : 10 ∉ r :=
  fun h => hl (hr.subset h)

theorem not_mem_cons_tail {c : UInt8} {l : List UInt8} (h : 10 ∉ c :: l) : 10 ∉ l :=
  fun h' => h (List.mem_cons_of_mem _ h')

theorem cons_ne_nl {c : UInt8} {l : List UInt8} (h : 10 ∉ c :: l) : c ≠ 10 :=
  fun h' => h (h' ▸ List.mem_cons_self ..)

theorem takeWhile_append_nl (p : UInt8 → Bool) (hp : p 10 = false) (l x : List UInt8) :
    (l ++ 10 :: x).takeWhile p = l.takeWhile p := by
  induction l with
  | nil => simp [hp]
  | cons c l ih => simp only [List.cons_append, List.takeWhile_cons]; split <;> simp [ih]

theorem dropWhile_append_nl (p : UInt8 → Bool) (hp : p 10 = false) (l x : List UInt8) :
    (l ++ 10 :: x).dropWhile p = l.dropWhile p ++ 10 :: x := by
  induction l with
  | nil => simp [hp]
  | cons c l ih => simp only [List.cons_append, List.dropWhile_cons]; split <;> simp [ih]

theorem isDigit_nl : isDigit 10 = false := by decide
theorem isWs_nl : isWs 10 = false := by decide

/-- Splitting a list at its first newline. -/
theorem split_first_nl {l : List UInt8} (h : 10 ∈ l) :
    ∃ pre x, l = pre ++ 10 :: x ∧ 10 ∉ pre := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons c l ih =>
    by_cases hc : c = 10
    · exact ⟨[], l, by rw [hc]; rfl, List.not_mem_nil⟩
    · have : 10 ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hc
        · exact h
      obtain ⟨pre, x, rfl, hpre⟩ := ih this
      exact ⟨c :: pre, x, rfl, fun hm => by
        rcases List.mem_cons.mp hm with hm | hm
        · exact hc hm.symm
        · exact hpre hm⟩

/-- A newline-free prefix ending at the newline is determined. -/
theorem nl_split_unique {pre pre' x x' : List UInt8} (h : pre ++ 10 :: x = pre' ++ 10 :: x')
    (hpre : 10 ∉ pre) (hpre' : 10 ∉ pre') : pre = pre' ∧ x = x' := by
  induction pre generalizing pre' with
  | nil =>
    cases pre' with
    | nil => simp_all
    | cons c pre' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self ..) hpre'
  | cons c pre ih =>
    cases pre' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (h.1.symm ▸ List.mem_cons_self ..) hpre
    | cons c' pre' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hx⟩ := ih h.2 (not_mem_cons_tail hpre) (not_mem_cons_tail hpre')
      exact ⟨by rw [h.1], hx⟩

/-! ## Scalars -/

theorem naiveNum_local (l : List UInt8) (_hl : 10 ∉ l) :
    (∀ x, naiveNum (l ++ 10 :: x) = none) ∨
    ∃ n r, r <:+ l ∧ ∀ x, naiveNum (l ++ 10 :: x) = some (n, r ++ 10 :: x) := by
  have ht := takeWhile_append_nl isDigit isDigit_nl l
  have hd := dropWhile_append_nl isDigit isDigit_nl l
  by_cases hc : ((l.takeWhile isDigit).isEmpty ||
      ((l.takeWhile isDigit).head? == some 48 && (l.takeWhile isDigit).length != 1)) = true
  · left; intro x; unfold naiveNum; rw [ht]; simp only [hc, ↓reduceIte]
  · right
    refine ⟨digitsVal (l.takeWhile isDigit), l.dropWhile isDigit, List.dropWhile_suffix _, ?_⟩
    intro x; unfold naiveNum; rw [ht, hd]; simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem naiveNat_local : LineLocal naiveNat := by
  intro l hl
  rcases naiveNum_local l hl with h | ⟨n, r, hr, h⟩
  · exact ⟨l, List.suffix_rfl, .inr ⟨.expectedNat, fun x => by unfold naiveNat; rw [h x]⟩⟩
  · exact ⟨r, hr, .inl ⟨n, fun x => by unfold naiveNat; rw [h x]⟩⟩

theorem naiveLit_local (s : String) (hs : 10 ∉ lit s) (l : List UInt8) (_hl : 10 ∉ l) :
    (∀ x, naiveLit s (l ++ 10 :: x) = none) ∨
    ∃ r, r <:+ l ∧ ∀ x, naiveLit s (l ++ 10 :: x) = some (r ++ 10 :: x) := by
  by_cases hp : lit s <+: l
  · right
    refine ⟨l.drop (lit s).length, List.drop_suffix _ _, fun x => ?_⟩
    unfold naiveLit
    rw [if_pos (List.isPrefixOf_iff_prefix.mpr (hp.trans (List.prefix_append _ _))),
      List.drop_append_of_le_length hp.length_le]
  · left; intro x
    unfold naiveLit
    rw [if_neg]
    intro hpx
    have hpx := List.isPrefixOf_iff_prefix.mp hpx
    apply hp
    -- the literal is a prefix of `l ++ 10 :: x`; it cannot reach the newline
    by_cases hlen : (lit s).length ≤ l.length
    · exact List.prefix_of_prefix_length_le hpx (List.prefix_append _ _) hlen
    · exfalso
      have hl' : l <+: lit s := List.prefix_of_prefix_length_le (List.prefix_append _ _) hpx
        (by omega)
      obtain ⟨t, ht⟩ := hl'
      obtain ⟨u, hu⟩ := hpx
      rw [← ht, List.append_assoc] at hu
      have := List.append_cancel_left hu
      cases t with
      | nil => rw [List.append_nil] at ht; rw [ht] at hlen; exact hlen (Nat.le_refl _)
      | cons c t =>
        simp only [List.cons_append, List.cons.injEq] at this
        exact hs (ht ▸ (List.mem_append.mpr (.inr (this.1 ▸ List.mem_cons_self ..))))

theorem naiveBool_local : LineLocal naiveBool := by
  intro l hl
  rcases naiveLit_local "true" (by rw [lit_eq_toByteArray]; decide) l hl with h1 | ⟨r, hr, h1⟩
  · rcases naiveLit_local "false" (by rw [lit_eq_toByteArray]; decide) l hl with h2 | ⟨r, hr, h2⟩
    · exact ⟨l, List.suffix_rfl, .inr ⟨.expectedBool, fun x => by
        unfold naiveBool; rw [h1 x, h2 x]⟩⟩
    · exact ⟨r, hr, .inl ⟨false, fun x => by unfold naiveBool; rw [h1 x, h2 x]⟩⟩
  · exact ⟨r, hr, .inl ⟨true, fun x => by unfold naiveBool; rw [h1 x]⟩⟩

theorem naiveStrBody_local : ∀ (n : Nat) (l : List UInt8), l.length ≤ n → 10 ∉ l →
    (∀ x, naiveStrBody (l ++ 10 :: x) = none) ∨
    ∃ body r, r <:+ l ∧ ∀ x, naiveStrBody (l ++ 10 :: x) = some (body, r ++ 10 :: x) := by
  intro n
  induction n with
  | zero =>
    intro l hn hl
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst this
    left; intro x; rw [List.nil_append, naiveStrBody.eq_def]; simp
  | succ n ih =>
    intro l hn hl
    cases l with
    | nil => left; intro x; rw [List.nil_append, naiveStrBody.eq_def]; simp
    | cons c l' =>
      have _hc10 := cons_ne_nl hl
      have hl' := not_mem_cons_tail hl
      by_cases h34 : c = 34
      · subst h34
        right
        exact ⟨[], l', List.suffix_cons _ _, fun x => by
          rw [List.cons_append, naiveStrBody.eq_def]; simp⟩
      by_cases h92 : c = 92
      · subst h92
        cases l' with
        | nil =>
          left; intro x
          rw [List.cons_append, List.nil_append, naiveStrBody.eq_def]
          simp
        | cons d l'' =>
          have hl'' := not_mem_cons_tail hl'
          by_cases hd : d < 32
          · left; intro x
            rw [List.cons_append, List.cons_append, naiveStrBody.eq_def]
            simp [hd]
          · rcases ih l'' (by simp at hn; omega) hl'' with h | ⟨body, r, hr, h⟩
            · left; intro x
              rw [List.cons_append, List.cons_append, naiveStrBody.eq_def]
              simp [hd, h x]
            · right
              refine ⟨92 :: d :: body, r, hr.trans ((List.suffix_cons _ _).trans
                (List.suffix_cons _ _)), fun x => ?_⟩
              rw [List.cons_append, List.cons_append, naiveStrBody.eq_def]
              simp [hd, h x]
      by_cases hlt : c < 32
      · left; intro x
        rw [List.cons_append, naiveStrBody.eq_def]
        simp [h34, h92, hlt]
      · rcases ih l' (by simp at hn; omega) hl' with h | ⟨body, r, hr, h⟩
        · left; intro x
          rw [List.cons_append, naiveStrBody.eq_def]
          simp [h34, h92, hlt, h x]
        · right
          refine ⟨c :: body, r, hr.trans (List.suffix_cons _ _), fun x => ?_⟩
          rw [List.cons_append, naiveStrBody.eq_def]
          simp [h34, h92, hlt, h x]

theorem naiveStr_local : LineLocal naiveStr := by
  intro l hl
  cases l with
  | nil =>
    exact ⟨[], List.suffix_rfl, .inr ⟨.expectedString, fun x => by
      rw [naiveStr_err (by simp)]⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h34 : c = 34
    · subst h34
      rcases naiveStrBody_local l'.length l' (Nat.le_refl _) hl' with h | ⟨body, r, hr, h⟩
      · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedString, fun x => by
          rw [naiveStr_cons _ _ (List.cons_append ..), h x]⟩⟩
      · by_cases hcon : body.contains 92 = true
        · cases hu : unescape (⟨⟨body⟩⟩ : ByteArray) 0 (⟨⟨body⟩⟩ : ByteArray).usize
            ByteArray.empty with
          | none =>
            exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badEscape, fun x => by
              rw [naiveStr_cons _ _ (List.cons_append ..), h x]
              simp only [hcon, ↓reduceIte, hu]⟩⟩
          | some s =>
            exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨s, fun x => by
              rw [naiveStr_cons _ _ (List.cons_append ..), h x]
              simp only [hcon, ↓reduceIte, hu]⟩⟩
        · cases hf : String.fromUTF8? (⟨⟨body⟩⟩ : ByteArray) with
          | none =>
            exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badUtf8, fun x => by
              rw [naiveStr_cons _ _ (List.cons_append ..), h x]
              simp only [hcon, Bool.false_eq_true, ↓reduceIte, hf]⟩⟩
          | some s =>
            exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨s, fun x => by
              rw [naiveStr_cons _ _ (List.cons_append ..), h x]
              simp only [hcon, Bool.false_eq_true, ↓reduceIte, hf]⟩⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedString, fun x => by
        rw [naiveStr_err (by simpa using h34)]⟩⟩

theorem naiveQuotedNat_local : LineLocal naiveQuotedNat := by
  intro l hl
  cases l with
  | nil =>
    exact ⟨[], List.suffix_rfl, .inr ⟨.badNatVal, fun x => by
      unfold naiveQuotedNat; rfl⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h34 : c = 34
    · subst h34
      have ht := takeWhile_append_nl isDigit isDigit_nl l'
      have hd := dropWhile_append_nl isDigit isDigit_nl l'
      cases hds : l'.takeWhile isDigit with
      | nil =>
        exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badNatVal, fun x => by
          rw [naiveQuotedNat_cons _ _ (List.cons_append ..), ht, hds]⟩⟩
      | cons d ds =>
        cases hdr : l'.dropWhile isDigit with
        | nil =>
          exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badNatVal, fun x => by
            rw [naiveQuotedNat_cons _ _ (List.cons_append ..), ht, hds, hd, hdr]; rfl⟩⟩
        | cons e rest =>
          by_cases he : e = 34
          · subst he
            refine ⟨rest, ?_, .inl ⟨digitsVal (d :: ds), fun x => by
              rw [naiveQuotedNat_cons _ _ (List.cons_append ..), ht, hds, hd, hdr]; rfl⟩⟩
            exact ((List.suffix_cons _ _).trans (hdr ▸ List.dropWhile_suffix _)).trans
              (List.suffix_cons _ _)
          · refine ⟨34 :: l', List.suffix_rfl, .inr ⟨.badNatVal, fun x => by
              rw [naiveQuotedNat_cons _ _ (List.cons_append ..), ht, hds, hd, hdr]
              simp only [List.cons_append]
              split
              all_goals first | rfl | simp_all⟩⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.badNatVal, fun x => by
        unfold naiveQuotedNat
        simp only [List.cons_append]
        split
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h34
        · rfl⟩⟩

theorem naiveBinderInfo_local : LineLocal naiveBinderInfo := by
  intro l hl
  cases l with
  | nil =>
    exact ⟨[], List.suffix_rfl, .inr ⟨.badBinderInfo, fun x => by
      unfold naiveBinderInfo; rfl⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h34 : c = 34
    · subst h34
      have unf : ∀ x, naiveBinderInfo (34 :: l' ++ 10 :: x) =
          (match naiveLit "default\"" (l' ++ 10 :: x) with
          | some r => .ok () r
          | none =>
            match naiveLit "implicit\"" (l' ++ 10 :: x) with
            | some r => .ok () r
            | none =>
              match naiveLit "strictImplicit\"" (l' ++ 10 :: x) with
              | some r => .ok () r
              | none =>
                match naiveLit "instImplicit\"" (l' ++ 10 :: x) with
                | some r => .ok () r
                | none => .err .badBinderInfo (34 :: l' ++ 10 :: x)) := fun x => rfl
      rcases naiveLit_local "default\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h1 | ⟨r, hr, h1⟩
      · rcases naiveLit_local "implicit\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h2 | ⟨r, hr, h2⟩
        · rcases naiveLit_local "strictImplicit\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h3 | ⟨r, hr, h3⟩
          · rcases naiveLit_local "instImplicit\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h4 | ⟨r, hr, h4⟩
            · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badBinderInfo, fun x => by
                rw [unf, h1 x, h2 x, h3 x, h4 x]⟩⟩
            · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨(), fun x => by
                rw [unf, h1 x, h2 x, h3 x, h4 x]⟩⟩
          · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨(), fun x => by
              rw [unf, h1 x, h2 x, h3 x]⟩⟩
        · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨(), fun x => by
            rw [unf, h1 x, h2 x]⟩⟩
      · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨(), fun x => by rw [unf, h1 x]⟩⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.badBinderInfo, fun x => by
        unfold naiveBinderInfo
        simp only [List.cons_append]
        split
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h34
        · rfl⟩⟩


/-! ## Keys and values -/

theorem naiveKeyBody_local : ∀ (l : List UInt8), 10 ∉ l →
    (∀ x, naiveKeyBody (l ++ 10 :: x) = none) ∨
    ∃ k r, r <:+ l ∧ ∀ x, naiveKeyBody (l ++ 10 :: x) = some (k, r ++ 10 :: x) := by
  intro l
  induction l with
  | nil => intro _; left; intro x; rw [List.nil_append, naiveKeyBody.eq_def]; simp
  | cons c l' ih =>
    intro hl
    have hl' := not_mem_cons_tail hl
    by_cases h34 : c = 34
    · subst h34
      right
      exact ⟨[], l', List.suffix_cons _ _, fun x => by
        rw [List.cons_append, naiveKeyBody.eq_def]; simp⟩
    by_cases hlt : (c < 32 || c == 92) = true
    · left; intro x
      rw [List.cons_append, naiveKeyBody.eq_def]
      simp [h34, hlt]
    · rcases ih hl' with h | ⟨k, r, hr, h⟩
      · left; intro x
        rw [List.cons_append, naiveKeyBody.eq_def]
        simp [h34, hlt, h x]
      · right
        refine ⟨c :: k, r, hr.trans (List.suffix_cons _ _), fun x => ?_⟩
        rw [List.cons_append, naiveKeyBody.eq_def]
        simp [h34, hlt, h x]

theorem naiveValue_local (l : List UInt8) (_hl : 10 ∉ l) :
    (∀ x, naiveValue (l ++ 10 :: x) = none) ∨
    ∃ r, r <:+ l ∧ ∀ x, naiveValue (l ++ 10 :: x) = some (r ++ 10 :: x) := by
  have hd := dropWhile_append_nl isWs isWs_nl l
  cases hdw : l.dropWhile isWs with
  | nil => left; intro x; unfold naiveValue; rw [hd, hdw]; rfl
  | cons c r' =>
    have hr' : r' <:+ l := (List.suffix_cons _ _).trans (hdw ▸ List.dropWhile_suffix _)
    by_cases h58 : c = 58
    · subst h58
      right
      refine ⟨r'.dropWhile isWs, (List.dropWhile_suffix _).trans hr', fun x => ?_⟩
      unfold naiveValue
      rw [hd, hdw, List.cons_append]
      show some ((r' ++ 10 :: x).dropWhile isWs) = _
      rw [dropWhile_append_nl isWs isWs_nl r' x]
    · left; intro x
      unfold naiveValue
      rw [hd, hdw, List.cons_append]
      split
      · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h58
      · rfl

/-- The length test every loop guards its recursion with, on the two
sides of a newline: the newline and what follows cancel. -/
theorem length_lt_nl (r l x : List UInt8) :
    (r ++ 10 :: x).length < (l ++ 10 :: x).length ↔ r.length < l.length := by
  simp only [List.length_append, List.length_cons]; omega

theorem naiveSkipBraced_local : ∀ (n : Nat) (l : List UInt8) (d : Nat), l.length ≤ n → 10 ∉ l →
    (∀ x, naiveSkipBraced (l ++ 10 :: x) d = none) ∨
    ∃ r, r <:+ l ∧ ∀ x, naiveSkipBraced (l ++ 10 :: x) d = some (r ++ 10 :: x) := by
  intro n
  induction n with
  | zero =>
    intro l d hn _
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst this
    left; intro x; rw [List.nil_append, naiveSkipBraced.eq_def]; simp
  | succ n ih =>
    intro l d hn hl
    cases l with
    | nil => left; intro x; rw [List.nil_append, naiveSkipBraced.eq_def]; simp
    | cons c l' =>
      have hc10 : (c == 10) = false := by simpa using cons_ne_nl hl
      have hl' := not_mem_cons_tail hl
      have hn' : l'.length ≤ n := by simp at hn; omega
      by_cases h34 : c = 34
      · subst h34
        rcases naiveStrBody_local l'.length l' (Nat.le_refl _) hl' with h | ⟨body, r₁, hr₁, h⟩
        · left; intro x
          rw [List.cons_append, naiveSkipBraced.eq_def]
          simp [h x]
        · have hr₁n : 10 ∉ r₁ := not_mem_of_suffix hr₁ hl'
          have hr₁l : r₁.length ≤ n := Nat.le_trans hr₁.length_le hn'
          by_cases hlt : r₁.length < (34 :: l').length
          · rcases ih r₁ d hr₁l hr₁n with h2 | ⟨r, hr, h2⟩
            · left; intro x
              rw [List.cons_append, naiveSkipBraced.eq_def]
              simp only [BEq.rfl, ↓reduceIte, h x, dite_eq_ite]
              rw [← List.cons_append, if_pos ((length_lt_nl _ _ _).mpr hlt), h2 x]
            · right
              refine ⟨r, hr.trans (hr₁.trans (List.suffix_cons _ _)), fun x => ?_⟩
              rw [List.cons_append, naiveSkipBraced.eq_def]
              simp only [BEq.rfl, ↓reduceIte, h x, dite_eq_ite]
              rw [← List.cons_append, if_pos ((length_lt_nl _ _ _).mpr hlt), h2 x]
          · left; intro x
            rw [List.cons_append, naiveSkipBraced.eq_def]
            simp only [BEq.rfl, ↓reduceIte, h x, dite_eq_ite]
            rw [← List.cons_append, if_neg (fun hx => hlt ((length_lt_nl _ _ _).mp hx))]
      have h34' : (c == 34) = false := by simpa using h34
      by_cases hbr : (c == 123 || c == 91) = true
      · rcases ih l' (d + 1) hn' hl' with h | ⟨r, hr, h⟩
        · left; intro x
          rw [List.cons_append, naiveSkipBraced.eq_def]
          simp [h34', hc10, hbr, h x]
        · right
          refine ⟨r, hr.trans (List.suffix_cons _ _), fun x => ?_⟩
          rw [List.cons_append, naiveSkipBraced.eq_def]
          simp [h34', hc10, hbr, h x]
      by_cases hcl : (c == 125 || c == 93) = true
      · cases d with
        | zero =>
          right
          exact ⟨l', List.suffix_cons _ _, fun x => by
            rw [List.cons_append, naiveSkipBraced.eq_def]
            simp [h34', hc10, hbr, hcl]⟩
        | succ d =>
          rcases ih l' d hn' hl' with h | ⟨r, hr, h⟩
          · left; intro x
            rw [List.cons_append, naiveSkipBraced.eq_def]
            simp [h34', hc10, hbr, hcl, h x]
          · right
            refine ⟨r, hr.trans (List.suffix_cons _ _), fun x => ?_⟩
            rw [List.cons_append, naiveSkipBraced.eq_def]
            simp [h34', hc10, hbr, hcl, h x]
      · rcases ih l' d hn' hl' with h | ⟨r, hr, h⟩
        · left; intro x
          rw [List.cons_append, naiveSkipBraced.eq_def]
          simp [h34', hc10, hbr, hcl, h x]
        · right
          refine ⟨r, hr.trans (List.suffix_cons _ _), fun x => ?_⟩
          rw [List.cons_append, naiveSkipBraced.eq_def]
          simp [h34', hc10, hbr, hcl, h x]

/-! ## Lists -/

theorem naiveListLoop_local (start : UInt8 → Bool) (hs : start 10 = false)
    (item : List UInt8 → NRes α) (hitem : LineLocal item) :
    ∀ (n : Nat) (l : List UInt8) (acc : List α) (w : Bool), l.length ≤ n → 10 ∉ l →
      ∃ r, r <:+ l ∧ LocalAt (fun l => naiveListLoop start item l acc w) l r := by
  intro n
  induction n with
  | zero =>
    intro l acc w hn _
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst this
    exact ⟨[], List.suffix_rfl, .inr ⟨.expectedList, fun x => by
      show naiveListLoop _ _ (10 :: x) _ _ = _; rw [naiveListLoop.eq_def]; simp [hs, isWs_nl]⟩⟩
  | succ n ih =>
    intro l acc w hn hl
    cases l with
    | nil =>
      exact ⟨[], List.suffix_rfl, .inr ⟨.expectedList, fun x => by
        show naiveListLoop _ _ (10 :: x) _ _ = _; rw [naiveListLoop.eq_def]; simp [hs, isWs_nl]⟩⟩
    | cons c l' =>
      have hl' := not_mem_cons_tail hl
      have hn' : l'.length ≤ n := by simp at hn; omega
      by_cases hws : isWs c = true
      · obtain ⟨r, hr, h⟩ := ih l' acc w hn' hl'
        refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
        rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
        · exact .inl ⟨v, fun x => by
            show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp only [hws, ↓reduceIte]; exact hv x⟩
        · exact .inr ⟨t, fun x => by
            show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp only [hws, ↓reduceIte]; exact ht x⟩
      have hws' : isWs c = false := by simpa using hws
      by_cases h93 : c = 93
      · subst h93
        by_cases hwa : (w && !acc.isEmpty) = true
        · exact ⟨93 :: l', List.suffix_rfl, .inr ⟨.expectedList, fun x => by
            show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp [hws', hwa]⟩⟩
        · exact ⟨l', List.suffix_cons _ _, .inl ⟨acc.reverse, fun x => by
            show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp [hws', hwa]⟩⟩
      have h93' : (c == 93) = false := by simpa using h93
      by_cases h44 : c = 44
      · subst h44
        by_cases hw : w = true
        · exact ⟨44 :: l', List.suffix_rfl, .inr ⟨.expectedList, fun x => by
            show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp [hws', hw]⟩⟩
        · obtain ⟨r, hr, h⟩ := ih l' acc true hn' hl'
          have hw' : w = false := by simpa using hw
          refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
          rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
          · exact .inl ⟨v, fun x => by
              show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp only [hws', hw', BEq.rfl,
                Bool.false_eq_true, ↓reduceIte]; exact hv x⟩
          · exact .inr ⟨t, fun x => by
              show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp only [hws', hw', BEq.rfl,
                Bool.false_eq_true, ↓reduceIte]; exact ht x⟩
      have h44' : (c == 44) = false := by simpa using h44
      by_cases hst : start c = true
      · by_cases hw : w = true
        · subst hw
          obtain ⟨r₁, hr₁, h⟩ := hitem (c :: l') hl
          rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
          · have hr₁n : 10 ∉ r₁ := not_mem_of_suffix hr₁ hl
            by_cases hlt : r₁.length < (c :: l').length
            · obtain ⟨r, hr, h2⟩ := ih r₁ (v :: acc) false (by
                have := hr₁.length_le; simp at this hn hlt; omega) hr₁n
              refine ⟨r, hr.trans hr₁, ?_⟩
              rcases h2 with ⟨v', hv'⟩ | ⟨t', ht'⟩
              · exact .inl ⟨v', fun x => by
                  show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]
                  simp only [hws', h93', h44', hst, Bool.false_eq_true, ↓reduceIte,
                    Bool.not_true, ← List.cons_append, hv x, dite_eq_ite]
                  rw [if_pos ((length_lt_nl _ _ _).mpr hlt)]; exact hv' x⟩
              · exact .inr ⟨t', fun x => by
                  show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]
                  simp only [hws', h93', h44', hst, Bool.false_eq_true, ↓reduceIte,
                    Bool.not_true, ← List.cons_append, hv x, dite_eq_ite]
                  rw [if_pos ((length_lt_nl _ _ _).mpr hlt)]; exact ht' x⟩
            · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.noProgress, fun x => by
                show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]
                simp only [hws', h93', h44', hst, Bool.false_eq_true, ↓reduceIte,
                  Bool.not_true, ← List.cons_append, hv x, dite_eq_ite]
                rw [if_neg (fun hx => hlt ((length_lt_nl _ _ _).mp hx))]⟩⟩
          · exact ⟨r₁, hr₁, .inr ⟨t, fun x => by
              show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]
              simp only [hws', h93', h44', hst, Bool.false_eq_true, ↓reduceIte,
                Bool.not_true, ← List.cons_append, ht x]⟩⟩
        · have hw' : w = false := by simpa using hw
          exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedList, fun x => by
            show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp [hws', h93', h44', hst, hw']⟩⟩
      · have hst' : start c = false := by simpa using hst
        exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedList, fun x => by
          show naiveListLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ = _; rw [naiveListLoop.eq_def]; simp [hws', h93', h44', hst']⟩⟩

theorem naiveList_local (start : UInt8 → Bool) (hs : start 10 = false)
    (item : List UInt8 → NRes α) (hitem : LineLocal item) :
    LineLocal (naiveList start item) := by
  intro l hl
  cases l with
  | nil => exact ⟨[], List.suffix_rfl, .inr ⟨.expectedList, fun x => by
      unfold naiveList; rfl⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h91 : c = 91
    · subst h91
      obtain ⟨r, hr, h⟩ := naiveListLoop_local start hs item hitem l'.length l' [] true
        (Nat.le_refl _) hl'
      refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
      rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
      · exact .inl ⟨v, fun x => by unfold naiveList; exact hv x⟩
      · exact .inr ⟨t, fun x => by unfold naiveList; exact ht x⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedList, fun x => by
        unfold naiveList
        simp only [List.cons_append]
        split
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h91
        · rfl⟩⟩

theorem naiveNatList_local : LineLocal naiveNatList :=
  naiveList_local isDigit isDigit_nl naiveNat naiveNat_local

theorem naivePw_local : LineLocal naivePw := by
  intro l hl
  cases l with
  | nil => exact ⟨[], List.suffix_rfl, .inr ⟨.badPw, fun x => by unfold naivePw; rfl⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h91 : c = 91
    · subst h91
      obtain ⟨r, hr, h⟩ := naiveListLoop_local isDigit isDigit_nl naiveNat naiveNat_local
        l'.length l' [] true (Nat.le_refl _) hl'
      refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
      rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
      · exact .inl ⟨.ifAllZero v, fun x => by
          unfold naivePw; simp only [List.cons_append]
          rw [show naiveListLoop _ _ (l' ++ 10 :: x) [] true = _ from hv x]; rfl⟩
      · exact .inr ⟨t, fun x => by
          unfold naivePw; simp only [List.cons_append]
          rw [show naiveListLoop _ _ (l' ++ 10 :: x) [] true = _ from ht x]; rfl⟩
    by_cases h34 : c = 34
    · subst h34
      rcases naiveLit_local "never\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h | ⟨r, hr, h⟩
      · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badPw, fun x => by
          unfold naivePw; simp only [List.cons_append]; rw [h x]⟩⟩
      · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨.never, fun x => by
          unfold naivePw; simp only [List.cons_append]; rw [h x]⟩⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.badPw, fun x => by
        unfold naivePw
        simp only [List.cons_append]
        split
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h91
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h34
        · rfl⟩⟩

theorem naiveHints_local : LineLocal naiveHints := by
  intro l hl
  cases l with
  | nil => exact ⟨[], List.suffix_rfl, .inr ⟨.badHints, fun x => by unfold naiveHints; rfl⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h34 : c = 34
    · subst h34
      rcases naiveLit_local "abbrev\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h1 | ⟨r, hr, h1⟩
      · rcases naiveLit_local "opaque\"" (by rw [lit_eq_toByteArray]; decide) l' hl' with h2 | ⟨r, hr, h2⟩
        · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.badHints, fun x => by
            unfold naiveHints; simp only [List.cons_append]; rw [h1 x, h2 x]⟩⟩
        · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨.«opaque», fun x => by
            unfold naiveHints; simp only [List.cons_append]; rw [h1 x, h2 x]⟩⟩
      · exact ⟨r, hr.trans (List.suffix_cons _ _), .inl ⟨.«abbrev», fun x => by
          unfold naiveHints; simp only [List.cons_append]; rw [h1 x]⟩⟩
    by_cases h123 : c = 123
    · subst h123
      have hd := dropWhile_append_nl isWs isWs_nl l'
      cases hdw : l'.dropWhile isWs with
      | nil =>
        exact ⟨123 :: l', List.suffix_rfl, .inr ⟨.badHints, fun x => by
          unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]; rfl⟩⟩
      | cons c₁ p' =>
        have hp' : p' <:+ l' := (List.suffix_cons _ _).trans (hdw ▸ List.dropWhile_suffix _)
        have hp'n : 10 ∉ p' := not_mem_of_suffix hp' hl'
        by_cases hc₁ : c₁ = 34
        · subst hc₁
          rcases naiveKeyBody_local p' hp'n with h | ⟨key, r₁, hr₁, h⟩
          · exact ⟨34 :: p', (hdw ▸ List.dropWhile_suffix _).trans (List.suffix_cons _ _),
              .inr ⟨.badHints, fun x => by
                unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                simp only [List.cons_append, h x]⟩⟩
          · have hr₁n : 10 ∉ r₁ := not_mem_of_suffix hr₁ hp'n
            have hr₁l : r₁ <:+ 123 :: l' := (hr₁.trans hp').trans (List.suffix_cons _ _)
            by_cases hreg : keyOf key = .kRegular
            · rcases naiveValue_local r₁ hr₁n with h2 | ⟨r₂, hr₂, h2⟩
              · exact ⟨34 :: p', (hdw ▸ List.dropWhile_suffix _).trans (List.suffix_cons _ _),
                  .inr ⟨.expectedColon, fun x => by
                    unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                    simp only [List.cons_append, h x, hreg, h2 x]⟩⟩
              · have hr₂n : 10 ∉ r₂ := not_mem_of_suffix hr₂ hr₁n
                rcases naiveNum_local r₂ hr₂n with h3 | ⟨v, r₃, hr₃, h3⟩
                · exact ⟨r₂, hr₂.trans hr₁l, .inr ⟨.expectedNat, fun x => by
                    unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                    simp only [List.cons_append, h x, hreg, h2 x, h3 x]⟩⟩
                · have hr₃n : 10 ∉ r₃ := not_mem_of_suffix hr₃ hr₂n
                  have hd3 := dropWhile_append_nl isWs isWs_nl r₃
                  cases hdw3 : r₃.dropWhile isWs with
                  | nil =>
                    exact ⟨[], List.nil_suffix, .inr ⟨.expectedComma, fun x => by
                      unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                      simp only [List.cons_append, h x, hreg, h2 x, h3 x]
                      rw [hd3, hdw3]; rfl⟩⟩
                  | cons c₂ rest =>
                    have hrest : rest <:+ 123 :: l' :=
                      ((List.suffix_cons _ _).trans (hdw3 ▸ List.dropWhile_suffix _)).trans
                        ((hr₃.trans hr₂).trans hr₁l)
                    by_cases hc₂ : c₂ = 125
                    · subst hc₂
                      exact ⟨rest, hrest, .inl ⟨.regular v, fun x => by
                        unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                        simp only [List.cons_append, h x, hreg, h2 x, h3 x]
                        rw [hd3, hdw3]; rfl⟩⟩
                    · have hcr : c₂ :: rest <:+ r₃ := hdw3 ▸ List.dropWhile_suffix _
                      exact ⟨c₂ :: rest, hcr.trans ((hr₃.trans hr₂).trans hr₁l),
                        .inr ⟨.expectedComma, fun x => by
                          unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                          simp only [List.cons_append, h x, hreg, h2 x, h3 x]
                          rw [hd3, hdw3]
                          simp only [List.cons_append]
                          split
                          · rename_i heq; simp only [List.cons.injEq] at heq
                            exact absurd heq.1 hc₂
                          · rfl⟩⟩
            · exact ⟨34 :: p', (hdw ▸ List.dropWhile_suffix _).trans (List.suffix_cons _ _),
                .inr ⟨.badHints, fun x => by
                  unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
                  simp only [List.cons_append, h x]
                  try (split <;> first | rfl | (rename_i hk; exact absurd hk hreg))⟩⟩
        · exact ⟨123 :: l', List.suffix_rfl, .inr ⟨.badHints, fun x => by
            unfold naiveHints; simp only [List.cons_append]; rw [hd, hdw]
            simp only [List.cons_append]
            split
            · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hc₁
            · rfl⟩⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.badHints, fun x => by
        unfold naiveHints
        simp only [List.cons_append]
        split
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h34
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h123
        · rfl⟩⟩


/-! ## Objects -/

theorem naiveObjLoop_local (fields : Key → Option (Slot σ)) (required : UInt32)
    (hf : ∀ k slot, fields k = some slot → ∀ st, LineLocal (fun l => slot.read l st)) :
    ∀ (n : Nat) (l : List UInt8) (w : Bool) (seen : UInt32) (st : σ), l.length ≤ n → 10 ∉ l →
      ∃ r, r <:+ l ∧ LocalAt (fun l => naiveObjLoop fields required l w seen st) l r := by
  intro n
  induction n with
  | zero =>
    intro l w seen st hn _
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst this
    exact ⟨[], List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
      show naiveObjLoop _ _ (10 :: x) _ _ _ = _; rw [naiveObjLoop.eq_def]; simp [isWs_nl]⟩⟩
  | succ n ih =>
    intro l w seen st hn hl
    cases l with
    | nil =>
      exact ⟨[], List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
        show naiveObjLoop _ _ (10 :: x) _ _ _ = _; rw [naiveObjLoop.eq_def]; simp [isWs_nl]⟩⟩
    | cons c l' =>
      have hl' := not_mem_cons_tail hl
      have hn' : l'.length ≤ n := by simp at hn; omega
      by_cases hws : isWs c = true
      · obtain ⟨r, hr, h⟩ := ih l' w seen st hn' hl'
        refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
        rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
        · exact .inl ⟨v, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp only [hws, ↓reduceIte]; exact hv x⟩
        · exact .inr ⟨t, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp only [hws, ↓reduceIte]; exact ht x⟩
      have hws' : isWs c = false := by simpa using hws
      by_cases h125 : c = 125
      · subst h125
        by_cases hwa : (w && seen != 0) = true
        · exact ⟨125 :: l', List.suffix_rfl, .inr ⟨.expectedKey, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp [hws', hwa]⟩⟩
        by_cases hreq : ((seen &&& required) != required) = true
        · exact ⟨125 :: l', List.suffix_rfl, .inr ⟨.missingKey, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp [hws', hwa, hreq]⟩⟩
        · exact ⟨l', List.suffix_cons _ _, .inl ⟨st, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp [hws', hwa, hreq]⟩⟩
      have h125' : (c == 125) = false := by simpa using h125
      by_cases h44 : c = 44
      · subst h44
        by_cases hw : w = true
        · exact ⟨44 :: l', List.suffix_rfl, .inr ⟨.expectedKey, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp [hws', hw]⟩⟩
        · have hw' : w = false := by simpa using hw
          obtain ⟨r, hr, h⟩ := ih l' true seen st hn' hl'
          refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
          rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
          · exact .inl ⟨v, fun x => by
              show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
              simp only [hws', hw', BEq.rfl, Bool.false_eq_true, ↓reduceIte]; exact hv x⟩
          · exact .inr ⟨t, fun x => by
              show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
              simp only [hws', hw', BEq.rfl, Bool.false_eq_true, ↓reduceIte]; exact ht x⟩
      have h44' : (c == 44) = false := by simpa using h44
      by_cases h34 : c = 34
      · subst h34
        by_cases hw : w = true
        · subst hw
          rcases naiveKeyBody_local l' hl' with h1 | ⟨key, r₁, hr₁, h1⟩
          · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedKey, fun x => by
              show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
              simp [hws', h1 x]⟩⟩
          have hr₁n := not_mem_of_suffix hr₁ hl'
          rcases naiveValue_local r₁ hr₁n with h2 | ⟨r₂, hr₂, h2⟩
          · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedColon, fun x => by
              show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
              simp [hws', h1 x, h2 x]⟩⟩
          have hr₂n := not_mem_of_suffix hr₂ hr₁n
          cases hfk : fields (keyOf key) with
          | none =>
            exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.unknownKey, fun x => by
              show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
              simp [hws', h1 x, h2 x, hfk]⟩⟩
          | some slot =>
            by_cases hdup : ((seen &&& slot.mask) != 0) = true
            · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.duplicateKey, fun x => by
                show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
                simp [hws', h1 x, h2 x, hfk, hdup]⟩⟩
            obtain ⟨r₃, hr₃, h3⟩ := hf _ _ hfk st r₂ hr₂n
            have hr₃l : r₃ <:+ 34 :: l' := (hr₃.trans (hr₂.trans hr₁)).trans (List.suffix_cons _ _)
            rcases h3 with ⟨st', h3⟩ | ⟨t, h3⟩
            · by_cases hlt : r₃.length < (34 :: l').length
              · have hr₃n := not_mem_of_suffix hr₃ hr₂n
                obtain ⟨r, hr, h4⟩ := ih r₃ false (seen ||| slot.mask) st'
                  (by have := hr₃l.length_le; simp at this hn hlt; omega) hr₃n
                refine ⟨r, hr.trans hr₃l, ?_⟩
                rcases h4 with ⟨v, hv⟩ | ⟨t', ht'⟩
                · exact .inl ⟨v, fun x => by
                    show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
                    simp only [hws', BEq.rfl, ↓reduceIte, h125', h44', Bool.false_eq_true,
                      Bool.not_true, h1 x, h2 x, hfk, hdup, h3 x, dite_eq_ite]
                    rw [← List.cons_append, if_pos ((length_lt_nl _ _ _).mpr hlt)]; exact hv x⟩
                · exact .inr ⟨t', fun x => by
                    show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
                    simp only [hws', BEq.rfl, ↓reduceIte, h125', h44', Bool.false_eq_true,
                      Bool.not_true, h1 x, h2 x, hfk, hdup, h3 x, dite_eq_ite]
                    rw [← List.cons_append, if_pos ((length_lt_nl _ _ _).mpr hlt)]; exact ht' x⟩
              · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.noProgress, fun x => by
                  show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
                  simp only [hws', BEq.rfl, ↓reduceIte, h125', h44', Bool.false_eq_true,
                    Bool.not_true, h1 x, h2 x, hfk, hdup, h3 x, dite_eq_ite]
                  rw [← List.cons_append, if_neg (fun hx => hlt ((length_lt_nl _ _ _).mp hx))]⟩⟩
            · exact ⟨r₃, hr₃l, .inr ⟨t, fun x => by
                show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
                simp only [hws', BEq.rfl, ↓reduceIte, h125', h44', Bool.false_eq_true,
                  Bool.not_true, h1 x, h2 x, hfk, hdup, h3 x]⟩⟩
        · have hw' : w = false := by simpa using hw
          exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
            show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
            simp [hws', hw']⟩⟩
      · have h34' : (c == 34) = false := by simpa using h34
        exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
          show naiveObjLoop _ _ (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveObjLoop.eq_def]
          simp [hws', h125', h44', h34']⟩⟩

theorem naiveObject_local (fields : Key → Option (Slot σ)) (required : UInt32)
    (hf : ∀ k slot, fields k = some slot → ∀ st, LineLocal (fun l => slot.read l st))
    (init : σ) (finish : σ → α) : LineLocal (naiveObject fields required init finish) := by
  intro l hl
  cases l with
  | nil => exact ⟨[], List.suffix_rfl, .inr ⟨.expectedObject, fun x => by
      unfold naiveObject; rfl⟩⟩
  | cons c l' =>
    have hl' := not_mem_cons_tail hl
    by_cases h123 : c = 123
    · subst h123
      obtain ⟨r, hr, h⟩ := naiveObjLoop_local fields required hf l'.length l' true 0 init
        (Nat.le_refl _) hl'
      refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
      rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
      · exact .inl ⟨finish v, fun x => by
          unfold naiveObject; simp only [List.cons_append]
          rw [show naiveObjLoop _ _ (l' ++ 10 :: x) true 0 init = _ from hv x]; rfl⟩
      · exact .inr ⟨t, fun x => by
          unfold naiveObject; simp only [List.cons_append]
          rw [show naiveObjLoop _ _ (l' ++ 10 :: x) true 0 init = _ from ht x]; rfl⟩
    · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedObject, fun x => by
        unfold naiveObject
        simp only [List.cons_append]
        split
        · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h123
        · rfl⟩⟩

theorem Slot.of_local {scan : List UInt8 → NRes α} (hscan : LineLocal scan) (mask : UInt32)
    (set : α → σ → σ) (st : σ) : LineLocal (fun l => (Slot.of mask scan set).read l st) := by
  intro l hl
  obtain ⟨r, hr, h⟩ := hscan l hl
  refine ⟨r, hr, ?_⟩
  rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
  · exact .inl ⟨set v st, fun x => by simp only [Slot.of, hv x]⟩
  · exact .inr ⟨t, fun x => by simp only [Slot.of, ht x]⟩

theorem Slot.drop_local {scan : List UInt8 → NRes α} (hscan : LineLocal scan) (mask : UInt32)
    (st : σ) : LineLocal (fun l => (Slot.drop mask scan : Slot σ).read l st) :=
  Slot.of_local hscan mask _ st

/-! ### The slot tables -/

-- every slot's reader is local: `Slot.of`/`Slot.drop` over a local scanner
-- (the scalar and index-list scanners; the object lists are added by
-- hand at the two tables that hold them, below their own lemmas)
macro "slot_local" : tactic => `(tactic| first
  | exact Slot.of_local naiveNat_local _ _ _ | exact Slot.of_local naiveStr_local _ _ _
  | exact Slot.of_local naiveNatList_local _ _ _ | exact Slot.of_local naiveBool_local _ _ _
  | exact Slot.of_local naivePw_local _ _ _ | exact Slot.of_local naiveHints_local _ _ _
  | exact Slot.drop_local naiveBinderInfo_local _ _ | exact Slot.drop_local naiveNat_local _ _
  | exact Slot.drop_local naiveBool_local _ _ | exact Slot.drop_local naiveNatList_local _ _)

macro "table_local" tbl:ident : tactic => `(tactic| (
  intro k slot hf st
  cases k <;> simp only [$tbl:ident, cvSlots, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_local)))

theorem strNameFields_read_local : ∀ k slot, strNameFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local strNameFields
theorem naiveStrName_local : LineLocal naiveStrName :=
  naiveObject_local _ _ strNameFields_read_local _ _

theorem numNameFields_read_local : ∀ k slot, numNameFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local numNameFields
theorem naiveNumName_local : LineLocal naiveNumName :=
  naiveObject_local _ _ numNameFields_read_local _ _

theorem appFields_read_local : ∀ k slot, appFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local appFields
theorem naiveAppExpr_local : LineLocal naiveAppExpr :=
  naiveObject_local _ _ appFields_read_local _ _

theorem binderFields_read_local : ∀ k slot, binderFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local binderFields
theorem naiveLamExpr_local : LineLocal naiveLamExpr :=
  naiveObject_local _ _ binderFields_read_local _ _
theorem naiveForallExpr_local : LineLocal naiveForallExpr :=
  naiveObject_local _ _ binderFields_read_local _ _

theorem letFields_read_local : ∀ k slot, letFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local letFields
theorem naiveLetExpr_local : LineLocal naiveLetExpr :=
  naiveObject_local _ _ letFields_read_local _ _

theorem constFields_read_local : ∀ k slot, constFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local constFields
theorem naiveConstExpr_local : LineLocal naiveConstExpr :=
  naiveObject_local _ _ constFields_read_local _ _

theorem projFields_read_local : ∀ k slot, projFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local projFields
theorem naiveProjExpr_local : LineLocal naiveProjExpr :=
  naiveObject_local _ _ projFields_read_local _ _

theorem ruleFields_read_local : ∀ k slot, ruleFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local ruleFields
theorem naiveRule_local : LineLocal naiveRule :=
  naiveObject_local _ _ ruleFields_read_local _ _
theorem naiveRules_local : LineLocal naiveRules :=
  naiveList_local _ (by decide) naiveRule naiveRule_local

theorem indRecFields_read_local : ∀ k slot, indRecFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by
  intro k slot hf st
  cases k <;> simp only [indRecFields, Option.some.injEq] at hf <;>
    first
      | exact absurd hf (by simp)
      | (subst hf; first | slot_local | exact Slot.of_local naiveRules_local _ _ _)
theorem naiveIndRec_local : LineLocal naiveIndRec :=
  naiveObject_local _ _ indRecFields_read_local _ _
theorem naiveIndRecs_local : LineLocal naiveIndRecs :=
  naiveList_local _ (by decide) naiveIndRec naiveIndRec_local

theorem indTypeFields_read_local : ∀ k slot, indTypeFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local indTypeFields
theorem naiveIndType_local : LineLocal naiveIndType :=
  naiveObject_local _ _ indTypeFields_read_local _ _
theorem naiveIndTypes_local : LineLocal naiveIndTypes :=
  naiveList_local _ (by decide) naiveIndType naiveIndType_local

theorem indCtorFields_read_local : ∀ k slot, indCtorFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local indCtorFields
theorem naiveIndCtor_local : LineLocal naiveIndCtor :=
  naiveObject_local _ _ indCtorFields_read_local _ _
theorem naiveIndCtors_local : LineLocal naiveIndCtors :=
  naiveList_local _ (by decide) naiveIndCtor naiveIndCtor_local

theorem axiomFields_read_local : ∀ k slot, axiomFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local axiomFields
theorem naiveAxiomDecl_local : LineLocal naiveAxiomDecl :=
  naiveObject_local _ _ axiomFields_read_local _ _

theorem defFields_read_local : ∀ k slot, defFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local defFields
theorem naiveDefDecl_local : LineLocal naiveDefDecl :=
  naiveObject_local _ _ defFields_read_local _ _

theorem thmFields_read_local : ∀ k slot, thmFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local thmFields
theorem naiveThmDecl_local : LineLocal naiveThmDecl :=
  naiveObject_local _ _ thmFields_read_local _ _

theorem opaqueFields_read_local : ∀ k slot, opaqueFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local opaqueFields
theorem naiveOpaqueDecl_local : LineLocal naiveOpaqueDecl :=
  naiveObject_local _ _ opaqueFields_read_local _ _

theorem quotFields_read_local : ∀ k slot, quotFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by table_local quotFields
theorem naiveQuotDecl_local : LineLocal naiveQuotDecl :=
  naiveObject_local _ _ quotFields_read_local _ _

theorem indFields_read_local : ∀ k slot, indFields k = some slot →
    ∀ st, LineLocal (fun l => slot.read l st) := by
  intro k slot hf st
  cases k <;> simp only [indFields, Option.some.injEq] at hf <;>
    first
      | exact absurd hf (by simp)
      | (subst hf
         first
           | slot_local
           | exact Slot.of_local naiveIndCtors_local _ _ _
           | exact Slot.of_local naiveIndRecs_local _ _ _
           | exact Slot.of_local naiveIndTypes_local _ _ _)
theorem naiveIndDecl_local : LineLocal naiveIndDecl :=
  naiveObject_local _ _ indFields_read_local _ _


/-! ## The line -/

/-- The record the line loop closes with at `}`, when the index key and
the payload fit: `none` is `missingKey` (no payload) or `mixedKeys`. -/
def closeRes : Option (IdxKey × Nat) → LinePayload → Option LineRec
  | some (.«in», i), .name r => some (.name i r)
  | some (.il, i), .level r => some (.level i r)
  | some (.ie, i), .expr r => some (.expr i r)
  | none, .decl d => some (.decl d)
  | none, .header => some .header
  | _, _ => none

theorem lineLoop_close (w : Bool) (idx : Option (IdxKey × Nat)) (pl : LinePayload)
    (y : List UInt8) (hw : (w && (idx.isSome || !pl.isAbsent)) = false) :
    naiveLineLoop (125 :: y) w idx pl =
      match closeRes idx pl with
      | some v => .ok v y
      | none => .err (if pl.isAbsent then .missingKey else .mixedKeys) (125 :: y) := by
  rw [naiveLineLoop.eq_def]
  simp only [isWs, BEq.rfl, Bool.false_eq_true, ↓reduceIte, hw]
  cases pl <;> rcases idx with _ | ⟨k, i⟩ <;> (try cases k) <;>
    simp [closeRes, LinePayload.isAbsent]

/-- The loop's continuation after a sub-scanner: either it made progress
and the loop goes on — by the induction hypothesis — or `noProgress`. -/
theorem lineLoop_cont {n : Nat}
    (ih : ∀ (l : List UInt8) (w : Bool) (idx : Option (IdxKey × Nat)) (pl : LinePayload),
      l.length ≤ n → 10 ∉ l → ∃ r, r <:+ l ∧ LocalAt (fun l => naiveLineLoop l w idx pl) l r)
    {c : UInt8} {l' r₁ : List UInt8} (hr₁ : r₁ <:+ c :: l') (hl : 10 ∉ c :: l')
    (hn : (c :: l').length ≤ n + 1) (idx : Option (IdxKey × Nat)) (pl : LinePayload) :
    ∃ r, r <:+ c :: l' ∧
      ((∃ v, ∀ x, (if (r₁ ++ 10 :: x).length < (c :: (l' ++ 10 :: x)).length then
            naiveLineLoop (r₁ ++ 10 :: x) false idx pl
          else .err .noProgress (c :: (l' ++ 10 :: x))) = .ok v (r ++ 10 :: x)) ∨
       (∃ t, ∀ x, (if (r₁ ++ 10 :: x).length < (c :: (l' ++ 10 :: x)).length then
            naiveLineLoop (r₁ ++ 10 :: x) false idx pl
          else .err .noProgress (c :: (l' ++ 10 :: x))) = .err t (r ++ 10 :: x))) := by
  by_cases hlt : r₁.length < (c :: l').length
  · have hr₁n := not_mem_of_suffix hr₁ hl
    obtain ⟨r, hr, h⟩ := ih r₁ false idx pl (by simp at hn hlt; omega) hr₁n
    refine ⟨r, hr.trans hr₁, ?_⟩
    rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
    · exact .inl ⟨v, fun x => by
        rw [← List.cons_append, if_pos ((length_lt_nl _ _ _).mpr hlt)]; exact hv x⟩
    · exact .inr ⟨t, fun x => by
        rw [← List.cons_append, if_pos ((length_lt_nl _ _ _).mpr hlt)]; exact ht x⟩
  · exact ⟨c :: l', List.suffix_rfl, .inr ⟨.noProgress, fun x => by
      rw [← List.cons_append, if_neg (fun hx => hlt ((length_lt_nl _ _ _).mp hx))]⟩⟩

section LineLoop

-- The line loop's member arm, one tactic per key group.  The macros
-- are unhygienic on purpose: they name the hypotheses the surrounding
-- proof introduces (`hws'`, `h125'`, `h44'`, `h1`, `h2`, `hk`, `hr₂n`,
-- `hr₂l`, `ih`, `hl`, `hn`, `l'`, `r₂`, `idx`, `pl`).
set_option hygiene false in
/-- unfold the loop on `34 :: (l' ++ 10 :: x)` down to the key dispatch -/
macro "line_unf" : tactic => `(tactic| (
  show naiveLineLoop (34 :: (l' ++ 10 :: x)) true idx pl = _
  rw [naiveLineLoop.eq_def]
  simp only [hws', BEq.rfl, ↓reduceIte, h125', h44', Bool.false_eq_true, Bool.not_true,
    h1 x, h2 x, hk, List.cons_append]))

set_option hygiene false in
/-- a key the dialect does not have -/
macro "line_unknown" : tactic => `(tactic|
  exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.unknownKey, fun x => by line_unf⟩⟩)

set_option hygiene false in
/-- an index key: `naiveNum`, then the loop with the index set -/
macro "line_idx" kind:term:max : tactic => `(tactic| (
  by_cases hi : idx.isSome = true
  · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.duplicateKey, fun x => by line_unf; simp [hi]⟩⟩
  · have hi' : idx.isSome = false := by simpa using hi
    rcases naiveNum_local r₂ hr₂n with h3 | ⟨v, r₃, hr₃, h3⟩
    · exact ⟨r₂, hr₂l, .inr ⟨.expectedNat, fun x => by
        line_unf; simp only [hi', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩
    · obtain ⟨r, hr, hres⟩ := lineLoop_cont ih (hr₃.trans hr₂l) hl hn (some ($kind, v)) pl
      refine ⟨r, hr, ?_⟩
      rcases hres with ⟨v', hv'⟩ | ⟨t', ht'⟩
      · exact .inl ⟨v', fun x => by
          line_unf; simp only [hi', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
          exact hv' x⟩
      · exact .inr ⟨t', fun x => by
          line_unf; simp only [hi', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
          exact ht' x⟩))

set_option hygiene false in
/-- a numeric payload key: `naiveNum`, then the loop with the payload -/
macro "line_num" pay:term:max : tactic => `(tactic| (
  by_cases hpa : (!pl.isAbsent) = true
  · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.duplicateKey, fun x => by line_unf; simp [hpa]⟩⟩
  · have hpa' : (!pl.isAbsent) = false := by simpa using hpa
    rcases naiveNum_local r₂ hr₂n with h3 | ⟨v, r₃, hr₃, h3⟩
    · exact ⟨r₂, hr₂l, .inr ⟨.expectedNat, fun x => by
        line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩
    · obtain ⟨r, hr, hres⟩ := lineLoop_cont ih (hr₃.trans hr₂l) hl hn idx ($pay v)
      refine ⟨r, hr, ?_⟩
      rcases hres with ⟨v', hv'⟩ | ⟨t', ht'⟩
      · exact .inl ⟨v', fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
          exact hv' x⟩
      · exact .inr ⟨t', fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
          exact ht' x⟩))

set_option hygiene false in
/-- a payload key read by a `LineLocal` scanner, then the loop with the payload -/
macro "line_pl" loc:term:max pay:term:max : tactic => `(tactic| (
  by_cases hpa : (!pl.isAbsent) = true
  · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.duplicateKey, fun x => by line_unf; simp [hpa]⟩⟩
  · have hpa' : (!pl.isAbsent) = false := by simpa using hpa
    obtain ⟨r₃, hr₃, h3⟩ := $loc r₂ hr₂n
    rcases h3 with ⟨v, h3⟩ | ⟨t, h3⟩
    · obtain ⟨r, hr, hres⟩ := lineLoop_cont ih (hr₃.trans hr₂l) hl hn idx ($pay v)
      refine ⟨r, hr, ?_⟩
      rcases hres with ⟨v', hv'⟩ | ⟨t', ht'⟩
      · exact .inl ⟨v', fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
          exact hv' x⟩
      · exact .inr ⟨t', fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
          exact ht' x⟩
    · exact ⟨r₃, hr₃.trans hr₂l, .inr ⟨t, fun x => by
        line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩))

set_option hygiene false in
/-- `max`/`imax`: a two-element index list -/
macro "line_pair" pay:term:max : tactic => `(tactic| (
  by_cases hpa : (!pl.isAbsent) = true
  · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.duplicateKey, fun x => by line_unf; simp [hpa]⟩⟩
  · have hpa' : (!pl.isAbsent) = false := by simpa using hpa
    obtain ⟨r₃, hr₃, h3⟩ := naiveNatList_local r₂ hr₂n
    rcases h3 with ⟨us, h3⟩ | ⟨t, h3⟩
    · rcases us with _ | ⟨a, _ | ⟨d, _ | ⟨e, us⟩⟩⟩
      · exact ⟨r₂, hr₂l, .inr ⟨.expectedList, fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩
      · exact ⟨r₂, hr₂l, .inr ⟨.expectedList, fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩
      · obtain ⟨r, hr, hres⟩ := lineLoop_cont ih (hr₃.trans hr₂l) hl hn idx ($pay a d)
        refine ⟨r, hr, ?_⟩
        rcases hres with ⟨v', hv'⟩ | ⟨t', ht'⟩
        · exact .inl ⟨v', fun x => by
            line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
            exact hv' x⟩
        · exact .inr ⟨t', fun x => by
            line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x, dite_eq_ite]
            exact ht' x⟩
      · exact ⟨r₂, hr₂l, .inr ⟨.expectedList, fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩
    · exact ⟨r₃, hr₃.trans hr₂l, .inr ⟨t, fun x => by
        line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, h3 x]⟩⟩))

set_option hygiene false in
/-- the `meta` header: a braced value, skipped -/
macro "line_meta" : tactic => `(tactic| (
  by_cases hpa : (!pl.isAbsent) = true
  · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.duplicateKey, fun x => by line_unf; simp [hpa]⟩⟩
  · have hpa' : (!pl.isAbsent) = false := by simpa using hpa
    rcases r₂ with _ | ⟨c₂, r₂'⟩
    · exact ⟨[], List.nil_suffix, .inr ⟨.expectedObject, fun x => by
        line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte]; rfl⟩⟩
    · have hr₂'n : 10 ∉ r₂' := not_mem_cons_tail hr₂n
      have hr₂'l : r₂' <:+ 34 :: l' := (List.suffix_cons _ _).trans hr₂l
      by_cases hc₂ : c₂ = 123
      · subst hc₂
        rcases naiveSkipBraced_local r₂'.length r₂' 0 (Nat.le_refl _) hr₂'n with h3 | ⟨r₃, hr₃, h3⟩
        · exact ⟨123 :: r₂', hr₂l, .inr ⟨.expectedObject, fun x => by
            line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, List.cons_append, h3 x]⟩⟩
        · obtain ⟨r, hr, hres⟩ := lineLoop_cont ih (hr₃.trans hr₂'l) hl hn idx .header
          refine ⟨r, hr, ?_⟩
          rcases hres with ⟨v', hv'⟩ | ⟨t', ht'⟩
          · exact .inl ⟨v', fun x => by
              line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, List.cons_append, h3 x,
                dite_eq_ite]
              exact hv' x⟩
          · exact .inr ⟨t', fun x => by
              line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, List.cons_append, h3 x,
                dite_eq_ite]
              exact ht' x⟩
      · exact ⟨c₂ :: r₂', hr₂l, .inr ⟨.expectedObject, fun x => by
          line_unf; simp only [hpa', Bool.false_eq_true, ↓reduceIte, List.cons_append]
          split
          · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hc₂
          · rfl⟩⟩))

theorem naiveLineLoop_local : ∀ (n : Nat) (l : List UInt8) (w : Bool)
    (idx : Option (IdxKey × Nat)) (pl : LinePayload), l.length ≤ n → 10 ∉ l →
    ∃ r, r <:+ l ∧ LocalAt (fun l => naiveLineLoop l w idx pl) l r := by
  intro n
  induction n with
  | zero =>
    intro l w idx pl hn _
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    subst this
    exact ⟨[], List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
      show naiveLineLoop (10 :: x) _ _ _ = _; rw [naiveLineLoop.eq_def]; simp [isWs_nl]⟩⟩
  | succ n ih =>
    intro l w idx pl hn hl
    cases l with
    | nil =>
      exact ⟨[], List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
        show naiveLineLoop (10 :: x) _ _ _ = _; rw [naiveLineLoop.eq_def]; simp [isWs_nl]⟩⟩
    | cons c l' =>
      have hl' := not_mem_cons_tail hl
      have hn' : l'.length ≤ n := by simp at hn; omega
      by_cases hws : isWs c = true
      · obtain ⟨r, hr, h⟩ := ih l' w idx pl hn' hl'
        refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
        rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
        · exact .inl ⟨v, fun x => by
            show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
            simp only [hws, ↓reduceIte]; exact hv x⟩
        · exact .inr ⟨t, fun x => by
            show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
            simp only [hws, ↓reduceIte]; exact ht x⟩
      have hws' : isWs c = false := by simpa using hws
      by_cases h125 : c = 125
      · subst h125
        by_cases hw : (w && (idx.isSome || !pl.isAbsent)) = true
        · exact ⟨125 :: l', List.suffix_rfl, .inr ⟨.expectedKey, fun x => by
            show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
            simp [hws', hw]⟩⟩
        · have hw' := (Bool.not_eq_true _).mp hw
          cases hc : closeRes idx pl with
          | some v =>
            exact ⟨l', List.suffix_cons _ _, .inl ⟨v, fun x => by
              show naiveLineLoop (125 :: (l' ++ 10 :: x)) _ _ _ = _
              rw [lineLoop_close _ _ _ _ hw', hc]⟩⟩
          | none =>
            exact ⟨125 :: l', List.suffix_rfl,
              .inr ⟨if pl.isAbsent then .missingKey else .mixedKeys, fun x => by
                show naiveLineLoop (125 :: (l' ++ 10 :: x)) _ _ _ = .err _ (125 :: (l' ++ 10 :: x))
                rw [lineLoop_close _ _ _ _ hw', hc]⟩⟩
      have h125' : (c == 125) = false := by simpa using h125
      by_cases h44 : c = 44
      · subst h44
        by_cases hw : w = true
        · exact ⟨44 :: l', List.suffix_rfl, .inr ⟨.expectedKey, fun x => by
            show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
            simp [hws', hw]⟩⟩
        · have hw' : w = false := by simpa using hw
          obtain ⟨r, hr, h⟩ := ih l' true idx pl hn' hl'
          refine ⟨r, hr.trans (List.suffix_cons _ _), ?_⟩
          rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
          · exact .inl ⟨v, fun x => by
              show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
              simp only [hws', hw', BEq.rfl, Bool.false_eq_true, ↓reduceIte, h125']; exact hv x⟩
          · exact .inr ⟨t, fun x => by
              show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
              simp only [hws', hw', BEq.rfl, Bool.false_eq_true, ↓reduceIte, h125']; exact ht x⟩
      have h44' : (c == 44) = false := by simpa using h44
      by_cases h34 : c = 34
      · subst h34
        by_cases hw : w = true
        · subst hw
          rcases naiveKeyBody_local l' hl' with h1 | ⟨key, r₁, hr₁, h1⟩
          · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedKey, fun x => by
              show naiveLineLoop (34 :: (l' ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
              simp [hws', h125', h44', h1 x]⟩⟩
          have hr₁n := not_mem_of_suffix hr₁ hl'
          rcases naiveValue_local r₁ hr₁n with h2 | ⟨r₂, hr₂, h2⟩
          · exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedColon, fun x => by
              show naiveLineLoop (34 :: (l' ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
              simp [hws', h125', h44', h1 x, h2 x]⟩⟩
          have hr₂n := not_mem_of_suffix hr₂ hr₁n
          have hr₂l : r₂ <:+ 34 :: l' := (hr₂.trans hr₁).trans (List.suffix_cons _ _)
          generalize hk : keyOf key = k
          cases k
          case kIn => line_idx IdxKey.«in»
          case kIl => line_idx IdxKey.il
          case kIe => line_idx IdxKey.ie
          case kBvar => line_num (fun n => LinePayload.expr (ExprRec.bvar n))
          case kSort => line_num (fun n => LinePayload.expr (ExprRec.sort n))
          case kSucc => line_num (fun n => LinePayload.level (LevelRec.succ n))
          case kParam => line_num (fun n => LinePayload.level (LevelRec.param n))
          case kMax => line_pair (fun a d => LinePayload.level (LevelRec.max a d))
          case kImax => line_pair (fun a d => LinePayload.level (LevelRec.imax a d))
          case kStr => line_pl naiveStrName_local LinePayload.name
          case kNum => line_pl naiveNumName_local LinePayload.name
          case kApp => line_pl naiveAppExpr_local LinePayload.expr
          case kLam => line_pl naiveLamExpr_local LinePayload.expr
          case kForallE => line_pl naiveForallExpr_local LinePayload.expr
          case kLetE => line_pl naiveLetExpr_local LinePayload.expr
          case kConst => line_pl naiveConstExpr_local LinePayload.expr
          case kProj => line_pl naiveProjExpr_local LinePayload.expr
          case kNatVal => line_pl naiveQuotedNat_local (fun n => LinePayload.expr (ExprRec.natVal n))
          case kStrVal => line_pl naiveStr_local (fun s => LinePayload.expr (ExprRec.strVal s))
          case kAxiom => line_pl naiveAxiomDecl_local LinePayload.decl
          case kDef => line_pl naiveDefDecl_local LinePayload.decl
          case kThm => line_pl naiveThmDecl_local LinePayload.decl
          case kOpaque => line_pl naiveOpaqueDecl_local LinePayload.decl
          case kQuot => line_pl naiveQuotDecl_local LinePayload.decl
          case kInductive => line_pl naiveIndDecl_local LinePayload.decl
          case kMeta => line_meta
          all_goals line_unknown
        · have hw' : w = false := by simpa using hw
          exact ⟨34 :: l', List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
            show naiveLineLoop (34 :: (l' ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
            simp [hws', h125', h44', hw']⟩⟩
      · have h34' : (c == 34) = false := by simpa using h34
        exact ⟨c :: l', List.suffix_rfl, .inr ⟨.expectedComma, fun x => by
          show naiveLineLoop (_ :: (_ ++ 10 :: x)) _ _ _ = _; rw [naiveLineLoop.eq_def]
          simp [hws', h125', h44', h34']⟩⟩

end LineLoop

/-- **The line is read inside its line.**  On `l ++ 10 :: x` with no
newline in `l`, `naiveLine` returns one record with the rest `x` — the
same record for every `x` — or fails at the same byte of `l` for every
`x`. -/
theorem naiveLine_local (l : List UInt8) (hl : 10 ∉ l) :
    (∃ r, ∀ x, naiveLine (l ++ 10 :: x) = .ok (r, some x) x) ∨
    (∃ t r', r' <:+ l ∧ ∀ x, naiveLine (l ++ 10 :: x) = .err t (r' ++ 10 :: x)) := by
  have hd := dropWhile_append_nl isWs isWs_nl l
  cases hdw : l.dropWhile isWs with
  | nil => exact .inl ⟨.blank, fun x => by unfold naiveLine; rw [hd, hdw]; rfl⟩
  | cons c l₁ =>
    have hcl : c :: l₁ <:+ l := hdw ▸ List.dropWhile_suffix _
    have hl₁ : 10 ∉ l₁ := not_mem_cons_tail (not_mem_of_suffix hcl hl)
    have hc10 : c ≠ 10 := cons_ne_nl (not_mem_of_suffix hcl hl)
    by_cases h123 : c = 123
    · subst h123
      obtain ⟨r₁, hr₁, h⟩ := naiveLineLoop_local l₁.length l₁ true none .absent (Nat.le_refl _) hl₁
      rcases h with ⟨v, hv⟩ | ⟨t, ht⟩
      · have hr₁n := not_mem_of_suffix hr₁ hl₁
        have hd1 := dropWhile_append_nl isWs isWs_nl r₁
        cases hdw1 : r₁.dropWhile isWs with
        | nil =>
          exact .inl ⟨v, fun x => by
            unfold naiveLine; rw [hd, hdw]; simp only [List.cons_append]
            rw [show naiveLineLoop (l₁ ++ 10 :: x) true none .absent = _ from hv x]
            simp only []; rw [hd1, hdw1]; rfl⟩
        | cons c₁ r₂ =>
          have hc₁ : c₁ ≠ 10 := cons_ne_nl (not_mem_of_suffix (hdw1 ▸ List.dropWhile_suffix _) hr₁n)
          refine .inr ⟨.trailing, c₁ :: r₂, ((hdw1 ▸ List.dropWhile_suffix _).trans hr₁).trans
            ((List.suffix_cons _ _).trans hcl), fun x => ?_⟩
          unfold naiveLine; rw [hd, hdw]; simp only [List.cons_append]
          rw [show naiveLineLoop (l₁ ++ 10 :: x) true none .absent = _ from hv x]
          simp only []; rw [hd1, hdw1]
          simp only [List.cons_append]
          split
          · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hc₁
          · rename_i heq; simp at heq
          · rfl
      · exact .inr ⟨t, r₁, hr₁.trans ((List.suffix_cons _ _).trans hcl), fun x => by
          unfold naiveLine; rw [hd, hdw]; simp only [List.cons_append]
          rw [show naiveLineLoop (l₁ ++ 10 :: x) true none .absent = _ from ht x]⟩
    · refine .inr ⟨.expectedObject, c :: l₁, hcl, fun x => ?_⟩
      unfold naiveLine; rw [hd, hdw]
      simp only [List.cons_append]
      split
      · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 hc10
      · rename_i heq; simp at heq
      · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h123
      · rfl

/-- A line the recogniser returns with `some rest`: the input is the
line up to its first newline, and `rest` is what follows. -/
theorem naiveLine_some {l : List UInt8} {r : LineRec} {rest rest' : List UInt8}
    (h : naiveLine l = .ok (r, some rest) rest') :
    ∃ pre, l = pre ++ 10 :: rest ∧ 10 ∉ pre ∧ rest' = rest := by
  by_cases hnl : 10 ∈ l
  · obtain ⟨pre, x, rfl, hpre⟩ := split_first_nl hnl
    rcases naiveLine_local pre hpre with ⟨r₀, h₀⟩ | ⟨t, r', _, h₀⟩
    · rw [h₀ x] at h
      simp only [NRes.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      exact ⟨pre, by rw [h.1.2], hpre, h.2.symm.trans h.1.2⟩
    · rw [h₀ x] at h; exact absurd h (by simp)
  · exfalso
    -- without a newline the line never returns `some`
    unfold naiveLine at h
    have hsuf := List.dropWhile_suffix (l := l) isWs
    split at h
    · rename_i heq; exact hnl (hsuf.subset (heq ▸ List.mem_cons_self ..))
    · simp at h
    · rename_i l' heq
      have hl' : 10 ∉ l' := fun hm => hnl (hsuf.subset (heq ▸ List.mem_cons_of_mem _ hm))
      split at h
      · simp at h
      · rename_i r₀ l₂ hloop
        have hl₂ : l₂ <:+ l' := by
          have := naiveLineLoop_rest_suffix l' true none .absent
          rw [hloop] at this; exact this
        split at h
        · rename_i heq2
          exact hl' (hl₂.subset ((List.dropWhile_suffix _).subset (heq2 ▸ List.mem_cons_self ..)))
        · simp at h
        · simp at h
    · simp at h

/-- A line the recogniser returns with `none` — the chunked reader's
incomplete tail — holds no newline. -/
theorem naiveLine_none {l : List UInt8} {r : LineRec} {rest : List UInt8}
    (h : naiveLine l = .ok (r, none) rest) : 10 ∉ l := by
  intro hnl
  obtain ⟨pre, x, rfl, hpre⟩ := split_first_nl hnl
  rcases naiveLine_local pre hpre with ⟨r₀, h₀⟩ | ⟨t, r', _, h₀⟩
  · rw [h₀ x] at h; simp at h
  · rw [h₀ x] at h; simp at h

end ConLeche.Frontend
