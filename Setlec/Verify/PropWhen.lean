import Setlec.Verify.Level

/-!
# The packed zero-ness datum: the bit battery (task #161; packed 2026-09-06)

`PropWhen` is the binder annotation of the validated-annotation
design — the reading of a codomain sort's zero-ness predicate
`Z(l) = {φ | eval φ l = 0}` — as a positional `UInt64` bitmask over
the current declaration's level-parameter list (`Kernel/Expr.lean`).
This file proves the design's load-bearing facts over the word:

* **Soundness of the readout** — `holds_maskOf?`: a datum the
  validation site accepted (`maskOf? ps l = some pw`) reads out the
  sort's true zero bit at *every* valuation; `holds_maskOf`: the total
  reader is exact at every valuation that is nonzero outside `ps`.
* **The instantiation laws** — `substPW_self` (identity at a
  declaration's own parameters, for data defined below the list's
  length) and `substPW_maskOf` / `maskOf_subst` (the substitution
  pushforward: reading zero-ness commutes with level instantiation
  into a new context).
* **The crossing** — `holds_substPW`: the instantiated datum's bit at
  `φ` is the datum's bit at the composed valuation (`denoteP`'s level
  crossing rides this at every binder).

Comparison needs no battery: with canonical words zero-ness agreement
*is* equality (`PropWhen.equiv a b := a == b`), so the former
containment-test completeness theorem and the `ZeroSet` canonical form
are gone.  All reasoning goes through `Nat.testBit` on `UInt64.toNat`;
`WF` (bit 63 clear unless `never`) is the invariant every operation
preserves and every union law needs.
-/

namespace Setlec.PropWhen

/-- `equiv` is reflexive (the fold's vacuous self-comparison steps). -/
theorem equiv_refl (p : PropWhen) : equiv p p = true := by simp [equiv]

/-- `equiv` is equality. -/
theorem eq_of_equiv {p q : PropWhen} (h : equiv p q = true) : p = q := by
  simpa [equiv] using h

/-! ## Bit-level toolkit -/

/-- The bit view of a word. -/
abbrev tb (pw : PropWhen) (i : Nat) : Bool := pw.toNat.testBit i

theorem tb_of_ge {pw : PropWhen} {i : Nat} (h : 64 ≤ i) : tb pw i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt_size pw)
    (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) h))

theorem ext_tb {a b : PropWhen} (h : ∀ i, i < 64 → tb a i = tb b i) : a = b := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · exact h i hi
  · have h1 := tb_of_ge (pw := a) (Nat.le_of_not_lt hi)
    have h2 := tb_of_ge (pw := b) (Nat.le_of_not_lt hi)
    simp only [tb] at h1 h2
    rw [h1, h2]

theorem toNat_toUInt64 {i : Nat} (h : i < 64) : i.toUInt64.toNat = i := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem toNat_never : never.toNat = 2 ^ 64 - 1 := by decide

@[simp] theorem tb_never (i : Nat) : tb never i = decide (i < 64) := by
  show never.toNat.testBit i = _
  rw [toNat_never, Nat.testBit_two_pow_sub_one]

@[simp] theorem tb_always (i : Nat) : tb always i = false := by
  show (always.toNat).testBit i = false
  simp [always]

theorem toNat_bit {i : Nat} (h : i < 63) : (bit i).toNat = 2 ^ i := by
  simp only [bit, if_pos h, UInt64.toNat_shiftLeft, UInt64.toNat_one]
  rw [toNat_toUInt64 (by omega), Nat.mod_eq_of_lt (by omega : i < 64),
    Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem tb_bit {i : Nat} (h : i < 63) (j : Nat) : tb (bit i) j = decide (i = j) := by
  show (bit i).toNat.testBit j = _
  rw [toNat_bit h, Nat.testBit_two_pow]

theorem bit_of_ge {i : Nat} (h : 63 ≤ i) : bit i = never := by
  simp [bit, Nat.not_lt.mpr h]

@[simp] theorem tb_inter (a b : PropWhen) (i : Nat) :
    tb (a.inter b) i = (tb a i || tb b i) := by
  show (a ||| b).toNat.testBit i = _
  rw [UInt64.toNat_or, Nat.testBit_or]

theorem tb_shiftRight (w : UInt64) (i : Nat) :
    tb (w >>> 1) i = tb w (i + 1) := by
  show (w >>> 1).toNat.testBit i = w.toNat.testBit (i + 1)
  rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, UInt64.toNat_one]
  simp [Nat.add_comm]

theorem and_one_eq_one_iff (w : UInt64) : ((w &&& 1) == 1) = tb w 0 := by
  show ((w &&& 1) == 1) = w.toNat.testBit 0
  rw [Nat.testBit_zero]
  have : (w &&& 1).toNat = w.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]
  cases h : (w &&& 1) == 1
  · have hne : (w &&& 1).toNat ≠ 1 := fun heq => by
      have : w &&& 1 = 1 := UInt64.toNat_inj.mp (by rw [heq]; rfl)
      simp [this] at h
    rw [this] at hne
    have : w.toNat % 2 ≠ 1 := hne
    simp [this]
  · have heq : w &&& 1 = 1 := by simpa using h
    have : w.toNat % 2 = 1 := by rw [← this, heq]; rfl
    simp [this]

theorem eq_zero_iff_tb (w : UInt64) : w = 0 ↔ ∀ i, i < 64 → tb w i = false := by
  constructor
  · rintro rfl i _; simp [tb]
  · intro h
    apply ext_tb
    intro i hi
    rw [h i hi]
    simp [tb]

theorem never_ne_always : never ≠ always := by decide

/-! ## Well-formedness: the reserved bit -/

/-- The invariant every datum the checker builds satisfies: `never`, or
bit `63` clear (a position at or beyond `maxParams` has no
representation — `bit` maps it to `never`).  Stated as the
`paramsDefined 63` test the checker already runs. -/
def WF (pw : PropWhen) : Prop := pw = never ∨ tb pw 63 = false

theorem WF.never : WF never := Or.inl rfl
theorem WF.always : WF always := Or.inr (by simp)
theorem WF.bit (i : Nat) : WF (bit i) := by
  by_cases h : i < 63
  · exact Or.inr (by rw [tb_bit h]; simp; omega)
  · rw [bit_of_ge (Nat.le_of_not_lt h)]; exact WF.never

/-- A word with bit 63 clear is not `never`. -/
theorem ne_never_of_tb63 {pw : PropWhen} (h : tb pw 63 = false) : pw ≠ never := by
  intro heq; rw [heq] at h; simp at h

theorem WF.inter {a b : PropWhen} (ha : WF a) (hb : WF b) : WF (a.inter b) := by
  rcases ha with rfl | ha
  · left; apply ext_tb; intro i hi; simp [hi]
  rcases hb with rfl | hb
  · left; apply ext_tb; intro i hi; simp [hi]
  · right; simp [ha, hb]

theorem inter_never_left (b : PropWhen) : never.inter b = never := by
  apply ext_tb; intro i hi; simp [hi]
theorem inter_never_right (a : PropWhen) : a.inter never = never := by
  apply ext_tb; intro i hi; simp [hi]
theorem inter_always_left (b : PropWhen) : always.inter b = b := by
  apply ext_tb; intro i _; simp
theorem inter_always_right (a : PropWhen) : a.inter always = a := by
  apply ext_tb; intro i _; simp

/-- The `|||` spellings (the loop's own). -/
theorem hor_never (a : PropWhen) : a ||| never = never := inter_never_right a
theorem tb_hor (a b : PropWhen) (i : Nat) : tb (a ||| b) i = (tb a i || tb b i) :=
  tb_inter a b i

/-- The union of two well-formed words is `never` iff one is. -/
theorem inter_eq_never_iff {a b : PropWhen} (ha : WF a) (hb : WF b) :
    a.inter b = never ↔ a = never ∨ b = never := by
  constructor
  · intro h
    by_cases h1 : a = never
    · exact Or.inl h1
    by_cases h2 : b = never
    · exact Or.inr h2
    exfalso
    have ha' : tb a 63 = false := ha.resolve_left h1
    have hb' : tb b 63 = false := hb.resolve_left h2
    have := congrArg (fun w => tb w 63) h
    simp [ha', hb'] at this
  · rintro (rfl | rfl)
    · exact inter_never_left b
    · exact inter_never_right a

/-! ## `holds` -/

theorem holds_iff {ψ : Nat → Nat} {pw : PropWhen} :
    holds ψ pw = true ↔ pw ≠ never ∧ ∀ i, i < 64 → tb pw i = true → ψ i = 0 := by
  unfold holds
  rw [Bool.and_eq_true, bne_iff_ne, List.all_eq_true]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun i hi hb => ?_⟩
    have := h i (List.mem_range.mpr hi)
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at this
    rcases this with h1 | h1
    · exact absurd hb (by simp [tb] at *; exact h1)
    · exact h1
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun i hi => ?_⟩
    have hi' := List.mem_range.mp hi
    by_cases hb : tb pw i = true
    · simp [h i hi' hb]
    · simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
      left; simpa [tb] using hb

theorem holds_never (ψ : Nat → Nat) : holds ψ never = false := by
  cases h : holds ψ never
  · rfl
  · exact absurd (holds_iff.mp h).1 (fun h => h rfl)

theorem holds_always (ψ : Nat → Nat) : holds ψ always = true :=
  holds_iff.mpr ⟨never_ne_always.symm, fun i _ h => by simp at h⟩

theorem holds_bit {i : Nat} (h : i < 63) (ψ : Nat → Nat) :
    holds ψ (bit i) = (ψ i == 0) := by
  cases hψ : ψ i == 0
  · cases hh : holds ψ (bit i)
    · rfl
    · exfalso
      have := (holds_iff.mp hh).2 i (by omega) (by rw [tb_bit h]; simp)
      simp [this] at hψ
  · apply holds_iff.mpr
    refine ⟨ne_never_of_tb63 (by rw [tb_bit h]; simp; omega), fun j _ hj => ?_⟩
    rw [tb_bit h] at hj
    have : i = j := by simpa using hj
    subst this
    simpa using hψ

theorem holds_inter {a b : PropWhen} (ha : WF a) (hb : WF b) (ψ : Nat → Nat) :
    holds ψ (a.inter b) = (holds ψ a && holds ψ b) := by
  by_cases hna : a = never
  · subst hna; simp [inter_never_left, holds_never]
  by_cases hnb : b = never
  · subst hnb; simp [inter_never_right, holds_never]
  have hne : a.inter b ≠ never := fun h => by
    rcases (inter_eq_never_iff ha hb).mp h with h | h <;> contradiction
  cases hab : (holds ψ a && holds ψ b)
  · cases hh : holds ψ (a.inter b)
    · rfl
    · exfalso
      have h := (holds_iff.mp hh).2
      have hA : holds ψ a = true := holds_iff.mpr ⟨hna, fun i hi hb => h i hi (by simp [hb])⟩
      have hB : holds ψ b = true := holds_iff.mpr ⟨hnb, fun i hi hb => h i hi (by simp [hb])⟩
      simp [hA, hB] at hab
  · rw [Bool.and_eq_true] at hab
    have hA := (holds_iff.mp hab.1).2
    have hB := (holds_iff.mp hab.2).2
    apply holds_iff.mpr
    refine ⟨hne, fun i hi h => ?_⟩
    rw [tb_inter, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hA i hi h
    · exact hB i hi h

/-- At the all-zero valuation every datum but `never` holds. -/
theorem holds_zero (pw : PropWhen) : holds (fun _ => 0) pw = (pw != never) := by
  cases h : pw == never
  · simp only [bne, h, Bool.not_false]
    exact holds_iff.mpr ⟨by simpa using h, fun _ _ _ => rfl⟩
  · have : pw = never := by simpa using h
    subst this; simp [holds_never]

/-- At the all-one valuation only `always` holds. -/
theorem holds_one (pw : PropWhen) : holds (fun _ => 1) pw = (pw == always) := by
  cases h : pw == always
  · cases hh : holds (fun _ => 1) pw
    · rfl
    · exfalso
      obtain ⟨hn, hb⟩ := holds_iff.mp hh
      have : pw = always := by
        apply ext_tb; intro i hi
        cases hi' : tb pw i
        · simp
        · exact absurd (hb i hi hi') (by decide)
      simp [this] at h
  · have : pw = always := by simpa using h
    subst this; simp [holds_always]

/-- Locality: a datum reads its valuation only at its set bits. -/
theorem holds_congr {ψ₁ ψ₂ : Nat → Nat} {pw : PropWhen}
    (h : ∀ i, i < 64 → tb pw i = true → ψ₁ i = ψ₂ i) :
    holds ψ₁ pw = holds ψ₂ pw := by
  cases h1 : holds ψ₁ pw <;> cases h2 : holds ψ₂ pw <;> try rfl
  · exfalso
    obtain ⟨hn, hb⟩ := holds_iff.mp h2
    have : holds ψ₁ pw = true := holds_iff.mpr ⟨hn, fun i hi ht => by
      rw [h i hi ht]; exact hb i hi ht⟩
    simp [this] at h1
  · exfalso
    obtain ⟨hn, hb⟩ := holds_iff.mp h1
    have : holds ψ₂ pw = true := holds_iff.mpr ⟨hn, fun i hi ht => by
      rw [← h i hi ht]; exact hb i hi ht⟩
    simp [this] at h2

/-! ## `paramsDefined` -/

theorem paramsDefined_iff {n : Nat} {pw : PropWhen} :
    pw.paramsDefined n = true ↔ pw = never ∨ ∀ i, n ≤ i → tb pw i = false := by
  unfold paramsDefined
  rw [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      intro i hi
      by_cases hn : n < 64
      · rw [if_pos hn] at h
        have h0 : pw >>> n.toUInt64 = 0 := by simpa using h
        by_cases hi64 : i < 64
        · have := congrArg (fun w => tb w (i - n)) h0
          simp only [tb] at this
          rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight] at this
          have hnn : n.toUInt64.toNat % 64 = n := by
            rw [toNat_toUInt64 hn]; exact Nat.mod_eq_of_lt hn
          rw [hnn, show n + (i - n) = i by omega] at this
          simpa using this
        · exact tb_of_ge (by omega)
      · exact tb_of_ge (by omega)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      by_cases hn : n < 64
      · rw [if_pos hn]
        simp only [beq_iff_eq]
        apply (eq_zero_iff_tb _).mpr
        intro i hi
        simp only [tb]
        rw [UInt64.toNat_shiftRight, Nat.testBit_shiftRight]
        have hnn : n.toUInt64.toNat % 64 = n := by
          rw [toNat_toUInt64 hn]; exact Nat.mod_eq_of_lt hn
        rw [hnn]
        exact h (n + i) (by omega)
      · rw [if_neg hn]

theorem paramsDefined_never (n : Nat) : never.paramsDefined n = true :=
  paramsDefined_iff.mpr (Or.inl rfl)

theorem paramsDefined_always (n : Nat) : always.paramsDefined n = true :=
  paramsDefined_iff.mpr (Or.inr fun _ _ => by simp)

theorem paramsDefined_bit {i n : Nat} (h : i < n) : (bit i).paramsDefined n = true := by
  by_cases hi : i < 63
  · exact paramsDefined_iff.mpr (Or.inr fun j hj => by rw [tb_bit hi]; simp; omega)
  · rw [bit_of_ge (Nat.le_of_not_lt hi)]; exact paramsDefined_never n

theorem paramsDefined_mono {m n : Nat} (h : m ≤ n) {pw : PropWhen}
    (hp : pw.paramsDefined m = true) : pw.paramsDefined n = true := by
  rcases paramsDefined_iff.mp hp with rfl | hp
  · exact paramsDefined_never n
  · exact paramsDefined_iff.mpr (Or.inr fun i hi => hp i (by omega))

theorem paramsDefined_inter_of {n : Nat} {p q : PropWhen}
    (hp : p.paramsDefined n = true) (hq : q.paramsDefined n = true) :
    (p.inter q).paramsDefined n = true := by
  rcases paramsDefined_iff.mp hp with rfl | hp
  · rw [inter_never_left]; exact paramsDefined_never n
  rcases paramsDefined_iff.mp hq with rfl | hq
  · rw [inter_never_right]; exact paramsDefined_never n
  exact paramsDefined_iff.mpr (Or.inr fun i hi => by simp [hp i hi, hq i hi])

/-- `WF` is `paramsDefined 63`. -/
theorem WF_iff {pw : PropWhen} : WF pw ↔ pw.paramsDefined 63 = true := by
  rw [paramsDefined_iff]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      intro i hi
      by_cases h63 : i = 63
      · subst h63; exact h
      · exact tb_of_ge (by omega)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (h 63 (Nat.le_refl _))

theorem WF.of_paramsDefined {n : Nat} (hn : n ≤ 63) {pw : PropWhen}
    (h : pw.paramsDefined n = true) : WF pw :=
  WF_iff.mpr (paramsDefined_mono hn h)

/-- Locality at a parameter count: a datum defined below `n` reads
its valuation only below `n`. -/
theorem holds_ext_lt {n : Nat} {pw : PropWhen} (hdef : pw.paramsDefined n = true)
    {ψ₁ ψ₂ : Nat → Nat} (h : ∀ i, i < n → ψ₁ i = ψ₂ i) :
    holds ψ₁ pw = holds ψ₂ pw := by
  rcases paramsDefined_iff.mp hdef with rfl | hd
  · simp [holds_never]
  · apply holds_congr
    intro i _ ht
    by_cases hi : i < n
    · exact h i hi
    · rw [hd i (Nat.le_of_not_lt hi)] at ht; exact absurd ht (by decide)

/-- Locality at a parameter count, up to the zero test: `holds` reads
its valuation only through `ψ i = 0`. -/
theorem holds_ext_zero {n : Nat} {pw : PropWhen} (hdef : pw.paramsDefined n = true)
    {ψ₁ ψ₂ : Nat → Nat} (h : ∀ i, i < n → (ψ₁ i = 0 ↔ ψ₂ i = 0)) :
    holds ψ₁ pw = holds ψ₂ pw := by
  rcases paramsDefined_iff.mp hdef with rfl | hd
  · simp [holds_never]
  · apply Bool.eq_iff_iff.mpr
    rw [holds_iff, holds_iff]
    constructor
    · rintro ⟨hn, hb⟩
      refine ⟨hn, fun i hi ht => ?_⟩
      have hlt : i < n := Nat.lt_of_not_le fun hl => by
        rw [hd i hl] at ht; exact absurd ht (by decide)
      exact (h i hlt).mp (hb i hi ht)
    · rintro ⟨hn, hb⟩
      refine ⟨hn, fun i hi ht => ?_⟩
      have hlt : i < n := Nat.lt_of_not_le fun hl => by
        rw [hd i hl] at ht; exact absurd ht (by decide)
      exact (h i hlt).mpr (hb i hi ht)

/-! ## `bindZ`: the specification of the bit loop -/

/-- Position `j` of the union of the masks selected by the set bits of
`w` (shifted by the recursion). -/
def Sel (ms : List PropWhen) (w : UInt64) (j : Nat) : Prop :=
  ∃ i, i < 64 ∧ tb w i = true ∧ ∃ m, ms[i]? = some m ∧ tb m j = true

/-- The set bits of `w` are all representable in `ms` and land on
non-`never` masks. -/
def Sound (ms : List PropWhen) (w : UInt64) : Prop :=
  ∀ i, i < 64 → tb w i = true → i < ms.length ∧ ms[i]? ≠ some never

theorem Sel_cons_iff {m : PropWhen} {rest : List PropWhen} {w : UInt64} {j : Nat} :
    Sel (m :: rest) w j ↔ (tb w 0 = true ∧ tb m j = true) ∨ Sel rest (w >>> 1) j := by
  constructor
  · rintro ⟨i, hi, ht, x, hx, hb⟩
    cases i with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx; exact ⟨ht, hb⟩
    | succ i =>
      right
      exact ⟨i, by omega, by rw [tb_shiftRight]; exact ht, x, by simpa using hx, hb⟩
  · rintro (⟨ht, hb⟩ | ⟨i, hi, ht, x, hx, hb⟩)
    · exact ⟨0, by decide, ht, m, rfl, hb⟩
    · refine ⟨i + 1, ?_, by rw [← tb_shiftRight]; exact ht, x, by simpa using hx, hb⟩
      by_cases h64 : i + 1 < 64
      · exact h64
      · exfalso
        rw [tb_shiftRight, tb_of_ge (by omega)] at ht
        exact absurd ht (by decide)

/-- The value of `bindZ.go` at a word: `never` when a set bit is beyond
`ms` or lands on a `never`; otherwise the selected union, bit by bit. -/
theorem bindZ_go_spec : ∀ (ms : List PropWhen) (w : UInt64),
    (∀ m ∈ ms, WF m) →
    ((∃ i, i < 64 ∧ tb w i = true ∧ (ms.length ≤ i ∨ ms[i]? = some never)) →
        bindZ.go ms w = never) ∧
    (Sound ms w →
        bindZ.go ms w ≠ never ∧
        ∀ j, j < 64 → (tb (bindZ.go ms w) j = true ↔ Sel ms w j))
  | [], w, _ => by
    simp only [bindZ.go, List.length_nil, List.getElem?_nil]
    constructor
    · rintro ⟨i, hi, ht, _⟩
      have : w ≠ 0 := fun h0 => by
        subst h0; simp [tb] at ht
      simp [this]
    · intro h
      have hw : w = 0 := (eq_zero_iff_tb w).mpr fun i hi => by
        cases ht : tb w i
        · rfl
        · exact absurd (h i hi ht).1 (by simp)
      subst hw
      simp only [beq_self_eq_true, ↓reduceIte]
      refine ⟨never_ne_always.symm, fun j _ => ?_⟩
      constructor
      · intro h; simp [tb] at h
      · rintro ⟨i, _, ht, _⟩; simp [tb] at ht
  | m :: rest, w, hwf => by
    have hwfm : WF m := hwf m (by simp)
    have hwfr : ∀ x ∈ rest, WF x := fun x hx => hwf x (by simp [hx])
    have ih := bindZ_go_spec rest (w >>> 1) hwfr
    simp only [bindZ.go]
    have h0 := and_one_eq_one_iff w
    constructor
    · rintro ⟨i, hi, ht, hbad⟩
      have hw : (w == 0) = false := by
        have : w ≠ 0 := fun h0 => by subst h0; simp [tb] at ht
        simpa using this
      rw [hw]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h0]
      cases i with
      | zero =>
        simp only [List.length_cons, List.getElem?_cons_zero, Option.some.injEq] at hbad
        rcases hbad with hbad | rfl
        · omega
        · rw [ht]; simp
      | succ i =>
        simp only [List.length_cons, List.getElem?_cons_succ] at hbad
        have hn : bindZ.go rest (w >>> 1) = never :=
          ih.1 ⟨i, by omega, by rw [tb_shiftRight]; exact ht, by
            rcases hbad with hbad | hbad
            · exact Or.inl (by omega)
            · exact Or.inr hbad⟩
        rw [hn, hor_never]
        split <;> split <;> rfl
    · intro h
      by_cases hw0 : w = 0
      · subst hw0
        simp only [beq_self_eq_true, ↓reduceIte]
        refine ⟨never_ne_always.symm, fun j _ => ?_⟩
        constructor
        · intro h; simp [tb] at h
        · rintro ⟨i, _, ht, _⟩; simp [tb] at ht
      have hw : (w == 0) = false := by simpa using hw0
      rw [hw]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h0]
      have hrest : Sound rest (w >>> 1) := by
        intro i hi ht
        rw [tb_shiftRight] at ht
        by_cases hi63 : i + 1 < 64
        · have := h (i + 1) hi63 ht
          simpa using this
        · rw [tb_of_ge (by omega)] at ht; exact absurd ht (by decide)
      obtain ⟨hne, hbits⟩ := ih.2 hrest
      have hhere : (if tb w 0 = true then m else always) ≠ never := by
        split
        · rename_i ht
          have := (h 0 (by decide) ht).2
          simpa using this
        · exact never_ne_always.symm
      have hhereB : ((if tb w 0 = true then m else always) == never) = false := by
        simpa using hhere
      rw [hhereB]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hwfh : WF (if tb w 0 = true then m else always) := by
        split
        · exact hwfm
        · exact WF.always
      have hwfrest : WF (bindZ.go rest (w >>> 1)) := by
        right
        cases hb : tb (bindZ.go rest (w >>> 1)) 63
        · rfl
        · exfalso
          obtain ⟨i, hi, ht, x, hx, hxb⟩ := (hbits 63 (by decide)).mp hb
          rcases hwfr x (List.mem_of_getElem? hx) with rfl | hx'
          · exact (hrest i hi ht).2 hx
          · rw [hx'] at hxb; exact absurd hxb (by decide)
      refine ⟨?_, ?_⟩
      · intro hn
        rcases (inter_eq_never_iff hwfh hwfrest).mp hn with hn | hn
        · exact hhere hn
        · exact hne hn
      · intro j hj
        rw [Sel_cons_iff, tb_hor, Bool.or_eq_true, hbits j hj]
        cases ht0 : tb w 0
        · simp only [Bool.false_eq_true, ↓reduceIte, tb_always, false_or, false_and]
        · simp only [↓reduceIte, true_and]

/-- `bindZ` at a well-formed mask list: `never` exactly when the input
is `never` or a set bit is unrepresentable/lands on `never`; otherwise
the union of the selected masks. -/
theorem bindZ_spec (ms : List PropWhen) (pw : PropWhen) (hwf : ∀ m ∈ ms, WF m) :
    ((∃ i, i < 64 ∧ tb pw i = true ∧ (ms.length ≤ i ∨ ms[i]? = some never)) →
        bindZ ms pw = never) ∧
    ((pw ≠ never ∧ Sound ms pw) →
        bindZ ms pw ≠ never ∧
        ∀ j, j < 64 → (tb (bindZ ms pw) j = true ↔ Sel ms pw j)) := by
  have hs := bindZ_go_spec ms pw hwf
  unfold bindZ
  constructor
  · intro h
    by_cases hne : pw = never
    · subst hne; simp
    · have : (pw == never) = false := by simpa using hne
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hs.1 h
  · rintro ⟨hne, h⟩
    have : (pw == never) = false := by simpa using hne
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hs.2 h

theorem bindZ_never (ms : List PropWhen) : bindZ ms never = never := by
  simp [bindZ]

/-- A defined datum's set bits are below the count. -/
theorem tb_lt_of_paramsDefined {n : Nat} {pw : PropWhen} (hne : pw ≠ never)
    (hdef : pw.paramsDefined n = true) {i : Nat} (ht : tb pw i = true) : i < n := by
  rcases paramsDefined_iff.mp hdef with h | h
  · exact absurd h hne
  · exact Nat.lt_of_not_le fun hl => by
      rw [h i hl] at ht; exact absurd ht (by decide)

/-- The witness of a failed soundness test. -/
theorem not_sound {ms : List PropWhen} {w : UInt64} (h : ¬ Sound ms w) :
    ∃ i, i < 64 ∧ tb w i = true ∧ (ms.length ≤ i ∨ ms[i]? = some never) := by
  apply Classical.byContradiction
  intro hno
  apply h
  intro i hi ht
  constructor
  · exact Nat.lt_of_not_le fun hl => hno ⟨i, hi, ht, Or.inl hl⟩
  · intro hn; exact hno ⟨i, hi, ht, Or.inr hn⟩

/-- `bindZ` at well-formed masks is well-formed. -/
theorem WF.bindZ {ms : List PropWhen} (hwf : ∀ m ∈ ms, WF m) (pw : PropWhen) :
    WF (PropWhen.bindZ ms pw) := by
  by_cases hne : pw = PropWhen.never
  · subst hne; rw [PropWhen.bindZ_never]; exact WF.never
  by_cases hb : Sound ms pw
  · obtain ⟨-, hbits⟩ := (bindZ_spec ms pw hwf).2 ⟨hne, hb⟩
    right
    cases h63 : tb (PropWhen.bindZ ms pw) 63
    · rfl
    · exfalso
      obtain ⟨i, hi, ht, x, hx, hxb⟩ := (hbits 63 (by decide)).mp h63
      rcases hwf x (List.mem_of_getElem? hx) with rfl | hx'
      · exact (hb i hi ht).2 hx
      · rw [hx'] at hxb; exact absurd hxb (by decide)
  · exact Or.inl ((bindZ_spec ms pw hwf).1 (not_sound hb))

theorem bindZ_paramsDefined {ms : List PropWhen} {n : Nat}
    (hwf : ∀ m ∈ ms, WF m) (hdef : ∀ m ∈ ms, m.paramsDefined n = true)
    (pw : PropWhen) : (bindZ ms pw).paramsDefined n = true := by
  by_cases hne : pw = never
  · subst hne; rw [bindZ_never]; exact paramsDefined_never n
  by_cases hb : Sound ms pw
  · obtain ⟨-, hbits⟩ := (bindZ_spec ms pw hwf).2 ⟨hne, hb⟩
    apply paramsDefined_iff.mpr
    right
    intro j hj
    by_cases hj64 : j < 64
    · cases hbj : tb (bindZ ms pw) j
      · rfl
      · exfalso
        obtain ⟨i, hi, ht, x, hx, hxj⟩ := (hbits j hj64).mp hbj
        have hd := hdef x (List.mem_of_getElem? hx)
        rcases paramsDefined_iff.mp hd with rfl | hd'
        · exact (hb i hi ht).2 hx
        · rw [hd' j hj] at hxj; exact absurd hxj (by decide)
    · exact tb_of_ge (by omega)
  · rw [(bindZ_spec ms pw hwf).1 (not_sound hb)]
    exact paramsDefined_never n

/-- **`holds` through `bindZ`**: the union of the selected masks holds
iff the input holds at the valuation reading each position's mask. -/
theorem holds_bindZ {ms : List PropWhen} (hwf : ∀ m ∈ ms, WF m)
    {n : Nat} (hlen : ms.length = n) {pw : PropWhen}
    (hdef : pw.paramsDefined n = true) (ψ : Nat → Nat) :
    holds ψ (bindZ ms pw) =
      holds (fun i => if holds ψ (ms.getD i never) then 0 else 1) pw := by
  by_cases hne : pw = never
  · subst hne; rw [bindZ_never, holds_never, holds_never]
  have hdef' : ∀ i, i < 64 → tb pw i = true → i < ms.length := by
    intro i _ ht
    rw [hlen]; exact tb_lt_of_paramsDefined hne hdef ht
  by_cases hb : ∀ i, i < 64 → tb pw i = true → ms[i]? ≠ some never
  · obtain ⟨hne', hbits⟩ := (bindZ_spec ms pw hwf).2 ⟨hne, fun i hi ht => ⟨hdef' i hi ht, hb i hi ht⟩⟩
    apply Bool.eq_iff_iff.mpr
    rw [holds_iff, holds_iff]
    constructor
    · rintro ⟨-, h⟩
      refine ⟨hne, fun i hi ht => ?_⟩
      have hi' := hdef' i hi ht
      have hget : ms.getD i never = ms[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
      rw [hget]
      have hmi : holds ψ ms[i] = true := by
        apply holds_iff.mpr
        refine ⟨fun hn => hb i hi ht (by rw [List.getElem?_eq_getElem hi', hn]), fun j hj hbj => ?_⟩
        apply h j hj
        exact (hbits j hj).mpr ⟨i, hi, ht, ms[i], List.getElem?_eq_getElem hi', hbj⟩
      simp [hmi]
    · rintro ⟨-, h⟩
      refine ⟨hne', fun j hj hbj => ?_⟩
      obtain ⟨i, hi, ht, x, hx, hxj⟩ := (hbits j hj).mp hbj
      have hget : ms.getD i never = x := by
        rw [List.getD_eq_getElem?_getD, hx]; rfl
      have := h i hi ht
      rw [hget] at this
      by_cases hh : holds ψ x = true
      · exact (holds_iff.mp hh).2 j hj hxj
      · simp [hh] at this
  · have hns : ¬ Sound ms pw := fun hs => hb fun i hi ht => (hs i hi ht).2
    obtain ⟨i, hi, ht, hbad⟩ := not_sound hns
    have hbad' : ms[i]? = some never := by
      rcases hbad with hl | hn
      · exact absurd (hdef' i hi ht) (Nat.not_lt.mpr hl)
      · exact hn
    rw [(bindZ_spec ms pw hwf).1 ⟨i, hi, ht, Or.inr hbad'⟩, holds_never]
    symm
    cases hh : holds (fun i => if holds ψ (ms.getD i never) then 0 else 1) pw
    · rfl
    · exfalso
      have := (holds_iff.mp hh).2 i hi ht
      have hget : ms.getD i never = never := by
        rw [List.getD_eq_getElem?_getD, hbad']; rfl
      rw [hget, holds_never] at this
      simp at this

/-- `bindZ` at singleton masks `bit i` (below the list's length and
below `63`) reproduces the datum. -/
theorem bindZ_bits {ms : List PropWhen} (hms : ∀ i, i < ms.length → ms[i]? = some (bit i))
    (hlen : ms.length ≤ 63) {pw : PropWhen}
    (hdef : pw.paramsDefined ms.length = true) : bindZ ms pw = pw := by
  have hwf : ∀ m ∈ ms, WF m := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have := hms i hi
    simp only [List.getElem?_eq_getElem hi, Option.some.injEq] at this
    rw [this]; exact WF.bit i
  by_cases hne : pw = never
  · subst hne; exact bindZ_never ms
  have hdef' : ∀ i, i < 64 → tb pw i = true → i < ms.length := fun i _ ht =>
    tb_lt_of_paramsDefined hne hdef ht
  have hbitne : ∀ i, i < 63 → bit i ≠ never := by
    intro i hi h
    have := congrArg (fun w => tb w 63) h
    rw [tb_bit hi] at this
    simp [show i ≠ 63 by omega] at this
  have hb : Sound ms pw := by
    intro i hi ht
    have hi' := hdef' i hi ht
    refine ⟨hi', ?_⟩
    rw [hms i hi']
    intro h
    exact hbitne i (by omega) (by simpa using h)
  obtain ⟨-, hbits⟩ := (bindZ_spec ms pw hwf).2 ⟨hne, hb⟩
  apply ext_tb
  intro j hj
  apply Bool.eq_iff_iff.mpr
  rw [hbits j hj]
  constructor
  · rintro ⟨i, hi, ht, x, hx, hxj⟩
    have hi' := hdef' i hi ht
    rw [hms i hi'] at hx
    simp only [Option.some.injEq] at hx
    subst hx
    rw [tb_bit (by omega)] at hxj
    have : i = j := by simpa using hxj
    subst this; exact ht
  · intro ht
    have hj' := hdef' j hj ht
    exact ⟨j, hj, ht, bit j, hms j hj', by rw [tb_bit (by omega)]; simp⟩

/-! ## `bindZ` algebra: singletons, unions, composition -/

/-- `bindZ` at a singleton position is the selected mask. -/
theorem bindZ_bit {ms : List PropWhen} (hwf : ∀ m ∈ ms, WF m) {i : Nat}
    (hi : i < 63) (hlen : i < ms.length) : bindZ ms (bit i) = ms[i] := by
  have hbitne : bit i ≠ never := by
    intro h
    have := congrArg (fun w => tb w 63) h
    rw [tb_bit hi] at this
    simp [show i ≠ 63 by omega] at this
  by_cases hn : ms[i] = never
  · rw [hn]
    exact (bindZ_spec ms (bit i) hwf).1 ⟨i, by omega, by rw [tb_bit hi]; simp,
      Or.inr (by rw [List.getElem?_eq_getElem hlen, hn])⟩
  · have hs : Sound ms (bit i) := by
      intro k hk ht
      rw [tb_bit hi] at ht
      have : i = k := by simpa using ht
      subst this
      exact ⟨hlen, by rw [List.getElem?_eq_getElem hlen]; intro h; exact hn (Option.some.inj h)⟩
    obtain ⟨-, hbits⟩ := (bindZ_spec ms (bit i) hwf).2 ⟨hbitne, hs⟩
    apply ext_tb
    intro j hj
    apply Bool.eq_iff_iff.mpr
    rw [hbits j hj]
    constructor
    · rintro ⟨k, hk, ht, x, hx, hxj⟩
      rw [tb_bit hi] at ht
      have : i = k := by simpa using ht
      subst this
      rw [List.getElem?_eq_getElem hlen] at hx
      rw [Option.some.inj hx]; exact hxj
    · intro ht
      exact ⟨i, by omega, by rw [tb_bit hi]; simp, ms[i], List.getElem?_eq_getElem hlen, ht⟩

theorem Sel_inter_iff {ms : List PropWhen} {a b : PropWhen} {j : Nat} :
    Sel ms (a.inter b) j ↔ Sel ms a j ∨ Sel ms b j := by
  constructor
  · rintro ⟨i, hi, ht, x, hx, hxj⟩
    rw [tb_inter, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · exact Or.inl ⟨i, hi, ht, x, hx, hxj⟩
    · exact Or.inr ⟨i, hi, ht, x, hx, hxj⟩
  · rintro (⟨i, hi, ht, x, hx, hxj⟩ | ⟨i, hi, ht, x, hx, hxj⟩)
    · exact ⟨i, hi, by rw [tb_inter, ht]; rfl, x, hx, hxj⟩
    · exact ⟨i, hi, by rw [tb_inter, ht]; simp, x, hx, hxj⟩

/-- `bindZ` distributes over the union (with `never` absorbing). -/
theorem bindZ_inter {ms : List PropWhen} (hwf : ∀ m ∈ ms, WF m) {a b : PropWhen}
    (ha : WF a) (hb : WF b) :
    bindZ ms (a.inter b) = (bindZ ms a).inter (bindZ ms b) := by
  by_cases hna : a = never
  · subst hna; rw [inter_never_left, bindZ_never, inter_never_left]
  by_cases hnb : b = never
  · subst hnb; rw [inter_never_right, bindZ_never, inter_never_right]
  have hnab : a.inter b ≠ never := fun h => by
    rcases (inter_eq_never_iff ha hb).mp h with h | h <;> contradiction
  by_cases hsa : Sound ms a
  · by_cases hsb : Sound ms b
    · have hsab : Sound ms (a.inter b) := by
        intro i hi ht
        rw [tb_inter, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact hsa i hi ht
        · exact hsb i hi ht
      obtain ⟨-, hbits⟩ := (bindZ_spec ms _ hwf).2 ⟨hnab, hsab⟩
      obtain ⟨-, hbitsa⟩ := (bindZ_spec ms _ hwf).2 ⟨hna, hsa⟩
      obtain ⟨-, hbitsb⟩ := (bindZ_spec ms _ hwf).2 ⟨hnb, hsb⟩
      apply ext_tb
      intro j hj
      rw [tb_inter]
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, hbits j hj, hbitsa j hj, hbitsb j hj]
      exact Sel_inter_iff
    · obtain ⟨i, hi, ht, hbad⟩ := not_sound hsb
      rw [(bindZ_spec ms b hwf).1 ⟨i, hi, ht, hbad⟩, inter_never_right]
      exact (bindZ_spec ms _ hwf).1 ⟨i, hi, by rw [tb_inter, ht]; simp, hbad⟩
  · obtain ⟨i, hi, ht, hbad⟩ := not_sound hsa
    rw [(bindZ_spec ms a hwf).1 ⟨i, hi, ht, hbad⟩, inter_never_left]
    exact (bindZ_spec ms _ hwf).1 ⟨i, hi, by rw [tb_inter, ht]; rfl, hbad⟩

/-- **Composition**: binding twice is binding once at the composed
masks.  Unconditional in the datum (bit algebra); the mask lists are
well-formed. -/
theorem bindZ_bindZ {ms₁ ms₂ : List PropWhen} (hwf₁ : ∀ m ∈ ms₁, WF m)
    (hwf₂ : ∀ m ∈ ms₂, WF m) (pw : PropWhen) :
    bindZ ms₂ (bindZ ms₁ pw) = bindZ (ms₁.map (bindZ ms₂)) pw := by
  have hwfm : ∀ m ∈ ms₁.map (bindZ ms₂), WF m := by
    intro m hm
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hm
    exact WF.bindZ hwf₂ x
  have hlen : (ms₁.map (bindZ ms₂)).length = ms₁.length := List.length_map ..
  by_cases hne : pw = never
  · subst hne; simp [bindZ_never]
  by_cases hs₁ : Sound ms₁ pw
  · obtain ⟨hne₁, hbits₁⟩ := (bindZ_spec ms₁ pw hwf₁).2 ⟨hne, hs₁⟩
    by_cases hs₂ : Sound ms₂ (bindZ ms₁ pw)
    · obtain ⟨-, hbits₂⟩ := (bindZ_spec ms₂ _ hwf₂).2 ⟨hne₁, hs₂⟩
      -- the mapped list is sound at `pw`
      have hsm : Sound (ms₁.map (bindZ ms₂)) pw := by
        intro i hi ht
        have hi' := (hs₁ i hi ht).1
        refine ⟨by rw [hlen]; exact hi', ?_⟩
        rw [List.getElem?_map, List.getElem?_eq_getElem hi']
        simp only [Option.map_some, ne_eq, Option.some.injEq]
        intro hn
        have hne_i : ms₁[i] ≠ never := fun h => (hs₁ i hi ht).2 (by rw [List.getElem?_eq_getElem hi', h])
        have hsi : Sound ms₂ ms₁[i] := by
          intro k hk htk
          exact hs₂ k hk ((hbits₁ k hk).mpr ⟨i, hi, ht, ms₁[i], List.getElem?_eq_getElem hi', htk⟩)
        exact ((bindZ_spec ms₂ _ hwf₂).2 ⟨hne_i, hsi⟩).1 hn
      obtain ⟨-, hbitsm⟩ := (bindZ_spec _ pw hwfm).2 ⟨hne, hsm⟩
      apply ext_tb
      intro j hj
      apply Bool.eq_iff_iff.mpr
      rw [hbits₂ j hj, hbitsm j hj]
      constructor
      · rintro ⟨k, hk, htk, y, hy, hyj⟩
        obtain ⟨i, hi, ht, x, hx, hxk⟩ := (hbits₁ k hk).mp htk
        have hi' := (hs₁ i hi ht).1
        rw [List.getElem?_eq_getElem hi'] at hx
        have hx' : x = ms₁[i] := (Option.some.inj hx).symm
        subst hx'
        have hne_i : ms₁[i] ≠ never := fun h => (hs₁ i hi ht).2 (by rw [List.getElem?_eq_getElem hi', h])
        have hsi : Sound ms₂ ms₁[i] := by
          intro k' hk' htk'
          exact hs₂ k' hk' ((hbits₁ k' hk').mpr ⟨i, hi, ht, ms₁[i], List.getElem?_eq_getElem hi', htk'⟩)
        obtain ⟨-, hbi⟩ := (bindZ_spec ms₂ _ hwf₂).2 ⟨hne_i, hsi⟩
        refine ⟨i, hi, ht, bindZ ms₂ ms₁[i], ?_, (hbi j hj).mpr ⟨k, hk, hxk, y, hy, hyj⟩⟩
        rw [List.getElem?_map, List.getElem?_eq_getElem hi']; rfl
      · rintro ⟨i, hi, ht, z, hz, hzj⟩
        have hi' := (hs₁ i hi ht).1
        rw [List.getElem?_map, List.getElem?_eq_getElem hi'] at hz
        have hz' : z = bindZ ms₂ ms₁[i] := (Option.some.inj hz).symm
        subst hz'
        have hne_i : ms₁[i] ≠ never := fun h => (hs₁ i hi ht).2 (by rw [List.getElem?_eq_getElem hi', h])
        have hsi : Sound ms₂ ms₁[i] := by
          intro k' hk' htk'
          exact hs₂ k' hk' ((hbits₁ k' hk').mpr ⟨i, hi, ht, ms₁[i], List.getElem?_eq_getElem hi', htk'⟩)
        obtain ⟨-, hbi⟩ := (bindZ_spec ms₂ _ hwf₂).2 ⟨hne_i, hsi⟩
        obtain ⟨k, hk, htk, y, hy, hyj⟩ := (hbi j hj).mp hzj
        exact ⟨k, hk, (hbits₁ k hk).mpr ⟨i, hi, ht, ms₁[i], List.getElem?_eq_getElem hi', htk⟩, y, hy, hyj⟩
    · -- a bad bit of the inner result: the mapped mask at its origin is never
      obtain ⟨k, hk, htk, hbad⟩ := not_sound hs₂
      rw [(bindZ_spec ms₂ _ hwf₂).1 ⟨k, hk, htk, hbad⟩]
      obtain ⟨i, hi, ht, x, hx, hxk⟩ := (hbits₁ k hk).mp htk
      have hi' := (hs₁ i hi ht).1
      rw [List.getElem?_eq_getElem hi'] at hx
      have hx' : x = ms₁[i] := (Option.some.inj hx).symm
      subst hx'
      symm
      apply (bindZ_spec _ pw hwfm).1
      refine ⟨i, hi, ht, Or.inr ?_⟩
      rw [List.getElem?_map, List.getElem?_eq_getElem hi']
      simp only [Option.map_some, Option.some.injEq]
      exact (bindZ_spec ms₂ _ hwf₂).1 ⟨k, hk, hxk, hbad⟩
  · obtain ⟨i, hi, ht, hbad⟩ := not_sound hs₁
    rw [(bindZ_spec ms₁ pw hwf₁).1 ⟨i, hi, ht, hbad⟩, bindZ_never]
    symm
    apply (bindZ_spec _ pw hwfm).1
    refine ⟨i, hi, ht, ?_⟩
    rcases hbad with hl | hn
    · exact Or.inl (by rw [hlen]; exact hl)
    · right
      rw [List.getElem?_map, hn]
      simp [bindZ_never]

end Setlec.PropWhen

namespace Setlec.Level

open Setlec.PropWhen

/-! ## `posOf` -/

theorem posOf_go_some : ∀ {ps : List Name} {n : Name} {k i : Nat},
    posOf.go n ps k = some i → k ≤ i ∧ i - k < ps.length ∧ ps[i - k]? = some n
  | [], n, k, i, h => by simp [posOf.go] at h
  | p :: ps, n, k, i, h => by
    simp only [posOf.go] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨Nat.le_refl _, by simp, ?_⟩
      simp only [Nat.sub_self, List.getElem?_cons_zero]
      have : p = n := by simpa using hp
      rw [this]
    · obtain ⟨h1, h2, h3⟩ := posOf_go_some h
      refine ⟨by omega, by simp; omega, ?_⟩
      rw [show i - k = (i - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      exact h3

theorem posOf_go_none : ∀ {ps : List Name} {n : Name} {k : Nat},
    posOf.go n ps k = none → n ∉ ps
  | [], n, k, _ => by simp
  | p :: ps, n, k, h => by
    simp only [posOf.go] at h
    split at h
    · exact nomatch h
    · rename_i hp
      have := posOf_go_none h
      simp only [List.mem_cons, not_or]
      exact ⟨fun he => hp (by simp [he]), this⟩

theorem posOf_some {ps : List Name} {n : Name} {i : Nat} (h : posOf ps n = some i) :
    i < ps.length ∧ ps[i]? = some n := by
  have := posOf_go_some (k := 0) h
  simpa using this

theorem posOf_none {ps : List Name} {n : Name} (h : posOf ps n = none) : n ∉ ps :=
  posOf_go_none h

theorem posOf_go_isSome_of_mem : ∀ {ps : List Name} {n : Name} (k : Nat),
    n ∈ ps → (posOf.go n ps k).isSome = true
  | [], n, _, h => by simp at h
  | p :: ps, n, k, h => by
    simp only [posOf.go]
    split
    · rfl
    · rename_i hp
      have hn : n ∈ ps := by
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact absurd (by simp) hp
        · exact h
      exact posOf_go_isSome_of_mem (k + 1) hn

theorem posOf_of_mem {ps : List Name} {n : Name} (h : n ∈ ps) :
    ∃ i, posOf ps n = some i := by
  have := posOf_go_isSome_of_mem (ps := ps) (n := n) 0 h
  cases hp : posOf ps n
  · rw [posOf] at hp; rw [hp] at this; exact nomatch this
  · exact ⟨_, rfl⟩

/-- Under `Nodup`, the position is the (unique) index: `ps[i] = n →
posOf ps n = some i`. -/
theorem posOf_go_of_nodup : ∀ {ps : List Name} (k : Nat), ps.Nodup →
    ∀ {i : Nat} {n : Name}, ps[i]? = some n → posOf.go n ps k = some (k + i)
  | [], _, _, i, n, h => by simp at h
  | p :: ps, k, hnd, i, n, h => by
    simp only [posOf.go]
    have hnd' := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : n ∈ ps := List.mem_of_getElem? h
      have hne : p ≠ n := fun he => hnd'.1 (he ▸ hmem)
      rw [if_neg (by simpa using hne), posOf_go_of_nodup (k + 1) hnd'.2 h]
      congr 1; omega

theorem posOf_of_nodup {ps : List Name} (hnd : ps.Nodup) {i : Nat} {n : Name}
    (h : ps[i]? = some n) : posOf ps n = some i := by
  have := posOf_go_of_nodup (ps := ps) 0 hnd h
  simpa [posOf] using this

/-! ## `maskOf` -/

theorem maskOf_zero (ps : List Name) : maskOf ps .zero = .always := rfl
theorem maskOf_succ (ps : List Name) (u : Level) : maskOf ps (.succ u) = .never := rfl
theorem maskOf_max (ps : List Name) (a b : Level) :
    maskOf ps (.max a b) = (maskOf ps a).inter (maskOf ps b) := rfl
theorem maskOf_imax (ps : List Name) (a b : Level) :
    maskOf ps (.imax a b) = maskOf ps b := rfl

theorem WF.maskOf (ps : List Name) : ∀ l : Level, WF (maskOf ps l)
  | .zero => WF.always
  | .succ _ => WF.never
  | .param n => by
    simp only [Level.maskOf]
    split
    · exact WF.bit _
    · exact WF.never
  | .max a b => (WF.maskOf ps a).inter (WF.maskOf ps b)
  | .imax _ b => WF.maskOf ps b

/-- The reader's footprint is the list's length. -/
theorem maskOf_paramsDefined (ps : List Name) :
    ∀ l : Level, (maskOf ps l).paramsDefined ps.length = true
  | .zero => paramsDefined_always _
  | .succ _ => paramsDefined_never _
  | .param n => by
    simp only [Level.maskOf]
    split
    · rename_i i hi
      exact paramsDefined_bit (posOf_some hi).1
    · exact paramsDefined_never _
  | .max a b => paramsDefined_inter_of (maskOf_paramsDefined ps a) (maskOf_paramsDefined ps b)
  | .imax _ b => maskOf_paramsDefined ps b

theorem maskOf?_eq {ps : List Name} : ∀ {l : Level} {pw : PropWhen},
    maskOf? ps l = some pw → maskOf ps l = pw
  | .zero, pw, h => by simp only [maskOf?, Option.some.injEq] at h; exact h
  | .succ _, pw, h => by simp only [maskOf?, Option.some.injEq] at h; exact h
  | .param n, pw, h => by
    simp only [maskOf?, maskOf] at h ⊢
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; exact h
      · exact nomatch h
    · exact nomatch h
  | .max a b, pw, h => by
    simp only [maskOf?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hxy⟩ := h
    have hxy' : x.inter y = pw := Option.some.inj hxy
    subst hxy'
    rw [maskOf_max, maskOf?_eq hx, maskOf?_eq hy]
  | .imax a b, pw, h => maskOf?_eq (l := b) h

/-- Where the validation reader answers, the answer is defined below
the reserved bit (no position at or beyond `maxParams`). -/
theorem maskOf?_wf63 {ps : List Name} : ∀ {l : Level} {pw : PropWhen},
    maskOf? ps l = some pw → WF pw
  | .zero, pw, h => by simp only [maskOf?, Option.some.injEq] at h; subst h; exact WF.always
  | .succ _, pw, h => by simp only [maskOf?, Option.some.injEq] at h; subst h; exact WF.never
  | .param n, pw, h => by
    simp only [maskOf?] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact WF.bit _
      · exact nomatch h
    · exact nomatch h
  | .max a b, pw, h => by
    simp only [maskOf?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hxy⟩ := h
    have hxy' : x.inter y = pw := Option.some.inj hxy
    subst hxy'
    exact (maskOf?_wf63 hx).inter (maskOf?_wf63 hy)
  | .imax a b, pw, h => maskOf?_wf63 (l := b) h

/-- The positional valuation read through a context. -/
def valAt (ps : List Name) (φ : Name → Nat) : Nat → Nat :=
  fun i => φ (ps.getD i .anonymous)

private theorem beq_zero_and (x y : Nat) :
    ((x == 0) && (y == 0)) = (Max.max x y == 0) := by
  cases hx : x == 0 <;> cases hy : y == 0 <;> simp_all <;> omega

/-- **Soundness of the validation reader**: an accepted datum reads
out the sort's zero bit at *every* valuation. -/
theorem holds_maskOf? {ps : List Name} (φ : Name → Nat) :
    ∀ {l : Level} {pw : PropWhen}, maskOf? ps l = some pw →
      holds (valAt ps φ) pw = (Level.eval φ l == 0)
  | .zero, pw, h => by
    simp only [maskOf?, Option.some.injEq] at h; subst h
    simp [holds_always, Level.eval]
  | .succ _, pw, h => by
    simp only [maskOf?, Option.some.injEq] at h; subst h
    simp [holds_never, Level.eval]
  | .param n, pw, h => by
    simp only [maskOf?] at h
    split at h
    · rename_i i hi
      split at h
      · rename_i hlt
        simp only [Option.some.injEq] at h; subst h
        rw [holds_bit hlt]
        simp only [valAt, Level.eval]
        obtain ⟨hil, hget⟩ := posOf_some hi
        rw [List.getD_eq_getElem?_getD, hget]
        rfl
      · exact nomatch h
    · exact nomatch h
  | .max a b, pw, h => by
    simp only [maskOf?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hxy⟩ := h
    have hxy' : x.inter y = pw := Option.some.inj hxy
    subst hxy'
    rw [holds_inter (maskOf?_wf63 hx) (maskOf?_wf63 hy), holds_maskOf? φ hx,
      holds_maskOf? φ hy, beq_zero_and]
    rfl
  | .imax a b, pw, h => by
    rw [holds_maskOf? φ (l := b) h]
    show _ = ((if Level.eval φ b = 0 then 0
      else Max.max (Level.eval φ a) (Level.eval φ b)) == 0)
    by_cases hb : Level.eval φ b = 0
    · simp [hb]
    · have hm : ¬ Max.max (Level.eval φ a) (Level.eval φ b) = 0 := by omega
      have h1 : (Level.eval φ b == 0) = false := by simpa using hb
      have h2 : (Max.max (Level.eval φ a) (Level.eval φ b) == 0) = false := by simpa using hm
      rw [h1, if_neg hb, h2]

/-- A valuation that is nonzero outside the context: the class at which
the total reader is exact (`holds_maskOf`) — an unrepresentable
parameter reads `never`, which is the truth wherever it is nonzero. -/
def NonzeroOutside (ps : List Name) (φ : Name → Nat) : Prop :=
  ∀ n, n ∉ ps → φ n ≠ 0

/-- **Soundness of the total reader** at every valuation nonzero
outside `ps`, for a context of at most `maxParams` parameters. -/
theorem holds_maskOf {ps : List Name} (hlen : ps.length ≤ 63) {φ : Name → Nat}
    (hφ : NonzeroOutside ps φ) :
    ∀ l : Level, holds (valAt ps φ) (maskOf ps l) = (Level.eval φ l == 0)
  | .zero => by simp [maskOf, holds_always, Level.eval]
  | .succ _ => by simp [maskOf, holds_never, Level.eval]
  | .param n => by
    simp only [maskOf]
    split
    · rename_i i hi
      obtain ⟨hil, hget⟩ := posOf_some hi
      rw [holds_bit (by omega)]
      simp only [valAt, Level.eval]
      rw [List.getD_eq_getElem?_getD, hget]
      rfl
    · rename_i hn
      rw [holds_never]
      have := hφ n (posOf_none hn)
      simp [Level.eval, this]
  | .max a b => by
    rw [maskOf_max, holds_inter (WF.maskOf ps a) (WF.maskOf ps b),
      holds_maskOf hlen hφ a, holds_maskOf hlen hφ b, beq_zero_and]
    rfl
  | .imax a b => by
    rw [maskOf_imax, holds_maskOf hlen hφ b]
    show _ = ((if Level.eval φ b = 0 then 0
      else Max.max (Level.eval φ a) (Level.eval φ b)) == 0)
    by_cases hb : Level.eval φ b = 0
    · simp [hb]
    · have hm : ¬ Max.max (Level.eval φ a) (Level.eval φ b) = 0 := by omega
      have h1 : (Level.eval φ b == 0) = false := by simpa using hb
      have h2 : (Max.max (Level.eval φ a) (Level.eval φ b) == 0) = false := by simpa using hm
      rw [h1, if_neg hb, h2]

/-! ## `masksOf` and `substPW` -/

theorem masksOf_length (ps' : List Name) (us : List Level) :
    (masksOf ps' us).length = us.length := by simp [masksOf]

theorem masksOf_wf (ps' : List Name) (us : List Level) :
    ∀ m ∈ masksOf ps' us, WF m := by
  intro m hm
  simp only [masksOf, List.mem_map] at hm
  obtain ⟨u, -, rfl⟩ := hm
  exact WF.maskOf ps' u

theorem masksOf_paramsDefined (ps' : List Name) (us : List Level) :
    ∀ m ∈ masksOf ps' us, m.paramsDefined ps'.length = true := by
  intro m hm
  simp only [masksOf, List.mem_map] at hm
  obtain ⟨u, -, rfl⟩ := hm
  exact maskOf_paramsDefined ps' u

theorem masksOf_getD (ps' : List Name) (us : List Level) (i : Nat) (hi : i < us.length) :
    (masksOf ps' us).getD i .never = maskOf ps' us[i] := by
  simp [masksOf, List.getD_eq_getElem?_getD, hi]

theorem substPW_never (ms : List PropWhen) : substPW ms .never = .never :=
  bindZ_never ms

theorem substPW_always (ms : List PropWhen) : substPW ms .always = .always := by
  cases ms <;> simp [Level.substPW, PropWhen.bindZ, PropWhen.bindZ.go, PropWhen.always,
    PropWhen.never]

theorem WF.substPW {ms : List PropWhen} (hwf : ∀ m ∈ ms, WF m) (pw : PropWhen) :
    WF (Level.substPW ms pw) := WF.bindZ hwf pw

/-- The pushforward keeps datum positions within the new context — the
datum half of `Level.allParamsDefined_subst`. -/
theorem substPW_paramsDefined {ps' : List Name} {us : List Level}
    (pw : PropWhen) :
    (substPW (masksOf ps' us) pw).paramsDefined ps'.length = true :=
  bindZ_paramsDefined (masksOf_wf ps' us) (masksOf_paramsDefined ps' us) pw

/-- **Identity at a declaration's own parameters**, for a datum defined
below the list's length (the invariant the checker enforces at
insertion): the masks of `ks.map param` over `ks` are the singletons
`bit i`. -/
theorem substPW_self {ks : List Name} (hnd : ks.Nodup) (hlen : ks.length ≤ 63)
    {pw : PropWhen} (hdef : pw.paramsDefined ks.length = true) :
    substPW (masksOf ks (ks.map Level.param)) pw = pw := by
  apply bindZ_bits
  · intro i hi
    rw [masksOf_length, List.length_map] at hi
    have h1 : (masksOf ks (ks.map Level.param))[i]? = some (maskOf ks (.param ks[i])) := by
      simp only [masksOf, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some]
    rw [h1]
    simp only [maskOf, posOf_of_nodup hnd (List.getElem?_eq_getElem hi)]
  · rw [masksOf_length, List.length_map]; exact hlen
  · rw [masksOf_length, List.length_map]; exact hdef

/-- `subst.go` at the `i`-th parameter of a duplicate-free list is
the `i`-th replacement. -/
theorem subst_go_getElem : ∀ {ks : List Name} {us : List Level}, ks.Nodup →
    us.length = ks.length → ∀ (i : Nat) (hi : i < ks.length) (hiu : i < us.length),
      Level.subst.go ks us ks[i] = us[i]
  | [], _, _, _, i, hi, _ => by simp at hi
  | k :: ks, [], _, hl, _, _, _ => by simp at hl
  | k :: ks, u :: us, hnd, hl, i, hi, hiu => by
    have hnd' := List.nodup_cons.mp hnd
    cases i with
    | zero => simp [Level.subst.go]
    | succ i =>
      simp only [List.getElem_cons_succ]
      have hi' : i < ks.length := by simpa using hi
      have hne : k ≠ ks[i] := fun he => hnd'.1 (he ▸ List.getElem_mem hi')
      simp only [Level.subst.go, if_neg hne]
      exact subst_go_getElem hnd'.2 (by simpa using hl) i hi' (by simpa using hiu)

/-- **The crossing law** for a datum: the instantiated datum's bit at
`φ` (read in the new context `ps'`) is the datum's bit at the
composed valuation `Level.substFn φ ks us` (read in the old context
`ks`).  Premises: the datum is defined below `|ks|`, the lists align,
`ks` has no duplicates and the new context is representable; and `φ`
is nonzero outside the new context (the total reader's exactness
class — `holds_maskOf`). -/
theorem holds_substPW {ks : List Name} {us : List Level} {ps' : List Name}
    (hnd : ks.Nodup) (hps : ps'.length ≤ 63)
    (hl : us.length = ks.length) {φ : Name → Nat} (hφ : NonzeroOutside ps' φ)
    {pw : PropWhen} (hdef : pw.paramsDefined ks.length = true) :
    holds (valAt ps' φ) (substPW (masksOf ps' us) pw)
      = holds (valAt ks (Level.substFn φ ks us)) pw := by
  unfold substPW
  rw [holds_bindZ (masksOf_wf ps' us) (by rw [masksOf_length, hl]) hdef]
  apply holds_ext_zero hdef
  intro i hi
  have hiu : i < us.length := by omega
  rw [masksOf_getD ps' us i hiu, holds_maskOf hps hφ]
  simp only [valAt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [Option.getD_some]
  rw [← Level.eval_subst_go, subst_go_getElem hnd hl i hi hiu]
  cases h : Level.eval φ us[i] == 0 <;> simp_all

/-! ## Substitution commutation and composition -/

/-- **The pushforward as a syntactic equation**: reading zero-ness in
the new context commutes with level substitution — for a level
defined in the duplicate-free, representable context `ks`. -/
theorem maskOf_subst {ks : List Name} {us : List Level} {c : List Name}
    (hnd : ks.Nodup) (hks : ks.length ≤ 63) (hlu : us.length = ks.length) :
    ∀ {v : Level}, v.allParamsDefined ks = true →
      maskOf c (Level.subst ks us v) = substPW (masksOf c us) (maskOf ks v)
  | .zero, _ => by simp [Level.subst, maskOf, substPW_always]
  | .succ _, _ => by simp [Level.subst, maskOf, substPW_never]
  | .param n, h => by
    have hn : n ∈ ks := by simpa [Level.allParamsDefined, List.contains_iff_mem] using h
    obtain ⟨i, hi⟩ := posOf_of_mem hn
    obtain ⟨hil, hget⟩ := posOf_some hi
    have hnk : ks[i] = n := by
      have := List.getElem?_eq_getElem hil
      rw [hget] at this; exact (Option.some.inj this).symm
    simp only [Level.subst, maskOf, hi]
    have hiu : i < us.length := by omega
    rw [← hnk, subst_go_getElem hnd hlu i hil hiu]
    unfold substPW
    rw [PropWhen.bindZ_bit (masksOf_wf c us) (by omega) (by rw [masksOf_length]; exact hiu)]
    simp [masksOf, List.getElem_map]
  | .max a b, h => by
    rw [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, maskOf_max]
    rw [maskOf_subst hnd hks hlu h.1, maskOf_subst hnd hks hlu h.2]
    unfold substPW
    rw [PropWhen.bindZ_inter (masksOf_wf c us) (WF.maskOf ks a) (WF.maskOf ks b)]
  | .imax a b, h => by
    rw [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, maskOf_imax]
    exact maskOf_subst hnd hks hlu h.2

/-- **Composition of datum instantiations**: pushing through `vs` (over
the intermediate context `ks`) and then through `us` is pushing through
`vs.map (subst ks us)` — the datum half of
`Expr.instantiateLevelParams_instantiateLevelParams`. -/
theorem substPW_comp {ks : List Name} {us : List Level} {ps : List Name}
    {vs : List Level} {c : List Name}
    (_hl : vs.length = ps.length) (hlu : us.length = ks.length) (hnd : ks.Nodup)
    (hks : ks.length ≤ 63) (hvs : ∀ v ∈ vs, v.allParamsDefined ks = true)
    {pw : PropWhen} (_hdef : pw.paramsDefined ps.length = true) :
    substPW (masksOf c us) (substPW (masksOf ks vs) pw)
      = substPW (masksOf c (vs.map (Level.subst ks us))) pw := by
  unfold substPW
  rw [PropWhen.bindZ_bindZ (masksOf_wf ks vs) (masksOf_wf c us)]
  congr 1
  simp only [masksOf, List.map_map]
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp]
  exact (maskOf_subst hnd hks hlu (hvs v hv)).symm

/-- **The one-way reading of the total reader**: where the level is
zero and the reader did not give up, every selected parameter is zero
(the direction the direct-structure guard instantiation consumes; no
valuation class, no length bound). -/
theorem holds_maskOf_of_eval_zero {ps : List Name} {φ : Name → Nat} :
    ∀ {l : Level}, Level.eval φ l = 0 → maskOf ps l ≠ never →
      holds (valAt ps φ) (maskOf ps l) = true
  | .zero, _, _ => by simp [maskOf, holds_always]
  | .succ _, h, _ => by simp [Level.eval] at h
  | .param n, h, hne => by
    simp only [maskOf] at hne ⊢
    cases hi : posOf ps n with
    | none => rw [hi] at hne; exact absurd rfl hne
    | some i =>
      rw [hi] at hne
      simp only
      obtain ⟨hil, hget⟩ := posOf_some hi
      by_cases hi63 : i < 63
      · rw [holds_bit hi63]
        simp only [valAt, List.getD_eq_getElem?_getD, hget, Option.getD_some]
        simpa [Level.eval] using h
      · exact absurd (bit_of_ge (Nat.le_of_not_lt hi63)) hne
  | .max a b, h, hne => by
    rw [maskOf_max] at hne ⊢
    have hab : Level.eval φ a = 0 ∧ Level.eval φ b = 0 := by
      simp only [Level.eval] at h; omega
    have hna : maskOf ps a ≠ never := fun ha => hne (by rw [ha, inter_never_left])
    have hnb : maskOf ps b ≠ never := fun hb => hne (by rw [hb, inter_never_right])
    rw [holds_inter (WF.maskOf ps a) (WF.maskOf ps b),
      holds_maskOf_of_eval_zero hab.1 hna, holds_maskOf_of_eval_zero hab.2 hnb]
    rfl
  | .imax a b, h, hne => by
    rw [maskOf_imax] at hne ⊢
    have hb : Level.eval φ b = 0 := by
      simp only [Level.eval] at h
      by_cases hb : Level.eval φ b = 0
      · exact hb
      · rw [if_neg hb] at h; omega
    exact holds_maskOf_of_eval_zero hb hne

end Setlec.Level
