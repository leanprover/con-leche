module

public import ConLeche.Verify.Ground.Machine

public section

/-!
# The application memo's lookup (task #423 soundness, layer (d), item 2(b))

The ground engine memoises an application of a recursor or a definition
entry `k` to argument cells: a record `[k, start, n, cell]` of `mem`, its
argument cells copied to `argA[start, start + n)`, its slot in the
open-addressing table `mH` (`g4MemoIns`; lookup `g4MemoFind`).  The hash is
seeded with the entry number, so two runs that number their entries
differently place the same records at different slots.  What both runs
agree on is the answer: `g4MemoFind` returns the cell of the record whose key
is the query's (`memoFind_hit`), or `0` if no record has it (`memoFind_miss`),
as long as the table keeps the open-addressing invariant (`MemoTab`): every
record is reachable from its hash slot over occupied slots, no slot holds two
records, the table is at most half full, and no two records have one key.
`MemoTab` holds of the empty memo and survives an insertion after a miss
(`MemoTab.ins`) and the growth of `argA` (`MemoTab.argA`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-! ## Arithmetic of the probe sequence -/

theorem g4Slot_lt (h : UInt64) {n : Nat} (hn : 0 < n) : g4Slot h n < n := by
  unfold g4Slot
  generalize (h * 0x9E3779B97F4A7C15) >>> 29 = x
  by_cases h0 : n.toUInt64 = 0
  · rw [h0, UInt64.mod_zero]
    have hx := x.toNat_lt
    have : n % 2 ^ 64 = 0 := by
      have := congrArg UInt64.toNat h0
      simpa using this
    omega
  · rw [UInt64.toNat_mod]
    have hpos : 0 < n.toUInt64.toNat := by
      rcases Nat.eq_zero_or_pos n.toUInt64.toNat with h' | h'
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h')) h0
      · exact h'
    have hle : n.toUInt64.toNat ≤ n := by simp; exact Nat.mod_le _ _
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hle

theorem probe_inj {s n e₁ e₂ : Nat} (h₁ : e₁ < n) (h₂ : e₂ < n) (h : (s + e₁) % n = (s + e₂) % n) :
    e₁ = e₂ := by
  rcases Nat.le_total e₁ e₂ with hle | hle
  · have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [show s + e₂ - (s + e₁) = e₂ - e₁ by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [show s + e₁ - (s + e₂) = e₁ - e₂ by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem probe_succ (s e n : Nat) : ((s + e) % n + 1) % n = (s + (e + 1)) % n := by
  rw [← Nat.add_assoc, Nat.add_mod (s + e) 1 n, Nat.add_mod ((s + e) % n) 1 n, Nat.mod_mod]

theorem probe_lt {s e n : Nat} (hn : 0 < n) : (s + e) % n < n := Nat.mod_lt _ hn

/-- **Pigeonhole**: an injection of `[0, n)` into `[0, m)`. -/
theorem pigeon : ∀ (n m : Nat) (g : Nat → Nat), (∀ i, i < n → g i < m) →
    (∀ i j, i < n → j < n → g i = g j → i = j) → n ≤ m
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, m, g, hg, hi => by
    have hv := hg n (Nat.lt_succ_self n)
    have hne : ∀ i, i < n → g i ≠ g n := fun i hi' he => by
      have := hi i n (by omega) (Nat.lt_succ_self n) he; omega
    have := pigeon n (m - 1) (fun i => if g i < g n then g i else g i - 1)
      (fun i hi' => by
        have := hg i (by omega); have := hne i hi'
        split <;> omega)
      (fun i j hi' hj' he => by
        have := hne i hi'; have := hne j hj'
        apply hi i j (by omega) (by omega)
        split at he <;> split at he <;> omega)
    omega

/-- The least index with a property, below a bound where it holds. -/
theorem least_of {p : Nat → Prop} [DecidablePred p] :
    ∀ (b : Nat), (∃ d, d < b ∧ p d) → ∃ d, d < b ∧ p d ∧ ∀ e, e < d → ¬p e
  | 0, ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)
  | b + 1, ⟨d, hd, hp⟩ => by
    by_cases hb : ∃ d, d < b ∧ p d
    · obtain ⟨d', h₁, h₂, h₃⟩ := least_of b hb
      exact ⟨d', by omega, h₂, h₃⟩
    · refine ⟨d, hd, hp, fun e he hpe => hb ⟨e, by omega, hpe⟩⟩

/-! ## Placed records -/

/-- **A table holding records `0 … m-1`** (`0` an empty slot, `r + 1`
record `r`), each reachable from its hash's slot over occupied slots. -/
structure PTab (hash : Nat → UInt64) (mT : Array Nat) (m : Nat) : Prop where
  pos : 0 < mT.size
  ent : ∀ i, i < mT.size → mT[i]! ≠ 0 → mT[i]! ≤ m
  inj : ∀ i j, i < mT.size → j < mT.size → mT[i]! ≠ 0 → mT[i]! = mT[j]! → i = j
  reach : ∀ r, r < m → ∃ d, d < mT.size ∧
    mT[(g4Slot (hash r) mT.size + d) % mT.size]! = r + 1 ∧
    ∀ e, e < d → mT[(g4Slot (hash r) mT.size + e) % mT.size]! ≠ 0

theorem PTab.empty (hash : Nat → UInt64) {n : Nat} (hn : 0 < n) :
    PTab hash (Array.replicate n 0) 0 where
  pos := by simpa using hn
  ent i hi h := by simp at hi; simp [hi] at h
  inj i _ hi _ h := by simp at hi; simp [hi] at h
  reach r hr := absurd hr (Nat.not_lt_zero _)

theorem PTab.congr {hash hash' : Nat → UInt64} {mT : Array Nat} {m : Nat} (h : PTab hash mT m)
    (he : ∀ r, r < m → hash' r = hash r) : PTab hash' mT m :=
  ⟨h.pos, h.ent, h.inj, fun r hr => by rw [he r hr]; exact h.reach r hr⟩

theorem getElem!_set!_ne {a : Array Nat} {i j w : Nat} (h : j ≠ i) : (a.set! i w)[j]! = a[j]! := by
  simp [getElem!_def, Array.set!_eq_setIfInBounds, Ne.symm h]

theorem getElem!_set!_self {a : Array Nat} {i w : Nat} (h : i < a.size) : (a.set! i w)[i]! = w := by
  simp [Array.set!_eq_setIfInBounds, h]

/-- `g4Place` from the `e`-th probe on, with the first empty slot at the
`D`-th. -/
theorem place_eq {mT : Array Nat} {r s D : Nat} (hz : mT[(s + D) % mT.size]! = 0)
    (hocc : ∀ e, e < D → mT[(s + e) % mT.size]! ≠ 0) :
    ∀ (f e : Nat), e ≤ D → D - e < f →
      g4Place mT r f ((s + e) % mT.size) = mT.set! ((s + D) % mT.size) (r + 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, e, he, hf => by
    unfold g4Place
    by_cases hD : e = D
    · subst hD; simp [hz]
    · have := hocc e (by omega)
      simp only [this, beq_iff_eq, ↓reduceIte, probe_succ]
      exact place_eq hz hocc f (e + 1) (by omega) (by omega)

/-- **Placing record `m`** in a table that has room keeps the records
placed and adds it. -/
theorem PTab.place {hash : Nat → UInt64} {mT : Array Nat} {m : Nat} (h : PTab hash mT m)
    (hm : m < mT.size) :
    PTab hash (g4Place mT m mT.size (g4Slot (hash m) mT.size)) (m + 1) := by
  have hn := h.pos
  generalize hs : g4Slot (hash m) mT.size = s
  have hsl : s < mT.size := hs ▸ g4Slot_lt _ hn
  -- an empty slot on the probe sequence
  have hex : ∃ d, d < mT.size ∧ mT[(s + d) % mT.size]! = 0 := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ d, d < mT.size → mT[(s + d) % mT.size]! ≠ 0 := fun d hd h' => hno ⟨d, hd, h'⟩
    have := pigeon mT.size m (fun d => mT[(s + d) % mT.size]! - 1)
      (fun d hd => by have := h.ent _ (probe_lt hn) (hall d hd); have := hall d hd; omega)
      (fun d d' hd hd' he => by
        have h₁ := hall d hd; have h₂ := hall d' hd'
        exact probe_inj hd hd' (h.inj _ _ (probe_lt hn) (probe_lt hn) h₁ (by omega)))
    omega
  obtain ⟨D, hD, hz, hocc⟩ := least_of mT.size hex
  have hocc' : ∀ e, e < D → mT[(s + e) % mT.size]! ≠ 0 := fun e he => hocc e he
  have heq := place_eq (r := m) hz hocc' mT.size 0 (Nat.zero_le _) (by omega)
  rw [Nat.add_zero, Nat.mod_eq_of_lt hsl] at heq
  rw [heq]
  generalize hp : (s + D) % mT.size = p at hz heq
  have hpl : p < mT.size := hp ▸ probe_lt hn
  have hsz : (mT.set! p (m + 1)).size = mT.size := by simp
  have hge : (mT.set! p (m + 1))[p]! = m + 1 := getElem!_set!_self hpl
  have hgn : ∀ i, i ≠ p → (mT.set! p (m + 1))[i]! = mT[i]! := fun i h' => getElem!_set!_ne h'
  refine ⟨by rw [hsz]; exact hn, fun i hi h' => ?_, fun i j hi hj h' he => ?_, fun r hr => ?_⟩
  · rw [hsz] at hi
    by_cases hip : i = p
    · rw [hip, hge]; exact Nat.le_refl _
    · rw [hgn i hip] at h' ⊢; have := h.ent i hi h'; omega
  · rw [hsz] at hi hj
    by_cases hip : i = p <;> by_cases hjp : j = p
    · rw [hip, hjp]
    · rw [hip, hge, hgn j hjp] at he
      have := h.ent j hj (by omega); omega
    · rw [hgn i hip, hjp, hge] at he
      rw [hgn i hip] at h'
      have := h.ent i hi h'; omega
    · rw [hgn i hip, hgn j hjp] at he; rw [hgn i hip] at h'
      exact h.inj i j hi hj h' he
  · rw [hsz]
    rcases Nat.lt_or_ge r m with hr' | hr'
    · obtain ⟨d, hd, h₁, h₂⟩ := h.reach r hr'
      refine ⟨d, hd, ?_, fun e he => ?_⟩
      · rw [hgn _ (fun h'' => by rw [h'', hz] at h₁; omega)]; exact h₁
      · by_cases hep : (g4Slot (hash r) mT.size + e) % mT.size = p
        · rw [hep, hge]; omega
        · rw [hgn _ hep]; exact h₂ e he
    · obtain rfl : r = m := by omega
      rw [hs]
      refine ⟨D, hD, by rw [hp, hge], fun e he => ?_⟩
      rw [hgn _ (fun h'' => by
        have := probe_inj (by omega) hD (h''.trans hp.symm); omega)]
      exact hocc e he

/-- `g4Rehash` places records `r … r + f - 1`. -/
theorem rehash_tab {hash : Nat → UInt64} (mem argA : Array Nat)
    (hh : ∀ r, hash r = g4HashSpan argA mem[g4X4 r + 1]! mem[g4X4 r + 2]! 0 (UInt64.ofNat mem[g4X4 r]!)) :
    ∀ (f r : Nat) (mT : Array Nat), PTab hash mT r → r + f ≤ mT.size →
      PTab hash (g4Rehash mem argA mT f r) (r + f) ∧ (g4Rehash mem argA mT f r).size = mT.size
  | 0, r, mT, h, _ => ⟨h, rfl⟩
  | f + 1, r, mT, h, hb => by
    unfold g4Rehash
    dsimp only
    rw [← hh r]
    have hp := h.place (by omega)
    have hps : (g4Place mT r mT.size (g4Slot (hash r) mT.size)).size = mT.size := place_size _ _ _ _
    obtain ⟨h₁, h₂⟩ := rehash_tab mem argA hh f (r + 1) _ hp (by rw [hps]; omega)
    rw [show r + (f + 1) = r + 1 + f by omega]
    exact ⟨h₁, h₂.trans hps⟩
where
  place_size (mT : Array Nat) (r : Nat) : ∀ (f i : Nat), (g4Place mT r f i).size = mT.size
    | 0, _ => rfl
    | f + 1, i => by
      unfold g4Place; split
      · simp
      · exact place_size mT r f _

/-! ## Records -/

theorem push_get_lt {a : Array Nat} {x i : Nat} (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  simp [getElem!_def, Array.getElem?_push, Nat.ne_of_lt h]

theorem push_get_eq {a : Array Nat} {x : Nat} : (a.push x)[a.size]! = x := by simp

/-- The hash `g4Rehash` computes for record `r`. -/
@[expose] def recHash (mem argA : Array Nat) (r : Nat) : UInt64 :=
  g4HashSpan argA mem[g4X4 r + 1]! mem[g4X4 r + 2]! 0 (UInt64.ofNat mem[g4X4 r]!)

/-- Record `r`'s key is entry `k` on the top `n` arguments (`g4MemoFind`'s test). -/
@[expose] def RecM (mem fs argA : Array Nat) (k n r : Nat) : Prop :=
  mem[g4X4 r]! = k ∧ mem[g4X4 r + 2]! = n ∧ g4SpanEq fs argA mem[g4X4 r + 1]! n 0 = true

theorem recM_iff (mem fs argA : Array Nat) (k n r : Nat) :
    (mem[g4X4 r]! == k && mem[g4X4 r + 2]! == n && g4SpanEq fs argA mem[g4X4 r + 1]! n 0) = true ↔
      RecM mem fs argA k n r := by
  simp [RecM, Bool.and_eq_true, and_assoc]

theorem spanEq_iff (fs argA : Array Nat) (start : Nat) : ∀ (n j : Nat),
    g4SpanEq fs argA start n j = true ↔ ∀ i, i < n → argA[start + j + i]! = g4ArgAt fs (j + i)
  | 0, j => by simp [g4SpanEq]
  | n + 1, j => by
    rw [g4SpanEq, Bool.and_eq_true, beq_iff_eq, spanEq_iff fs argA start n (j + 1)]
    constructor
    · rintro ⟨h₀, h⟩ i hi
      rcases i with _ | i
      · simpa using h₀
      · have := h i (by omega)
        rwa [show start + (j + 1) + i = start + j + (i + 1) by omega,
          show j + 1 + i = j + (i + 1) by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rwa [show start + j + (i + 1) = start + (j + 1) + i by omega,
        show j + (i + 1) = j + 1 + i by omega] at this

/-- **A nonzero answer** is a record whose key is the entry and the top arguments
(no invariant needed). -/
theorem memoFind_spec (mem mT fs argA : Array Nat) (k n : Nat) (hn : 0 < n) :
    ∀ (f i : Nat), g4MemoFind mem mT fs argA k n f i ≠ 0 →
      ∃ r, 4 * r + 2 < mem.size ∧ mem[4 * r]! = k ∧ mem[4 * r + 2]! = n ∧
        g4SpanEq fs argA mem[4 * r + 1]! n 0 = true ∧ g4MemoFind mem mT fs argA k n f i = mem[4 * r + 3]!
  | 0, _, h => absurd rfl h
  | f + 1, i, h => by
    unfold g4MemoFind at h ⊢
    dsimp only at h ⊢
    by_cases h0 : (mT[i]! == 0) = true
    · simp only [h0, ↓reduceIte] at h; exact absurd rfl h
    · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hc : (mem[g4X4 (mT[i]! - 1)]! == k && mem[g4X4 (mT[i]! - 1) + 2]! == n &&
          g4SpanEq fs argA mem[g4X4 (mT[i]! - 1) + 1]! n 0) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hc
        rw [g4X4_eq] at h₁ h₂ h₃ ⊢
        refine ⟨mT[i]! - 1, ?_, h₁, h₂, h₃, rfl⟩
        rcases Nat.lt_or_ge (4 * (mT[i]! - 1) + 2) mem.size with h' | h'
        · exact h'
        · rw [getElem!_neg mem _ (by omega)] at h₂; exact absurd h₂ (by simp; omega)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact memoFind_spec mem mT fs argA k n hn f _ h

/-- The query's hash is the matching record's. -/
theorem hash_span (fs argA : Array Nat) (k start : Nat) : ∀ (n j : Nat) (h : UInt64),
    g4SpanEq fs argA start n j = true → g4Hash fs k n j h = g4HashSpan argA start n j h
  | 0, _, _, _ => rfl
  | n + 1, j, h, hs => by
    rw [g4SpanEq, Bool.and_eq_true, beq_iff_eq] at hs
    rw [g4Hash, g4HashSpan, hs.1]
    exact hash_span fs argA k start n (j + 1) _ hs.2

theorem hashSpan_pre {a a' : Array Nat} (hp : Pre a a') (start : Nat) : ∀ (n j : Nat) (h : UInt64),
    start + j + n ≤ a.size → g4HashSpan a' start n j h = g4HashSpan a start n j h
  | 0, _, _, _ => rfl
  | n + 1, j, h, hb => by
    rw [g4HashSpan, g4HashSpan, hp.2 _ (by omega)]
    exact hashSpan_pre hp start n (j + 1) _ (by omega)

theorem spanEq_pre {a a' : Array Nat} (hp : Pre a a') (fs : Array Nat) (start : Nat) : ∀ (n j : Nat),
    start + j + n ≤ a.size → g4SpanEq fs a' start n j = g4SpanEq fs a start n j
  | 0, _, _ => rfl
  | n + 1, j, hb => by
    rw [g4SpanEq, g4SpanEq, hp.2 _ (by omega), spanEq_pre hp fs start n (j + 1) (by omega)]

/-- **The memo's invariant**: `mem` holds `mem.size / 4` records, the table
places them all and is at most half full, every record's span is in `argA`,
and no two records match one query. -/
structure MemoTab (mem argA mT : Array Nat) : Prop where
  tab : PTab (recHash mem argA) mT (mem.size / 4)
  half : 2 * (mem.size / 4) ≤ mT.size
  sz : mem.size % 4 = 0
  span : ∀ r, r < mem.size / 4 → mem[g4X4 r + 1]! + mem[g4X4 r + 2]! ≤ argA.size
  cell : ∀ r, r < mem.size / 4 → mem[g4X4 r + 3]! ≠ 0
  uniq : ∀ (fs : Array Nat) (k n r r' : Nat), r < mem.size / 4 → r' < mem.size / 4 →
    RecM mem fs argA k n r → RecM mem fs argA k n r' → r = r'

/-- The empty memo. -/
theorem MemoTab.fresh (argA : Array Nat) {n : Nat} (hn : 0 < n) :
    MemoTab #[] argA (Array.replicate n 0) where
  tab := PTab.empty _ hn
  half := by simp
  sz := rfl
  span r hr := absurd hr (by simp)
  cell r hr := absurd hr (by simp)
  uniq _ _ _ r _ hr := absurd hr (by simp)

/-! ## Lookup -/

theorem probe_hit {mem mT fs argA : Array Nat} {k n r s D : Nat} (ht : MemoTab mem argA mT)
    (hr : r < mem.size / 4) (hm : RecM mem fs argA k n r)
    (hD : mT[(s + D) % mT.size]! = r + 1) (hocc : ∀ e, e < D → mT[(s + e) % mT.size]! ≠ 0) :
    ∀ (f e : Nat), e ≤ D → D - e < f →
      g4MemoFind mem mT fs argA k n f ((s + e) % mT.size) = mem[g4X4 r + 3]!
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, e, he, hf => by
    have hpos := ht.tab.pos
    unfold g4MemoFind
    dsimp only
    generalize hv : mT[(s + e) % mT.size]! = v
    have hv0 : v ≠ 0 := by
      by_cases hDe : e = D
      · subst hDe; rw [hD] at hv; omega
      · rw [← hv]; exact hocc e (by omega)
    have hvl : v - 1 < mem.size / 4 := by
      have := ht.tab.ent _ (probe_lt hpos) (by rw [hv]; exact hv0); omega
    simp only [show (v == 0) = false from by simpa using hv0, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hc
      obtain rfl := ht.uniq fs k n _ r hvl hr ((recM_iff _ _ _ _ _ _).mp hc) hm
      rfl
    · rename_i hc
      by_cases hDe : e = D
      · subst hDe; rw [hD] at hv; subst hv
        exact absurd ((recM_iff _ _ _ _ _ _).mpr (by simpa using hm)) hc
      · rw [probe_succ]
        exact probe_hit ht hr hm hD hocc f (e + 1) (by omega) (by omega)

/-- **A hit**: the lookup returns the cell of the record whose key is the
query's. -/
theorem memoFind_hit {mem mT fs argA : Array Nat} {k n r : Nat} (ht : MemoTab mem argA mT)
    (hr : r < mem.size / 4) (hm : RecM mem fs argA k n r) :
    g4MemoFind mem mT fs argA k n mT.size (g4Slot (g4Hash fs k n 0 (UInt64.ofNat k)) mT.size) =
      mem[g4X4 r + 3]! := by
  have hh : g4Hash fs k n 0 (UInt64.ofNat k) = recHash mem argA r := by
    obtain ⟨h₀, h₂, h₁⟩ := hm
    unfold recHash; rw [h₀, h₂]; exact hash_span fs argA k _ n 0 _ h₁
  rw [hh]
  obtain ⟨D, hD, h₁, h₂⟩ := ht.tab.reach r hr
  have := probe_hit ht hr hm h₁ h₂ mT.size 0 (Nat.zero_le _) (by omega)
  rwa [Nat.add_zero, Nat.mod_eq_of_lt (g4Slot_lt _ ht.tab.pos)] at this

theorem probe_miss {mem mT fs argA : Array Nat} {k n : Nat} (ht : MemoTab mem argA mT)
    (hno : ∀ r, r < mem.size / 4 → ¬RecM mem fs argA k n r) :
    ∀ (f i : Nat), i < mT.size → g4MemoFind mem mT fs argA k n f i = 0
  | 0, _, _ => rfl
  | f + 1, i, hi => by
    unfold g4MemoFind
    dsimp only
    split
    · rfl
    · rename_i hv
      split
      · rename_i hc
        have h0 : mT[i]! ≠ 0 := by simpa using hv
        exact absurd ((recM_iff _ _ _ _ _ _).mp hc) (hno _ (by have := ht.tab.ent i hi h0; omega))
      · exact probe_miss ht hno f _ (Nat.mod_lt _ ht.tab.pos)

/-- **A miss**: no record has the query's key. -/
theorem memoFind_miss {mem mT fs argA : Array Nat} {k n : Nat} (ht : MemoTab mem argA mT)
    (hno : ∀ r, r < mem.size / 4 → ¬RecM mem fs argA k n r) :
    g4MemoFind mem mT fs argA k n mT.size (g4Slot (g4Hash fs k n 0 (UInt64.ofNat k)) mT.size) = 0 :=
  probe_miss ht hno _ _ (g4Slot_lt _ ht.tab.pos)

/-- A zero answer is a miss (record cells are not `0`). -/
theorem memoFind_zero {mem mT fs argA : Array Nat} {k n : Nat} (ht : MemoTab mem argA mT)
    (h : g4MemoFind mem mT fs argA k n mT.size (g4Slot (g4Hash fs k n 0 (UInt64.ofNat k)) mT.size) = 0) :
    ∀ r, r < mem.size / 4 → ¬RecM mem fs argA k n r :=
  fun r hr hm => ht.cell r hr (by rw [← memoFind_hit ht hr hm]; exact h)

/-- **Two memos with the same records agree**: the records' spans and cells
equal, their entries related by `rel` (the kept/fresh or the extension
relation on entry numbers, a partial bijection on the records' entries). -/
theorem memoFind_agree {memA memB mTA mTB fs argA : Array Nat} {kA kB n : Nat}
    (hA : MemoTab memA argA mTA) (hB : MemoTab memB argA mTB) (hsz : memA.size = memB.size)
    (hw : ∀ r, r < memA.size / 4 → ∀ i, 0 < i → i < 4 → memA[g4X4 r + i]! = memB[g4X4 r + i]!)
    (hk : ∀ r, r < memA.size / 4 → (memA[g4X4 r]! = kA ↔ memB[g4X4 r]! = kB)) :
    g4MemoFind memA mTA fs argA kA n mTA.size (g4Slot (g4Hash fs kA n 0 (UInt64.ofNat kA)) mTA.size) =
      g4MemoFind memB mTB fs argA kB n mTB.size (g4Slot (g4Hash fs kB n 0 (UInt64.ofNat kB)) mTB.size) := by
  have hm : ∀ r, r < memA.size / 4 → (RecM memA fs argA kA n r ↔ RecM memB fs argA kB n r) := by
    intro r hr
    unfold RecM
    rw [hk r hr, hw r hr 1 (by omega) (by omega), hw r hr 2 (by omega) (by omega)]
  by_cases hex : ∃ r, r < memA.size / 4 ∧ RecM memA fs argA kA n r
  · obtain ⟨r, hr, hra⟩ := hex
    rw [memoFind_hit hA hr hra, memoFind_hit hB (by rw [← hsz]; exact hr) ((hm r hr).mp hra),
      hw r hr 3 (by omega) (by omega)]
  · rw [memoFind_miss hA (fun r hr h => hex ⟨r, hr, h⟩),
      memoFind_miss hB (fun r hr h => hex ⟨r, by rw [hsz]; exact hr, (hm r (by rw [hsz]; exact hr)).mpr h⟩)]

/-! ## Insertion -/

/-- The memo invariant survives the growth of `argA`. -/
theorem MemoTab.argA {mem argA argA' mT : Array Nat} (ht : MemoTab mem argA mT) (hp : Pre argA argA') :
    MemoTab mem argA' mT where
  tab := ht.tab.congr fun r hr => by
    unfold recHash; exact hashSpan_pre hp _ _ 0 _ (by have := ht.span r hr; omega)
  half := ht.half
  sz := ht.sz
  span r hr := Nat.le_trans (ht.span r hr) hp.1
  cell := ht.cell
  uniq fs k n r r' hr hr' h h' := by
    have e : ∀ q, q < mem.size / 4 → RecM mem fs argA' k n q → RecM mem fs argA k n q := by
      intro q hq ⟨h₀, h₂, h₁⟩
      refine ⟨h₀, h₂, ?_⟩
      rw [← spanEq_pre hp fs _ n 0 (by have := ht.span q hq; omega), ← h₂]; rw [h₂]; exact h₁
    exact ht.uniq fs k n r r' hr hr' (e r hr h) (e r' hr' h')

/-- **An insertion after a miss**: the record `[k, argA.size, n, c]`, its
arguments copied to the end of `argA` (`g4CopyArgs`), placed by `g4MemoIns`
under the query's hash. -/
theorem MemoTab.ins {mem argA argA' mT fs : Array Nat} {k n c : Nat} (ht : MemoTab mem argA mT)
    (hno : ∀ r, r < mem.size / 4 → ¬RecM mem fs argA k n r) (hc : c ≠ 0)
    (hp : Pre argA argA') (hsz : argA'.size = argA.size + n)
    (hcp : ∀ i, i < n → argA'[argA.size + i]! = g4ArgAt fs i) :
    MemoTab ((((mem.push k).push argA.size).push n).push c) argA'
      (g4MemoIns ((((mem.push k).push argA.size).push n).push c) argA' mT (mem.size / 4)
        (g4Hash fs k n 0 (UInt64.ofNat k))) := by
  generalize hM : (((mem.push k).push argA.size).push n).push c = M
  have ht' := ht.argA hp
  have hN : M.size / 4 = mem.size / 4 + 1 := by
    rw [← hM]; simp only [Array.size_push]; have := ht.sz; omega
  have hNs : 4 * (mem.size / 4) = mem.size := by have := ht.sz; omega
  have hold : ∀ i, i < mem.size → M[i]! = mem[i]! := by
    intro i hi; rw [← hM]
    rw [push_get_lt (by simp only [Array.size_push]; omega), push_get_lt (by simp only [Array.size_push]; omega),
      push_get_lt (by simp only [Array.size_push]; omega), push_get_lt hi]
  have hold4 : ∀ r, r < mem.size / 4 → ∀ i, i < 4 → M[g4X4 r + i]! = mem[g4X4 r + i]! :=
    fun r hr i hi => hold _ (by rw [g4X4_eq]; omega)
  have hold0 : ∀ r, r < mem.size / 4 → M[g4X4 r]! = mem[g4X4 r]! :=
    fun r hr => hold _ (by rw [g4X4_eq]; omega)
  have hnew : M[g4X4 (mem.size / 4)]! = k ∧ M[g4X4 (mem.size / 4) + 1]! = argA.size ∧
      M[g4X4 (mem.size / 4) + 2]! = n ∧ M[g4X4 (mem.size / 4) + 3]! = c := by
    rw [g4X4_eq, hNs, ← hM]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [push_get_lt (by simp only [Array.size_push]; omega), push_get_lt (by simp only [Array.size_push]; omega), push_get_lt (by simp only [Array.size_push]; omega)]; exact push_get_eq
    · rw [push_get_lt (by simp only [Array.size_push]; omega), push_get_lt (by simp only [Array.size_push]; omega)]
      exact (show mem.size + 1 = (mem.push k).size by simp) ▸ push_get_eq
    · rw [push_get_lt (by simp only [Array.size_push]; omega)]
      exact (show mem.size + 2 = ((mem.push k).push argA.size).size by simp) ▸ push_get_eq
    · exact (show mem.size + 3 = (((mem.push k).push argA.size).push n).size by simp) ▸ push_get_eq
  -- the old records: their hashes and keys
  have hhold : ∀ r, r < mem.size / 4 → recHash M argA' r = recHash mem argA' r := by
    intro r hr; unfold recHash
    rw [hold0 r hr, hold4 r hr 1 (by omega), hold4 r hr 2 (by omega)]
  have hrold : ∀ fs' k' n' r, r < mem.size / 4 → (RecM M fs' argA' k' n' r ↔ RecM mem fs' argA' k' n' r) := by
    intro fs' k' n' r hr; unfold RecM
    rw [hold0 r hr, hold4 r hr 1 (by omega), hold4 r hr 2 (by omega)]
  -- the new record
  have hspan : g4SpanEq fs argA' argA.size n 0 = true :=
    (spanEq_iff fs argA' argA.size n 0).mpr fun i hi => by simpa using hcp i hi
  have hhnew : recHash M argA' (mem.size / 4) = g4Hash fs k n 0 (UInt64.ofNat k) := by
    unfold recHash; rw [hnew.1, hnew.2.1, hnew.2.2.1]; exact (hash_span fs argA' k _ n 0 _ hspan).symm
  have htab : ∀ (T : Array Nat), PTab (recHash M argA') T (mem.size / 4) → mem.size / 4 < T.size →
      PTab (recHash M argA') (g4Place T (mem.size / 4) T.size (g4Slot (g4Hash fs k n 0 (UInt64.ofNat k)) T.size))
        (mem.size / 4 + 1) ∧
      (g4Place T (mem.size / 4) T.size (g4Slot (g4Hash fs k n 0 (UInt64.ofNat k)) T.size)).size = T.size := by
    intro T hT hlt
    rw [← hhnew]
    exact ⟨hT.place hlt, rehash_tab.place_size _ _ _ _⟩
  have hpos := ht.tab.pos
  have hhalf := ht.half
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]; unfold g4MemoIns; dsimp only
    split
    · obtain ⟨h₁, h₂⟩ := rehash_tab M argA' (hash := recHash M argA') (fun _ => rfl) (mem.size / 4) 0
        (Array.replicate (2 * mT.size) 0) (PTab.empty _ (by omega)) (by simp; omega)
      rw [Nat.zero_add] at h₁
      exact (htab _ h₁ (by rw [h₂]; simp; omega)).1
    · exact (htab mT (ht'.tab.congr hhold) (by omega)).1
  · rw [hN]; unfold g4MemoIns; dsimp only
    split
    · obtain ⟨-, h₂⟩ := rehash_tab M argA' (hash := recHash M argA') (fun _ => rfl) (mem.size / 4) 0
        (Array.replicate (2 * mT.size) 0) (PTab.empty _ (by omega)) (by simp; omega)
      rw [rehash_tab.place_size, h₂]; simp; omega
    · rename_i hg; rw [rehash_tab.place_size]; omega
  · rw [← hM]; simp only [Array.size_push]; have := ht.sz; omega
  · intro r hr; rw [hN] at hr
    rcases Nat.lt_or_ge r (mem.size / 4) with hr' | hr'
    · rw [hold4 r hr' 1 (by omega), hold4 r hr' 2 (by omega)]
      exact Nat.le_trans (ht.span r hr') hp.1
    · obtain rfl : r = mem.size / 4 := by omega
      rw [hnew.2.1, hnew.2.2.1]; omega
  · intro r hr; rw [hN] at hr
    rcases Nat.lt_or_ge r (mem.size / 4) with hr' | hr'
    · rw [hold4 r hr' 3 (by omega)]; exact ht.cell r hr'
    · obtain rfl : r = mem.size / 4 := by omega
      rw [hnew.2.2.2]; exact hc
  · intro fs' k' n' r r' hr hr' h h'
    rw [hN] at hr hr'
    -- a query both an old record and the new one match is the insertion's query
    have hcross : ∀ q, q < mem.size / 4 → RecM M fs' argA' k' n' q → RecM M fs' argA' k' n' (mem.size / 4) →
        False := by
      intro q hq hq' hn'
      obtain ⟨e₀, e₂, e₁⟩ := hn'
      rw [hnew.1] at e₀; rw [hnew.2.2.1] at e₂; rw [hnew.2.1] at e₁
      subst e₀ e₂
      obtain ⟨f₀, f₂, f₁⟩ := (hrold fs' k n q hq).mp hq'
      apply hno q hq
      refine ⟨f₀, f₂, ?_⟩
      have hsq := ht.span q hq
      rw [← spanEq_pre hp fs _ n 0 (by omega)]
      refine (spanEq_iff fs argA' _ n 0).mpr fun i hi => ?_
      have a₁ := (spanEq_iff fs' argA' _ n 0).mp f₁ i hi
      have a₂ := (spanEq_iff fs' argA' _ n 0).mp e₁ i hi
      have a₃ := hcp i hi
      simp only [Nat.add_zero, Nat.zero_add] at a₁ a₂ ⊢
      rw [a₁, ← a₂, a₃]
    rcases Nat.lt_or_ge r (mem.size / 4) with h₁ | h₁ <;> rcases Nat.lt_or_ge r' (mem.size / 4) with h₂ | h₂
    · exact ht'.uniq fs' k' n' r r' h₁ h₂ ((hrold _ _ _ r h₁).mp h) ((hrold _ _ _ r' h₂).mp h')
    · obtain rfl : r' = mem.size / 4 := by omega
      exact (hcross r h₁ h h').elim
    · obtain rfl : r = mem.size / 4 := by omega
      exact (hcross r' h₂ h' h).elim
    · omega

end ConLeche.Verify.Ground
