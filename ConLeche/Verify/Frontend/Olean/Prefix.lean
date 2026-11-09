module

public import ConLeche.Frontend.Olean.Fast
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads
import Init.Data.ByteArray.Lemmas

/-!
# A view reads the same in the region of later files

A module's files are laid end to end, and a view reads the files up to its own.
`Region.Sub P r n`: the region `P` is the first `n` bytes of `r`: its bytes read the
same, and its files are `r`'s first ones.  The instances are the regions of a
module's files (`Region.Sub.single_two`, `Region.Sub.two_three`).

Everything below an address `P` knows reads the same in `r`: a pointer an object
holds points below it, so it stays inside `P`.  Only the address a read starts from
can leave it (`decodeAt_sub`'s hypothesis).
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **`P` is the first `n` bytes of `r`.** -/
structure Region.Sub (P r : Region) (n : Nat) : Prop where
  u8 : ∀ i, i < n → rdU8 r.bytes i = rdU8 P.bytes i
  u64 : ∀ i, i + 8 ≤ n → rdU64 r.bytes i = rdU64 P.bytes i
  extract : ∀ a b, b ≤ n → r.bytes.extract a b = P.bytes.extract a b
  loc : ∀ v c, P.loc v = some c → r.loc v = some c
  locLt : ∀ v c, r.loc v = some c → c < n → P.loc v = some c
  good : ∀ v c, P.loc v = some c → c + 8 ≤ P.fileEnd c
  endEq : ∀ g, g < n → r.fileEnd g = P.fileEnd g
  endLe : ∀ g, P.fileEnd g ≤ n

/-! ## Appending a file -/

theorem rdU8_append {B x : ByteArray} {i : Nat} (h : i < B.size) :
    rdU8 (B ++ x) i = rdU8 B i := by
  have h' : i < (B ++ x).size := by simp; omega
  simp only [rdU8, h, h', dite_true]
  exact ByteArray.getElem_append_left h

theorem rdU64_append {B x : ByteArray} {i : Nat} (h : i + 8 ≤ B.size) :
    rdU64 (B ++ x) i = rdU64 B i := by
  have h' : i + 8 ≤ (B ++ x).size := by simp; omega
  simp only [rdU64, h, h', dite_true]
  simp only [ByteArray.getElem_append_left (show i < B.size by omega),
    ByteArray.getElem_append_left (show i + 1 < B.size by omega),
    ByteArray.getElem_append_left (show i + 2 < B.size by omega),
    ByteArray.getElem_append_left (show i + 3 < B.size by omega),
    ByteArray.getElem_append_left (show i + 4 < B.size by omega),
    ByteArray.getElem_append_left (show i + 5 < B.size by omega),
    ByteArray.getElem_append_left (show i + 6 < B.size by omega),
    ByteArray.getElem_append_left (show i + 7 < B.size by omega)]

theorem extract_append {B x : ByteArray} {a b : Nat} (h : b ≤ B.size) :
    (B ++ x).extract a b = B.extract a b := by
  apply ByteArray.ext
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp at h1
    simp [*]

/-- The hit of `locGo` at a file. -/
def Seg.hit (s : Seg) (a : UInt64) : Prop := s.base ≤ a ∧ (a - s.base).toNat < s.size

theorem Seg.hit_lt {s : Seg} {a : UInt64} (h : s.hit a) : a.toNat < s.base.toNat + s.size := by
  obtain ⟨h1, h2⟩ := h
  rw [UInt64.toNat_sub_of_le _ _ h1] at h2
  have : s.base.toNat ≤ a.toNat := h1
  omega

theorem Seg.hit_ge {s : Seg} {a : UInt64} (h : s.hit a) : s.base.toNat ≤ a.toNat := h.1

/-- The search in the files up to `k` ignores the rest of the region. -/
theorem locGo_push {B B' : ByteArray} {S : Array Seg} {x : Seg} (a : UInt64) :
    ∀ k, k ≤ S.size → Region.locGo ⟨B', S.push x⟩ a k = Region.locGo ⟨B, S⟩ a k
  | 0, _ => rfl
  | k + 1, h => by
    have hk : k < S.size := by omega
    have hk' : k < (S.push x).size := by simp; omega
    unfold Region.locGo
    simp only [hk, hk', dite_true, Array.getElem_push_lt hk]
    split
    · rfl
    · exact locGo_push a k (by omega)

theorem endGo_push {B B' : ByteArray} {S : Array Seg} {x : Seg} (g : Nat) :
    ∀ k, k ≤ S.size → Region.endGo ⟨B', S.push x⟩ g k = Region.endGo ⟨B, S⟩ g k
  | 0, _ => rfl
  | k + 1, h => by
    have hk : k < S.size := by omega
    have hk' : k < (S.push x).size := by simp; omega
    unfold Region.endGo
    simp only [hk, hk', dite_true, Array.getElem_push_lt hk]
    split
    · rfl
    · exact endGo_push g k (by omega)

/-- What the search finds. -/
theorem locGo_found {r : Region} {a : UInt64} :
    ∀ k, r.locGo a k ≠ 0 → ∃ i, ∃ h : i < r.segs.size, i < k ∧ r.segs[i].hit a ∧
      r.locGo a k = r.segs[i].off + (a - r.segs[i].base).toNat ∧
      (a - r.segs[i].base).toNat + 8 ≤ r.segs[i].size
  | 0, h => absurd rfl h
  | k + 1, h => by
    unfold Region.locGo at h ⊢
    split at h
    · rename_i hk
      simp only [hk, dite_true]
      dsimp only at h ⊢
      split at h
      · rename_i hb
        simp only [hb, ite_true]
        split at h
        · rename_i hc
          simp only [hc, ite_true]
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb hc
          exact ⟨k, hk, by omega, ⟨hb.1, hb.2⟩, rfl, hc.2⟩
        · exact absurd rfl h
      · rename_i hb
        simp only [hb]
        obtain ⟨i, hi, hik, h1⟩ := locGo_found k h
        exact ⟨i, hi, by omega, h1⟩
    · exact absurd rfl h

theorem loc_some {r : Region} {a : UInt64} {c : Nat} (h : r.loc a = some c) :
    r.locGo a r.segs.size = c ∧ c ≠ 0 ∧ isScalar a = false := by
  unfold Region.loc at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hs
    split at h
    · cases h
    · rename_i h0
      cases h
      exact ⟨rfl, by simpa using h0, by simpa using hs⟩

theorem loc_of {r : Region} {a : UInt64} {c : Nat} (h : r.locGo a r.segs.size = c) (h0 : c ≠ 0)
    (hs : isScalar a = false) : r.loc a = some c := by
  simp [Region.loc, hs, h, h0]

/-- The end the search finds, the files disjoint. -/
def SegsDisj (S : Array Seg) : Prop :=
  ∀ i j (hi : i < S.size) (hj : j < S.size), i < j → S[i].off + S[i].size ≤ S[j].off

theorem endGo_in {r : Region} (hd : SegsDisj r.segs) {g i : Nat} (hi : i < r.segs.size)
    (h1 : r.segs[i].off ≤ g) (h2 : g < r.segs[i].off + r.segs[i].size) :
    ∀ k, i < k → k ≤ r.segs.size → r.endGo g k = r.segs[i].off + r.segs[i].size
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, h, hk => by
    have hk' : k < r.segs.size := by omega
    unfold Region.endGo
    simp only [hk', dite_true]
    by_cases hki : k = i
    · subst hki
      have : (decide (r.segs[k].off ≤ g) && decide (g < r.segs[k].off + r.segs[k].size)) = true := by
        simp [h1, h2]
      simp [this]
    · have hlt : i < k := by omega
      have := hd i k hi hk' hlt
      have hn : ¬ (decide (r.segs[k].off ≤ g) && decide (g < r.segs[k].off + r.segs[k].size)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      simp only [hn]
      exact endGo_in hd hi h1 h2 k hlt (by omega)

theorem endGo_le {r : Region} {n : Nat} (hs : ∀ i (hi : i < r.segs.size), r.segs[i].off + r.segs[i].size ≤ n) :
    ∀ k, r.endGo g k ≤ n
  | 0 => Nat.zero_le _
  | k + 1 => by
    unfold Region.endGo
    split
    · rename_i hk
      dsimp only
      split
      · exact hs k hk
      · exact endGo_le hs k
    · exact Nat.zero_le _

/-- **Appending a file makes a region of which the old one is the first bytes.** -/
theorem Region.Sub.append {B x : ByteArray} {S : Array Seg} {b : UInt64}
    (hd : SegsDisj S) (hend : ∀ i (hi : i < S.size), S[i].off + S[i].size ≤ B.size)
    (hbase : ∀ i (hi : i < S.size), S[i].base.toNat + S[i].size ≤ b.toNat) :
    Region.Sub ⟨B, S⟩ ⟨B ++ x, S.push ⟨b, B.size, x.size⟩⟩ B.size where
  u8 i h := rdU8_append h
  u64 i h := rdU64_append h
  extract a c h := extract_append h
  loc v c h := by
    obtain ⟨h1, h0, hs⟩ := loc_some h
    obtain ⟨i, hi, -, hhit, -⟩ := locGo_found (r := ⟨B, S⟩) S.size (by rw [h1]; exact h0)
    have hb := hbase i hi
    have hlt : v.toNat < S[i].base.toNat + S[i].size := Seg.hit_lt hhit
    apply loc_of ?_ h0 hs
    show Region.locGo _ v (S.push _).size = c
    rw [Array.size_push]
    unfold Region.locGo
    have hk : S.size < (S.push ⟨b, B.size, x.size⟩).size := by simp
    simp only [hk, dite_true, Array.getElem_push_eq]
    have hn : ¬ (decide (b ≤ v) && decide ((v - b).toNat < x.size)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h3, -⟩
      have : b.toNat ≤ v.toNat := h3
      omega
    simp only [hn]
    rw [locGo_push v S.size (Nat.le_refl _)]
    exact h1
  locLt v c h hc := by
    obtain ⟨h1, h0, hs⟩ := loc_some h
    change Region.locGo _ v (S.push _).size = c at h1
    rw [Array.size_push] at h1
    unfold Region.locGo at h1
    have hk : S.size < (S.push ⟨b, B.size, x.size⟩).size := by simp
    simp only [hk, dite_true, Array.getElem_push_eq] at h1
    split at h1
    · split at h1
      · omega
      · exact absurd h1.symm h0
    · rw [locGo_push v S.size (Nat.le_refl _)] at h1
      exact loc_of h1 h0 hs
  good v c h := by
    obtain ⟨h1, h0, -⟩ := loc_some h
    obtain ⟨i, hi, -, -, h2, h3⟩ := locGo_found (r := ⟨B, S⟩) S.size (by rw [h1]; exact h0)
    have hi' : i < S.size := hi
    have h2' : c = S[i].off + (v - S[i].base).toNat := h1.symm.trans h2
    have h3' : (v - S[i].base).toNat + 8 ≤ S[i].size := h3
    have he : Region.endGo ⟨B, S⟩ c S.size = S[i].off + S[i].size :=
      endGo_in (r := ⟨B, S⟩) (g := c) hd hi (by show S[i].off ≤ c; omega)
        (by show c < S[i].off + S[i].size; omega) S.size hi (Nat.le_refl _)
    show c + 8 ≤ Region.endGo ⟨B, S⟩ c S.size
    omega
  endEq g hg := by
    show Region.endGo _ g (S.push _).size = Region.endGo ⟨B, S⟩ g S.size
    rw [Array.size_push]
    generalize hrhs : Region.endGo ⟨B, S⟩ g S.size = e
    unfold Region.endGo
    have hk : S.size < (S.push ⟨b, B.size, x.size⟩).size := by simp
    simp only [hk, dite_true, Array.getElem_push_eq]
    have hn : ¬ (decide (B.size ≤ g) && decide (g < B.size + x.size)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp only [hn]
    rw [← hrhs]
    exact endGo_push g S.size (Nat.le_refl _)
  endLe g := endGo_le hend _

theorem Region.Sub.trans {P q r : Region} {n m : Nat} (h1 : Region.Sub P q n) (h2 : Region.Sub q r m)
    (hnm : n ≤ m) : Region.Sub P r n where
  u8 i h := (h2.u8 i (by omega)).trans (h1.u8 i h)
  u64 i h := (h2.u64 i (by omega)).trans (h1.u64 i h)
  extract a b h := (h2.extract a b (by omega)).trans (h1.extract a b h)
  loc v c h := h2.loc v c (h1.loc v c h)
  locLt v c h hc := h1.locLt v c (h2.locLt v c h (by omega)) hc
  good := h1.good
  endEq g hg := (h2.endEq g (by omega)).trans (h1.endEq g hg)
  endLe := h1.endLe

/-! ## Objects -/

/-- The object's header is inside its file. -/
abbrev Region.Good (P : Region) (g : Nat) : Prop := g + 8 ≤ P.fileEnd g

namespace Region.Sub

variable {P r : Region} {n : Nat}

theorem lt (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) : g + 8 ≤ n :=
  Nat.le_trans h (hs.endLe g)

theorem endE (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) : r.fileEnd g = P.fileEnd g :=
  hs.endEq g (by have := hs.lt h; omega)

theorem tag (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) : r.tag g = P.tag g := by
  simp only [Region.tag]
  rw [hs.u8 _ (by have := hs.lt h; omega)]

theorem nobjs (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) : r.nobjs g = P.nobjs g := by
  simp only [Region.nobjs]
  rw [hs.u8 _ (by have := hs.lt h; omega)]

theorem fits (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) : r.fits g = P.fits g := by
  simp only [Region.fits, hs.nobjs h, hs.endE h]

theorem fld (hs : Region.Sub P r n) {g i : Nat} (_h : P.Good g) (hf : P.fits g = true)
    (hi : i < P.nobjs g) : r.fld g i = P.fld g i := by
  simp only [Region.fld]
  apply hs.u64
  have h1 := hs.endLe g
  simp only [Region.fits, decide_eq_true_eq] at hf
  have : 8 * (i + 1) ≤ 8 * P.nobjs g := by omega
  omega

theorem isCtor (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) (t k : Nat) :
    r.isCtor g t k = P.isCtor g t k := by
  simp only [Region.isCtor, hs.tag h, hs.nobjs h, hs.fits h]

theorem isCtor_parts {P : Region} {g t k : Nat} (h : P.isCtor g t k = true) :
    P.tag g = t ∧ P.nobjs g = k ∧ P.fits g = true := by
  simp only [Region.isCtor, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem down (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.down g v = P.down g v := by
  simp only [Region.down]
  cases hp : P.loc v with
  | some c => rw [hs.loc v c hp]
  | none =>
    cases hr : r.loc v with
    | none => rfl
    | some c =>
      dsimp only
      split
      · rw [hs.locLt v c hr (by omega)] at hp
        cases hp
      · rfl

theorem good_of_down (hs : Region.Sub P r n) {g c : Nat} {v : UInt64} (h : P.down g v = some c) :
    P.Good c := by
  simp only [Region.down] at h
  split at h
  · rename_i c' hc
    split at h
    · cases h
      exact hs.good v _ hc
    · cases h
  · cases h

theorem okPtr (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.okPtr g v = P.okPtr g v := by
  simp only [Region.okPtr, hs.down hg]

theorem ptrFld (hs : Region.Sub P r n) {g i : Nat} (h : P.Good g) (hf : P.fits g = true)
    (hi : i < P.nobjs g) : r.ptrFld g i = P.ptrFld g i := by
  have hg : g ≤ n := by have := hs.lt h; omega
  simp only [Region.ptrFld, hs.fld h hf hi, hs.okPtr hg]

theorem u8' (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) (k : Nat) : r.u8 g k = P.u8 g k := by
  simp only [Region.u8, hs.nobjs h, hs.endE h]
  split
  · rename_i hi
    rw [hs.u8 _ (by have := hs.endLe g; omega)]
  · rfl

theorem u32' (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) (k : Nat) : r.u32 g k = P.u32 g k := by
  simp only [Region.u32, hs.nobjs h, hs.endE h]
  split
  · rename_i hi
    have := hs.endLe g
    simp only [rdU32]
    rw [hs.u8 _ (by omega), hs.u8 _ (by omega), hs.u8 _ (by omega), hs.u8 _ (by omega)]
  · rfl

theorem bool (hs : Region.Sub P r n) {g : Nat} (h : P.Good g) (k : Nat) : r.bool g k = P.bool g k := by
  simp only [Region.bool, hs.u8' h]

end Region.Sub

theorem limbsFold_congr {b b' : ByteArray} {lo : Nat} :
    ∀ k acc, (∀ i, i + 8 ≤ lo + 8 * k → lo ≤ i → rdU64 b i = rdU64 b' i) →
      limbsFold b lo k acc = limbsFold b' lo k acc
  | 0, _, _ => rfl
  | k + 1, acc, h => by
    simp only [limbsFold]
    rw [h (lo + 8 * k) (by omega) (by omega)]
    exact limbsFold_congr k _ fun i h1 h2 => h i (by omega) h2

theorem limbs_congr {b b' : ByteArray} (k : Nat) :
    ∀ lo, (∀ i, i + 8 ≤ lo + 8 * k → lo ≤ i → rdU64 b i = rdU64 b' i) →
      limbs b lo k = limbs b' lo k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro lo h
    unfold limbs
    split
    · exact limbsFold_congr k 0 h
    · rename_i hk
      dsimp only
      rw [ih (k / 2) (by omega) lo fun i h1 h2 => h i (by omega) h2,
        ih (k - k / 2) (by omega) (lo + 8 * (k / 2)) fun i h1 h2 => h i (by omega) (by omega)]

namespace Region.Sub

variable {P r : Region} {n : Nat}

theorem mpzAt (hs : Region.Sub P r n) {c : Nat} (h : P.Good c) (v : UInt64) :
    r.mpzAt c v = P.mpzAt c v := by
  simp only [Region.mpzAt, hs.tag h, hs.endE h]
  split
  · have hle := hs.endLe c
    by_cases hc : c + 24 ≤ P.fileEnd c
    · have h1 : rdU32 r.bytes (c + 12) = rdU32 P.bytes (c + 12) := by
        simp only [rdU32]
        rw [hs.u8 _ (by omega), hs.u8 _ (by omega), hs.u8 _ (by omega), hs.u8 _ (by omega)]
      rw [h1, hs.u64 _ (by omega)]
      split
      · rename_i hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        have hb3 := hb.2
        rw [limbs_congr _ _ fun i h1 _ => hs.u64 i (by omega)]
      · rfl
    · have hf : ∀ (k : Nat), decide (c + 24 + 8 * k ≤ P.fileEnd c) = false := by
        intro k
        simp only [decide_eq_false_iff_not]
        omega
      simp [hf]
  · rfl

theorem strAt (hs : Region.Sub P r n) {c : Nat} (h : P.Good c) : r.strAt c = P.strAt c := by
  simp only [Region.strAt, hs.tag h, hs.endE h]
  split
  · have hle := hs.endLe c
    by_cases hc : c + 16 ≤ P.fileEnd c
    · rw [hs.u64 _ (by omega)]
      generalize (rdU64 P.bytes (c + 8)).toNat = sz
      by_cases hb : (decide (1 ≤ sz) && decide (c + 32 + sz ≤ P.fileEnd c)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        rw [hs.u8 _ (by omega), hs.extract _ _ (by omega)]
      · have hb' := Bool.eq_false_iff.mpr hb
        simp only [hb', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · have hf : ∀ k : Nat, decide (c + 32 + k ≤ P.fileEnd c) = false := by
        intro k
        simp only [decide_eq_false_iff_not]
        omega
      simp [hf]
  · rfl

theorem natP (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.natP g v = P.natP g v := by
  simp only [Region.natP, hs.down hg]
  split
  · rfl
  · cases hd : P.down g v with
    | none => rfl
    | some c => exact hs.mpzAt (hs.good_of_down hd) v

theorem strP (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.strP g v = P.strP g v := by
  simp only [Region.strP, hs.down hg]
  cases hd : P.down g v with
  | none => rfl
  | some c => exact hs.strAt (hs.good_of_down hd)

theorem litP (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.litP g v = P.litP g v := by
  simp only [Region.litP, hs.down hg]
  cases hd : P.down g v with
  | none => rfl
  | some c =>
    have hc := hs.good_of_down hd
    have hl := hs.lt hc
    dsimp only
    simp only [hs.isCtor hc]
    split
    · rename_i h1
      obtain ⟨-, h2, h3⟩ := isCtor_parts h1
      rw [hs.fld hc h3 (by omega), hs.natP (by omega)]
    · split
      · rename_i h1
        obtain ⟨-, h2, h3⟩ := isCtor_parts ‹_›
        rw [hs.fld hc h3 (by omega), hs.strP (by omega)]
      · rfl

end Region.Sub

theorem Region.nameIn_eq (r : Region) (g : Nat) (v : UInt64) (f : Nat → Option Name) :
    r.nameIn g v (fun c _ => f c) = if v == 1 then some .anonymous else (r.down g v).bind f := by
  simp only [Region.nameIn]
  split
  · rfl
  · split <;> simp_all

theorem Region.levelIn_eq (r : Region) (g : Nat) (v : UInt64) (f : Nat → Option Level) :
    r.levelIn g v (fun c _ => f c) = if v == 1 then some .zero else (r.down g v).bind f := by
  simp only [Region.levelIn]
  split
  · rfl
  · split <;> simp_all

theorem Region.levelsIn_eq (r : Region) (g : Nat) (v : UInt64) (f : Nat → Option (List Level)) :
    r.levelsIn g v (fun c _ => f c) = if v == 1 then some [] else (r.down g v).bind f := by
  simp only [Region.levelsIn]
  split
  · rfl
  · split <;> simp_all

theorem Region.exprIn_eq (r : Region) (g : Nat) (v : UInt64) (f : Nat → Option Expr) :
    r.exprIn g v (fun c _ => f c) = (r.down g v).bind f := by
  simp only [Region.exprIn]
  split <;> simp_all

theorem bind_congr' {α β : Type} {x x' : Option α} {f f' : α → Option β} (hx : x = x')
    (hf : ∀ a, x' = some a → f a = f' a) : (x >>= f) = (x' >>= f') := by
  subst hx
  cases hc : x with
  | none => rfl
  | some a => exact hf a hc

namespace Region.Sub

variable {P r : Region} {n : Nat}

theorem down_bind {α : Type} (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64)
    {f f' : Nat → Option α} (hf : ∀ c, P.Good c → c < g → f c = f' c) :
    (r.down g v).bind f = (P.down g v).bind f' := by
  rw [hs.down hg]
  cases hd : P.down g v with
  | none => rfl
  | some c => exact hf c (hs.good_of_down hd) (Region.down_lt hd)

theorem nameNode_sub (hs : Region.Sub P r n) {g : Nat} (hg : P.Good g) (f f' : Nat → Option Name)
    (hf : ∀ c, P.Good c → c < g → f c = f' c) :
    nameNode r g (fun c _ => f c) = nameNode P g (fun c _ => f' c) := by
  have hgn : g ≤ n := by have := hs.lt hg; omega
  have NI : ∀ v, r.nameIn g v (fun c _ => f c) = P.nameIn g v (fun c _ => f' c) := by
    intro v
    simp only [Region.nameIn_eq, hs.down_bind hgn v hf]
  unfold nameNode
  rw [hs.fits hg]
  split
  · rename_i hF
    rw [hs.tag hg, hs.nobjs hg]
    split
    all_goals simp (disch := omega) only [hs.fld hg hF, NI, hs.strP hgn, hs.natP hgn]
  · rfl

theorem levelNode_sub (hs : Region.Sub P r n) {g : Nat} (hg : P.Good g) (f f' : Nat → Option Level)
    (m m' : Nat → Option Name) (hf : ∀ c, P.Good c → c < g → f c = f' c)
    (hm : ∀ c, P.Good c → c < g → m c = m' c) :
    levelNode r g (fun c _ => f c) (fun c _ => m c) = levelNode P g (fun c _ => f' c) (fun c _ => m' c) := by
  have hgn : g ≤ n := by have := hs.lt hg; omega
  have NI : ∀ v, r.nameIn g v (fun c _ => m c) = P.nameIn g v (fun c _ => m' c) := by
    intro v
    simp only [Region.nameIn_eq, hs.down_bind hgn v hm]
  have LI : ∀ v, r.levelIn g v (fun c _ => f c) = P.levelIn g v (fun c _ => f' c) := by
    intro v
    simp only [Region.levelIn_eq, hs.down_bind hgn v hf]
  unfold levelNode
  rw [hs.fits hg]
  split
  · rename_i hF
    rw [hs.tag hg, hs.nobjs hg]
    split
    all_goals simp (disch := omega) only [hs.fld hg hF, NI, LI]
  · rfl

theorem levelsNode_sub (hs : Region.Sub P r n) {g : Nat} (hg : P.Good g)
    (f f' : Nat → Option (List Level)) (l l' : Nat → Option Level)
    (hf : ∀ c, P.Good c → c < g → f c = f' c) (hl : ∀ c, P.Good c → c < g → l c = l' c) :
    levelsNode r g (fun c _ => f c) (fun c _ => l c) = levelsNode P g (fun c _ => f' c) (fun c _ => l' c) := by
  have hgn : g ≤ n := by have := hs.lt hg; omega
  have LI : ∀ v, r.levelIn g v (fun c _ => l c) = P.levelIn g v (fun c _ => l' c) := by
    intro v
    simp only [Region.levelIn_eq, hs.down_bind hgn v hl]
  have LsI : ∀ v, r.levelsIn g v (fun c _ => f c) = P.levelsIn g v (fun c _ => f' c) := by
    intro v
    simp only [Region.levelsIn_eq, hs.down_bind hgn v hf]
  unfold levelsNode
  rw [hs.fits hg]
  split
  · rename_i hF
    rw [hs.tag hg, hs.nobjs hg]
    split
    all_goals simp (disch := omega) only [hs.fld hg hF, LI, LsI]
  · rfl

theorem exprNode_sub (hs : Region.Sub P r n) {g : Nat} (hg : P.Good g) (e e' : Nat → Option Expr)
    (m m' : Nat → Option Name) (l l' : Nat → Option Level) (ls ls' : Nat → Option (List Level))
    (he : ∀ c, P.Good c → c < g → e c = e' c) (hm : ∀ c, P.Good c → c < g → m c = m' c)
    (hl : ∀ c, P.Good c → c < g → l c = l' c) (hls : ∀ c, P.Good c → c < g → ls c = ls' c) :
    exprNode r g (fun c _ => e c) (fun c _ => m c) (fun c _ => l c) (fun c _ => ls c) =
      exprNode P g (fun c _ => e' c) (fun c _ => m' c) (fun c _ => l' c) (fun c _ => ls' c) := by
  have hgn : g ≤ n := by have := hs.lt hg; omega
  have NI : ∀ v, r.nameIn g v (fun c _ => m c) = P.nameIn g v (fun c _ => m' c) := by
    intro v
    simp only [Region.nameIn_eq, hs.down_bind hgn v hm]
  have LI : ∀ v, r.levelIn g v (fun c _ => l c) = P.levelIn g v (fun c _ => l' c) := by
    intro v
    simp only [Region.levelIn_eq, hs.down_bind hgn v hl]
  have LsI : ∀ v, r.levelsIn g v (fun c _ => ls c) = P.levelsIn g v (fun c _ => ls' c) := by
    intro v
    simp only [Region.levelsIn_eq, hs.down_bind hgn v hls]
  have EI : ∀ v, r.exprIn g v (fun c _ => e c) = P.exprIn g v (fun c _ => e' c) := by
    intro v
    simp only [Region.exprIn_eq, hs.down_bind hgn v he]
  unfold exprNode
  rw [hs.fits hg]
  split
  · rename_i hF
    rw [hs.tag hg, hs.nobjs hg]
    split
    all_goals simp (disch := omega) only [hs.fld hg hF, NI, LI, LsI, EI, hs.natP hgn, hs.litP hgn]
  · rfl

theorem nameAt_sub (hs : Region.Sub P r n) (g : Nat) : P.Good g → nameAt r g = nameAt P g := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg
    rw [nameAt.eq_def r g, nameAt.eq_def P g]
    exact hs.nameNode_sub hg _ _ fun c hc hlt => ih c hlt hc

theorem levelAt_sub (hs : Region.Sub P r n) (g : Nat) : P.Good g → levelAt r g = levelAt P g := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg
    rw [levelAt.eq_def r g, levelAt.eq_def P g]
    exact hs.levelNode_sub hg _ _ _ _ (fun c hc hlt => ih c hlt hc)
      (fun c hc _ => hs.nameAt_sub c hc)

theorem levelsAt_sub (hs : Region.Sub P r n) (g : Nat) : P.Good g → levelsAt r g = levelsAt P g := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg
    rw [levelsAt.eq_def r g, levelsAt.eq_def P g]
    exact hs.levelsNode_sub hg _ _ _ _ (fun c hc hlt => ih c hlt hc)
      (fun c hc _ => hs.levelAt_sub c hc)

theorem exprAt_sub (hs : Region.Sub P r n) (g : Nat) : P.Good g → exprAt r g = exprAt P g := by
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg
    rw [exprAt.eq_def r g, exprAt.eq_def P g]
    exact hs.exprNode_sub hg _ _ _ _ _ _ _ _ (fun c hc hlt => ih c hlt hc)
      (fun c hc _ => hs.nameAt_sub c hc) (fun c hc _ => hs.levelAt_sub c hc)
      (fun c hc _ => hs.levelsAt_sub c hc)

/-! ## Arrays and lists -/

theorem objArrayGo_sub (hs : Region.Sub P r n) {c lo k : Nat} (hc : c ≤ n) (hk : lo + 8 * k ≤ n) :
    ∀ m i acc, k - i = m → r.objArrayGo c lo k i acc = P.objArrayGo c lo k i acc := by
  intro m
  induction m with
  | zero =>
    intro i acc h
    rw [Region.objArrayGo.eq_def r, Region.objArrayGo.eq_def P]
    simp only [show ¬ i < k by omega, ↓reduceIte]
  | succ m ih =>
    intro i acc h
    rw [Region.objArrayGo.eq_def r, Region.objArrayGo.eq_def P]
    have hi : i < k := by omega
    have : 8 * (i + 1) ≤ 8 * k := by omega
    simp only [hi, ↓reduceIte]
    rw [hs.u64 _ (by omega), hs.down hc]
    cases P.down c (rdU64 P.bytes (lo + 8 * i)) with
    | none => rfl
    | some e => exact ih _ _ (by omega)

theorem objArray_sub (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.objArray g v = P.objArray g v := by
  simp only [Region.objArray, hs.down hg]
  cases hd : P.down g v with
  | none => rfl
  | some c =>
    have hc := hs.good_of_down hd
    have hle := hs.endLe c
    simp only [hs.tag hc, hs.endE hc]
    split
    · by_cases hc2 : c + 16 ≤ P.fileEnd c
      · rw [hs.u64 _ (by omega)]
        split
        · exact hs.objArrayGo_sub (by omega) (by omega) _ _ _ rfl
        · rfl
      · have hf : ∀ k : Nat, ¬ c + 24 + 8 * k ≤ P.fileEnd c := by intro k; omega
        simp [hf]
    · rfl

theorem objArrayGo_good (hs : Region.Sub P r n) {c lo k : Nat} :
    ∀ m i (acc arr : Array Nat), k - i = m → P.objArrayGo c lo k i acc = some arr →
      (∀ e ∈ acc, P.Good e) → ∀ e ∈ arr, P.Good e := by
  intro m
  induction m with
  | zero =>
    intro i acc arr h ha hacc
    rw [Region.objArrayGo.eq_def] at ha
    simp only [show ¬ i < k by omega, ↓reduceIte, Option.some.injEq] at ha
    subst ha
    exact hacc
  | succ m ih =>
    intro i acc arr h ha hacc
    rw [Region.objArrayGo.eq_def] at ha
    simp only [show i < k by omega, ↓reduceIte] at ha
    split at ha
    · rename_i e hd
      refine ih _ _ _ (by omega) ha fun x hx => ?_
      rcases Array.mem_push.mp hx with hx | rfl
      · exact hacc x hx
      · exact hs.good_of_down hd
    · cases ha

theorem objArray_good (hs : Region.Sub P r n) {g : Nat} {v : UInt64} {arr : Array Nat}
    (h : P.objArray g v = some arr) : ∀ e ∈ arr, P.Good e := by
  simp only [Region.objArray] at h
  split at h
  · split at h
    · split at h
      · exact hs.objArrayGo_good _ _ _ _ rfl h (by simp)
      · cases h
    · cases h
  · cases h

theorem listGo_sub (hs : Region.Sub P r n) (c : Nat) :
    P.Good c → ∀ acc, r.listGo c acc = P.listGo c acc := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro hc acc
    rw [Region.listGo.eq_def r, Region.listGo.eq_def P]
    have hcn : c ≤ n := by have := hs.lt hc; omega
    simp only [hs.isCtor hc]
    split
    · rename_i hC
      obtain ⟨-, hN, hF⟩ := isCtor_parts hC
      rw [hs.ptrFld hc hF (by omega)]
      split
      · rw [hs.fld hc hF (by omega)]
        split
        · rfl
        · rw [hs.down hcn]
          split
          · rename_i c' hc'
            exact ih c' (Region.down_lt hc') (hs.good_of_down hc') _
          · rfl
      · rfl
    · rfl

theorem list_sub (hs : Region.Sub P r n) {g : Nat} (hg : g ≤ n) (v : UInt64) :
    r.list g v = P.list g v := by
  simp only [Region.list, hs.down hg]
  split
  · rfl
  · cases hd : P.down g v with
    | none => rfl
    | some c => exact hs.listGo_sub c (hs.good_of_down hd) _

/-! ## The skeletons -/

theorem hintsSkel_sub (hs : Region.Sub P r n) {x : Nat} (hx : P.Good x) (hv : UInt64) :
    hintsSkel r x hv = hintsSkel P x hv := by
  have hxn : x ≤ n := by have := hs.lt hx; omega
  unfold hintsSkel
  split
  · rfl
  · split
    · rfl
    · rw [hs.down hxn]
      refine bind_congr' rfl fun h hd => ?_
      have hh := hs.good_of_down hd
      simp only [hs.isCtor hh, hs.u32' hh]

theorem ruleSkel_sub (hs : Region.Sub P r n) {x : Nat} (hx : P.Good x) (v : UInt64) :
    ruleSkel r x v = ruleSkel P x v := by
  have hxn : x ≤ n := by have := hs.lt hx; omega
  unfold ruleSkel
  refine bind_congr' (hs.down hxn v) fun y hd => ?_
  have hy := hs.good_of_down hd
  have hyn : y ≤ n := by have := hs.lt hy; omega
  simp only [hs.isCtor hy]
  split
  · rename_i hC
    obtain ⟨-, hN, hF⟩ := isCtor_parts hC
    simp (disch := omega) only [hs.fld hy hF, hs.ptrFld hy hF, hs.natP hyn]
  · rfl

theorem kindSkel_sub (hs : Region.Sub P r n) {x : Nat} (hx : P.Good x) (t : Nat) :
    kindSkel r t x = kindSkel P t x := by
  have hxn : x ≤ n := by have := hs.lt hx; omega
  have R : ruleSkel r x = ruleSkel P x := funext (hs.ruleSkel_sub hx)
  unfold kindSkel
  split
  all_goals
    simp only [hs.isCtor hx]
    split
    · rename_i hC
      obtain ⟨-, hN, hF⟩ := isCtor_parts hC
      simp (disch := omega) only [Region.natF, Region.nameList, hs.fld hx hF, hs.ptrFld hx hF,
        hs.natP hxn, hs.list_sub hxn, hs.bool hx, hs.u8' hx, hs.hintsSkel_sub hx, R]
    · rfl

theorem constSkel_sub (hs : Region.Sub P r n) {c : Nat} (hc : P.Good c) :
    constSkel r c = constSkel P c := by
  have hcn : c ≤ n := by have := hs.lt hc; omega
  unfold constSkel
  simp only [hs.nobjs hc, hs.tag hc, hs.fits hc]
  split
  · rename_i hG
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hG
    obtain ⟨⟨hN, -⟩, hF⟩ := hG
    refine bind_congr' (by rw [hs.fld hc hF (by omega), hs.down hcn]) fun x hd => ?_
    have hx := hs.good_of_down hd
    have hxn : x ≤ n := by have := hs.lt hx; omega
    simp only [hs.nobjs hx, hs.fits hx]
    split
    · rename_i hG2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hG2
      obtain ⟨hN2, hF2⟩ := hG2
      refine bind_congr' (by rw [hs.fld hx hF2 (by omega), hs.down hxn]) fun cv hd2 => ?_
      have hcv := hs.good_of_down hd2
      have hcvn : cv ≤ n := by have := hs.lt hcv; omega
      simp only [hs.isCtor hcv]
      split
      · rename_i hC
        obtain ⟨-, hN3, hF3⟩ := isCtor_parts hC
        refine bind_congr' (hs.ptrFld hcv hF3 (by omega)) fun _ _ => ?_
        refine bind_congr' (by simp only [Region.nameList]; rw [hs.fld hcv hF3 (by omega), hs.list_sub hcvn])
          fun _ _ => ?_
        refine bind_congr' (hs.ptrFld hcv hF3 (by omega)) fun _ _ => ?_
        refine bind_congr' (hs.kindSkel_sub hx _) fun _ _ => rfl
      · rfl
    · rfl
  · rfl

/-! ## The pointers a skeleton holds -/

end Region.Sub

/-- A pointer a skeleton holds: a scalar, or at a location. -/
abbrev Region.PtrOk (P : Region) (v : UInt64) : Prop := isScalar v = true ∨ (P.loc v).isSome = true

theorem ptrOk_of_okPtr {P : Region} {g : Nat} {v : UInt64} (h : P.okPtr g v = true) : P.PtrOk v := by
  simp only [Region.okPtr, Bool.or_eq_true] at h
  rcases h with h | h
  · exact .inl h
  · refine .inr ?_
    simp only [Region.down] at h
    split at h
    · simp_all
    · cases h

theorem ptrFld_ok {P : Region} {g i : Nat} {v : UInt64} (h : P.ptrFld g i = some v) : P.PtrOk v := by
  simp only [Region.ptrFld] at h
  split at h
  · cases h
    exact ptrOk_of_okPtr ‹_›
  · cases h

theorem listGo_ok {P : Region} (c : Nat) :
    ∀ acc arr, P.listGo c acc = some arr → (∀ e ∈ acc, P.PtrOk e) → ∀ e ∈ arr, P.PtrOk e := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro acc arr h hacc
    rw [Region.listGo.eq_def] at h
    split at h
    · split at h
      · rename_i hd hp
        have hP : ∀ e ∈ acc.push hd, P.PtrOk e := by
          intro x hx
          rcases Array.mem_push.mp hx with hx | rfl
          · exact hacc x hx
          · exact ptrFld_ok hp
        dsimp only at h
        split at h
        · cases h
          exact hP
        · split at h
          · rename_i c' hc'
            exact ih c' (Region.down_lt hc') _ _ h hP
          · cases h
      · cases h
    · cases h

theorem list_ok {P : Region} {g : Nat} {v : UInt64} {arr : Array UInt64} (h : P.list g v = some arr) :
    ∀ e ∈ arr, P.PtrOk e := by
  simp only [Region.list] at h
  split at h
  · cases h
    simp
  · split at h
    · exact listGo_ok _ _ _ h (by simp)
    · cases h

theorem nameList_ok {P : Region} {g i : Nat} {l : List UInt64} (h : P.nameList g i = some l) :
    ∀ e ∈ l, P.PtrOk e := by
  simp only [Region.nameList] at h
  cases hl : P.list g (P.fld g i) with
  | none => simp [hl] at h
  | some arr =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    subst h
    intro e he
    exact list_ok hl e (by simpa using he)

theorem ruleSkel_ok {P : Region} {x : Nat} {v : UInt64} {y : UInt64 × Nat × UInt64}
    (h : ruleSkel P x v = some y) : P.PtrOk y.1 ∧ P.PtrOk y.2.2 := by
  unfold ruleSkel at h
  obtain ⟨c, -, h⟩ := bind_some_left h
  split at h
  · obtain ⟨a, ha, h⟩ := bind_some_left h
    obtain ⟨b, -, h⟩ := bind_some_left h
    obtain ⟨d, hd, h⟩ := bind_some_left h
    cases h
    exact ⟨ptrFld_ok ha, ptrFld_ok hd⟩
  · cases h

/-- What a kind's skeleton holds is at locations. -/
def KindOk (P : Region) : CKindF UInt64 UInt64 → Prop
  | .defn v _ _ | .opaq v _ | .ctor v .. => P.PtrOk v
  | .thm v all => P.PtrOk v ∧ ∀ x ∈ all, P.PtrOk x
  | .induct _ _ all cs .. => (∀ x ∈ all, P.PtrOk x) ∧ ∀ x ∈ cs, P.PtrOk x
  | .recur all _ _ _ _ rules .. =>
    (∀ x ∈ all, P.PtrOk x) ∧ ∀ y ∈ rules, P.PtrOk y.1 ∧ P.PtrOk y.2.2
  | .ax _ | .quot _ => True

theorem kindSkel_ok {P : Region} {t x : Nat} {k : CKindF UInt64 UInt64}
    (h : kindSkel P t x = some k) : KindOk P k := by
  unfold kindSkel at h
  split at h
  · split at h
    · obtain ⟨_, -, h⟩ := bind_some_left h
      cases h; trivial
    · cases h
  · split at h
    · obtain ⟨v, hv, h⟩ := bind_some_left h
      obtain ⟨_, -, h⟩ := bind_some_left h
      obtain ⟨_, -, h⟩ := bind_some_left h
      dsimp only at h
      split at h
      all_goals first
        | (cases h; done)
        | (simp only [bind, Option.bind, pure, Option.some.injEq] at h
           subst h
           exact ptrFld_ok hv)
    · cases h
  · split at h
    · obtain ⟨v, hv, h⟩ := bind_some_left h
      obtain ⟨a, ha, h⟩ := bind_some_left h
      cases h
      exact ⟨ptrFld_ok hv, nameList_ok ha⟩
    · cases h
  · split at h
    · obtain ⟨v, hv, h⟩ := bind_some_left h
      obtain ⟨_, -, h⟩ := bind_some_left h
      cases h
      exact ptrFld_ok hv
    · cases h
  · split at h
    · obtain ⟨_, -, h⟩ := bind_some_left h
      dsimp only at h
      split at h
      all_goals first
        | (cases h; done)
        | (simp only [bind, Option.bind, pure, Option.some.injEq] at h
           subst h
           trivial)
    · cases h
  · split at h
    · obtain ⟨_, -, h⟩ := bind_some_left h
      obtain ⟨_, -, h⟩ := bind_some_left h
      obtain ⟨a, ha, h⟩ := bind_some_left h
      obtain ⟨c, hc, h⟩ := bind_some_left h
      repeat' (obtain ⟨_, -, h⟩ := bind_some_left h)
      cases h
      exact ⟨nameList_ok ha, nameList_ok hc⟩
    · cases h
  · split at h
    · obtain ⟨v, hv, h⟩ := bind_some_left h
      repeat' (obtain ⟨_, -, h⟩ := bind_some_left h)
      cases h
      exact ptrFld_ok hv
    · cases h
  · split at h
    · obtain ⟨a, ha, h⟩ := bind_some_left h
      obtain ⟨cells, -, h⟩ := bind_some_left h
      obtain ⟨rs, hrs, h⟩ := bind_some_left h
      repeat' (obtain ⟨_, -, h⟩ := bind_some_left h)
      cases h
      refine ⟨nameList_ok ha, fun y hy => ?_⟩
      obtain ⟨v, -, hv⟩ := mapM_mem_inv hrs hy
      exact ruleSkel_ok hv
    · cases h

theorem constSkel_ok {P : Region} {c : Nat} {s : CEntryF UInt64 UInt64} (h : constSkel P c = some s) :
    (∀ v ∈ s.names, P.PtrOk v) ∧ (∀ v ∈ s.exprs, P.PtrOk v) := by
  unfold constSkel at h
  split at h
  · obtain ⟨x, -, h⟩ := bind_some_left h
    split at h
    · obtain ⟨cv, -, h⟩ := bind_some_left h
      split at h
      · obtain ⟨nm, hn, h⟩ := bind_some_left h
        obtain ⟨ls, hl, h⟩ := bind_some_left h
        obtain ⟨ty, ht, h⟩ := bind_some_left h
        obtain ⟨k, hk, h⟩ := bind_some_left h
        cases h
        have hK := kindSkel_ok hk
        have h1 : P.PtrOk nm := ptrFld_ok hn
        have h2 := nameList_ok hl
        have h3 : P.PtrOk ty := ptrFld_ok ht
        constructor
        · intro v hv
          simp only [CEntryF.names, List.mem_cons, List.mem_append] at hv
          rcases hv with (rfl | hv) | hv
          · exact h1
          · exact h2 v hv
          cases k <;> simp only [KindOk] at hK <;> simp_all
          all_goals grind
        · intro v hv
          simp only [CEntryF.exprs, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact h3
          cases k <;> simp only [KindOk] at hK <;> simp_all
          all_goals grind
      · cases h
    · cases h
  · cases h

namespace Region.Sub

variable {P r : Region} {n : Nat}

theorem loc_ok (hs : Region.Sub P r n) {v : UInt64} (h : P.PtrOk v) : r.loc v = P.loc v := by
  rcases h with h | h
  · simp [Region.loc, h]
  · cases hp : P.loc v with
    | none => simp [hp] at h
    | some c => exact hs.loc v c hp

theorem nameP_sub (hs : Region.Sub P r n) {v : UInt64} (h : P.PtrOk v) : nameP r v = nameP P v := by
  simp only [nameP, hs.loc_ok h]
  split
  · rfl
  · cases hp : P.loc v with
    | none => rfl
    | some c => exact hs.nameAt_sub c (hs.good v c hp)

theorem exprP_sub (hs : Region.Sub P r n) {v : UInt64} (h : P.PtrOk v) : exprP r v = exprP P v := by
  simp only [exprP, hs.loc_ok h]
  cases hp : P.loc v with
  | none => rfl
  | some c => exact hs.exprAt_sub c (hs.good v c hp)

theorem constSpec_sub (hs : Region.Sub P r n) {c : Nat} (hc : P.Good c) :
    constSpec r c = constSpec P c := by
  unfold constSpec
  refine bind_congr' (hs.constSkel_sub hc) fun s hk => ?_
  obtain ⟨h1, h2⟩ := constSkel_ok hk
  exact CEntryF.mapM_congr s (fun v hv => hs.nameP_sub (h1 v hv)) (fun v hv => hs.exprP_sub (h2 v hv))

theorem constNamesGo_sub (hs : Region.Sub P r n) :
    ∀ {ns cs : List Nat}, (∀ x ∈ ns, P.Good x) → (∀ x ∈ cs, P.Good x) → ∀ seen,
      constNamesGo r ns cs seen = constNamesGo P ns cs seen
  | [], [], _, _, _ => by simp [constNamesGo]
  | [], _ :: _, _, _, _ => by simp [constNamesGo]
  | _ :: _, [], _, _, _ => by simp [constNamesGo]
  | m :: ns, c :: cs, h1, h2, seen => by
    unfold constNamesGo
    rw [hs.constSkel_sub (h2 c List.mem_cons_self), hs.nameAt_sub m (h1 m List.mem_cons_self)]
    split
    · rename_i sk a hsk hna
      have hok : P.PtrOk sk.name := (constSkel_ok hsk).1 _ (by simp [CEntryF.names])
      have IH := fun seen => hs.constNamesGo_sub (ns := ns) (cs := cs)
        (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) seen
      simp only [hs.loc_ok hok, hs.nameP_sub hok, IH]
    · rfl

theorem constNamesOk_sub (hs : Region.Sub P r n) {a : UInt64} {g : Nat} (hl : P.loc a = some g) :
    constNamesOk r a = constNamesOk P a := by
  unfold constNamesOk
  rw [hs.loc a g hl, hl]
  have hg := hs.good a g hl
  have hgn : g ≤ n := by have := hs.lt hg; omega
  dsimp only
  rw [hs.isCtor hg]
  split
  · rename_i hC
    obtain ⟨-, hN, hF⟩ := isCtor_parts hC
    rw [hs.fld hg hF (by omega), hs.fld hg hF (by omega), hs.objArray_sub hgn, hs.objArray_sub hgn]
    split
    · rename_i ns cs h1 h2
      rw [hs.constNamesGo_sub (fun x hx => hs.objArray_good h1 x (by simpa using hx))
        (fun x hx => hs.objArray_good h2 x (by simpa using hx))]
    · rfl
  · rfl

theorem importSkel_sub (hs : Region.Sub P r n) {i : Nat} (hi : P.Good i) :
    importSkel r i = importSkel P i := by
  unfold importSkel
  simp only [hs.isCtor hi]
  split
  · rename_i hC
    obtain ⟨-, hN, hF⟩ := isCtor_parts hC
    simp (disch := omega) only [hs.ptrFld hi hF, hs.bool hi]
  · rfl

theorem moduleSkel_sub (hs : Region.Sub P r n) {a : UInt64} {g : Nat} (hl : P.loc a = some g) :
    moduleSkel r a = moduleSkel P a := by
  unfold moduleSkel
  refine bind_congr' (hs.loc a g hl |>.trans hl.symm) fun g' hg' => ?_
  obtain rfl : g = g' := Option.some.inj (hl.symm.trans hg')
  have hg := hs.good a g hl
  have hgn : g ≤ n := by have := hs.lt hg; omega
  simp only [hs.isCtor hg]
  split
  · rename_i hC
    obtain ⟨-, hN, hF⟩ := isCtor_parts hC
    refine bind_congr' (hs.bool hg 0) fun _ _ => ?_
    refine bind_congr' (by rw [hs.fld hg hF (by omega), hs.objArray_sub hgn]) fun imps hi => ?_
    refine bind_congr' (listMapM_congr _ fun i hm =>
      hs.importSkel_sub (hs.objArray_good hi i (by simpa using hm))) fun _ _ => ?_
    refine bind_congr' (by rw [hs.fld hg hF (by omega), hs.objArray_sub hgn]) fun _ _ => rfl
  · rfl

/-- What a module's skeleton holds is at locations. -/
theorem moduleSkel_ok (hs : Region.Sub P r n) {a : UInt64} {sk : ModSkel} (h : moduleSkel P a = some sk) :
    (∀ c ∈ sk.consts, P.Good c) ∧ ∀ i ∈ sk.imports, P.PtrOk i.module := by
  unfold moduleSkel at h
  obtain ⟨g, -, h⟩ := bind_some_left h
  split at h
  · obtain ⟨_, -, h⟩ := bind_some_left h
    obtain ⟨imps, -, h⟩ := bind_some_left h
    obtain ⟨is, his, h⟩ := bind_some_left h
    obtain ⟨cs, hcs, h⟩ := bind_some_left h
    cases h
    refine ⟨fun c hc => hs.objArray_good hcs c (by simpa using hc), fun i hi => ?_⟩
    obtain ⟨v, -, hv⟩ := mapM_mem_inv his hi
    unfold importSkel at hv
    split at hv
    · obtain ⟨m, hm, hv⟩ := bind_some_left hv
      repeat' (obtain ⟨_, -, hv⟩ := bind_some_left hv)
      cases hv
      exact ptrFld_ok hm
    · cases hv
  · cases h

/-- **A `ModuleData` at an address the first bytes know reads the same.** -/
theorem decodeAt_sub (hs : Region.Sub P r n) {a : UInt64} {g : Nat} (hl : P.loc a = some g) :
    decodeAt r a = decodeAt P a := by
  unfold decodeAt
  rw [hs.constNamesOk_sub hl]
  split
  · refine bind_congr' (hs.moduleSkel_sub hl) fun sk hk => ?_
    obtain ⟨h1, h2⟩ := hs.moduleSkel_ok hk
    refine bind_congr' (listMapM_congr _ fun i hm => ImportF.mapM_congr i (hs.nameP_sub (h2 i hm)))
      fun _ _ => ?_
    refine bind_congr' (listMapM_congr _ fun c hm => hs.constSpec_sub (h1 c hm)) fun _ _ => rfl
  · simp

end Region.Sub

/-! ## The regions of a module's files -/

theorem emptyCap_append (t : Nat) (b : ByteArray) : ByteArray.emptyWithCapacity t ++ b = b := by
  apply ByteArray.ext
  simp
  rfl

theorem emptyCap_size (t : Nat) : (ByteArray.emptyWithCapacity t).size = 0 := by
  rfl

theorem ofParts_two {a b : Part} {r : Region} (h : Region.ofParts #[a, b] = .ok r) :
    r = ⟨a.bytes ++ b.bytes, #[⟨a.base, 0, a.bytes.size⟩, ⟨b.base, a.bytes.size, b.bytes.size⟩]⟩ ∧
      a.base.toNat + a.bytes.size ≤ b.base.toNat := by
  by_cases ho : a.base.toNat + a.bytes.size ≤ b.base.toNat
  · have hp : partsOrdered (#[a, b] : Array Part).toList = true := by
      simp [partsOrdered, ho]
    simp only [Region.ofParts, hp] at h
    simp [emptyCap_append, emptyCap_size] at h
    cases h
    exact ⟨rfl, ho⟩
  · have hp : partsOrdered (#[a, b] : Array Part).toList = false := by
      simp [partsOrdered, ho]
    simp only [Region.ofParts, hp] at h
    cases h

theorem ofParts_three {a b c : Part} {r : Region} (h : Region.ofParts #[a, b, c] = .ok r) :
    r = ⟨(a.bytes ++ b.bytes) ++ c.bytes, #[⟨a.base, 0, a.bytes.size⟩, ⟨b.base, a.bytes.size, b.bytes.size⟩,
        ⟨c.base, (a.bytes ++ b.bytes).size, c.bytes.size⟩]⟩ ∧
      a.base.toNat + a.bytes.size ≤ b.base.toNat ∧ b.base.toNat + b.bytes.size ≤ c.base.toNat := by
  by_cases ho : a.base.toNat + a.bytes.size ≤ b.base.toNat ∧ b.base.toNat + b.bytes.size ≤ c.base.toNat
  · have hp : partsOrdered (#[a, b, c] : Array Part).toList = true := by
      simp [partsOrdered, ho]
    simp only [Region.ofParts, hp] at h
    simp [emptyCap_append, emptyCap_size] at h
    cases h
    exact ⟨by simp, ho⟩
  · have hp : partsOrdered (#[a, b, c] : Array Part).toList = false := by
      simp only [Decidable.not_and_iff_not_or_not] at ho
      rcases ho with ho | ho <;> simp [partsOrdered, ho]
    simp only [Region.ofParts, hp] at h
    cases h

/-- **`M.olean` is the first bytes of itself and the server file.** -/
theorem Region.Sub.single_two (a b : Part) (ho : a.base.toNat + a.bytes.size ≤ b.base.toNat) :
    Region.Sub (Region.single a)
      ⟨a.bytes ++ b.bytes, #[⟨a.base, 0, a.bytes.size⟩, ⟨b.base, a.bytes.size, b.bytes.size⟩]⟩
      a.bytes.size := by
  refine Region.Sub.append (B := a.bytes) (x := b.bytes) (S := #[⟨a.base, 0, a.bytes.size⟩]) (b := b.base)
    ?_ ?_ ?_
  · intro i j hi hj hij
    simp at hi hj
    omega
  · intro i hi
    simp at hi
    subst hi
    simp
  · intro i hi
    simp at hi
    subst hi
    simpa using ho

/-- **Those two are the first bytes of the three.** -/
theorem Region.Sub.two_three (a b c : Part) (h1 : a.base.toNat + a.bytes.size ≤ b.base.toNat)
    (h2 : b.base.toNat + b.bytes.size ≤ c.base.toNat) :
    Region.Sub
      ⟨a.bytes ++ b.bytes, #[⟨a.base, 0, a.bytes.size⟩, ⟨b.base, a.bytes.size, b.bytes.size⟩]⟩
      ⟨(a.bytes ++ b.bytes) ++ c.bytes, #[⟨a.base, 0, a.bytes.size⟩, ⟨b.base, a.bytes.size, b.bytes.size⟩,
        ⟨c.base, (a.bytes ++ b.bytes).size, c.bytes.size⟩]⟩
      (a.bytes ++ b.bytes).size := by
  refine Region.Sub.append (B := a.bytes ++ b.bytes) (x := c.bytes)
    (S := #[⟨a.base, 0, a.bytes.size⟩, ⟨b.base, a.bytes.size, b.bytes.size⟩]) (b := c.base) ?_ ?_ ?_
  · intro i j hi hj hij
    simp at hi hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 1 := by omega
    simp
  · intro i hi
    simp at hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp
    · simp
  · intro i hi
    simp at hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa using (by omega : a.base.toNat + a.bytes.size ≤ c.base.toNat)
    · simpa using h2

/-- A `ModuleData` at an address no file holds does not read. -/
theorem decodeAt_of_loc {r : Region} {a : UInt64} (h : r.loc a = none) : decodeAt r a = none := by
  unfold decodeAt constNamesOk
  simp [h]

end ConLeche.Frontend.Olean
