module

public import ConLeche.Frontend.RoundsWork
public import ConLeche.Verify.Frontend.Good

public section

/-!
# The rounds keep good entries (task #329)

The round functions of `ConLeche/Frontend/RoundsWork.lean`, against the
lines of the chunks they work on:

* **Keys** (`Keys.Rep`): round 0's keys of a table are the indices the
  chunk's lines of that table bind, in order; `Keys.idx` finds a bound
  index back (`keysFind` is a binary search on increasing indices).
* **Round 0** (`round0_spec`): without an anomaly, every table of the
  chunk binds increasing indices; every entry it computed is good in
  every window the chunk is part of; its pending and declaration lines
  are the chunk's, with their counts.
* **A later round** (`roundR_spec`): every late entry it computes is
  good, given that every entry it reads is.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The indices a list of lines binds -/

/-- The indices the lines bind in table `t`, in order. -/
@[expose] def idsT (t : Tb) (rs : List LineRec) : List Nat := rs.filterMap (·.idAt t)

theorem idsT_nil (t : Tb) : idsT t [] = [] := rfl

theorem idsT_append (t : Tb) (l₁ l₂ : List LineRec) :
    idsT t (l₁ ++ l₂) = idsT t l₁ ++ idsT t l₂ := by
  simp [idsT, List.filterMap_append]

theorem idsT_cons (t : Tb) (r : LineRec) (l : List LineRec) :
    idsT t (r :: l) = (r.idAt t).toList ++ idsT t l := by
  cases h : r.idAt t <;> simp [idsT, h]

theorem idsT_singleton (t : Tb) (r : LineRec) : idsT t [r] = (r.idAt t).toList := by
  simp [idsT_cons, idsT_nil]

/-- A table's counter after some lines: one past the last index they
bind there, or where it was. -/
theorem stepAll_at (c : Ctr) (l : List LineRec) (t : Tb) :
    (c.stepAll l).at t = match (idsT t l).getLast? with
      | some i => i + 1
      | none => c.at t := by
  induction l generalizing c with
  | nil => rfl
  | cons r rs ih =>
    simp only [Ctr.stepAll]
    rw [ih, idsT_cons, Ctr.step_at]
    cases h : (idsT t rs).getLast? with
    | some i =>
      simp only [List.getLast?_append, h]
      cases r.idAt t <;> rfl
    | none =>
      have : idsT t rs = [] := List.getLast?_eq_none_iff.mp h
      rw [this]
      cases r.idAt t <;> rfl

/-- The counter after lines that bind something in table `t` does not
depend on where it started. -/
theorem stepAll_at_of_ne (c c' : Ctr) {l : List LineRec} {t : Tb} (h : idsT t l ≠ []) :
    (c.stepAll l).at t = (c'.stepAll l).at t := by
  rw [stepAll_at, stepAll_at]
  cases hl : (idsT t l).getLast? with
  | some i => rfl
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h

/-! ## Keys -/

/-- Keys `K` name the indices `l`, in order. -/
@[expose] def Keys.Rep (K : Keys) (l : List Nat) : Prop :=
  K.cnt = l.length ∧
  ((K.ids.isEmpty = true ∧ ∀ k (h : k < l.length), l[k] = K.first + k) ∨
   (K.ids.isEmpty = false ∧ K.ids.toList = l))

/-- Strictly increasing. -/
@[expose] def Incr (l : List Nat) : Prop := l.Pairwise (· < ·)

theorem keysPush_rep {n f b : Nat} {ids : Array Nat} {l : List Nat} {id : Nat}
    (hn : n = l.length) (hshape : (ids.isEmpty = true ∧ ∀ k (h : k < l.length), l[k] = f + k) ∨
      (ids.isEmpty = false ∧ ids.toList = l))
    (hb : ∀ i, l.getLast? = some i → b = i + 1) :
    let f' := if n == 0 then id else f
    let ids' := keysPush n f b ids id
    ((ids'.isEmpty = true ∧ ∀ k (h : k < (l ++ [id]).length), (l ++ [id])[k] = f' + k) ∨
      (ids'.isEmpty = false ∧ ids'.toList = l ++ [id])) := by
  intro f' ids'
  simp only [ids', f', keysPush]
  by_cases h0 : n = 0
  · subst h0
    have hl : l = [] := List.eq_nil_of_length_eq_zero hn.symm
    subst hl
    rcases hshape with ⟨he, _⟩ | ⟨he, hl⟩
    · left; refine ⟨he, ?_⟩; intro k hk; simp at hk; subst hk; simp
    · simp at hl; subst hl; simp at he
  · simp only [beq_iff_eq, h0, ↓reduceIte]
    rcases hshape with ⟨he, hd⟩ | ⟨he, hl⟩
    · simp only [he, ↓reduceIte]
      by_cases hib : id = b
      · subst hib
        simp only [↓reduceIte]
        left; refine ⟨he, ?_⟩
        intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        rw [List.getElem_append]
        split
        · exact hd k ‹_›
        · have hk' : k = l.length := by omega
          subst hk'
          have hne : l ≠ [] := by intro h; subst h; simp at hn; omega
          have hlast := hb _ (List.getLast?_eq_some_getLast hne)
          rw [List.getLast_eq_getElem] at hlast
          have := hd (l.length - 1) (by omega)
          simp only [List.getElem_singleton]
          omega
      · simp only [hib, ↓reduceIte]
        right
        refine ⟨by simp, ?_⟩
        simp only [Array.toList_push, Array.toList_map, Array.toList_range]
        congr 1
        apply List.ext_getElem (by simp [hn])
        intro k h1 h2
        simp [hd k h2]
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      right; exact ⟨by simp, by simp [hl]⟩

theorem keyOf_of_shape {K : Keys} {l : List Nat}
    (hshape : (K.ids.isEmpty = true ∧ ∀ k (h : k < l.length), l[k] = K.first + k) ∨
      (K.ids.isEmpty = false ∧ K.ids.toList = l)) :
    ∀ k (h : k < l.length), K.keyOf k = l[k] := by
  intro k hk
  rcases hshape with ⟨he, hd⟩ | ⟨he, hl⟩
  · simp [Keys.keyOf, he, hd k hk]
  · simp only [Keys.keyOf, he, Bool.false_eq_true, ↓reduceIte]
    subst hl
    have hk' : k < K.ids.size := by simpa using hk
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']

/-! ## The binary search -/

theorem keysFind_spec (a : Array Nat) (j : Nat)
    (hs : ∀ i i' (hle : i ≤ i') (h : i' < a.size), a[i]'(by omega) ≤ a[i']) :
    ∀ lo hi, hi ≤ a.size → lo ≤ hi →
    (∀ i (h : i < a.size), i < lo → a[i] < j) → (∀ i (h : i < a.size), hi ≤ i → j ≤ a[i]) →
    (∀ i (h : i < a.size), i < keysFind a j lo hi → a[i] < j) ∧
    (∀ i (h : i < a.size), keysFind a j lo hi ≤ i → j ≤ a[i]) := by
  intro lo hi
  induction lo, hi using keysFind.induct a j with
  | case1 lo hi hlh mid hm ih =>
    intro hhi hle hlo hhi'
    rw [keysFind, ite_eq_left hlh]
    simp only [show ((lo + hi) / 2) = mid from rfl, hm, ↓reduceIte]
    have hmid : mid < a.size := by omega
    have hm' : a[mid] < j := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid,
        Option.getD_some] at hm; exact hm
    exact ih hhi (by omega) (fun i h hi => by
        rcases Nat.lt_or_ge i mid with h' | h'
        · exact Nat.lt_of_le_of_lt (hs i mid (by omega) hmid) hm'
        · have : i = mid := by omega
          subst this; exact hm') hhi'
  | case2 lo hi hlh mid hm ih =>
    intro hhi hle hlo hhi'
    rw [keysFind, ite_eq_left hlh]
    simp only [show ((lo + hi) / 2) = mid from rfl, hm, ↓reduceIte]
    have hmid : mid < a.size := by omega
    have hm' : j ≤ a[mid] := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid,
        Option.getD_some, Nat.not_lt] at hm; exact hm
    exact ih (by omega) (by omega) hlo (fun i h hi => Nat.le_trans hm' (hs mid i hi h))
  | case3 lo hi hlh =>
    intro hhi hle hlo hhi'
    rw [keysFind, ite_eq_right hlh]
    exact ⟨hlo, fun i h hi => hhi' i h (by omega)⟩

/-- On strictly increasing indices, the search finds an index where it
is. -/
theorem keysFind_eq (a : Array Nat) (ha : Incr a.toList) {k : Nat} (hk : k < a.size) :
    keysFind a a[k] 0 a.size = k := by
  have hlt : ∀ i i' (hi : i < a.size) (hi' : i' < a.size), i < i' → a[i] < a[i'] := by
    intro i i' hi hi' h
    have := List.pairwise_iff_getElem.mp ha i i' (by simpa using hi) (by simpa using hi') h
    simpa using this
  have hs : ∀ i i' (hle : i ≤ i') (h : i' < a.size), a[i]'(by omega) ≤ a[i'] := by
    intro i i' hle h
    rcases Nat.lt_or_ge i i' with h1 | h1
    · exact Nat.le_of_lt (hlt i i' _ h h1)
    · have : i = i' := by omega
      subst this; exact Nat.le_refl _
  obtain ⟨h1, h2⟩ := keysFind_spec a a[k] hs 0 a.size (Nat.le_refl _) (Nat.zero_le _)
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun i h hi => absurd h (by omega))
  rcases Nat.lt_trichotomy (keysFind a a[k] 0 a.size) k with h | h | h
  · have := h2 (keysFind a a[k] 0 a.size) (by omega) (Nat.le_refl _)
    have := hlt _ k (by omega) hk h
    omega
  · exact h
  · have := h1 k hk h
    omega

/-! ## Keys found back -/

theorem Keys.idx_sound {K : Keys} {j k : Nat} (h : K.idx j = some k) :
    k < K.cnt ∧ K.keyOf k = j := by
  simp only [Keys.idx] at h
  split at h
  · rename_i he
    split at h
    · rename_i hr
      simp only [Option.some.injEq] at h; subst h
      refine ⟨by omega, ?_⟩
      simp [Keys.keyOf, he]; omega
    · simp at h
  · rename_i he
    split at h
    · rename_i hr
      simp only [Option.some.injEq] at h; subst h
      simp only [beq_iff_eq] at hr
      refine ⟨hr.1, ?_⟩
      simp [Keys.keyOf, he, hr.2]
    · simp at h

theorem Keys.idx_complete {K : Keys} {l : List Nat} (hK : K.Rep l) (hl : Incr l) {k : Nat}
    (hk : k < K.cnt) : K.idx (K.keyOf k) = some k := by
  obtain ⟨hc, hshape⟩ := hK
  rcases hshape with ⟨he, hd⟩ | ⟨he, hl'⟩
  · simp only [Keys.idx, he, ↓reduceIte, Keys.keyOf]
    split
    · simp
    · rename_i h; exact absurd ⟨by omega, by omega⟩ h
  · have hsz : K.ids.size = K.cnt := by rw [hc, ← hl']; simp
    have hk' : k < K.ids.size := by omega
    have hkey : K.keyOf k = K.ids[k] := by
      simp [Keys.keyOf, he, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']
    rw [hkey]
    have hinc : Incr K.ids.toList := by rw [hl']; exact hl
    simp only [Keys.idx, he, Bool.false_eq_true, ↓reduceIte, keysFind_eq K.ids hinc hk']
    have hc2 : k < K.cnt ∧ (K.ids.getD k 0 == K.ids[k]) = true :=
      ⟨hk, by simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']⟩
    exact ite_eq_left hc2

/-! ## A chunk inside a window -/

/-- The window `Γ` has the chunk `recs` from line `off` on, after the
finished tables `P` from counters `c0`. -/
@[expose] def Emb (Γ : WCtx) (P : Prior) (c0 : Ctr) (off : Nat) (recs : Array LineRec) : Prop :=
  Γ.P = P ∧ Γ.c0 = c0 ∧ off + recs.size ≤ Γ.rs.length ∧
    ∀ q (h : q < recs.size), Γ.rs[off + q]? = some recs[q]

/-- The table, in a window. -/
@[expose] def Sel.seg : Sel α → Win → Seg α
  | .n => Win.n
  | .l => Win.l
  | .e => Win.e

/-- The table's builder, in round 0's result. -/
@[expose] def Sel.r0 : Sel α → R0 → TB α
  | .n => R0.n
  | .l => R0.l
  | .e => R0.e

/-- Good in every window the chunk is part of. -/
@[expose] def GoodIn (P : Prior) (c0 : Ctr) (recs : Array LineRec) (j : Nat) (v : TV) : Prop :=
  ∀ Γ off, Emb Γ P c0 off recs → Good Γ j v

theorem Emb.drop {Γ : WCtx} {P : Prior} {c0 : Ctr} {off : Nat} {recs : Array LineRec}
    (h : Emb Γ P c0 off recs) : (Γ.rs.drop off).take recs.size = recs.toList := by
  obtain ⟨_, _, hlen, hq⟩ := h
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
    have := hq i (by simpa using h2)
    have hi : off + i < Γ.rs.length := by simp at h1; omega
    rw [List.getElem?_eq_getElem hi] at this
    exact Option.some.inj this

theorem Emb.take {Γ : WCtx} {P : Prior} {c0 : Ctr} {off : Nat} {recs : Array LineRec}
    (h : Emb Γ P c0 off recs) {p : Nat} (hp : p ≤ recs.size) :
    Γ.rs.take (off + p) = Γ.rs.take off ++ recs.toList.take p := by
  rw [List.take_add, ← h.drop, List.take_take, Nat.min_eq_left hp]

/-- The counters at line `p` of a chunk inside a window: the chunk's
start counters, stepped over its lines before `p`. -/
theorem Emb.ctr {Γ : WCtx} {P : Prior} {c0 : Ctr} {off : Nat} {recs : Array LineRec}
    (h : Emb Γ P c0 off recs) {p : Nat} (hp : p ≤ recs.size) :
    Γ.ctr (off + p) = (Γ.ctr off).stepAll (recs.toList.take p) := by
  simp only [WCtx.ctr, ctrAt]
  rw [h.take hp, Ctr.stepAll_append]

/-- A table's counter at line `p` of a chunk whose lines before `p`
bind something there: one past the last. -/
theorem Emb.ctr_at {Γ : WCtx} {P : Prior} {c0 : Ctr} {off : Nat} {recs : Array LineRec}
    (h : Emb Γ P c0 off recs) {p : Nat} (hp : p ≤ recs.size) {t : Tb} {i : Nat}
    (hl : (idsT t (recs.toList.take p)).getLast? = some i) :
    (Γ.ctr (off + p)).at t = i + 1 := by
  rw [h.ctr hp, stepAll_at, hl]

/-! ## Round 0 -/

/-! ### Bytes -/

theorem ByteArray.size_eq_data (b : ByteArray) : b.size = b.data.size := rfl

theorem byteN_eq (b : ByteArray) (k : Nat) : byteN b k = b.data.getD k 0 := by
  unfold byteN
  rw [Array.getD_eq_getD_getElem?]
  split
  · rename_i h
    rw [ByteArray.getElem_eq_getElem_data, Array.getElem?_eq_getElem]; rfl
  · rename_i h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]; rfl

theorem byteN_push (b : ByteArray) (x : UInt8) (k : Nat) :
    byteN (b.push x) k = if k < b.size then byteN b k else if k = b.size then x else 0 := by
  rw [byteN_eq, byteN_eq, ByteArray.data_push, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_push, ByteArray.size_eq_data]
  by_cases h : k < b.data.size
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · by_cases h' : k = b.data.size
    · rw [ite_eq_left h', ite_eq_right h, ite_eq_left h']; rfl
    · rw [ite_eq_right h', ite_eq_right h, ite_eq_right h', Array.getElem?_eq_none (by omega)]; rfl

theorem byteN_set (b : ByteArray) (s k : Nat) (x : UInt8) :
    byteN (b.set! s x) k = if k = s ∧ s < b.size then x else byteN b k := by
  rw [byteN_eq, byteN_eq, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    ByteArray.size_eq_data]
  show ((b.data.set! s x)[k]?).getD 0 = _
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : k = s
  · subst h
    by_cases hs : k < b.data.size
    · rw [ite_eq_left rfl, ite_eq_left hs, ite_eq_left ⟨rfl, hs⟩]; rfl
    · rw [ite_eq_left rfl, ite_eq_right hs, ite_eq_right (fun h => hs h.2), Array.getElem?_eq_none (by omega)]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right (fun h' => h h'.1)]

theorem byteN_zero (n k : Nat) : byteN (zeroBytes n) k = 0 := by
  rw [byteN_eq, Array.getD_eq_getD_getElem?]
  show ((Array.replicate n (0 : UInt8))[k]?).getD 0 = 0
  rw [Array.getElem?_replicate]
  split <;> rfl

theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  rw [ByteArray.size_eq_data]; exact Array.size_replicate

/-- **Round 0's table builder after the first `p` lines of the chunk**
(table `t`, entries tagged by `inj`): one slot per line of the table,
its late byte and late number; keys and counter naming the lines'
indices, which increase; distinct late numbers below the count; and a
good entry in every slot that is not late. -/
structure TBI (P : Prior) (c0 : Ctr) (recs : Array LineRec) (t : Tb) (inj : α → TV) (p : Nat)
    (d : Array α) (lt : ByteArray) (ls : Array Nat) (np f : Nat) (ids : Array Nat) (b : Nat) :
    Prop where
  size : d.size = (idsT t (recs.toList.take p)).length
  ltsz : lt.size = d.size
  lssz : ls.size = d.size
  shape : (ids.isEmpty = true ∧ ∀ k (h : k < (idsT t (recs.toList.take p)).length),
      (idsT t (recs.toList.take p))[k] = f + k) ∨
    (ids.isEmpty = false ∧ ids.toList = idsT t (recs.toList.take p))
  incr : Incr (idsT t (recs.toList.take p))
  last : ∀ i, (idsT t (recs.toList.take p)).getLast? = some i → b = i + 1
  head : ∀ i, (idsT t (recs.toList.take p)).head? = some i → f = i
  lsLt : ∀ k, k < d.size → byteN lt k = 1 → ls.getD k 0 < np
  lsInj : ∀ k k', k < d.size → k' < d.size → byteN lt k = 1 → byteN lt k' = 1 →
    ls.getD k 0 = ls.getD k' 0 → k = k'
  good : ∀ k v, d[k]? = some v → byteN lt k ≠ 1 →
    GoodIn P c0 recs ((idsT t (recs.toList.take p)).getD k 0) (inj v)

theorem TBI.init (P : Prior) (c0 : Ctr) (recs : Array LineRec) (t : Tb) (inj : α → TV) :
    TBI P c0 recs t inj 0 #[] .empty #[] 0 0 #[] 0 where
  size := by simp [idsT]
  ltsz := rfl
  lssz := rfl
  shape := Or.inl ⟨rfl, fun k h => by simp [idsT] at h⟩
  incr := by simp [idsT, Incr]
  last := by simp [idsT]
  head := by simp [idsT]
  lsLt := fun k h => by simp at h
  lsInj := fun k _ h => by simp at h
  good := fun k v h => by simp at h

theorem take_succ_toList (recs : Array LineRec) {p : Nat} (hp : p < recs.size) :
    recs.toList.take (p + 1) = recs.toList.take p ++ [recs[p]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hp)]; simp

theorem idsT_succ_none {recs : Array LineRec} {p : Nat} (hp : p < recs.size) {t : Tb}
    (hn : recs[p].idAt t = none) :
    idsT t (recs.toList.take (p + 1)) = idsT t (recs.toList.take p) := by
  rw [take_succ_toList recs hp, idsT_append, idsT_singleton, hn]; simp

theorem idsT_succ_some {recs : Array LineRec} {p : Nat} (hp : p < recs.size) {t : Tb} {i : Nat}
    (hn : recs[p].idAt t = some i) :
    idsT t (recs.toList.take (p + 1)) = idsT t (recs.toList.take p) ++ [i] := by
  rw [take_succ_toList recs hp, idsT_append, idsT_singleton, hn]; simp

/-- A line that binds nothing in the table leaves its builder as it is. -/
theorem TBI.skip {P c0 recs t inj p d lt ls np f ids b} (h : TBI (α := α) P c0 recs t inj p d lt
    ls np f ids b) (hp : p < recs.size) (hn : recs[p].idAt t = none) :
    TBI P c0 recs t inj (p + 1) d lt ls np f ids b := by
  have he := idsT_succ_none hp hn
  exact { size := he ▸ h.size, ltsz := h.ltsz, lssz := h.lssz, shape := he ▸ h.shape,
          incr := he ▸ h.incr, last := he ▸ h.last, head := he ▸ h.head, lsLt := h.lsLt,
          lsInj := h.lsInj, good := by rw [he]; exact h.good }

theorem Incr.le_last {l : List Nat} (h : Incr l) {i : Nat} (hl : l.getLast? = some i) :
    ∀ x ∈ l, x ≤ i := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hne : l ≠ [] := List.ne_nil_of_mem hx
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq, List.getLast_eq_getElem] at hl
  subst hl
  rcases Nat.lt_or_ge k (l.length - 1) with h1 | h1
  · exact Nat.le_of_lt (List.pairwise_iff_getElem.mp h k (l.length - 1) hk (by omega) h1)
  · have : k = l.length - 1 := by omega
    subst this; exact Nat.le_refl _

theorem Incr.snoc {l : List Nat} (h : Incr l) {b x : Nat}
    (hb : ∀ i, l.getLast? = some i → b = i + 1) (hx : l = [] ∨ b ≤ x) : Incr (l ++ [x]) := by
  unfold Incr
  rw [List.pairwise_append]
  refine ⟨h, by simp, ?_⟩
  intro a ha y hy
  simp only [List.mem_singleton] at hy; subst hy
  have hne : l ≠ [] := List.ne_nil_of_mem ha
  have hlast := List.getLast?_eq_some_getLast hne
  have := Incr.le_last h hlast a ha
  have := hb _ hlast
  rcases hx with hx | hx
  · exact absurd hx hne
  · omega

/-- A line binding `id` (at or above the counter): the builder's keys,
order, counter and first index after it. -/
theorem TBI.keys_step {P c0 recs t inj p d lt ls np f ids b} (h : TBI (α := α) P c0 recs t inj p d
    lt ls np f ids b) (hp : p < recs.size) {id : Nat} (hn : recs[p].idAt t = some id)
    (hfit : d.size = 0 ∨ b ≤ id) :
    (((keysPush d.size f b ids id).isEmpty = true ∧
        ∀ k (h : k < (idsT t (recs.toList.take (p + 1))).length),
          (idsT t (recs.toList.take (p + 1)))[k] = (if d.size == 0 then id else f) + k) ∨
      (keysPush d.size f b ids id).isEmpty = false ∧
        (keysPush d.size f b ids id).toList = idsT t (recs.toList.take (p + 1))) ∧
    Incr (idsT t (recs.toList.take (p + 1))) ∧
    (∀ i, (idsT t (recs.toList.take (p + 1))).getLast? = some i → id + 1 = i + 1) ∧
    (∀ i, (idsT t (recs.toList.take (p + 1))).head? = some i →
      (if d.size == 0 then id else f) = i) ∧
    d.size = (idsT t (recs.toList.take p)).length := by
  have he := idsT_succ_some hp hn
  have hsz := h.size
  refine ⟨?_, ?_, ?_, ?_, hsz⟩
  · rw [he]; exact keysPush_rep (id := id) hsz h.shape h.last
  · rw [he]
    exact Incr.snoc h.incr h.last (by
      rcases hfit with h0 | h0
      · left; exact List.eq_nil_of_length_eq_zero (by omega)
      · right; exact h0)
  · rw [he]; intro i hi; simp at hi; omega
  · rw [he]; intro i hi
    by_cases h0 : d.size = 0
    · have : idsT t (recs.toList.take p) = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at hi; simp at hi; simp [h0, hi]
    · have hne : idsT t (recs.toList.take p) ≠ [] := by
        intro h'; rw [h', List.length_nil] at hsz; exact h0 hsz
      rw [List.head?_append, List.head?_eq_some_head hne] at hi
      simp only [Option.some_or, Option.some.injEq] at hi
      simp only [beq_iff_eq, h0, ↓reduceIte]
      exact h.head _ (by rw [List.head?_eq_some_head hne, hi])

/-- A line binding `id` (at or above the counter), with a good entry. -/
theorem TBI.add {P c0 recs t inj p d lt ls np f ids b} (h : TBI (α := α) P c0 recs t inj p d lt
    ls np f ids b) (hp : p < recs.size) {id : Nat} (hn : recs[p].idAt t = some id)
    (hfit : d.size = 0 ∨ b ≤ id) {v : α} (hg : GoodIn P c0 recs id (inj v)) :
    TBI P c0 recs t inj (p + 1) (d.push v) (lt.push 0) (ls.push 0) np
      (if d.size == 0 then id else f) (keysPush d.size f b ids id) (id + 1) := by
  have he := idsT_succ_some hp hn
  have hsz := h.size
  obtain ⟨k1, k2, k3, k4, k5⟩ := h.keys_step hp hn hfit
  refine { size := ?_, ltsz := ?_, lssz := ?_, shape := k1, incr := k2, last := k3,
           head := k4, lsLt := ?_, lsInj := ?_, good := ?_ }
  · simp [he, k5]
  · simp [ByteArray.size_push, h.ltsz]
  · simp [h.lssz]
  · intro k hk hb1
    rw [byteN_push] at hb1
    simp only [Array.size_push] at hk
    split at hb1
    · rename_i hkl
      have := h.lsLt k (by rw [h.ltsz] at hkl; exact hkl) hb1
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push] at ⊢
      rw [Array.getD_eq_getD_getElem?] at this
      simp only [h.lssz, show k ≠ d.size by rw [h.ltsz] at hkl; omega, ↓reduceIte]; exact this
    · split at hb1 <;> simp at hb1
  · intro k k' hk hk' h1 h2 heq
    simp only [Array.size_push] at hk hk'
    rw [byteN_push] at h1 h2
    split at h1
    · split at h2
      · rename_i hk1 hk2
        rw [h.ltsz] at hk1 hk2
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.lssz,
          show k ≠ d.size by omega, show k' ≠ d.size by omega, ↓reduceIte] at heq
        exact h.lsInj k k' hk1 hk2 h1 h2 (by simpa [Array.getD_eq_getD_getElem?] using heq)
      · split at h2 <;> simp at h2
    · split at h1 <;> simp at h1
  · intro k w hk hb1
    rw [he]
    rw [Array.getElem?_push] at hk
    rw [byteN_push] at hb1
    split at hk
    · rename_i hkd
      subst hkd
      simp only [Option.some.injEq] at hk; subst hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hsz, Nat.sub_self]
      exact hg
    · rename_i hkd
      have hkl : k < d.size := by
        rcases Nat.lt_or_ge k d.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none (by omega)] at hk; simp at hk
      have := h.good k w hk (by rw [h.ltsz, ite_eq_left hkl] at hb1; exact hb1)
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rwa [List.getD_eq_getElem?_getD] at this

/-- A line binding `id` (at or above the counter), deferred. -/
theorem TBI.addLate [Inhabited α] {P c0 recs t inj p d lt ls np f ids b}
    (h : TBI (α := α) P c0 recs t inj p d lt ls np f ids b) (hp : p < recs.size) {id : Nat}
    (hn : recs[p].idAt t = some id) (hfit : d.size = 0 ∨ b ≤ id) :
    TBI P c0 recs t inj (p + 1) (d.push default) (lt.push 1) (ls.push np) (np + 1)
      (if d.size == 0 then id else f) (keysPush d.size f b ids id) (id + 1) := by
  have he := idsT_succ_some hp hn
  have hsz := h.size
  obtain ⟨k1, k2, k3, k4, k5⟩ := h.keys_step hp hn hfit
  refine { size := ?_, ltsz := ?_, lssz := ?_, shape := k1, incr := k2, last := k3,
           head := k4, lsLt := ?_, lsInj := ?_, good := ?_ }
  · simp [he, k5]
  · simp [ByteArray.size_push, h.ltsz]
  · simp [h.lssz]
  · intro k hk hb1
    rw [byteN_push] at hb1
    simp only [Array.size_push] at hk
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.lssz]
    split
    · rename_i hkd; subst hkd; simp
    · rename_i hkd
      split at hb1
      · rename_i hkl
        have := h.lsLt k (by rw [h.ltsz] at hkl; exact hkl) hb1
        rw [Array.getD_eq_getD_getElem?] at this; omega
      · split at hb1
        · rename_i h3; rw [h.ltsz] at h3; exact absurd h3 hkd
        · simp at hb1
  · intro k k' hk hk' h1 h2 heq
    simp only [Array.size_push] at hk hk'
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.lssz] at heq
    have bound : ∀ j, j < d.size → byteN lt j = 1 → (ls[j]?).getD 0 < np := fun j hj hbj => by
      have := h.lsLt j hj hbj; rwa [Array.getD_eq_getD_getElem?] at this
    rw [byteN_push, h.ltsz] at h1 h2
    by_cases hkd : k = d.size
    · by_cases hkd' : k' = d.size
      · omega
      · simp only [hkd, hkd', ↓reduceIte, Option.getD_some] at heq
        have hk'l : k' < d.size := by omega
        simp only [hk'l, ↓reduceIte] at h2
        have := bound k' hk'l h2; omega
    · by_cases hkd' : k' = d.size
      · simp only [hkd, hkd', ↓reduceIte, Option.getD_some] at heq
        have hkl : k < d.size := by omega
        simp only [hkl, ↓reduceIte] at h1
        have := bound k hkl h1; omega
      · have hkl : k < d.size := by omega
        have hk'l : k' < d.size := by omega
        simp only [hkd, hkd', ↓reduceIte] at heq
        simp only [hkl, hk'l, ↓reduceIte] at h1 h2
        exact h.lsInj k k' hkl hk'l h1 h2 (by simpa [Array.getD_eq_getD_getElem?] using heq)
  · intro k w hk hb1
    rw [Array.getElem?_push] at hk
    rw [byteN_push, h.ltsz] at hb1
    split at hk
    · rename_i hkd; subst hkd; simp at hb1
    · rename_i hkd
      have hkl : k < d.size := by
        rcases Nat.lt_or_ge k d.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none (by omega)] at hk; simp at hk
      have := h.good k w hk (by rw [ite_eq_left hkl] at hb1; exact hb1)
      rw [he, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rwa [List.getD_eq_getElem?_getD] at this

/-! ### Round 0's lookups answer good entries -/

theorem r0Look_ok {pg : Pages α} {c0t c : Nat} {t : WT} {d : Array α} {lt : ByteArray}
    {f : Nat} {ids : Array Nat} {b j : Nat} {w : α}
    (h : r0Look pg c0t c t d lt f ids b j = .ok w) :
    (j < c0t ∧ pg.get j = some w) ∨
    (d.size ≠ 0 ∧ j < b ∧ ∃ k, d[k]? = some w ∧ byteN lt k ≠ 1 ∧
      Keys.keyOf ⟨f, d.size, ids⟩ k = j) := by
  unfold r0Look at h
  by_cases hj : j < c0t
  · rw [ite_eq_left hj] at h
    left; refine ⟨hj, ?_⟩
    split at h
    · rename_i x hx; cases h; exact hx
    · cases h
  · rw [ite_eq_right hj] at h
    by_cases hd : (d.size == 0) = true
    · rw [ite_eq_left hd] at h; cases h
    · rw [ite_eq_right hd] at h
      by_cases hjb : j < b
      · rw [ite_eq_left hjb] at h
        by_cases hf : f ≤ j
        · rw [ite_eq_left hf] at h
          simp only [] at h
          generalize hkk : (if ids.isEmpty = true then j - f else keysFind ids j 0 ids.size) = k
            at h
          by_cases hk : k < d.size
          · rw [dite_eq_left hk] at h
            by_cases hid : (ids.isEmpty || ids.getD k 0 == j) = true
            · rw [ite_eq_left hid] at h
              by_cases hlt : (byteN lt k == 1) = true
              · rw [ite_eq_left hlt] at h; cases h
              · rw [ite_eq_right hlt] at h
                cases h
                right
                refine ⟨by simpa using hd, hjb, k, Array.getElem?_eq_getElem hk,
                  by simpa using hlt, ?_⟩
                simp only [Keys.keyOf]
                by_cases he : ids.isEmpty = true
                · rw [ite_eq_left he] at hkk ⊢; omega
                · rw [ite_eq_right he]
                  simp only [Bool.or_eq_true, beq_iff_eq] at hid
                  rcases hid with hid | hid
                  · exact absurd hid he
                  · exact hid
            · rw [ite_eq_right hid] at h; cases h
          · rw [dite_eq_right hk] at h; cases h
        · rw [ite_eq_right hf] at h; cases h
      · rw [ite_eq_right hjb] at h; cases h

/-- The finished tables' answers are good in every window after them. -/
@[expose] def PriorGood (P : Prior) (c0 : Ctr) (t : Tb) (pg : Pages α) (inj : α → TV) : Prop :=
  ∀ j w, j < c0.at t → pg.get j = some w → ∀ Γ : WCtx, Γ.P = P → Γ.c0 = c0 → Good Γ j (inj w)

theorem priorGood (P : Prior) (c0 : Ctr) (S : Sel α) : PriorGood P c0 S.tb (S.pages P) S.inj :=
  fun _ _ h1 h2 _ hP hc => Good.ofPrior S (by rw [hc]; exact h1) (by rw [hP]; exact h2)

/-- Round 0's lookups in a table answer good entries, below the window's
start or below the line's counter. -/
theorem r0_refs {P : Prior} {c0 : Ctr} {recs : Array LineRec} {t : Tb} {inj : α → TV}
    {p : Nat} {d : Array α} {lt : ByteArray} {ls : Array Nat} {np f : Nat} {ids : Array Nat}
    {b : Nat} (hT : TBI P c0 recs t inj p d lt ls np f ids b) {pg : Pages α}
    (hpri : PriorGood P c0 t pg inj) (hp : p ≤ recs.size) {c : Nat} {wt : WT}
    {Γ : WCtx} {off : Nat} (hE : Emb Γ P c0 off recs) :
    ∀ j w, r0Look pg (c0.at t) c wt d lt f ids b j = .ok w →
      Good Γ j (inj w) ∧ (j < Γ.c0.at t ∨ j < (Γ.ctr (off + p)).at t) := by
  intro j w h
  rcases r0Look_ok h with ⟨hj, hg⟩ | ⟨hd, hjb, k, hk, hlt, hkey⟩
  · exact ⟨hpri j w hj hg Γ hE.1 hE.2.1, Or.inl (by rw [hE.2.1]; exact hj)⟩
  · have hkl : k < d.size := by
      rcases Nat.lt_or_ge k d.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at hk; cases hk
    have hkl' : k < (idsT t (recs.toList.take p)).length := by rw [← hT.size]; exact hkl
    have hkey' : (idsT t (recs.toList.take p)).getD k 0 = j := by
      rw [← hkey, keyOf_of_shape hT.shape k hkl', List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hkl']; rfl
    refine ⟨hkey' ▸ hT.good k w hk hlt Γ off hE, Or.inr ?_⟩
    have hne : idsT t (recs.toList.take p) ≠ [] := by
      intro he; rw [he] at hkl'; simp at hkl'
    have hlast := List.getLast?_eq_some_getLast hne
    rw [hE.ctr_at hp hlast, ← hT.last _ hlast]
    exact hjb

/-- A table line's entry from round 0's lookups is good. -/
theorem r0_good {P : Prior} {c0 : Ctr} {c : Nat} {recs : Array LineRec} {p : Nat}
    (hp : p < recs.size) {t : Tb} {id : Nat} (hid : recs[p].idAt t = some id)
    {dn : Array Name} {ltn : ByteArray} {lsn : Array Nat} {npn fn : Nat} {idn : Array Nat}
    {bn : Nat} (hn : TBI P c0 recs .n TV.n p dn ltn lsn npn fn idn bn)
    {dl : Array Level} {ltl : ByteArray} {lsl : Array Nat} {npl fl : Nat} {idl : Array Nat}
    {bl : Nat} (hl : TBI P c0 recs .l TV.l p dl ltl lsl npl fl idl bl)
    {de : Array Expr} {lte : ByteArray} {lse : Array Nat} {npe fe : Nat} {ide : Array Nat}
    {be : Nat} (he : TBI P c0 recs .e TV.e p de lte lse npe fe ide be) {v : TV}
    (hb : lineVal (r0Look P.n c0.n c .name dn ltn fn idn bn)
      (r0Look P.l c0.l c .level dl ltl fl idl bl) (r0Look P.e c0.e c .expr de lte fe ide be)
      recs[p] = some (.ok v)) : GoodIn P c0 recs id v := by
  intro Γ off hE
  have rn := r0_refs hn (priorGood P c0 .n) (Nat.le_of_lt hp) (c := c) (wt := .name) hE
  have rl := r0_refs hl (priorGood P c0 .l) (Nat.le_of_lt hp) (c := c) (wt := .level) hE
  have re := r0_refs he (priorGood P c0 .e) (Nat.le_of_lt hp) (c := c) (wt := .expr) hE
  exact Good.line (p := off + p) _ _ _ (hE.2.2.2 p hp) hid
    (lkAt_forall (fun i w h => (rn i w h).1) (fun i w h => (rl i w h).1) (fun i w h => (re i w h).1))
    (lkAt_forall (fun i w h => (rn i w h).2) (fun i w h => (rl i w h).2) (fun i w h => (re i w h).2))
    hb

/-- The line's value, from its builder's. -/
theorem lineVal_name {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {r : LineRec} {id : Nat} {x : NameRec} (hr : r = .name id x)
    {v : Name} (h : nameOfF nm lv ex x = .ok v) : lineVal nm lv ex r = some (.ok (.n v)) := by
  subst hr; simp [lineVal, h]; rfl
theorem lineVal_level {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {r : LineRec} {id : Nat} {x : LevelRec} (hr : r = .level id x)
    {v : Level} (h : levelOfF nm lv ex x = .ok v) : lineVal nm lv ex r = some (.ok (.l v)) := by
  subst hr; simp [lineVal, h]; rfl
theorem lineVal_expr {ε : Type} {nm : Nat → Except ε Name} {lv : Nat → Except ε Level}
    {ex : Nat → Except ε Expr} {r : LineRec} {id : Nat} {x : ExprRec} (hr : r = .expr id x)
    {v : Expr} (h : exprOfF nm lv ex x = .ok v) : lineVal nm lv ex r = some (.ok (.e v)) := by
  subst hr; simp [lineVal, h]; rfl

/-! ### Round 0, line by line -/

/-- Slot `k` of a builder is late, with late number `s`. -/
@[expose] def TB.lateAt (t : TB α) (k s : Nat) : Prop :=
  k < t.d.size ∧ byteN t.late k = 1 ∧ t.ls.getD k 0 = s

/-- The pending lines after the first `p` lines: lines of the chunk
before `p`, with the counts of each table's lines before them, and the
slot of each a late slot naming the line's late number. -/
@[expose] def PendI (recs : Array LineRec) (p : Nat) (pend : Array Pend) (tn : TB Name)
    (tl : TB Level) (te : TB Expr) : Prop :=
  ∀ e ∈ pend.toList, e.pos < p ∧
    e.kn = (idsT .n (recs.toList.take e.pos)).length ∧
    e.kl = (idsT .l (recs.toList.take e.pos)).length ∧
    e.ke = (idsT .e (recs.toList.take e.pos)).length ∧
    (match recs[e.pos]? with
     | some (.name _ _) => tn.lateAt e.kn e.s
     | some (.level _ _) => tl.lateAt e.kl e.s
     | some (.expr _ _) => te.lateAt e.ke e.s
     | _ => False)

/-- A table builder's invariant, on the record. -/
@[expose] def TB.I (P : Prior) (c0 : Ctr) (recs : Array LineRec) (t : Tb) (inj : α → TV) (p : Nat)
    (x : TB α) : Prop :=
  TBI P c0 recs t inj p x.d x.late x.ls x.np x.first x.ids x.b

/-- **Round 0's invariant after the first `p` lines.** -/
structure R0I (P : Prior) (c0 : Ctr) (recs : Array LineRec) (p : Nat) (tn : TB Name)
    (tl : TB Level) (te : TB Expr) (pend : Array Pend) : Prop where
  n : tn.I P c0 recs .n TV.n p
  l : tl.I P c0 recs .l TV.l p
  e : te.I P c0 recs .e TV.e p
  pend : PendI recs p pend tn tl te

/-- A pushed builder keeps its late slots. -/
theorem TB.lateAt.push {t : TB α} {k s : Nat} (h : t.lateAt k s) (hlt : t.late.size = t.d.size)
    (hls : t.ls.size = t.d.size) (v : α) (b : UInt8) (n np f : Nat) (ids : Array Nat) (bb : Nat) :
    (⟨t.d.push v, t.late.push b, t.ls.push n, np, f, ids, bb⟩ : TB α).lateAt k s := by
  obtain ⟨k1, k2, k3⟩ := h
  refine ⟨by simp; omega, ?_, ?_⟩
  · show byteN (t.late.push b) k = 1; rw [byteN_push, ite_eq_left (by omega)]; exact k2
  · show (t.ls.push n).getD k 0 = s
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
    rw [ite_eq_right (by omega)]; simpa [Array.getD_eq_getD_getElem?] using k3

/-- A deferred line's new slot is late. -/
theorem TB.lateAt_new [Inhabited α] {t : TB α} (hlt : t.late.size = t.d.size)
    (hls : t.ls.size = t.d.size) (f : Nat) (ids : Array Nat) (bb : Nat) :
    (⟨t.d.push default, t.late.push 1, t.ls.push t.np, t.np + 1, f, ids, bb⟩ : TB α).lateAt
      t.d.size t.np := by
  refine ⟨by simp, ?_, ?_⟩
  · show byteN (t.late.push 1) t.d.size = 1
    rw [byteN_push, ite_eq_right (by omega), ite_eq_left hlt.symm]
  · show (t.ls.push t.np).getD t.d.size 0 = t.np
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hls]; simp

theorem PendI.succ {recs : Array LineRec} {p : Nat} {pend : Array Pend} {tn : TB Name}
    {tl : TB Level} {te : TB Expr} (h : PendI recs p pend tn tl te) :
    PendI recs (p + 1) pend tn tl te := fun e he => by
  obtain ⟨h1, h2⟩ := h e he; exact ⟨by omega, h2⟩

/-- The pending lines keep their slots in builders that keep the late
slots. -/
theorem PendI.mono {recs : Array LineRec} {p : Nat} {pend : Array Pend} {tn tn' : TB Name}
    {tl tl' : TB Level} {te te' : TB Expr} (h : PendI recs p pend tn tl te)
    (hn : ∀ k s, tn.lateAt k s → tn'.lateAt k s) (hl : ∀ k s, tl.lateAt k s → tl'.lateAt k s)
    (he : ∀ k s, te.lateAt k s → te'.lateAt k s) : PendI recs p pend tn' tl' te' := fun e he' => by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h e he'
  refine ⟨h1, h2, h3, h4, ?_⟩
  cases hq : recs[e.pos]? with
  | none => rw [hq] at h5; exact h5.elim
  | some r =>
    rw [hq] at h5
    cases r <;> simp only [] at h5 ⊢
    · exact hn _ _ h5
    · exact hl _ _ h5
    · exact he _ _ h5

/-- Line `p`, deferred, joins the pending lines. -/
theorem PendI.defer {recs : Array LineRec} {p : Nat} {pend : Array Pend} {tn : TB Name}
    {tl : TB Level} {te : TB Expr} (h : PendI recs (p + 1) pend tn tl te) (hp : p < recs.size)
    {x : Pend} (hx : x.pos = p) (hn : x.kn = (idsT .n (recs.toList.take p)).length)
    (hl : x.kl = (idsT .l (recs.toList.take p)).length)
    (he : x.ke = (idsT .e (recs.toList.take p)).length)
    (hs : match recs[p]? with
      | some (.name _ _) => tn.lateAt x.kn x.s
      | some (.level _ _) => tl.lateAt x.kl x.s
      | some (.expr _ _) => te.lateAt x.ke x.s
      | _ => False) :
    PendI recs (p + 1) (pend.push x) tn tl te := by
  intro e he'
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he'
  rcases he' with he' | he'
  · exact h e he'
  · subst he'; subst hx; exact ⟨by omega, hn, hl, he, hs⟩

/-- A line that passed round 0's order test binds at or above the
table's counter, or is the table's first. -/
theorem fit_of {n b id : Nat} (hc : ¬ (n != 0 && id < b) = true) : n = 0 ∨ b ≤ id := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_and, Nat.not_lt] at hc
  by_cases h0 : n = 0
  · exact Or.inl h0
  · exact Or.inr (hc h0)

/-- **Round 0 keeps its invariant**, line by line, to the end of the
chunk (when it meets no anomaly). -/
theorem round0Go_spec (P : Prior) (c0 : Ctr) (c : Nat) (recs : Array LineRec) :
    ∀ (n p : Nat) (dn : Array Name) (ltn : ByteArray) (lsn : Array Nat) (npn fn : Nat)
      (idn : Array Nat) (bn : Nat) (dl : Array Level) (ltl : ByteArray) (lsl : Array Nat)
      (npl fl : Nat) (idl : Array Nat) (bl : Nat) (de : Array Expr) (lte : ByteArray)
      (lse : Array Nat) (npe fe : Nat) (ide : Array Nat) (be : Nat) (pend : Array Pend)
      (prog : Nat),
    recs.size - p = n → p ≤ recs.size →
    R0I P c0 recs p ⟨dn, ltn, lsn, npn, fn, idn, bn⟩ ⟨dl, ltl, lsl, npl, fl, idl, bl⟩
      ⟨de, lte, lse, npe, fe, ide, be⟩ pend →
    (round0Go P c0 c recs p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe
      ide be pend prog).bad = false →
    R0I P c0 recs recs.size
      (round0Go P c0 c recs p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe
        ide be pend prog).n
      (round0Go P c0 c recs p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe
        ide be pend prog).l
      (round0Go P c0 c recs p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe
        ide be pend prog).e
      (round0Go P c0 c recs p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe
        ide be pend prog).pend := by
  intro n
  induction n with
  | zero =>
    intro p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe ide be pend
      prog hn hle hI hb
    have hp : p = recs.size := by omega
    subst hp
    rw [round0Go, dite_eq_right (by omega)]
    exact hI
  | succ n ih =>
    intro p dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl de lte lse npe fe ide be pend
      prog hn hle hI hb
    have hp : p < recs.size := by omega
    rw [round0Go, dite_eq_left hp] at hb ⊢
    split
    · rename_i id x heq
      simp only [heq] at hb
      have hid : recs[p].idAt .n = some id := by rw [heq]; rfl
      have hnl : recs[p].idAt .l = none := by rw [heq]; rfl
      have hne : recs[p].idAt .e = none := by rw [heq]; rfl
      by_cases hc : (dn.size != 0 && id < bn) = true
      · rw [ite_eq_left hc] at hb; simp at hb
      · rw [ite_eq_right hc] at hb ⊢
        have hfit := fit_of hc
        simp only [] at hb ⊢
        split
        · rename_i v hv
          simp only [hv] at hb
          exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            ⟨TBI.add hI.n hp hid hfit (r0_good hp hid hI.n hI.l hI.e (lineVal_name heq hv)), hI.l.skip hp hnl,
             hI.e.skip hp hne, hI.pend.succ.mono
               (fun _ _ h => h.push hI.n.ltsz hI.n.lssz _ _ _ _ _ _ _) (fun _ _ h => h)
               (fun _ _ h => h)⟩ hb
        · rename_i wc wk wt hv
          simp only [hv] at hb
          exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            ⟨TBI.addLate hI.n hp hid hfit, hI.l.skip hp hnl, hI.e.skip hp hne,
             (hI.pend.succ.mono (fun _ _ h => h.push hI.n.ltsz hI.n.lssz _ _ _ _ _ _ _)
               (fun _ _ h => h) (fun _ _ h => h)).defer hp rfl hI.n.size hI.l.size hI.e.size
               (by simp only [Array.getElem?_eq_getElem hp, heq]
                   exact TB.lateAt_new (t := ⟨dn, ltn, lsn, npn, fn, idn, bn⟩) hI.n.ltsz
                     hI.n.lssz _ _ _)⟩ hb
        · rename_i hv
          simp only [hv] at hb; simp at hb
    · rename_i id x heq
      simp only [heq] at hb
      have hid : recs[p].idAt .l = some id := by rw [heq]; rfl
      have hnn : recs[p].idAt .n = none := by rw [heq]; rfl
      have hne : recs[p].idAt .e = none := by rw [heq]; rfl
      by_cases hc : (dl.size != 0 && id < bl) = true
      · rw [ite_eq_left hc] at hb; simp at hb
      · rw [ite_eq_right hc] at hb ⊢
        have hfit := fit_of hc
        simp only [] at hb ⊢
        split
        · rename_i v hv
          simp only [hv] at hb
          exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            ⟨hI.n.skip hp hnn, TBI.add hI.l hp hid hfit (r0_good hp hid hI.n hI.l hI.e (lineVal_level heq hv)),
             hI.e.skip hp hne, hI.pend.succ.mono (fun _ _ h => h)
               (fun _ _ h => h.push hI.l.ltsz hI.l.lssz _ _ _ _ _ _ _) (fun _ _ h => h)⟩ hb
        · rename_i wc wk wt hv
          simp only [hv] at hb
          exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            ⟨hI.n.skip hp hnn, TBI.addLate hI.l hp hid hfit, hI.e.skip hp hne,
             (hI.pend.succ.mono (fun _ _ h => h)
               (fun _ _ h => h.push hI.l.ltsz hI.l.lssz _ _ _ _ _ _ _)
               (fun _ _ h => h)).defer hp rfl hI.n.size hI.l.size hI.e.size
               (by simp only [Array.getElem?_eq_getElem hp, heq]
                   exact TB.lateAt_new (t := ⟨dl, ltl, lsl, npl, fl, idl, bl⟩) hI.l.ltsz
                     hI.l.lssz _ _ _)⟩ hb
        · rename_i hv
          simp only [hv] at hb; simp at hb
    · rename_i id x heq
      simp only [heq] at hb
      have hid : recs[p].idAt .e = some id := by rw [heq]; rfl
      have hnn : recs[p].idAt .n = none := by rw [heq]; rfl
      have hnl : recs[p].idAt .l = none := by rw [heq]; rfl
      by_cases hc : (de.size != 0 && id < be) = true
      · rw [ite_eq_left hc] at hb; simp at hb
      · rw [ite_eq_right hc] at hb ⊢
        have hfit := fit_of hc
        simp only [] at hb ⊢
        split
        · rename_i v hv
          simp only [hv] at hb
          exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            ⟨hI.n.skip hp hnn, hI.l.skip hp hnl,
             TBI.add hI.e hp hid hfit (r0_good hp hid hI.n hI.l hI.e (lineVal_expr heq hv)),
             hI.pend.succ.mono (fun _ _ h => h) (fun _ _ h => h)
               (fun _ _ h => h.push hI.e.ltsz hI.e.lssz _ _ _ _ _ _ _)⟩ hb
        · rename_i wc wk wt hv
          simp only [hv] at hb
          exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            ⟨hI.n.skip hp hnn, hI.l.skip hp hnl, TBI.addLate hI.e hp hid hfit,
             (hI.pend.succ.mono (fun _ _ h => h) (fun _ _ h => h)
               (fun _ _ h => h.push hI.e.ltsz hI.e.lssz _ _ _ _ _ _ _)).defer hp rfl hI.n.size
               hI.l.size hI.e.size
               (by simp only [Array.getElem?_eq_getElem hp, heq]
                   exact TB.lateAt_new (t := ⟨de, lte, lse, npe, fe, ide, be⟩) hI.e.ltsz
                     hI.e.lssz _ _ _)⟩ hb
        · rename_i hv
          simp only [hv] at hb; simp at hb
    · rename_i heq1 heq2 heq3
      have key : ∀ t, recs[p].idAt t = none := by
        intro t
        cases hr : recs[p] with
        | name i x => exact absurd hr (heq1 i x)
        | level i x => exact absurd hr (heq2 i x)
        | expr i x => exact absurd hr (heq3 i x)
        | decl r => cases t <;> rfl
        | header => cases t <;> rfl
        | blank => cases t <;> rfl
      have hb' := hb
      cases hr : recs[p] with
      | name i x => exact absurd hr (heq1 i x)
      | level i x => exact absurd hr (heq2 i x)
      | expr i x => exact absurd hr (heq3 i x)
      | decl r =>
        simp only [hr] at hb'
        exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
          ⟨hI.n.skip hp (key _), hI.l.skip hp (key _), hI.e.skip hp (key _), hI.pend.succ⟩ hb'
      | header =>
        simp only [hr] at hb'
        exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
          ⟨hI.n.skip hp (key _), hI.l.skip hp (key _), hI.e.skip hp (key _), hI.pend.succ⟩ hb'
      | blank =>
        simp only [hr] at hb'
        exact ih (p + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
          ⟨hI.n.skip hp (key _), hI.l.skip hp (key _), hI.e.skip hp (key _), hI.pend.succ⟩ hb'

/-- **Round 0's result**, without an anomaly: its invariant over the
whole chunk. -/
theorem round0_spec {P : Prior} {c0 : Ctr} {c : Nat} {recs : Array LineRec}
    (hb : (round0 P c0 c recs).bad = false) :
    R0I P c0 recs recs.size (round0 P c0 c recs).n (round0 P c0 c recs).l
      (round0 P c0 c recs).e (round0 P c0 c recs).pend :=
  round0Go_spec P c0 c recs _ 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
    (Nat.zero_le _)
    ⟨TBI.init P c0 recs .n TV.n, TBI.init P c0 recs .l TV.l, TBI.init P c0 recs .e TV.e,
     fun e he => by simp at he⟩ hb

/-- **What a chunk's owner keeps between rounds**: its pending lines,
as round 0 left them (when it met no anomaly). -/
@[expose] def PendOK (P : Prior) (c0 : Ctr) (c : Nat) (recs : Array LineRec) (pend : Array Pend) :
    Prop :=
  (round0 P c0 c recs).bad = false →
    PendI recs recs.size pend (round0 P c0 c recs).n (round0 P c0 c recs).l (round0 P c0 c recs).e

theorem pendOK_round0 (P : Prior) (c0 : Ctr) (c : Nat) (recs : Array LineRec) :
    PendOK P c0 c recs (round0 P c0 c recs).pend := fun hb => (round0_spec hb).pend

theorem PendOK.empty (P : Prior) (c0 : Ctr) (c : Nat) (recs : Array LineRec) :
    PendOK P c0 c recs #[] := fun _ e he => by simp at he

/-! ## The later rounds -/

/-- A table's slots, as a window holds a chunk's: round 0's builder `t`,
with the late entries `lv` (done where `ld` says). -/
@[expose] def TB.get (t : TB α) (lv : Array α) (ld : ByteArray) (k : Nat) : Option α :=
  slotGet t.d t.late t.ls lv ld k

/-- **The late entries of a chunk's table are good** in window `Γ`:
`np` of them, each done one good for its slot's index. -/
structure LateOK (Γ : WCtx) (inj : α → TV) (t : TB α) (lv : Array α) (ld : ByteArray) : Prop where
  lvsz : lv.size = t.np
  ldsz : ld.size = t.np
  good : ∀ k v, k < t.d.size → byteN t.late k = 1 → byteN ld (t.ls.getD k 0) = 1 →
    lv[t.ls.getD k 0]? = some v → Good Γ (t.keys.keyOf k) (inj v)

theorem LateOK.init (Γ : WCtx) (inj : α → TV) [Inhabited α] (t : TB α) :
    LateOK Γ inj t (Array.replicate t.np default) (zeroBytes t.np) :=
  ⟨by simp, zeroBytes_size _, fun k v _ _ h => by rw [byteN_zero] at h; cases h⟩

/-- Round 0's slots of a chunk, with good late entries, are good. -/
theorem TBI.get_good {P : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb} {inj : α → TV}
    {t : TB α} (hT : t.I P c0 recs tb inj recs.size) {Γ : WCtx} {off : Nat}
    (hE : Emb Γ P c0 off recs) {lv : Array α} {ld : ByteArray} (hL : LateOK Γ inj t lv ld)
    {k : Nat} {v : α} (h : t.get lv ld k = some v) : Good Γ (t.keys.keyOf k) (inj v) := by
  simp only [TB.get, slotGet] at h
  split at h
  · rename_i hk
    by_cases hl' : (byteN t.late k == 1) = true
    · have hl : byteN t.late k = 1 := beq_iff_eq.mp hl'
      rw [ite_eq_left hl'] at h
      simp only [lateVal] at h
      split at h
      · rename_i hd
        split at h
        · rename_i hs
          cases h
          exact hL.good k _ hk hl (by simpa using hd) (Array.getElem?_eq_getElem hs)
        · cases h
      · cases h
    · have hl : byteN t.late k ≠ 1 := fun h' => hl' (beq_iff_eq.mpr h')
      rw [ite_eq_right hl'] at h
      cases h
      have hkl : k < (idsT tb (recs.toList.take recs.size)).length := by rw [← hT.size]; exact hk
      have := hT.good k t.d[k] (Array.getElem?_eq_getElem hk) hl Γ off hE
      have hkey : t.keys.keyOf k = (idsT tb (recs.toList.take recs.size)).getD k 0 := by
        rw [keyOf_of_shape hT.shape k hkl, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hkl]; rfl
      rw [hkey]; exact this
  · cases h

/-- The indices a chunk's lines before `pos` bind: a prefix of the
chunk's. -/
theorem idsT_take_prefix (t : Tb) (l : List LineRec) (pos : Nat) :
    idsT t l = idsT t (l.take pos) ++ idsT t (l.drop pos) := by
  rw [← idsT_append, List.take_append_drop]

/-- **A pending line's counter**, from its count of the table's lines
before it and the chunk's start. -/
theorem ctrOf_eq {P : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb} {inj : α → TV}
    {t : TB α} (hT : t.I P c0 recs tb inj recs.size) {Γ : WCtx} {off : Nat}
    (hE : Emb Γ P c0 off recs) {lo : Nat} (hlo : lo = (Γ.ctr off).at tb) {pos : Nat}
    (hpos : pos ≤ recs.size) :
    ctrOf lo t.keys (idsT tb (recs.toList.take pos)).length = (Γ.ctr (off + pos)).at tb := by
  rw [hE.ctr hpos, stepAll_at]
  simp only [ctrOf]
  cases hl : (idsT tb (recs.toList.take pos)).getLast? with
  | none =>
    have : idsT tb (recs.toList.take pos) = [] := List.getLast?_eq_none_iff.mp hl
    rw [this]; simp [hlo]
  | some i =>
    have hne : idsT tb (recs.toList.take pos) ≠ [] := by
      intro h'; rw [h'] at hl; simp at hl
    have hlen : (idsT tb (recs.toList.take pos)).length ≠ 0 := by
      intro h'; exact hne (List.eq_nil_of_length_eq_zero h')
    simp only [beq_iff_eq, hlen, ↓reduceIte]
    have hfull : idsT tb (recs.toList.take recs.size) = idsT tb recs.toList := by
      rw [List.take_of_length_le (by simp)]
    have hpre := idsT_take_prefix tb recs.toList pos
    have hk : (idsT tb (recs.toList.take pos)).length - 1 <
        (idsT tb (recs.toList.take recs.size)).length := by
      rw [hfull, hpre, List.length_append]; omega
    rw [keyOf_of_shape hT.shape _ hk]
    have : (idsT tb (recs.toList.take recs.size))[(idsT tb (recs.toList.take pos)).length - 1] =
        i := by
      simp only [hfull]
      rw [List.getLast?_eq_some_getLast hne, Option.some.injEq, List.getLast_eq_getElem] at hl
      rw [← hl]
      simp only [hpre]
      rw [List.getElem_append_left (by omega)]
    rw [this]

/-- **A later round's lookups answer good entries**, below the
line's counter: the finished tables' below the window, the chunk's own,
or an earlier chunk's of the window. -/
theorem rLk_good {Γ : WCtx} {inj : α → TV} {P : Pages α} {S : Seg α} {c0t c lo : Nat}
    {K : Keys} {d0 : Array α} {late : ByteArray} {ls : Array Nat} {lv : Array α}
    {ld : ByteArray} {t : WT} {b : Nat}
    (hpri : ∀ j w, j < c0t → P.get j = some w → Good Γ j (inj w))
    (hown : ∀ k w, slotGet d0 late ls lv ld k = some w → Good Γ (K.keyOf k) (inj w))
    (hS : ∀ e k w, e < c → S.getAt e k = some w →
      ∃ K', S.keys[e]? = some K' ∧ Good Γ (K'.keyOf k) (inj w))
    {j : Nat} {w : α} (h : rLk P S c0t c lo K d0 late ls lv ld t b j = .ok w) :
    Good Γ j (inj w) ∧ j < b := by
  unfold rLk at h
  by_cases hjb : j < b
  · rw [ite_eq_left hjb] at h
    refine ⟨?_, hjb⟩
    split at h
    · rename_i hf
      split at h
      · rename_i x hx
        cases h
        have := hown _ _ hx
        have hk : K.keyOf (j - K.first) = j := by
          simp only [Keys.keyOf, hf.1, ↓reduceIte]; omega
        rwa [hk] at this
      · cases h
    · split at h
      · rename_i hc
        split at h
        · rename_i x hx; cases h; exact hpri j _ hc hx
        · cases h
      · unfold rawLk at h
        split at h
        · split at h
          · rename_i k hk
            split at h
            · rename_i x hx
              cases h
              have := hown _ _ hx
              rwa [(Keys.idx_sound hk).2] at this
            · cases h
          · cases h
        · simp only [] at h
          generalize Seg.findGo S.starts j 0 c = e at h
          split at h
          · rename_i hr
            cases hK' : S.keys[e]? with
            | none => simp [hK'] at h
            | some K' =>
              simp only [hK'] at h
              cases hk : K'.idx j with
              | none => simp [hk] at h
              | some k =>
                simp only [hk] at h
                cases hx : S.getAt e k with
                | none => simp [hx] at h
                | some x =>
                  simp only [hx, Except.ok.injEq] at h; subst h
                  obtain ⟨K'', hK'', hg⟩ := hS _ k x hr.1 hx
                  rw [hK''] at hK'; cases hK'
                  rwa [(Keys.idx_sound hk).2] at hg
          · cases h
  · rw [ite_eq_right hjb] at h; cases h

/-- Writing a good entry for a late slot keeps the late entries good. -/
theorem LateOK.set {Γ : WCtx} {inj : α → TV} {P : Prior} {c0 : Ctr} {recs : Array LineRec}
    {tb : Tb} {t : TB α} (hT : t.I P c0 recs tb inj recs.size) {lv : Array α} {ld : ByteArray}
    (hL : LateOK Γ inj t lv ld) {k0 : Nat} (hk0 : k0 < t.d.size) (hl0 : byteN t.late k0 = 1)
    {v : α} (hg : Good Γ (t.keys.keyOf k0) (inj v)) :
    LateOK Γ inj t (lv.setIfInBounds (t.ls.getD k0 0) v) (ld.set! (t.ls.getD k0 0) 1) := by
  refine ⟨by simp [hL.lvsz], ?_, ?_⟩
  · show (ld.data.set! _ 1).size = _
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hL.ldsz
  · intro k w hk hl hd hw
    rw [byteN_set] at hd
    by_cases hs : t.ls.getD k 0 = t.ls.getD k0 0
    · have hkk : k = k0 := hT.lsInj k k0 hk hk0 hl hl0 hs
      subst hkk
      rw [Array.getElem?_setIfInBounds] at hw
      simp only [↓reduceIte] at hw
      split at hw
      · cases hw; exact hg
      · cases hw
    · rw [ite_eq_right (fun h => hs h.1)] at hd
      rw [Array.getElem?_setIfInBounds, ite_eq_right (Ne.symm hs)] at hw
      exact hL.good k w hk hl hd hw

/-- A table line's slot key is the index it binds. -/
theorem TBI.key_line {P : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb} {inj : α → TV}
    {t : TB α} (hT : t.I P c0 recs tb inj recs.size) {pos : Nat} (hpos : pos < recs.size)
    {i : Nat} (hi : recs[pos].idAt tb = some i) :
    (idsT tb (recs.toList.take pos)).length < t.d.size ∧
    t.keys.keyOf (idsT tb (recs.toList.take pos)).length = i := by
  have hfull : idsT tb (recs.toList.take recs.size) = idsT tb recs.toList := by
    rw [List.take_of_length_le (by simp)]
  have hsplit : idsT tb recs.toList =
      idsT tb (recs.toList.take pos) ++ i :: idsT tb (recs.toList.drop (pos + 1)) := by
    rw [idsT_take_prefix tb recs.toList pos, List.drop_eq_getElem_cons (by simpa using hpos),
      idsT_cons]
    simp [hi]
  have hlt : (idsT tb (recs.toList.take pos)).length < (idsT tb recs.toList).length := by
    rw [hsplit]; simp
  have hsz : t.d.size = (idsT tb recs.toList).length := by rw [← hfull]; exact hT.size
  refine ⟨by omega, ?_⟩
  rw [keyOf_of_shape hT.shape _ (by rw [hfull]; exact hlt)]
  simp only [hfull, hsplit]
  rw [List.getElem_append_right (by omega)]
  simp

/-- A chunk of a window, as a later round sees it: inside the window,
round 0's tables and keys as the window holds them, its range starting
at the window's counters there, and every earlier chunk's entries good. -/
structure ChunkCtx (Γ : WCtx) (P : Prior) (W : Win) (c : Nat) (recs : Array LineRec) (off : Nat) :
    Prop where
  emb : Emb Γ P W.c0 off recs
  bad0 : (round0 P W.c0 c recs).bad = false
  geo : W.geo c = ⟨c, (Γ.ctr off).n, (Γ.ctr off).l, (Γ.ctr off).e,
    (round0 P W.c0 c recs).n.keys, (round0 P W.c0 c recs).l.keys, (round0 P W.c0 c recs).e.keys,
    (round0 P W.c0 c recs).n.d, (round0 P W.c0 c recs).l.d, (round0 P W.c0 c recs).e.d,
    (round0 P W.c0 c recs).n.late, (round0 P W.c0 c recs).l.late, (round0 P W.c0 c recs).e.late,
    (round0 P W.c0 c recs).n.ls, (round0 P W.c0 c recs).l.ls, (round0 P W.c0 c recs).e.ls⟩
  other : ∀ {α : Type} (S : Sel α) e k w, e < c → (S.seg W).getAt e k = some w →
    ∃ K', (S.seg W).keys[e]? = some K' ∧ Good Γ (K'.keyOf k) (S.inj w)

/-- **A later round's invariant**: the chunk's late entries good, its
remaining pending lines some of the round's. -/
structure RRI (Γ : WCtx) (P : Prior) (W : Win) (c : Nat) (recs : Array LineRec)
    (pend : Array Pend) (vn : Array Name) (dn : ByteArray) (vl : Array Level) (dl : ByteArray)
    (ve : Array Expr) (de : ByteArray) (pend' : Array Pend) : Prop where
  n : LateOK Γ TV.n (round0 P W.c0 c recs).n vn dn
  l : LateOK Γ TV.l (round0 P W.c0 c recs).l vl dl
  e : LateOK Γ TV.e (round0 P W.c0 c recs).e ve de
  sub : ∀ x ∈ pend'.toList, ∃ e0 ∈ pend.toList, x.pos = e0.pos ∧ x.kn = e0.kn ∧
    x.kl = e0.kl ∧ x.ke = e0.ke ∧ x.s = e0.s

/-- A pending line kept for the next round keeps the invariant. -/
theorem RRI.push {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {pend : Array Pend} {vn : Array Name} {dn : ByteArray} {vl : Array Level} {dl : ByteArray}
    {ve : Array Expr} {de : ByteArray} {pend' : Array Pend}
    (hI : RRI Γ P W c recs pend vn dn vl dl ve de pend') {q : Nat} (hq : q < pend.size) {x : Pend}
    (hx : x.pos = pend[q].pos ∧ x.kn = pend[q].kn ∧ x.kl = pend[q].kl ∧ x.ke = pend[q].ke ∧
      x.s = pend[q].s) :
    RRI Γ P W c recs pend vn dn vl dl ve de (pend'.push x) :=
  { n := hI.n, l := hI.l, e := hI.e, sub := fun y hy => by
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact hI.sub y hy
      · subst hy; exact ⟨_, List.getElem_mem (by simpa using hq), hx⟩ }

/-- **A later round's entry is good**: the value of a pending line's
builder over the round's lookups (late entries `vn`…`de` good). -/
theorem rr_good {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {off : Nat} (hC : ChunkCtx Γ P W c recs off) {vn : Array Name} {dn : ByteArray}
    {vl : Array Level} {dl : ByteArray} {ve : Array Expr} {de : ByteArray}
    (hn : LateOK Γ TV.n (round0 P W.c0 c recs).n vn dn)
    (hl : LateOK Γ TV.l (round0 P W.c0 c recs).l vl dl)
    (he : LateOK Γ TV.e (round0 P W.c0 c recs).e ve de) {pos : Nat} (hpos : pos < recs.size)
    {t : Tb} {i : Nat} (hid : recs[pos].idAt t = some i) {kn kl ke : Nat}
    (hkn : kn = (idsT .n (recs.toList.take pos)).length)
    (hkl : kl = (idsT .l (recs.toList.take pos)).length)
    (hke : ke = (idsT .e (recs.toList.take pos)).length) {v : TV}
    (hv : lineVal
      (rLk P.n W.n W.c0.n c (Γ.ctr off).n (round0 P W.c0 c recs).n.keys
        (round0 P W.c0 c recs).n.d (round0 P W.c0 c recs).n.late (round0 P W.c0 c recs).n.ls
        vn dn .name (ctrOf (Γ.ctr off).n (round0 P W.c0 c recs).n.keys kn))
      (rLk P.l W.l W.c0.l c (Γ.ctr off).l (round0 P W.c0 c recs).l.keys
        (round0 P W.c0 c recs).l.d (round0 P W.c0 c recs).l.late (round0 P W.c0 c recs).l.ls
        vl dl .level (ctrOf (Γ.ctr off).l (round0 P W.c0 c recs).l.keys kl))
      (rLk P.e W.e W.c0.e c (Γ.ctr off).e (round0 P W.c0 c recs).e.keys
        (round0 P W.c0 c recs).e.d (round0 P W.c0 c recs).e.late (round0 P W.c0 c recs).e.ls
        ve de .expr (ctrOf (Γ.ctr off).e (round0 P W.c0 c recs).e.keys ke))
      recs[pos] = some (.ok v)) : Good Γ i v := by
  have hR := round0_spec hC.bad0
  have cn := ctrOf_eq hR.n hC.emb (lo := (Γ.ctr off).n) rfl (Nat.le_of_lt hpos)
  have cl := ctrOf_eq hR.l hC.emb (lo := (Γ.ctr off).l) rfl (Nat.le_of_lt hpos)
  have ce := ctrOf_eq hR.e hC.emb (lo := (Γ.ctr off).e) rfl (Nat.le_of_lt hpos)
  rw [← hkn] at cn; rw [← hkl] at cl; rw [← hke] at ce
  have pri : ∀ {α : Type} (S : Sel α) j w, j < W.c0.at S.tb → (S.pages P).get j = some w →
      Good Γ j (S.inj w) := fun S j w h1 h2 =>
    Good.ofPrior S (by rw [hC.emb.2.1]; exact h1) (by rw [hC.emb.1]; exact h2)
  refine Good.line (p := off + pos) _ _ _ (hC.emb.2.2.2 _ hpos) hid ?_ ?_ hv
  · exact lkAt_forall
      (fun _ _ h => (rLk_good (pri .n) (fun k w h => TBI.get_good hR.n hC.emb hn h) (hC.other .n) h).1)
      (fun _ _ h => (rLk_good (pri .l) (fun k w h => TBI.get_good hR.l hC.emb hl h) (hC.other .l) h).1)
      (fun _ _ h => (rLk_good (pri .e) (fun k w h => TBI.get_good hR.e hC.emb he h) (hC.other .e) h).1)
  · exact lkAt_forall
      (fun _ _ h => Or.inr (cn ▸ (rLk_good (pri .n) (fun k w h => TBI.get_good hR.n hC.emb hn h)
        (hC.other .n) h).2))
      (fun _ _ h => Or.inr (cl ▸ (rLk_good (pri .l) (fun k w h => TBI.get_good hR.l hC.emb hl h)
        (hC.other .l) h).2))
      (fun _ _ h => Or.inr (ce ▸ (rLk_good (pri .e) (fun k w h => TBI.get_good hR.e hC.emb he h)
        (hC.other .e) h).2))

/-- **A later round keeps its invariant**, pending line by pending line
(when it meets no anomaly). -/
theorem roundRGo_spec {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {off : Nat} (hC : ChunkCtx Γ P W c recs off) {pend : Array Pend}
    (hp : PendI recs recs.size pend (round0 P W.c0 c recs).n (round0 P W.c0 c recs).l
      (round0 P W.c0 c recs).e) :
    ∀ (n q : Nat) (vn : Array Name) (dn : ByteArray) (vl : Array Level) (dl : ByteArray)
      (ve : Array Expr) (de : ByteArray) (fn : Array Name) (fl : Array Level) (fe : Array Expr)
      (pend' : Array Pend) (prog : Nat),
    pend.size - q = n →
    RRI Γ P W c recs pend vn dn vl dl ve de pend' →
    (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).bad = false →
    RRI Γ P W c recs pend
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).vn
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).dn
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).vl
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).dl
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).ve
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).de
      (roundRGo P W (W.geo c) recs pend q vn dn vl dl ve de fn fl fe pend' prog).pend := by
  have hR := round0_spec hC.bad0
  rw [hC.geo]
  intro n
  induction n with
  | zero =>
    intro q vn dn vl dl ve de fn fl fe pend' prog hn hI hb
    rw [roundRGo, dite_eq_right (by omega)]
    exact hI
  | succ n ih =>
    intro q vn dn vl dl ve de fn fl fe pend' prog hn hI hb
    have hq : q < pend.size := by omega
    rw [roundRGo, dite_eq_left hq] at hb ⊢
    simp only [] at hb ⊢
    split
    · rename_i hsb
      rw [ite_eq_left hsb] at hb
      exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
        (hI.push hq ⟨rfl, rfl, rfl, rfl, rfl⟩) hb
    · rename_i hsb
      rw [ite_eq_right hsb] at hb
      have hmem : pend[q] ∈ pend.toList := List.getElem_mem (by simpa using hq)
      obtain ⟨hpos, hkn, hkl, hke, hslot⟩ := hp _ hmem
      have hrec : ∀ r, recs[pend[q].pos]? = some r → recs[pend[q].pos] = r := fun r h => by
        rw [Array.getElem?_eq_getElem hpos] at h; exact Option.some.inj h
      split at hb
      · rename_i i x heq
        rw [heq] at hslot
        obtain ⟨hk0, hl0, hs0⟩ := hslot
        have hid : recs[pend[q].pos].idAt .n = some i := by rw [hrec _ heq]; rfl
        split
        · rename_i v hv
          simp only [hv] at hb
          have hkey := (TBI.key_line hR.n hpos hid).2
          rw [← hkn] at hkey
          have hg := rr_good hC hI.n hI.l hI.e hpos hid hkn hkl hke (lineVal_name (hrec _ heq) hv)
          have hL := LateOK.set hR.n hI.n hk0 hl0 (hkey ▸ hg)
          rw [hs0] at hL
          exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
            { n := hL, l := hI.l, e := hI.e, sub := hI.sub } hb
        · rename_i wc wk wt hv
          simp only [hv] at hb
          exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
            (hI.push hq ⟨rfl, rfl, rfl, rfl, rfl⟩) hb
        · rename_i hv; simp only [hv] at hb; simp at hb
      · rename_i i x heq
        rw [heq] at hslot
        obtain ⟨hk0, hl0, hs0⟩ := hslot
        have hid : recs[pend[q].pos].idAt .l = some i := by rw [hrec _ heq]; rfl
        split
        · rename_i v hv
          simp only [hv] at hb
          have hkey := (TBI.key_line hR.l hpos hid).2
          rw [← hkl] at hkey
          have hg := rr_good hC hI.n hI.l hI.e hpos hid hkn hkl hke (lineVal_level (hrec _ heq) hv)
          have hL := LateOK.set hR.l hI.l hk0 hl0 (hkey ▸ hg)
          rw [hs0] at hL
          exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
            { n := hI.n, l := hL, e := hI.e, sub := hI.sub } hb
        · rename_i wc wk wt hv
          simp only [hv] at hb
          exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
            (hI.push hq ⟨rfl, rfl, rfl, rfl, rfl⟩) hb
        · rename_i hv; simp only [hv] at hb; simp at hb
      · rename_i i x heq
        rw [heq] at hslot
        obtain ⟨hk0, hl0, hs0⟩ := hslot
        have hid : recs[pend[q].pos].idAt .e = some i := by rw [hrec _ heq]; rfl
        split
        · rename_i v hv
          simp only [hv] at hb
          have hkey := (TBI.key_line hR.e hpos hid).2
          rw [← hke] at hkey
          have hg := rr_good hC hI.n hI.l hI.e hpos hid hkn hkl hke (lineVal_expr (hrec _ heq) hv)
          have hL := LateOK.set hR.e hI.e hk0 hl0 (hkey ▸ hg)
          rw [hs0] at hL
          exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
            { n := hI.n, l := hI.l, e := hL, sub := hI.sub } hb
        · rename_i wc wk wt hv
          simp only [hv] at hb
          exact ih (q + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega)
            (hI.push hq ⟨rfl, rfl, rfl, rfl, rfl⟩) hb
        · rename_i hv; simp only [hv] at hb; simp at hb
      · simp at hb

/-- **A later round of a chunk** (without an anomaly): its late entries
good, its pending lines some of the round's. -/
theorem roundR_spec {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {off : Nat} (hC : ChunkCtx Γ P W c recs off) {pend : Array Pend}
    (hp : PendI recs recs.size pend (round0 P W.c0 c recs).n (round0 P W.c0 c recs).l
      (round0 P W.c0 c recs).e)
    (hL : RRI Γ P W c recs pend (W.n.tabs.getD c .blank).lv (W.n.tabs.getD c .blank).ldone
      (W.l.tabs.getD c .blank).lv (W.l.tabs.getD c .blank).ldone
      (W.e.tabs.getD c .blank).lv (W.e.tabs.getD c .blank).ldone #[])
    (hb : (roundR P W c recs pend).bad = false) :
    RRI Γ P W c recs pend (roundR P W c recs pend).vn (roundR P W c recs pend).dn
      (roundR P W c recs pend).vl (roundR P W c recs pend).dl (roundR P W c recs pend).ve
      (roundR P W c recs pend).de (roundR P W c recs pend).pend := by
  unfold roundR at hb ⊢
  simp only [] at hb ⊢
  split
  · exact hL
  · rename_i hne
    rw [ite_eq_right hne] at hb
    exact roundRGo_spec hC hp _ 0 _ _ _ _ _ _ _ _ _ _ _ rfl hL hb

/-- The pending lines after a round satisfy the owner's invariant. -/
theorem PendI.of_sub {recs : Array LineRec} {pend pend' : Array Pend} {tn : TB Name}
    {tl : TB Level} {te : TB Expr} (h : PendI recs recs.size pend tn tl te)
    (hs : ∀ x ∈ pend'.toList, ∃ e0 ∈ pend.toList, x.pos = e0.pos ∧ x.kn = e0.kn ∧
      x.kl = e0.kl ∧ x.ke = e0.ke ∧ x.s = e0.s) : PendI recs recs.size pend' tn tl te := by
  intro x hx
  obtain ⟨e0, he0, h1, h2, h3, h4, h5⟩ := hs x hx
  rw [h1, h2, h3, h4, h5]
  exact h e0 he0

/-- The lines a later round leaves pending are some of the round's, with
their waits renewed. -/
theorem roundRGo_sub (P : Prior) (W : Win) (G : Geo) (d : Array LineRec) (pend : Array Pend) :
    ∀ (n q : Nat) vn dn vl dl ve de fn fl fe (pend' : Array Pend) prog,
    pend.size - q = n →
    (∀ x ∈ pend'.toList, ∃ e0 ∈ pend.toList, x.pos = e0.pos ∧ x.kn = e0.kn ∧ x.kl = e0.kl ∧
      x.ke = e0.ke ∧ x.s = e0.s) →
    ∀ x ∈ (roundRGo P W G d pend q vn dn vl dl ve de fn fl fe pend' prog).pend.toList,
      ∃ e0 ∈ pend.toList, x.pos = e0.pos ∧ x.kn = e0.kn ∧ x.kl = e0.kl ∧ x.ke = e0.ke ∧
        x.s = e0.s := by
  intro n
  induction n with
  | zero =>
    intro q vn dn vl dl ve de fn fl fe pend' prog hn hp
    rw [roundRGo, dite_eq_right (by omega)]
    exact hp
  | succ n ih =>
    intro q vn dn vl dl ve de fn fl fe pend' prog hn hp
    have hq : q < pend.size := by omega
    have hmem : pend[q] ∈ pend.toList := List.getElem_mem (by simpa using hq)
    have hpush : ∀ (y : Pend), y.pos = pend[q].pos → y.kn = pend[q].kn → y.kl = pend[q].kl →
        y.ke = pend[q].ke → y.s = pend[q].s →
        ∀ x ∈ (pend'.push y).toList, ∃ e0 ∈ pend.toList, x.pos = e0.pos ∧ x.kn = e0.kn ∧
          x.kl = e0.kl ∧ x.ke = e0.ke ∧ x.s = e0.s := by
      intro y h1 h2 h3 h4 h5 x hx
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hp x hx
      · subst hx; exact ⟨_, hmem, h1, h2, h3, h4, h5⟩
    rw [roundRGo, dite_eq_left hq]
    simp only []
    split
    · exact ih _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (hpush _ rfl rfl rfl rfl rfl)
    · split
      all_goals first
        | (split
           · exact ih _ _ _ _ _ _ _ _ _ _ _ _ (by omega) hp
           · exact ih _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (hpush _ rfl rfl rfl rfl rfl)
           · exact hp)
        | exact hp

theorem PendOK.afterRound {P : Prior} {c0 : Ctr} {c : Nat} {recs : Array LineRec} {pend : Array Pend}
    (h : PendOK P c0 c recs pend) (P' : Prior) (W : Win) :
    PendOK P c0 c recs (roundR P' W c recs pend).pend := by
  intro hb
  apply PendI.of_sub (h hb)
  unfold roundR
  simp only []
  split
  · intro x hx; simp at hx
  · exact roundRGo_sub P' W _ recs pend _ 0 _ _ _ _ _ _ _ _ _ _ _ rfl (fun x hx => by simp at hx)

/-! ## Segments: where an index lies -/

theorem Seg.getAt_eq {s : Seg α} {e k : Nat} :
    s.getAt e k = (s.tabs[e]?.bind fun t => t.get k) := by
  unfold Seg.getAt
  split <;> simp_all

theorem Seg.atC_some {s : Seg α} {e j : Nat} {v : α} (h : s.atC e j = some v) :
    ∃ K k, s.keys[e]? = some K ∧ K.idx j = some k ∧ s.getAt e k = some v := by
  unfold Seg.atC at h
  split at h
  · rename_i he
    split at h
    · rename_i k hk
      exact ⟨_, k, Array.getElem?_eq_getElem he, hk, h⟩
    · cases h
  · cases h

theorem Seg.getSlow_go_some {s : Seg α} {j : Nat} :
    ∀ c, Seg.getSlow.go s j c = some v → ∃ e, s.atC e j = some v := by
  intro c
  induction c using Seg.getSlow.go.induct s j with
  | case1 c h1 h2 => intro h; rw [Seg.getSlow.go, ite_eq_left h1, ite_eq_left h2] at h; exact ⟨c, h⟩
  | case2 c h1 h2 ih => intro h; rw [Seg.getSlow.go, ite_eq_left h1, ite_eq_right h2] at h; exact ih h
  | case3 c h1 => intro h; rw [Seg.getSlow.go, ite_eq_right h1] at h; cases h

/-- An entry a segment answers is some chunk's. -/
theorem Seg.get_some {s : Seg α} {j : Nat} {v : α} (h : s.get j = some v) :
    ∃ e, s.atC e j = some v := by
  unfold Seg.get at h
  simp only [] at h
  split at h
  · exact ⟨_, h⟩
  · exact Seg.getSlow_go_some 0 (by simpa [Seg.getSlow] using h)

/-- Chunk `c`'s range. -/
@[expose] def Seg.holds (s : Seg α) (c j : Nat) : Prop :=
  c < s.tabs.size ∧ s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0

/-- Monotone starts. -/
@[expose] def Seg.mono (s : Seg α) : Prop :=
  ∀ c, c < s.tabs.size → s.starts.getD c 0 ≤ s.starts.getD (c + 1) 0

theorem Seg.holds_unique {s : Seg α} (hm : s.mono) {c c' j : Nat} (h : s.holds c j)
    (h' : s.holds c' j) : c = c' := by
  have mono2 : ∀ a b, a ≤ b → b ≤ s.tabs.size → s.starts.getD a 0 ≤ s.starts.getD b 0 := by
    intro a b hab hb
    induction hab with
    | refl => exact Nat.le_refl _
    | step h ih => exact Nat.le_trans (ih (by omega)) (hm _ (by omega))
  obtain ⟨h1, h2, h3⟩ := h; obtain ⟨h1', h2', h3'⟩ := h'
  rcases Nat.lt_trichotomy c c' with hc | hc | hc
  · have := mono2 (c + 1) c' hc (by omega); omega
  · exact hc
  · have := mono2 (c' + 1) c hc (by omega); omega

theorem Seg.getSlow_go_holds {s : Seg α} (hm : s.mono) {c j : Nat} (h : s.holds c j) :
    ∀ c', c' ≤ c → Seg.getSlow.go s j c' = s.atC c j := by
  intro c'
  induction c' using Seg.getSlow.go.induct s j with
  | case1 c' h1 h2 => intro _; rw [Seg.getSlow.go, ite_eq_left h1, ite_eq_left h2]
                      rw [Seg.holds_unique hm ⟨h1, h2⟩ h]
  | case2 c' h1 h2 ih =>
    intro hc
    rw [Seg.getSlow.go, ite_eq_left h1, ite_eq_right h2]
    apply ih
    rcases Nat.lt_or_ge c' c with h3 | h3
    · omega
    · have : c' = c := by omega
      subst this; exact absurd h.2 h2
  | case3 c' h1 => intro hc; exact absurd (Nat.lt_of_le_of_lt hc h.1) h1

/-- **On monotone starts, a segment's entry is the entry of the chunk
whose range holds the index.** -/
theorem Seg.get_holds {s : Seg α} (hm : s.mono) {c j : Nat} (h : s.holds c j) :
    s.get j = s.atC c j := by
  unfold Seg.get
  simp only []
  split
  · rename_i h'
    rw [Seg.holds_unique hm h' h]
  · simp only [Seg.getSlow]
    exact Seg.getSlow_go_holds hm h 0 (Nat.zero_le _)

/-! ## Where the window's chunks start -/

/-- The start of chunk `c`, from the keys of the chunks before it. -/
@[expose] def startsSpec (ks : Array Keys) (a : Nat) : Nat → Nat
  | 0 => a
  | c + 1 =>
    let K := ks.getD c default
    if K.cnt == 0 then startsSpec ks a c else K.keyOf (K.cnt - 1) + 1

theorem startsSpec_succ (ks : Array Keys) (a : Nat) {i : Nat} (h : i < ks.size) :
    startsSpec ks a (i + 1) =
      if ks[i].cnt == 0 then startsSpec ks a i else ks[i].keyOf (ks[i].cnt - 1) + 1 := by
  simp only [startsSpec, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]

theorem startsGo_spec (ks : Array Keys) (a : Nat) :
    ∀ i a' (acc : Array Nat), acc.size = i + 1 → a' = startsSpec ks a i →
    (∀ j, j ≤ i → acc.getD j 0 = startsSpec ks a j) → i ≤ ks.size →
    (∀ j, j ≤ ks.size → (startsGo ks i a' acc).getD j 0 = startsSpec ks a j) := by
  intro i a' acc
  induction i, a', acc using startsGo.induct ks with
  | case1 i a' acc h K a'' ih =>
    intro hsz ha' hacc hi
    rw [startsGo, dite_eq_left h]
    have hnext : a'' = startsSpec ks a (i + 1) := by
      simp only [a'', K, dite_eq_ite, ha', startsSpec_succ ks a h]
    apply ih (by simp [hsz]) hnext
    · intro j hj
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      split
      · rename_i hj'
        have : j = i + 1 := by omega
        subst this
        simp only [Option.getD_some]; exact hnext
      · have := hacc j (by omega)
        simpa [Array.getD_eq_getD_getElem?] using this
    · omega
  | case2 i a' acc h =>
    intro hsz ha' hacc hi j hj
    rw [startsGo, dite_eq_right h]
    exact hacc j (by omega)

/-- The starts of a segment built from keys. -/
theorem Seg.mk'_starts (a : Nat) (ts : Array (CTab α)) (ks : Array Keys) :
    ∀ j, j ≤ ks.size → (Seg.mk' a ts ks).starts.getD j 0 = startsSpec ks a j :=
  startsGo_spec ks a 0 a #[a] rfl rfl (fun j hj => by
    have : j = 0 := by omega
    subst this; rfl) (Nat.zero_le _)

/-! ## The pages after a window -/

/-- What index `j` holds after a window over the indices `[lo, hi)`:
the finished tables before below it, the window's entries in it. -/
@[expose] def pageView (P : Pages α) (s : Seg α) (lo hi j : Nat) : Option α :=
  if j < lo then P.get j else if j < hi then s.get j else none

/-- What rank `r` holds after a window over the ranks `[lo, hi)` (`s`
the window by rank). -/
@[expose] def rankView (P : Pages α) (s : Seg α) (lo hi r : Nat) : Option α :=
  if r < lo then P.atRank r else if r < hi then s.get r else none

/-- **A page after a window** holds, slot by slot up to rank `hi`, the
finished tables' entries below the window and the window's in it (on
monotone starts: the cursor only picks which chunk to ask first). -/
theorem pageGo_spec [Inhabited α] (P : Pages α) (s : Seg α) (hm : s.mono) (lo hi p : Nat)
    (hlh : lo ≤ hi) :
    ∀ i c (v : Array α), v.size = i → i ≤ 4096 → (i = 0 ∨ p * 4096 + i ≤ hi) →
    (∀ i', i' < i → v[i']? = some ((rankView P s lo hi (p * 4096 + i')).getD default)) →
    ∀ i', i' < 4096 → (pageGo P s lo hi p i c v)[i']? =
      if p * 4096 + i' < hi then some ((rankView P s lo hi (p * 4096 + i')).getD default)
      else none := by
  intro i c v
  induction i, c, v using pageGo.induct P s lo hi p with
  | case1 i c v h4 j hj ih =>
    intro hv hle _ hacc
    have hj2 : p * 4096 + i < lo := hj
    rw [pageGo, ite_eq_left h4]
    simp only [ite_eq_left hj2]
    apply ih (by simp [hv]) (by omega) (Or.inr (by omega))
    intro i' hi'
    rw [Array.getElem?_push]
    split
    · rename_i he; subst he; rw [hv]; simp [rankView, hj2]; rfl
    · exact hacc i' (by omega)
  | case2 i c v h4 j hj hj' c' x ih =>
    intro hv hle _ hacc
    have hj2 : ¬ p * 4096 + i < lo := hj
    have hj3 : p * 4096 + i < hi := hj'
    have hx : x = s.get (p * 4096 + i) := by
      show (if _ then _ else _) = _
      split
      · rename_i hh'; rw [Seg.get_holds hm hh']
      · rfl
    rw [pageGo, ite_eq_left h4]
    simp only [ite_eq_right hj2, ite_eq_left hj3]
    apply ih (by simp [hv]) (by omega) (Or.inr (by omega))
    intro i' hi'
    rw [Array.getElem?_push]
    split
    · rename_i he; subst he; rw [hv]
      show some (x.getD default) = _
      simp [rankView, hj2, hj3, hx]
    · exact hacc i' (by omega)
  | case3 i c v h4 j hj hj' =>
    intro hv hle h0 hacc i' hi'
    have hj2 : ¬ p * 4096 + i < lo := hj
    have hj3 : ¬ p * 4096 + i < hi := hj'
    rw [pageGo, ite_eq_left h4]
    simp only [ite_eq_right hj2, ite_eq_right hj3]
    rcases Nat.lt_or_ge i' i with h1 | h1
    · rw [hacc i' h1, ite_eq_left (by omega)]
    · rw [Array.getElem?_eq_none (by omega), ite_eq_right (by omega)]
  | case4 i c v h4 =>
    intro hv hle h0 hacc i' hi'
    rw [pageGo, ite_eq_right h4, hacc i' (by omega), ite_eq_left (by omega)]

theorem pageOf_spec [Inhabited α] (P : Pages α) (s : Seg α) (hm : s.mono) (lo hi p : Nat)
    (hlh : lo ≤ hi) {i : Nat} (hi' : i < 4096) :
    (pageOf P s lo hi p)[i]? = if p * 4096 + i < hi then
      some ((rankView P s lo hi (p * 4096 + i)).getD default) else none :=
  pageGo_spec P s hm lo hi p hlh 0 _ _ (by simp) (Nat.zero_le _) (Or.inl rfl)
    (fun _ h => absurd h (by omega)) i hi'

/-! ## A chunk's declarations -/

/-- The window's view of a table, cut at a counter, is the serial
parse's lookup in tables `T` that hold the view below it. -/
theorem vN_eq {P : Prior} {W : Win} {T : Tabs} {b : Nat}
    (h : ∀ j, j < b → T.n j = if j < W.c0.n then P.n.get j else W.n.get j) :
    vN P W b = (cutLk T ⟨b, 0, 0⟩).name := by
  funext j
  simp only [vN, cutLk]
  by_cases hj : j < b
  · rw [ite_eq_left hj, ite_eq_left hj, h j hj]; rfl
  · rw [ite_eq_right hj, ite_eq_right hj]

theorem vL_eq {P : Prior} {W : Win} {T : Tabs} {b : Nat}
    (h : ∀ j, j < b → T.l j = if j < W.c0.l then P.l.get j else W.l.get j) :
    vL P W b = (cutLk T ⟨0, b, 0⟩).level := by
  funext j
  simp only [vL, cutLk]
  by_cases hj : j < b
  · rw [ite_eq_left hj, ite_eq_left hj, h j hj]; rfl
  · rw [ite_eq_right hj, ite_eq_right hj]

theorem vE_eq {P : Prior} {W : Win} {T : Tabs} {b : Nat}
    (h : ∀ j, j < b → T.e j = if j < W.c0.e then P.e.get j else W.e.get j) :
    vE P W b = (cutLk T ⟨0, 0, b⟩).expr := by
  funext j
  simp only [vE, cutLk]
  by_cases hj : j < b
  · rw [ite_eq_left hj, ite_eq_left hj, h j hj]; rfl
  · rw [ite_eq_right hj, ite_eq_right hj]

/-- Tables `T` hold the window's view below the counters of every line
of the chunk. -/
@[expose] def ViewBelow (Γ : WCtx) (P : Prior) (W : Win) (off n : Nat) (T : Tabs) : Prop :=
  ∀ q, q ≤ n → ∀ {α : Type} (S : Sel α) j, j < (Γ.ctr (off + q)).at S.tb →
    S.tab T j = if j < W.c0.at S.tb then (S.pages P).get j else (S.seg W).get j

/-- Chunk `c`'s start counters are the window's counters at its first
line. -/
theorem ChunkCtx.start {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {off : Nat} (hC : ChunkCtx Γ P W c recs off) : W.start c = Γ.ctr off := by
  have h1 : W.n.starts.getD c 0 = (Γ.ctr off).n := congrArg Geo.ln hC.geo
  have h2 : W.l.starts.getD c 0 = (Γ.ctr off).l := congrArg Geo.ll hC.geo
  have h3 : W.e.starts.getD c 0 = (Γ.ctr off).e := congrArg Geo.le hC.geo
  simp only [Win.start, h1, h2, h3]

theorem chunkDeclsGo_spec {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {off : Nat} (hC : ChunkCtx Γ P W c recs off) {T : Tabs}
    (hV : ViewBelow Γ P W off recs.size T) :
    ∀ i ct acc ds, chunkDeclsGo P W recs i ct acc = some ds → ct = Γ.ctr (off + i) →
    ds = declsAlong T ct (recs.toList.drop i) acc ∧
    ∀ q (hq : q < recs.size) d, i ≤ q → recs[q] = .decl d →
      ∃ x, declOf (cutLk T (Γ.ctr (off + q))) d = .ok (.inl x) := by
  have hsucc : ∀ i (h : i < recs.size), Γ.ctr (off + (i + 1)) = (Γ.ctr (off + i)).step recs[i] := by
    intro i h
    rw [hC.emb.ctr (by omega), hC.emb.ctr (by omega)]
    exact ctrAt_succ (Γ.ctr off) recs.toList i (by simpa using h)
  intro i ct acc
  induction i, ct, acc using chunkDeclsGo.induct P W recs with
  | case1 i ct acc h r hr x hx ih =>
    intro ds hds hct
    rw [chunkDeclsGo, dite_eq_left h] at hds
    simp only [hr, hx] at hds
    have v1 := hV i (Nat.le_of_lt h) .n
    have v2 := hV i (Nat.le_of_lt h) .l
    have v3 := hV i (Nat.le_of_lt h) .e
    rw [← hct] at v1 v2 v3
    have w1 : vN P W ct.n = (cutLk T ct).name := vN_eq v1
    have w2 : vL P W ct.l = (cutLk T ct).level := vL_eq v2
    have w3 : vE P W ct.e = (cutLk T ct).expr := vE_eq v3
    have hdecl : declOf (cutLk T ct) r = .ok (.inl x) := by
      rw [← hx, w1, w2, w3]; rfl
    have hct' : ct = Γ.ctr (off + (i + 1)) := by rw [hsucc i h, hr, ← hct]; rfl
    obtain ⟨ih1, ih2⟩ := ih ds hds hct'
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    refine ⟨?_, ?_⟩
    · rw [ih1]
      simp only [declsAlong, Array.getElem_toList, hr, lineDecl, hdecl]
      rfl
    · intro q hq d hiq hd
      rcases Nat.lt_or_ge i q with hlt | hge
      · exact ih2 q hq d hlt hd
      · have : q = i := by omega
        subst this
        rw [hr] at hd; cases hd
        rw [← hct]; exact ⟨x, hdecl⟩
  | case2 i ct acc h r hr hx =>
    intro ds hds _
    rw [chunkDeclsGo, dite_eq_left h] at hds
    simp only [hr] at hds
    cases hds
  | case3 i ct acc h hr ih =>
    intro ds hds hct
    rw [chunkDeclsGo, dite_eq_left h] at hds
    split at hds
    · rename_i r hr'; exact absurd hr' (hr r)
    · have hct' : ct.step recs[i] = Γ.ctr (off + (i + 1)) := by rw [hsucc i h, hct]
      obtain ⟨ih1, ih2⟩ := ih ds hds hct'
      rw [List.drop_eq_getElem_cons (by simpa using h)]
      refine ⟨?_, ?_⟩
      · rw [ih1]
        simp only [declsAlong, Array.getElem_toList]
        have : lineDecl T ct recs[i] = none := by
          cases hq : recs[i] with
          | decl r => exact absurd hq (hr r)
          | _ => rfl
        rw [this]
      · intro q hq d hiq hd
        rcases Nat.lt_or_ge i q with hlt | hge
        · exact ih2 q hq d hlt hd
        · have : q = i := by omega
          subst this; exact absurd hd (hr d)
  | case4 i ct acc h =>
    intro ds hds _
    rw [chunkDeclsGo, dite_eq_right h] at hds
    cases hds
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    refine ⟨rfl, fun q hq _ hiq _ => absurd hq (by omega)⟩

/-- **A chunk's declarations**, when every declaration line's builder
yields a record: each is the serial parse's at the line, over tables
holding the window's view, and together they are the records the
serial parse pushes for the chunk. -/
theorem chunkDecls_spec {Γ : WCtx} {P : Prior} {W : Win} {c : Nat} {recs : Array LineRec}
    {off : Nat} (hC : ChunkCtx Γ P W c recs off) {T : Tabs}
    (hV : ViewBelow Γ P W off recs.size T) {ds : Array Declaration}
    (h : chunkDecls P W c recs = some ds) :
    (∀ q (hq : q < recs.size) d, recs[q] = .decl d →
      ∃ x, declOf (cutLk T (Γ.ctr (off + q))) d = .ok (.inl x)) ∧
    ds = declsAlong T (Γ.ctr off) recs.toList #[] := by
  obtain ⟨h1, h2⟩ := chunkDeclsGo_spec hC hV 0 _ _ ds h (by rw [hC.start]; rfl)
  rw [hC.start, List.drop_zero] at h1
  exact ⟨fun q hq d hd => h2 q hq d (Nat.zero_le _) hd, h1⟩

end ConLeche.Frontend
