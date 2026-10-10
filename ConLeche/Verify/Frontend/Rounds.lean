module

public import ConLeche.Verify.Frontend.RoundsWork

public section

/-!
# The rounds parse is the serial parse (task #329)

What the driver of the rounds parse (`ConLeche/Driver/OwnerParse.lean`)
carries between windows is `GOK g`: some state the serial parse
reaches after the lines before (`Reached`) holds the finished tables
`g.P` cut at the counters `g.c`, with the records `g.ds`.  Within a
window it carries `WinInv`: the window's chunk tables are round 0's
over the window's chunks, and every entry stored is good
(`ConLeche/Verify/Frontend/Good.lean`).

* `winInv_ofRound0`, `WinInv.setLate`: round 0's results, checked by
  `after0`, make the invariant, and every later round keeps it
  (`round0_spec`, `roundR_spec`, `ConLeche/Verify/Frontend/RoundsWork.lean`).
* `GOK.window`: once every late entry is done, each chunk scanned to
  its end, the pages built and the tables before the window kept, the
  window is one more stretch of the serial parse — the tables after it
  are good and hold an entry for every line (`allOK_of_good`).
* `GOK.finish` and `GOK.reached`: the end of the stream, and the state
  a window that falls back continues the serial parse from
  (`Prior.toState`).
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The window -/

/-- A chunk's records. -/
@[expose] def recsOf (b : ByteArray) : Array LineRec := (scanChunk b).recs

/-- The lines of a window's chunks, in order. -/
@[expose] def chunkRecs (bs : List ByteArray) : List LineRec :=
  (bs.map fun b => (recsOf b).toList).flatten

/-- Where chunk `c`'s lines start among the window's. -/
@[expose] def chunkOff (bs : List ByteArray) (c : Nat) : Nat :=
  ((bs.take c).map fun b => (recsOf b).size).sum

/-- The window of chunks `bs` from counters `c0` after tables `P`. -/
@[expose] def winCtx (P : Prior) (c0 : Ctr) (bs : List ByteArray) : WCtx := ⟨P, c0, chunkRecs bs⟩

/-- A segment's chunk `c` is round 0's table builder `t`'s (its slots
and keys), with late entries satisfying `Q`. -/
@[expose] def TabAt (s : Seg α) (c : Nat) (t : TB α) (Q : Array α → ByteArray → Prop) : Prop :=
  (∃ T, s.tabs[c]? = some T ∧ T.d0 = t.d ∧ T.late = t.late ∧ T.ls = t.ls ∧ Q T.lv T.ldone) ∧
    s.keys[c]? = some t.keys

/-- **The window invariant**: the window's chunks are round 0's over the
chunks `bs` (with no anomaly, every chunk's first index at least its
start), the starts are the keys', and the late entries are good. -/
@[expose] def WinInv (P : Prior) (bs : List ByteArray) (W : Win) : Prop :=
  W.nc = bs.length ∧ W.n.tabs.size = W.nc ∧ W.l.tabs.size = W.nc ∧ W.e.tabs.size = W.nc ∧
  W.n.keys.size = W.nc ∧ W.l.keys.size = W.nc ∧ W.e.keys.size = W.nc ∧
  (∀ c (h : c < bs.length), (round0 P W.c0 c (recsOf bs[c])).bad = false ∧
    TabAt W.n c (round0 P W.c0 c (recsOf bs[c])).n
      (LateOK (winCtx P W.c0 bs) TV.n (round0 P W.c0 c (recsOf bs[c])).n) ∧
    TabAt W.l c (round0 P W.c0 c (recsOf bs[c])).l
      (LateOK (winCtx P W.c0 bs) TV.l (round0 P W.c0 c (recsOf bs[c])).l) ∧
    TabAt W.e c (round0 P W.c0 c (recsOf bs[c])).e
      (LateOK (winCtx P W.c0 bs) TV.e (round0 P W.c0 c (recsOf bs[c])).e) ∧
    W.n.firstOK c = true ∧ W.l.firstOK c = true ∧ W.e.firstOK c = true) ∧
  W.n.starts = startsGo W.n.keys 0 W.c0.n #[W.c0.n] ∧
  W.l.starts = startsGo W.l.keys 0 W.c0.l #[W.c0.l] ∧
  W.e.starts = startsGo W.e.keys 0 W.c0.e #[W.c0.e]

theorem chunkRecs_cons (b : ByteArray) (bs : List ByteArray) :
    chunkRecs (b :: bs) = (recsOf b).toList ++ chunkRecs bs := by
  simp [chunkRecs]

theorem chunkOff_zero (bs : List ByteArray) : chunkOff bs 0 = 0 := by simp [chunkOff]

theorem chunkOff_cons_succ (b : ByteArray) (bs : List ByteArray) (c : Nat) :
    chunkOff (b :: bs) (c + 1) = (recsOf b).size + chunkOff bs c := by
  simp [chunkOff]

theorem chunkOff_succ (bs : List ByteArray) {c : Nat} (h : c < bs.length) :
    chunkOff bs (c + 1) = chunkOff bs c + (recsOf bs[c]).size := by
  simp only [chunkOff, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero]

theorem chunkOff_length (bs : List ByteArray) : chunkOff bs bs.length = (chunkRecs bs).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, chunkOff_cons_succ, ih, chunkRecs_cons, List.length_append]
    simp

/-- Chunk `c` of a window sits at its offset among the window's lines. -/
theorem chunk_at (bs : List ByteArray) :
    ∀ c (h : c < bs.length), chunkOff bs c + (recsOf bs[c]).size ≤ (chunkRecs bs).length ∧
      ∀ q (hq : q < (recsOf bs[c]).size),
        (chunkRecs bs)[chunkOff bs c + q]? = some (recsOf bs[c])[q] := by
  induction bs with
  | nil => intro c h; simp at h
  | cons b bs ih =>
    intro c h
    cases c with
    | zero =>
      simp only [chunkOff_zero, Nat.zero_add, chunkRecs_cons, List.getElem_cons_zero,
        List.length_append, Array.length_toList]
      refine ⟨by omega, fun q hq => ?_⟩
      rw [List.getElem?_append_left (by simpa using hq)]
      simp [hq]
    | succ c =>
      obtain ⟨h1, h2⟩ := ih c (by simpa using h)
      simp only [chunkOff_cons_succ, chunkRecs_cons, List.getElem_cons_succ, List.length_append,
        Array.length_toList]
      refine ⟨by omega, fun q hq => ?_⟩
      rw [Nat.add_assoc, List.getElem?_append_right (by simp)]
      simp only [Array.length_toList, Nat.add_sub_cancel_left]
      exact h2 q hq

/-- The window embeds each of its chunks. -/
theorem winCtx_emb (P : Prior) (c0 : Ctr) (bs : List ByteArray) {c : Nat} (h : c < bs.length) :
    Emb (winCtx P c0 bs) P c0 (chunkOff bs c) (recsOf bs[c]) :=
  ⟨rfl, rfl, (chunk_at bs c h).1, (chunk_at bs c h).2⟩

/-- Every line of a window lies in one of its chunks. -/
theorem chunk_of_pos (bs : List ByteArray) :
    ∀ p, p < (chunkRecs bs).length → ∃ c q, ∃ (h : c < bs.length), q < (recsOf bs[c]).size ∧
      p = chunkOff bs c + q := by
  induction bs with
  | nil => intro p h; simp [chunkRecs] at h
  | cons b bs ih =>
    intro p hp
    rw [chunkRecs_cons, List.length_append, Array.length_toList] at hp
    rcases Nat.lt_or_ge p (recsOf b).size with h | h
    · exact ⟨0, p, by simp, by simpa using h, by simp [chunkOff_zero]⟩
    · obtain ⟨c, q, hc, hq, hpq⟩ := ih (p - (recsOf b).size) (by omega)
      exact ⟨c + 1, q, by simpa using hc, by simpa using hq,
        by rw [chunkOff_cons_succ]; omega⟩

/-! ### One table of a window, generically -/

/-- The keys of a table builder name its chunk's indices. -/
theorem TBI.rep {P : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb} {inj : α → TV}
    {t : TB α} (hT : t.I P c0 recs tb inj recs.size) :
    t.keys.Rep (idsT tb recs.toList) := by
  have hfull : idsT tb (recs.toList.take recs.size) = idsT tb recs.toList := by
    rw [List.take_of_length_le (by simp)]
  refine ⟨?_, ?_⟩
  · show t.d.size = _; rw [← hfull]; exact hT.size
  · rw [← hfull]; exact hT.shape

theorem TBI.incr' {P : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb} {inj : α → TV}
    {t : TB α} (hT : t.I P c0 recs tb inj recs.size) : Incr (idsT tb recs.toList) := by
  have hfull : idsT tb (recs.toList.take recs.size) = idsT tb recs.toList := by
    rw [List.take_of_length_le (by simp)]
  rw [← hfull]; exact hT.incr

/-- The counters after a whole chunk. -/
theorem winCtx_ctr_succ (P : Prior) (c0 : Ctr) (bs : List ByteArray) {c : Nat}
    (h : c < bs.length) :
    (winCtx P c0 bs).ctr (chunkOff bs (c + 1)) =
      ((winCtx P c0 bs).ctr (chunkOff bs c)).stepAll (recsOf bs[c]).toList := by
  rw [chunkOff_succ bs h, (winCtx_emb P c0 bs h).ctr (Nat.le_refl _),
    List.take_of_length_le (by simp)]

/-- **Where a window's chunks start** in one table: the window's
counters at each chunk's first line. -/
theorem seg_starts {s : Seg α} {sel : R0 → TB α} {inj : α → TV} {tb : Tb} {P : Prior}
    {c0 : Ctr} {bs : List ByteArray} (hk : s.keys.size = bs.length)
    (hseg : ∀ c (h : c < bs.length), s.keys[c]? = some (sel (round0 P c0 c (recsOf bs[c]))).keys ∧
      (sel (round0 P c0 c (recsOf bs[c]))).I P c0 (recsOf bs[c]) tb inj (recsOf bs[c]).size)
    (hst : s.starts = startsGo s.keys 0 (c0.at tb) #[c0.at tb]) :
    ∀ c, c ≤ bs.length → s.starts.getD c 0 = ((winCtx P c0 bs).ctr (chunkOff bs c)).at tb := by
  have hsp : ∀ c, c ≤ bs.length → s.starts.getD c 0 = startsSpec s.keys (c0.at tb) c := by
    intro c hc
    rw [hst]
    exact startsGo_spec s.keys (c0.at tb) 0 _ #[c0.at tb] rfl rfl
      (fun j hj => by have : j = 0 := by omega
                      subst this; rfl) (Nat.zero_le _) c (by omega)
  intro c
  induction c with
  | zero =>
    intro _
    rw [hsp 0 (Nat.zero_le _), chunkOff_zero]
    simp [startsSpec, WCtx.ctr, ctrAt_zero, winCtx]
  | succ c ih =>
    intro hc
    have hcl : c < bs.length := by omega
    rw [hsp _ hc, startsSpec_succ _ _ (by omega)]
    obtain ⟨hK, hT⟩ := hseg c hcl
    have hKe : s.keys[c]'(by omega) = (sel (round0 P c0 c (recsOf bs[c]))).keys := by
      rw [Array.getElem?_eq_getElem (by omega)] at hK; exact Option.some.inj hK
    rw [hKe, winCtx_ctr_succ P c0 bs hcl, stepAll_at]
    have hrep := TBI.rep hT
    have hcnt : (sel (round0 P c0 c (recsOf bs[c]))).keys.cnt =
        (idsT tb (recsOf bs[c]).toList).length := hrep.1
    cases hl : (idsT tb (recsOf bs[c]).toList).getLast? with
    | none =>
      have he : idsT tb (recsOf bs[c]).toList = [] := List.getLast?_eq_none_iff.mp hl
      rw [hcnt, he]
      simp only [List.length_nil, beq_self_eq_true, ↓reduceIte]
      rw [← hsp c (by omega)]; exact ih (by omega)
    | some i =>
      have hne : idsT tb (recsOf bs[c]).toList ≠ [] := by intro h'; rw [h'] at hl; simp at hl
      have hlen : (idsT tb (recsOf bs[c]).toList).length ≠ 0 := by
        intro h'; exact hne (List.eq_nil_of_length_eq_zero h')
      rw [hcnt]
      simp only [beq_iff_eq, hlen, ↓reduceIte]
      rw [keyOf_of_shape hrep.2 _ (by omega)]
      rw [List.getLast?_eq_some_getLast hne, Option.some.injEq, List.getLast_eq_getElem] at hl
      rw [hl]

/-- A chunk whose indices of a table increase and begin at or above
the counter. -/
theorem incAll_of_ids {s : Ctr} {l : List LineRec}
    (h : ∀ t, Incr (idsT t l) ∧ ∀ i, (idsT t l).head? = some i → s.at t ≤ i) : IncAll s l := by
  induction l generalizing s with
  | nil => trivial
  | cons r rs ih =>
    refine ⟨Ctr.fits_iff.mpr fun t i hi => ?_, ih fun t => ?_⟩
    · have := (h t).2 i (by rw [idsT_cons, hi]; rfl)
      exact this
    · obtain ⟨h1, h2⟩ := h t
      rw [idsT_cons] at h1 h2
      refine ⟨?_, fun i hi => ?_⟩
      · cases hr : r.idAt t with
        | none => rw [hr] at h1; simpa using h1
        | some x => rw [hr] at h1; exact (List.pairwise_cons.mp h1).2
      · rw [Ctr.step_at]
        cases hr : r.idAt t with
        | none =>
          rw [hr] at h2
          exact h2 i (by simpa using hi)
        | some x =>
          rw [hr] at h1
          have := (List.pairwise_cons.mp h1).1 i (List.mem_of_mem_head? hi)
          simp only []
          omega

theorem IncAll.append' {c : Ctr} {l₁ l₂ : List LineRec} (h₁ : IncAll c l₁)
    (h₂ : IncAll (c.stepAll l₁) l₂) : IncAll c (l₁ ++ l₂) := by
  induction l₁ generalizing c with
  | nil => exact h₂
  | cons r l ih => exact ⟨h₁.1, ih h₁.2 h₂⟩

theorem IncAll.of_get {c : Ctr} {rs : List LineRec}
    (h : ∀ p (hp : p < rs.length), (ctrAt c rs p).fits rs[p] = true) : IncAll c rs := by
  induction rs generalizing c with
  | nil => trivial
  | cons r rs ih =>
    have h0 := h 0 (by simp)
    rw [List.getElem_cons_zero, ctrAt_zero] at h0
    refine ⟨h0, ih fun p hp => ?_⟩
    have := h (p + 1) (by simpa using hp)
    simpa [ctrAt, List.take_succ_cons, Ctr.stepAll] using this

/-- A chunk's first index of a table at or above its start. -/
theorem firstOK_head {s : Seg α} {c : Nat} (hf : s.firstOK c = true) {t : TB α}
    (hK : s.keys[c]? = some t.keys) {P' : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb}
    {inj : α → TV} (hT : t.I P' c0 recs tb inj recs.size) :
    ∀ i, (idsT tb recs.toList).head? = some i → s.starts.getD c 0 ≤ i := by
  intro i hi
  simp only [Seg.firstOK, hK, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  have hfull : idsT tb (recs.toList.take recs.size) = idsT tb recs.toList := by
    rw [List.take_of_length_le (by simp)]
  have hh := hT.head i (by rw [hfull]; exact hi)
  rcases hf with hf | hf
  · have hne : idsT tb recs.toList ≠ [] := by intro h'; rw [h'] at hi; simp at hi
    have : t.d.size = (idsT tb recs.toList).length := by rw [← hfull]; exact hT.size
    simp only [TB.keys] at hf
    rw [this] at hf
    exact absurd (List.eq_nil_of_length_eq_zero hf) hne
  · simp only [TB.keys] at hf; omega

theorem chunkOff_mono (bs : List ByteArray) {a b : Nat} (h : a ≤ b) :
    chunkOff bs a ≤ chunkOff bs b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih =>
    rename_i m
    rcases Nat.lt_or_ge m bs.length with hm | hm
    · show chunkOff bs a ≤ chunkOff bs (m + 1)
      rw [chunkOff_succ bs hm]; omega
    · show chunkOff bs a ≤ chunkOff bs (m + 1)
      have : chunkOff bs (m + 1) = chunkOff bs m := by
        simp only [chunkOff, List.take_of_length_le (show bs.length ≤ m + 1 by omega),
          List.take_of_length_le hm]
      omega

/-- A chunk table's slots, as round 0's builder's with its late entries. -/
theorem TabAt.get {s : Seg α} {c : Nat} {t : TB α} {Q : Array α → ByteArray → Prop}
    (h : TabAt s c t Q) {k : Nat} {w : α} (hw : s.getAt c k = some w) :
    ∃ T, s.tabs[c]? = some T ∧ Q T.lv T.ldone ∧ t.get T.lv T.ldone k = some w := by
  obtain ⟨⟨T, hT, h1, h2, h3, hq⟩, _⟩ := h
  rw [Seg.getAt_eq, hT] at hw
  simp only [Option.bind_some, CTab.get] at hw
  rw [h1, h2, h3] at hw
  exact ⟨T, hT, hq, hw⟩

theorem getD_of_some {a : Array β} {i : Nat} {x d : β} (h : a[i]? = some x) : a.getD i d = x := by
  rw [Array.getD_eq_getD_getElem?, h]; rfl

/-! ### What the window invariant gives -/

section
variable {P : Prior} {bs : List ByteArray} {W : Win} (hW : WinInv P bs W)
include hW

theorem WinInv.chunk {c : Nat} (h : c < bs.length) :
    (round0 P W.c0 c (recsOf bs[c])).bad = false ∧
    TabAt W.n c (round0 P W.c0 c (recsOf bs[c])).n
      (LateOK (winCtx P W.c0 bs) TV.n (round0 P W.c0 c (recsOf bs[c])).n) ∧
    TabAt W.l c (round0 P W.c0 c (recsOf bs[c])).l
      (LateOK (winCtx P W.c0 bs) TV.l (round0 P W.c0 c (recsOf bs[c])).l) ∧
    TabAt W.e c (round0 P W.c0 c (recsOf bs[c])).e
      (LateOK (winCtx P W.c0 bs) TV.e (round0 P W.c0 c (recsOf bs[c])).e) ∧
    W.n.firstOK c = true ∧ W.l.firstOK c = true ∧ W.e.firstOK c = true :=
  hW.2.2.2.2.2.2.2.1 c h

theorem WinInv.spec {c : Nat} (h : c < bs.length) :
    R0I P W.c0 (recsOf bs[c]) (recsOf bs[c]).size (round0 P W.c0 c (recsOf bs[c])).n
      (round0 P W.c0 c (recsOf bs[c])).l (round0 P W.c0 c (recsOf bs[c])).e
      (round0 P W.c0 c (recsOf bs[c])).pend :=
  round0_spec (hW.chunk h).1

/-- One table of a window's chunk: round 0's builder, its late entries
good, its first index at or above the chunk's start. -/
theorem WinInv.tabAt (S : Sel α) {c : Nat} (h : c < bs.length) :
    TabAt (S.seg W) c (S.r0 (round0 P W.c0 c (recsOf bs[c])))
      (LateOK (winCtx P W.c0 bs) S.inj (S.r0 (round0 P W.c0 c (recsOf bs[c])))) ∧
    (S.seg W).firstOK c = true := by
  obtain ⟨_, hn, hl, he, fn, fl, fe⟩ := hW.chunk h
  cases S
  · exact ⟨hn, fn⟩
  · exact ⟨hl, fl⟩
  · exact ⟨he, fe⟩

theorem WinInv.specS (S : Sel α) {c : Nat} (h : c < bs.length) :
    (S.r0 (round0 P W.c0 c (recsOf bs[c]))).I P W.c0 (recsOf bs[c]) S.tb S.inj
      (recsOf bs[c]).size := by
  cases S
  · exact (hW.spec h).n
  · exact (hW.spec h).l
  · exact (hW.spec h).e

theorem WinInv.tabsSize (S : Sel α) : (S.seg W).tabs.size = W.nc := by
  cases S
  · exact hW.2.1
  · exact hW.2.2.1
  · exact hW.2.2.2.1

theorem WinInv.keysSize (S : Sel α) : (S.seg W).keys.size = W.nc := by
  cases S
  · exact hW.2.2.2.2.1
  · exact hW.2.2.2.2.2.1
  · exact hW.2.2.2.2.2.2.1

theorem WinInv.startsEq (S : Sel α) :
    (S.seg W).starts = startsGo (S.seg W).keys 0 (W.c0.at S.tb) #[W.c0.at S.tb] := by
  cases S
  · exact hW.2.2.2.2.2.2.2.2.1
  · exact hW.2.2.2.2.2.2.2.2.2.1
  · exact hW.2.2.2.2.2.2.2.2.2.2

/-- Where the window's chunks start, in each table. -/
theorem WinInv.starts (S : Sel α) : ∀ c, c ≤ bs.length →
    (S.seg W).starts.getD c 0 = ((winCtx P W.c0 bs).ctr (chunkOff bs c)).at S.tb :=
  seg_starts (sel := S.r0) (inj := S.inj) (tb := S.tb) (by rw [hW.keysSize S, hW.1])
    (fun _ h => ⟨(hW.tabAt S h).1.2, hW.specS S h⟩) (hW.startsEq S)

/-- **The window's lines bind each table in increasing order.** -/
theorem WinInv.inc : IncAll W.c0 (chunkRecs bs) := by
  have hchunk : ∀ c (h : c < bs.length),
      IncAll ((winCtx P W.c0 bs).ctr (chunkOff bs c)) (recsOf bs[c]).toList := by
    intro c h
    apply incAll_of_ids
    intro t
    obtain ⟨_, S, rfl⟩ := t.exSel
    exact ⟨TBI.incr' (hW.specS S h), fun i hi => by
      have := firstOK_head (hW.tabAt S h).2 (hW.tabAt S h).1.2 (hW.specS S h) i hi
      rw [hW.starts S c (by omega)] at this; exact this⟩
  apply IncAll.of_get
  intro p hp
  obtain ⟨c, q, hc, hq, rfl⟩ := chunk_of_pos bs p hp
  have hE := winCtx_emb P W.c0 bs hc
  have h1 : (chunkRecs bs)[chunkOff bs c + q] = (recsOf bs[c])[q] := by
    have := hE.2.2.2 q hq
    simp only [winCtx] at this
    rw [List.getElem?_eq_getElem hp] at this
    exact Option.some.inj this
  have h2 : ctrAt W.c0 (chunkRecs bs) (chunkOff bs c + q) =
      ctrAt ((winCtx P W.c0 bs).ctr (chunkOff bs c)) (recsOf bs[c]).toList q := by
    have := hE.ctr (p := q) (Nat.le_of_lt hq)
    simp only [WCtx.ctr, winCtx] at this ⊢
    rw [this]; rfl
  rw [h1, h2]
  have := (hchunk c hc).get q (by simpa using hq)
  simpa using this

theorem WinInv.ctr_mono {a b : Nat} (h : a ≤ b) (t : Tb) :
    ((winCtx P W.c0 bs).ctr a).at t ≤ ((winCtx P W.c0 bs).ctr b).at t :=
  ctrAt_mono hW.inc h t

theorem WinInv.mono (S : Sel α) : (S.seg W).mono := fun c hc => by
  have hl : c < bs.length := by rw [hW.tabsSize S, hW.1] at hc; exact hc
  rw [hW.starts S c (by omega), hW.starts S (c + 1) (by omega)]
  exact hW.ctr_mono (chunkOff_mono bs (Nat.le_succ c)) S.tb

/-- **Every entry a window's chunk tables hold is good** for the index
its key names. -/
theorem WinInv.store (S : Sel α) : ∀ e k w, (S.seg W).getAt e k = some w →
    ∃ K', (S.seg W).keys[e]? = some K' ∧ Good (winCtx P W.c0 bs) (K'.keyOf k) (S.inj w) := by
  intro e k w hw
  have he : e < bs.length := by
    rw [Seg.getAt_eq] at hw
    cases ht : (S.seg W).tabs[e]? with
    | none => rw [ht] at hw; cases hw
    | some _ =>
      have := (Array.getElem?_eq_some_iff.mp ht).1
      rw [hW.tabsSize S, hW.1] at this; exact this
  obtain ⟨T, _, hq, hg⟩ := (hW.tabAt S he).1.get hw
  exact ⟨_, (hW.tabAt S he).1.2, TBI.get_good (hW.specS S he) (winCtx_emb P W.c0 bs he) hq hg⟩

/-- **Each chunk of the window, as a later round sees it.** -/
theorem WinInv.chunkCtx {c : Nat} (hc : c < bs.length) :
    ChunkCtx (winCtx P W.c0 bs) P W c (recsOf bs[c]) (chunkOff bs c) := by
  obtain ⟨hb, ⟨⟨Tn, hTn, n1, n2, n3, _⟩, hKn⟩, ⟨⟨Tl, hTl, l1, l2, l3, _⟩, hKl⟩,
    ⟨⟨Te, hTe, e1, e2, e3, _⟩, hKe⟩, _⟩ := hW.chunk hc
  refine ⟨winCtx_emb P W.c0 bs hc, hb, ?_, fun S e k w _ hw => hW.store S e k w hw⟩
  simp only [Win.geo]
  rw [getD_of_some hTn, getD_of_some hTl, getD_of_some hTe, getD_of_some hKn, getD_of_some hKl,
    getD_of_some hKe, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?]
  have sn := hW.starts .n c (by omega)
  have sl := hW.starts .l c (by omega)
  have se := hW.starts .e c (by omega)
  rw [Array.getD_eq_getD_getElem?] at sn sl se
  simp only [Sel.seg, Sel.tb] at sn sl se
  rw [sn, sl, se, n1, n2, n3, l1, l2, l3, e1, e2, e3]
  rfl

/-- The window's counters at its end. -/
theorem WinInv.cEnd : W.cEnd = W.c0.stepAll (chunkRecs bs) := by
  have hn := hW.starts .n bs.length (Nat.le_refl _)
  have hl := hW.starts .l bs.length (Nat.le_refl _)
  have he := hW.starts .e bs.length (Nat.le_refl _)
  rw [chunkOff_length] at hn hl he
  simp only [Sel.seg, Sel.tb] at hn hl he
  simp only [WCtx.ctr, ctrAt, winCtx, List.take_length] at hn hl he
  simp only [Win.cEnd, Win.start, hW.1, hn, hl, he]
  rfl

end

/-- Round 0's results, as the window's chunk tables. -/
theorem winInv_ofRound0 {P : Prior} {c0 : Ctr} {bs : List ByteArray} {os : Array R0}
    (hsz : os.size = bs.length)
    (hos : ∀ c (h : c < bs.length),
      os[c]'(by omega) = { round0 P c0 c (recsOf bs[c]) with pend := #[] })
    (ha : after0 (Win.ofRound0 c0 os) os = true) :
    WinInv P bs (Win.ofRound0 c0 os) := by
  simp only [after0, Bool.and_eq_true, List.all_eq_true, List.mem_range] at ha
  obtain ⟨_, hall⟩ := ha
  refine ⟨by simp [Win.ofRound0, hsz], by simp [Win.ofRound0, Seg.mk'], by simp [Win.ofRound0, Seg.mk'],
    by simp [Win.ofRound0, Seg.mk'], by simp [Win.ofRound0, Seg.mk'],
    by simp [Win.ofRound0, Seg.mk'], by simp [Win.ofRound0, Seg.mk'], fun c hc => ?_, rfl, rfl,
    rfl⟩
  have hco : c < os.size := by omega
  have hoc := hos c hc
  have hall' := hall c hco
  rw [Array.getElem?_eq_getElem hco] at hall'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall'
  obtain ⟨⟨⟨hb, h1⟩, h2⟩, h3⟩ := hall'
  rw [hoc] at hb
  refine ⟨hb, ?_, ?_, ?_, h1, h2, h3⟩
  · refine ⟨⟨(round0 P c0 c (recsOf bs[c])).n.tab, by simp [Win.ofRound0, Seg.mk', hco, hoc],
      rfl, rfl, rfl, LateOK.init _ _ _⟩, by simp [Win.ofRound0, Seg.mk', hco, hoc]⟩
  · refine ⟨⟨(round0 P c0 c (recsOf bs[c])).l.tab, by simp [Win.ofRound0, Seg.mk', hco, hoc],
      rfl, rfl, rfl, LateOK.init _ _ _⟩, by simp [Win.ofRound0, Seg.mk', hco, hoc]⟩
  · refine ⟨⟨(round0 P c0 c (recsOf bs[c])).e.tab, by simp [Win.ofRound0, Seg.mk', hco, hoc],
      rfl, rfl, rfl, LateOK.init _ _ _⟩, by simp [Win.ofRound0, Seg.mk', hco, hoc]⟩

/-- The late entries of a round's result. -/
@[expose] def RR.lates (r : RR) :
    (Array Name × ByteArray) × (Array Level × ByteArray) × (Array Expr × ByteArray) :=
  ((r.vn, r.dn), (r.vl, r.dl), (r.ve, r.de))

/-- What a later round's result for chunk `c` (bytes `b`) must be: the
round function's on the chunk's records and pending lines its owner
holds, without an anomaly. -/
@[expose] def RRok (P : Prior) (W : Win) (c : Nat) (b : ByteArray) (r : RR) : Prop :=
  ∃ pend, PendOK P W.c0 c (recsOf b) pend ∧
    RR.lates r = RR.lates (roundR P W c (recsOf b) pend) ∧
    (roundR P W c (recsOf b) pend).bad = false

/-- A later round keeps the invariant. -/
theorem WinInv.setLate {P : Prior} {bs : List ByteArray} {W : Win} (hW : WinInv P bs W)
    (rrs : Array RR) (hsz : rrs.size = W.nc)
    (hrr : ∀ c (h : c < rrs.size) (hb : c < bs.length), RRok P W c bs[c] rrs[c]) :
    WinInv P bs (W.setLate rrs) := by
  have hn : W.nc = bs.length := hW.1
  have tabsAt : ∀ {α : Type} (sg : Seg α) (lvs : Array (Array α × ByteArray)) (c : Nat)
      (T : CTab α), sg.tabs[c]? = some T → c < lvs.size →
      (sg.setLate lvs).tabs[c]? = some { T with lv := lvs[c]!.1, ldone := lvs[c]!.2 } := by
    intro α sg lvs c T hT hc
    have hc' : c < sg.tabs.size := (Array.getElem?_eq_some_iff.mp hT).1
    have hTe : sg.tabs[c] = T := (Array.getElem?_eq_some_iff.mp hT).2
    have hz : c < (sg.tabs.zip lvs).size := by rw [Array.size_zip]; omega
    simp only [Seg.setLate, Array.getElem?_map, Array.getElem?_eq_getElem hz, Option.map_some,
      Array.getElem_zip, hTe, getElem!_pos lvs c hc]
  refine ⟨hW.1, by simp [Win.setLate, Seg.setLate, hW.2.1, hsz],
    by simp [Win.setLate, Seg.setLate, hW.2.2.1, hsz], by simp [Win.setLate, Seg.setLate, hW.2.2.2.1, hsz],
    hW.2.2.2.2.1, hW.2.2.2.2.2.1, hW.2.2.2.2.2.2.1, fun c hc => ?_, hW.2.2.2.2.2.2.2.2.1,
    hW.2.2.2.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.2.2.2⟩
  have hcr : c < rrs.size := by omega
  obtain ⟨hb, ⟨⟨Tn, hTn, n1, n2, n3, hLn⟩, hKn⟩, ⟨⟨Tl, hTl, l1, l2, l3, hLl⟩, hKl⟩,
    ⟨⟨Te, hTe, e1, e2, e3, hLe⟩, hKe⟩, f1, f2, f3⟩ := hW.chunk hc
  obtain ⟨pend, hpend, hlates, hbad⟩ := hrr c hcr hc
  have hI : RRI (winCtx P W.c0 bs) P W c (recsOf bs[c]) pend (W.n.tabs.getD c .blank).lv
      (W.n.tabs.getD c .blank).ldone (W.l.tabs.getD c .blank).lv (W.l.tabs.getD c .blank).ldone
      (W.e.tabs.getD c .blank).lv (W.e.tabs.getD c .blank).ldone #[] := by
    rw [getD_of_some hTn, getD_of_some hTl, getD_of_some hTe]
    exact ⟨hLn, hLl, hLe, fun x hx => by simp at hx⟩
  have hR := roundR_spec (hW.chunkCtx hc) (hpend hb) hI hbad
  simp only [RR.lates, Prod.mk.injEq] at hlates
  obtain ⟨⟨v1, d1⟩, ⟨v2, d2⟩, ⟨v3, d3⟩⟩ := hlates
  have hgetD : ∀ {β : Type} (f : RR → Array β × ByteArray), (rrs.map f)[c]! = f rrs[c] := by
    intro β f; rw [getElem!_pos _ c (by simp; omega)]; simp
  refine ⟨hb, ⟨⟨_, tabsAt W.n _ c Tn hTn (by simp; omega), n1, n2, n3, ?_⟩, hKn⟩,
    ⟨⟨_, tabsAt W.l _ c Tl hTl (by simp; omega), l1, l2, l3, ?_⟩, hKl⟩,
    ⟨⟨_, tabsAt W.e _ c Te hTe (by simp; omega), e1, e2, e3, ?_⟩, hKe⟩, f1, f2, f3⟩
  · simp only [hgetD]; rw [v1, d1]; exact hR.n
  · simp only [hgetD]; rw [v2, d2]; exact hR.l
  · simp only [hgetD]; rw [v3, d3]; exact hR.e

theorem Win.setLate_c0 (W : Win) (rrs : Array RR) : (W.setLate rrs).c0 = W.c0 := rfl
theorem Win.setLate_nc (W : Win) (rrs : Array RR) : (W.setLate rrs).nc = W.nc := rfl

/-! ## The finished tables -/

theorem Pages.atRank_eq (P : Pages α) (r : Nat) :
    P.atRank r = (P.pages[r / 4096]?.bind fun pg => pg[r % 4096]?) := by
  have h1 : r >>> 12 = r / 4096 := by rw [Nat.shiftRight_eq_div_pow]
  have h2 : r &&& 4095 = r % 4096 := by
    have := Nat.and_two_pow_sub_one_eq_mod r 12; simpa using this
  simp only [Pages.atRank, h1, h2]
  by_cases hp : r / 4096 < P.pages.size
  · simp [hp]
  · simp [hp]

/-! ### The runs

`findRank` is what a list of runs says of an index: the first run that
holds it.  On runs in increasing order (`RunsOK`) at most one does, and
the binary search finds it (`Pages.rank_eq`). -/

theorem Run.rank_some {x : Run} {j r : Nat} :
    x.rank j = some r ↔ x.i ≤ j ∧ j < x.e ∧ r = x.r + (j - x.i) := by
  unfold Run.rank
  split
  · rename_i h
    simp only [Option.some.injEq]
    exact ⟨fun e => ⟨h.1, h.2, e.symm⟩, fun e => e.2.2.symm⟩
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun e => h ⟨e.1, e.2.1⟩

theorem Run.rank_none {x : Run} {j : Nat} : x.rank j = none ↔ ¬ (x.i ≤ j ∧ j < x.e) := by
  unfold Run.rank; split <;> simp_all

/-- The rank a list of runs gives index `j`: the first run's that holds
it. -/
@[expose] def findRank (rs : List Run) (j : Nat) : Option Nat := rs.findSome? (·.rank j)

/-- Runs in increasing order of indices, below index `b`, their ranks
below `n`. -/
@[expose] def RunsOK (rs : List Run) (b n : Nat) : Prop :=
  rs.Pairwise (fun x y => x.e ≤ y.i) ∧ ∀ x ∈ rs, x.i ≤ x.e ∧ x.e ≤ b ∧ x.r + (x.e - x.i) ≤ n

theorem RunsOK.mono {rs : List Run} {b n b' n' : Nat} (h : RunsOK rs b n) (hb : b ≤ b')
    (hn : n ≤ n') : RunsOK rs b' n' :=
  ⟨h.1, fun x hx => by have := h.2 x hx; exact ⟨this.1, by omega, by omega⟩⟩

theorem RunsOK.nil (b n : Nat) : RunsOK [] b n := ⟨List.Pairwise.nil, by simp⟩

/-- One more run after the others. -/
theorem RunsOK.snoc {L : List Run} {b n E N : Nat} (h : RunsOK L b n) {z : Run}
    (hz : b ≤ z.i) (hz2 : z.i ≤ z.e) (hE : z.e ≤ E) (hbE : b ≤ E)
    (hN : z.r + (z.e - z.i) ≤ N) (hn : n ≤ N) : RunsOK (L ++ [z]) E N := by
  refine ⟨List.pairwise_append.mpr ⟨h.1, by simp, fun a ha y hy => ?_⟩, fun a ha => ?_⟩
  · simp only [List.mem_singleton] at hy; subst hy
    have := h.2 a ha; omega
  · rcases List.mem_append.mp ha with ha | ha
    · have := h.2 a ha; exact ⟨this.1, by omega, by omega⟩
    · simp only [List.mem_singleton] at ha; subst ha; exact ⟨hz2, hE, hN⟩

theorem findSome?_unique {f : β → Option γ} :
    ∀ (l : List β) (c : Nat) (hc : c < l.length),
    (∀ k (hk : k < l.length), k ≠ c → f l[k] = none) → l.findSome? f = f l[c]
  | [], c, hc, _ => absurd hc (by simp)
  | x :: l, 0, _, h => by
    rw [List.findSome?_cons]
    simp only [List.getElem_cons_zero]
    split
    · rename_i b hb; exact hb.symm
    · rename_i hb
      rw [hb, List.findSome?_eq_none_iff]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
      have := h (k + 1) (by simp; omega) (by omega)
      rwa [List.getElem_cons_succ] at this
  | x :: l, c + 1, hc, h => by
    have h0 : f x = none := by
      have := h 0 (by simp) (by omega); rwa [List.getElem_cons_zero] at this
    rw [List.findSome?_cons, h0]
    simp only [List.getElem_cons_succ]
    exact findSome?_unique l c (by simpa using hc) fun k hk hkc => by
      have := h (k + 1) (by simp; omega) (by omega); rwa [List.getElem_cons_succ] at this

/-- **The binary search over the runs**: the last run in `[lo, hi)`
whose first index is at most `j`, or `lo`. -/
theorem runFind_spec (rs : Array Run) (j : Nat) :
    ∀ lo hi, lo < hi → ((rs.getD lo default).i ≤ j ∨ lo = 0) →
    (hi = rs.size ∨ j < (rs.getD hi default).i) →
    runFind rs j lo hi < hi ∧ ((rs.getD (runFind rs j lo hi) default).i ≤ j ∨ runFind rs j lo hi = 0) ∧
    (runFind rs j lo hi + 1 = rs.size ∨ j < (rs.getD (runFind rs j lo hi + 1) default).i) := by
  intro lo hi
  induction lo, hi using runFind.induct rs j with
  | case1 lo hi h mid hmid ih =>
    intro hlh hlo hhi
    rw [runFind, ite_eq_left h]; simp only [mid] at hmid ⊢; rw [ite_eq_left hmid]
    exact ih (by simp only [mid]; omega) (Or.inl hmid) hhi
  | case2 lo hi h mid hmid ih =>
    intro hlh hlo hhi
    rw [runFind, ite_eq_left h]; simp only [mid] at hmid ⊢; rw [ite_eq_right hmid]
    obtain ⟨r1, r2, r3⟩ := ih (by simp only [mid]; omega) hlo (Or.inr (by simp only [mid]; omega))
    exact ⟨by simp only [mid] at r1; omega, r2, r3⟩
  | case3 lo hi h =>
    intro hlh hlo hhi
    rw [runFind, ite_eq_right h]
    have : hi = lo + 1 := by omega
    subst this
    exact ⟨by omega, hlo, hhi⟩

theorem Array.getD_lt {a : Array β} {i : Nat} {d : β} (h : i < a.size) : a.getD i d = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

/-- **On increasing runs, the binary search is the first run holding
the index.** -/
theorem Pages.rank_eq {P : Pages α} {b n : Nat} (h : RunsOK P.runs.toList b n) (j : Nat) :
    P.rank j = findRank P.runs.toList j := by
  have hpw := List.pairwise_iff_getElem.mp h.1
  have hc : ∀ c, c < P.runs.size → ((P.runs.getD c default).i ≤ j ∨ c = 0) →
      (c + 1 = P.runs.size ∨ j < (P.runs.getD (c + 1) default).i) →
      (if h : c < P.runs.size then P.runs[c].rank j else none) = findRank P.runs.toList j := by
    intro c hcs h0 h1
    rw [dite_eq_left hcs, findRank]
    have hl : c < P.runs.toList.length := by simpa using hcs
    rw [findSome?_unique _ c hl ?_]
    · simp
    intro k hk hkc
    have hk' : k < P.runs.size := by simpa using hk
    simp only [Array.getElem_toList]
    rw [Run.rank_none]
    rintro ⟨hk1, hk2⟩
    rcases Nat.lt_or_gt_of_ne hkc with hlt | hlt
    · have := hpw k c hk hl hlt
      simp only [Array.getElem_toList] at this
      rcases h0 with h0 | h0
      · rw [Array.getD_lt hcs] at h0; omega
      · omega
    · rcases h1 with h1 | h1
      · omega
      · have hc1 : c + 1 < P.runs.size := by omega
        rw [Array.getD_lt hc1] at h1
        have hle : P.runs[c + 1].i ≤ P.runs[k].i := by
          rcases Nat.eq_or_lt_of_le (show c + 1 ≤ k by omega) with he | he
          · simp only [he]; exact Nat.le_refl _
          · have h3 := hpw (c + 1) k (by simpa using hc1) hk he
            have h4 := (h.2 _ (List.getElem_mem (l := P.runs.toList) (by simpa using hc1))).1
            simp only [Array.getElem_toList] at h3 h4
            omega
        omega
  unfold Pages.rank
  simp only []
  by_cases h2 : P.runs.size < 2
  · rw [ite_eq_left h2]
    by_cases h0 : P.runs.size = 0
    · have : P.runs.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using h0)
      rw [this, dite_eq_right (by omega)]; rfl
    · exact hc 0 (by omega) (Or.inr rfl) (Or.inl (by omega))
  · rw [ite_eq_right h2]
    obtain ⟨h2', h3, h4⟩ := runFind_spec P.runs j 0 P.runs.size (by omega) (Or.inr rfl) (Or.inl rfl)
    exact hc _ h2' h3 h4

theorem Pages.get_eq {P : Pages α} {b n : Nat} (h : RunsOK P.runs.toList b n) (j : Nat) :
    P.get j = (findRank P.runs.toList j).bind P.atRank := by
  unfold Pages.get; rw [Pages.rank_eq h]; cases findRank P.runs.toList j <;> rfl

theorem Run.rank_fuse {y x : Run} (he : y.e = x.i) (hr : y.r + (y.e - y.i) = x.r)
    (hy : y.i ≤ y.e) (hx : x.i ≤ x.e) (j : Nat) :
    (Run.mk y.i x.e y.r).rank j = (y.rank j).or (x.rank j) := by
  obtain ⟨yi, ye, yr⟩ := y
  obtain ⟨xi, xe, xr⟩ := x
  simp only at he hr hy hx
  subst he hr
  unfold Run.rank
  simp only
  split <;> split <;> split <;> simp_all <;> omega

theorem findRank_snoc (L : List Run) (x : Run) (j : Nat) :
    findRank (L ++ [x]) j = (findRank L j).or (x.rank j) := by
  simp only [findRank, List.findSome?_append, List.findSome?_cons, List.findSome?_nil]
  cases x.rank j <;> rfl

/-- A run added: what the runs say is what they said before, else what
the run says. -/
theorem pushRun_find {rs : Array Run} {x : Run} (hi : ∀ y ∈ rs.toList, y.i ≤ y.e)
    (hx : x.i ≤ x.e) (j : Nat) :
    findRank (pushRun rs x).toList j = (findRank rs.toList j).or (x.rank j) := by
  unfold pushRun
  cases hb : rs.back? with
  | none => simp only [Array.toList_push, findRank_snoc]
  | some y =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hb
    simp only []
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨he, hr⟩ := hc
      have hy := hi y (by simp)
      simp only [Array.pop_push, Array.toList_push, findRank_snoc, Option.or_assoc]
      rw [Run.rank_fuse he hr hy hx]
    · simp only [Array.toList_push, findRank_snoc]

/-- A run added after runs below its first index. -/
theorem RunsOK.push {rs : Array Run} {b n : Nat} (h : RunsOK rs.toList b n) {x : Run}
    (hb : b ≤ x.i) (hx : x.i ≤ x.e) (hn : n ≤ x.r) :
    RunsOK (pushRun rs x).toList x.e (x.r + (x.e - x.i)) := by
  unfold pushRun
  cases hbk : rs.back? with
  | none =>
    simp only [Array.toList_push]
    exact h.snoc hb hx (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega)
  | some y =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp hbk
    simp only []
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [Array.toList_push] at h
      have hy := h.2 y (by simp)
      have hys : RunsOK ys.toList y.i n := by
        refine ⟨(List.pairwise_append.mp h.1).1, fun a ha => ?_⟩
        have h1 := h.2 a (by simp [ha])
        have h2 := (List.pairwise_append.mp h.1).2.2 a ha y (by simp)
        exact ⟨h1.1, h2, h1.2.2⟩
      simp only [Array.pop_push, Array.toList_push]
      exact hys.snoc (Nat.le_refl _) (by simp only []; omega) (Nat.le_refl _) (by omega)
        (by simp only []; omega) (by omega)
    · simp only [Array.toList_push] at h ⊢
      exact h.snoc hb hx (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega)

/-! ### The runs of a window -/

theorem Keys.keyOf_lt {K : Keys} {l : List Nat} (hK : K.Rep l) (hl : Incr l) {a b : Nat}
    (hab : a < b) (hb : b < K.cnt) : K.keyOf a < K.keyOf b := by
  have hlen : K.cnt = l.length := hK.1
  rw [keyOf_of_shape hK.2 a (by omega), keyOf_of_shape hK.2 b (by omega)]
  exact List.pairwise_iff_getElem.mp hl a b _ _ hab

/-- The position of index `j` among keys `K`, if it is the `k`-th or
later. -/
@[expose] def idxFrom (K : Keys) (j k : Nat) : Option Nat :=
  match K.idx j with
  | some k' => if k ≤ k' then some k' else none
  | none => none

theorem idsRuns_spec {K : Keys} {l : List Nat} (hK : K.Rep l) (hl : Incr l) (base E : Nat)
    (hE : ∀ k, k < K.cnt → K.keyOf k < E) :
    ∀ k (acc : Array Run) (b : Nat), k ≤ K.cnt → RunsOK acc.toList b (base + k) → b ≤ E →
    (k < K.cnt → b ≤ K.keyOf k) →
    RunsOK (idsRuns K base k acc).toList E (base + K.cnt) ∧
    ∀ j, findRank (idsRuns K base k acc).toList j =
      (findRank acc.toList j).or ((idxFrom K j k).map (base + ·)) := by
  intro k acc
  induction k, acc using idsRuns.induct K base with
  | case1 k acc hk ih =>
    intro b _ hacc hbE hbk
    rw [idsRuns, ite_eq_left hk]
    have hb0 := hbk hk
    have hacc' := hacc.push (x := ⟨K.keyOf k, K.keyOf k + 1, base + k⟩) hb0
      (by simp only []; omega) (Nat.le_refl _)
    obtain ⟨r1, r2⟩ := ih (K.keyOf k + 1) (by omega)
      (hacc'.mono (Nat.le_refl _) (by simp only []; omega)) (hE k hk)
      (fun h => Keys.keyOf_lt hK hl (by omega) h)
    refine ⟨r1, fun j => ?_⟩
    rw [r2 j, pushRun_find (fun y hy => (hacc.2 y hy).1) (by simp only []; omega),
      Option.or_assoc]
    congr 1
    unfold idxFrom
    cases hidx : K.idx j with
    | none =>
      have : ¬ (K.keyOf k ≤ j ∧ j < K.keyOf k + 1) := by
        intro h
        have : j = K.keyOf k := by omega
        rw [this, Keys.idx_complete hK hl hk] at hidx; cases hidx
      simp [Run.rank, this]
    | some k' =>
      obtain ⟨hk'c, hkey⟩ := Keys.idx_sound hidx
      rcases Nat.lt_trichotomy k' k with h | h | h
      · have := Keys.keyOf_lt hK hl h hk
        have hn : ¬ (K.keyOf k ≤ j ∧ j < K.keyOf k + 1) := by omega
        simp [Run.rank, hn, show ¬ k + 1 ≤ k' by omega, show ¬ k ≤ k' by omega]
      · subst h
        simp [Run.rank, hkey]
      · have := Keys.keyOf_lt hK hl h hk'c
        have hn : ¬ (K.keyOf k ≤ j ∧ j < K.keyOf k + 1) := by omega
        simp [Run.rank, hn, show k + 1 ≤ k' by omega, show k ≤ k' by omega]
  | case2 k acc hk =>
    intro b hkc hacc hbE _
    rw [idsRuns, ite_eq_right hk]
    have : k = K.cnt := by omega
    subst this
    refine ⟨hacc.mono hbE (Nat.le_refl _), fun j => ?_⟩
    have : idxFrom K j K.cnt = none := by
      unfold idxFrom; split
      · rename_i k' h; exact ite_eq_right (Nat.not_le.mpr (Keys.idx_sound h).1)
      · rfl
    simp [this]

/-- **The runs of a chunk's keys** say, of an index, its position among
the keys, from rank `base`. -/
theorem keysRuns_spec {K : Keys} {l : List Nat} (hK : K.Rep l) (hl : Incr l) {base b E : Nat}
    (hk : ∀ k, k < K.cnt → b ≤ K.keyOf k ∧ K.keyOf k < E) (hbE : b ≤ E) {acc : Array Run}
    (hacc : RunsOK acc.toList b base) :
    RunsOK (keysRuns K base acc).toList E (base + K.cnt) ∧
    ∀ j, findRank (keysRuns K base acc).toList j =
      (findRank acc.toList j).or ((K.idx j).map (base + ·)) := by
  unfold keysRuns
  by_cases h0 : K.cnt = 0
  · rw [ite_eq_left (by simp [h0])]
    refine ⟨hacc.mono hbE (by omega), fun j => ?_⟩
    have : K.idx j = none := by
      cases h : K.idx j with
      | none => rfl
      | some k => have := (Keys.idx_sound h).1; omega
    simp [this]
  · rw [ite_eq_right (by simp [h0])]
    split
    · rename_i he
      have hd : ∀ k, K.keyOf k = K.first + k := fun k => by simp [Keys.keyOf, he]
      have h1 := hk 0 (by omega)
      have h2 := hk (K.cnt - 1) (by omega)
      rw [hd] at h1 h2
      refine ⟨(hacc.push (x := ⟨K.first, K.first + K.cnt, base⟩) (by simp only []; omega)
        (by simp only []; omega) (Nat.le_refl _)).mono (by simp only []; omega)
        (by simp only []; omega), fun j => ?_⟩
      rw [pushRun_find (fun y hy => (hacc.2 y hy).1) (by simp only []; omega)]
      congr 1
      simp only [Run.rank, Keys.idx, he, ↓reduceIte]
      split <;> simp
    · rename_i he
      have := idsRuns_spec hK hl base E (fun k hk' => (hk k hk').2) 0 acc b (Nat.zero_le _)
        (by simpa using hacc) hbE (fun h => (hk 0 h).1)
      refine ⟨this.1, fun j => ?_⟩
      rw [this.2 j]; congr 1
      unfold idxFrom; cases K.idx j <;> simp

/-- What the runs of a window's chunks from chunk `c` say of index `j`:
the first chunk's whose keys hold it. -/
@[expose] def winClaim (ks : Array Keys) (st : Array Nat) (j c : Nat) : Option Nat :=
  if h : c < ks.size then ((ks[c].idx j).map (st.getD c 0 + ·)).or (winClaim ks st j (c + 1))
  else none
termination_by ks.size - c

/-- **The runs of a window**, after the runs before: in increasing
order, and saying of an index what the runs before say, else its chunk's
keys. -/
theorem winRunsGo_spec (ks : Array Keys) (st : Array Nat) (S : Nat → Nat)
    (hk : ∀ c (h : c < ks.size), ∃ l, ks[c].Rep l ∧ Incr l ∧
      ∀ k, k < ks[c].cnt → S c ≤ ks[c].keyOf k ∧ ks[c].keyOf k < S (c + 1))
    (hS : ∀ c, c < ks.size → S c ≤ S (c + 1))
    (hst : ∀ c (h : c < ks.size), st.getD (c + 1) 0 = st.getD c 0 + ks[c].cnt) :
    ∀ c (acc : Array Run), c ≤ ks.size → RunsOK acc.toList (S c) (st.getD c 0) →
    RunsOK (winRunsGo ks st c acc).toList (S ks.size) (st.getD ks.size 0) ∧
    ∀ j, findRank (winRunsGo ks st c acc).toList j =
      (findRank acc.toList j).or (winClaim ks st j c) := by
  intro c acc
  induction c, acc using winRunsGo.induct ks st with
  | case1 c acc h ih =>
    intro _ hacc
    rw [winRunsGo, dite_eq_left h]
    obtain ⟨l, hK, hl, hkk⟩ := hk c h
    obtain ⟨k1, k2⟩ := keysRuns_spec hK hl hkk (hS c h) hacc
    rw [← hst c h] at k1
    obtain ⟨r1, r2⟩ := ih (by omega) k1
    refine ⟨r1, fun j => ?_⟩
    rw [r2 j, k2 j, Option.or_assoc]
    conv => rhs; rw [winClaim, dite_eq_left h]
  | case2 c acc h =>
    intro hc hacc
    rw [winRunsGo, dite_eq_right h]
    have : c = ks.size := by omega
    subst this
    refine ⟨hacc, fun j => ?_⟩
    rw [winClaim, dite_eq_right h]; simp

theorem winClaim_none {ks : Array Keys} {st : Array Nat} {j : Nat} :
    ∀ c, (∀ c' (h : c' < ks.size), c ≤ c' → ks[c'].idx j = none) → winClaim ks st j c = none := by
  intro c
  induction c using winClaim.induct ks with
  | case1 c h ih =>
    intro hn
    rw [winClaim, dite_eq_left h, hn c h (Nat.le_refl _), ih fun c' h' hc => hn c' h' (by omega)]
    rfl
  | case2 c h => intro _; rw [winClaim, dite_eq_right h]

theorem winClaim_one {ks : Array Keys} {st : Array Nat} {j c1 : Nat} (h1 : c1 < ks.size) :
    ∀ c, c ≤ c1 → (∀ c' (h : c' < ks.size), c ≤ c' → c' ≠ c1 → ks[c'].idx j = none) →
    winClaim ks st j c = (ks[c1].idx j).map (st.getD c1 0 + ·) := by
  intro c
  induction c using winClaim.induct ks with
  | case1 c h ih =>
    intro hc hn
    rw [winClaim, dite_eq_left h]
    by_cases he : c = c1
    · subst he
      rw [winClaim_none (c + 1) fun c' h' hc' => hn c' h' (by omega) (by omega)]
      cases (ks[c].idx j).map (st.getD c 0 + ·) <;> rfl
    · rw [hn c h (Nat.le_refl _) he, ih (by omega) fun c' h' hc' hne => hn c' h' (by omega) hne]
      rfl
  | case2 c h => intro hc _; omega

/-! ### The window by rank -/

/-- Where chunk `c`'s ranks start. -/
@[expose] def rstartSpec (ks : Array Keys) (r0 : Nat) : Nat → Nat
  | 0 => r0
  | c + 1 => rstartSpec ks r0 c + (ks.getD c default).cnt

theorem rstartsGo_spec (ks : Array Keys) (r0 : Nat) :
    ∀ i a (acc : Array Nat), acc.size = i + 1 → a = rstartSpec ks r0 i →
    (∀ j, j ≤ i → acc.getD j 0 = rstartSpec ks r0 j) → i ≤ ks.size →
    (∀ j, j ≤ ks.size → (rstartsGo ks i a acc).getD j 0 = rstartSpec ks r0 j) := by
  intro i a acc
  induction i, a, acc using rstartsGo.induct ks with
  | case1 i a acc h ih =>
    intro hsz ha hacc hi
    rw [rstartsGo, dite_eq_left h]
    have hnext : a + ks[i].cnt = rstartSpec ks r0 (i + 1) := by
      simp only [rstartSpec, ha, Array.getD_lt h]
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
  | case2 i a acc h =>
    intro hsz ha hacc hi j hj
    rw [rstartsGo, dite_eq_right h]
    exact hacc j (by omega)

theorem rstarts_spec (ks : Array Keys) (r0 : Nat) :
    ∀ c, c ≤ ks.size → (rstarts ks r0).getD c 0 = rstartSpec ks r0 c :=
  rstartsGo_spec ks r0 0 r0 #[r0] rfl rfl (fun j hj => by
    have : j = 0 := by omega
    subst this; rfl) (Nat.zero_le _)

theorem rstartSpec_mono (ks : Array Keys) (r0 : Nat) {a b : Nat} (h : a ≤ b) :
    rstartSpec ks r0 a ≤ rstartSpec ks r0 b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [rstartSpec]; omega

theorem rstartSpec_succ (ks : Array Keys) (r0 : Nat) {c : Nat} (h : c < ks.size) :
    rstartSpec ks r0 (c + 1) = rstartSpec ks r0 c + ks[c].cnt := by
  simp only [rstartSpec, Array.getD_lt h]

theorem Seg.byRank_mono (s : Seg α) (r0 : Nat) (hts : s.tabs.size = s.keys.size) :
    (s.byRank r0).mono := by
  intro c hc
  simp only [Seg.byRank] at hc ⊢
  rw [rstarts_spec _ _ c (by omega), rstarts_spec _ _ (c + 1) (by omega)]
  exact rstartSpec_mono _ _ (Nat.le_succ c)

/-- Rank `k` of chunk `c` in the window by rank is the chunk's slot `k`. -/
theorem Seg.byRank_get {s : Seg α} {r0 : Nat} (hts : s.tabs.size = s.keys.size) {c : Nat}
    (hc : c < s.keys.size) {k : Nat} (hk : k < s.keys[c].cnt) :
    (s.byRank r0).get (rstartSpec s.keys r0 c + k) = s.getAt c k := by
  have hholds : (s.byRank r0).holds c (rstartSpec s.keys r0 c + k) := by
    refine ⟨by simp only [Seg.byRank]; omega, ?_, ?_⟩
    · simp only [Seg.byRank]; rw [rstarts_spec _ _ c (by omega)]; omega
    · simp only [Seg.byRank]
      rw [rstarts_spec _ _ (c + 1) (by omega), rstartSpec_succ _ _ hc]; omega
  rw [Seg.get_holds (Seg.byRank_mono s r0 hts) hholds]
  have hkc : c < (s.byRank r0).keys.size := by simp only [Seg.byRank, Array.size_mapIdx]; omega
  simp only [Seg.atC, dite_eq_left hkc]
  have hK : (s.byRank r0).keys[c] = ⟨rstartSpec s.keys r0 c, s.keys[c].cnt, #[]⟩ := by
    simp only [Seg.byRank, Array.getElem_mapIdx]
    rw [rstarts_spec _ _ c (by omega)]
  rw [hK]
  simp only [Keys.idx, Array.isEmpty_empty, ↓reduceIte]
  rw [ite_eq_left (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rfl

/-! ### The serial parse's tables -/

theorem IdTable.get?_empty (j : Nat) : ({} : IdTable α).get? j = none := by
  simp [IdTable.get?]

theorem findRank_none {rs : List Run} {j : Nat} (h : ∀ x ∈ rs, x.rank j = none) :
    findRank rs j = none := List.findSome?_eq_none_iff.mpr h

theorem Pages.toTable_runGo (P : Pages α) (cut : Nat) (x : Run) (j : Nat) :
    ∀ j0 (t : IdTable α), (Pages.toTable.runGo P cut x j0 t).get? j =
      if j0 ≤ j ∧ j < x.e ∧ j < cut then (P.atRank (x.r + (j - x.i))).or (t.get? j)
      else t.get? j := by
  intro j0 t
  induction j0, t using Pages.toTable.runGo.induct P cut x with
  | case1 j0 t h ih =>
    rw [Pages.toTable.runGo, ite_eq_left h, ih]
    cases hv : P.atRank (x.r + (j0 - x.i)) with
    | none =>
      by_cases hj : j = j0
      · subst hj; rw [ite_eq_right (by omega), ite_eq_left ⟨Nat.le_refl _, h⟩, hv, Option.none_or]
      · by_cases h1 : j0 + 1 ≤ j ∧ j < x.e ∧ j < cut
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    | some v =>
      simp only [IdTable.get?_insert]
      by_cases hj : j = j0
      · subst hj; simp [hv, h]
      · simp only [hj, ↓reduceIte]
        by_cases h1 : j0 + 1 ≤ j ∧ j < x.e ∧ j < cut
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
  | case2 j0 t h =>
    rw [Pages.toTable.runGo, ite_eq_right h, ite_eq_right (by omega)]

/-- **A finished table as the serial parse keeps it** answers its
entries below the cut. -/
theorem Pages.toTable_get? {P : Pages α} {b n : Nat} (h : RunsOK P.runs.toList b n)
    (cut j : Nat) : (P.toTable cut).get? j = if j < cut then P.get j else none := by
  rw [Pages.get_eq h]
  have hpw := List.pairwise_iff_getElem.mp h.1
  have key : ∀ k (t : IdTable α), k ≤ P.runs.size →
      (∀ j, t.get? j = if j < cut then (findRank (P.runs.toList.take k) j).bind P.atRank
        else none) →
      ∀ j, (Pages.toTable.runsGo P cut k t).get? j =
        if j < cut then (findRank P.runs.toList j).bind P.atRank else none := by
    intro k t
    induction k, t using Pages.toTable.runsGo.induct P cut with
    | case1 k t hk ih =>
      intro _ ht
      rw [Pages.toTable.runsGo, dite_eq_left hk]
      apply ih (by omega)
      intro j
      rw [Pages.toTable_runGo, List.take_add_one,
        List.getElem?_eq_getElem (by simpa using hk), Option.toList_some, findRank_snoc]
      simp only [Array.getElem_toList]
      by_cases hin : P.runs[k].i ≤ j ∧ j < P.runs[k].e ∧ j < cut
      · rw [ite_eq_left hin, ht j, ite_eq_left hin.2.2, ite_eq_left hin.2.2]
        have hnone : findRank (P.runs.toList.take k) j = none := by
          apply findRank_none
          intro y hy
          obtain ⟨k', hk', rfl⟩ := List.mem_iff_getElem.mp hy
          have hk'' : k' < k := by simp at hk'; omega
          have := hpw k' k (by simp; omega) (by simpa using hk) hk''
          simp only [List.getElem_take]
          exact Run.rank_none.mpr (by simp only [Array.getElem_toList] at this ⊢; omega)
        rw [hnone]
        simp [Run.rank, hin.1, hin.2.1]
      · rw [ite_eq_right hin, ht j]
        split
        · have : P.runs[k].rank j = none := Run.rank_none.mpr (by omega)
          rw [this, Option.or_none]
        · rfl
    | case2 k t hk =>
      intro hk' ht j
      rw [Pages.toTable.runsGo, dite_eq_right hk, ht j]
      have : k = P.runs.size := by omega
      subst this; rw [List.take_of_length_le (by simp)]
  exact key 0 {} (Nat.zero_le _) (fun j => by simp [findRank, IdTable.get?_empty]) j

/-- **A finished table's invariant**, below index `b`: its runs in
increasing order below `b`, an entry at every rank below its count, a
page for every full page of ranks. -/
structure Pages.Inv (P : Pages α) (b : Nat) : Prop where
  runs : RunsOK P.runs.toList b P.n
  full : ∀ r, r < P.n → (P.atRank r).isSome
  cover : P.n / 4096 ≤ P.pages.size

/-- The finished tables' invariant below the counters. -/
@[expose] def Prior.Inv (P : Prior) (c : Ctr) : Prop := P.n.Inv c.n ∧ P.l.Inv c.l ∧ P.e.Inv c.e

theorem Prior.Inv.sel {P : Prior} {c : Ctr} (h : P.Inv c) (S : Sel α) :
    (S.pages P).Inv (c.at S.tb) := by
  cases S
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem Prior.Inv.ofSel {P : Prior} {c : Ctr}
    (h : ∀ {α : Type} (S : Sel α), (S.pages P).Inv (c.at S.tb)) : P.Inv c :=
  ⟨h .n, h .l, h .e⟩

theorem Prior.toState_holds {P : Prior} {c : Ctr} (h : P.Inv c) (ds : Array Declaration) :
    Holds (P.toState c ds) P.tabs c :=
  ⟨fun j => Pages.toTable_get? h.1.runs c.n j, fun j => Pages.toTable_get? h.2.1.runs c.l j,
   fun j => Pages.toTable_get? h.2.2.runs c.e j⟩

/-! ### The finished tables after a window -/

/-- What the finished tables after a window need of the window's
segment of one table over the indices `[lo, hi)`: monotone starts from
`lo` to `hi`, each chunk's keys increasing within its range, an entry
in every slot. -/
structure SegOK (s : Seg α) (lo hi : Nat) : Prop where
  tabs : s.tabs.size = s.keys.size
  mono : s.mono
  lo : s.starts.getD 0 0 = lo
  hi : s.starts.getD s.keys.size 0 = hi
  keys : ∀ c (h : c < s.keys.size), ∃ l, s.keys[c].Rep l ∧ Incr l ∧
    ∀ k, k < s.keys[c].cnt → s.starts.getD c 0 ≤ s.keys[c].keyOf k ∧
      s.keys[c].keyOf k < s.starts.getD (c + 1) 0
  full : ∀ c (h : c < s.keys.size) k, k < s.keys[c].cnt → (s.getAt c k).isSome

theorem Seg.starts_le {s : Seg α} (hm : s.mono) {a b : Nat} (hab : a ≤ b) (hb : b ≤ s.tabs.size) :
    s.starts.getD a 0 ≤ s.starts.getD b 0 := by
  induction hab with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans (ih (by omega)) (hm _ (by omega))

/-- An index between a segment's first and last start is in some
chunk's range. -/
theorem Seg.exists_holds {s : Seg α} {j : Nat} (hlo : s.starts.getD 0 0 ≤ j)
    (hhi : j < s.starts.getD s.tabs.size 0) : ∃ c, s.holds c j := by
  have key : ∀ d k, k + d = s.tabs.size → s.starts.getD k 0 ≤ j → ∃ c, s.holds c j := by
    intro d
    induction d with
    | zero => intro k hk h; subst hk; omega
    | succ d ih =>
      intro k hk h
      by_cases h' : j < s.starts.getD (k + 1) 0
      · exact ⟨k, by omega, h, h'⟩
      · exact ih (k + 1) (by omega) (by omega)
  exact key s.tabs.size 0 (by omega) hlo

/-- A chunk's keys hold only indices of its range. -/
theorem SegOK.idx_holds {s : Seg α} {lo hi : Nat} (hs : SegOK s lo hi) {c j k : Nat}
    (hc : c < s.keys.size) (h : s.keys[c].idx j = some k) : s.holds c j ∧ k < s.keys[c].cnt ∧
      s.keys[c].keyOf k = j := by
  obtain ⟨hk, hkey⟩ := Keys.idx_sound h
  obtain ⟨l, _, _, hb⟩ := hs.keys c hc
  have := hb k hk
  exact ⟨⟨by rw [hs.tabs]; exact hc, by omega, by omega⟩, hk, hkey⟩

theorem Pages.after_atRank [Inhabited α] {P : Pages α} {s : Seg α} {b : Nat} (hP : P.Inv b)
    (hts : s.tabs.size = s.keys.size) {NN : Array (Array α)}
    (hsz : NN.size = pagesCount P.n (s.rEnd P.n))
    (hN : ∀ i (h : i < NN.size),
      NN[i] = pageOf P (s.byRank P.n) P.n (s.rEnd P.n) (pagesFrom P.n + i)) (r : Nat) :
    (P.after s NN).atRank r = if r < P.n then P.atRank r else if r < s.rEnd P.n then
      some (((s.byRank P.n).get r).getD default) else none := by
  have hnE : P.n ≤ s.rEnd P.n := by
    have := rstartSpec_mono s.keys P.n (Nat.zero_le s.keys.size)
    simp only [Seg.rEnd, rstarts_spec _ _ _ (Nat.le_refl _)]; simpa [rstartSpec] using this
  have hcov := hP.cover
  rw [Pages.atRank_eq]
  simp only [Pages.after]
  have hext : (P.pages.extract 0 (P.n / 4096)).size = P.n / 4096 := by simp; omega
  by_cases hp : r / 4096 < P.n / 4096
  · rw [Array.getElem?_append_left (by omega)]
    rw [ite_eq_left (by omega), Pages.atRank_eq]
    simp [show r / 4096 < min (P.n / 4096) P.pages.size by omega,
      Array.getElem?_eq_getElem (show r / 4096 < P.pages.size by omega)]
  · rw [Array.getElem?_append_right (by omega), hext]
    by_cases hin : r / 4096 - P.n / 4096 < NN.size
    · rw [Array.getElem?_eq_getElem hin, Option.bind_some, hN _ hin]
      simp only [pagesFrom]
      rw [show P.n / 4096 + (r / 4096 - P.n / 4096) = r / 4096 by omega,
        pageOf_spec P _ (Seg.byRank_mono s P.n hts) _ _ _ hnE (Nat.mod_lt _ (by decide)),
        Nat.div_add_mod' r 4096]
      simp only [rankView]
      by_cases h1 : r < P.n
      · have hs := hP.full r h1
        rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_left h1]
        cases hx : P.atRank r with
        | none => rw [hx] at hs; cases hs
        | some x => rfl
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : r < s.rEnd P.n
        · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_left h2]
        · rw [ite_eq_right h2, ite_eq_right h2]
    · rw [Array.getElem?_eq_none (by omega), Option.bind_none]
      rw [hsz] at hin
      simp only [pagesCount] at hin
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **The finished tables after a window** keep their invariant and
answer, at every index, the window's view: the tables before below its
start, its own entries in it, nothing above. -/
theorem Pages.after_spec [Inhabited α] {P : Pages α} {s : Seg α} {lo hi : Nat}
    (hP : P.Inv lo) (hs : SegOK s lo hi) {NN : Array (Array α)}
    (hsz : NN.size = pagesCount P.n (s.rEnd P.n))
    (hN : ∀ i (h : i < NN.size),
      NN[i] = pageOf P (s.byRank P.n) P.n (s.rEnd P.n) (pagesFrom P.n + i)) :
    (P.after s NN).Inv hi ∧ ∀ j, (P.after s NN).get j = pageView P s lo hi j := by
  have hst : ∀ c, c ≤ s.keys.size → (rstarts s.keys P.n).getD c 0 = rstartSpec s.keys P.n c :=
    rstarts_spec _ _
  have hlh : lo ≤ hi := by
    rw [← hs.lo, ← hs.hi]; exact Seg.starts_le hs.mono (Nat.zero_le _) (Nat.le_of_eq hs.tabs.symm)
  obtain ⟨hr1, hr2⟩ := winRunsGo_spec s.keys (rstarts s.keys P.n) (fun c => s.starts.getD c 0)
    hs.keys (fun c hc => hs.mono c (by rw [hs.tabs]; exact hc))
    (fun c hc => by rw [hst _ hc, hst _ (by omega), rstartSpec_succ _ _ hc])
    0 P.runs (Nat.zero_le _) (by rw [hs.lo, hst 0 (Nat.zero_le _)]; exact hP.runs)
  simp only [hs.hi] at hr1
  have hrE : (P.after s NN).runs = winRunsGo s.keys (rstarts s.keys P.n) 0 P.runs := rfl
  have hnE' : (P.after s NN).n = s.rEnd P.n := rfl
  have hat := Pages.after_atRank hP hs.tabs hsz hN
  have hnE : P.n ≤ s.rEnd P.n := by
    have := rstartSpec_mono s.keys P.n (Nat.zero_le s.keys.size)
    simp only [Seg.rEnd, hst _ (Nat.le_refl _)]; simpa [rstartSpec] using this
  have hOK : RunsOK (P.after s NN).runs.toList hi (P.after s NN).n := by
    rw [hrE, hnE']; exact hr1
  refine ⟨⟨hOK, fun r hr => ?_, ?_⟩, fun j => ?_⟩
  · rw [hat]
    split
    · exact hP.full r ‹_›
    · rw [hnE'] at hr; rw [ite_eq_left hr]; rfl
  · have := hP.cover
    simp only [Seg.rEnd] at hnE
    simp only [Pages.after, Array.size_append, Array.size_extract, hsz, pagesCount, Seg.rEnd]
    omega
  · rw [Pages.get_eq hOK, hrE, hr2 j]
    -- the runs before hold indices below `lo` only, at ranks below their count
    have hold : ∀ r, findRank P.runs.toList j = some r → j < lo ∧ r < P.n := by
      intro r hr
      obtain ⟨x, hx, hxr⟩ := List.exists_of_findSome?_eq_some hr
      have := hP.runs.2 x hx
      have := Run.rank_some.mp hxr
      omega
    have holdNone : lo ≤ j → findRank P.runs.toList j = none := by
      intro hj
      cases h : findRank P.runs.toList j with
      | none => rfl
      | some r => have := hold r h; omega
    have hwinNone : (j < lo ∨ hi ≤ j) → winClaim s.keys (rstarts s.keys P.n) j 0 = none := by
      intro hj
      apply winClaim_none
      intro c' hc' _
      cases h : s.keys[c'].idx j with
      | none => rfl
      | some k =>
        obtain ⟨⟨h1, h2, h3⟩, _⟩ := hs.idx_holds hc' h
        have := Seg.starts_le hs.mono (Nat.zero_le c') (by omega)
        have := Seg.starts_le hs.mono (show c' + 1 ≤ s.keys.size by omega) (Nat.le_of_eq hs.tabs.symm)
        rw [hs.lo] at *; rw [hs.hi] at *
        omega
    unfold pageView
    by_cases hj1 : j < lo
    · rw [ite_eq_left hj1, hwinNone (Or.inl hj1), Option.or_none, Pages.get_eq hP.runs]
      cases h : findRank P.runs.toList j with
      | none => rfl
      | some r =>
        simp only [Option.bind_some]
        rw [hat, ite_eq_left (hold r h).2]
    · rw [ite_eq_right hj1, holdNone (by omega), Option.none_or]
      by_cases hj2 : j < hi
      · rw [ite_eq_left hj2]
        obtain ⟨c, hc⟩ := Seg.exists_holds (s := s) (j := j) (by rw [hs.lo]; omega)
          (by rw [hs.tabs, hs.hi]; exact hj2)
        have hck : c < s.keys.size := by rw [← hs.tabs]; exact hc.1
        rw [winClaim_one hck 0 (Nat.zero_le _) (fun c' hc' _ hne => by
          cases h : s.keys[c'].idx j with
          | none => rfl
          | some k => exact absurd (Seg.holds_unique hs.mono (hs.idx_holds hc' h).1 hc) hne),
          Seg.get_holds hs.mono hc]
        simp only [Seg.atC, dite_eq_left hck]
        cases h : s.keys[c].idx j with
        | none => rfl
        | some k =>
          obtain ⟨_, hk, _⟩ := hs.idx_holds hck h
          simp only [Option.map_some, Option.bind_some]
          have h1 := rstartSpec_mono s.keys P.n (Nat.zero_le c)
          have h2 := rstartSpec_mono s.keys P.n (show c + 1 ≤ s.keys.size by omega)
          rw [rstartSpec_succ _ _ hck] at h2
          simp only [rstartSpec] at h1
          rw [hst c (by omega), hat, ite_eq_right (by omega),
            ite_eq_left (by simp only [Seg.rEnd, hst _ (Nat.le_refl _)]; omega),
            Seg.byRank_get hs.tabs hck hk]
          have hf := hs.full c hck k hk
          cases hx : s.getAt c k with
          | none => rw [hx] at hf; cases hf
          | some x => rfl
      · rw [ite_eq_right hj2, hwinNone (Or.inr (by omega))]
        rfl

/-! ## The invariant between windows -/

/-- **The rounds parse's invariant**: some state the serial parse
reaches after the lines so far, with nothing carried, holds the
finished tables cut at the counters, with the records so far; the
finished tables keep their own invariant. -/
def GOK (g : GSt) : Prop :=
  ∃ st, Reached st .empty g.lineNo g.total ∧ Holds st g.P.tabs g.c ∧ st.decls = g.ds ∧
    g.P.Inv g.c

theorem Prior.init_inv : Prior.init.Inv GSt.init.c := by
  refine ⟨⟨?_, ?_, by decide⟩, ⟨?_, ?_, by decide⟩, ⟨RunsOK.nil _ _, by simp [Prior.init], by
    decide⟩⟩
  · exact ⟨by simp [Prior.init], by simp [Prior.init, GSt.init]⟩
  · intro r hr; simp [Prior.init] at hr; subst hr; simp [Pages.atRank_eq, Prior.init]
  · exact ⟨by simp [Prior.init], by simp [Prior.init, GSt.init]⟩
  · intro r hr; simp [Prior.init] at hr; subst hr; simp [Pages.atRank_eq, Prior.init]

theorem GOK.init : GOK GSt.init := by
  have hi := Prior.init_inv
  refine ⟨.init, Reached.init, ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩, rfl, hi⟩
  · simp only [StateD.init, IdTable.get?_singleton, GSt.init, Prior.tabs,
      Pages.get_eq hi.1.runs]
    rcases j with _ | j
    · simp [Prior.init, findRank, Run.rank, Pages.atRank_eq]
    · simp
  · simp only [StateD.init, IdTable.get?_singleton, GSt.init, Prior.tabs,
      Pages.get_eq hi.2.1.runs]
    rcases j with _ | j
    · simp [Prior.init, findRank, Run.rank, Pages.atRank_eq]
    · simp
  · simp [StateD.init, IdTable.get?_empty, GSt.init]

/-- The state a window that falls back continues the serial parse
from. -/
theorem GOK.reached {g : GSt} (h : GOK g) :
    Reached (g.P.toState g.c g.ds) .empty g.lineNo g.total := by
  obtain ⟨st, hr, hh, hd, hi⟩ := h
  exact hr.equiv (Holds.equiv hh (Prior.toState_holds hi g.ds) (by rw [hd]; rfl))

/-- The end of the stream: the records so far are the parse's. -/
theorem GOK.finish {g : GSt} (h : GOK g) : ∃ cs, parseChunks cs = .ok ⟨g.ds⟩ := by
  obtain ⟨st, hr, _, hd, -⟩ := h
  obtain ⟨cs, hcs⟩ := hr.finish
  refine ⟨cs, ?_⟩
  rw [hcs, chunkFinish, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl)]
  simp [ParseResultD.ofState, hd]

/-! ## A window, applied -/

/-- What the finish of a window yields for one chunk: its slices of the
pages. -/
structure FinPart where
  pn : Array (Array Name)
  pl : Array (Array Level)
  pe : Array (Array Expr)
  ds : Array Declaration
  deriving Inhabited

/-- Chunk `c`'s part of a window's finish (of `m` parts, the chunk's
bytes `b`), as it must be: the `c`-th slice of each table's pages, the
chunk's scan ended at its end, its late entries all done, and its
records. -/
@[expose] def FinOK (P : Prior) (W : Win) (m c : Nat) (b : ByteArray) (x : FinPart) : Prop :=
  x.pn = finSlice P.n W.n m c ∧ x.pl = finSlice P.l W.l m c ∧ x.pe = finSlice P.e W.e m c ∧
  scanEnds b (scanChunk b) = true ∧ W.fullAt c = true ∧ chunkDecls P W c (recsOf b) = some x.ds

/-- The parts joined. -/
def joinN (ps : Array FinPart) : Array (Array Name) := ps.foldl (fun a x => a ++ x.pn) #[]
def joinL (ps : Array FinPart) : Array (Array Level) := ps.foldl (fun a x => a ++ x.pl) #[]
def joinE (ps : Array FinPart) : Array (Array Expr) := ps.foldl (fun a x => a ++ x.pe) #[]
def joinD (ps : Array FinPart) : Array Declaration := ps.foldl (fun a x => a ++ x.ds) #[]

/-! ### The pages, joined -/

theorem pagesSlice_go_spec [Inhabited α] (P : Pages α) (s : Seg α) (lo hi b : Nat) :
    ∀ p (acc : Array (Array α)), (∀ i (h : i < acc.size), acc[i] = pageOf P s lo hi (p - acc.size + i)) →
    acc.size ≤ p →
    (pagesSlice.go P s lo hi b p acc).size = acc.size + (b - p) ∧
    ∀ i (h : i < (pagesSlice.go P s lo hi b p acc).size),
      (pagesSlice.go P s lo hi b p acc)[i] = pageOf P s lo hi (p - acc.size + i) := by
  intro p acc
  induction p, acc using pagesSlice.go.induct P s lo hi b with
  | case1 p acc h ih =>
    intro hacc hle
    rw [pagesSlice.go, ite_eq_left h]
    have := ih (fun i hi => by
        rw [Array.getElem_push]
        split
        · rename_i hi'; rw [hacc i hi']; congr 1; simp only [Array.size_push]; omega
        · have : i = acc.size := by simp at hi; omega
          subst this; congr 1; simp only [Array.size_push]; omega) (by simp; omega)
    obtain ⟨h1, h2⟩ := this
    refine ⟨by rw [h1]; simp only [Array.size_push]; omega, fun i hi => ?_⟩
    rw [h2 i hi]; congr 1; simp only [Array.size_push]; omega
  | case2 p acc h =>
    intro hacc hle
    rw [pagesSlice.go, ite_eq_right h]
    exact ⟨by omega, hacc⟩

theorem pagesSlice_spec [Inhabited α] (P : Pages α) (s : Seg α) (lo hi a b : Nat) :
    (pagesSlice P s lo hi a b).size = b - a ∧
    ∀ i (h : i < (pagesSlice P s lo hi a b).size),
      (pagesSlice P s lo hi a b)[i] = pageOf P s lo hi (a + i) := by
  have := pagesSlice_go_spec P s lo hi b a (Array.mkEmpty (b - a))
    (fun i h => by simp at h) (by simp)
  unfold pagesSlice
  simpa using this

theorem slice_mono {cnt m j : Nat} : j * cnt / m ≤ (j + 1) * cnt / m :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ j))

/-- **The slices of the pages, joined**: every page from the window's
first, in order. -/
theorem join_spec [Inhabited α] (P : Pages α) (s : Seg α) (lo hi : Nat) (ps : Array FinPart)
    (f : FinPart → Array (Array α)) (hm : 0 < ps.size)
    (hps : ∀ c (h : c < ps.size), f ps[c] = pagesSlice P s lo hi
      (slice (pagesFrom lo) (pagesCount lo hi) ps.size c).1
      (slice (pagesFrom lo) (pagesCount lo hi) ps.size c).2) :
    (ps.foldl (fun a x => a ++ f x) #[]).size = pagesCount lo hi ∧
    ∀ i (h : i < (ps.foldl (fun a x => a ++ f x) #[]).size),
      (ps.foldl (fun a x => a ++ f x) #[])[i] = pageOf P s lo hi (pagesFrom lo + i) := by
  have key : ∀ k, k ≤ ps.size →
      ((ps.toList.take k).foldl (fun a x => a ++ f x) #[]).size =
        k * pagesCount lo hi / ps.size ∧
      ∀ i (h : i < ((ps.toList.take k).foldl (fun a x => a ++ f x) #[]).size),
        ((ps.toList.take k).foldl (fun a x => a ++ f x) #[])[i] =
          pageOf P s lo hi (pagesFrom lo + i) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨i1, i2⟩ := ih (by omega)
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega), Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hs := pagesSlice_spec P s lo hi
        (slice (pagesFrom lo) (pagesCount lo hi) ps.size k).1
        (slice (pagesFrom lo) (pagesCount lo hi) ps.size k).2
      have hf := hps k (by omega)
      simp only [Array.getElem_toList] at hf ⊢
      obtain ⟨s1, s2⟩ := hs
      simp only [slice] at s1 s2 hf
      have s1' : (f ps[k]).size = pagesFrom lo + (k + 1) * pagesCount lo hi / ps.size -
          (pagesFrom lo + k * pagesCount lo hi / ps.size) := by rw [hf]; exact s1
      have s2' : ∀ i (h : i < (f ps[k]).size), (f ps[k])[i] = pageOf P s lo hi
          (pagesFrom lo + k * pagesCount lo hi / ps.size + i) := by
        intro i h
        have h' : i < (pagesSlice P s lo hi (pagesFrom lo + k * pagesCount lo hi / ps.size)
            (pagesFrom lo + (k + 1) * pagesCount lo hi / ps.size)).size := by rw [← hf]; exact h
        have := s2 i h'
        simp only [hf]; exact this
      have hmono := slice_mono (cnt := pagesCount lo hi) (m := ps.size) (j := k)
      refine ⟨by rw [Array.size_append, i1, s1']; omega, fun i hi => ?_⟩
      rw [Array.getElem_append]
      split
      · rename_i hi'; exact i2 i hi'
      · rename_i hi'
        rw [s2']; congr 1; rw [i1] at hi'; omega
  have := key ps.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp), Array.foldl_toList] at this
  rw [Nat.mul_div_cancel_left _ hm] at this
  exact this

/-- With every late entry done, a chunk table holds an entry in every
slot. -/
theorem TB.get_full {P : Prior} {c0 : Ctr} {recs : Array LineRec} {tb : Tb} {inj : α → TV}
    {t : TB α} (hT : t.I P c0 recs tb inj recs.size) {Γ : WCtx} {lv : Array α} {ld : ByteArray}
    (hL : LateOK Γ inj t lv ld) (hfull : ld.size == lv.size && ld.data.all (· == 1))
    {k : Nat} (hk : k < t.d.size) : (t.get lv ld k).isSome := by
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at hfull
  simp only [TB.get, slotGet, hk, ↓reduceDIte]
  split
  · rename_i hl
    have hl' : byteN t.late k = 1 := beq_iff_eq.mp hl
    have hs := hT.lsLt k hk hl'
    have hs1 : t.ls.getD k 0 < ld.size := by rw [hL.ldsz]; exact hs
    have hs2 : t.ls.getD k 0 < lv.size := by rw [hL.lvsz]; exact hs
    simp only [lateVal]
    have hb : byteN ld (t.ls.getD k 0) = 1 := by
      rw [byteN_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs1]
      exact hfull.2 _ hs1
    rw [ite_eq_left (beq_iff_eq.mpr hb), dite_eq_left hs2]
    rfl
  · rfl

/-- **The tables after a window are good**: given the window
invariant, every late entry done, and the tables after the window
answering the window's view. -/
theorem window_goodTabs {P : Prior} {bs : List ByteArray} {W : Win} (hW : WinInv P bs W)
    (hfull : ∀ c, c < bs.length → W.fullAt c = true) {P' : Prior}
    (hv : ∀ {α : Type} (S : Sel α) j,
      (S.pages P').get j = pageView (S.pages P) (S.seg W) (W.c0.at S.tb) (W.cEnd.at S.tb) j) :
    GoodTabs (winCtx P W.c0 bs) P'.tabs := by
  have hinc := hW.inc
  have hcE := hW.cEnd
  -- the window's ends, as counters of its lines
  have hend : ∀ t, (W.cEnd).at t = ((winCtx P W.c0 bs).ctr (chunkRecs bs).length).at t := by
    intro t; rw [hcE]; simp [WCtx.ctr, ctrAt, winCtx]
  have hstart : ∀ t, W.c0.at t = ((winCtx P W.c0 bs).ctr 0).at t := by
    intro t; simp [WCtx.ctr, ctrAt_zero, winCtx]
  -- a line's index lies in its chunk's range, inside the window
  have hrange : ∀ (t : Tb) p (hp : p < (chunkRecs bs).length) i,
      (chunkRecs bs)[p].idAt t = some i →
      ∃ c q, ∃ (hc : c < bs.length) (hq : q < (recsOf bs[c]).size),
        p = chunkOff bs c + q ∧ (recsOf bs[c])[q].idAt t = some i ∧
        ((winCtx P W.c0 bs).ctr (chunkOff bs c)).at t ≤ i ∧
        i < ((winCtx P W.c0 bs).ctr (chunkOff bs (c + 1))).at t ∧
        W.c0.at t ≤ i ∧ i < W.cEnd.at t := by
    intro t p hp i hi
    obtain ⟨c, q, hc, hq, rfl⟩ := chunk_of_pos bs _ hp
    have hE := winCtx_emb P W.c0 bs hc
    have hrq : (chunkRecs bs)[chunkOff bs c + q] = (recsOf bs[c])[q] := by
      have := hE.2.2.2 q hq
      simp only [winCtx] at this
      rw [List.getElem?_eq_getElem hp] at this; exact Option.some.inj this
    rw [hrq] at hi
    have hb := hinc.bind (rs := chunkRecs bs) hp (by rw [hrq]; exact hi)
    have m1 := ctrAt_mono hinc (Nat.le_add_right (chunkOff bs c) q) t
    have m2 := ctrAt_mono hinc (show chunkOff bs c + q + 1 ≤ chunkOff bs (c + 1) by
      rw [chunkOff_succ bs hc]; omega) t
    have m3 := ctrAt_mono hinc (Nat.zero_le (chunkOff bs c)) t
    have m4 := ctrAt_mono hinc (show chunkOff bs (c + 1) ≤ (chunkRecs bs).length by
      rw [← chunkOff_length]; exact chunkOff_mono bs (by omega)) t
    have e1 := hend t
    have e0 := hstart t
    simp only [WCtx.ctr, winCtx] at e1 e0 ⊢
    exact ⟨c, q, hc, hq, rfl, hi, by omega, by omega, by omega, by omega⟩
  -- a table's slot after the window, as the window's view
  have hat : ∀ {α : Type} (S : Sel α) j, P'.tabs.at S.tb j =
      (pageView (S.pages P) (S.seg W) (W.c0.at S.tb) (W.cEnd.at S.tb) j).map S.inj := by
    intro α S j; rw [S.at, S.prior_tab, hv]
  refine ⟨hinc, fun t j hj => ?_, fun t j v hj hx => ?_, fun t p hp i hi => ?_⟩ <;>
    obtain ⟨_, S, rfl⟩ := t.exSel
  · rw [hat, S.at, S.prior_tab]
    simp [pageView, show j < W.c0.at S.tb from hj]
    rfl
  · rw [hat] at hx
    obtain ⟨x, hx', rfl⟩ := Option.map_eq_some_iff.mp hx
    simp only [pageView, show ¬ j < W.c0.at S.tb by simpa [winCtx] using Nat.not_lt.mpr hj,
      ↓reduceIte] at hx'
    split at hx'
    · obtain ⟨e, he⟩ := Seg.get_some hx'
      obtain ⟨K, k, hK, hk, hg⟩ := Seg.atC_some he
      obtain ⟨K', hK', hgood⟩ := hW.store S e k x hg
      rw [hK] at hK'; cases hK'
      rwa [(Keys.idx_sound hk).2] at hgood
    · cases hx'
  · obtain ⟨c, q, hc, hq, rfl, hiq, h1, h2, h3, h4⟩ := hrange S.tb p hp i hi
    rw [hat, Option.isSome_map]
    simp only [pageView, show ¬ i < W.c0.at S.tb by omega, show i < W.cEnd.at S.tb by omega,
      ↓reduceIte]
    obtain ⟨⟨T, hT, t1, t2, t3, hL⟩, hK⟩ := (hW.tabAt S hc).1
    have hspec := hW.specS S hc
    have hholds : (S.seg W).holds c i := by
      refine ⟨by rw [hW.tabsSize S, hW.1]; exact hc, ?_, ?_⟩
      · rw [hW.starts S c (by omega)]; exact h1
      · rw [hW.starts S (c + 1) (by omega)]; exact h2
    rw [Seg.get_holds (hW.mono S) hholds]
    obtain ⟨hkd, hkey⟩ := TBI.key_line hspec hq hiq
    have hidx := Keys.idx_complete (TBI.rep hspec) (TBI.incr' hspec)
      (k := (idsT S.tb ((recsOf bs[c]).toList.take q)).length) (by
        show _ < (S.r0 (round0 P W.c0 c (recsOf bs[c]))).d.size; exact hkd)
    rw [hkey] at hidx
    simp only [Seg.atC, Array.getElem?_eq_some_iff.mp hK |>.1, ↓reduceDIte]
    have hK' : (S.seg W).keys[c]'(Array.getElem?_eq_some_iff.mp hK).1 =
        (S.r0 (round0 P W.c0 c (recsOf bs[c]))).keys := (Array.getElem?_eq_some_iff.mp hK).2
    rw [hK', hidx]
    simp only [Seg.getAt_eq, hT, Option.bind_some, CTab.get]
    rw [t1, t2, t3]
    have hfT : T.ldone.size == T.lv.size && T.ldone.data.all (· == 1) := by
      have hf := hfull c hc
      simp only [Win.fullAt, Bool.and_eq_true] at hf
      cases S <;> simp only [Sel.seg] at hT
      · have := hf.1.1; rw [getD_of_some hT] at this; exact this
      · have := hf.1.2; rw [getD_of_some hT] at this; exact this
      · have := hf.2; rw [getD_of_some hT] at this; exact this
    exact TB.get_full hspec hL hfT hkd

theorem AllOK.split {T : Tabs} :
    ∀ {c : Ctr} {l₁ l₂ : List LineRec}, AllOK T c (l₁ ++ l₂) →
    AllOK T c l₁ ∧ AllOK T (c.stepAll l₁) l₂ := by
  intro c l₁ l₂ h
  induction l₁ generalizing c with
  | nil => exact ⟨trivial, h⟩
  | cons r l ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨i1, i2⟩ := ih h2
    exact ⟨⟨h1, i1⟩, i2⟩

theorem ByteArray.extract_size_self (b : ByteArray) : b.extract b.size b.size = .empty := by
  ext1; simp [ByteArray.empty, ByteArray.emptyWithCapacity]

/-- **A chunk whose lines are right is one more serial step.** -/
theorem chunkStep_of_allOK {st : StateD} {T : Tabs} {c : Ctr} {n tot : Nat} {b : ByteArray}
    (hh : Holds st T c) (hok : AllOK T c (recsOf b).toList)
    (hend : scanEnds b (scanChunk b) = true) (htot : tot + b.size < USize.size) :
    ∃ st', chunkStep st .empty n tot b = .ok (st', .empty, n + (recsOf b).size, tot + b.size) ∧
      Holds st' T (c.stepAll (recsOf b).toList) ∧
      st'.decls = declsAlong T c (recsOf b).toList st.decls := by
  obtain ⟨st', happ, hh', hd'⟩ := applyList_of_allOK T c (recsOf b).toList st n hok hh
  simp only [scanEnds] at hend
  split at hend
  · rename_i i hstop
    simp only [beq_iff_eq] at hend
    refine ⟨st', ?_, hh', hd'⟩
    rw [← chunkStepS_scanChunk]
    rw [chunkStepS, ite_eq_left (show ByteArray.empty.isEmpty = true by rfl),
      ite_eq_right (show ¬ (tot + b.size ≥ USize.size) by omega)]
    simp only [recsOf] at happ
    rw [applyScanned, applyRecs_eq, List.drop_zero, happ, hstop]
    simp only [Array.length_toList, hend, ByteArray.extract_size_self, recsOf]
  · simp at hend

/-- The bytes of the window's first `k` chunks. -/
@[expose] def byteOff (bs : List ByteArray) (k : Nat) : Nat := ((bs.take k).map ByteArray.size).sum

theorem byteOff_succ (bs : List ByteArray) {c : Nat} (h : c < bs.length) :
    byteOff bs (c + 1) = byteOff bs c + bs[c].size := by
  simp only [byteOff, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero]

theorem byteOff_le (bs : List ByteArray) (k : Nat) : byteOff bs k ≤ (bs.map ByteArray.size).sum := by
  simp only [byteOff]
  induction bs generalizing k with
  | nil => simp
  | cons b bs ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; have := ih k; omega

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

theorem joinD_take (ps : Array FinPart) (k : Nat) (hk : k < ps.size) :
    (ps.toList.take (k + 1)).foldl (fun a x => a ++ x.ds) #[] =
      (ps.toList.take k).foldl (fun a x => a ++ x.ds) #[] ++ ps[k].ds := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk), Option.toList_some,
    List.foldl_append]
  simp

/-- A chunk's slice of a table's pages. -/
@[expose] def Sel.part : Sel α → FinPart → Array (Array α)
  | .n => FinPart.pn
  | .l => FinPart.pl
  | .e => FinPart.pe

/-- A table's slices, joined. -/
@[expose] def Sel.join (S : Sel α) (ps : Array FinPart) : Array (Array α) :=
  ps.foldl (fun a x => a ++ S.part x) #[]

theorem Sel.pages_setFrom (S : Sel α) (P : Prior) (W : Win) (ps : Array FinPart) :
    S.pages (P.setFrom W (joinN ps) (joinL ps) (joinE ps)) =
      (S.pages P).after (S.seg W) (S.join ps) := by
  cases S <;> rfl

theorem FinOK.sel {P : Prior} {W : Win} {m c : Nat} {b : ByteArray} {x : FinPart}
    (h : FinOK P W m c b x) (S : Sel α) :
    letI := S.inh
    S.part x = finSlice (S.pages P) (S.seg W) m c := by
  cases S
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

/-- **A window's segment of a table, complete**: what the finished
tables after it need (`SegOK`). -/
theorem WinInv.segOK {P : Prior} {bs : List ByteArray} {W : Win} (hW : WinInv P bs W)
    (hfull : ∀ c, c < bs.length → W.fullAt c = true) (S : Sel α) :
    SegOK (S.seg W) (W.c0.at S.tb) (W.cEnd.at S.tb) := by
  have hks := hW.keysSize S
  have hts := hW.tabsSize S
  have hn : W.nc = bs.length := hW.1
  -- chunk `c`'s keys are round 0's
  have hkey : ∀ c (hb : c < bs.length) (h : c < (S.seg W).keys.size), (S.seg W).keys[c] =
      (S.r0 (round0 P W.c0 c (recsOf bs[c]))).keys := fun c hb h => by
    have := (hW.tabAt S hb).1.2
    rw [Array.getElem?_eq_getElem h] at this; exact Option.some.inj this
  have hsp : ∀ c, c ≤ (S.seg W).keys.size →
      (S.seg W).starts.getD c 0 = startsSpec (S.seg W).keys (W.c0.at S.tb) c := by
    intro c hc
    rw [hW.startsEq S]
    exact startsGo_spec _ (W.c0.at S.tb) 0 _ #[W.c0.at S.tb] rfl rfl
      (fun j hj => by have : j = 0 := by omega
                      subst this; rfl) (Nat.zero_le _) c hc
  refine ⟨by rw [hts, hks], hW.mono S, by rw [hsp 0 (Nat.zero_le _)]; rfl, ?_, ?_, ?_⟩
  · rw [hks]; cases S <;> rfl
  · intro c hc
    have hcb : c < bs.length := by omega
    have hspec := hW.specS S hcb
    rw [hkey c hcb hc]
    refine ⟨_, TBI.rep hspec, TBI.incr' hspec, fun k hk => ?_⟩
    have hrep := TBI.rep hspec
    have hinc := TBI.incr' hspec
    have hlen := hrep.1
    have hfirst := firstOK_head (hW.tabAt S hcb).2 (hW.tabAt S hcb).1.2 hspec
    refine ⟨?_, ?_⟩
    · rw [keyOf_of_shape hrep.2 k (by omega)]
      have h0 := hfirst _ (List.head?_eq_getElem?.trans
        (List.getElem?_eq_getElem (by omega)))
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; exact h0
      · have := List.pairwise_iff_getElem.mp hinc 0 k (by omega) (by omega) h
        omega
    · rw [hsp (c + 1) (by omega), startsSpec_succ _ _ hc, hkey c hcb hc]
      rw [ite_eq_right (by simp only [beq_iff_eq]; omega)]
      rcases Nat.lt_or_ge k ((S.r0 (round0 P W.c0 c (recsOf bs[c]))).keys.cnt - 1) with h | h
      · have := Keys.keyOf_lt hrep hinc h (by omega); omega
      · have : k = (S.r0 (round0 P W.c0 c (recsOf bs[c]))).keys.cnt - 1 := by omega
        rw [this]; omega
  · intro c hc k hk
    have hcb : c < bs.length := by omega
    have hspec := hW.specS S hcb
    obtain ⟨⟨T, hT, t1, t2, t3, hL⟩, _⟩ := (hW.tabAt S hcb).1
    rw [hkey c hcb hc] at hk
    simp only [Seg.getAt_eq, hT, Option.bind_some, CTab.get]
    rw [t1, t2, t3]
    have hfT : T.ldone.size == T.lv.size && T.ldone.data.all (· == 1) := by
      have hf := hfull c hcb
      simp only [Win.fullAt, Bool.and_eq_true] at hf
      cases S <;> simp only [Sel.seg] at hT
      · have := hf.1.1; rw [getD_of_some hT] at this; exact this
      · have := hf.1.2; rw [getD_of_some hT] at this; exact this
      · have := hf.2; rw [getD_of_some hT] at this; exact this
    exact TB.get_full hspec hL hfT hk

/-- **A window is one more stretch of the serial parse.** -/
theorem GOK.window {g : GSt} (hg : GOK g) {bs : List ByteArray} {W : Win}
    (hW : WinInv g.P bs W) (hc0 : W.c0 = g.c)
    {ps : Array FinPart} (hm : ps.size = bs.length) (hb : 0 < bs.length)
    (hps : ∀ c (h : c < ps.size) (hb : c < bs.length), FinOK g.P W ps.size c bs[c] ps[c])
    (htot : g.total + (bs.map ByteArray.size).sum < USize.size) :
    GOK ⟨g.P.setFrom W (joinN ps) (joinL ps) (joinE ps), W.cEnd, g.ds ++ joinD ps,
      g.lineNo + (bs.map fun b => (recsOf b).size).sum,
      g.total + (bs.map ByteArray.size).sum⟩ := by
  obtain ⟨st0, hr0, hh0, hd0, hcov⟩ := hg
  have hcE := hW.cEnd
  have hsz : ps.size = W.nc := by rw [hm, hW.1]
  rw [← hc0] at hcov
  -- the window's counters only grow
  have hctrE : ∀ q t, ((winCtx g.P W.c0 bs).ctr q).at t ≤ W.cEnd.at t := by
    intro q t
    rcases Nat.lt_or_ge q (chunkRecs bs).length with hq | hq
    · have := hW.ctr_mono (Nat.le_of_lt hq) t
      rw [hcE]; simpa [WCtx.ctr, ctrAt, winCtx] using this
    · rw [hcE]
      simp [WCtx.ctr, ctrAt, winCtx, List.take_of_length_le hq]
  have hlh : ∀ t, W.c0.at t ≤ W.cEnd.at t := fun t => by
    simpa [WCtx.ctr, ctrAt, winCtx, Ctr.stepAll] using hctrE 0 t
  have hfull : ∀ c, c < bs.length → W.fullAt c = true := fun c h =>
    (hps c (by omega) h).2.2.2.2.1
  -- the pages, joined, and the finished tables after the window
  have hA : ∀ {α : Type} (S : Sel α), letI := S.inh
      ((S.pages g.P).after (S.seg W) (S.join ps)).Inv (W.cEnd.at S.tb) ∧
      ∀ j, ((S.pages g.P).after (S.seg W) (S.join ps)).get j =
        pageView (S.pages g.P) (S.seg W) (W.c0.at S.tb) (W.cEnd.at S.tb) j := by
    intro α S
    letI := S.inh
    have hj := join_spec (S.pages g.P) ((S.seg W).byRank (S.pages g.P).n) (S.pages g.P).n
      ((S.seg W).rEnd (S.pages g.P).n) ps S.part (by omega) (fun c h => (hps c h (by omega)).sel S)
    exact Pages.after_spec (hcov.sel S) (hW.segOK hfull S) hj.1 hj.2
  have hv : ∀ {α : Type} (S : Sel α) j,
      (S.pages (g.P.setFrom W (joinN ps) (joinL ps) (joinE ps))).get j =
        pageView (S.pages g.P) (S.seg W) (W.c0.at S.tb) (W.cEnd.at S.tb) j := by
    intro α S j
    rw [S.pages_setFrom]
    exact (hA S).2 j
  have hGT := window_goodTabs hW hfull hv
  -- the tables below each line of the window are the window's view
  have hV : ∀ c (hc : c < bs.length), ViewBelow (winCtx g.P W.c0 bs) g.P W (chunkOff bs c)
      (recsOf bs[c]).size (g.P.setFrom W (joinN ps) (joinL ps) (joinE ps)).tabs := by
    intro c hc q hq α S j hj
    rw [S.prior_tab, hv]; simp only [pageView]; split
    · rfl
    · rw [ite_eq_left (by have := hctrE (chunkOff bs c + q) S.tb; omega)]
  have hDs : ∀ c (hc : c < bs.length),
      chunkDecls g.P W c (recsOf bs[c]) = some (ps[c]'(by omega)).ds := fun c hc =>
    (hps c (by omega) hc).2.2.2.2.2
  have hD : ∀ p (hp : p < (winCtx g.P W.c0 bs).rs.length) d,
      (winCtx g.P W.c0 bs).rs[p] = .decl d →
      ∃ x, declOf (cutLk (g.P.setFrom W (joinN ps) (joinL ps) (joinE ps)).tabs
        ((winCtx g.P W.c0 bs).ctr p)) d = .ok (.inl x) := by
    intro p hp d hd
    obtain ⟨c, q, hc, hq, rfl⟩ := chunk_of_pos bs p hp
    have hE := winCtx_emb g.P W.c0 bs hc
    have hrq : (winCtx g.P W.c0 bs).rs[chunkOff bs c + q] = (recsOf bs[c])[q] := by
      have := hE.2.2.2 q hq
      rw [List.getElem?_eq_getElem hp] at this; exact Option.some.inj this
    rw [hrq] at hd
    exact (chunkDecls_spec (hW.chunkCtx hc) (hV c hc) (hDs c hc)).1 q hq d hd
  have hAll := allOK_of_good hGT hD
  -- the window, chunk by chunk
  have hchain : ∀ k, k ≤ bs.length → ∃ st, Reached st .empty (g.lineNo + chunkOff bs k)
      (g.total + byteOff bs k) ∧
      Holds st (g.P.setFrom W (joinN ps) (joinL ps) (joinE ps)).tabs
        ((winCtx g.P W.c0 bs).ctr (chunkOff bs k)) ∧
      st.decls = g.ds ++ (ps.toList.take k).foldl (fun a x => a ++ x.ds) #[] := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨st0, by simpa [chunkOff, byteOff] using hr0, ?_, by simp [hd0]⟩
      simp only [chunkOff_zero, WCtx.ctr, ctrAt_zero, winCtx]
      rw [← hc0] at hh0
      refine Holds.ofSel fun S j => ?_
      rw [hh0.sel S j]; split
      · rename_i hj; exact (S.inj_inj_opt (hGT.keep S.tb j hj)).symm
      · rfl
    | succ k ih =>
      intro hk
      have hkl : k < bs.length := by omega
      obtain ⟨st, hr, hh, hd⟩ := ih (by omega)
      -- the chunk's lines are right
      have hE := winCtx_emb g.P W.c0 bs hkl
      have hrs : chunkRecs bs = (chunkRecs bs).take (chunkOff bs k) ++ ((recsOf bs[k]).toList ++
          (chunkRecs bs).drop (chunkOff bs k + (recsOf bs[k]).size)) := by
        conv => lhs; rw [← List.take_append_drop (chunkOff bs k) (chunkRecs bs)]
        congr 1
        have hd := hE.drop
        simp only [winCtx] at hd
        conv => lhs; rw [← List.take_append_drop (recsOf bs[k]).size
          ((chunkRecs bs).drop (chunkOff bs k)), hd, List.drop_drop]
      have hAll' := hAll
      simp only [winCtx] at hAll'
      rw [hrs] at hAll'
      have hok := (AllOK.split (AllOK.split hAll').2).1
      have hcc : W.c0.stepAll ((chunkRecs bs).take (chunkOff bs k)) =
          (winCtx g.P W.c0 bs).ctr (chunkOff bs k) := rfl
      rw [hcc] at hok
      have hend := (hps k (by omega) hkl).2.2.2.1
      have htot' : g.total + byteOff bs k + bs[k].size < USize.size := by
        have := byteOff_le bs (k + 1); rw [byteOff_succ bs hkl] at this; omega
      obtain ⟨st', hs, hh', hd'⟩ := chunkStep_of_allOK hh hok hend htot'
      refine ⟨st', ?_, ?_, ?_⟩
      · rw [chunkOff_succ bs hkl, byteOff_succ bs hkl, ← Nat.add_assoc, ← Nat.add_assoc]
        exact hr.step hs
      · rw [winCtx_ctr_succ g.P W.c0 bs hkl]; exact hh'
      · rw [hd', declsAlong_acc, hd, joinD_take ps k (by omega),
          ← (chunkDecls_spec (hW.chunkCtx hkl) (hV k hkl) (hDs k hkl)).2]
        simp
  obtain ⟨st, hr, hh, hd⟩ := hchain bs.length (Nat.le_refl _)
  refine ⟨st, ?_, ?_, ?_, ?_⟩
  · have h1 : chunkOff bs bs.length = (bs.map fun b => (recsOf b).size).sum := by
      simp [chunkOff]
    have h2 : byteOff bs bs.length = (bs.map ByteArray.size).sum := by simp [byteOff]
    rw [h1, h2] at hr; exact hr
  · show Holds st _ W.cEnd
    rw [hcE]
    have : (winCtx g.P W.c0 bs).ctr (chunkOff bs bs.length) = W.c0.stepAll (chunkRecs bs) := by
      rw [chunkOff_length]; simp [WCtx.ctr, ctrAt, winCtx]
    rw [this] at hh; exact hh
  · rw [hd, joinD, ← Array.foldl_toList, List.take_of_length_le (by simp; omega)]
  · -- the finished tables after the window keep their invariant
    refine Prior.Inv.ofSel fun {α} S => ?_
    rw [S.pages_setFrom]
    exact (hA S).1

end ConLeche.Frontend
