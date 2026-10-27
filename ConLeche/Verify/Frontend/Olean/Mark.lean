module

public import ConLeche.Verify.Frontend.Olean.Nodes

public section

/-!
# The downward sweep (task #371)

`markPass` (`ConLeche/Frontend/Olean/Fast.lean`) keeps two invariants
over a memo whose marks hold for the slots it has swept:

* `Reach A`: every marked object reads, as its kind, as soon as `A`
  holds — `A` is "every root reads";
* `Closed p n`: every marked object at a slot from `p` up has a shape
  its node function reads (`MarkOK`), and the objects it leads to are
  marked.

A failure of the sweep therefore refutes `A`, and its success leaves
every marked object `MarkOK` with its `Kid`s marked.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Locations are word-aligned -/

theorem locGo_mod (r : Region) (a : UInt64) : ∀ i, r.locGo a i % 8 = 0
  | 0 => rfl
  | i + 1 => by
    unfold Region.locGo
    dsimp only
    split
    · split
      · split
        · rename_i h; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          exact h.1.1
        · rfl
      · exact locGo_mod r a i
    · rfl

theorem loc_mod {r : Region} {a : UInt64} {c : Nat} (h : r.loc a = some c) : c % 8 = 0 := by
  unfold Region.loc at h
  dsimp only at h
  split at h
  · cases h
  · cases h; exact locGo_mod r a _

theorem down_mod {r : Region} {g c : Nat} {v : UInt64} (h : r.down g v = some c) : c % 8 = 0 := by
  unfold Region.down at h
  split at h
  · split at h
    · cases h; exact loc_mod (by assumption)
    · cases h
  · cases h

theorem Kid.mod {r : Region} {k : UInt8} {g : Nat} {k' : UInt8} {c : Nat} (h : Kid r k g k' c) :
    c % 8 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hd⟩ := h
  exact down_mod hd

/-! ## The invariants -/

/-- Every marked object reads as its kind, once `A` holds. -/
@[expose] def Reach (r : Region) (A : Prop) (m : ByteArray) : Prop :=
  ∀ k s, IsKind k → marked m k s = true → A → KindOK r k (8 * s)

/-- Every marked object at a slot in `[p, n)` is fine, and what it
leads to is marked. -/
@[expose] def Closed (r : Region) (m : ByteArray) (p n : Nat) : Prop :=
  ∀ s, p ≤ s → s < n → ∀ k, IsKind k → marked m k s = true →
    MarkOK r k (8 * s) ∧ ∀ k' c, Kid r k (8 * s) k' c → marked m k' (c / 8) = true

/-- The marks only grow. -/
@[expose] def Sub (m m' : ByteArray) : Prop :=
  ∀ k s, IsKind k → marked m k s = true → marked m' k s = true

theorem Sub.refl (m : ByteArray) : Sub m m := fun _ _ _ h => h

theorem Sub.trans {a b c : ByteArray} (h1 : Sub a b) (h2 : Sub b c) : Sub a c :=
  fun k s hk h => h2 k s hk (h1 k s hk h)

/-! ## One kind at one slot -/

/-- The marking of slot `p` as kind `k`, if it is marked so. -/
@[expose] def markStep (r : Region) (k : UInt8) (p : Nat) (m : ByteArray) : ByteArray :=
  if marked m k p then markObj r k (8 * p) m else m

theorem size_markStep (r : Region) (k : UInt8) (p : Nat) (m : ByteArray) :
    (markStep r k p m).size = m.size := by
  unfold markStep; split
  · exact size_markObj _ _ _ _
  · rfl

theorem markStep_failed {r : Region} {k : UInt8} {p : Nat} {m : ByteArray} (hs : 0 < m.size)
    (hf : failedM m = true) : failedM (markStep r k p m) = true := by
  unfold markStep; split
  · exact markObj_failed _ _ _ _ hs hf
  · exact hf

/-- What one step does: from a marking that has not failed, it fails
only where its object is marked and not `MarkOK`; otherwise it adds
exactly the marks of its `Kid`s, all below `p`. -/
theorem markStep_spec {r : Region} {k : UInt8} {p : Nat} {st : ByteArray}
    (hs : 0 < st.size) (hp : p < st.size) (hf : failedM st = false) :
    (failedM (markStep r k p st) = true → marked st k p = true ∧ ¬ MarkOK r k (8 * p)) ∧
    (failedM (markStep r k p st) = false → Sub st (markStep r k p st) ∧
        (∀ k'' s, IsKind k'' → marked (markStep r k p st) k'' s = true →
          marked st k'' s = true ∨
          ∃ c, marked st k p = true ∧ Kid r k (8 * p) k'' c ∧ c / 8 = s) ∧
        (marked st k p = true → MarkOK r k (8 * p) ∧
          ∀ k' c, Kid r k (8 * p) k' c → marked (markStep r k p st) k' (c / 8) = true)) := by
  unfold markStep
  by_cases hm : marked st k p = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
    obtain ⟨h1, h2⟩ := markObj_spec r k (8 * p) st hs hf
    refine ⟨fun h => ⟨hm, h1.mp h⟩, fun hnf => ⟨?_, ?_, ?_⟩⟩
    · intro k'' s hk'' h
      exact (h2 hnf k'' s hk'').mpr (Or.inl h)
    · intro k'' s hk'' h
      rcases (h2 hnf k'' s hk'').mp h with h | ⟨c, hc, hcs, _⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, hm, hc, hcs⟩
    · intro _
      have hok : MarkOK r k (8 * p) := Classical.byContradiction fun hn => by
        rw [h1.mpr hn] at hnf; cases hnf
      refine ⟨hok, fun k' c hc => (h2 hnf k' (c / 8) hc.kind).mpr (Or.inr ⟨c, hc, rfl, ?_⟩)⟩
      have := hc.lt
      have : c / 8 < p := by omega
      omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    refine ⟨(fun h => by rw [hf] at h; cases h), fun _ => ⟨Sub.refl st, fun _ _ _ h => Or.inl h,
      fun h => absurd h hm⟩⟩

/-! ## One slot -/

/-- The marking of slot `p` as each of the kinds `ks`, in order. -/
@[expose] def markSteps (r : Region) (ks : List UInt8) (p : Nat) (st : ByteArray) : ByteArray :=
  ks.foldl (fun st k => markStep r k p st) st

theorem markKind_eq {r : Region} {k : UInt8} {markK : Region → Nat → ByteArray → ByteArray}
    (h : ∀ g st, markK r g st = markObj r k g st) (p : Nat) :
    markKind r k markK p = markStep r k p := by
  funext st; simp only [markKind, markStep, h]

theorem markSlot_eq (r : Region) (p : Nat) (st : ByteArray) :
    markSlot r p st = markSteps r [kName, kLevel, kLevels, kExpr] p st := by
  simp only [markSlot, markKind_eq (markName_eq r), markKind_eq (markLevel_eq r),
    markKind_eq (markLevels_eq r), markKind_eq (markExpr_eq r), markSteps, List.foldl_cons,
    List.foldl_nil]

theorem size_markSteps (r : Region) (p : Nat) :
    ∀ (ks : List UInt8) (st : ByteArray), (markSteps r ks p st).size = st.size
  | [], _ => rfl
  | k :: ks, st => by
    have := size_markSteps r p ks (markStep r k p st)
    simp only [markSteps, List.foldl_cons] at this ⊢
    rw [this, size_markStep]

theorem markSteps_failed {r : Region} {p : Nat} :
    ∀ (ks : List UInt8) (st : ByteArray), 0 < st.size → failedM st = true →
    failedM (markSteps r ks p st) = true
  | [], _, _, h => h
  | k :: ks, st, hs, h => by
    have := markSteps_failed (r := r) (p := p) ks (markStep r k p st)
      (by rw [size_markStep]; exact hs) (markStep_failed hs h)
    simp only [markSteps, List.foldl_cons] at this ⊢
    exact this

theorem markSteps_spec {r : Region} {p : Nat} :
    ∀ (ks : List UInt8) (st : ByteArray), (∀ k ∈ ks, IsKind k) → 0 < st.size → p < st.size →
    failedM st = false →
    (failedM (markSteps r ks p st) = true →
        ∃ k ∈ ks, marked st k p = true ∧ ¬ MarkOK r k (8 * p)) ∧
    (failedM (markSteps r ks p st) = false → Sub st (markSteps r ks p st) ∧
        (∀ k'' s, IsKind k'' → marked (markSteps r ks p st) k'' s = true →
          marked st k'' s = true ∨
          ∃ k c, IsKind k ∧ marked st k p = true ∧ Kid r k (8 * p) k'' c ∧ c / 8 = s) ∧
        (∀ k ∈ ks, marked st k p = true → MarkOK r k (8 * p) ∧
          ∀ k' c, Kid r k (8 * p) k' c → marked (markSteps r ks p st) k' (c / 8) = true))
  | [], st, _, _, _, hf => by
    simp only [markSteps, List.foldl_nil]
    exact ⟨(fun h => by rw [hf] at h; cases h),
      fun _ => ⟨Sub.refl st, fun _ _ _ h => Or.inl h, fun _ h => absurd h (by simp)⟩⟩
  | k :: ks, st, hks, hs, hp, hf => by
    have hk : IsKind k := hks k (by simp)
    have hks' : ∀ k ∈ ks, IsKind k := fun k' h => hks k' (List.mem_cons_of_mem _ h)
    have hstep : markSteps r (k :: ks) p st = markSteps r ks p (markStep r k p st) := rfl
    rw [hstep]
    have h1 := markStep_spec (r := r) (k := k) hs hp hf
    generalize e1 : markStep r k p st = st1 at h1
    have hs1 : st1.size = st.size := by rw [← e1, size_markStep]
    cases hf1 : failedM st1 with
    | true =>
      obtain ⟨hkp, hnot⟩ := h1.1 hf1
      have := markSteps_failed (r := r) (p := p) ks st1 (by omega) hf1
      rw [this]
      exact ⟨fun _ => ⟨k, by simp, hkp, hnot⟩, fun h => by cases h⟩
    | false =>
      obtain ⟨hsub1, hnew1, hdone1⟩ := h1.2 hf1
      have hsame : ∀ k', IsKind k' → marked st1 k' p = marked st k' p := by
        intro k' hk'
        cases e : marked st k' p
        · cases e1 : marked st1 k' p
          · rfl
          · rcases hnew1 k' p hk' e1 with h | ⟨c, _, hc, hcs⟩
            · rw [e] at h; cases h
            · have := hc.lt; omega
        · exact hsub1 k' p hk' e
      obtain ⟨ih1, ih2⟩ := markSteps_spec (r := r) (p := p) ks st1 hks' (by omega) (by omega) hf1
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨k', hk'm, hk'p, hk'ok⟩ := ih1 h
        exact ⟨k', by simp [hk'm], by rw [← hsame k' (hks' k' hk'm)]; exact hk'p, hk'ok⟩
      · obtain ⟨hsub2, hnew2, hdone2⟩ := ih2 h
        refine ⟨hsub1.trans hsub2, ?_, ?_⟩
        · intro k'' s hk'' h
          rcases hnew2 k'' s hk'' h with h | ⟨k0, c, hk0, hk0p, hc, hcs⟩
          · rcases hnew1 k'' s hk'' h with h | ⟨c, hkp, hc, hcs⟩
            · exact Or.inl h
            · exact Or.inr ⟨k, c, hk, hkp, hc, hcs⟩
          · exact Or.inr ⟨k0, c, hk0, by rw [← hsame k0 hk0]; exact hk0p, hc, hcs⟩
        · intro k' hk'm hk'p
          simp only [List.mem_cons] at hk'm
          rcases hk'm with rfl | hk'm
          · obtain ⟨hok, hkids⟩ := hdone1 hk'p
            exact ⟨hok, fun k'' c hc => hsub2 k'' (c / 8) hc.kind (hkids k'' c hc)⟩
          · exact hdone2 k' hk'm (by rw [hsame k' (hks' k' hk'm)]; exact hk'p)

/-! ## The sweep -/

theorem marked_of_marksAt_zero {st : ByteArray} {p : Nat} (h : ¬ (marksAt st p != 0) = true)
    (k : UInt8) : marked st k p = false := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
  simp [marked, h]

theorem kinds_all : ∀ k ∈ [kName, kLevel, kLevels, kExpr], IsKind k := by
  intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  unfold IsKind; rcases hk with rfl | rfl | rfl | rfl <;> simp

theorem IsKind.mem {k : UInt8} (h : IsKind k) : k ∈ [kName, kLevel, kLevels, kExpr] := by
  unfold IsKind at h; rcases h with rfl | rfl | rfl | rfl <;> simp

theorem size_markPass (r : Region) : ∀ (p : Nat) (st : ByteArray), (markPass r st p).size = st.size
  | 0, _ => rfl
  | p + 1, st => by
    unfold markPass
    split
    · dsimp only
      split
      · rw [markSlot_eq, size_markSteps]
      · rw [size_markPass r p, markSlot_eq, size_markSteps]
    · exact size_markPass r p st

/-- **The downward sweep keeps its invariants**, and fails only when
`A` does not hold. -/
theorem markPass_spec {r : Region} {n : Nat} {A : Prop} (hn : 0 < n) :
    ∀ p st, p ≤ n → st.size = n → failedM st = false → Reach r A st → Closed r st p n →
    (failedM (markPass r st p) = true → ¬ A) ∧
    (failedM (markPass r st p) = false → Sub st (markPass r st p) ∧
      Reach r A (markPass r st p) ∧ Closed r (markPass r st p) 0 n)
  | 0, st, _, _, hf, hr, hc => by
    simp only [markPass]
    exact ⟨(fun h => by rw [hf] at h; cases h), fun _ => ⟨Sub.refl st, hr, hc⟩⟩
  | p + 1, st, hp, hs, hf, hr, hc => by
    unfold markPass
    by_cases hnz : (marksAt st p != 0) = true
    · simp only [hnz, ↓reduceIte]
      rw [markSlot_eq]
      have h := markSteps_spec (r := r) (p := p) _ st kinds_all (by omega) (by omega) hf
      generalize e1 : markSteps r [kName, kLevel, kLevels, kExpr] p st = st1 at h
      have hs1 : st1.size = n := by rw [← e1, size_markSteps, hs]
      cases hf1 : failedM st1 with
      | true =>
        simp only [↓reduceIte, hf1]
        obtain ⟨k, hkm, hkp, hnot⟩ := h.1 hf1
        refine ⟨fun _ hA => hnot (KindOK.markOK (kinds_all k hkm)
          (hr k p (kinds_all k hkm) hkp hA)), fun h => by cases h⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hsub1, hnew1, hdone1⟩ := h.2 hf1
        have hold : ∀ k s, IsKind k → p ≤ s → marked st1 k s = true → marked st k s = true := by
          intro k s hk hps hm
          rcases hnew1 k s hk hm with h | ⟨k0, c, _, _, hc, hcs⟩
          · exact h
          · have := hc.lt; omega
        have hr1 : Reach r A st1 := by
          intro k s hk hm hA
          rcases hnew1 k s hk hm with h | ⟨k0, c, hk0, hk0p, hc, hcs⟩
          · exact hr k s hk h hA
          · have := KindOK.kid hk0 (hr k0 p hk0 hk0p hA) hc
            have hm8 := hc.mod
            rw [show 8 * s = c by omega]; exact this
        have hc1 : Closed r st1 p n := by
          intro s hps hsn k hk hm
          have hm0 := hold k s hk hps hm
          by_cases e : s = p
          · subst e; exact hdone1 k hk.mem hm0
          · obtain ⟨hok, hkids⟩ := hc s (by omega) hsn k hk hm0
            exact ⟨hok, fun k' c hkc => hsub1 k' (c / 8) hkc.kind (hkids k' c hkc)⟩
        obtain ⟨ih1, ih2⟩ := markPass_spec hn p st1 (by omega) hs1 hf1 hr1 hc1
        refine ⟨ih1, fun h => ?_⟩
        obtain ⟨hsub2, hr2, hc2⟩ := ih2 h
        exact ⟨hsub1.trans hsub2, hr2, hc2⟩
    · simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      have hc' : Closed r st p n := by
        intro s hps hsn k hk hm
        by_cases e : s = p
        · subst e; rw [marked_of_marksAt_zero hnz k] at hm; cases hm
        · exact hc s (by omega) hsn k hk hm
      exact markPass_spec hn p st (by omega) hs hf hr hc'

end ConLeche.Frontend.Olean
