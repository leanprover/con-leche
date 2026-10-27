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
          exact h.1.1.1.2
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
@[expose] def Reach (r : Region) (A : Prop) (st : DS) : Prop :=
  ∀ k s, IsKind k → st.marked k s = true → A → KindOK r k (8 * s)

/-- Every marked object at a slot in `[p, n)` is fine, and what it
leads to is marked. -/
@[expose] def Closed (r : Region) (st : DS) (p n : Nat) : Prop :=
  ∀ s, p ≤ s → s < n → ∀ k, IsKind k → st.marked k s = true →
    MarkOK r k (8 * s) ∧ ∀ k' c, Kid r k (8 * s) k' c → st.marked k' (c / 8) = true

/-- The marks only grow. -/
@[expose] def Sub (st st' : DS) : Prop :=
  ∀ k s, IsKind k → st.marked k s = true → st'.marked k s = true

theorem Sub.refl (st : DS) : Sub st st := fun _ _ _ h => h

theorem Sub.trans {a b c : DS} (h1 : Sub a b) (h2 : Sub b c) : Sub a c :=
  fun k s hk h => h2 k s hk (h1 k s hk h)

/-! ## One kind at one slot -/

/-- The marking of slot `p` as kind `k`, if it is marked so. -/
@[expose] def markStep (r : Region) (k : UInt8) (p : Nat) (st : DS) : Option DS :=
  if st.marked k p then markObj r k (8 * p) st else some st

/-- What one step does: it fails only where its object is marked and not
`MarkOK`; otherwise it adds exactly the marks of its `Kid`s, all below
`p`, and leaves the memo's sizes and values alone. -/
theorem markStep_spec {r : Region} {k : UInt8} {p n : Nat} {st : DS}
    (hs : st.Sized n) (hp : p < n) :
    match markStep r k p st with
    | none => st.marked k p = true ∧ ¬ MarkOK r k (8 * p)
    | some st' => st'.Sized n ∧ Sub st st' ∧
        (∀ k'' s, IsKind k'' → st'.marked k'' s = true → st.marked k'' s = true ∨
          ∃ c, st.marked k p = true ∧ Kid r k (8 * p) k'' c ∧ c / 8 = s) ∧
        (st.marked k p = true → MarkOK r k (8 * p) ∧
          ∀ k' c, Kid r k (8 * p) k' c → st'.marked k' (c / 8) = true) := by
  unfold markStep
  by_cases hm : st.marked k p = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
    have h := markObj_spec r k (8 * p) st
    split at h
    · rename_i heq; rw [heq]; exact ⟨hm, h⟩
    · rename_i st' heq
      rw [heq]
      obtain ⟨hok, hsz, h1, h2, h3, h4, hmk⟩ := h
      refine ⟨⟨by rw [hsz, hs.marks], by rw [h1, hs.names], by rw [h2, hs.levels],
        by rw [h3, hs.exprs], by rw [h4, hs.lists]⟩, ?_, ?_, ?_⟩
      · intro k'' s hk'' h
        exact (hmk k'' s hk'').mpr (Or.inl h)
      · intro k'' s hk'' h
        rcases (hmk k'' s hk'').mp h with h | ⟨c, hc, hcs, _⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hm, hc, hcs⟩
      · intro _
        refine ⟨hok, fun k' c hc => (hmk k' (c / 8) hc.kind).mpr (Or.inr ⟨c, hc, rfl, ?_⟩)⟩
        have := hc.lt
        rw [hs.marks]
        have : c / 8 < p := by omega
        omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
    refine ⟨hs, Sub.refl st, fun _ _ _ h => Or.inl h, fun h => absurd h hm⟩

/-! ## One slot -/

/-- The marking of slot `p` as each of the kinds `ks`, in order. -/
@[expose] def markSteps (r : Region) (ks : List UInt8) (p : Nat) (st : DS) : Option DS :=
  ks.foldlM (fun st k => markStep r k p st) st

theorem markKind_eq {r : Region} {k : UInt8} {mark : Region → Nat → DS → Option DS}
    (h : ∀ g st, mark r g st = markObj r k g st) (p : Nat) :
    markKind r k mark p = markStep r k p := by
  funext st; simp only [markKind, markStep, h]

theorem markSlot_eq (r : Region) (p : Nat) (st : DS) :
    markSlot r p st = markSteps r [kName, kLevel, kLevels, kExpr] p st := by
  simp only [markSlot, markKind_eq (markName_eq r), markKind_eq (markLevel_eq r),
    markKind_eq (markLevels_eq r), markKind_eq (markExpr_eq r), markSteps,
    List.foldlM_cons, List.foldlM_nil, bind_pure, Option.bind_eq_bind]
  rw [Option.bind_assoc, Option.bind_assoc]

theorem markSteps_spec {r : Region} {p n : Nat} (hp : p < n) :
    ∀ (ks : List UInt8) (st : DS), (∀ k ∈ ks, IsKind k) → st.Sized n →
    match markSteps r ks p st with
    | none => ∃ k ∈ ks, st.marked k p = true ∧ ¬ MarkOK r k (8 * p)
    | some st' => st'.Sized n ∧ Sub st st' ∧
        (∀ k'' s, IsKind k'' → st'.marked k'' s = true → st.marked k'' s = true ∨
          ∃ k c, IsKind k ∧ st.marked k p = true ∧ Kid r k (8 * p) k'' c ∧ c / 8 = s) ∧
        (∀ k ∈ ks, st.marked k p = true → MarkOK r k (8 * p) ∧
          ∀ k' c, Kid r k (8 * p) k' c → st'.marked k' (c / 8) = true)
  | [], st, _, hs => by
    simp only [markSteps, List.foldlM]
    exact ⟨hs, Sub.refl st, fun _ _ _ h => Or.inl h, fun _ h => absurd h (by simp)⟩
  | k :: ks, st, hks, hs => by
    have hk : IsKind k := hks k (by simp)
    have hks' : ∀ k ∈ ks, IsKind k := fun k' h => hks k' (List.mem_cons_of_mem _ h)
    have h1 := markStep_spec (r := r) (k := k) hs hp
    simp only [markSteps, List.foldlM_cons] at *
    split at h1
    · rename_i heq
      simp only [heq, bind, Option.bind]
      exact ⟨k, by simp, h1⟩
    · rename_i st1 heq
      simp only [heq, bind, Option.bind]
      obtain ⟨hs1, hsub1, hnew1, hdone1⟩ := h1
      -- the marks at slot `p` are the same in `st1`
      have hsame : ∀ k', IsKind k' → st1.marked k' p = st.marked k' p := by
        intro k' hk'
        cases e : st.marked k' p
        · cases e1 : st1.marked k' p
          · rfl
          · rcases hnew1 k' p hk' e1 with h | ⟨c, _, hc, hcs⟩
            · rw [e] at h; cases h
            · have := hc.lt; omega
        · exact hsub1 k' p hk' e
      have ih := markSteps_spec (r := r) hp ks st1 hks' hs1
      split at ih
      · rename_i heq2
        simp only [markSteps] at heq2
        rw [heq2]
        obtain ⟨k', hk'm, hk'p, hk'ok⟩ := ih
        exact ⟨k', by simp [hk'm], by rw [← hsame k' (hks' k' hk'm)]; exact hk'p, hk'ok⟩
      · rename_i st2 heq2
        simp only [markSteps] at heq2
        rw [heq2]
        obtain ⟨hs2, hsub2, hnew2, hdone2⟩ := ih
        refine ⟨hs2, hsub1.trans hsub2, ?_, ?_⟩
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

theorem marked_of_marksAt_zero {st : DS} {p : Nat} (h : ¬ (st.marksAt p != 0) = true)
    (k : UInt8) : st.marked k p = false := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
  simp [DS.marked, h]

theorem kinds_all : ∀ k ∈ [kName, kLevel, kLevels, kExpr], IsKind k := by
  intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  unfold IsKind; rcases hk with rfl | rfl | rfl | rfl <;> simp

theorem IsKind.mem {k : UInt8} (h : IsKind k) : k ∈ [kName, kLevel, kLevels, kExpr] := by
  unfold IsKind at h; rcases h with rfl | rfl | rfl | rfl <;> simp

/-- **The downward sweep keeps its invariants**, and fails only when
`A` does not hold. -/
theorem markPass_spec {r : Region} {n : Nat} {A : Prop} :
    ∀ p st, p ≤ n → st.Sized n → Reach r A st → Closed r st p n →
    match markPass r st p with
    | none => ¬ A
    | some st' => st'.Sized n ∧ Sub st st' ∧ Reach r A st' ∧ Closed r st' 0 n
  | 0, st, _, hs, hr, hc => by
    simp only [markPass]; exact ⟨hs, Sub.refl st, hr, hc⟩
  | p + 1, st, hp, hs, hr, hc => by
    unfold markPass
    by_cases hnz : (st.marksAt p != 0) = true
    · simp only [hnz, ↓reduceIte]
      rw [markSlot_eq]
      have h := markSteps_spec (r := r) (show p < n by omega) _ st kinds_all hs
      split at h
      · rename_i heq
        simp only [heq]
        obtain ⟨k, hkm, hkp, hnot⟩ := h
        exact fun hA => hnot (KindOK.markOK (kinds_all k hkm) (hr k p (kinds_all k hkm) hkp hA))
      · rename_i st1 heq
        simp only [heq]
        obtain ⟨hs1, hsub1, hnew1, hdone1⟩ := h
        have hold : ∀ k s, IsKind k → p ≤ s → st1.marked k s = true → st.marked k s = true := by
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
        have ih := markPass_spec p st1 (by omega) hs1 hr1 hc1
        split at ih
        · exact ih
        · obtain ⟨hs2, hsub2, hr2, hc2⟩ := ih
          exact ⟨hs2, hsub1.trans hsub2, hr2, hc2⟩
    · simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      have hc' : Closed r st p n := by
        intro s hps hsn k hk hm
        by_cases e : s = p
        · subst e; rw [marked_of_marksAt_zero hnz k] at hm; cases hm
        · exact hc s (by omega) hsn k hk hm
      exact markPass_spec p st (by omega) hs hr hc'

end ConLeche.Frontend.Olean
