module

public import ConLeche.Verify.Frontend.Olean.Build

public section

/-!
# Both passes from the roots (task #371)

`runPasses` (`ConLeche/Frontend/Olean/Fast.lean`) marks the roots in a
fresh memo, sweeps down, sweeps up.  With `A` the statement that every
root reads, the sweeps' invariants give: on success every root's memo
value is its specification's (`runPasses_some`), and on failure some
root does not read (`runPasses_none`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- Every root reads. -/
@[expose] def RootsOK (r : Region) (names exprs : List UInt64) : Prop :=
  (∀ v ∈ names, (nameP r v).isSome) ∧ (∀ v ∈ exprs, (exprP r v).isSome)

theorem maxLoc_ge_init (r : Region) : ∀ (vs : List UInt64) (m : Nat), m ≤ maxLoc r vs m
  | [], m => by simp [maxLoc]
  | v :: vs, m => by
    simp only [maxLoc, List.foldl_cons] at *
    exact Nat.le_trans (Nat.le_max_left _ _) (maxLoc_ge_init r vs _)

theorem maxLoc_ge (r : Region) : ∀ (vs : List UInt64) (m : Nat) (v : UInt64), v ∈ vs →
    r.locGo v r.segs.size ≤ maxLoc r vs m
  | [], _, _, h => by simp at h
  | w :: vs, m, v, h => by
    simp only [maxLoc, List.foldl_cons] at *
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (maxLoc_ge_init r vs _)
    · exact maxLoc_ge r vs _ v h

theorem loc_eq {r : Region} {v : UInt64} {c : Nat} (h : r.loc v = some c) :
    r.locGo v r.segs.size = c := by
  unfold Region.loc at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

/-- What marking the roots does. -/
theorem rootsFold {r : Region} {A : Prop} {n : Nat} {K : UInt8} (hK : IsKind K) {nil : Bool}
    {P : UInt64 → Prop}
    (hP : ∀ v, ¬ (nil = true ∧ v = 1) → P v → ∃ c, r.loc v = some c ∧ KindOK r K c)
    (hPn : ∀ v, ¬ (nil = true ∧ v = 1) → r.loc v = none → ¬ P v) :
    ∀ (vs : List UInt64) (st : ByteArray), st.size = n →
      (∀ v ∈ vs, r.locGo v r.segs.size / 8 < n) → Reach r A st → (A → ∀ v ∈ vs, P v) →
      match vs.foldlM (markRoot r K nil) st with
      | none => ¬ A
      | some st' => st'.size = n ∧ Sub st st' ∧ Reach r A st' ∧
          ∀ v ∈ vs, ¬ (nil = true ∧ v = 1) → ∃ c, r.loc v = some c ∧ marked st' K (c / 8) = true
  | [], st, hs, _, hr, _ => by
    simp only [List.foldlM_nil]
    exact ⟨hs, Sub.refl st, hr, fun _ h => absurd h (by simp)⟩
  | v :: vs, st, hs, hb, hr, hA => by
    simp only [List.foldlM_cons]
    have hstep : markRoot r K nil st v =
        if (nil && v == 1) = true then some st
        else match r.loc v with
          | some c => some (mark st K (c / 8))
          | none => none := rfl
    rw [hstep]
    by_cases hn : nil = true ∧ v = 1
    · have : (nil && v == 1) = true := by simp [hn.1, hn.2]
      simp only [this, ↓reduceIte]
      have ih := rootsFold hK hP hPn vs st hs (fun w hw => hb w (List.mem_cons_of_mem _ hw)) hr
        (fun a w hw => hA a w (List.mem_cons_of_mem _ hw))
      simp only [bind, Option.bind]
      split at ih
      · exact ih
      · rename_i st' heq
        obtain ⟨hs', hsub, hr', hm⟩ := ih
        refine ⟨hs', hsub, hr', ?_⟩
        intro w hw hnw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact absurd hn hnw
        · exact hm w hw hnw
    · have : (nil && v == 1) = false := by
        cases nil <;> simp_all
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      cases hl : r.loc v with
      | none =>
        simp only [bind, Option.bind]
        exact fun a => hPn v hn hl (hA a v (by simp))
      | some c =>
        simp only [bind, Option.bind]
        have hcn : c / 8 < n := by have := hb v (by simp); rw [loc_eq hl] at this; exact this
        have hs1 : (mark st K (c / 8)).size = n := by rw [size_mark, hs]
        have hr1 : Reach r A (mark st K (c / 8)) := by
          intro k s hk hm a
          rw [marked_mark st hK hk] at hm
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
          rcases hm with hm | ⟨⟨rfl, rfl⟩, _⟩
          · exact hr k _ hk hm a
          · obtain ⟨c', hc', hok⟩ := hP v hn (hA a v (by simp))
            rw [hl] at hc'; cases hc'
            rw [eight_div (loc_mod hl)]; exact hok
        have hsub1 : Sub st (mark st K (c / 8)) := by
          intro k s hk hm
          rw [marked_mark st hK hk]; simp [hm]
        have ih := rootsFold hK hP hPn vs (mark st K (c / 8)) hs1
          (fun w hw => hb w (List.mem_cons_of_mem _ hw)) hr1
          (fun a w hw => hA a w (List.mem_cons_of_mem _ hw))
        split at ih
        · exact ih
        · rename_i st' heq
          obtain ⟨hs', hsub, hr', hm⟩ := ih
          refine ⟨hs', hsub1.trans hsub, hr', ?_⟩
          intro w hw hnw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · refine ⟨c, hl, hsub K (c / 8) hK ?_⟩
            rw [marked_mark st hK hK]
            simp [hs, hcn]
          · exact hm w hw hnw

theorem kName_kind : IsKind kName := Or.inl rfl
theorem kExpr_kind : IsKind kExpr := Or.inr (Or.inr (Or.inl rfl))

/-- **Both passes, from the roots.** -/
theorem runPasses_spec (r : Region) (names exprs : List UInt64) :
    match runPasses r names exprs with
    | none => ¬ RootsOK r names exprs
    | some st => (∀ v ∈ names, st.nameOf r v = nameP r v) ∧
        (∀ v ∈ exprs, st.exprOf r v = exprP r v) := by
  unfold runPasses
  generalize hn : maxLoc r exprs (maxLoc r names 0) / 8 + 1 = n
  have hbN : ∀ v ∈ names, r.locGo v r.segs.size / 8 < n := by
    intro v hv
    have := Nat.le_trans (maxLoc_ge r names 0 v hv) (maxLoc_ge_init r exprs _)
    have := Nat.div_le_div_right (c := 8) this
    omega
  have hbE : ∀ v ∈ exprs, r.locGo v r.segs.size / 8 < n := by
    intro v hv
    have := Nat.div_le_div_right (c := 8) (maxLoc_ge r exprs (maxLoc r names 0) v hv)
    omega
  have hP1 : ∀ v, ¬ (true = true ∧ v = 1) → (nameP r v).isSome →
      ∃ c, r.loc v = some c ∧ KindOK r kName c := by
    intro v hv h
    have hv' : v ≠ 1 := fun e => hv ⟨rfl, e⟩
    unfold nameP at h
    simp only [hv', beq_iff_eq, ↓reduceIte] at h
    split at h
    · rename_i c hc; exact ⟨c, hc, KindOK.name h⟩
    · cases h
  have hPn1 : ∀ v, ¬ (true = true ∧ v = 1) → r.loc v = none → ¬ (nameP r v).isSome := by
    intro v hv hl h
    have hv' : v ≠ 1 := fun e => hv ⟨rfl, e⟩
    unfold nameP at h
    simp only [hv', beq_iff_eq, ↓reduceIte, hl] at h
    cases h
  have hP2 : ∀ v, ¬ (false = true ∧ v = 1) → (exprP r v).isSome →
      ∃ c, r.loc v = some c ∧ KindOK r kExpr c := by
    intro v _ h
    unfold exprP at h
    split at h
    · rename_i c hc; exact ⟨c, hc, KindOK.expr h⟩
    · cases h
  have hPn2 : ∀ v, ¬ (false = true ∧ v = 1) → r.loc v = none → ¬ (exprP r v).isSome := by
    intro v _ hl h
    unfold exprP at h
    simp only [hl] at h
    cases h
  have hr0 : Reach r (RootsOK r names exprs) (zeros n) := by
    intro k s _ hm; rw [marked_zeros] at hm; cases hm
  have h1 := rootsFold (A := RootsOK r names exprs) kName_kind hP1 hPn1 names (zeros n)
    (size_zeros n) hbN hr0 (fun a => a.1)
  cases e1 : names.foldlM (markRoot r kName true) (zeros n) with
  | none => rw [e1] at h1; simp only [bind, Option.bind, e1]; exact h1
  | some st1 =>
    rw [e1] at h1
    simp only [bind, Option.bind, e1]
    obtain ⟨hs1, _, hr1, hm1⟩ := h1
    have h2 := rootsFold (A := RootsOK r names exprs) kExpr_kind hP2 hPn2 exprs st1 hs1 hbE hr1
      (fun a => a.2)
    cases e2 : exprs.foldlM (markRoot r kExpr false) st1 with
    | none => rw [e2] at h2; exact h2
    | some st2 =>
      rw [e2] at h2
      obtain ⟨hs2, hsub2, hr2, hm2⟩ := h2
      simp only
      have h3 := markPass_spec (r := r) (A := RootsOK r names exprs) n st2 (Nat.le_refl n) hs2 hr2
        (fun s h1 h2 => absurd h2 (by omega))
      cases e3 : markPass r st2 n with
      | none => rw [e3] at h3; exact h3
      | some st3 =>
        rw [e3] at h3
        obtain ⟨hs3, hsub3, hr3, hc3⟩ := h3
        simp only
        have h4 := buildPass_spec (r := r) (A := RootsOK r names exprs) (n := n) hc3 hr3 0
          (DS.fresh n) (DS.fresh_sized n) (fun s h => absurd h (by omega))
        cases e4 : buildPass r st3 n (DS.fresh n) 0 with
        | none => rw [e4] at h4; exact h4
        | some st4 =>
          rw [e4] at h4
          obtain ⟨_, hb4⟩ := h4
          have hmark : ∀ k s, IsKind k → marked st2 k s = true → marked st3 k s = true :=
            fun k s hk h => hsub3 k s hk h
          refine ⟨?_, ?_⟩
          · intro v hv
            by_cases e : v = 1
            · subst e; simp [DS.nameOf, nameP]
            · obtain ⟨c, hl, hmc⟩ := hm1 v hv (fun h => e h.2)
              have hmc4 := hmark kName (c / 8) kName_kind (hsub2 kName (c / 8) kName_kind hmc)
              have hcn : c / 8 < n := by have := hbN v hv; rw [loc_eq hl] at this; exact this
              have hval := (hb4 (c / 8) hcn kName kName_kind hmc4).1 rfl
              rw [eight_div (loc_mod hl)] at hval
              simp only [DS.nameOf, nameP, e, beq_iff_eq, ↓reduceIte, hl, hval]
          · intro v hv
            obtain ⟨c, hl, hmc⟩ := hm2 v hv (fun h => by cases h.1)
            have hmc4 := hmark kExpr (c / 8) kExpr_kind hmc
            have hcn : c / 8 < n := by have := hbE v hv; rw [loc_eq hl] at this; exact this
            have hval := (hb4 (c / 8) hcn kExpr kExpr_kind hmc4).2.2.2 rfl
            rw [eight_div (loc_mod hl)] at hval
            simp only [DS.exprOf, exprP, hl, hval]

end ConLeche.Frontend.Olean
