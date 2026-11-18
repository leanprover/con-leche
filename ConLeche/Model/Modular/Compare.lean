module

public import ConLeche.Model.Copies
public import ConLeche.Driver.Compare
public import ConLeche.Verify.Cached.Fill

public section

/-!
# A compared challenge, record by record (task #607)

What the comparison (`Driver.compareRecords`) accepting a challenge record says: the record it
stands for (`ctx`) is the solution's record, or its statement for a hole, and the challenge's
record, a hole as its statement (`Driver.chalRecord`), installs copies of that record's
constants at the challenge's level-parameter names (`RecCopy`), with the same tables; and the
solution's record presents what it stands for (`Modular.Presents`), its theorems' values filled
or not.
-/

namespace ConLeche.Model.Compare

open ConLeche ConLeche.Driver ConLeche.Verify ConLeche.Model

/-- **A record installing copies of another's constants**, the same tables. -/
@[expose] def RecCopy (e r : Declaration) : Prop :=
  ConstsCopy (declConstants e) (declConstants r) ∧ declTables r = declTables e

theorem constsCopy_refl : ∀ l : List ConstantInfo, ConstsCopy l l
  | [] => .nil
  | _ :: l => .cons (.inl rfl) (constsCopy_refl l)

theorem RecCopy.refl (d : Declaration) : RecCopy d d := ⟨constsCopy_refl _, rfl⟩

theorem sameRecord_eq {d d' : Declaration} (h : sameRecord d d' = true) :
    declConstants d = declConstants d' ∧ declTables d = declTables d' := by
  unfold sameRecord at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hb⟩ := h
    rw [eq_of_listBeqBy (fun _ _ => ConstantInfo.eq_of_beqP) hb]
    exact ⟨rfl, rfl⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hc⟩ := h
    rw [ConstantVal.eq_of_beqP hc]
    exact ⟨rfl, rfl⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, rfl⟩ := h
    rw [ConstantVal.eq_of_beqP hc]
    exact ⟨rfl, rfl⟩
  · rw [ConstantVal.eq_of_beqP h]
    exact ⟨rfl, rfl⟩
  · exact ⟨eq_of_listBeqBy (fun _ _ => ConstantInfo.eq_of_beqP) h, by simp [declTables]⟩
  · exact ⟨eq_of_listBeqBy (fun _ _ => ConstantInfo.eq_of_beqP) h, by simp [declTables]⟩
  · exact nomatch h

theorem RecCopy.of_same {d d' : Declaration} (h : sameRecord d d' = true) : RecCopy d' d := by
  obtain ⟨h1, h2⟩ := sameRecord_eq h
  exact ⟨h1 ▸ constsCopy_refl _, h2⟩

/-- **A statement, the solution's up to level names.** -/
theorem sameCv_copy {cv cv' : ConstantVal} (h : sameCvUpToLevels cv cv' = true) :
    cv = cv' ∨ ∃ ps, cv = cv'.atLps ps ∧ ps.Nodup ∧ cv'.levelParams.length = ps.length := by
  unfold sameCvUpToLevels at h
  split at h
  · exact .inl (ConstantVal.eq_of_beqP h)
  · simp only [levelsRenaming, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact .inr ⟨cv.levelParams, (ConstantVal.eq_of_beqP h.2).symm, h.1.1.2, h.1.1.1.symm⟩

/-- **A constant, the solution's up to level names**: a copy of it. -/
theorem sameUpTo_copy {c c' : ConstantInfo} (h : sameUpToLevels c c' = true) : ConstCopy c' c := by
  unfold sameUpToLevels at h
  dsimp only at h
  split at h
  · exact .inl (ConstantInfo.eq_of_beqP h)
  · simp only [levelsRenaming, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact .inr ⟨_, (ConstantInfo.eq_of_beqP h.2).symm, h.1.1.2, h.1.1.1.symm⟩

theorem copy_axiom {cv cv' : ConstantVal}
    (h : cv = cv' ∨ ∃ ps, cv = cv'.atLps ps ∧ ps.Nodup ∧ cv'.levelParams.length = ps.length) :
    ConstCopy (.axiomInfo cv') (.axiomInfo cv) := by
  rcases h with rfl | ⟨ps, rfl, hnd, hl⟩
  · exact .inl rfl
  · exact .inr ⟨ps, rfl, hnd, hl⟩

theorem copy_thm {cv cv' : ConstantVal}
    (h : cv = cv' ∨ ∃ ps, cv = cv'.atLps ps ∧ ps.Nodup ∧ cv'.levelParams.length = ps.length) :
    ConstCopy (.thmInfo cv') (.thmInfo cv) := by
  rcases h with rfl | ⟨ps, rfl, hnd, hl⟩
  · exact .inl rfl
  · exact .inr ⟨ps, rfl, hnd, hl⟩

theorem cv_name {cv cv' : ConstantVal}
    (h : cv = cv' ∨ ∃ ps, cv = cv'.atLps ps ∧ ps.Nodup ∧ cv'.levelParams.length = ps.length) :
    cv.name = cv'.name := by
  rcases h with rfl | ⟨ps, rfl, -, -⟩ <;> rfl

/-- An axiom record of two copies of one statement installs copies. -/
theorem recCopy_axiom {cv cv' : ConstantVal}
    (h : cv = cv' ∨ ∃ ps, cv = cv'.atLps ps ∧ ps.Nodup ∧ cv'.levelParams.length = ps.length)
    (hq : cv'.name ≠ quotSoundName) :
    RecCopy (.axiomDecl cv') (.axiomDecl cv) := by
  refine ⟨?_, rfl⟩
  have hn := cv_name h
  simp only [declConstants, hn]
  rw [ite_eq_right hq]
  split
  · exact .nil
  · exact .cons (copy_axiom h) .nil

theorem recCopy_single {c c' : ConstantInfo} {d d' : Declaration} (h : ConstCopy c c')
    (h1 : declConstants d = [c]) (h2 : declConstants d' = [c']) (ht : declTables d' = declTables d) :
    RecCopy d d' := by
  refine ⟨?_, ht⟩
  rw [h1, h2]
  exact .cons h .nil

/-- **A record, the solution's up to level names**: it installs copies of the solution's. -/
theorem sameRecordUpTo_copy {dC dS : Declaration} (h : sameRecordUpToLevels dC dS = true) :
    RecCopy dS dC := by
  unfold sameRecordUpToLevels at h
  split at h
  · exact recCopy_single (sameUpTo_copy h) rfl rfl rfl
  · exact recCopy_single (copy_thm (sameCv_copy h)) rfl rfl rfl
  · rename_i cv v cv' v'
    have hc := sameUpTo_copy h
    refine recCopy_single (c := .axiomInfo cv') (c' := .axiomInfo cv) ?_ rfl rfl rfl
    rcases hc with he | ⟨ps, he, hnd, hl⟩
    · cases he; exact .inl rfl
    · simp only [ConstantInfo.atLps, ConstantInfo.defnInfo.injEq] at he
      exact .inr ⟨ps, by rw [he.1]; rfl, hnd, hl⟩
  · exact RecCopy.of_same h

theorem declConstants_fill (F : Expr → Expr) (d : Declaration) :
    declConstants (Cached.fillDecl F d) = declConstants d := by
  cases d <;> rfl

theorem declTables_fill (F : Expr → Expr) (d : Declaration) :
    declTables (Cached.fillDecl F d) = declTables d := by
  cases d <;> rfl

theorem stmtOf_fill (F : Expr → Expr) (d : Declaration) :
    Modular.stmtOf (Cached.fillDecl F d) = Modular.stmtOf d := by
  cases d <;> rfl

theorem presents_fill (d : Declaration) (F : Expr → Expr) :
    Modular.Presents d (Cached.fillDecl F d) :=
  .inl ⟨by rw [declConstants_fill], by rw [declTables_fill]⟩

theorem recKey_of_recCv {d : Declaration} {cv : ConstantVal} (h : recCv? d = some cv) :
    recKey d = cv.name := by
  cases d <;> simp_all [recCv?, recKey]

/-- **A filled hole's statement presents the solution's record**, but at a compiler-trust name
where the record is a definition or a theorem. -/
theorem presents_hole {dS : Declaration} (F : Expr → Expr)
    (hk : (∃ cv, dS = .axiomDecl cv) ∨
      (∃ cv v, dS = .opaqueDecl cv v ∧ cv.name ≠ quotSoundName) ∨
      (((∃ cv v h, dS = .defnDecl cv v h) ∨ (∃ cv v, dS = .thmDecl cv v)) ∧
        ∀ cv, recCv? dS = some cv → reduceOpNames.contains cv.name = false)) :
    Modular.Presents (Modular.stmtOf dS) (Cached.fillDecl F dS) := by
  rw [← stmtOf_fill F dS]
  rcases hk with ⟨cv, rfl⟩ | ⟨cv, v, rfl, hq⟩ | ⟨⟨cv, v, h, rfl⟩ | ⟨cv, v, rfl⟩, hr⟩
  · exact .inl ⟨.refl _, rfl⟩
  · by_cases hr : reduceOpNames.contains cv.name = true
    · refine .inl ⟨?_, rfl⟩
      have hs : cv.name ≠ sorryAxName := by
        intro e; rw [e] at hr; exact absurd hr (by decide)
      simp [Modular.stmtOf, Cached.fillDecl, declConstants, hq, hs]
    · refine .inr ⟨rfl, fun n hn => ?_⟩
      simp only [Cached.fillDecl, declConstants, List.map_cons, List.map_nil,
        List.mem_singleton, ConstantInfo.toConstantVal] at hn
      subst hn
      simpa using hr
  all_goals
    refine .inr ⟨rfl, fun n hn => ?_⟩
    simp only [Cached.fillDecl, declConstants, List.map_cons, List.map_nil,
      List.mem_singleton, ConstantInfo.toConstantVal] at hn
    subst hn
    simpa using hr cv rfl

/-- The statement of a record that declares one, not a quotient constant's. -/
theorem stmtOf_of_recCv {d : Declaration} {cv : ConstantVal} (h : recCv? d = some cv)
    (hq : ∀ k cv', d ≠ .quotDecl k cv') : Modular.stmtOf d = .axiomDecl cv := by
  cases d with
  | quotDecl k cv' => exact absurd rfl (hq k cv')
  | indDecl => simp [recCv?] at h
  | _ => simp only [recCv?, Option.some.injEq] at h; subst h; rfl

theorem isHole_kind {uses : Declaration → Array Name} {d : Declaration}
    (h : isHole uses d = true) : ∀ k cv', d ≠ .quotDecl k cv' := by
  rintro k cv' rfl; simp [isHole] at h

/-- **One compared record** (`Driver.cmpRecord`'s accept): the challenge's record, a hole as its
statement, installs copies of what it stands for; the solution's record presents what it stands
for, its values filled or not; and a name the challenge imports, but a theorem, has the same
home on both sides. -/
theorem cmpRecord_spec {C : Name} {uses : Declaration → Array Name} {own : Bool}
    {homeC homeS : Option Name} {dC dS e : Declaration} {f : Option Filled}
    (h : cmpRecord C uses own homeC homeS dC dS = .ok (e, f)) :
    RecCopy e (if own && isHole uses dC then Modular.stmtOf dC else dC) ∧
    (∀ F, Modular.Presents e (Cached.fillDecl F dS)) ∧
    (own = false → (∀ cv v, dC ≠ .thmDecl cv v) → homeC = homeS) := by
  unfold cmpRecord at h
  dsimp only at h
  cases own with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at h
    split at h
    · split at h
      · exact nomatch h
      · split at h
        · rename_i hs
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
          refine ⟨by simpa using RecCopy.of_same hs, presents_fill dS, fun _ hk => ?_⟩
          first
            | exact absurd rfl (hk _ _)
            | (rename_i heq; exact absurd heq (hk _ _))
            | simp_all
        · exact nomatch h
    · split at h
      · exact nomatch h
      · rename_i hne
        split at h
        · rename_i hs
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
          exact ⟨by simpa using RecCopy.of_same hs, presents_fill dS, fun _ _ => by simpa using hne⟩
        · exact nomatch h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and] at h ⊢
    split at h
    · rename_i hh
      simp only [hh, ↓reduceIte]
      split at h
      · exact nomatch h
      · rename_i hq
        -- the solution's kinds, and what fills the hole
        have hfill : ∀ {x}, (match recCv? dC, recCv? dS with
            | some cv, some cv' =>
              if sameCvUpToLevels cv cv' then
                (Except.ok (Modular.stmtOf dS, some ⟨recKey dC, x, recKind dS, homeS.getD C⟩) :
                  Except String (Declaration × Option Filled))
              else .error s!"{recKey dC}: the solution's {recKind dS} is not of the hole's type"
            | _, _ => .error s!"{recKey dC}: the solution's {recKind dS} is not of the hole's type")
              = .ok (e, f) →
            e = Modular.stmtOf dS ∧ ∃ cv cv', recCv? dC = some cv ∧ recCv? dS = some cv' ∧
              sameCvUpToLevels cv cv' = true := by
          intro x hx
          split at hx
          · rename_i cv cv' h1 h2
            split at hx
            · exact ⟨(Prod.mk.inj (Except.ok.inj hx)).1.symm, cv, cv', h1, h2, by assumption⟩
            · exact nomatch hx
          · exact nomatch hx
        have hcopy : ∀ {cv cv'}, recCv? dC = some cv → recCv? dS = some cv' →
            sameCvUpToLevels cv cv' = true → (∀ k c, dS ≠ .quotDecl k c) →
            RecCopy (Modular.stmtOf dS) (Modular.stmtOf dC) ∧ cv'.name ≠ quotSoundName := by
          intro cv cv' h1 h2 hs hkS
          have hc := sameCv_copy hs
          have hn : cv'.name ≠ quotSoundName := by
            rw [← cv_name hc, ← recKey_of_recCv h1]; simpa using hq
          rw [stmtOf_of_recCv h1 (isHole_kind hh), stmtOf_of_recCv h2 hkS]
          exact ⟨recCopy_axiom hc hn, hn⟩
        split at h
        · obtain ⟨rfl, cv, cv', h1, h2, hs⟩ := hfill h
          obtain ⟨hr, -⟩ := hcopy h1 h2 hs (by rintro _ _ ⟨⟩)
          exact ⟨hr, fun F => presents_hole F (.inl ⟨_, rfl⟩), fun h => nomatch h⟩
        · obtain ⟨rfl, cv, cv', h1, h2, hs⟩ := hfill h
          obtain ⟨hr, hn⟩ := hcopy h1 h2 hs (by rintro _ _ ⟨⟩)
          simp only [recCv?, Option.some.injEq] at h2
          subst h2
          exact ⟨hr, fun F => presents_hole F (.inr (.inl ⟨_, _, rfl, hn⟩)), fun h => nomatch h⟩
        · split at h
          · exact nomatch h
          · rename_i hred
            obtain ⟨rfl, cv, cv', h1, h2, hs⟩ := hfill h
            obtain ⟨hr, -⟩ := hcopy h1 h2 hs (by rintro _ _ ⟨⟩)
            refine ⟨hr, fun F => presents_hole F (.inr (.inr ⟨.inl ⟨_, _, _, rfl⟩, ?_⟩)),
              fun h => nomatch h⟩
            intro c hc
            simp only [recCv?, Option.some.injEq] at hc h2
            subst hc
            subst h2
            have := recKey_of_recCv h1
            rw [← cv_name (sameCv_copy hs), ← this]
            simpa using hred
        · split at h
          · exact nomatch h
          · rename_i hred
            obtain ⟨rfl, cv, cv', h1, h2, hs⟩ := hfill h
            obtain ⟨hr, -⟩ := hcopy h1 h2 hs (by rintro _ _ ⟨⟩)
            refine ⟨hr, fun F => presents_hole F (.inr (.inr ⟨.inr ⟨_, _, rfl⟩, ?_⟩)),
              fun h => nomatch h⟩
            intro c hc
            simp only [recCv?, Option.some.injEq] at hc h2
            subst hc
            subst h2
            have := recKey_of_recCv h1
            rw [← cv_name (sameCv_copy hs), ← this]
            simpa using hred
        · exact nomatch h
    · rename_i hh
      simp only [hh, ↓reduceIte, Bool.false_eq_true]
      split at h
      · rename_i hs
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨sameRecordUpTo_copy hs, presents_fill dS, fun h => nomatch h⟩
      · exact nomatch h

end ConLeche.Model.Compare
