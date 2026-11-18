module

public import ConLeche.Model.Copies
public import ConLeche.Driver.Compare
public import ConLeche.Verify.Cached.Fill
public import ConLeche.Model.Modular.Valid
import ConLeche.Model.Modular.Main
import ConLeche.Verify.Driver.ComposeReads
import ConLeche.Verify.Driver.Reach
import ConLeche.Model.Modular.Proofs

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

open ConLeche ConLeche.Driver ConLeche.Verify ConLeche.Model SetTheory

/-- **A record installing copies of another's constants**, the same tables. -/
@[expose] def RecCopy (e r : Declaration) : Prop :=
  ConstsCopy (declConstants e) (declConstants r) ∧ declTables r = declTables e

theorem constsCopy_refl : ∀ l : List ConstantInfo, ConstsCopy l l
  | [] => .nil
  | _ :: l => .cons (.inl rfl) (constsCopy_refl l)

theorem RecCopy.refl (d : Declaration) : RecCopy d d := ⟨constsCopy_refl _, rfl⟩

theorem QuotKind.slot_inj {k k' : QuotKind} (h : k.slot = k'.slot) : k = k' := by
  cases k <;> cases k' <;> simp_all [QuotKind.slot]

theorem sameRecord_eq {d d' : Declaration} (h : sameRecord d d' = true) :
    declConstants d = declConstants d' ∧ declTables d = declTables d' := by
  unfold sameRecord at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hb⟩ := h
    rw [eq_of_listBeqBy (fun _ _ => ConstantInfo.eq_of_beqP) hb]
    exact ⟨rfl, rfl⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hk, hc⟩ := h
    obtain rfl : _ := QuotKind.slot_inj hk
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
            rw [← cv_name hc, ← recKey_of_recCv h1]; exact fun e => hq (by simp [e])
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

/-- **A hole the comparison accepts is at neither the quotient's axiom nor the placeholder
axiom.** -/
theorem cmpRecord_hole_name {C : Name} {uses : Declaration → Array Name}
    {homeC homeS : Option Name} {dC dS e : Declaration} {f : Option Filled}
    (hh : isHole uses dC = true) (h : cmpRecord C uses true homeC homeS dC dS = .ok (e, f)) :
    recKey dC ≠ quotSoundName ∧ recKey dC ≠ sorryAxName := by
  unfold cmpRecord at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hh] at h
  split at h
  · exact nomatch h
  · rename_i hq
    exact ⟨fun e => hq (by simp [e]), fun e => hq (by simp [e])⟩

/-! ## The comparison, record by record -/

/-- A fold that pushes one element per step, each related to its input. -/
theorem foldlM_push {α β γ ε : Type} {g : Array β × γ → α → Except ε (Array β × γ)}
    (P : α → β → Prop) (hg : ∀ acc a r, g acc a = .ok r → ∃ b, r.1 = acc.1.push b ∧ P a b) :
    ∀ (L : List α) (acc r : Array β × γ), L.foldlM g acc = .ok r →
      r.1.size = acc.1.size + L.length ∧ (∀ i, i < acc.1.size → r.1[i]? = acc.1[i]?) ∧
      ∀ i (hi : i < L.length), ∃ b, r.1[acc.1.size + i]? = some b ∧ P L[i] b
  | [], acc, r, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | a :: L, acc, r, h => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · rename_i r₁ h₁
      obtain ⟨b, hb, hP⟩ := hg acc a r₁ h₁
      obtain ⟨hs, hpre, hall⟩ := foldlM_push P hg L r₁ r h
      have hs₁ : r₁.1.size = acc.1.size + 1 := by rw [hb, Array.size_push]
      refine ⟨by rw [hs, hs₁]; simp; omega, fun i hi => ?_, fun i hi => ?_⟩
      · rw [hpre i (by omega), hb, Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]
      · cases i with
        | zero =>
          refine ⟨b, ?_, hP⟩
          rw [Nat.add_zero, hpre _ (by omega), hb, Array.getElem?_push_size]
        | succ i =>
          obtain ⟨b', hb', hP'⟩ := hall i (by simp at hi; omega)
          refine ⟨b', ?_, hP'⟩
          rw [← hb', hs₁]
          congr 1
          omega

/-- **The comparison's accept, record by record**: what each challenge record stands for is
`cmpRecord`'s accept against a solution record. -/
theorem compareRecords_spec {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    (h : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled)) :
    ctx.size = recsC.size ∧ ∀ k (hk : k < recsC.size), ∃ e, ctx[k]? = some e ∧
      ∃ dS ∈ recsS, ∃ f, cmpRecord C uses (homesC[recKey recsC[k]]? == some C)
        homesC[recKey recsC[k]]? homesS[recKey recsC[k]]? recsC[k] dS = .ok (e, f) := by
  unfold compareRecords at h
  rw [← Array.foldlM_toList] at h
  have := foldlM_push (fun dC e => ∃ dS ∈ recsS, ∃ f, cmpRecord C uses
      (homesC[recKey dC]? == some C) homesC[recKey dC]? homesS[recKey dC]? dC dS = .ok (e, f))
    (fun acc a r hr => ?_) recsC.toList _ _ h
  · obtain ⟨hs, -, hall⟩ := this
    refine ⟨by simpa using hs, fun k hk => ?_⟩
    obtain ⟨b, hb, hP⟩ := hall k (by simpa using hk)
    exact ⟨b, by simpa using hb, by simpa using hP⟩
  · obtain ⟨ctx₀, fl₀⟩ := acc
    dsimp only at hr
    split at hr
    · exact nomatch hr
    · rename_i dS hdS
      split at hr
      · exact nomatch hr
      · rename_i d f hc
        obtain ⟨rfl⟩ := hr
        refine ⟨d, rfl, dS, ?_, f, hc⟩
        obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.mp hdS
        exact Array.mem_of_getElem? hi

/-! ## The order check -/

/-- The names, installed one at a time, none twice. -/
theorem installs_ok {install : Std.HashSet Name → Name → Except String (Std.HashSet Name)}
    (hi : ∀ S n S', install S n = .ok S' → S.contains n = false ∧ S' = S.insert n) :
    ∀ (ns : List Name) (S S' : Std.HashSet Name), ns.foldlM install S = .ok S' →
      (∀ n ∈ ns, S.contains n = false) ∧ ns.Nodup ∧
        ∀ m, S'.contains m = true ↔ (S.contains m = true ∨ m ∈ ns)
  | [], S, S', h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | n :: ns, S, S', h => by
    simp only [List.foldlM, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · rename_i S₁ h₁
      obtain ⟨hn, rfl⟩ := hi S n S₁ h₁
      obtain ⟨hf, hnd, hc⟩ := installs_ok hi ns _ S' h
      refine ⟨fun m hm => ?_, List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun m => ?_⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hn
        · have := hf m hm
          simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
          exact this.2
      · have := hf n hm
        simp [Std.HashSet.contains_insert] at this
      · rw [hc m]
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
        constructor
        · rintro ((rfl | h) | h) <;> simp_all
        · rintro (h | rfl | h) <;> simp_all

/-- A fold over records that installs each one's names fresh and checks what it reads. -/
theorem scoped_fold {g : Std.HashSet Name → Declaration → Except String (Std.HashSet Name)}
    (hg : ∀ S e S', g S e = .ok S' → (∀ n ∈ Modular.declNames e, S.contains n = false) ∧
      (Modular.declNames e).Nodup ∧
      (∀ m, S'.contains m = true ↔ (S.contains m = true ∨ m ∈ Modular.declNames e)) ∧
      ∀ y ∈ recordReads e, S'.contains y = true) :
    ∀ (L P : List Declaration) (S₀ S₁ : Std.HashSet Name),
      (∀ m, S₀.contains m = true ↔ m ∈ P.flatMap Modular.declNames) →
      (P.flatMap Modular.declNames).Nodup → L.foldlM g S₀ = .ok S₁ →
      ((P ++ L).flatMap Modular.declNames).Nodup ∧
        ∀ i (hi : i < L.length), ∀ y ∈ recordReads L[i],
          y ∈ (P ++ L.take (i + 1)).flatMap Modular.declNames
  | [], _, _, _, _, hnd, _ => by simpa using hnd
  | e :: L, P, S₀, S₁, hS₀, hnd, hf => by
    simp only [List.foldlM, bind, Except.bind] at hf
    split at hf
    · exact nomatch hf
    · rename_i S₃ h₃
      obtain ⟨hnew, hnd₁, hc, hrd⟩ := hg _ _ _ h₃
      have hS₃ : ∀ m, S₃.contains m = true ↔ m ∈ (P ++ [e]).flatMap Modular.declNames := by
        intro m; rw [hc m, hS₀ m]; simp
      have hnd₃ : ((P ++ [e]).flatMap Modular.declNames).Nodup := by
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        refine List.nodup_append.mpr ⟨hnd, hnd₁, fun a ha b hb hab => ?_⟩
        subst hab
        have := hnew a hb
        rw [← Bool.not_eq_true, hS₀ a] at this
        exact this ha
      obtain ⟨hA, hB⟩ := scoped_fold hg L (P ++ [e]) S₃ S₁ hS₃ hnd₃ hf
      refine ⟨by simpa using hA, fun i hi y hy => ?_⟩
      cases i with
      | zero =>
        have hy' := (hS₃ y).mp (hrd y hy)
        simpa using hy'
      | succ i =>
        have := hB i (by simp at hi; omega) y hy
        simpa using this

/-- **The order check's accept** (`Driver.ctxScoped`): no name installed twice, and every name
a record reads installed by it or a record before it. -/
theorem ctxScoped_spec {ctx : Array Declaration} (h : ctxScoped ctx = none) :
    (ctx.toList.flatMap Modular.declNames).Nodup ∧
      ∀ k (hk : k < ctx.size), ∀ y ∈ recordReads ctx[k],
        y ∈ (ctx.toList.take (k + 1)).flatMap Modular.declNames := by
  unfold ctxScoped at h
  dsimp only at h
  split at h
  · exact nomatch h
  · rename_i S hS
    rw [← Array.foldlM_toList] at hS
    have key := scoped_fold ?hg ctx.toList [] {} S (by simp) (by simp) hS
    · obtain ⟨hA, hB⟩ := key
      refine ⟨by simpa using hA, fun k hk y hy => ?_⟩
      have := hB k (by simpa using hk) y (by simpa using hy)
      simpa using this
    case hg =>
      intro S₀ e S' hx
      try dsimp only at hx
      split at hx
      · exact nomatch hx
      · rename_i S₂ h₂
        split at hx
        · exact nomatch hx
        · rename_i hfind
          obtain rfl := Except.ok.inj hx
          obtain ⟨hnew, hnd, hc⟩ := installs_ok (fun S n S' hi => by
            try dsimp only at hi
            split at hi
            · exact nomatch hi
            · rename_i hn
              exact ⟨by simpa using hn, (Except.ok.inj hi).symm⟩) _ _ _ h₂
          refine ⟨hnew, hnd, hc, fun y hy => ?_⟩
          have := Array.find?_eq_none.mp hfind y hy
          simpa using this

/-! ## The challenge's environment, a copy of what it stands for -/

theorem _root_.ConLeche.Model.ConstsCopy.append : ∀ {a a' b b' : List ConstantInfo}, ConstsCopy a a' →
    ConstsCopy b b' → ConstsCopy (a ++ b) (a' ++ b')
  | _, _, _, _, .nil, hb => hb
  | _, _, _, _, .cons hc ha, hb => .cons hc (ha.append hb)

theorem _root_.ConLeche.Model.ConstsCopy.reverse : ∀ {a a' : List ConstantInfo}, ConstsCopy a a' →
    ConstsCopy a.reverse a'.reverse
  | _, _, .nil => .nil
  | _, _, .cons hc ha => by
    simp only [List.reverse_cons]
    exact ha.reverse.append (.cons hc .nil)

theorem records_copy : ∀ (L L' : List Declaration), L.length = L'.length →
    (∀ i (h : i < L.length) (h' : i < L'.length), RecCopy L[i] L'[i]) →
    ConstsCopy (Model.Modular.recsC L) (Model.Modular.recsC L') ∧
      L'.flatMap declTables = L.flatMap declTables
  | [], [], _, _ => ⟨.nil, rfl⟩
  | d :: L, d' :: L', hl, h => by
    obtain ⟨h1, h2⟩ := records_copy L L' (by simpa using hl)
      (fun i hi hi' => h (i + 1) (by simp; omega) (by simp; omega))
    obtain ⟨h3, h4⟩ := h 0 (by simp) (by simp)
    simp only [Model.Modular.recsC, List.flatMap_cons] at h1 h2 ⊢
    exact ⟨h3.append h1, by simp only [List.getElem_cons_zero] at h4; rw [h4, h2]⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- **The challenge's environment is a copy of what its records stand for**: on the comparison's
and the order check's accept, the challenge's records, each hole as its statement, install
copies of the constants of what they stand for, at the challenge's level-parameter names, and
the same tables. -/
theorem chal_copies {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    (hcmp : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled))
    (hsc : ctxScoped ctx = none) :
    CopiesEnv (streamEnv ctx.toList) (streamEnv (recsC.toList.map (chalRecord C uses homesC))) := by
  obtain ⟨hsz, hk⟩ := compareRecords_spec hcmp
  obtain ⟨hnd, -⟩ := ctxScoped_spec hsc
  have key := records_copy ctx.toList (recsC.toList.map (chalRecord C uses homesC))
    (by simp [hsz]) ?hrec
  · obtain ⟨hc, ht⟩ := key
    refine ⟨?_, ?_, ?_⟩
    · rw [Model.Modular.streamEnv_empty_consts, Model.Modular.streamEnv_empty_consts]
      exact hc.reverse
    · rw [Model.Modular.streamEnv_empty_tables, Model.Modular.streamEnv_empty_tables, ht]
    · rw [Model.Modular.streamEnv_empty_consts, List.map_reverse,
        (List.reverse_perm _).nodup_iff]
      simp only [Model.Modular.recsC, List.map_flatMap]
      exact hnd
  case hrec =>
    intro i h h'
    have hi : i < recsC.size := by simpa using h'
    obtain ⟨e, he, dS, -, f, hr⟩ := hk i hi
    have hei : ctx.toList[i] = e := by
      simp only [Array.getElem_toList]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by simpa using h)).symm.trans he)
    rw [hei]
    simp only [List.getElem_map, Array.getElem_toList, chalRecord]
    exact (cmpRecord_spec hr).1

/-! ## The two-module development -/

/-- **A compared run as a development of two modules**: module 0 the solution, its own records
`ds` (the solution's records, its theorems' values in place), presenting `ctx`; module 1 the
challenge, checked against `ctx`, read from module 0, with no records of its own. -/
@[expose] def cmpDev (ds ctx : List Declaration) : Nat → Modular.Module
  | 0 => { imports := [], ctx := [], decls := ds, src := fun _ => 0, iface := ctx }
  | _ => { imports := [0], ctx := ctx, decls := [], src := fun _ => 0, iface := [] }

theorem empty_find? (n : Name) : (Env.empty.find? n) = none := rfl

theorem names_isSome {L : List Declaration} {y : Name} (hy : y ∈ L.flatMap Modular.declNames) :
    ((streamEnv L).find? y).isSome = true := by
  obtain ⟨d, hd, hn⟩ := List.mem_flatMap.mp hy
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hn
  have hm : ci ∈ (streamEnv L).consts := (mem_streamEnv_consts L Env.empty).2 (.inl ⟨d, hd, hci⟩)
  simpa [ConstantInfo.name] using Model.Modular.find?_isSome_of_mem' hm

/-- **Both modules pass the local checks.** -/
theorem cmpDev_localOk {pins : List NatOpPinSet} {maxNatSize : Nat} {F : Expr → Expr}
    {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    {env : Env}
    (hcmp : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled))
    (hsc : ctxScoped ctx = none)
    (hchk : Cached.checkDecls .verified pins maxNatSize (recsS.map (Cached.fillDecl F)) = .ok env) :
    ∀ j ≤ 1, Modular.LocalOk .verified pins maxNatSize
      (cmpDev (recsS.map (Cached.fillDecl F)).toList ctx.toList) j := by
  obtain ⟨hsz, hk⟩ := compareRecords_spec hcmp
  obtain ⟨hnd, hrd⟩ := ctxScoped_spec hsc
  have hcp := chal_copies hcmp hsc
  -- every context record presents a solution record
  have hpres : ∀ e ∈ ctx.toList, ∃ p ∈ (recsS.map (Cached.fillDecl F)).toList,
      Modular.Presents e p := by
    intro e he
    obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp he
    have hkc : k < recsC.size := by simp at hk'; omega
    obtain ⟨e', he', dS, hdS, f, hr⟩ := hk k hkc
    have : ctx.toList[k] = e' := by
      simp only [Array.getElem_toList]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by simpa using hk')).symm.trans he')
    rw [this]
    exact ⟨Cached.fillDecl F dS, by simpa using Array.mem_map_of_mem hdS, (cmpRecord_spec hr).2.1 F⟩
  intro j hj
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · refine ⟨⟨hpres⟩, ⟨fun b hb => by simp [cmpDev] at hb, fun n hn => ?_, ?_,
      fun d hd => by simp [cmpDev] at hd, fun d hd => by simp [cmpDev] at hd,
      fun d hd => by simp [cmpDev] at hd, fun k hk => by simp [cmpDev] at hk, ?_⟩⟩
    · simp [cmpDev, Modular.Module.context, streamEnv, empty_find?] at hn
    · simp [cmpDev, Modular.Module.context, streamEnv, Env.empty]
    · obtain ⟨n, fe, hrun, -⟩ := Cached.checkDecls_run (mode := .verified) hchk
      exact ⟨_, hrun⟩
  · have hctx : (cmpDev (recsS.map (Cached.fillDecl F)).toList ctx.toList 1).context
        = streamEnv ctx.toList := rfl
    refine ⟨⟨fun e he => by simp [cmpDev] at he⟩, ⟨fun b hb => ?_,
      fun n _ => Nat.zero_lt_one, ?_, fun d hd n _ => hd, fun _ _ _ _ _ _ => rfl,
      fun d hd n _ => ?_, fun k hk => ?_, ⟨_, .nil _⟩⟩⟩
    · simp only [cmpDev, List.mem_singleton] at hb; omega
    · rw [hctx]; exact hcp.nodup
    · -- what a context record reads, stored in the solution and read alike
      obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hd
      apply recordReads_scoped
      intro y hy
      have hk'' : k < ctx.size := by simpa [cmpDev] using hk'
      have hyt := hrd k hk'' y (by simpa [cmpDev] using hy)
      obtain ⟨e, he, hye⟩ := List.mem_flatMap.mp hyt
      have he' : e ∈ ctx.toList := List.mem_of_mem_take he
      have hyn : y ∈ ctx.toList.flatMap Modular.declNames := List.mem_flatMap.mpr ⟨e, he', hye⟩
      obtain ⟨p, hp, hpr⟩ := hpres e he'
      exact Compose.Run.readsAlike_isSome (by rw [hctx]; exact names_isSome hyn) (.same rfl)
        (Compose.Run.own_of_decl hp (Compose.presents_names hpr hye))
    · apply recordReads_scoped
      intro y hy
      have hk'' : k < ctx.size := by simpa [cmpDev] using hk
      exact names_isSome (by simpa [cmpDev] using hrd k hk'' y (by simpa [cmpDev] using hy))

/-! ## The models -/

universe w

/-- **The compared run's models** (the model-tier core of `MainTheorem.compare_solves`): on the
comparison's and the order check's accept and the fold's accept of the solution's records, the
challenge's environment (its holes as statements) and the solution's have models, and the
challenge's model values every name as the solution's model values it, at the challenge's
level-parameter names. -/
theorem compare_models (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}
    {F : Expr → Expr} {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    {env : Env}
    (hcmp : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled))
    (hsc : ctxScoped ctx = none)
    (hchk : Cached.checkDecls .verified pins maxNatSize (recsS.map (Cached.fillDecl F)) = .ok env) :
    ∃ (mC : ConLeche.Model V (streamEnv (recsC.toList.map (chalRecord C uses homesC))))
      (mS : ConLeche.Model V (streamEnv (recsS.map (Cached.fillDecl F)).toList)),
      ∀ n cC, (streamEnv (recsC.toList.map (chalRecord C uses homesC))).find? n = some cC →
        ∃ cS, (streamEnv (recsS.map (Cached.fillDecl F)).toList).find? n = some cS ∧
          cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
          ∀ φ, mC.cval n φ = mS.cval n (Level.substFn φ cS.toConstantVal.levelParams
            (cC.toConstantVal.levelParams.map Level.param)) := by
  classical
  have hok := cmpDev_localOk (F := F) hcmp hsc hchk
  have hcp := chal_copies hcmp hsc
  let dev := cmpDev (recsS.map (Cached.fillDecl F)).toList ctx.toList
  obtain ⟨mm, hc⟩ := Model.Modular.modularModels (V := V) (pins := pins) (dev := dev) (i := 1) hok
  have hex : ∀ j (hj : j < 2), ∃ mp : EnvModelM V (dev j).own,
      ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = (mm j hj).1 n :=
    fun j hj => (mm j hj).2.2.2.2.elim fun mp h => ⟨mp, h.2.2⟩
  obtain ⟨mp1, hmp1⟩ := hex 1 (by omega)
  obtain ⟨mp0, hmp0⟩ := hex 0 (by omega)
  refine ⟨Model.ofCopies (env := streamEnv ctx.toList) mp1 hcp,
    Model.ofEnvModelM (env := streamEnv (recsS.map (Cached.fillDecl F)).toList) mp0,
    fun n cC hfC => ?_⟩
  rcases hcp.find n with ⟨-, h2⟩ | ⟨c, cC', h1, h2, hr⟩
  · rw [h2] at hfC; exact nomatch hfC
  · rw [h2] at hfC
    obtain rfl := Option.some.inj hfC
    obtain ⟨cS, hS, hal, -⟩ := Model.Modular.agree_alike hok (Modular.Agree.same (dev := dev)
      (i := 1) (b := 0) (n := n) rfl) (Nat.le_refl 1) (Nat.zero_le 1) h1
    have hlps : cS.toConstantVal.levelParams = c.toConstantVal.levelParams := by
      rw [hal.cv]
    refine ⟨cS, hS, ?_, fun φ => ?_⟩
    · rw [hlps]
      rcases hr with rfl | ⟨ps, rfl, -, hl⟩
      · rfl
      · rw [atLps_cv]; exact hl
    · refine (Model.ofCopies_cval mp1 hcp h1 h2 φ).trans ?_
      refine Eq.trans ?_ (congrFun (congrFun (Model.Model.ofEnvModelM_cval
        (env := streamEnv (recsS.map (Cached.fillDecl F)).toList) mp0) n) _).symm
      rw [hlps]
      refine congrFun (Model.cvalOf_congr ?_) _
      have hn1 : ((dev 1).own.find? n).isSome = true := by
        show ((streamEnv ctx.toList).find? n).isSome = true
        rw [h1]; rfl
      have hn0 : ((dev 0).own.find? n).isSome = true := by rw [hS]; rfl
      rw [hmp1 n hn1, hmp0 n hn0]
      obtain ⟨_, he, _⟩ := hc 1 (by omega) n ⟨by
        show ((streamEnv ctx.toList).find? n).isSome = true
        rw [h1]; rfl, trivial⟩
      exact he

/-- **The home rule, on the comparison's accept**: a name the challenge imports, but a
theorem, has the same home in the solution's closure. -/
theorem compare_homes {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    (hcmp : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled)) :
    ∀ k (hk : k < recsC.size), homesC[recKey recsC[k]]? ≠ some C →
      (∀ cv v, recsC[k] ≠ .thmDecl cv v) →
      homesS[recKey recsC[k]]? = homesC[recKey recsC[k]]? := by
  intro k hk hne hthm
  obtain ⟨-, hall⟩ := compareRecords_spec hcmp
  obtain ⟨e, -, dS, -, f, hr⟩ := hall k hk
  exact ((cmpRecord_spec hr).2.2 (by simpa using hne) hthm).symm

theorem isHole_recCv {uses : Declaration → Array Name} {d : Declaration}
    (h : isHole uses d = true) : ∃ cv, recCv? d = some cv := by
  cases d <;> simp_all [isHole, recCv?]

/-- **The holes are inhabited by the solution's constants**: on the same accepts as
`compare_models`, its two models, and for every hole of the challenge module `C` (a record of
`C`'s own that `isHole` names), the solution's constant of its name, whose value in the
solution's model, read at the challenge's level-parameter names, is a member of what the
hole's type denotes in the challenge's model. -/
theorem compare_solved (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {maxNatSize : Nat}
    {F : Expr → Expr} {C : Name} {uses : Declaration → Array Name}
    {homesC homesS : Std.HashMap Name Name} {recsS : Array Declaration}
    {idxS : Std.HashMap Name Nat} {recsC ctx : Array Declaration} {filled : Array Filled}
    {env : Env}
    (hcmp : compareRecords C uses homesC homesS recsS idxS recsC = .ok (ctx, filled))
    (hsc : ctxScoped ctx = none)
    (hchk : Cached.checkDecls .verified pins maxNatSize (recsS.map (Cached.fillDecl F)) = .ok env) :
    ∃ (mC : ConLeche.Model V (streamEnv (recsC.toList.map (chalRecord C uses homesC))))
      (mS : ConLeche.Model V (streamEnv (recsS.map (Cached.fillDecl F)).toList)),
      (∀ n cC, (streamEnv (recsC.toList.map (chalRecord C uses homesC))).find? n = some cC →
        ∃ cS, (streamEnv (recsS.map (Cached.fillDecl F)).toList).find? n = some cS ∧
          cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
          ∀ φ, mC.cval n φ = mS.cval n (Level.substFn φ cS.toConstantVal.levelParams
            (cC.toConstantVal.levelParams.map Level.param))) ∧
      ∀ d ∈ recsC, homesC[recKey d]? = some C → isHole uses d = true →
        ∃ cv cS, recCv? d = some cv ∧
          (streamEnv (recsS.map (Cached.fillDecl F)).toList).find? cv.name = some cS ∧
          ∀ φ ρ, ∃ T, Denotes mC.cval (streamEnv (recsC.toList.map (chalRecord C uses homesC)))
            φ ρ cv.type T ∧
            mS.cval cv.name (Level.substFn φ cS.toConstantVal.levelParams
              (cv.levelParams.map Level.param)) ∈ˢ T := by
  obtain ⟨mC, mS, h1⟩ := compare_models V hcmp hsc hchk
  have hcp := chal_copies hcmp hsc
  refine ⟨mC, mS, h1, fun d hd hown hh => ?_⟩
  obtain ⟨cv, hcv⟩ := isHole_recCv hh
  have hnames : cv.name ≠ quotSoundName ∧ cv.name ≠ sorryAxName := by
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hd
    obtain ⟨-, hall⟩ := compareRecords_spec hcmp
    obtain ⟨e, he, dS, hdS, f, hr⟩ := hall k hk
    rw [hown] at hr
    rw [← recKey_of_recCv hcv]
    exact cmpRecord_hole_name hh (by simpa using hr)
  have hrec : chalRecord C uses homesC d = .axiomDecl cv := by
    simp only [chalRecord, hown, beq_self_eq_true, hh, Bool.and_self, ↓reduceIte]
    exact stmtOf_of_recCv hcv (isHole_kind hh)
  have hm : ConstantInfo.axiomInfo cv ∈
      (streamEnv (recsC.toList.map (chalRecord C uses homesC))).consts :=
    (mem_streamEnv_consts _ Env.empty).2 (.inl ⟨_, List.mem_map_of_mem
      (Array.mem_toList_iff.mpr hd), by rw [hrec]; simp [declConstants, hnames]⟩)
  obtain ⟨-, -, -, hf, -⟩ := mem_copies hcp.consts hcp.nodup _ hm
  obtain ⟨cS, hS, -, he⟩ := h1 cv.name (.axiomInfo cv) hf
  refine ⟨cv, cS, hcv, hS, fun φ ρ => ?_⟩
  obtain ⟨T, hT, hmem⟩ := mC.mem _ hm φ ρ
  refine ⟨T, hT, ?_⟩
  have e2 : mC.cval cv.name φ = mS.cval cv.name (Level.substFn φ cS.toConstantVal.levelParams
      (cv.levelParams.map Level.param)) := he φ
  rw [← e2]
  exact hmem

end ConLeche.Model.Compare
