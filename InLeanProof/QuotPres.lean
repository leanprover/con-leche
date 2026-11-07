module

public import InLeanProof.EnvPresI
/- `QuotKind`'s derived `BEq` (read by `quotRecVal`/`quotRuleRhs`) is not
exposed. -/
import all Lean.Declaration
/- `InLean.markQuot` is core's private `markQuotInit` (`InLean/Push.lean`, not
exposed for that reason); the proof reads that it changes no constant. -/
import all Lean.Environment
import all InLean.Push
/- `Expr.updateSort!`/`updateConst!` (read by `instLPF`'s arms, as in `Range.lean`). -/
import all Lean.Expr

/-!
# The quotient package keeps the relation (task #451, lane P3b)

`quotGroupPres : QuotGroupPres`.  InLean's `checkQuotC` adds the four
quotient constants at the pins' own level names (`quotPin`, …), so every
term involved is a closed constant: con-leche's record of each
(`toDecl`, `quotDecl`) installs `quotAt k cv`, the pinned basis block's
slot at those names, and the two are related as `EntryRelI`'s `quotInfo`
clause states (by evaluation, `decide`).  The eliminators' rule is
`quotRuleRhs`, InLean's level instantiation of the pin's rule, which is
related to con-leche's through `toExpr_instantiateLevelParams` once it is
known to write no `rangePoison` (`emvarS_instantiateLevelParams`, from the
pins' level depths).  The four constants are pushed one by one
(`presI_one`), then `markQuot` changes no lookup (`presI_congr`).

Also here: `presI_congr` (the relation only reads lookups) and
`emvarS_instantiateLevelParams` (level instantiation writes no poison where
every level fits).
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Level instantiation writes no poison where every level fits -/

/-- Every `sort`'s and `const`'s level fits `md` more levels of depth. -/
@[expose] def LvFits (md : Nat) : Expr → Prop
  | .sort u => depthS u + md ≤ maxLevelDepth
  | .const _ ls => ∀ u ∈ ls, depthS u + md ≤ maxLevelDepth
  | .app f a | .lam _ f a _ | .forallE _ f a _ => LvFits md f ∧ LvFits md a
  | .letE _ t v b _ => LvFits md t ∧ LvFits md v ∧ LvFits md b
  | .mdata _ x | .proj _ _ x => LvFits md x
  | _ => True

theorem depthFits_of {us : List Level} (hus : ∀ u ∈ us, depthS u ≤ maxLevelDepth) {u : Level}
    (h : depthS u + maxDepthS us ≤ maxLevelDepth) : EO.depthFits (EO.maxDepthOf us) u = true := by
  have hu : depthS u ≤ maxLevelDepth := by omega
  simp only [EO.depthFits, EO.maxLevelDepth, (Level.fields u hu).1, maxDepthOf_eq hus,
    decide_eq_true_eq]
  exact h

/-- **Level instantiation writes no `rangePoison`** on a term in range
without metavariables whose levels fit the substituted ones' depth. -/
theorem emvarS_instantiateLevelParams {e : Expr} (ps : List Name) (us : List Level)
    (hr : Expr.RangeOk e) (he : emvarS e = false) (hus : ∀ u ∈ us, depthS u ≤ maxLevelDepth)
    (hf : LvFits (maxDepthS us) e) :
    emvarS (EO.instantiateLevelParams e ps us) = false := by
  rw [instantiateLevelParams_eq]
  split
  · exact he
  · suffices ∀ (x : Expr) (k : Nat), Expr.RangeOk x → emvarS x = false → LvFits (maxDepthS us) x →
        emvarS (mapSpec (instLPF ps us) x k) = false from this e 0 hr he hf
    intro x
    induction x with
    | sort u =>
      intro k _ _ hfx
      by_cases hp : (Expr.sort u).hasLevelParam = false
      · rw [mapSpec_eq_of_some (show instLPF ps us (.sort u) k = some (.sort u) by
          simp [instLPF, hp])]; rfl
      · have hfit := depthFits_of hus hfx
        rw [mapSpec_eq_of_some (show instLPF ps us (.sort u) k =
            some (.sort (Lvl.subst ps us u)) by
          simp [instLPF, hp, hfit, Expr.updateSort!, mkSort])]
        rfl
    | const n ls =>
      intro k _ _ hfx
      by_cases hp : (Expr.const n ls).hasLevelParam = false
      · rw [mapSpec_eq_of_some (show instLPF ps us (.const n ls) k = some (.const n ls) by
          simp [instLPF, hp])]; rfl
      · have hfit : ls.all (EO.depthFits (EO.maxDepthOf us)) = true :=
          List.all_eq_true.2 fun u hu => depthFits_of hus (hfx u hu)
        rw [mapSpec_eq_of_some (show instLPF ps us (.const n ls) k =
            some (.const n (ls.map (Lvl.subst ps us))) by
          simp only [instLPF, hp, hfit]; simp [Expr.updateConst!, mkConst])]
        rfl
    | app g a ihg iha =>
      intro k hx he hfx
      cases hc : instLPF ps us (.app g a) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none =>
        simp only [emvarS, Bool.or_eq_false_iff] at he
        simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff]
        exact ⟨ihg k hx.1 he.1 hfx.1, iha k hx.2 he.2 hfx.2⟩
    | lam n t b bi iht ihb =>
      intro k hx he hfx
      cases hc : instLPF ps us (.lam n t b bi) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none =>
        simp only [emvarS, Bool.or_eq_false_iff] at he
        simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff]
        exact ⟨iht k hx.1 he.1 hfx.1, ihb (k + 1) hx.2 he.2 hfx.2⟩
    | forallE n t b bi iht ihb =>
      intro k hx he hfx
      cases hc : instLPF ps us (.forallE n t b bi) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none =>
        simp only [emvarS, Bool.or_eq_false_iff] at he
        simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff]
        exact ⟨iht k hx.1 he.1 hfx.1, ihb (k + 1) hx.2 he.2 hfx.2⟩
    | letE n t v b nd iht ihv ihb =>
      intro k hx he hfx
      cases hc : instLPF ps us (.letE n t v b nd) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none =>
        simp only [emvarS, Bool.or_eq_false_iff] at he
        simp only [mapSpec, hc, Option.getD_none, emvarS, Bool.or_eq_false_iff]
        exact ⟨⟨iht k hx.1 he.1.1 hfx.1, ihv k hx.2.1 he.1.2 hfx.2.1⟩, ihb (k + 1) hx.2.2 he.2 hfx.2.2⟩
    | mdata m y ih =>
      intro k hx he hfx
      cases hc : instLPF ps us (.mdata m y) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none => simp only [mapSpec, hc, Option.getD_none]; exact ih k hx he hfx
    | proj s i y ih =>
      intro k hx he hfx
      cases hc : instLPF ps us (.proj s i y) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none => simp only [mapSpec, hc, Option.getD_none]; exact ih k hx he hfx
    | bvar | fvar | mvar | lit =>
      intro k _ he _
      rw [mapSpec_leaf _ k rfl]
      cases hc : instLPF ps us _ k with
      | some r => simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact he
      | none => exact he

/-! ## The relation reads only lookups -/

/-- **`EnvPresI` reads only `find?`**: an environment with the same lookups
and the same axiom policy is related to the same `L`. -/
theorem presI_congr {fe fe' : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (hcore : fe'.coreAxioms = fe.coreAxioms) (hfind : ∀ n, fe'.env.find? n = fe.env.find? n) :
    EnvPresI fe' L := by
  have h := presI_push (fe' := fe') (news := []) (tabs := []) (names := []) hP hcore
    (fun _ h => by cases h) (fun n _ => hfind n) (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  exact h

/-! ## InLean's check of the package -/

/-- The four constants `checkQuotC` adds. -/
@[expose] def quotConstsI : Array Lean.ConstantInfo :=
  #[.quotInfo ⟨⟨quotPin.name, quotPin.lps, quotPin.type⟩, .type⟩,
    .quotInfo ⟨⟨quotMkPin.name, quotMkPin.lps, quotMkPin.type⟩, .ctor⟩,
    .quotInfo ⟨⟨quotLiftPin.name, quotLiftPin.lps, quotLiftPin.type⟩, .lift⟩,
    .quotInfo ⟨⟨quotIndPin.name, quotIndPin.lps, quotIndPin.type⟩, .ind⟩]

/-- **What an accepted `checkQuotC` says**: the four names fresh, the four
pinned constants added. -/
theorem checkQuotC_ok {fe : FEnv} {s s' : CState} {a : Added}
    (h : (checkQuotC fe).run s = .ok (a, s')) :
    fe.env.find? quotPin.name = none ∧ fe.env.find? quotMkPin.name = none ∧
    fe.env.find? quotLiftPin.name = none ∧ fe.env.find? quotIndPin.name = none ∧
    a.consts = quotConstsI := by
  simp only [checkQuotC] at h
  cases hq : quotPredsOk fe <;>
  cases h1 : fe.env.find? quotPin.name <;> cases h2 : fe.env.find? quotMkPin.name <;>
  cases h3 : fe.env.find? quotLiftPin.name <;> cases h4 : fe.env.find? quotIndPin.name <;>
  simp [hq, h1, h2, h3, h4, StateT.run, bind, StateT.bind, pure, StateT.pure, forIn,
    List.forIn'_cons, List.forIn'_nil, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind,
    Except.pure] at h
  exact ⟨rfl, rfl, rfl, rfl, by rw [← h.1]; rfl⟩

/-! ## Closed terms, by evaluation -/

/-- `Expr.RangeOk` as a test. -/
@[expose] def rangeB : Expr → Bool
  | .bvar i => decide (i + 1 ≤ maxRange)
  | .sort u => decide (depthS u ≤ maxLevelDepth)
  | .const _ us => us.all fun u => decide (depthS u ≤ maxLevelDepth)
  | .app f a | .lam _ f a _ | .forallE _ f a _ => rangeB f && rangeB a
  | .letE _ t v b _ => rangeB t && rangeB v && rangeB b
  | .mdata _ x | .proj _ _ x => rangeB x
  | _ => true

theorem RangeOk_of_rangeB : ∀ {e : Expr}, rangeB e = true → Expr.RangeOk e := by
  intro e
  induction e with
  | bvar i => intro h; simpa [rangeB, Expr.RangeOk] using h
  | sort u => intro h; simpa [rangeB, Expr.RangeOk] using h
  | const n us => intro h; simpa [rangeB, Expr.RangeOk] using h
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro h; simp only [rangeB, Bool.and_eq_true] at h; exact ⟨ihf h.1, iha h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [rangeB, Bool.and_eq_true] at h; exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | mdata _ x ih | proj _ _ x ih => intro h; exact ih h
  | fvar | mvar | lit => intro _; trivial

/-- `LvFits` as a test. -/
@[expose] def lvFitsB (md : Nat) : Expr → Bool
  | .sort u => decide (depthS u + md ≤ maxLevelDepth)
  | .const _ ls => ls.all fun u => decide (depthS u + md ≤ maxLevelDepth)
  | .app f a | .lam _ f a _ | .forallE _ f a _ => lvFitsB md f && lvFitsB md a
  | .letE _ t v b _ => lvFitsB md t && lvFitsB md v && lvFitsB md b
  | .mdata _ x | .proj _ _ x => lvFitsB md x
  | _ => true

theorem LvFits_of_lvFitsB {md : Nat} : ∀ {e : Expr}, lvFitsB md e = true → LvFits md e := by
  intro e
  induction e with
  | sort u => intro h; simpa [lvFitsB, LvFits] using h
  | const n us => intro h; simpa [lvFitsB, LvFits] using h
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro h; simp only [lvFitsB, Bool.and_eq_true] at h; exact ⟨ihf h.1, iha h.2⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [lvFitsB, Bool.and_eq_true] at h; exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | mdata _ x ih | proj _ _ x ih => intro h; exact ih h
  | bvar | fvar | mvar | lit => intro _; trivial

/-- **A closed term's level instantiation is stored**, read through con-leche's. -/
theorem storedT_instantiateLevelParams {R : Expr} {C : ConLeche.Expr} (ps : List Name)
    {us : List Level} {cus : List ConLeche.Level}
    (hR : rangeB R = true) (hf : fvarS R = false) (he : emvarS R = false)
    (hc : toExprC R = some C) (hus : toLevels us = some cus)
    (hud : us.all (fun u => decide (depthS u ≤ maxLevelDepth)) = true)
    (hfit : lvFitsB (maxDepthS us) R = true) :
    StoredT (EO.instantiateLevelParams R ps us) (C.instantiateLevelParams (ps.map toName) cus) := by
  have hud' : ∀ u ∈ us, depthS u ≤ maxLevelDepth := by simpa using hud
  have hr := RangeOk_of_rangeB hR
  have hnp := emvarS_instantiateLevelParams ps us hr he hud' (LvFits_of_lvFitsB hfit)
  have ht := toExpr_instantiateLevelParams hr hf hc ps hus hnp
  exact StoredT_of (RangeOk_instantiateLevelParams ps us hr hud') ht

theorem StoredT.of_eq {t : Expr} {c c' : ConLeche.Expr} (h : StoredT t c) (he : c = c') :
    StoredT t c' := he ▸ h

/-! ## The four constants against con-leche's records -/

@[expose] def qTypeI : QuotVal := ⟨⟨quotPin.name, quotPin.lps, quotPin.type⟩, .type⟩
@[expose] def qCtorI : QuotVal := ⟨⟨quotMkPin.name, quotMkPin.lps, quotMkPin.type⟩, .ctor⟩
@[expose] def qLiftI : QuotVal := ⟨⟨quotLiftPin.name, quotLiftPin.lps, quotLiftPin.type⟩, .lift⟩
@[expose] def qIndI : QuotVal := ⟨⟨quotIndPin.name, quotIndPin.lps, quotIndPin.type⟩, .ind⟩

theorem quotConstsI_eq : quotConstsI.toList =
    [.quotInfo qTypeI, .quotInfo qCtorI, .quotInfo qLiftI, .quotInfo qIndI] := rfl

theorem entry_qType (E : Kernel.Environment) : EntryRelI E (.quotInfo qTypeI) ConLeche.quotA :=
  ⟨_, rfl, by decide, by decide, by decide, RangeOk_of_rangeB (by decide), by decide⟩

theorem entry_qCtor (E : Kernel.Environment) : EntryRelI E (.quotInfo qCtorI) ConLeche.quotMkA :=
  ⟨_, rfl, by decide, by decide, by decide, RangeOk_of_rangeB (by decide), by decide⟩

theorem entry_qLift (E : Kernel.Environment) : EntryRelI E (.quotInfo qLiftI) ConLeche.quotLiftA := by
  refine ⟨_, rfl, _, _, rfl, ⟨by decide, by decide, by decide, RangeOk_of_rangeB (by decide), by decide⟩,
    .cons ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩ .nil⟩
  have h := storedT_instantiateLevelParams [BasisDSL.uN, BasisDSL.vN] (R := quotLiftRule)
    (us := [.param BasisDSL.uN, .param BasisDSL.vN]) (by decide) (by decide) (by decide) rfl rfl
    (by decide) (by decide)
  have hq : quotRuleRhs qLiftI =
      EO.instantiateLevelParams quotLiftRule [BasisDSL.uN, BasisDSL.vN]
        [.param BasisDSL.uN, .param BasisDSL.vN] := rfl
  show StoredT (quotRuleRhs qLiftI) _
  rw [hq]
  exact StoredT.of_eq h (by decide)

theorem entry_qInd (E : Kernel.Environment) : EntryRelI E (.quotInfo qIndI) ConLeche.quotIndA := by
  refine ⟨_, rfl, _, _, rfl, ⟨by decide, by decide, by decide, RangeOk_of_rangeB (by decide), by decide⟩,
    .cons ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩ .nil⟩
  have h := storedT_instantiateLevelParams [BasisDSL.uN] (R := quotIndRule)
    (us := [.param BasisDSL.uN]) (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide)
  have hq : quotRuleRhs qIndI =
      EO.instantiateLevelParams quotIndRule [BasisDSL.uN] [.param BasisDSL.uN] := rfl
  show StoredT (quotRuleRhs qIndI) _
  rw [hq]
  exact StoredT.of_eq h (by decide)

/-- **One quotient constant's step**: its record installs one constant, no
table, at its name, related to it in every environment. -/
theorem quotStep {ci : Lean.ConstantInfo} (hci : ci ∈ quotConstsI.toList) {d : ConLeche.Declaration}
    (hd : toDecl [ci] = some d) :
    ConLeche.declTables d = [] ∧ ∃ cci, ConLeche.declConstants d = [cci] ∧
      cci.name = toName ci.name ∧ ∀ E, EntryRelI E ci cci := by
  rw [quotConstsI_eq] at hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · rw [show toDecl [.quotInfo qTypeI] = some (.quotDecl .type ConLeche.quotA.toConstantVal) by decide] at hd
    cases hd
    exact ⟨rfl, _, rfl, by decide, fun E => (show ConLeche.quotAt .type ConLeche.quotA.toConstantVal =
      ConLeche.quotA by decide) ▸ entry_qType E⟩
  · rw [show toDecl [.quotInfo qCtorI] = some (.quotDecl .ctor ConLeche.quotMkA.toConstantVal) by
      decide] at hd
    cases hd
    exact ⟨rfl, _, rfl, by decide, fun E => (show ConLeche.quotAt .ctor ConLeche.quotMkA.toConstantVal =
      ConLeche.quotMkA by decide) ▸ entry_qCtor E⟩
  · rw [show toDecl [.quotInfo qLiftI] = some (.quotDecl .lift ConLeche.quotLiftA.toConstantVal) by
      decide] at hd
    cases hd
    exact ⟨rfl, _, rfl, by decide, fun E => (show ConLeche.quotAt .lift ConLeche.quotLiftA.toConstantVal =
      ConLeche.quotLiftA by decide) ▸ entry_qLift E⟩
  · rw [show toDecl [.quotInfo qIndI] = some (.quotDecl .ind ConLeche.quotIndA.toConstantVal) by
      decide] at hd
    cases hd
    exact ⟨rfl, _, rfl, by decide, fun E => (show ConLeche.quotAt .ind ConLeche.quotIndA.toConstantVal =
      ConLeche.quotIndA by decide) ▸ entry_qInd E⟩

/-- The quotient constants' names are none of `sorryAx`. -/
theorem quot_not_sorry {ci : Lean.ConstantInfo} (hci : ci ∈ quotConstsI.toList) :
    ci.name ≠ InLean.sorryAxName := by
  rw [quotConstsI_eq] at hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl <;>
    exact fun h => absurd (congrArg toName h) (by decide)

/-- The pushes of the quotient constants, one by one. -/
theorem presI_quotFold (hlaws : EnvLaws) :
    ∀ (cs : List Lean.ConstantInfo) (ds : List ConLeche.Declaration) (fe : InLean.FEnv) (L : ConLeche.Env),
      (∀ ci ∈ cs, ci ∈ quotConstsI.toList) → cs.mapM (fun ci => toDecl [ci]) = some ds →
      EnvPresI fe L → (∀ ci ∈ cs, fe.env.find? ci.name = none) → (cs.map (·.name)).Nodup →
      EnvPresI { fe with env := cs.foldl InLean.addConst fe.env }
        (ds.foldl (fun L d => L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) L)
  | [], ds, fe, L, _, hds, hP, _, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hds
    subst hds
    exact hP
  | c :: cs, ds, fe, L, hmem, hds, hP, hfresh, hnd => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hds
    obtain ⟨d, hd, ds', hds', rfl⟩ := hds
    have hc := hmem c List.mem_cons_self
    obtain ⟨ht, cci, hcs, hn, hrel⟩ := quotStep hc hd
    have hP1 : EnvPresI { fe with env := InLean.addConst fe.env c }
        (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) := by
      rw [ht, hcs]
      refine presI_one hlaws hP (hfresh c List.mem_cons_self) ?_
        (.inr ⟨cci, rfl, hn, hrel _, fun h => absurd h (quot_not_sorry hc)⟩)
      rw [quotConstsI_eq] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> intro v h <;> cases h
    simp only [List.map_cons, List.nodup_cons] at hnd
    have := presI_quotFold hlaws cs ds' { fe with env := InLean.addConst fe.env c } _
      (fun ci h => hmem ci (List.mem_cons_of_mem _ h)) hds' hP1 ?_ hnd.2
    · exact this
    · intro ci h
      show (InLean.addConst fe.env c).find? ci.name = none
      rw [find_addConst hlaws (hfresh c List.mem_cons_self)]
      have hne : ci.name ≠ c.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem h)
      simp only [hne, ↓reduceIte]
      exact hfresh ci (List.mem_cons_of_mem _ h)

/-- `markQuot` changes no lookup. -/
theorem markQuot_find (hlaws : EnvLaws) (E : Kernel.Environment) (n : Name) :
    (InLean.markQuot E).find? n = E.find? n := by
  rw [hlaws.2 E (InLean.markQuot E) rfl]

/-- **The quotient group keeps the relation.** -/
theorem quotGroupPres : QuotGroupPres := by
  intro hlaws fe L s s' a ds hP hrun hds
  obtain ⟨h1, h2, h3, h4, ha⟩ := checkQuotC_ok hrun
  rw [ha] at hds ⊢
  have hfold := presI_quotFold hlaws quotConstsI.toList ds fe L (fun _ h => h) hds hP ?_
    (List.Pairwise.of_map (S := fun a b => a ≠ b) toName
      (fun _ _ h e => h (congrArg toName e)) (by decide))
  · refine presI_congr hfold rfl ?_
    intro n
    show (InLean.markQuot _).find? n = _
    rw [markQuot_find hlaws, ← Array.foldl_toList]
  · rw [quotConstsI_eq]
    intro ci hci
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    rcases hci with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

end InLeanProof
