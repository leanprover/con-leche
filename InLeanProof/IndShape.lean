module

public import InLeanProof.IndPres
/- `ConstantInfo.type`/`levelParams` are read as projections of `toConstantVal`. -/
import all Lean.Declaration

/-!
# O7: the inductive block's recogniser at the translation (task #451, lane O7)

InLean's recogniser (`InLean/Inductives/BlockShape.lean`: `blockSplit`,
`blockShape?`, `indParamsOk`, `basisNameHit`) is pure; so is con-leche's
(`ConLeche/Kernel/Inductives/BlockShape.lean`).  A block's terms are closed
(`toBlock` reads them with `toExprC`), so the translation here is the total
closed one, `trC` (`trE` with no free variable), and a whole block reads as
`block.map trCI`; a recognised shape reads as `trShape`.

**Main results.**
* `toBlock_eq`: a block with a record (`toBlock block = some cb`) is
  `block.map trCI`, every constant a former, a constructor or a recursor.
* `blockSplit_tr`: `ConLeche.blockSplit (block.map trCI)` is InLean's split,
  translated, for every list.
* `blockShape?_tr`: the recogniser at the translated block answers the
  translation of InLean's answer, given that the block's types have a reading
  (`okC`, no level metavariable: the comparisons `memberIdxAt?` and the
  result sort's `isEquiv` read levels).
* `indParamsOk_tr`, `basisNameHit_tr`: the two guards in front of it.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## The closed total translation -/

/-- A closed term, translated (a free variable has no reading here; the
block's terms have none). -/
@[expose] def trC (e : Lean.Expr) : ConLeche.Expr := trE (fun _ => none) e

/-- A closed term has a reading: no metavariable, no free variable, in range. -/
@[expose] def okC (e : Lean.Expr) : Bool := okE (fun _ => none) e

@[expose] def trCV (v : Lean.ConstantVal) : ConLeche.ConstantVal :=
  ⟨toName v.name, v.levelParams.map toName, trC v.type⟩

@[expose] def trRule (r : Lean.RecursorRule) : ConLeche.RecRule :=
  ⟨toName r.ctor, r.nfields, .plain, trC r.rhs⟩

/-- A block's constant as the export's record of it (`toBlockRecord`,
total): any other kind reads as an axiom, which no recogniser accepts. -/
@[expose] def trCI : Lean.ConstantInfo → ConLeche.ConstantInfo
  | .inductInfo v => .indInfo (trCV v.toConstantVal) {}
  | .ctorInfo v => .ctorInfo (trCV v.toConstantVal) v.numParams v.numFields
  | .recInfo v => .recInfo (trCV v.toConstantVal) (majorIdxOf v) (rulePrefixOf v) v.k
      (v.rules.map trRule)
  | ci => .axiomInfo (trCV ci.toConstantVal)

/-- A constant is one of a block's kinds. -/
@[expose] def isBlockKind : Lean.ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

theorem trC_of_toExprC {e : Lean.Expr} {c : ConLeche.Expr} (h : toExprC e = some c)
    (hr : Expr.RangeOk e) : okC e = true ∧ trC e = c :=
  okE_of_toExpr (fun _ => none) hr h

theorem toRules_eq : ∀ {rs : List Lean.RecursorRule} {crs : List ConLeche.RecRule},
    toRules rs = some crs → (∀ r ∈ rs, Expr.RangeOk r.rhs) → crs = rs.map trRule
  | [], crs, h, _ => by simp [toRules] at h; simp [h]
  | r :: rs, crs, h, hr => by
    simp only [toRules, toRule, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cr, ⟨c, hc, rfl⟩, crs', hrs, rfl⟩ := h
    rw [toRules_eq hrs (fun r h => hr r (List.mem_cons_of_mem _ h))]
    simp [trRule, (trC_of_toExprC hc (hr r List.mem_cons_self)).2]

theorem toCV_eq {v : Lean.ConstantVal} {cv : ConLeche.ConstantVal} (h : toCV v = some cv)
    (hr : Expr.RangeOk v.type) : cv = trCV v ∧ okC v.type = true := by
  simp only [toCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨h1, h2⟩ := trC_of_toExprC hc hr
  exact ⟨by simp [trCV, h2], h1⟩

/-- A constant's terms are in range (what `constInRange` checks). -/
@[expose] def CIRange : Lean.ConstantInfo → Prop
  | .recInfo v => Expr.RangeOk v.type ∧ ∀ r ∈ v.rules, Expr.RangeOk r.rhs
  | ci => Expr.RangeOk ci.type

theorem CIRange.type : ∀ {ci : Lean.ConstantInfo}, CIRange ci → Expr.RangeOk ci.toConstantVal.type
  | .recInfo _, h => h.1
  | .inductInfo _, h | .ctorInfo _, h | .axiomInfo _, h | .defnInfo _, h | .thmInfo _, h
  | .opaqueInfo _, h | .quotInfo _, h => h

/-- **A block with a record is its total translation**, every constant one
of a block's kinds with a type that has a reading. -/
theorem toBlock_eq : ∀ {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo},
    toBlock block = some cb → (∀ ci ∈ block, CIRange ci) →
    cb = block.map trCI ∧ ∀ ci ∈ block, isBlockKind ci = true ∧ okC ci.toConstantVal.type = true
  | [], cb, h, _ => by simp [toBlock] at h; simp [h]
  | ci :: cs, cb, h, hr => by
    simp only [toBlock, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs', hcs, rfl⟩ := h
    obtain ⟨ih1, ih2⟩ := toBlock_eq hcs (fun c h => hr c (List.mem_cons_of_mem _ h))
    have hci := hr ci List.mem_cons_self
    have key : c = trCI ci ∧ isBlockKind ci = true ∧ okC ci.toConstantVal.type = true := by
      cases ci with
      | inductInfo v =>
        simp only [toBlockRecord, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hc
        obtain ⟨cv, hcv, rfl⟩ := hc
        obtain ⟨h1, h2⟩ := toCV_eq hcv hci
        exact ⟨by simp [trCI, h1], rfl, h2⟩
      | ctorInfo v =>
        simp only [toBlockRecord, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hc
        obtain ⟨cv, hcv, rfl⟩ := hc
        obtain ⟨h1, h2⟩ := toCV_eq hcv hci
        exact ⟨by simp [trCI, h1], rfl, h2⟩
      | recInfo v =>
        simp only [toBlockRecord, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hc
        obtain ⟨cv, hcv, crs, hrs, rfl⟩ := hc
        obtain ⟨h1, h2⟩ := toCV_eq hcv hci.1
        refine ⟨?_, rfl, h2⟩
        simp only [trCI, h1, toRules_eq hrs hci.2, majorIdxOf, rulePrefixOf]
      | axiomInfo _ | defnInfo _ | thmInfo _ | opaqueInfo _ | quotInfo _ =>
        simp [toBlockRecord] at hc
    refine ⟨by simp [key.1, ih1], ?_⟩
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact key.2
    · exact ih2 c' hc'

/-- A block constant's terms have a closed reading: its type, and a recursor's
rules. -/
@[expose] def CIOk : Lean.ConstantInfo → Prop
  | .recInfo v => okC v.type = true ∧ ∀ r ∈ v.rules, okC r.rhs = true
  | ci => okC ci.toConstantVal.type = true

theorem toRules_okC : ∀ {rs : List Lean.RecursorRule} {crs : List ConLeche.RecRule},
    toRules rs = some crs → (∀ r ∈ rs, Expr.RangeOk r.rhs) → ∀ r ∈ rs, okC r.rhs = true
  | [], _, _, _ => by simp
  | r :: rs, crs, h, hr => by
    simp only [toRules, toRule, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cr, ⟨c, hc, rfl⟩, crs', hrs, rfl⟩ := h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (trC_of_toExprC hc (hr _ List.mem_cons_self)).1
    · exact toRules_okC hrs (fun r h => hr r (List.mem_cons_of_mem _ h)) x hx

/-- **A block with a record has closed readings throughout.** -/
theorem toBlock_CIOk : ∀ {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo},
    toBlock block = some cb → (∀ ci ∈ block, CIRange ci) → ∀ ci ∈ block, CIOk ci
  | [], _, _, _ => by simp
  | ci :: cs, cb, h, hr => by
    simp only [toBlock, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs', hcs, rfl⟩ := h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have hk := (toBlock_eq (block := [x]) (cb := [c]) (by simp [toBlock, hc])
        (by simpa using hr x List.mem_cons_self)).2 x List.mem_cons_self
      cases x with
      | recInfo v =>
        simp only [toBlockRecord, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hc
        obtain ⟨_, _, crs, hrs, rfl⟩ := hc
        exact ⟨hk.2, toRules_okC hrs (hr _ List.mem_cons_self).2⟩
      | inductInfo _ | ctorInfo _ | axiomInfo _ | defnInfo _ | thmInfo _ | opaqueInfo _
      | quotInfo _ => exact hk.2
    · exact toBlock_CIOk hcs (fun c h => hr c (List.mem_cons_of_mem _ h)) x hx

/-! ## Names and levels -/

theorem findIdx?_map_toName (l : List Lean.Name) (n : Lean.Name) :
    (l.map toName).findIdx? (· == toName n) = l.findIdx? (· == n) := by
  rw [List.findIdx?_map]
  congr 1
  funext a
  simp only [Function.comp_apply]
  rw [toName_beq]

/-- `trL` reads a level parameter back exactly (no `okL` needed: a
metavariable reads as `zero`). -/
theorem trL_eq_param {u : Lean.Level} {n : Lean.Name} :
    trL u = .param (toName n) ↔ u = .param n := by
  constructor
  · intro h
    cases u <;> simp [trL] at h
    rw [toName_inj h]
  · rintro rfl; rfl

theorem levels_beq_params (us : List Lean.Level) (lps : List Lean.Name) :
    (us.map trL == (lps.map toName).map ConLeche.Level.param) = (us == lps.map Level.param) := by
  induction us generalizing lps with
  | nil => cases lps <;> rfl
  | cons u us ih =>
    cases lps with
    | nil => rfl
    | cons n lps =>
      simp only [List.map_cons, List.cons_beq_cons, ih]
      by_cases h : u = .param n
      · subst h; simp [trL]
      · have : trL u ≠ .param (toName n) := fun he => h (trL_eq_param.1 he)
        rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr this]

theorem isEquiv_trL {l r : Lean.Level} (hl : okL l = true) (hr : okL r = true) :
    Lvl.isEquiv l r = ConLeche.Level.isEquiv (trL l) (trL r) := by
  unfold Lvl.isEquiv ConLeche.Level.isEquiv Lvl.leq ConLeche.Level.leq
  rw [beq_eq_decide_trL hl hr, beq_eq_decide_trL (okL_simplify hl) (okL_simplify hr),
    trL_simplify hl, trL_simplify hr,
    leqCore_trL _ _ _ _ (okL_simplify hl) (okL_simplify hr),
    leqCore_trL _ _ _ _ (okL_simplify hr) (okL_simplify hl),
    trL_simplify hl, trL_simplify hr, defaultFuel_eq]
  by_cases h1 : trL l = trL r
  · simp [h1]
  · by_cases h2 : ConLeche.Level.simplify (trL l) = ConLeche.Level.simplify (trL r)
    · simp [h1, h2]
    · simp [h1, h2]

/-! ## Telescopes through the closed translation -/

theorem okC_forallE {n : Lean.Name} {d b : Lean.Expr} {bi : BinderInfo} :
    okC (.forallE n d b bi) = (okC d && okC b) := rfl

theorem okC_mdata {m : MData} {e : Lean.Expr} : okC (.mdata m e) = okC e := rfl

/-- `stripPis` commutes with the closed translation. -/
theorem stripPis_tr : ∀ (n : Nat) (e : Lean.Expr),
    ConLeche.Expr.stripPis n (trC e) =
      (InLean.stripPis n e).map fun (ds, r) => (ds.map trC, trC r)
  | 0, e => by simp [InLean.stripPis, ConLeche.Expr.stripPis]
  | n + 1, .forallE _ d b _ => by
    simp only [InLean.stripPis, ConLeche.Expr.stripPis, trC, trE]
    rw [show trE (fun _ => none) b = trC b from rfl, stripPis_tr n b]
    cases InLean.stripPis n b <;> simp [trC]
  | n + 1, .mdata _ e => by
    simp only [InLean.stripPis]
    exact stripPis_tr (n + 1) e
  | _ + 1, .bvar _ | _ + 1, .fvar _ | _ + 1, .mvar _ | _ + 1, .sort _ | _ + 1, .const _ _
  | _ + 1, .app _ _ | _ + 1, .lam _ _ _ _ | _ + 1, .letE _ _ _ _ _ | _ + 1, .lit _
  | _ + 1, .proj _ _ _ => by
    simp [InLean.stripPis, ConLeche.Expr.stripPis, trC, trE]

theorem stripPis_okC : ∀ {n : Nat} {e : Lean.Expr} {ds : List Lean.Expr} {r : Lean.Expr},
    okC e = true → InLean.stripPis n e = some (ds, r) → okC r = true
  | 0, e, ds, r, h, hs => by simp [InLean.stripPis] at hs; rw [← hs.2]; exact h
  | n + 1, .forallE _ d b _, ds, r, h, hs => by
    simp only [InLean.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨ds', r'⟩, h1, h2⟩ := hs
    simp only [Prod.mk.injEq] at h2
    rw [← h2.2]
    rw [okC_forallE, Bool.and_eq_true] at h
    exact stripPis_okC h.2 h1
  | n + 1, .mdata _ e, ds, r, h, hs => by
    simp only [InLean.stripPis] at hs
    rw [okC_mdata] at h
    exact stripPis_okC (n := n + 1) h hs
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _, _, _, _, hs | _ + 1, .mvar _, _, _, _, hs
  | _ + 1, .sort _, _, _, _, hs | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs
  | _ + 1, .lam _ _ _ _, _, _, _, hs | _ + 1, .letE _ _ _ _ _, _, _, _, hs
  | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs => by
    simp [InLean.stripPis] at hs
termination_by _ e => sizeOf e

theorem piBinders_tr : ∀ (e : Lean.Expr),
    ConLeche.Expr.piBinders (trC e) =
      ((InLean.piBinders e).1.map trC, trC (InLean.piBinders e).2)
  | .forallE _ d b _ => by
    simp only [InLean.piBinders, ConLeche.Expr.piBinders, trC, trE]
    rw [show trE (fun _ => none) b = trC b from rfl, piBinders_tr b]
    simp [trC]
  | .mdata _ e => by simp only [InLean.piBinders]; exact piBinders_tr e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => by
    simp [InLean.piBinders, ConLeche.Expr.piBinders, trC, trE]

theorem piSortTeleLen?_tr : ∀ (e : Lean.Expr),
    ConLeche.Expr.piSortTeleLen? (trC e) = InLean.piSortTeleLen? e
  | .forallE _ d b _ => by
    simp only [InLean.piSortTeleLen?, ConLeche.Expr.piSortTeleLen?, trC, trE]
    rw [show trE (fun _ => none) b = trC b from rfl, piSortTeleLen?_tr b]
  | .mdata _ e => by simp only [InLean.piSortTeleLen?]; exact piSortTeleLen?_tr e
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => by
    simp [InLean.piSortTeleLen?, ConLeche.Expr.piSortTeleLen?, trC, trE]

theorem trC_stripTop (e : Lean.Expr) : trC (EO.stripTop e) = trC e := by
  induction e <;> simp_all [EO.stripTop, trC, trE]

theorem getAppFn_tr (e : Lean.Expr) : (trC e).getAppFn = trC (Expr.getAppFnT e) := by
  induction e with
  | app f a ihf _ => simp only [trC, trE, ConLeche.Expr.getAppFn, Expr.getAppFnT]; exact ihf
  | mdata _ e ih => simp only [Expr.getAppFnT]; exact ih
  | _ => simp [trC, trE, ConLeche.Expr.getAppFn, Expr.getAppFnT]

theorem trC_const_iff {x : Lean.Expr} (hx : ∀ m b, x ≠ .mdata m b) {n : ConLeche.Name}
    {us : List ConLeche.Level} :
    trC x = .const n us ↔ ∃ n' us', x = .const n' us' ∧ n = toName n' ∧ us = us'.map trL := by
  constructor
  · intro h
    cases x <;> simp [trC, trE] at h
    case const n' us' => exact ⟨n', us', rfl, h.1.symm, h.2.symm⟩
    case mdata m b => exact absurd rfl (hx m b)
  · rintro ⟨n', us', rfl, rfl, rfl⟩; rfl

/-! ## Recognition at the translation -/

theorem reservedBasisNames_tr :
    ConLeche.reservedBasisNames = InLean.reservedBasisNames.map toName := rfl

theorem reserved_tr (n : Lean.Name) :
    ConLeche.reservedBasisNames.contains (toName n) = InLean.reservedBasisNames.contains n := by
  rw [reservedBasisNames_tr, contains_map_toName]

theorem memberIdxAt?_tr (names lps : List Lean.Name) : ∀ (e : Lean.Expr),
    ConLeche.memberIdxAt? (names.map toName) ((lps.map toName).map .param) (trC e) =
      InLean.memberIdxAt? names (lps.map .param) e
  | .mdata _ e => by simp only [InLean.memberIdxAt?]; exact memberIdxAt?_tr names lps e
  | .const n us => by
    simp only [trC, trE, ConLeche.memberIdxAt?, InLean.memberIdxAt?]
    rw [levels_beq_params, findIdx?_map_toName]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .app _ _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ _ | .lit _ | .proj _ _ _ => by
    simp [trC, trE, ConLeche.memberIdxAt?, InLean.memberIdxAt?]

/-- The recursor parts, translated. -/
@[expose] def trParts (r : InLean.RecParts) :
    ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule :=
  (trCV r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.map trRule)

@[expose] def trCtorParts (c : Lean.ConstantVal × Nat × Nat) : ConLeche.ConstantVal × Nat × Nat :=
  (trCV c.1, c.2.1, c.2.2)

theorem blockSplitRecs_tr : ∀ (l : List Lean.ConstantInfo),
    ConLeche.blockSplitRecs (l.map trCI) = (InLean.blockSplitRecs l).map (·.map trParts)
  | [] => rfl
  | .recInfo v :: rest => by
    simp only [List.map_cons, trCI, ConLeche.blockSplitRecs, InLean.blockSplitRecs,
      blockSplitRecs_tr rest, Option.map_map]
    cases InLean.blockSplitRecs rest <;> rfl
  | .inductInfo _ :: _ | .ctorInfo _ :: _ | .axiomInfo _ :: _ | .defnInfo _ :: _
  | .thmInfo _ :: _ | .opaqueInfo _ :: _ | .quotInfo _ :: _ => rfl

theorem blockSplitCtors_tr : ∀ (l : List Lean.ConstantInfo),
    ConLeche.blockSplitCtors (l.map trCI) =
      (InLean.blockSplitCtors l).map fun q => (q.1.map trCtorParts, q.2.map trParts)
  | .ctorInfo v :: rest => by
    simp only [List.map_cons, trCI, ConLeche.blockSplitCtors, InLean.blockSplitCtors,
      blockSplitCtors_tr rest, Option.map_map]
    cases InLean.blockSplitCtors rest <;> rfl
  | [] => by
    simp only [List.map_nil, ConLeche.blockSplitCtors, InLean.blockSplitCtors]
    rfl
  | .recInfo v :: rest => by
    rw [List.map_cons]
    simp only [trCI, ConLeche.blockSplitCtors, InLean.blockSplitCtors]
    have := blockSplitRecs_tr (.recInfo v :: rest)
    simp only [List.map_cons, trCI] at this
    rw [this, Option.map_map, Option.map_map]; rfl
  | .inductInfo _ :: _ | .axiomInfo _ :: _ | .defnInfo _ :: _
  | .thmInfo _ :: _ | .opaqueInfo _ :: _ | .quotInfo _ :: _ => rfl

theorem blockSplit_tr : ∀ (l : List Lean.ConstantInfo),
    ConLeche.blockSplit (l.map trCI) =
      (InLean.blockSplit l).map fun q => (q.1.map trCV, q.2.1.map trCtorParts, q.2.2.map trParts)
  | .inductInfo v :: rest => by
    simp only [List.map_cons, trCI, ConLeche.blockSplit, InLean.blockSplit,
      blockSplit_tr rest, Option.map_map]
    cases InLean.blockSplit rest <;> rfl
  | [] => by
    simp only [List.map_nil, ConLeche.blockSplit, InLean.blockSplit]
    rfl
  | .ctorInfo v :: rest => by
    simp only [InLean.blockSplit]
    have := blockSplitCtors_tr (.ctorInfo v :: rest)
    simp only [List.map_cons, trCI] at this ⊢
    rw [show ∀ x l, ConLeche.blockSplit (x :: l) = match x with
      | .indInfo cvT _ => (ConLeche.blockSplit l).map fun q => (cvT :: q.1, q.2)
      | _ => (ConLeche.blockSplitCtors (x :: l)).map fun q => ([], q.1, q.2) from
        fun x l => by cases x <;> rfl]
    simp only []
    rw [this, Option.map_map, Option.map_map]; rfl
  | .recInfo v :: rest => by
    simp only [InLean.blockSplit]
    have := blockSplitCtors_tr (.recInfo v :: rest)
    simp only [List.map_cons, trCI] at this ⊢
    rw [show ∀ x l, ConLeche.blockSplit (x :: l) = match x with
      | .indInfo cvT _ => (ConLeche.blockSplit l).map fun q => (cvT :: q.1, q.2)
      | _ => (ConLeche.blockSplitCtors (x :: l)).map fun q => ([], q.1, q.2) from
        fun x l => by cases x <;> rfl]
    simp only []
    rw [this, Option.map_map, Option.map_map]; rfl
  | .axiomInfo _ :: _ | .defnInfo _ :: _ | .thmInfo _ :: _ | .opaqueInfo _ :: _
  | .quotInfo _ :: _ => rfl

/-- The stripped telescope's rest, read through `mdata`: never an `mdata`. -/
theorem stripTop_ne_mdata' (e : Lean.Expr) (m : MData) (b : Lean.Expr) :
    EO.stripTop e ≠ .mdata m b := fun h => stripTop_ne_mdata h

theorem recTargetOf_tr (names : List Lean.Name) (mI : Nat) (ty : Lean.Expr) :
    ConLeche.recTargetOf (names.map toName) mI (trC ty) = InLean.recTargetOf names mI ty := by
  unfold ConLeche.recTargetOf InLean.recTargetOf
  rw [stripPis_tr]
  cases InLean.stripPis mI ty with
  | none => simp
  | some q =>
    obtain ⟨ds, r⟩ := q
    simp only [Option.map_some]
    try rw [← trC_stripTop r]
    generalize hx : EO.stripTop r = x
    have hxm : ∀ m b, x ≠ .mdata m b := hx ▸ stripTop_ne_mdata' r
    cases x with
    | forallE _ dom b _ =>
      simp only [trC, trE]
      rw [show trE (fun _ => none) dom = trC dom from rfl, getAppFn_tr]
      generalize hh : Expr.getAppFnT dom = h
      have hhm : ∀ m b, h ≠ .mdata m b := fun m b he => getAppFnT_ne_mdata (hh.trans he)
      cases h with
      | const n us =>
        simp only [trC, trE, findIdx?_map_toName, List.length_map]
      | mdata m b => exact absurd rfl (hhm m b)
      | _ => simp [trC, trE]
    | mdata m b => exact absurd rfl (hxm m b)
    | _ => simp [trC, trE]

theorem recTargetOf_tr' (L : List Lean.ConstantVal) (mI : Nat) (ty : Lean.Expr) :
    ConLeche.recTargetOf (L.map fun x => toName x.name) mI (trC ty) =
      InLean.recTargetOf (L.map (·.name)) mI ty := by
  rw [← recTargetOf_tr, List.map_map]; rfl

theorem blockCounts?_tr (nPd k nC nR : Nat) (cvT : Lean.ConstantVal) (r : Option (Nat × Nat)) :
    ConLeche.blockCounts? nPd k nC nR (trCV cvT) r = InLean.blockCounts? nPd k nC nR cvT r := by
  unfold ConLeche.blockCounts? InLean.blockCounts?
  simp only [trCV]
  rw [piBinders_tr]
  have hne : ∀ m b, (InLean.piBinders cvT.type).2 ≠ .mdata m b := by
    generalize cvT.type = e
    intro m b
    induction e <;> simp_all [InLean.piBinders]
  generalize InLean.piBinders cvT.type = q at hne
  obtain ⟨bs, x⟩ := q
  cases x with
  | sort u => simp [trC, trE]
  | mdata m b => exact absurd rfl (hne m b)
  | _ => simp only [trC, trE, Option.getD_none] <;> rfl

theorem ctorMember?_tr (names lps : List Lean.Name) (nP : Nat) (c : Lean.ConstantVal × Nat) :
    ConLeche.ctorMember? (names.map toName) (lps.map toName) nP (trCV c.1, c.2) =
      InLean.ctorMember? names lps nP c := by
  unfold ConLeche.ctorMember? InLean.ctorMember?
  simp only [trCV]
  rw [stripPis_tr]
  cases InLean.stripPis (nP + c.2) c.1.type with
  | none => rfl
  | some q =>
    simp only [Option.map_some]
    rw [getAppFn_tr]
    exact memberIdxAt?_tr names lps _

@[expose] def trCtor (c : Lean.ConstantVal × Nat) : ConLeche.ConstantVal × Nat := (trCV c.1, c.2)

theorem blockGroups_tr (names lps : List Lean.Name) (nP k : Nat) (cs : List (Lean.ConstantVal × Nat)) :
    ConLeche.blockGroups (names.map toName) (lps.map toName) nP k (cs.map trCtor) =
      (InLean.blockGroups names lps nP k cs).map (·.map trCtor) := by
  unfold ConLeche.blockGroups InLean.blockGroups
  split
  · simp
  · simp only [List.map_map]
    congr 1
    funext m
    simp only [Function.comp_apply, List.filter_map]
    congr 2
    funext c
    simp only [Function.comp_apply, trCtor]
    rw [ctorMember?_tr]

theorem blockMemberCounts?_tr (nPd k nC : Nat) (names : List Lean.Name) (rs : List InLean.RecParts) :
    ∀ (m : Nat) (ts : List Lean.ConstantVal),
      ConLeche.blockMemberCounts? nPd k nC (names.map toName) (rs.map trParts) m (ts.map trCV) =
        InLean.blockMemberCounts? nPd k nC names rs m ts
  | _, [] => rfl
  | m, cvT :: ts => by
    simp only [List.map_cons, ConLeche.blockMemberCounts?, InLean.blockMemberCounts?, List.length_map]
    have hfind : ((rs.map trParts).find? fun q =>
        ConLeche.recTargetOf (names.map toName) q.2.1 q.1.type == m).map (fun q => (q.2.1, q.2.2.1)) =
        (rs.find? fun q => InLean.recTargetOf names q.2.1 q.1.type == m).map
          (fun q => (q.2.1, q.2.2.1)) := by
      rw [List.find?_map, Option.map_map]
      have : ((fun q : ConLeche.ConstantVal × Nat × Nat × Bool × List ConLeche.RecRule =>
          ConLeche.recTargetOf (names.map toName) q.2.1 q.1.type == m) ∘ trParts) =
          fun q => InLean.recTargetOf names q.2.1 q.1.type == m := by
        funext q; simp only [Function.comp_apply, trParts, trCV]; rw [recTargetOf_tr]
      rw [this]; rfl
    rw [hfind, blockCounts?_tr]
    cases InLean.blockCounts? nPd k nC rs.length cvT _ with
    | none => rfl
    | some c => simp only [blockMemberCounts?_tr nPd k nC names rs (m + 1) ts]

theorem blockSplit_head {block : List Lean.ConstantInfo} {cvT0 : Lean.ConstantVal}
    {tl : List Lean.ConstantVal} {cs rs}
    (h : InLean.blockSplit block = some (cvT0 :: tl, cs, rs)) :
    ∃ v rest, block = .inductInfo v :: rest ∧ v.toConstantVal = cvT0 := by
  match block, h with
  | .inductInfo v :: rest, h =>
    simp only [InLean.blockSplit] at h
    cases hq : InLean.blockSplit rest with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
      exact ⟨v, rest, rfl, h.1.1⟩
  | [], h => simp [InLean.blockSplit, InLean.blockSplitCtors, InLean.blockSplitRecs] at h
  | .ctorInfo v :: rest, h | .recInfo v :: rest, h | .axiomInfo v :: rest, h
  | .defnInfo v :: rest, h | .thmInfo v :: rest, h | .opaqueInfo v :: rest, h
  | .quotInfo v :: rest, h =>
    unfold InLean.blockSplit at h
    simp at h

@[simp] theorem trCV_name (v : Lean.ConstantVal) : (trCV v).name = toName v.name := rfl
@[simp] theorem trCV_levelParams (v : Lean.ConstantVal) :
    (trCV v).levelParams = v.levelParams.map toName := rfl
@[simp] theorem trCV_type (v : Lean.ConstantVal) : (trCV v).type = trC v.type := rfl

theorem names_trCV (l : List Lean.ConstantVal) :
    (l.map trCV).map (·.name) = (l.map (·.name)).map toName := by
  simp [trCV]

theorem okL_of_okC_sort {u : Lean.Level} (h : okC (.sort u) = true) : okL u = true := by
  simp only [okC, okE, okLv, Bool.and_eq_true] at h; exact h.1

/-! ## The recognised shape, translated -/

@[expose] def trMember (ms : InLean.MemberShape) : ConLeche.MemberShape :=
  ⟨trCV ms.cvT, trCV ms.declared, ms.nIdx, ms.ctors.map trCtor⟩

@[expose] def trRec (rc : InLean.RecShape) : ConLeche.RecShape :=
  ⟨trCV rc.cvR, rc.rP, rc.mI, rc.tgt, rc.rules.map trRule, rc.isK⟩

/-- **A recognised shape, translated.** -/
@[expose] def trShape (p : InLean.BlockShape) : ConLeche.BlockShape :=
  ⟨p.members.map trMember, p.recs.map trRec, p.nP, toName p.elim, trL p.resSort, p.large, p.isProp⟩


theorem members_tr (L : List Lean.ConstantVal) (nIdxs : List Nat)
    (G : List (List (Lean.ConstantVal × Nat))) :
    List.map (fun (a : (ConLeche.ConstantVal × Nat) × List (ConLeche.ConstantVal × Nat)) =>
        ({ cvT := a.1.1, declared := a.1.1, nIdx := a.1.2, ctors := a.2 } : ConLeche.MemberShape))
      (((L.map trCV).zip nIdxs).zip (G.map fun x => x.map trCtor)) =
    (List.map (fun (a : (Lean.ConstantVal × Nat) × List (Lean.ConstantVal × Nat)) =>
        ({ cvT := a.1.1, declared := a.1.1, nIdx := a.1.2, ctors := a.2 } : InLean.MemberShape))
      ((L.zip nIdxs).zip G)).map trMember := by
  induction L generalizing nIdxs G with
  | nil => rfl
  | cons c L ih =>
    cases nIdxs with
    | nil => rfl
    | cons n nIdxs =>
      cases G with
      | nil => rfl
      | cons g G =>
        simp only [List.map_cons, List.zip_cons_cons]
        rw [ih]; rfl

theorem isEquiv_zero_tr {s : Lean.Level} (h : okL s = true) :
    ConLeche.Level.isEquiv (trL s) .zero = Lvl.isEquiv s .zero :=
  (isEquiv_trL (r := .zero) h rfl).symm

theorem okC_stripTop (e : Lean.Expr) : okC (EO.stripTop e) = okC e := by
  induction e <;> simp_all [EO.stripTop, okC, okE]

theorem shape_eq_of {M : List ConLeche.MemberShape} {M' : List InLean.MemberShape}
    {R : List ConLeche.RecShape} {R' : List InLean.RecShape} {nP : Nat} {X : ConLeche.Name}
    {X' : Lean.Name} {lg : Bool} {sC : ConLeche.Level} {sI : Lean.Level}
    (hM : M = M'.map trMember) (hR : R = R'.map trRec) (hX : X = toName X')
    (hs : sC = trL sI) (hok : okL sI = true) :
    some (⟨M, R, nP, X, sC, lg, ConLeche.Level.isEquiv sC .zero == some true⟩ :
      ConLeche.BlockShape) =
    some (trShape ⟨M', R', nP, X', sI, lg, Lvl.isEquiv sI .zero == some true⟩) := by
  subst hM hR hX hs
  simp only [trShape, isEquiv_zero_tr hok]

/-- The result sort's two readings (a local closing step, used three times
below: the matches are `blockShape?`'s own, so no lemma can name them). -/
local macro "sort_tac " h:term : tactic => `(tactic| (
  try rw [stripPis_tr]
  cases hst : InLean.stripPis _ _ with
  | none => rfl
  | some q =>
    obtain ⟨ds, r⟩ := q
    have hokr : okC (EO.stripTop r) = true := by
      rw [okC_stripTop]; exact stripPis_okC $h hst
    have hm := stripTop_ne_mdata' r
    simp only [Option.map_some]
    try rw [← trC_stripTop r]
    generalize EO.stripTop r = x at hokr hm
    cases x with
    | sort u => first | rfl | exact okL_of_okC_sort hokr
    | mdata m b => exact absurd rfl (hm m b)
    | _ => rfl))

/-- **The recogniser at the translation**: con-leche's `blockShape?` on the
translated block answers InLean's shape, translated, given that the former
types have a reading. -/
theorem blockShape?_tr (nPd : Nat) (block : List Lean.ConstantInfo)
    (hok : ∀ ci ∈ block, okC ci.toConstantVal.type = true) :
    ConLeche.blockShape? nPd (block.map trCI) = (InLean.blockShape? nPd block).map trShape := by
  unfold ConLeche.blockShape? InLean.blockShape?
  rw [blockSplit_tr]
  cases hsp : InLean.blockSplit block with
  | none => rfl
  | some q =>
    obtain ⟨cvTs, cs, rs⟩ := q
    simp only [Option.map_some]
    cases cvTs with
    | nil => cases rs <;> rfl
    | cons cvT0 tl =>
      cases rs with
      | nil => rfl
      | cons r0 rtl =>
        obtain ⟨v, rest, rfl, hv⟩ := blockSplit_head hsp
        have hok0 : okC cvT0.type = true := hv ▸ hok _ List.mem_cons_self
        simp only [List.map_cons]
        simp only [← List.map_cons, List.length_map, names_trCV, trCV_name, trCV_levelParams,
          trCV_type]
        rw [blockMemberCounts?_tr]
        have hgrp : List.map (fun c => (c.1, c.2.2)) (List.map trCtorParts cs) =
            (cs.map fun c => (c.1, c.2.2)).map trCtor := by
          simp [trCtorParts, trCtor]
        rw [hgrp, blockGroups_tr]
        simp only [recTargetOf_tr, trParts, trCV_type]
        generalize hL : cvT0 :: tl = L
        generalize hR : rtl = R
        cases InLean.blockMemberCounts? nPd L.length cs.length (L.map (·.name)) (r0 :: R) 0 L with
        | none => rfl
        | some nIdxs =>
          simp only [List.all_map, Function.comp_def, trCV_levelParams,
            map_toName_beq, trCtorParts, trParts, List.map_map, trCV_type]
          have hsort := hok0
          by_cases hc : ((L.all fun x => x.levelParams == cvT0.levelParams) &&
            cs.all fun x => x.2.1 == nPd && x.1.levelParams == cvT0.levelParams) = true
          · simp only [hc, ↓reduceIte, recTargetOf_tr']
            cases hlp : r0.1.levelParams with
            | nil =>
              simp only [List.map_nil, Option.map_some]
              refine shape_eq_of (members_tr _ _ _) (by simp [trRec]) rfl ?_ ?_ <;> sort_tac hsort
            | cons elim relps =>
              simp only [List.map_cons, map_toName_beq, contains_map_toName]
              by_cases hl : (relps == cvT0.levelParams && !cvT0.levelParams.contains elim) = true
              · simp only [hl, ↓reduceIte, Option.map_some]
                refine shape_eq_of (members_tr _ _ _) (by simp [trRec]) rfl ?_ ?_ <;> sort_tac hsort
              · simp only [hl, Bool.false_eq_true, ↓reduceIte, Option.map_some]
                refine shape_eq_of (members_tr _ _ _) (by simp [trRec]) rfl ?_ ?_ <;> sort_tac hsort
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl

/-! ## The guards in front of the recogniser -/

@[simp] theorem trCI_name (ci : Lean.ConstantInfo) : (trCI ci).name = toName ci.name := by
  cases ci <;> rfl

/-- **The declared parameter count's guard** at the translation. -/
theorem indParamsOk_tr (nP : Nat) (block : List Lean.ConstantInfo) :
    ConLeche.indParamsOk nP (block.map trCI) = InLean.indParamsOk nP block := by
  unfold ConLeche.indParamsOk InLean.indParamsOk
  rw [List.all_map]
  congr 1
  funext ci
  cases ci with
  | inductInfo v =>
    simp only [Function.comp_apply, trCI, trCV_type, piSortTeleLen?_tr]
    cases InLean.piSortTeleLen? v.type <;> rfl
  | ctorInfo v => rfl
  | recInfo v => rfl
  | axiomInfo _ | defnInfo _ | thmInfo _ | opaqueInfo _ | quotInfo _ => rfl

/-- The pinned kinds, translated. -/
@[expose] def trKind : InLean.BasisKind → ConLeche.BasisKind
  | .eqK => .eqK
  | .natK => .natK
  | .emptyK => .emptyK
  | .falseK => .falseK

theorem decls_names_tr (k : InLean.BasisKind) :
    (trKind k).decls.map (·.name) = (k.decls.map (·.name)).map toName := by
  cases k <;> rfl

/-- **The pinned blocks' recognition by name** at the translation. -/
theorem basisNameHit_tr (block : List Lean.ConstantInfo) :
    ConLeche.basisNameHit (block.map trCI) = (InLean.basisNameHit block).map trKind := by
  unfold ConLeche.basisNameHit InLean.basisNameHit
  have h : ∀ k : InLean.BasisKind,
      ((trKind k).decls.map (·.name) == (block.map trCI).map (·.name)) =
        (k.decls.map (·.name) == block.map (·.name)) := by
    intro k
    rw [decls_names_tr, List.map_map (f := trCI)]
    rw [show ((·.name) ∘ trCI : Lean.ConstantInfo → ConLeche.Name) = toName ∘ (·.name) from
      funext fun ci => trCI_name ci, ← List.map_map, map_toName_beq]
  have h1 := h .eqK; have h2 := h .natK; have h3 := h .emptyK; have h4 := h .falseK
  simp only [trKind] at h1 h2 h3 h4
  simp only [List.find?_cons, List.find?_nil, h1, h2, h3, h4]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

end InLeanProof
