module

public import InLeanProof.Ops
/- `Expr.updateSort!`/`updateConst!` are `@[implemented_by]` definitions whose
bodies `Lean.Expr` does not expose; the level walk's range lemma reads them
(the logical body: the node rebuilt with the new levels). -/
import all Lean.Expr

/-!
# O9: what the checker builds stays in range (task #451, lane P1)

The cached fields InLean's cutoffs read mean what the walks compute on a term
in range (`Expr.RangeOk`, `InLeanProof/Fields.lean`).  The operations that
build terms keep a term in range:

* instantiation at closed, in-range values (`RangeOk_instantiate`; every
  checker site) — it only lowers indices;
* abstraction by depth (`RangeOk_abstractDepthsFrom`) — an index past C's
  bound becomes `EO.rangePoison`, a metavariable, which its call site reports;
* level instantiation **only under a depth condition**
  (`RangeOk_instantiateLevelParams`): `Lvl.subst` can deepen a level past
  C's bound (`depthS_subst_le` bounds the growth by the values' depth), and
  nothing at run time stops it.  At run time C's `Level.mkData` would abort
  first; in the logic the term exists and its cached fields are unspecified.
  A proof of the checker needs either a check at the call sites or a bound on
  the input levels; see the lane P1 record in DESIGN.md.
-/

public section

namespace InLeanProof

open Lean InLean

/-- **A walk keeps a term in range** when its callback answers in range on an
input in range. -/
theorem RangeOk_mapSpec (f : Expr → Nat → Option Expr)
    (hf : ∀ x k r, Expr.RangeOk x → f x k = some r → Expr.RangeOk r) :
    ∀ (e : Expr) (k : Nat), Expr.RangeOk e → Expr.RangeOk (mapSpec f e k) := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k hr
    cases hc : f (.app g a) k with
    | some r => rw [mapSpec_eq_of_some hc]; exact hf _ _ _ hr hc
    | none => simp only [mapSpec, hc, Option.getD_none]; exact ⟨ihg k hr.1, iha k hr.2⟩
  | lam n t b bi iht ihb =>
    intro k hr
    cases hc : f (.lam n t b bi) k with
    | some r => rw [mapSpec_eq_of_some hc]; exact hf _ _ _ hr hc
    | none => simp only [mapSpec, hc, Option.getD_none]; exact ⟨iht k hr.1, ihb (k + 1) hr.2⟩
  | forallE n t b bi iht ihb =>
    intro k hr
    cases hc : f (.forallE n t b bi) k with
    | some r => rw [mapSpec_eq_of_some hc]; exact hf _ _ _ hr hc
    | none => simp only [mapSpec, hc, Option.getD_none]; exact ⟨iht k hr.1, ihb (k + 1) hr.2⟩
  | letE n t v b nd iht ihv ihb =>
    intro k hr
    cases hc : f (.letE n t v b nd) k with
    | some r => rw [mapSpec_eq_of_some hc]; exact hf _ _ _ hr hc
    | none =>
      simp only [mapSpec, hc, Option.getD_none]
      exact ⟨iht k hr.1, ihv k hr.2.1, ihb (k + 1) hr.2.2⟩
  | mdata m x ih =>
    intro k hr
    cases hc : f (.mdata m x) k with
    | some r => rw [mapSpec_eq_of_some hc]; exact hf _ _ _ hr hc
    | none => simp only [mapSpec, hc, Option.getD_none]; exact ih k hr
  | proj s i x ih =>
    intro k hr
    cases hc : f (.proj s i x) k with
    | some r => rw [mapSpec_eq_of_some hc]; exact hf _ _ _ hr hc
    | none => simp only [mapSpec, hc, Option.getD_none]; exact ih k hr
  | bvar | fvar | mvar | sort | const | lit =>
    intro k hr
    rw [mapSpec_leaf f k rfl]
    cases hc : f _ k with
    | some r => exact hf _ _ _ hr hc
    | none => exact hr

/-- Lifting a closed term is the term. -/
theorem liftLooseBVars_closed {e : Expr} (h : e.looseBVarRange = 0) (s d : Nat) :
    EO.liftLooseBVars e s d = e := by
  unfold EO.liftLooseBVars
  simp [h]

/-- **Instantiation at closed values in range keeps a term in range.** -/
theorem RangeOk_instantiate {e : Expr} {subst : Array Expr} (hr : Expr.RangeOk e)
    (hsr : ∀ j (hj : j < subst.size), Expr.RangeOk subst[j])
    (hcl : ∀ j (hj : j < subst.size), subst[j].looseBVarRange = 0) :
    Expr.RangeOk (EO.instantiate e subst) := by
  rw [instantiate_eq]
  split
  · exact hr
  · refine RangeOk_mapSpec _ ?_ e 0 hr
    intro x k r hx h
    by_cases hc : x.looseBVarRange ≤ k
    · simp only [instF, hc, ↓reduceIte, Option.some.injEq] at h; subst h; exact hx
    · cases x with
      | bvar i =>
        simp only [instF, hc, ↓reduceIte] at h
        by_cases hik : i < k
        · simp only [hik, ↓reduceIte, Option.some.injEq] at h; subst h; exact hx
        · by_cases hin : i - k < subst.size
          · simp only [hik, hin, ↓reduceIte, Option.some.injEq] at h; subst h
            rw [getElem!_pos subst (i - k) hin, liftLooseBVars_closed (hcl _ hin)]
            exact hsr _ hin
          · simp only [hik, hin, ↓reduceIte, Option.some.injEq] at h; subst h
            simp only [Expr.RangeOk] at hx ⊢; omega
      | _ => simp [instF, hc] at h

/-- **Abstraction by depth keeps a term in range** (an index past C's bound
is written as `EO.rangePoison`). -/
theorem RangeOk_abstractDepthsFrom {e : Expr} (hr : Expr.RangeOk e) (d k c₀ : Nat) :
    Expr.RangeOk (EO.abstractDepthsFrom e d k c₀) := by
  rw [abstractDepthsFrom_eq]
  split
  · exact hr
  · refine RangeOk_mapSpec _ ?_ e c₀ hr
    intro x c r hx h
    unfold absF at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact hx
    · split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h; subst h
            split
            · rename_i hmax; simp only [Expr.RangeOk, EO.maxBVarIdx, maxRange] at hmax ⊢; omega
            · trivial
          · simp only [Option.some.injEq] at h; subst h; exact hx
        · simp only [Option.some.injEq] at h; subst h; exact hx
      · simp at h

/-! ## The check on an unverified term: `EO.inRange` -/

theorem Lvl_depth_eq : ∀ u : Level, Lvl.depth u = depthS u := by
  intro u; induction u <;> simp_all [Lvl.depth, depthS]

/-- `EO.inRange`'s test. -/
@[expose] def inRangeF (x : Expr) (_ : Nat) : Option Bool :=
  match x with
  | .bvar i => some (EO.maxBVarIdx < i)
  | .mvar _ => some true
  | .sort u => some (16777215 < Lvl.depth u)
  | .const _ us => some (us.any fun u => 16777215 < Lvl.depth u)
  | _ => none

theorem inRange_eq (e : Expr) : EO.inRange e = !anySpec inRangeF e 0 := by
  unfold EO.inRange
  rw [anyNode_fresh]
  rfl

theorem RangeOk_of_anySpec : ∀ (e : Expr) (k : Nat), anySpec inRangeF e k = false →
    Expr.RangeOk e ∧ emvarS e = false := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    rw [anySpec_some (show inRangeF (.bvar i) k = some (decide (EO.maxBVarIdx < i)) from rfl)] at h
    have h' : ¬ (EO.maxBVarIdx < i) := by simpa using h
    unfold EO.maxBVarIdx at h'
    exact ⟨by simp only [Expr.RangeOk, maxRange]; omega, rfl⟩
  | mvar m =>
    intro k h
    rw [anySpec_some (show inRangeF (.mvar m) k = some true from rfl)] at h
    simp at h
  | sort u =>
    intro k h
    rw [anySpec_some (show inRangeF (.sort u) k = some (decide (16777215 < Lvl.depth u)) from rfl)] at h
    simp only [decide_eq_false_iff_not, Nat.not_lt, Lvl_depth_eq] at h
    exact ⟨h, rfl⟩
  | const n us =>
    intro k h
    rw [anySpec_some (show inRangeF (.const n us) k =
      some (us.any fun u => 16777215 < Lvl.depth u) from rfl)] at h
    refine ⟨?_, rfl⟩
    intro u hu
    have := List.any_eq_false.1 h u hu
    simp only [decide_eq_true_eq, Nat.not_lt, Lvl_depth_eq] at this
    exact this
  | fvar id => intro k _; exact ⟨trivial, rfl⟩
  | lit l => intro k _; exact ⟨trivial, rfl⟩
  | app g a ihg iha =>
    intro k h
    simp only [anySpec, inRangeF, Option.getD_none, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := ihg k h.1
    obtain ⟨h3, h4⟩ := iha k h.2
    exact ⟨⟨h1, h3⟩, by simp [emvarS, h2, h4]⟩
  | lam n t b bi iht ihb =>
    intro k h
    simp only [anySpec, inRangeF, Option.getD_none, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := iht k h.1
    obtain ⟨h3, h4⟩ := ihb (k + 1) h.2
    exact ⟨⟨h1, h3⟩, by simp [emvarS, h2, h4]⟩
  | forallE n t b bi iht ihb =>
    intro k h
    simp only [anySpec, inRangeF, Option.getD_none, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := iht k h.1
    obtain ⟨h3, h4⟩ := ihb (k + 1) h.2
    exact ⟨⟨h1, h3⟩, by simp [emvarS, h2, h4]⟩
  | letE n t v b nd iht ihv ihb =>
    intro k h
    simp only [anySpec, inRangeF, Option.getD_none, Bool.or_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := iht k h.1.1
    obtain ⟨h3, h4⟩ := ihv k h.1.2
    obtain ⟨h5, h6⟩ := ihb (k + 1) h.2
    exact ⟨⟨h1, h3, h5⟩, by simp [emvarS, h2, h4, h6]⟩
  | mdata m x ih =>
    intro k h
    simp only [anySpec, inRangeF, Option.getD_none] at h
    obtain ⟨h1, h2⟩ := ih k h
    exact ⟨h1, by simpa [emvarS] using h2⟩
  | proj s i x ih =>
    intro k h
    simp only [anySpec, inRangeF, Option.getD_none] at h
    obtain ⟨h1, h2⟩ := ih k h
    exact ⟨h1, by simpa [emvarS] using h2⟩

/-- **A term `EO.inRange` accepts is in range and has no metavariable**
(the check the inductive job runs on the unverified generator's output). -/
theorem RangeOk_of_inRange {e : Expr} (h : EO.inRange e = true) :
    Expr.RangeOk e ∧ emvarS e = false := by
  rw [inRange_eq] at h
  exact RangeOk_of_anySpec e 0 (by simpa using h)

/-! ## Level instantiation: in range under a depth condition -/

/-- Every level of a term satisfies `P`. -/
@[expose] def LevelsOk (P : Level → Prop) : Expr → Prop
  | .sort u => P u
  | .const _ us => ∀ u ∈ us, P u
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => True
  | .app f a => LevelsOk P f ∧ LevelsOk P a
  | .lam _ t b _ | .forallE _ t b _ => LevelsOk P t ∧ LevelsOk P b
  | .letE _ t v b _ => LevelsOk P t ∧ LevelsOk P v ∧ LevelsOk P b
  | .mdata _ x | .proj _ _ x => LevelsOk P x

/-- The deepest of a list of levels. -/
@[expose] def maxDepthS (us : List Level) : Nat := us.foldr (fun u m => max (depthS u) m) 0

theorem depthS_le_maxDepthS : ∀ {us : List Level} {u : Level}, u ∈ us → depthS u ≤ maxDepthS us
  | u' :: us, u, h => by
    simp only [maxDepthS, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := depthS_le_maxDepthS (us := us) h
      simp only [maxDepthS] at this
      omega

theorem depthS_substGo_le : ∀ (ps : List Name) (us : List Level) (n : Name),
    depthS (Lvl.substGo ps us n) ≤ maxDepthS us
  | [], us, n => by simp [Lvl.substGo, depthS]
  | p :: ps, [], n => by simp [Lvl.substGo, depthS]
  | p :: ps, u :: us, n => by
    simp only [Lvl.substGo]
    split
    · exact depthS_le_maxDepthS List.mem_cons_self
    · have := depthS_substGo_le ps us n
      simp only [maxDepthS, List.foldr_cons] at this ⊢
      omega

/-- **How deep a substituted level gets**: at most its own depth plus the
deepest value's. -/
theorem depthS_subst_le (ps : List Name) (us : List Level) :
    ∀ u : Level, depthS (Lvl.subst ps us u) ≤ depthS u + maxDepthS us := by
  intro u
  induction u with
  | zero => simp [Lvl.subst, depthS]
  | mvar m => simp [Lvl.subst, depthS]
  | param n => have := depthS_substGo_le ps us n; simp only [Lvl.subst, depthS]; omega
  | succ u ih => simp only [Lvl.subst, depthS]; omega
  | max u v ihu ihv => simp only [Lvl.subst, depthS]; omega
  | imax u v ihu ihv => simp only [Lvl.subst, depthS]; omega

/-- **Level instantiation keeps a term in range when every substituted level
stays within C's bound** (`depthS_subst_le` gives a sufficient condition).
Not unconditional: nothing at run time bounds the depth (lane P1 finding). -/
theorem RangeOk_instantiateLevelParams {e : Expr} (ps : List Name) (us : List Level)
    (hr : Expr.RangeOk e)
    (hl : LevelsOk (fun u => depthS (Lvl.subst ps us u) ≤ maxLevelDepth) e) :
    Expr.RangeOk (EO.instantiateLevelParams e ps us) := by
  rw [instantiateLevelParams_eq]
  split
  · exact hr
  · -- a direct induction: the callback's answer needs the depth condition
    -- at its node, which `RangeOk_mapSpec`'s hypothesis does not carry
    suffices ∀ (x : Expr) (k : Nat), Expr.RangeOk x →
        LevelsOk (fun u => depthS (Lvl.subst ps us u) ≤ maxLevelDepth) x →
        Expr.RangeOk (mapSpec (instLPF ps us) x k) from this e 0 hr hl
    intro x
    induction x with
    | sort u =>
      intro k hx hlx
      by_cases hp : (Expr.sort u).hasLevelParam = false
      · rw [mapSpec_eq_of_some (show instLPF ps us (.sort u) k = some (.sort u) by
          simp [instLPF, hp])]; exact hx
      · rw [mapSpec_eq_of_some (show instLPF ps us (.sort u) k = some (.sort (Lvl.subst ps us u)) by
          simp [instLPF, hp, Expr.updateSort!, mkSort])]
        exact hlx
    | const n ls =>
      intro k hx hlx
      by_cases hp : (Expr.const n ls).hasLevelParam = false
      · rw [mapSpec_eq_of_some (show instLPF ps us (.const n ls) k = some (.const n ls) by
          simp [instLPF, hp])]; exact hx
      · rw [mapSpec_eq_of_some (show instLPF ps us (.const n ls) k =
            some (.const n (ls.map (Lvl.subst ps us))) by
          simp [instLPF, hp, Expr.updateConst!, mkConst])]
        intro u hu
        obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hu
        exact hlx u' hu'
    | app g a ihg iha =>
      intro k hx hlx
      cases hc : instLPF ps us (.app g a) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none => simp only [mapSpec, hc, Option.getD_none]; exact ⟨ihg k hx.1 hlx.1, iha k hx.2 hlx.2⟩
    | lam n t b bi iht ihb =>
      intro k hx hlx
      cases hc : instLPF ps us (.lam n t b bi) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none =>
        simp only [mapSpec, hc, Option.getD_none]
        exact ⟨iht k hx.1 hlx.1, ihb (k + 1) hx.2 hlx.2⟩
    | forallE n t b bi iht ihb =>
      intro k hx hlx
      cases hc : instLPF ps us (.forallE n t b bi) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none =>
        simp only [mapSpec, hc, Option.getD_none]
        exact ⟨iht k hx.1 hlx.1, ihb (k + 1) hx.2 hlx.2⟩
    | letE n t v b nd iht ihv ihb =>
      intro k hx hlx
      cases hc : instLPF ps us (.letE n t v b nd) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none =>
        simp only [mapSpec, hc, Option.getD_none]
        exact ⟨iht k hx.1 hlx.1, ihv k hx.2.1 hlx.2.1, ihb (k + 1) hx.2.2 hlx.2.2⟩
    | mdata m y ih =>
      intro k hx hlx
      cases hc : instLPF ps us (.mdata m y) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none => simp only [mapSpec, hc, Option.getD_none]; exact ih k hx hlx
    | proj s i y ih =>
      intro k hx hlx
      cases hc : instLPF ps us (.proj s i y) k with
      | some r => rw [mapSpec_eq_of_some hc]; simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none => simp only [mapSpec, hc, Option.getD_none]; exact ih k hx hlx
    | bvar | fvar | mvar | lit =>
      intro k hx _
      rw [mapSpec_leaf _ k rfl]
      cases hc : instLPF ps us _ k with
      | some r => simp [instLPF] at hc; obtain ⟨-, rfl⟩ := hc; exact hx
      | none => exact hx

end InLeanProof
