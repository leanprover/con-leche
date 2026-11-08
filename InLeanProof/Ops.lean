module

public import InLeanProof.ToCL
public import InLeanProof.Fields
public import ConLeche.Verify.Shift
public import ConLeche.Verify.Subst
public import ConLeche.Verify.InstList
public import ConLeche.Verify.AbstractRange
/- `Expr.updateApp!` & co. are `@[implemented_by]` definitions whose
bodies `Lean.Expr` does not expose; the walk's spec reads them (the
logical body: the node rebuilt with the new children, binder data kept). -/
import all Lean.Expr

/-!
# The expression-operation layer (task #451, lane F pilot)

InLean's substitutions are one memoised walk, `EO.mapOff f`, at a
node callback `f`.  Two steps relate them to con-leche's pure
operations:

1. `mapOff_spec`: the memoised walk computes the plain structural map
   `mapSpec f` (the walk carries its proof against its plain descent
   `EO.mapP`, `EO.mapOff_eq`; `mapP_spec` reads `Expr.update*!` as the
   constructors).
2. Per operation, `toExpr` commutes: InLean's lift on a term in range
   (`Expr.RangeOk`) reading as `c` reads as con-leche's `liftLooseBVars` of
   `c`.  The walks' cutoffs read Lean's cached fields, which is where the
   stop-gap axioms enter (`Expr.looseBVarRange_eq`).
-/

public section

namespace InLeanProof

open Lean InLean

/- The walks' memos compare nodes exactly (`instBEqExprExact`, as
`InLean/ExprOps.lean` elaborates them); their lawfulness is the exact
equality's. -/
attribute [local instance 2000] instBEqExprExact
local instance : LawfulBEq Expr := instBEqExprExact_lawful
local instance : LawfulHashable Expr := ⟨fun _ _ h => by rw [eq_of_beq h]⟩

/-- The plain structural map a walk computes: `f` decides a node, or the
walk rebuilds it from its mapped children (binder offset `+1` under a
binder). -/
@[expose] def mapSpec (f : Expr → Nat → Option Expr) : Expr → Nat → Expr
  | e@(.app g a), k => (f e k).getD (.app (mapSpec f g k) (mapSpec f a k))
  | e@(.lam n t b bi), k => (f e k).getD (.lam n (mapSpec f t k) (mapSpec f b (k + 1)) bi)
  | e@(.forallE n t b bi), k =>
    (f e k).getD (.forallE n (mapSpec f t k) (mapSpec f b (k + 1)) bi)
  | e@(.letE n t v b nd), k =>
    (f e k).getD (.letE n (mapSpec f t k) (mapSpec f v k) (mapSpec f b (k + 1)) nd)
  | e@(.mdata m x), k => (f e k).getD (.mdata m (mapSpec f x k))
  | e@(.proj s i x), k => (f e k).getD (.proj s i (mapSpec f x k))
  | e, k => (f e k).getD e

theorem mapSpec_eq_of_some {f : Expr → Nat → Option Expr} {e : Expr} {k : Nat} {r : Expr}
    (h : f e k = some r) : mapSpec f e k = r := by
  rw [mapSpec.eq_def]; split <;> simp_all

/-- At a leaf (no children) the spec is the callback's answer or the
leaf itself. -/
theorem mapSpec_leaf (f : Expr → Nat → Option Expr) {e : Expr} (k : Nat)
    (h : EO.isCompound e = false) : mapSpec f e k = (f e k).getD e := by
  cases e
  case bvar i => rfl
  case fvar i => rfl
  case mvar i => rfl
  case sort u => rfl
  case const n us => rfl
  case lit l => rfl
  all_goals simp [EO.isCompound] at h

/-- **The walk's plain descent is the structural map** (`EO.mapP` rebuilds
with `Expr.update*!`, whose logical bodies are the constructors). -/
theorem mapP_spec (f : Expr → Nat → Option Expr) :
    ∀ (e : Expr) (k : Nat), EO.mapP f e k = mapSpec f e k := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k
    cases hf : f (.app g a) k with
    | some r => rw [EO.mapP_some hf, mapSpec_eq_of_some hf]
    | none => rw [EO.mapP_app hf, ihg, iha]; simp [mapSpec, hf, Expr.updateApp!, mkApp]
  | lam n t b bi iht ihb =>
    intro k
    cases hf : f (.lam n t b bi) k with
    | some r => rw [EO.mapP_some hf, mapSpec_eq_of_some hf]
    | none =>
      rw [EO.mapP_lam hf, iht, ihb]
      simp [mapSpec, hf, Expr.updateLambdaE!, Expr.updateLambda!, mkLambda]
  | forallE n t b bi iht ihb =>
    intro k
    cases hf : f (.forallE n t b bi) k with
    | some r => rw [EO.mapP_some hf, mapSpec_eq_of_some hf]
    | none =>
      rw [EO.mapP_forallE hf, iht, ihb]
      simp [mapSpec, hf, Expr.updateForallE!, Expr.updateForall!, mkForall]
  | letE n t v b nd iht ihv ihb =>
    intro k
    cases hf : f (.letE n t v b nd) k with
    | some r => rw [EO.mapP_some hf, mapSpec_eq_of_some hf]
    | none =>
      rw [EO.mapP_letE hf, iht, ihv, ihb]
      simp [mapSpec, hf, Expr.updateLetE!, Expr.updateLet!]
  | mdata m x ih =>
    intro k
    cases hf : f (.mdata m x) k with
    | some r => rw [EO.mapP_some hf, mapSpec_eq_of_some hf]
    | none => rw [EO.mapP_mdata hf, ih]; simp [mapSpec, hf, Expr.updateMData!, mkMData]
  | proj s i x ih =>
    intro k
    cases hf : f (.proj s i x) k with
    | some r => rw [EO.mapP_some hf, mapSpec_eq_of_some hf]
    | none => rw [EO.mapP_proj hf, ih]; simp [mapSpec, hf, Expr.updateProj!, mkProj]
  | bvar | fvar | mvar | sort | const | lit =>
    intro k
    rw [mapSpec_leaf f k rfl]
    cases hf : f _ k with
    | some r => rw [EO.mapP_some hf]; rfl
    | none => rw [EO.mapP_leaf hf rfl]; rfl

/-- **The memoised walk is the structural map.** -/
theorem mapOff_spec (f : Expr → Nat → Option Expr) (e : Expr) (k : Nat) :
    EO.mapOff f e k = mapSpec f e k := by
  rw [EO.mapOff_eq, mapP_spec]

/-! ## The reading of a term below its range -/

/-- A free-variable translation answers only con-leche free variables
(InLean's table does: `FVarTable.transNum`). -/
@[expose] def FVarsOnly (fv : FVarId → Option ConLeche.Expr) : Prop :=
  ∀ id c, fv id = some c → ∃ i ty, c = .fvar i ty

/-- A term's reading has no loose variable at or above its range. -/
theorem toExpr_bounded {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c →
      c.looseBVarsBounded (rangeS e) = true := by
  intro e
  induction e with
  | bvar i =>
    intro c h
    simp only [toExpr, Option.some.injEq] at h
    subst h
    simp [ConLeche.Expr.looseBVarsBounded, rangeS]
  | fvar id =>
    intro c h
    obtain ⟨i, ty, rfl⟩ := hfv id c h
    simp [ConLeche.Expr.looseBVarsBounded]
  | mvar m => intro c h; simp [toExpr] at h
  | sort u =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨u', -, rfl⟩ := h
    simp [ConLeche.Expr.looseBVarsBounded]
  | const n us =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨us', -, rfl⟩ := h
    simp [ConLeche.Expr.looseBVarsBounded]
  | lit l =>
    intro c h
    simp only [toExpr, Option.some.injEq] at h
    subst h
    simp [ConLeche.Expr.looseBVarsBounded]
  | app g a ihg iha =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, ha, rfl⟩ := h
    simp only [ConLeche.Expr.looseBVarsBounded, rangeS, Bool.and_eq_true]
    exact ⟨ConLeche.Expr.looseBVarsBounded_mono (by omega) (ihg cg hg),
      ConLeche.Expr.looseBVarsBounded_mono (by omega) (iha ca ha)⟩
  | lam n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [ConLeche.Expr.looseBVarsBounded, rangeS, Bool.and_eq_true]
    exact ⟨ConLeche.Expr.looseBVarsBounded_mono (by omega) (iht ct ht),
      ConLeche.Expr.looseBVarsBounded_mono (by omega) (ihb cb hb)⟩
  | forallE n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [ConLeche.Expr.looseBVarsBounded, rangeS, Bool.and_eq_true]
    exact ⟨ConLeche.Expr.looseBVarsBounded_mono (by omega) (iht ct ht),
      ConLeche.Expr.looseBVarsBounded_mono (by omega) (ihb cb hb)⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    simp only [ConLeche.Expr.looseBVarsBounded, rangeS, Bool.and_eq_true]
    exact ⟨⟨ConLeche.Expr.looseBVarsBounded_mono (by omega) (iht ct ht),
      ConLeche.Expr.looseBVarsBounded_mono (by omega) (ihv cv hv)⟩,
      ConLeche.Expr.looseBVarsBounded_mono (by omega) (ihb cb hb)⟩
  | mdata m x ih =>
    intro c h
    simp only [toExpr] at h
    simpa only [rangeS] using ih c h
  | proj sn i x ih =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    simpa only [ConLeche.Expr.looseBVarsBounded, rangeS] using ih cx hx

/-! ## Lifting -/

/-- InLean's lift callback (`EO.liftLooseBVars`'s). -/
@[expose] def liftF (s d : Nat) (x : Expr) (k : Nat) : Option Expr :=
  if x.looseBVarRange ≤ s + k then some x else
  match x with
  | .bvar i => some (.bvar (i + d))
  | _ => none

theorem liftLooseBVars_eq (e : Expr) (s d : Nat) :
    EO.liftLooseBVars e s d =
      if d == 0 || e.looseBVarRange ≤ s then e else mapSpec (liftF s d) e 0 := by
  unfold EO.liftLooseBVars
  split
  · rfl
  · exact mapOff_spec _ e 0

/-- Lifting by zero is the identity (con-leche side). -/
theorem cl_lift_zero : ∀ (c : ConLeche.Expr) (cut : Nat), c.liftLooseBVars 0 cut = c := by
  intro c
  induction c <;> intro cut <;> simp_all [ConLeche.Expr.liftLooseBVars]

/-- The cutoff: a node in range below the cut is its own lift. -/
theorem lift_cut {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) (s d : Nat)
    {x : Expr} {k : Nat} {c : ConLeche.Expr} (hr : Expr.RangeOk x)
    (hc : x.looseBVarRange ≤ s + k) (h : toExpr fv x = some c) :
    toExpr fv (mapSpec (liftF s d) x k) = some (c.liftLooseBVars d (s + k)) := by
  have hf : liftF s d x k = some x := by simp [liftF, hc]
  rw [mapSpec_eq_of_some hf, h, ConLeche.Expr.liftLooseBVars_eq_self
    (ConLeche.Expr.looseBVarsBounded_mono (by rw [Expr.looseBVarRange_eq hr] at hc; exact hc)
      (toExpr_bounded hfv x c h))]

theorem toExpr_mapSpec_lift {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    (s d : Nat) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      toExpr fv (mapSpec (liftF s d) e k) = some (c.liftLooseBVars d (s + k)) := by
  intro e
  induction e with
  | bvar i =>
    intro hr k c h
    by_cases hcut : (Expr.bvar i).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · simp only [toExpr, Option.some.injEq] at h
      subst h
      have hcut' := hcut
      rw [Expr.looseBVarRange_eq hr] at hcut'
      have hge : i ≥ s + k := by simp only [rangeS] at hcut'; omega
      have hf : liftF s d (.bvar i) k = some (.bvar (i + d)) := by simp [liftF, hcut]
      rw [mapSpec_eq_of_some hf]
      simp [toExpr, ConLeche.Expr.liftLooseBVars, hge]
  | fvar id =>
    intro hr k c h
    exact lift_cut hfv s d hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | mvar m => intro _ k c h; simp [toExpr] at h
  | sort u =>
    intro hr k c h
    exact lift_cut hfv s d hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | const n us =>
    intro hr k c h
    exact lift_cut hfv s d hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | lit l =>
    intro hr k c h
    exact lift_cut hfv s d hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | app g a ihg iha =>
    intro hr k c h
    by_cases hcut : (Expr.app g a).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · have hf : liftF s d (.app g a) k = none := by simp [liftF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      simp [mapSpec, hf, toExpr, ihg hr.1 k cg hg, iha hr.2 k ca ha,
        ConLeche.Expr.liftLooseBVars]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.lam n t b bi).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · have hf : liftF s d (.lam n t b bi) k = none := by simp [liftF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb,
        ConLeche.Expr.liftLooseBVars, Nat.add_assoc]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.forallE n t b bi).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · have hf : liftF s d (.forallE n t b bi) k = none := by simp [liftF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb,
        ConLeche.Expr.liftLooseBVars, Nat.add_assoc]
  | letE n t v b nd iht ihv ihb =>
    intro hr k c h
    by_cases hcut : (Expr.letE n t v b nd).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · have hf : liftF s d (.letE n t v b nd) k = none := by simp [liftF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihv hr.2.1 k cv hv,
        ihb hr.2.2 (k + 1) cb hb, ConLeche.Expr.liftLooseBVars, Nat.add_assoc]
  | mdata m x ih =>
    intro hr k c h
    by_cases hcut : (Expr.mdata m x).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · have hf : liftF s d (.mdata m x) k = none := by simp [liftF, hcut]
      simp only [toExpr] at h
      simp [mapSpec, hf, toExpr, ih hr k c h]
  | proj sn i x ih =>
    intro hr k c h
    by_cases hcut : (Expr.proj sn i x).looseBVarRange ≤ s + k
    · exact lift_cut hfv s d hr hcut h
    · have hf : liftF s d (.proj sn i x) k = none := by simp [liftF, hcut]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      simp [mapSpec, hf, toExpr, ih hr k cx hx, ConLeche.Expr.liftLooseBVars]

/-- **InLean's lift simulates con-leche's** on a term in range
(`EO.liftLooseBVars e s d` reads as `liftLooseBVars d s` of `e`'s reading). -/
theorem toExpr_liftLooseBVars {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) (s d : Nat) :
    toExpr fv (EO.liftLooseBVars e s d) = some (c.liftLooseBVars d s) := by
  rw [liftLooseBVars_eq]
  split
  · rename_i hd
    by_cases hd0 : d = 0
    · subst hd0
      rw [cl_lift_zero]; exact h
    · have hle : e.looseBVarRange ≤ s := by simpa [hd0] using hd
      rw [ConLeche.Expr.liftLooseBVars_eq_self
        (ConLeche.Expr.looseBVarsBounded_mono (by rw [Expr.looseBVarRange_eq hr] at hle; exact hle)
          (toExpr_bounded hfv e c h))]
      exact h
  · simpa using toExpr_mapSpec_lift hfv s d e hr 0 c h

/-! ## Instantiation -/

/-- InLean's instantiation callback (`EO.instantiate`'s). -/
@[expose] def instF (subst : Array Expr) (x : Expr) (k : Nat) : Option Expr :=
  if x.looseBVarRange ≤ k then some x else
  match x with
  | .bvar i =>
    if i < k then some x
    else if i - k < subst.size then some (EO.liftLooseBVars (subst[i - k]!) 0 k)
    else some (.bvar (i - subst.size))
  | _ => none

theorem instantiate_eq (e : Expr) (subst : Array Expr) :
    EO.instantiate e subst =
      if subst.size == 0 || !e.hasLooseBVars then e else mapSpec (instF subst) e 0 := by
  unfold EO.instantiate EO.instantiateBy
  split
  · rfl
  · exact mapOff_spec _ e 0

/-- The substitution reads its values only below `n`. -/
theorem instantiateBy_congr {e : Expr} {n : Nat} {get get' : Nat → Expr}
    (h : ∀ j, j < n → get j = get' j) : EO.instantiateBy e n get = EO.instantiateBy e n get' := by
  unfold EO.instantiateBy
  split
  · rfl
  · congr 1
    funext x k
    split
    · rfl
    · split
      · split
        · rfl
        · split
          · rename_i i _ _ hi; rw [h _ hi]
          · rfl
      · rfl

theorem instantiate1_eq (e v : Expr) : EO.instantiate1 e v = EO.instantiate e #[v] := by
  unfold EO.instantiate1 EO.instantiate
  exact instantiateBy_congr fun j hj => by
    have : j = 0 := by omega
    subst this; rfl

theorem instantiateRev_eq (e : Expr) (subst : Array Expr) :
    EO.instantiateRev e subst = EO.instantiate e subst.reverse := by
  unfold EO.instantiateRev EO.instantiate
  rw [Array.size_reverse]
  exact instantiateBy_congr fun j hj => by
    rw [getElem!_pos subst.reverse j (by simpa using hj), Array.getElem_reverse,
      getElem!_pos subst _ (by omega)]

/-- The substitution reads, entry by entry, as the closed list `cvs`, and
is in range. -/
structure SubstReads (fv : FVarId → Option ConLeche.Expr) (subst : Array Expr)
    (cvs : List ConLeche.Expr) : Prop where
  len : cvs.length = subst.size
  entry : ∀ j (hj : j < subst.size), toExpr fv subst[j] = some (cvs[j]'(len ▸ hj))
  closed : ∀ cv ∈ cvs, cv.looseBVarsBounded 0 = true
  range : ∀ j (hj : j < subst.size), Expr.RangeOk subst[j]

/-- The cutoff: a node in range below the offset is its own instantiation. -/
theorem inst_cut {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) (subst : Array Expr)
    (cvs : List ConLeche.Expr) {x : Expr} {k : Nat} {c : ConLeche.Expr} (hr : Expr.RangeOk x)
    (hc : x.looseBVarRange ≤ k) (h : toExpr fv x = some c) :
    toExpr fv (mapSpec (instF subst) x k) = some (c.instantiateList cvs k) := by
  have hf : instF subst x k = some x := by simp [instF, hc]
  rw [mapSpec_eq_of_some hf, h, ConLeche.Expr.instantiateList_eq_self
    (ConLeche.Expr.looseBVarsBounded_mono (by rw [Expr.looseBVarRange_eq hr] at hc; exact hc)
      (toExpr_bounded hfv x c h))]

theorem toExpr_mapSpec_inst {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {subst : Array Expr} {cvs : List ConLeche.Expr} (hs : SubstReads fv subst cvs) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      toExpr fv (mapSpec (instF subst) e k) = some (c.instantiateList cvs k) := by
  intro e
  induction e with
  | bvar i =>
    intro hr k c h
    by_cases hcut : (Expr.bvar i).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · simp only [toExpr, Option.some.injEq] at h
      subst h
      have hcut' := hcut
      rw [Expr.looseBVarRange_eq hr] at hcut'
      have hik : ¬ i < k := by simp only [rangeS] at hcut'; omega
      by_cases hin : i - k < subst.size
      · have hj : i - k < cvs.length := hs.len ▸ hin
        have hcl := hs.closed _ (List.getElem_mem hj)
        have hent := hs.entry (i - k) hin
        have hf : instF subst (.bvar i) k = some (EO.liftLooseBVars subst[i - k] 0 k) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf, toExpr_liftLooseBVars hfv (hs.range _ hin) hent,
          ConLeche.Expr.liftLooseBVars_eq_self hcl, ConLeche.Expr.instantiateList]
        simp only [hik, ↓reduceIte, hj, ↓reduceDIte]
        rw [ConLeche.Expr.instantiateList_eq_self
          (ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) hcl)]
      · have hf : instF subst (.bvar i) k = some (.bvar (i - subst.size)) := by
          simp [instF, hcut, hik, hin]
        rw [mapSpec_eq_of_some hf]
        simp only [toExpr]
        rw [ConLeche.Expr.instantiateList]
        simp [hik, hs.len, hin]
  | fvar id =>
    intro hr k c h
    exact inst_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | mvar m => intro _ k c h; simp [toExpr] at h
  | sort u =>
    intro hr k c h
    exact inst_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | const n us =>
    intro hr k c h
    exact inst_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | lit l =>
    intro hr k c h
    exact inst_cut hfv subst cvs hr (by rw [Expr.looseBVarRange_eq hr]; simp [rangeS]) h
  | app g a ihg iha =>
    intro hr k c h
    by_cases hcut : (Expr.app g a).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.app g a) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      rw [ConLeche.Expr.instantiateList]
      simp [mapSpec, hf, toExpr, ihg hr.1 k cg hg, iha hr.2 k ca ha]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.lam n t b bi).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.lam n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      rw [ConLeche.Expr.instantiateList]
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.forallE n t b bi).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.forallE n t b bi) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      rw [ConLeche.Expr.instantiateList]
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb]
  | letE n t v b nd iht ihv ihb =>
    intro hr k c h
    by_cases hcut : (Expr.letE n t v b nd).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.letE n t v b nd) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      rw [ConLeche.Expr.instantiateList]
      simp [mapSpec, hf, toExpr, iht hr.1 k ct ht, ihv hr.2.1 k cv hv, ihb hr.2.2 (k + 1) cb hb]
  | mdata m x ih =>
    intro hr k c h
    by_cases hcut : (Expr.mdata m x).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.mdata m x) k = none := by simp [instF, hcut]
      simp only [toExpr] at h
      simp [mapSpec, hf, toExpr, ih hr k c h]
  | proj sn i x ih =>
    intro hr k c h
    by_cases hcut : (Expr.proj sn i x).looseBVarRange ≤ k
    · exact inst_cut hfv subst cvs hr hcut h
    · have hf : instF subst (.proj sn i x) k = none := by simp [instF, hcut]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      rw [ConLeche.Expr.instantiateList]
      simp [mapSpec, hf, toExpr, ih hr k cx hx]

/-- **InLean's instantiation simulates con-leche's bulk instantiation**
on a term in range (`EO.instantiate e subst` reads as `instantiateList` of
`e`'s reading by the substitution's, at closed substitutions — every
checker site). -/
theorem toExpr_instantiate {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {subst : Array Expr} {cvs : List ConLeche.Expr} (hs : SubstReads fv subst cvs)
    {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) :
    toExpr fv (EO.instantiate e subst) = some (c.instantiateList cvs 0) := by
  rw [instantiate_eq]
  split
  · rename_i hn
    by_cases hn0 : subst.size = 0
    · have : cvs = [] := List.eq_nil_of_length_eq_zero (hs.len.trans hn0)
      subst this
      rw [ConLeche.Expr.instantiateList_nil]; exact h
    · have hl : e.looseBVarRange = 0 := by
        have : (!e.hasLooseBVars) = true := by simpa [hn0] using hn
        simpa [Expr.hasLooseBVars] using this
      rw [Expr.looseBVarRange_eq hr] at hl
      have hb := toExpr_bounded hfv e c h
      rw [hl] at hb
      rw [ConLeche.Expr.instantiateList_eq_self hb]; exact h
  · exact toExpr_mapSpec_inst hfv hs e hr 0 c h

/-! ## O1: the rest of the operation layer (task #451, lane P1)

Each lemma reads an InLean operation as con-leche's *pure* operation on the
translation; `ConLeche/Verify/Cached/OpsC.lean` relates the cached
operations of con-leche's checker to the same pure ones
(`instantiate1C_spec`, `instantiateRev_spec`, `abstractRangeC_spec`,
`instLevelParams_spec`, `getAppArgsC_spec`). -/

/-! ### Instantiation by one value, and on a reversed array -/

/-- One value. -/
theorem SubstReads.single {fv : FVarId → Option ConLeche.Expr} {v : Expr} {cv : ConLeche.Expr}
    (hv : toExpr fv v = some cv) (hcl : cv.looseBVarsBounded 0 = true) (hvr : Expr.RangeOk v) :
    SubstReads fv #[v] [cv] where
  len := rfl
  entry j hj := by
    have : j = 0 := by simp at hj; omega
    subst this; exact hv
  closed cv' h := by simp at h; subst h; exact hcl
  range j hj := by
    have : j = 0 := by simp at hj; omega
    subst this; exact hvr

/-- **InLean's `instantiate1` simulates con-leche's** (at a closed value,
every checker site). -/
theorem toExpr_instantiate1 {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {e v : Expr} {c cv : ConLeche.Expr} (hr : Expr.RangeOk e) (hvr : Expr.RangeOk v)
    (h : toExpr fv e = some c) (hv : toExpr fv v = some cv) (hcl : cv.looseBVarsBounded 0 = true) :
    toExpr fv (EO.instantiate1 e v) = some (c.instantiate1 cv 0) := by
  rw [instantiate1_eq, toExpr_instantiate hfv (SubstReads.single hv hcl hvr) hr h,
    ConLeche.Expr.instantiateList_cons, ConLeche.Expr.instantiateList_nil]

/-- The reversed substitution reads as the reversed list. -/
theorem SubstReads.reverse {fv : FVarId → Option ConLeche.Expr} {subst : Array Expr}
    {cvs : List ConLeche.Expr} (hs : SubstReads fv subst cvs) :
    SubstReads fv subst.reverse cvs.reverse where
  len := by simp [hs.len]
  entry j hj := by
    have hj' : j < subst.size := by simpa using hj
    have hlen := hs.len
    rw [Array.getElem_reverse, hs.entry _ (by omega)]
    simp only [List.getElem_reverse, Option.some.injEq]
    congr 1; omega
  closed cv h := hs.closed cv (List.mem_reverse.1 h)
  range j hj := by
    have hj' : j < subst.size := by simpa using hj
    rw [Array.getElem_reverse]; exact hs.range _ (by omega)

/-- **InLean's `instantiateRev` simulates con-leche's** (`instantiateList`
on the reversed list, `ConLeche.Verify.Cached.instantiateRev_spec`'s right
side). -/
theorem toExpr_instantiateRev {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {subst : Array Expr} {cvs : List ConLeche.Expr} (hs : SubstReads fv subst cvs)
    {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) :
    toExpr fv (EO.instantiateRev e subst) = some (c.instantiateList cvs.reverse 0) := by
  rw [instantiateRev_eq]; exact toExpr_instantiate hfv hs.reverse hr h

/-! ### Abstraction by depth -/

/-- An id translation that keeps the id's depth (InLean's table does). -/
@[expose] def FvDepthOK (fv : FVarId → Option ConLeche.Expr) : Prop :=
  ∀ id c, fv id = some c → ∃ d ty, c = .fvar d ty ∧ EO.fvDepth? id = some d

/-- A term with no free variable reads as one below every depth. -/
theorem fvarsBelow_of_fvarS {fv : FVarId → Option ConLeche.Expr} :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c → fvarS e = false →
      ∀ d, c.fvarsBelow d := by
  intro e
  induction e with
  | fvar id => intro c _ h; simp [fvarS] at h
  | mvar m => intro c h; simp [toExpr] at h
  | bvar i => intro c h _ d; simp only [toExpr, Option.some.injEq] at h; subst h; trivial
  | lit l => intro c h _ d; simp only [toExpr, Option.some.injEq] at h; subst h; trivial
  | sort u =>
    intro c h _ d
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; trivial
  | const n us =>
    intro c h _ d
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; trivial
  | app g a ihg iha =>
    intro c h hf d
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, ha, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    exact ⟨ihg cg hg hf.1 d, iha ca ha hf.2 d⟩
  | lam n t b bi iht ihb =>
    intro c h hf d
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    exact ⟨iht ct ht hf.1 d, ihb cb hb hf.2 d⟩
  | forallE n t b bi iht ihb =>
    intro c h hf d
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    exact ⟨iht ct ht hf.1 d, ihb cb hb hf.2 d⟩
  | letE n t v b nd iht ihv ihb =>
    intro c h hf d
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    exact ⟨iht ct ht hf.1.1 d, ihv cv hv hf.1.2 d, ihb cb hb hf.2 d⟩
  | mdata m x ih => intro c h hf d; simp only [toExpr] at h; exact ih c h hf d
  | proj s i x ih =>
    intro c h hf d
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    exact ih cx hx hf d

/-- `EO.abstractDepthsFrom`'s callback. -/
@[expose] def absF (d k : Nat) (x : Expr) (c : Nat) : Option Expr :=
  if !x.hasFVar then some x else
  match x with
  | .fvar id =>
    match EO.fvDepth? id with
    | some idx =>
      if d ≤ idx ∧ idx < d + k then
        let i := c + (d + k - 1 - idx)
        some (if i ≤ EO.maxBVarIdx then .bvar i else EO.rangePoison)
      else some x
    | none => some x
  | _ => none

theorem abstractDepthsFrom_eq (e : Expr) (d k c₀ : Nat) :
    EO.abstractDepthsFrom e d k c₀ =
      if k == 0 || !e.hasFVar then e else mapSpec (absF d k) e c₀ := by
  unfold EO.abstractDepthsFrom
  split
  · rfl
  · exact mapOff_spec _ e c₀

/-- The cutoff: a node in range with no free variable is its own
abstraction. -/
theorem abs_cut {fv : FVarId → Option ConLeche.Expr} {d k : Nat} {x : Expr} {c : Nat}
    {cx : ConLeche.Expr} (hr : Expr.RangeOk x) (hf : x.hasFVar = false)
    (h : toExpr fv x = some cx) :
    toExpr fv (mapSpec (absF d k) x c) = some (cx.abstractRange d k c) := by
  have hcb : absF d k x c = some x := by simp [absF, hf]
  rw [mapSpec_eq_of_some hcb, h, ConLeche.abstractRange_eq_self
    (fvarsBelow_of_fvarS x cx h (by rw [← Expr.hasFVar_eq hr]; exact hf) d)]

theorem toExpr_mapSpec_abs {fv : FVarId → Option ConLeche.Expr} (hfd : FvDepthOK fv) (d k : Nat) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (c : Nat) (ce : ConLeche.Expr), toExpr fv e = some ce →
      emvarS (mapSpec (absF d k) e c) = false →
      toExpr fv (mapSpec (absF d k) e c) = some (ce.abstractRange d k c) := by
  intro e
  induction e with
  | fvar id =>
    intro hr c ce h hm
    by_cases hf : (Expr.fvar id).hasFVar = false
    · exact abs_cut hr hf h
    · obtain ⟨idx, ty, rfl, hdep⟩ := hfd id ce h
      simp only [Bool.not_eq_false] at hf
      by_cases hin : d ≤ idx ∧ idx < d + k
      · by_cases hmax : c + (d + k - 1 - idx) ≤ EO.maxBVarIdx
        · have hcb : absF d k (.fvar id) c = some (.bvar (c + (d + k - 1 - idx))) := by
            simp [absF, hf, hdep, hin, hmax]
          rw [mapSpec_eq_of_some hcb]
          simp [toExpr, ConLeche.Expr.abstractRange, hin]
        · have hcb : absF d k (.fvar id) c = some EO.rangePoison := by
            simp [absF, hf, hdep, hin, hmax]
          rw [mapSpec_eq_of_some hcb] at hm
          simp [EO.rangePoison, emvarS] at hm
      · have hcb : absF d k (.fvar id) c = some (.fvar id) := by
          simp [absF, hf, hdep, hin]
        rw [mapSpec_eq_of_some hcb, h]
        simp [ConLeche.Expr.abstractRange, hin]
  | mvar m => intro _ c ce h; simp [toExpr] at h
  | bvar i =>
    intro hr c ce h _
    exact abs_cut hr (by rw [Expr.hasFVar_eq hr]; rfl) h
  | sort u =>
    intro hr c ce h _
    exact abs_cut hr (by rw [Expr.hasFVar_eq hr]; rfl) h
  | const n us =>
    intro hr c ce h _
    exact abs_cut hr (by rw [Expr.hasFVar_eq hr]; rfl) h
  | lit l =>
    intro hr c ce h _
    exact abs_cut hr (by rw [Expr.hasFVar_eq hr]; rfl) h
  | app g a ihg iha =>
    intro hr c ce h hm
    by_cases hf : (Expr.app g a).hasFVar = false
    · exact abs_cut hr hf h
    · have hcb : absF d k (.app g a) c = none := by simp [absF, hf]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hm ⊢
      simp [toExpr, ihg hr.1 c cg hg hm.1, iha hr.2 c ca ha hm.2, ConLeche.Expr.abstractRange]
  | lam n t b bi iht ihb =>
    intro hr c ce h hm
    by_cases hf : (Expr.lam n t b bi).hasFVar = false
    · exact abs_cut hr hf h
    · have hcb : absF d k (.lam n t b bi) c = none := by simp [absF, hf]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hm ⊢
      simp [toExpr, iht hr.1 c ct ht hm.1, ihb hr.2 (c + 1) cb hb hm.2,
        ConLeche.Expr.abstractRange]
  | forallE n t b bi iht ihb =>
    intro hr c ce h hm
    by_cases hf : (Expr.forallE n t b bi).hasFVar = false
    · exact abs_cut hr hf h
    · have hcb : absF d k (.forallE n t b bi) c = none := by simp [absF, hf]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hm ⊢
      simp [toExpr, iht hr.1 c ct ht hm.1, ihb hr.2 (c + 1) cb hb hm.2,
        ConLeche.Expr.abstractRange]
  | letE n t v b nd iht ihv ihb =>
    intro hr c ce h hm
    by_cases hf : (Expr.letE n t v b nd).hasFVar = false
    · exact abs_cut hr hf h
    · have hcb : absF d k (.letE n t v b nd) c = none := by simp [absF, hf]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hm ⊢
      simp [toExpr, iht hr.1 c ct ht hm.1.1, ihv hr.2.1 c cv hv hm.1.2,
        ihb hr.2.2 (c + 1) cb hb hm.2, ConLeche.Expr.abstractRange]
  | mdata m x ih =>
    intro hr c ce h hm
    by_cases hf : (Expr.mdata m x).hasFVar = false
    · exact abs_cut hr hf h
    · have hcb : absF d k (.mdata m x) c = none := by simp [absF, hf]
      simp only [toExpr] at h
      simp only [mapSpec, hcb, Option.getD_none, emvarS] at hm ⊢
      simp [toExpr, ih hr c ce h hm]
  | proj s i x ih =>
    intro hr c ce h hm
    by_cases hf : (Expr.proj s i x).hasFVar = false
    · exact abs_cut hr hf h
    · have hcb : absF d k (.proj s i x) c = none := by simp [absF, hf]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      simp only [mapSpec, hcb, Option.getD_none, emvarS] at hm ⊢
      simp [toExpr, ih hr c cx hx hm, ConLeche.Expr.abstractRange]

/-- **InLean's abstraction by depth simulates con-leche's `abstractRange`**
on a term in range, unless it wrote the out-of-range marker (which its
checker call site reports as an error, `InLean.abstractRangeM`). -/
theorem toExpr_abstractDepthsFrom {fv : FVarId → Option ConLeche.Expr} (hfd : FvDepthOK fv)
    {e : Expr} {ce : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some ce)
    (d k c₀ : Nat) (hm : emvarS (EO.abstractDepthsFrom e d k c₀) = false) :
    toExpr fv (EO.abstractDepthsFrom e d k c₀) = some (ce.abstractRange d k c₀) := by
  rw [abstractDepthsFrom_eq] at hm ⊢
  split
  · rename_i hc
    rcases Bool.or_eq_true_iff.1 hc with hk | hf
    · have : k = 0 := by simpa using hk
      subst this
      rw [h, ConLeche.abstractRange_zero]
    · have hf' : fvarS e = false := by rw [← Expr.hasFVar_eq hr]; simpa using hf
      rw [h, ConLeche.abstractRange_eq_self (fvarsBelow_of_fvarS e ce h hf' d)]
  · rename_i hc
    have hc' : (k == 0 || !e.hasFVar) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at hm
    exact toExpr_mapSpec_abs hfd d k e hr c₀ ce h hm

/-! ### Level instantiation (on terms without free variables: every
checker site instantiates a constant's stored type, value, rule or pin) -/

theorem toLevel_substGo : ∀ (ps : List Name) (us : List Level) (cus : List ConLeche.Level)
    (n : Name), toLevels us = some cus →
      toLevel (Lvl.substGo ps us n) = some (ConLeche.Level.subst.go (ps.map toName) cus (toName n))
  | [], us, cus, n, _ => by
    cases cus <;> simp [Lvl.substGo, ConLeche.Level.subst.go, toLevel]
  | p :: ps, [], cus, n, h => by
    simp only [toLevels, Option.some.injEq] at h; subst h
    simp [Lvl.substGo, ConLeche.Level.subst.go, toLevel]
  | p :: ps, u :: us, cus, n, h => by
    simp only [toLevels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cus', hus, rfl⟩ := h
    simp only [Lvl.substGo, List.map_cons, ConLeche.Level.subst.go]
    by_cases hpn : p = n
    · subst hpn; simp [hu]
    · have : toName p ≠ toName n := fun h => hpn (toName_inj h)
      simp [hpn, this, toLevel_substGo ps us cus' n hus]

/-- **`Lvl.subst` reads as con-leche's `Level.subst`.** -/
theorem toLevel_subst (ps : List Name) {us : List Level} {cus : List ConLeche.Level}
    (hus : toLevels us = some cus) :
    ∀ {u : Level} {cu : ConLeche.Level}, toLevel u = some cu →
      toLevel (Lvl.subst ps us u) = some (ConLeche.Level.subst (ps.map toName) cus cu) := by
  intro u
  induction u with
  | zero => intro cu h; simp only [toLevel, Option.some.injEq] at h; subst h; rfl
  | param n =>
    intro cu h; simp only [toLevel, Option.some.injEq] at h; subst h
    exact toLevel_substGo ps us cus n hus
  | mvar m => intro cu h; simp [toLevel] at h
  | succ u ih =>
    intro cu h
    simp only [toLevel, Option.map_eq_some_iff] at h
    obtain ⟨cu', hu, rfl⟩ := h
    simp [Lvl.subst, toLevel, ih hu, ConLeche.Level.subst]
  | max u v ihu ihv =>
    intro cu h
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu', hu, cv', hv, rfl⟩ := h
    simp [Lvl.subst, toLevel, ihu hu, ihv hv, ConLeche.Level.subst]
  | imax u v ihu ihv =>
    intro cu h
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu', hu, cv', hv, rfl⟩ := h
    simp [Lvl.subst, toLevel, ihu hu, ihv hv, ConLeche.Level.subst]

theorem toLevels_map_subst (ps : List Name) {us : List Level} {cus : List ConLeche.Level}
    (hus : toLevels us = some cus) :
    ∀ {ls : List Level} {cls : List ConLeche.Level}, toLevels ls = some cls →
      toLevels (ls.map (Lvl.subst ps us)) = some (cls.map (ConLeche.Level.subst (ps.map toName) cus))
  | [], cls, h => by simp only [toLevels, Option.some.injEq] at h; subst h; rfl
  | l :: ls, cls, h => by
    simp only [toLevels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cl, hl, cls', hls, rfl⟩ := h
    simp [toLevels, toLevel_subst ps hus hl, toLevels_map_subst ps hus hls]

/-- A level's parameter flag reads as con-leche's. -/
theorem hasParam_toLevel : ∀ {u : Level} {cu : ConLeche.Level}, toLevel u = some cu →
    cu.hasParam = lparamS u := by
  intro u
  induction u with
  | zero => intro cu h; simp only [toLevel, Option.some.injEq] at h; subst h; rfl
  | param n => intro cu h; simp only [toLevel, Option.some.injEq] at h; subst h; rfl
  | mvar m => intro cu h; simp [toLevel] at h
  | succ u ih =>
    intro cu h
    simp only [toLevel, Option.map_eq_some_iff] at h
    obtain ⟨cu', hu, rfl⟩ := h
    simp [ConLeche.Level.hasParam, lparamS, ih hu]
  | max u v ihu ihv =>
    intro cu h
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu', hu, cv', hv, rfl⟩ := h
    simp [ConLeche.Level.hasParam, lparamS, ihu hu, ihv hv]
  | imax u v ihu ihv =>
    intro cu h
    simp only [toLevel, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu', hu, cv', hv, rfl⟩ := h
    simp [ConLeche.Level.hasParam, lparamS, ihu hu, ihv hv]

theorem hasParam_toLevels : ∀ {us : List Level} {cus : List ConLeche.Level},
    toLevels us = some cus → cus.any ConLeche.Level.hasParam = us.any lparamS
  | [], cus, h => by simp only [toLevels, Option.some.injEq] at h; subst h; rfl
  | u :: us, cus, h => by
    simp only [toLevels, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cu, hu, cus', hus, rfl⟩ := h
    simp [hasParam_toLevel hu, hasParam_toLevels hus]

/-- A term with no free variable: its level-parameter flag reads as con-leche's. -/
theorem hasLevelParam_toExpr {fv : FVarId → Option ConLeche.Expr} :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c → fvarS e = false →
      c.hasLevelParam = elparamS e := by
  intro e
  induction e with
  | fvar id => intro c _ h; simp [fvarS] at h
  | mvar m => intro c h; simp [toExpr] at h
  | bvar i => intro c h _; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | lit l => intro c h _; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | sort u =>
    intro c h _
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cu, hu, rfl⟩ := h
    simp [ConLeche.Expr.hasLevelParam, elparamS, hasParam_toLevel hu]
  | const n us =>
    intro c h _
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cus, hus, rfl⟩ := h
    simp [ConLeche.Expr.hasLevelParam, elparamS, hasParam_toLevels hus]
  | app g a ihg iha =>
    intro c h hf
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, ha, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    simp [ConLeche.Expr.hasLevelParam, elparamS, ihg cg hg hf.1, iha ca ha hf.2]
  | lam n t b bi iht ihb =>
    intro c h hf
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    simp [ConLeche.Expr.hasLevelParam, elparamS, iht ct ht hf.1, ihb cb hb hf.2]
  | forallE n t b bi iht ihb =>
    intro c h hf
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    simp [ConLeche.Expr.hasLevelParam, elparamS, iht ct ht hf.1, ihb cb hb hf.2]
  | letE n t v b nd iht ihv ihb =>
    intro c h hf
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    simp only [fvarS, Bool.or_eq_false_iff] at hf
    simp [ConLeche.Expr.hasLevelParam, elparamS, iht ct ht hf.1.1, ihv cv hv hf.1.2,
      ihb cb hb hf.2]
  | mdata m x ih => intro c h hf; simp only [toExpr] at h; exact ih c h hf
  | proj s i x ih =>
    intro c h hf
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    simpa [ConLeche.Expr.hasLevelParam, elparamS] using ih cx hx hf

/-- `EO.instantiateLevelParams`'s callback. -/
@[expose] def instLPF (ps : List Name) (us : List Level) (x : Expr) (_ : Nat) : Option Expr :=
  if !x.hasLevelParam then some x else
  match x with
  | .sort u =>
    some (if EO.depthFits (EO.maxDepthOf us) u then x.updateSort! (Lvl.subst ps us u)
      else EO.rangePoison)
  | .const _ ls =>
    some (if ls.all (EO.depthFits (EO.maxDepthOf us)) then x.updateConst! (ls.map (Lvl.subst ps us))
      else EO.rangePoison)
  | _ => none

theorem instantiateLevelParams_eq (e : Expr) (ps : List Name) (us : List Level) :
    EO.instantiateLevelParams e ps us =
      if ps.isEmpty || us.isEmpty || !e.hasLevelParam then e else mapSpec (instLPF ps us) e 0 := by
  unfold EO.instantiateLevelParams
  split
  · rfl
  · exact mapOff_spec _ e 0

theorem ilp_cut {fv : FVarId → Option ConLeche.Expr} {ps : List Name} {us : List Level}
    {cus : List ConLeche.Level} {x : Expr} {k : Nat} {cx : ConLeche.Expr}
    (hr : Expr.RangeOk x) (hfv : fvarS x = false) (hl : x.hasLevelParam = false)
    (h : toExpr fv x = some cx) :
    toExpr fv (mapSpec (instLPF ps us) x k) =
      some (cx.instantiateLevelParams (ps.map toName) cus) := by
  have hcb : instLPF ps us x k = some x := by simp [instLPF, hl]
  rw [mapSpec_eq_of_some hcb, h, ConLeche.Expr.instantiateLevelParams_eq_self]
  rw [hasLevelParam_toExpr x cx h hfv, ← Expr.hasLevelParam_eq hr, hl]

theorem toExpr_mapSpec_ilp {fv : FVarId → Option ConLeche.Expr} (ps : List Name) {us : List Level}
    {cus : List ConLeche.Level} (hus : toLevels us = some cus) :
    ∀ (e : Expr), Expr.RangeOk e → fvarS e = false → ∀ (k : Nat) (c : ConLeche.Expr),
      toExpr fv e = some c → emvarS (mapSpec (instLPF ps us) e k) = false →
      toExpr fv (mapSpec (instLPF ps us) e k) =
        some (c.instantiateLevelParams (ps.map toName) cus) := by
  intro e
  induction e with
  | fvar id => intro _ h; simp [fvarS] at h
  | mvar m => intro _ _ k c h _; simp [toExpr] at h
  | bvar i => intro hr hf k c h _; exact ilp_cut hr hf (by rw [Expr.hasLevelParam_eq hr]; rfl) h
  | lit l => intro hr hf k c h _; exact ilp_cut hr hf (by rw [Expr.hasLevelParam_eq hr]; rfl) h
  | sort u =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.sort u).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · by_cases hfit : EO.depthFits (EO.maxDepthOf us) u = true
      · have hcb : instLPF ps us (.sort u) k = some (.sort (Lvl.subst ps us u)) := by
          simp [instLPF, hl, hfit, Expr.updateSort!, mkSort]
        simp only [toExpr, Option.map_eq_some_iff] at h
        obtain ⟨cu, hu, rfl⟩ := h
        rw [mapSpec_eq_of_some hcb]
        simp [toExpr, toLevel_subst ps hus hu, ConLeche.Expr.instantiateLevelParams]
      · have hcb : instLPF ps us (.sort u) k = some EO.rangePoison := by
          simp [instLPF, hl, hfit]
        rw [mapSpec_eq_of_some hcb] at hnp; simp [EO.rangePoison, emvarS] at hnp
  | const n ls =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.const n ls).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · by_cases hfit : ls.all (EO.depthFits (EO.maxDepthOf us)) = true
      · have hcb : instLPF ps us (.const n ls) k = some (.const n (ls.map (Lvl.subst ps us))) := by
          simp only [instLPF, hl, hfit]; simp [Expr.updateConst!, mkConst]
        simp only [toExpr, Option.map_eq_some_iff] at h
        obtain ⟨cls, hls, rfl⟩ := h
        rw [mapSpec_eq_of_some hcb]
        simp [toExpr, toLevels_map_subst ps hus hls, ConLeche.Expr.instantiateLevelParams]
      · have hcb : instLPF ps us (.const n ls) k = some EO.rangePoison := by
          simp only [instLPF, hl, hfit]; simp
        rw [mapSpec_eq_of_some hcb] at hnp; simp [EO.rangePoison, emvarS] at hnp
  | app g a ihg iha =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.app g a).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · have hcb : instLPF ps us (.app g a) k = none := by simp [instLPF, hl]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      simp only [fvarS, Bool.or_eq_false_iff] at hf
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hnp
      simp [mapSpec, hcb, toExpr, ihg hr.1 hf.1 k cg hg hnp.1, iha hr.2 hf.2 k ca ha hnp.2,
        ConLeche.Expr.instantiateLevelParams]
  | lam n t b bi iht ihb =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.lam n t b bi).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · have hcb : instLPF ps us (.lam n t b bi) k = none := by simp [instLPF, hl]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp only [fvarS, Bool.or_eq_false_iff] at hf
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hnp
      simp [mapSpec, hcb, toExpr, iht hr.1 hf.1 k ct ht hnp.1, ihb hr.2 hf.2 (k + 1) cb hb hnp.2,
        ConLeche.Expr.instantiateLevelParams]
  | forallE n t b bi iht ihb =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.forallE n t b bi).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · have hcb : instLPF ps us (.forallE n t b bi) k = none := by simp [instLPF, hl]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp only [fvarS, Bool.or_eq_false_iff] at hf
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hnp
      simp [mapSpec, hcb, toExpr, iht hr.1 hf.1 k ct ht hnp.1, ihb hr.2 hf.2 (k + 1) cb hb hnp.2,
        ConLeche.Expr.instantiateLevelParams]
  | letE n t v b nd iht ihv ihb =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.letE n t v b nd).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · have hcb : instLPF ps us (.letE n t v b nd) k = none := by simp [instLPF, hl]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      simp only [fvarS, Bool.or_eq_false_iff] at hf
      simp only [mapSpec, hcb, Option.getD_none, emvarS, Bool.or_eq_false_iff] at hnp
      simp [mapSpec, hcb, toExpr, iht hr.1 hf.1.1 k ct ht hnp.1.1, ihv hr.2.1 hf.1.2 k cv hv hnp.1.2,
        ihb hr.2.2 hf.2 (k + 1) cb hb hnp.2, ConLeche.Expr.instantiateLevelParams]
  | mdata m x ih =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.mdata m x).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · have hcb : instLPF ps us (.mdata m x) k = none := by simp [instLPF, hl]
      simp only [toExpr] at h
      simp only [mapSpec, hcb, Option.getD_none, emvarS] at hnp
      simp [mapSpec, hcb, toExpr, ih hr hf k c h hnp]
  | proj s i x ih =>
    intro hr hf k c h hnp
    by_cases hl : (Expr.proj s i x).hasLevelParam = false
    · exact ilp_cut hr hf hl h
    · have hcb : instLPF ps us (.proj s i x) k = none := by simp [instLPF, hl]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      simp only [mapSpec, hcb, Option.getD_none, emvarS] at hnp
      simp [mapSpec, hcb, toExpr, ih hr hf k cx hx hnp, ConLeche.Expr.instantiateLevelParams]

/-- con-leche's level substitution with no parameters, or no values, is the
identity. -/
theorem cl_subst_nil_left (cus : List ConLeche.Level) :
    ∀ l : ConLeche.Level, ConLeche.Level.subst [] cus l = l := by
  intro l; induction l <;> simp_all [ConLeche.Level.subst, ConLeche.Level.subst.go]

theorem cl_subst_nil_right (ks : List ConLeche.Name) :
    ∀ l : ConLeche.Level, ConLeche.Level.subst ks [] l = l := by
  intro l
  induction l with
  | param n => cases ks <;> simp [ConLeche.Level.subst, ConLeche.Level.subst.go]
  | _ => simp_all [ConLeche.Level.subst]

theorem cl_ilp_id {ks : List ConLeche.Name} {cus : List ConLeche.Level}
    (hid : ∀ l, ConLeche.Level.subst ks cus l = l) :
    ∀ c : ConLeche.Expr, c.instantiateLevelParams ks cus = c := by
  intro c
  induction c with
  | const n us =>
    simp only [ConLeche.Expr.instantiateLevelParams]
    congr 1
    exact List.map_id'' hid us
  | _ => simp_all [ConLeche.Expr.instantiateLevelParams]

/-- **InLean's level instantiation simulates con-leche's** on a term in range
with no free variable (every checker site; con-leche's descends into a free
variable's type annotation, InLean's id has none). -/
theorem toExpr_instantiateLevelParams {fv : FVarId → Option ConLeche.Expr} {e : Expr}
    {c : ConLeche.Expr} (hr : Expr.RangeOk e) (hf : fvarS e = false) (h : toExpr fv e = some c)
    (ps : List Name) {us : List Level} {cus : List ConLeche.Level} (hus : toLevels us = some cus)
    (hnp : emvarS (EO.instantiateLevelParams e ps us) = false) :
    toExpr fv (EO.instantiateLevelParams e ps us) =
      some (c.instantiateLevelParams (ps.map toName) cus) := by
  rw [instantiateLevelParams_eq]
  split
  · rename_i hc
    rw [h]
    simp only [Bool.or_eq_true] at hc
    rcases hc with (hps | hus') | hl
    · rw [List.isEmpty_iff.1 hps, List.map_nil, cl_ilp_id (cl_subst_nil_left cus)]
    · have : us = [] := List.isEmpty_iff.1 hus'
      subst this
      simp only [toLevels, Option.some.injEq] at hus
      subst hus
      rw [cl_ilp_id (cl_subst_nil_right _)]
    · have hl' : e.hasLevelParam = false := by simpa using hl
      rw [ConLeche.Expr.instantiateLevelParams_eq_self]
      rw [hasLevelParam_toExpr e c h hf, ← Expr.hasLevelParam_eq hr, hl']
  · rename_i hc
    rw [instantiateLevelParams_eq] at hnp
    split at hnp
    · contradiction
    · exact toExpr_mapSpec_ilp ps hus e hr hf 0 c h hnp

/-! ### The memoised fold `EO.anyNode` -/

/-- The plain fold `EO.anyNode` computes: `p` decides a node, or the fold
asks the children (binder offset `+1` under a binder), left to right. -/
@[expose] def anySpec (p : Expr → Nat → Option Bool) : Expr → Nat → Bool
  | e@(.app g a), k => (p e k).getD (anySpec p g k || anySpec p a k)
  | e@(.lam _ t b _), k => (p e k).getD (anySpec p t k || anySpec p b (k + 1))
  | e@(.forallE _ t b _), k => (p e k).getD (anySpec p t k || anySpec p b (k + 1))
  | e@(.letE _ t v b _), k =>
    (p e k).getD (anySpec p t k || anySpec p v k || anySpec p b (k + 1))
  | e@(.mdata _ x), k => (p e k).getD (anySpec p x k)
  | e@(.proj _ _ x), k => (p e k).getD (anySpec p x k)
  | e, k => (p e k).getD false

section anyNode
attribute [local instance 2000] instBEqExprExact

theorem anySpec_some {p : Expr → Nat → Option Bool} {e : Expr} {k : Nat} {b : Bool}
    (h : p e k = some b) : anySpec p e k = b := by
  rw [anySpec.eq_def]; split <;> simp_all

/-- **The walk's plain descent is the structural fold.** -/
theorem anyP_spec (p : Expr → Nat → Option Bool) :
    ∀ (e : Expr) (k : Nat), EO.anyP p e k = anySpec p e k := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k
    cases hp : p (.app g a) k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_app hp, ihg, iha]; simp [anySpec, hp]
  | lam n t b bi iht ihb =>
    intro k
    cases hp : p (.lam n t b bi) k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_lam hp, iht, ihb]; simp [anySpec, hp]
  | forallE n t b bi iht ihb =>
    intro k
    cases hp : p (.forallE n t b bi) k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_forallE hp, iht, ihb]; simp [anySpec, hp]
  | letE n t v b nd iht ihv ihb =>
    intro k
    cases hp : p (.letE n t v b nd) k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_letE hp, iht, ihv, ihb]; simp [anySpec, hp]
  | mdata m x ih =>
    intro k
    cases hp : p (.mdata m x) k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_mdata hp, ih]; simp [anySpec, hp]
  | proj s i x ih =>
    intro k
    cases hp : p (.proj s i x) k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_proj hp, ih]; simp [anySpec, hp]
  | bvar | fvar | mvar | sort | const | lit =>
    intro k
    cases hp : p _ k with
    | some b => rw [EO.anyP_some hp, anySpec_some hp]
    | none => rw [EO.anyP_leaf hp rfl]; simp [anySpec, hp]

/-- **The memoised fold is the structural fold.** -/
theorem anyNode_spec (p : Expr → Nat → Option Bool) (e : Expr) (k : Nat) :
    EO.anyNode p e k = anySpec p e k := by
  rw [EO.anyNode_eq, anyP_spec]

end anyNode

/-! ### The application spine, `mdata` read through -/

theorem getAppFn_of_not_app {c : ConLeche.Expr} (h : ∀ f a, c ≠ .app f a) : c.getAppFn = c := by
  cases c <;> simp_all [ConLeche.Expr.getAppFn]

theorem getAppArgs_of_not_app {c : ConLeche.Expr} (h : ∀ f a, c ≠ .app f a) : c.getAppArgs = [] := by
  cases c <;> simp_all [ConLeche.Expr.getAppArgs]

/-- A translation that is not an application, at a node that is no `app` or
`mdata`. -/
theorem toExpr_not_app {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) {e : Expr}
    {c : ConLeche.Expr} (h : toExpr fv e = some c) (ha : ∀ g a, e ≠ .app g a)
    (hm : ∀ m x, e ≠ .mdata m x) : ∀ f a, c ≠ .app f a := by
  intro f a hc
  subst hc
  cases e with
  | app g x => exact ha g x rfl
  | mdata m x => exact hm m x rfl
  | fvar id => obtain ⟨_, _, h'⟩ := hfv id _ h; cases h'
  | mvar m => simp [toExpr] at h
  | bvar i => simp [toExpr] at h
  | lit l => simp [toExpr] at h
  | sort u => simp [toExpr] at h
  | const n us => simp [toExpr] at h
  | lam n t b bi =>
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, h'⟩ := h; cases h'
  | forallE n t b bi =>
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, h'⟩ := h; cases h'
  | letE n t v b nd =>
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, _, h'⟩ := h; cases h'
  | proj s i x =>
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h'⟩ := h; cases h'

/-- **The spine's head reads as con-leche's `getAppFn`.** -/
theorem toExpr_getAppFnT {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c →
      toExpr fv (Expr.getAppFnT e) = some c.getAppFn := by
  intro e
  induction e with
  | app g a ihg _ =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, -, rfl⟩ := h
    simp only [Expr.getAppFnT, ConLeche.Expr.getAppFn]
    exact ihg cg hg
  | mdata m x ih => intro c h; simp only [toExpr] at h; simp only [Expr.getAppFnT]; exact ih c h
  | _ =>
    intro c h
    rw [getAppFn_of_not_app (toExpr_not_app hfv h (by simp) (by simp))]
    exact h

/-- The spine's arguments, accumulated. -/
theorem toExpr_getAppArgsT_go {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (e : Expr) (c : ConLeche.Expr) (acc : List Expr) (cacc : List ConLeche.Expr),
      toExpr fv e = some c → acc.mapM (toExpr fv) = some cacc →
      (Expr.getAppArgsT.go e acc).mapM (toExpr fv) = some (c.getAppArgs ++ cacc) := by
  intro e
  induction e with
  | app g a ihg _ =>
    intro c acc cacc h hacc
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, ha, rfl⟩ := h
    simp only [Expr.getAppArgsT.go, ConLeche.Expr.getAppArgs, List.append_assoc,
      List.singleton_append]
    exact ihg cg (a :: acc) (ca :: cacc) hg (by simp [List.mapM_cons, ha, hacc])
  | mdata m x ih =>
    intro c acc cacc h hacc
    simp only [toExpr] at h; simp only [Expr.getAppArgsT.go]; exact ih c acc cacc h hacc
  | _ =>
    intro c acc cacc h hacc
    rw [getAppArgs_of_not_app (toExpr_not_app hfv h (by simp) (by simp))]
    simpa [Expr.getAppArgsT.go] using hacc

/-- **The spine's arguments read as con-leche's `getAppArgs`.** -/
theorem toExpr_getAppArgsT {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {e : Expr} {c : ConLeche.Expr} (h : toExpr fv e = some c) :
    (Expr.getAppArgsT e).toList.mapM (toExpr fv) = some c.getAppArgs := by
  simpa [Expr.getAppArgsT] using toExpr_getAppArgsT_go hfv e c [] [] h rfl

/-- **The spine's argument count is con-leche's.** -/
theorem getAppNumArgsT_eq {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c →
      Expr.getAppNumArgsT e = c.getAppArgs.length := by
  intro e
  induction e with
  | app g a ihg _ =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, -, rfl⟩ := h
    simp [Expr.getAppNumArgsT, ConLeche.Expr.getAppArgs, ihg cg hg]
  | mdata m x ih => intro c h; simp only [toExpr] at h; simp only [Expr.getAppNumArgsT]; exact ih c h
  | _ =>
    intro c h
    rw [getAppArgs_of_not_app (toExpr_not_app hfv h (by simp) (by simp))]
    rfl

/-! ### The guards: the cached fields, on a term in range, read as con-leche's -/

/-- con-leche's loose-variable bound of the translation is the term's range. -/
theorem bvarBound_toExpr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c → c.bvarBound = rangeS e := by
  intro e
  induction e with
  | bvar i => intro c h; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | fvar id => intro c h; obtain ⟨_, _, rfl⟩ := hfv id c h; rfl
  | mvar m => intro c h; simp [toExpr] at h
  | lit l => intro c h; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | sort u =>
    intro c h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | const n us =>
    intro c h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | app g a ihg iha =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, ha, rfl⟩ := h
    simp [ConLeche.Expr.bvarBound, rangeS, ihg cg hg, iha ca ha]
  | lam n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp [ConLeche.Expr.bvarBound, rangeS, iht ct ht, ihb cb hb]
  | forallE n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp [ConLeche.Expr.bvarBound, rangeS, iht ct ht, ihb cb hb]
  | letE n t v b nd iht ihv ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    simp [ConLeche.Expr.bvarBound, rangeS, iht ct ht, ihv cv hv, ihb cb hb]
  | mdata m x ih => intro c h; simp only [toExpr] at h; exact ih c h
  | proj s i x ih =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    simp [ConLeche.Expr.bvarBound, rangeS, ih cx hx]

/-- **The loose-variable guard**: on a term in range, InLean's cached range is
con-leche's bound of the translation. -/
theorem looseBVarRange_toExpr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) :
    e.looseBVarRange = c.bvarBound := by
  rw [Expr.looseBVarRange_eq hr, bvarBound_toExpr hfv e c h]

/-- con-leche's free-variable test of the translation is the term's. -/
theorem hasFvar_toExpr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ (e : Expr) (c : ConLeche.Expr), toExpr fv e = some c → c.hasFvar = fvarS e := by
  intro e
  induction e with
  | bvar i => intro c h; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | fvar id => intro c h; obtain ⟨_, _, rfl⟩ := hfv id c h; rfl
  | mvar m => intro c h; simp [toExpr] at h
  | lit l => intro c h; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | sort u =>
    intro c h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | const n us =>
    intro c h; simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | app g a ihg iha =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cg, hg, ca, ha, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, fvarS, ihg cg hg, iha ca ha]
  | lam n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, fvarS, iht ct ht, ihb cb hb]
  | forallE n t b bi iht ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, fvarS, iht ct ht, ihb cb hb]
  | letE n t v b nd iht ihv ihb =>
    intro c h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, fvarS, iht ct ht, ihv cv hv, ihb cb hb]
  | mdata m x ih => intro c h; simp only [toExpr] at h; exact ih c h
  | proj s i x ih =>
    intro c h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, fvarS, ih cx hx]

/-- **The free-variable guard**: on a term in range, InLean's cached flag is
con-leche's test of the translation. -/
theorem hasFVar_toExpr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {e : Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) :
    e.hasFVar = c.hasFvar := by
  rw [Expr.hasFVar_eq hr, hasFvar_toExpr hfv e c h]

/-! ### `EO.hasLooseBVar` -/

/-- `EO.hasLooseBVar`'s test. -/
@[expose] def hlbF (i : Nat) (x : Expr) (k : Nat) : Option Bool :=
  if x.looseBVarRange ≤ i + k then some false else
  match x with
  | .bvar j => some (j == i + k)
  | _ => none

theorem hasLooseBVar_eq (e : Expr) (i : Nat) :
    EO.hasLooseBVar e i = anySpec (hlbF i) e 0 :=
  anyNode_spec _ e 0

/-- con-leche's test is false at and above a term's bound. -/
theorem cl_hasLooseBVar_of_bound : ∀ {c : ConLeche.Expr} {n : Nat}, c.bvarBound ≤ n →
    ConLeche.Expr.hasLooseBVar n c = false := by
  intro c
  induction c with
  | bvar j =>
    intro n h; simp only [ConLeche.Expr.bvarBound] at h
    simp only [ConLeche.Expr.hasLooseBVar, beq_eq_false_iff_ne]; omega
  | app f a ihf iha =>
    intro n h; simp only [ConLeche.Expr.bvarBound] at h
    simp [ConLeche.Expr.hasLooseBVar, ihf (n := n) (by omega), iha (n := n) (by omega)]
  | lam ty b iht ihb =>
    intro n h; simp only [ConLeche.Expr.bvarBound] at h
    simp [ConLeche.Expr.hasLooseBVar, iht (n := n) (by omega), ihb (n := n + 1) (by omega)]
  | forallE ty b iht ihb =>
    intro n h; simp only [ConLeche.Expr.bvarBound] at h
    simp [ConLeche.Expr.hasLooseBVar, iht (n := n) (by omega), ihb (n := n + 1) (by omega)]
  | letE t v b iht ihv ihb =>
    intro n h; simp only [ConLeche.Expr.bvarBound] at h
    simp [ConLeche.Expr.hasLooseBVar, iht (n := n) (by omega), ihv (n := n) (by omega),
      ihb (n := n + 1) (by omega)]
  | proj s i x ih =>
    intro n h; simp only [ConLeche.Expr.bvarBound] at h
    simp [ConLeche.Expr.hasLooseBVar, ih h]
  | _ => intro n _; simp [ConLeche.Expr.hasLooseBVar]

/-- **InLean's loose-variable occurrence test reads as con-leche's** on a
term in range (at binder offset `k`). -/
theorem hasLooseBVar_toExpr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) (i : Nat) :
    ∀ (e : Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      anySpec (hlbF i) e k = ConLeche.Expr.hasLooseBVar (i + k) c := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro hr k c h
    by_cases hcut : (Expr.app g a).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVar_of_bound hcut).symm
    · have hn : hlbF i (.app g a) k = none := by simp [hlbF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      simp [anySpec, hn, ihg hr.1 k cg hg, iha hr.2 k ca ha, ConLeche.Expr.hasLooseBVar]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.lam n t b bi).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVar_of_bound hcut).symm
    · have hn : hlbF i (.lam n t b bi) k = none := by simp [hlbF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [anySpec, hn, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, ConLeche.Expr.hasLooseBVar,
        Nat.add_assoc]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Expr.forallE n t b bi).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVar_of_bound hcut).symm
    · have hn : hlbF i (.forallE n t b bi) k = none := by simp [hlbF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      simp [anySpec, hn, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, ConLeche.Expr.hasLooseBVar,
        Nat.add_assoc]
  | letE n t v b nd iht ihv ihb =>
    intro hr k c h
    by_cases hcut : (Expr.letE n t v b nd).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVar_of_bound hcut).symm
    · have hn : hlbF i (.letE n t v b nd) k = none := by simp [hlbF, hcut]
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      simp [anySpec, hn, iht hr.1 k ct ht, ihv hr.2.1 k cv hv, ihb hr.2.2 (k + 1) cb hb,
        ConLeche.Expr.hasLooseBVar, Nat.add_assoc]
  | mdata m x ih =>
    intro hr k c h
    by_cases hcut : (Expr.mdata m x).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVar_of_bound hcut).symm
    · have hn : hlbF i (.mdata m x) k = none := by simp [hlbF, hcut]
      simp only [toExpr] at h
      simp [anySpec, hn, ih hr k c h]
  | proj s j x ih =>
    intro hr k c h
    by_cases hcut : (Expr.proj s j x).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVar_of_bound hcut).symm
    · have hn : hlbF i (.proj s j x) k = none := by simp [hlbF, hcut]
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      simp [anySpec, hn, ih hr k cx hx, ConLeche.Expr.hasLooseBVar]
  | bvar j =>
    intro hr k c h
    simp only [toExpr, Option.some.injEq] at h; subst h
    by_cases hcut : (Expr.bvar j).looseBVarRange ≤ i + k
    · rw [anySpec_some (show hlbF i _ k = some false by simp [hlbF, hcut])]
      rw [Expr.looseBVarRange_eq hr] at hcut
      simp only [rangeS] at hcut
      simp only [ConLeche.Expr.hasLooseBVar]
      exact (beq_false_of_ne (a := i + k) (b := j) (by omega)).symm
    · rw [anySpec_some (show hlbF i _ k = some (j == i + k) by simp [hlbF, hcut])]
      simp only [ConLeche.Expr.hasLooseBVar]
      by_cases hj : j = i + k
      · subst hj; simp
      · have : i + k ≠ j := fun h => hj h.symm
        rw [beq_false_of_ne hj, beq_false_of_ne this]
  | mvar m => intro _ k c h; simp [toExpr] at h
  | fvar id =>
    intro hr k c h
    obtain ⟨_, _, rfl⟩ := hfv id c h
    rw [anySpec_some (show hlbF i _ k = some false by
      simp [hlbF, Expr.looseBVarRange_eq hr, rangeS])]
    rfl
  | sort u =>
    intro hr k c h
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
    rw [anySpec_some (show hlbF i _ k = some false by
      simp [hlbF, Expr.looseBVarRange_eq hr, rangeS])]
    rfl
  | const n us =>
    intro hr k c h
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
    rw [anySpec_some (show hlbF i _ k = some false by
      simp [hlbF, Expr.looseBVarRange_eq hr, rangeS])]
    rfl
  | lit l =>
    intro hr k c h
    simp only [toExpr, Option.some.injEq] at h; subst h
    rw [anySpec_some (show hlbF i _ k = some false by
      simp [hlbF, Expr.looseBVarRange_eq hr, rangeS])]
    rfl

/-- **`EO.hasLooseBVar` reads as con-leche's `hasLooseBVar`.** -/
theorem toExpr_hasLooseBVar {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) {e : Expr}
    {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) (i : Nat) :
    EO.hasLooseBVar e i = ConLeche.Expr.hasLooseBVar i c := by
  rw [hasLooseBVar_eq, hasLooseBVar_toExpr hfv i e hr 0 c h]; rfl

end InLeanProof
