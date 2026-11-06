module

public import InLeanProof.ToCL
public import InLeanProof.Fields
public import ConLeche.Verify.Shift
public import ConLeche.Verify.Subst
public import ConLeche.Verify.InstList
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
   `mapSpec f` (the memo invariant: every entry is `mapSpec`'s answer).
2. Per operation, `toExpr` commutes: InLean's lift on a term in range
   (`Expr.RangeOk`) reading as `c` reads as con-leche's `liftLooseBVars` of
   `c`.  The walks' cutoffs read Lean's cached fields, which is where the
   stop-gap axioms enter (`Expr.looseBVarRange_eq`).
-/

public section

namespace InLeanProof

open Lean InLean

/-- The plain structural map a walk computes: `f` decides a node, or the
walk rebuilds it from its mapped children (binder offset `+1` under a
binder). -/
def mapSpec (f : Expr → Nat → Option Expr) : Expr → Nat → Expr
  | e@(.app g a), k => (f e k).getD (.app (mapSpec f g k) (mapSpec f a k))
  | e@(.lam n t b bi), k => (f e k).getD (.lam n (mapSpec f t k) (mapSpec f b (k + 1)) bi)
  | e@(.forallE n t b bi), k =>
    (f e k).getD (.forallE n (mapSpec f t k) (mapSpec f b (k + 1)) bi)
  | e@(.letE n t v b nd), k =>
    (f e k).getD (.letE n (mapSpec f t k) (mapSpec f v k) (mapSpec f b (k + 1)) nd)
  | e@(.mdata m x), k => (f e k).getD (.mdata m (mapSpec f x k))
  | e@(.proj s i x), k => (f e k).getD (.proj s i (mapSpec f x k))
  | e, k => (f e k).getD e

/-- The memo invariant: every recorded answer is `mapSpec`'s. -/
def MapMemoInv (f : Expr → Nat → Option Expr) (memo : EO.Memo) : Prop :=
  ∀ (key : Expr × Nat) (r : Expr), memo[key]? = some r → r = mapSpec f key.1 key.2

theorem MapMemoInv.empty {f : Expr → Nat → Option Expr} : MapMemoInv f {} := by
  intro key r h; simp at h

theorem MapMemoInv.insert {f : Expr → Nat → Option Expr} {memo : EO.Memo}
    (hm : MapMemoInv f memo) {e : Expr} {k : Nat} {r : Expr} (hr : r = mapSpec f e k) :
    MapMemoInv f (memo.insert (e, k) r) := by
  intro key r' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    have : (e, k) = key := eq_of_beq heq
    subst this
    simp only [Option.some.injEq] at h
    exact h ▸ hr
  · exact hm key r' h

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

/-- **The memoised walk is its plain spec** (and keeps the invariant). -/
theorem mapOff_spec (f : Expr → Nat → Option Expr) :
    ∀ (e : Expr) (k : Nat) (memo : EO.Memo), MapMemoInv f memo →
      (EO.mapOff f e k memo).1 = mapSpec f e k ∧ MapMemoInv f (EO.mapOff f e k memo).2 := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro k memo hm
    rw [EO.mapOff]
    cases hf : f (.app g a) k with
    | some r => exact ⟨(mapSpec_eq_of_some hf).symm, hm⟩
    | none =>
      simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hhit : memo[(Expr.app g a, k)]? with
      | some r => exact ⟨hm _ _ hhit, hm⟩
      | none =>
        obtain ⟨h1, h2⟩ := ihg k memo hm
        obtain ⟨h3, h4⟩ := iha k _ h2
        have hv : (Expr.app g a).updateApp! (EO.mapOff f g k memo).1
            (EO.mapOff f a k (EO.mapOff f g k memo).2).1 = mapSpec f (.app g a) k := by
          rw [h1, h3]; simp [mapSpec, hf, Expr.updateApp!, mkApp]
        exact ⟨hv, h4.insert hv⟩
  | lam n t b bi iht ihb =>
    intro k memo hm
    rw [EO.mapOff]
    cases hf : f (.lam n t b bi) k with
    | some r => exact ⟨(mapSpec_eq_of_some hf).symm, hm⟩
    | none =>
      simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hhit : memo[(Expr.lam n t b bi, k)]? with
      | some r => exact ⟨hm _ _ hhit, hm⟩
      | none =>
        obtain ⟨h1, h2⟩ := iht k memo hm
        obtain ⟨h3, h4⟩ := ihb (k + 1) _ h2
        have hv : (Expr.lam n t b bi).updateLambdaE! (EO.mapOff f t k memo).1
            (EO.mapOff f b (k + 1) (EO.mapOff f t k memo).2).1 = mapSpec f (.lam n t b bi) k := by
          rw [h1, h3]; simp [mapSpec, hf, Expr.updateLambdaE!, Expr.updateLambda!, mkLambda]
        exact ⟨hv, h4.insert hv⟩
  | forallE n t b bi iht ihb =>
    intro k memo hm
    rw [EO.mapOff]
    cases hf : f (.forallE n t b bi) k with
    | some r => exact ⟨(mapSpec_eq_of_some hf).symm, hm⟩
    | none =>
      simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hhit : memo[(Expr.forallE n t b bi, k)]? with
      | some r => exact ⟨hm _ _ hhit, hm⟩
      | none =>
        obtain ⟨h1, h2⟩ := iht k memo hm
        obtain ⟨h3, h4⟩ := ihb (k + 1) _ h2
        have hv : (Expr.forallE n t b bi).updateForallE! (EO.mapOff f t k memo).1
            (EO.mapOff f b (k + 1) (EO.mapOff f t k memo).2).1
              = mapSpec f (.forallE n t b bi) k := by
          rw [h1, h3]; simp [mapSpec, hf, Expr.updateForallE!, Expr.updateForall!, mkForall]
        exact ⟨hv, h4.insert hv⟩
  | letE n t v b nd iht ihv ihb =>
    intro k memo hm
    rw [EO.mapOff]
    cases hf : f (.letE n t v b nd) k with
    | some r => exact ⟨(mapSpec_eq_of_some hf).symm, hm⟩
    | none =>
      simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hhit : memo[(Expr.letE n t v b nd, k)]? with
      | some r => exact ⟨hm _ _ hhit, hm⟩
      | none =>
        obtain ⟨h1, h2⟩ := iht k memo hm
        obtain ⟨h3, h4⟩ := ihv k _ h2
        obtain ⟨h5, h6⟩ := ihb (k + 1) _ h4
        have hv : (Expr.letE n t v b nd).updateLetE! (EO.mapOff f t k memo).1
            (EO.mapOff f v k (EO.mapOff f t k memo).2).1
            (EO.mapOff f b (k + 1) (EO.mapOff f v k (EO.mapOff f t k memo).2).2).1
              = mapSpec f (.letE n t v b nd) k := by
          rw [h1, h3, h5]; simp [mapSpec, hf, Expr.updateLetE!, Expr.updateLet!]
        exact ⟨hv, h6.insert hv⟩
  | mdata m x ih =>
    intro k memo hm
    rw [EO.mapOff]
    cases hf : f (.mdata m x) k with
    | some r => exact ⟨(mapSpec_eq_of_some hf).symm, hm⟩
    | none =>
      simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hhit : memo[(Expr.mdata m x, k)]? with
      | some r => exact ⟨hm _ _ hhit, hm⟩
      | none =>
        obtain ⟨h1, h2⟩ := ih k memo hm
        have hv : (Expr.mdata m x).updateMData! (EO.mapOff f x k memo).1
            = mapSpec f (.mdata m x) k := by
          rw [h1]; simp [mapSpec, hf, Expr.updateMData!, mkMData]
        exact ⟨hv, h2.insert hv⟩
  | proj s i x ih =>
    intro k memo hm
    rw [EO.mapOff]
    cases hf : f (.proj s i x) k with
    | some r => exact ⟨(mapSpec_eq_of_some hf).symm, hm⟩
    | none =>
      simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hhit : memo[(Expr.proj s i x, k)]? with
      | some r => exact ⟨hm _ _ hhit, hm⟩
      | none =>
        obtain ⟨h1, h2⟩ := ih k memo hm
        have hv : (Expr.proj s i x).updateProj! (EO.mapOff f x k memo).1
            = mapSpec f (.proj s i x) k := by
          rw [h1]; simp [mapSpec, hf, Expr.updateProj!, mkProj]
        exact ⟨hv, h2.insert hv⟩
  | bvar | fvar | mvar | sort | const | lit =>
    intro k memo hm
    unfold EO.mapOff
    rw [mapSpec_leaf f k rfl]
    cases f _ k <;> exact ⟨rfl, hm⟩

/-- The walk from an empty memo. -/
theorem mapOff_empty (f : Expr → Nat → Option Expr) (e : Expr) (k : Nat) :
    (EO.mapOff f e k {}).1 = mapSpec f e k :=
  (mapOff_spec f e k {} MapMemoInv.empty).1

/-! ## The reading of a term below its range -/

/-- A free-variable translation answers only con-leche free variables
(InLean's table does: `FVarTable.transNum`). -/
def FVarsOnly (fv : FVarId → Option ConLeche.Expr) : Prop :=
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
def liftF (s d : Nat) (x : Expr) (k : Nat) : Option Expr :=
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
  · exact mapOff_empty _ e 0

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
def instF (subst : Array Expr) (x : Expr) (k : Nat) : Option Expr :=
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
  unfold EO.instantiate
  dsimp only
  split
  · rfl
  · exact mapOff_empty _ e 0

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

end InLeanProof
