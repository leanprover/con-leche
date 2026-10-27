module

import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.Shift
import ConLeche.Verify.PropRead
import ConLeche.Verify.EnvWF
import ConLeche.Verify.InstLevels
public import ConLeche.Verify.InferIOLeaves
import ConLeche.Verify.Knot
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Abstract
import ConLeche.Verify.InstSpine
public section

/-!
# Depth invariance of the checker core

The checker core threads a binder depth, used only to name freshly
opened `fvar`s.  This module proves that every entry point's *result*
is independent of the ambient depth, for inputs well-scoped at both
depths — the theorem that justifies memoizing the executed knot
(`ConLeche/Cached/CoreC.lean`) under depth-free keys.

The proof is a bisimulation: a run at depth `d` on `e` is matched
against the run at depth `d + 1` on `shiftFrom p e` (all `fvar`s at
indices `≥ p` bumped by one, `p ≤ d` the shift point); the two runs
step in lock-step, results relating by the shift.  One claim per core
entry point (`ShiftClaims`), one helper lemma per record-parameterized
body helper (at the same fuel, against `pureFns mode env fuel`), one fuel
induction at the knot.  Setting `p := d` and shrinking with
`shiftFrom_eq_self` turns the bisimulation into
`whnfCore mode env fuel (d+1) e = whnfCore mode env fuel d e` for `e` scoped at
`d`, and chaining walks any two well-scoped depths
(`whnfCore_depth_inv` and friends).
-/

namespace ConLeche

variable {mode : CheckMode}


open Expr

/-- The skip of `U E C a` (task #368) reads only
fvar-free terms, so shifting does not change it. -/
theorem bvUnsatSkip_shiftFrom {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry} {p : Nat} {f a body : Expr} :
    bvUnsatSkip find? findProj? (shiftFrom p f) (shiftFrom p a) (shiftFrom p body) =
      bvUnsatSkip find? findProj? f a body := by
  by_cases hf : f.hasFvar = false
  · by_cases ha : a.hasFvar = false
    · by_cases hb : body.hasFvar = false
      · rw [shiftFrom_eq_self_of_not_hasFvar hf, shiftFrom_eq_self_of_not_hasFvar ha,
          shiftFrom_eq_self_of_not_hasFvar hb]
      · simp only [Bool.not_eq_false] at hb
        simp [bvUnsatSkip, hasFvar_shiftFrom, hb]
    · simp only [Bool.not_eq_false] at ha
      simp [bvUnsatSkip, hasFvar_shiftFrom, ha]
  · simp only [Bool.not_eq_false] at hf
    simp [bvUnsatSkip, hasFvar_shiftFrom, hf]


/-! ## `Except` bind relators -/

/-- Relate two `CheckM` binds: scrutinees related by a value map,
continuations pointwise by a result map. -/
private theorem bind_rel {α α' β β' : Type} {x : CheckM α} {x' : CheckM α'}
    {g : α → CheckM β} {g' : α' → CheckM β'} (σx : α → α') (σ : β → β')
    (hx : x' = x.map σx)
    (hg : ∀ a, x = .ok a → g' (σx a) = (g a).map σ) :
    x' >>= g' = (x >>= g).map σ := by
  subst hx
  cases x with
  | error err => rfl
  | ok a => exact hg a rfl

/-- `bind_rel` with an unchanged scrutinee. -/
private theorem bind_rel_eq {α β β' : Type} {x x' : CheckM α}
    {g : α → CheckM β} {g' : α → CheckM β'} (σ : β → β')
    (hx : x' = x)
    (hg : ∀ a, x = .ok a → g' a = (g a).map σ) :
    x' >>= g' = (x >>= g).map σ := by
  subst hx
  cases x' with
  | error err => rfl
  | ok a => exact hg a rfl

/-- Relate two `CheckM` binds with equal results (the `Bool`-valued
claims): scrutinees related by a value map, continuations equal. -/
private theorem bind_congr {α α' β : Type} {x : CheckM α} {x' : CheckM α'}
    {g : α → CheckM β} {g' : α' → CheckM β} (σx : α → α')
    (hx : x' = x.map σx)
    (hg : ∀ a, x = .ok a → g' (σx a) = g a) :
    x' >>= g' = x >>= g := by
  subst hx
  cases x with
  | error err => rfl
  | ok a => exact hg a rfl

/-- `bind_congr` with an unchanged scrutinee. -/
private theorem bind_congr_eq {α β : Type} {x x' : CheckM α}
    {g g' : α → CheckM β}
    (hx : x' = x)
    (hg : ∀ a, x = .ok a → g' a = g a) :
    x' >>= g' = x >>= g := by
  subst hx
  cases x' with
  | error err => rfl
  | ok a => exact hg a rfl

@[local simp]
private theorem map_ok {α β : Type} (σ : α → β) (a : α) :
    (Except.ok a : CheckM α).map σ = .ok (σ a) := rfl

/-- Congruence for `if` with a common condition. -/
private theorem ite_congr' {α : Sort _} {c : Prop} [Decidable c]
    {x y x' y' : α} (hx : c → x' = x) (hy : ¬ c → y' = y) :
    (if c then x' else y') = (if c then x else y) := by
  split
  next h => exact hx h
  next h => exact hy h

/-- Congruence for `if` with a common condition, under a result map. -/
private theorem ite_rel {β β' : Type} {c : Prop} [Decidable c]
    {x' y' : CheckM β'} {x y : CheckM β} (σ : β → β')
    (hx : c → x' = x.map σ) (hy : ¬ c → y' = y.map σ) :
    (if c then x' else y') = (if c then x else y).map σ := by
  split
  next h => exact hx h
  next h => exact hy h

/-! ## Small shift facts about the checker's syntactic helpers -/

/-- The index of a shifted `fvar`. -/
private def shiftIdx (p i : Nat) : Nat := if p ≤ i then i + 1 else i

/-- The annotation of a shifted `fvar`. -/
private def shiftTy (p i : Nat) (ty : Expr) : Expr :=
  if p ≤ i then shiftFrom p ty else ty

/-- `shiftFrom` on an `fvar`, in constructor-headed form (so that
`match`es on shifted scrutinees reduce). -/
private theorem shiftFrom_fvar (p idx : Nat) (ty : Expr) :
    shiftFrom p (.fvar idx ty) =
      .fvar (shiftIdx p idx) (shiftTy p idx ty) := by
  by_cases h : p ≤ idx <;>
    simp [shiftFrom, shiftIdx, shiftTy, h, ge_iff_le]

private theorem shiftIdx_beq (p i j : Nat) :
    (shiftIdx p i == shiftIdx p j) = (i == j) := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [beq_iff_eq, beq_iff_eq]
  simp only [shiftIdx]
  by_cases hi : p ≤ i <;> by_cases hj : p ≤ j <;>
    simp only [hi, hj, ite_true, ite_false] <;> omega

/-- Shifting a freshly opened `fvar` at depth `d ≥ p`. -/
private theorem shiftFrom_fvar_ge {p d : Nat} (h : p ≤ d)
    (ty : Expr) :
    shiftFrom p (.fvar d ty) = .fvar (d + 1) (shiftFrom p ty) := by
  simp [shiftFrom, ge_iff_le, h]

/-- `shiftFrom` distributes over `app` (definitional; a targeted simp
lemma that leaves `fvar` leaves to `shiftFrom_fvar`). -/
private theorem shiftFrom_app (p : Nat) (f a : Expr) :
    shiftFrom p (.app f a) = .app (shiftFrom p f) (shiftFrom p a) := rfl

/-- `getD` with the (shift-invariant) `bvar 0` default commutes with
mapping the shift. -/
private theorem getD_map_shiftFrom (p : Nat) :
    ∀ (l : List Expr) (n : Nat),
      (l.map (shiftFrom p)).getD n (.bvar 0) =
        shiftFrom p (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons x xs ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n => simpa [List.getD] using ih n

/-- `isCtorApp` only reads head constants, which shifting preserves. -/
private theorem isCtorApp_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    isCtorApp env (shiftFrom p e) = isCtorApp env e := by
  unfold isCtorApp
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- `rawNatLit?` only reads literal and constant heads, which shifting
preserves. -/
private theorem rawNatLit?_shiftFrom (p : Nat) (e : Expr) :
    rawNatLit? (shiftFrom p e) = rawNatLit? e := by
  cases e <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl

/-- The constructor form of a literal is closed, hence shift-fixed. -/
private theorem shiftFrom_natLitToConstructor (p n : Nat) :
    shiftFrom p (natLitToConstructor n) = natLitToConstructor n := by
  cases n <;> rfl

/-- The literal-major conversion commutes with the shift. -/
private theorem litToCtorIfNat_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    litToCtorIfNat env (shiftFrom p e) = shiftFrom p (litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    show litToCtorIfNat env (.lit (.natVal n)) = _
    rw [litToCtorIfNat]
    split
    · rw [shiftFrom_natLitToConstructor]
    · rfl
  | .lit (.strVal _) => rfl
  | .bvar _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ => rfl
  | .fvar idx ty => simp [litToCtorIfNat, shiftFrom_fvar]

/-- Delta-unfolding commutes with the shift (stored values are closed
by `EnvWF`). -/
private theorem unfoldDefinition_shiftFrom {env : Env} (henv : EnvWF env)
    (p : Nat) (e : Expr) :
    unfoldDefinition env (shiftFrom p e) =
      (unfoldDefinition env e).map (shiftFrom p) := by
  unfold unfoldDefinition
  rw [getAppFn_shiftFrom]
  cases hfn : e.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const n us =>
  simp only [shiftFrom]
  cases hf : env.find? n with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case defnInfo cv value hint =>
      dsimp only
      split
      · have hval : (value.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          obtain ⟨-, -, -, -, hvalwf, -⟩ := henv.consts _ (Env.find?_mem hf)
          obtain ⟨hvc, -, -, -⟩ := hvalwf cv value hint rfl
          rw [hasFvar_instantiateLevelParams]
          exact hvc
        rw [getAppArgs_shiftFrom, Option.map_some]
        rw [show Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            (e.getAppArgs.map (shiftFrom p)) =
          shiftFrom p (Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs) from by
          rw [shiftFrom_mkAppN, shiftFrom_eq_self_of_not_hasFvar hval]]
      · rfl

/-- `headHint` only reads a head constant's name, which shifting
preserves. -/
private theorem headHint_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    headHint env (shiftFrom p e) = headHint env e := by
  unfold headHint
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- The lazy-delta *decision* only reads the head constant and its
level count, which shifting preserves (task #106). -/
private theorem unfoldableHead_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    unfoldableHead env (shiftFrom p e) = unfoldableHead env e := by
  unfold unfoldableHead
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- The same-head test only reads app shapes and head constants, which
shifting preserves. -/
private theorem sameConstHeads_shiftFrom (p : Nat) (a b : Expr) :
    sameConstHeads (shiftFrom p a) (shiftFrom p b) = sameConstHeads a b := by
  cases a <;> cases b <;>
    try (first
      | rfl
      | (simp only [shiftFrom_fvar]; rfl))
  case app.app f₁ x₁ f₂ x₂ =>
    show sameConstHeads (.app (shiftFrom p f₁) (shiftFrom p x₁))
      (.app (shiftFrom p f₂) (shiftFrom p x₂)) = _
    unfold sameConstHeads
    dsimp only
    rw [getAppFn_shiftFrom, getAppFn_shiftFrom]
    generalize f₁.getAppFn = g₁
    generalize f₂.getAppFn = g₂
    cases g₁ <;> cases g₂ <;> (try simp only [shiftFrom_fvar]) <;> rfl

/-- Peeling a `∀`-telescope along arguments commutes with the shift. -/
private theorem piResidual_shiftFrom {p : Nat} :
    ∀ (as : List Expr) (t : Expr),
      piResidual (shiftFrom p t) (as.map (shiftFrom p)) =
        (piResidual t as).map (shiftFrom p)
  | [], t => rfl
  | a :: as, t => by
    cases t <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE ty body =>
      show piResidual ((shiftFrom p body).instantiate1 (shiftFrom p a))
        (as.map (shiftFrom p)) = _
      rw [← shiftFrom_instantiate1_gen]
      exact piResidual_shiftFrom as _

/-! ## The bisimulation claims -/

/-- `whnfCore` commutes with the fvar shift. -/
def WhnfCoreShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {c : Bool} {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    whnfCore mode env fuel (d + 1) (shiftFrom p e) c =
      (whnfCore mode env fuel d e c).map (shiftFrom p)

/-- The `whnf` reduction loop commutes with the fvar shift. -/
def WhnfShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    whnf mode env fuel (d + 1) (shiftFrom p e) =
      (whnf mode env fuel d e).map (shiftFrom p)

/-- `inferTypeCore` commutes with the fvar shift. -/
def InferShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    inferTypeCore mode env fuel (d + 1) (shiftFrom p e) =
      (inferTypeCore mode env fuel d e).map (shiftFrom p)

/-- `isDefEqCore` is invariant under the fvar shift. -/
def DefEqShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {a b : Expr}, WScoped d a → WScoped d b →
    isDefEqCore mode env fuel (d + 1) (shiftFrom p a) (shiftFrom p b) =
      isDefEqCore mode env fuel d a b

/-- The knot's io slot commutes with the fvar shift (task #172 B4): the
io lane's own walk (`inferIOCore_step` below). -/
def InferIOShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    inferTypeIO mode env fuel (d + 1) (shiftFrom p e) =
      (inferTypeIO mode env fuel d e).map (shiftFrom p)

/-- All entry-point bisimulation claims at one fuel. -/
structure ShiftClaims (mode : CheckMode) (env : Env) (fuel : Nat) : Prop where
  whnfCore : WhnfCoreShift mode env fuel
  whnf : WhnfShift mode env fuel
  infer : InferShift mode env fuel
  defeq : DefEqShift mode env fuel
  /-- the eager slot (task #353): the eager tower's `defeq` -/
  defeqE : DefEqShift mode.toEager env fuel
  inferIO : InferIOShift mode env fuel

/-! ## Helper bodies at the same fuel

Every record-parameterized helper commutes with the shift, given the
entry-point claims at the same fuel (the helpers only call the record's
entry points; the list helpers recurse structurally). -/

/-- An `eagerReduce _ _` application stays one under the shift (its
head is a constant, which the shift fixes). -/
theorem isEagerReduce_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).isEagerReduce = e.isEagerReduce := by
  match e with
  | .app (.app f x) y =>
    cases f <;> first
      | rfl
      | (simp only [shiftFrom]; split <;> rfl)
  | .app (.fvar i t) y => simp only [shiftFrom]; split <;> rfl
  | .app (.bvar _) _ | .app (.sort _) _ | .app (.const _ _) _ | .app (.lam _ _) _
  | .app (.forallE _ _) _ | .app (.letE _ _ _) _ | .app (.lit _) _
  | .app (.proj _ _ _) _ => rfl
  | .fvar i t => simp only [shiftFrom]; split <;> rfl
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _
  | .lit _ | .proj _ _ _ => rfl

section Helpers

variable {env : Env} {fuel : Nat}

private theorem ensureSort_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    ensureSort (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      ensureSort (pureFns mode env fuel) env d e := by
  simp only [ensureSort]
  refine bind_congr _ (ih.whnf hpd hw) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem reduceNat_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    reduceNat (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (reduceNat (pureFns mode env fuel) env d e).map
        (Option.map (shiftFrom p)) := by
  match e with
  | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    first
    | rfl
    | (simp only [shiftFrom_fvar]; rfl)
  | .app f a =>
    have hwfa : WScoped d f ∧ WScoped d a := by simpa only [WScoped] using hw
    match f with
    | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
    | .letE _ _ _ | .lit _ | .proj _ _ _ =>
      first
      | rfl
      | (simp only [shiftFrom_app, shiftFrom_fvar]; rfl)
    | .const c us =>
      match us with
      | _ :: _ => rfl
      | [] =>
        show reduceNat _ env (d + 1) (.app (.const c []) (shiftFrom p a)) = _
        simp only [reduceNat]
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
        intro w _
        rw [rawNatLit?_shiftFrom]
        cases rawNatLit? w <;> rfl
    | .app g b =>
      have hwgb : WScoped d g ∧ WScoped d b := by
        simpa only [WScoped] using hwfa.1
      match g with
      | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ | .forallE _ _
      | .letE _ _ _ | .lit _ | .proj _ _ _ | .app _ _ =>
        first
        | rfl
        | (simp only [shiftFrom_app, shiftFrom_fvar]; rfl)
      | .const c us =>
        match us with
        | _ :: _ => rfl
        | [] =>
          show reduceNat _ env (d + 1)
            (.app (.app (.const c []) (shiftFrom p b)) (shiftFrom p a)) = _
          simp only [reduceNat]
          refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
          · -- first argument first; the second only behind a literal (D15)
            refine bind_rel _ _ (ih.whnf hpd hwgb.2) ?_
            intro w₁ _
            rw [rawNatLit?_shiftFrom]
            cases rawNatLit? w₁ with
            | none => rfl
            | some n₁ =>
              refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
              intro w₂ _
              rw [rawNatLit?_shiftFrom]
              cases rawNatLit? w₂ with
              | none => rfl
              | some n₂ =>
                dsimp only
                cases hres : natOpResult c n₁ n₂ with
                | none => rfl
                | some r =>
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                    rfl
          · refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel _ _ (ih.whnf hpd hwgb.2) ?_
            intro w₁ _
            rw [rawNatLit?_shiftFrom]
            cases rawNatLit? w₁ with
            | none => rfl
            | some n₁ =>
              refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
              intro w₂ _
              rw [rawNatLit?_shiftFrom]
              cases rawNatLit? w₂ <;> rfl

/-- `reduceNat_shift` under the defeq-side fvar guard: the pruned
branch is `pure none` on both sides. -/
private theorem reduceNatIf_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) (g : Bool) :
    (if g then reduceNat (pureFns mode env fuel) env (d + 1) (shiftFrom p e)
      else pure none) =
      (if g then reduceNat (pureFns mode env fuel) env d e
        else (pure none : CheckM (Option Expr))).map
        (Option.map (shiftFrom p)) := by
  cases g
  · rfl
  · exact reduceNat_shift henv ih hpd hw

/-- A `some` result of the guarded fold always comes from `reduceNat`
itself (the pruned branch returns `none`). -/
private theorem reduceNatIf_some {g : Bool} {x : CheckM (Option Expr)}
    {a : Expr} (h : (if g then x else pure none) = .ok (some a)) :
    x = .ok (some a) := by
  cases g
  · exact absurd h (by simp [pure, Except.pure])
  · exact h

/-- Shifting keeps the head's kind (task #342 L18). -/
private theorem ioNeutral_shiftFrom (p : Nat) (e : Expr) :
    (shiftFrom p e).ioNeutral = e.ioNeutral := by
  unfold Expr.ioNeutral
  rw [getAppFn_shiftFrom]
  cases e.getAppFn <;> try rfl
  case fvar idx ty =>
    simp only [shiftFrom]
    by_cases h : idx ≥ p <;> simp [h]

/-- Shifting keeps a ∀ a ∀ (task #342 L18). -/
private theorem isForallE_shiftFrom (p : Nat) (e : Expr) :
    (shiftFrom p e).isForallE = e.isForallE := by
  cases e <;> try rfl
  case fvar idx ty => simp only [shiftFrom]; split <;> rfl

private theorem iotaCertsFull_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {args : List Expr} {ty : Expr}, WScoped d ty →
      (∀ x ∈ args, WScoped d x) →
      iotaCertsFull (pureFns mode env fuel) env (d + 1) (shiftFrom p ty)
          (args.map (shiftFrom p)) =
        iotaCertsFull (pureFns mode env fuel) env d ty args := by
  intro args
  induction args with
  | nil => intro ty _ _; rfl
  | cons arg rest ihrest =>
    intro ty hwty hwargs
    have hwarg : WScoped d arg := hwargs arg (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ rest, WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    match ty with
    | .forallE ty' body =>
      have hwty' : WScoped d ty' ∧ WScoped d body := by
        simpa only [WScoped] using hwty
      show (do
          let ta ← (pureFns mode env fuel).infer (d + 1) (shiftFrom p arg)
          if ← (pureFns mode env fuel).defeq (d + 1) ta (shiftFrom p ty') then
            iotaCertsFull (pureFns mode env fuel) env (d + 1)
              ((shiftFrom p body).instantiate1 (shiftFrom p arg))
              (rest.map (shiftFrom p))
          else pure false : CheckM Bool) =
        (do
          let ta ← (pureFns mode env fuel).infer d arg
          if ← (pureFns mode env fuel).defeq d ta ty' then
            iotaCertsFull (pureFns mode env fuel) env d (body.instantiate1 arg) rest
          else pure false : CheckM Bool)
      have hrest := ihrest (WScoped.instantiate1_gen hwarg 0 hwty'.2) hwrest
      rw [shiftFrom_instantiate1_gen] at hrest
      refine bind_congr _ (ih.infer hpd hwarg) ?_
      intro ta hta
      refine bind_congr_eq
        (ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hwarg)
          hwty'.1) ?_
      intro bb _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      exact hrest
    | .bvar i => rfl
    | .fvar idx ty'' => rw [shiftFrom_fvar]; rfl
    | .sort u => rfl
    | .const n' us => rfl
    | .app f a => rfl
    | .lam ty'' body' => rfl
    | .letE ty'' v' b' => rfl
    | .lit l => rfl
    | .proj sp i' e' => rfl

/-- The fabricated projections commute with the shift (the `.proj`
nodes by `shiftFrom`'s own clause). -/
private theorem etaProjs_shift (p : Nat) (T : Name) (b : Expr) (nF : Nat) :
    etaProjs T (shiftFrom p b) nF
      = List.map (shiftFrom p) (etaProjs T b nF) := by
  unfold etaProjs
  rw [List.map_map]
  rfl

private theorem etaFabArgsE_shift (p : Nat) (T : Name)
    (targs : List Expr) (major : Expr) (nF : Nat) :
    etaFabArgsE T (List.map (shiftFrom p) targs) (shiftFrom p major)
      nF = List.map (shiftFrom p) (etaFabArgsE T targs major nF) := by
  unfold etaFabArgsE
  rw [List.map_append, etaProjs_shift]

private theorem defEqList_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {as bs : List Expr}, (∀ x ∈ as, WScoped d x) →
      (∀ x ∈ bs, WScoped d x) →
      defEqList (pureFns mode env fuel) env (d + 1) (as.map (shiftFrom p))
          (bs.map (shiftFrom p)) =
        defEqList (pureFns mode env fuel) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs _ _
    cases bs <;> rfl
  | cons a as ihas =>
    intro bs hwas hwbs
    cases bs with
    | nil => rfl
    | cons b bs =>
      have hwa : WScoped d a := hwas a (List.mem_cons_self ..)
      have hwb : WScoped d b := hwbs b (List.mem_cons_self ..)
      show ((do
          if ← (pureFns mode env fuel).defeq (d + 1) (shiftFrom p a)
              (shiftFrom p b) then
            defEqList (pureFns mode env fuel) env (d + 1)
              (as.map (shiftFrom p)) (bs.map (shiftFrom p))
          else pure false : CheckM Bool)) = _
      refine bind_congr_eq (ih.defeq hpd hwa hwb) ?_
      intro bb _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      exact ihas (fun x hx => hwas x (List.mem_cons_of_mem _ hx))
        (fun x hx => hwbs x (List.mem_cons_of_mem _ hx))

/-- The lazy delta same-head spine congruence is invariant under the
shift: the head constants and levels are shift-fixed, the spine
lengths are preserved, and the argument comparisons commute
(`defEqList_shift`). -/
private theorem defeqSpine_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    defeqSpine (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
      (shiftFrom p b) = defeqSpine (pureFns mode env fuel) env d a b := by
  unfold defeqSpine
  rw [getAppFn_shiftFrom]
  cases hfa : a.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case const n us =>
  dsimp only
  rw [getAppFn_shiftFrom]
  cases hfb : b.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const n' us' =>
  dsimp only
  rw [getAppArgs_shiftFrom, getAppArgs_shiftFrom]
  simp only [List.length_map]
  refine ite_congr' (fun _ => ?_) (fun _ => rfl)
  cases Level.isEquivList us us' with
  | none => rfl
  | some r =>
    cases r with
    | true =>
      rw [← List.map_reverse, ← List.map_reverse]
      exact defEqList_shift _henv ih hpd
        (fun x hx => hwa.getAppArgs x (List.mem_reverse.mp hx))
        (fun x hx => hwb.getAppArgs x (List.mem_reverse.mp hx))
    | false => rfl

private theorem proofIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    proofIrrel (pureFns mode env fuel) (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      proofIrrel (pureFns mode env fuel) d a b := by
  simp only [proofIrrel]
  refine bind_congr _ (ih.inferIO hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeIO_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.inferIO hpd hwta) ?_
  intro tta htta
  have hwtta : WScoped d tta := inferTypeIO_WScoped henv fuel htta hwta
  refine bind_congr _ (ih.whnf hpd hwtta) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case sort u =>
  refine bind_congr_eq rfl ?_
  intro okA _
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.inferIO hpd hwtb) ?_
  intro ttb httb
  have hwttb : WScoped d ttb := inferTypeIO_WScoped henv fuel httb hwtb
  refine bind_congr _ (ih.whnf hpd hwttb) ?_
  intro w' _
  cases w' <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem structEtaCertWith_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b wtb : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) (hwwtb : WScoped d wtb) :
    structEtaCertWith (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) (shiftFrom p wtb) =
      structEtaCertWith (pureFns mode env fuel) env d a b wtb := by
  simp only [structEtaCertWith]
  rw [getAppFn_shiftFrom]
  cases hfa : a.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case const c us =>
  simp only [shiftFrom]
  cases hfc : env.find? c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case ctorInfo cvc cnP cnF =>
    simp only [getAppArgs_shiftFrom, List.length_map]
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    rw [getAppFn_shiftFrom]
    cases hfw : wtb.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]
    case const T us' =>
    simp only [shiftFrom]
    cases hfT : env.find? T with
    | none => rfl
    | some ciT =>
      cases ciT <;> try rfl
      case indInfo cvT caps =>
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      refine bind_congr_eq rfl ?_
      intro okl _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have h2 := defEqList_shift henv ih hpd (as := a.getAppArgs.take caps.etaParams)
        (bs := wtb.getAppArgs)
        (fun x hx => hwa.getAppArgs x (List.mem_of_mem_take hx))
        (fun x hx => hwwtb.getAppArgs x hx)
      rw [List.map_take] at h2
      refine bind_congr_eq h2 ?_
      intro b₃ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have hlist := etaProjs_shift p T b caps.etaFields
      have hwprojs : ∀ x ∈ etaProjs T b caps.etaFields,
          WScoped d x := by
        intro x hx
        unfold etaProjs at hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        simpa [WScoped] using hwb
      have h3 := defEqList_shift henv ih hpd (as := a.getAppArgs.drop caps.etaParams)
        (bs := etaProjs T b caps.etaFields)
        (fun x hx => hwa.getAppArgs x (List.mem_of_mem_drop hx))
        hwprojs
      rw [List.map_drop, ← hlist] at h3
      exact h3

/-- `etaCtorShape` reads the head constant and the spine length, both
shift-invariant. -/
private theorem etaCtorShape_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    etaCtorShape env (shiftFrom p e) = etaCtorShape env e := by
  unfold etaCtorShape
  rw [getAppFn_shiftFrom, getAppArgs_shiftFrom, List.length_map]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem structEtaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    structEtaCert (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      structEtaCert (pureFns mode env fuel) env d a b := by
  simp only [structEtaCert]
  rw [etaCtorShape_shiftFrom]
  refine ite_congr' (fun _ => ?_) (fun _ => rfl)
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.whnf hpd hwtb) ?_
  intro wtb hwtb'
  exact structEtaCertWith_shift henv ih hpd hwa hwb
    (whnf_WScoped henv fuel hwtb' hwtb)

private theorem structUnitCert_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    structUnitCert (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      structUnitCert (pureFns mode env fuel) env d a b := by
  simp only [structUnitCert]
  refine bind_congr _ (ih.inferIO hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeIO_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.whnf hpd hwta) ?_
  intro wta hwta'
  have hwwta : WScoped d wta := whnf_WScoped henv fuel hwta' hwta
  rw [getAppFn_shiftFrom]
  cases hfn : wta.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case const T us' =>
  simp only [shiftFrom]
  cases hf : env.find? T with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case indInfo cvT caps =>
    rw [getAppArgs_shiftFrom, List.length_map]
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    refine bind_congr _ (ih.inferIO hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.whnf hpd hwtb) ?_
    intro wtb hwtb'
    rw [isForallE_shiftFrom]
    exact ite_congr' (fun _ => rfl)
      (fun _ => ih.defeq hpd hwwta (whnf_WScoped henv fuel hwtb' hwtb))

private theorem etaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d)
    {ty₁ body₁ : Expr} {b : Expr}
    (hwty₁ : WScoped d ty₁) (hwbody₁ : WScoped d body₁)
    (hwb : WScoped d b) :
    etaCert mode (pureFns mode env fuel) env (d + 1) (shiftFrom p ty₁)
        (shiftFrom p body₁) (shiftFrom p b) =
      etaCert mode (pureFns mode env fuel) env d ty₁ body₁ b := by
  simp only [etaCert]
  rw [ioNeutral_shiftFrom]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.whnf hpd hwtb) ?_
  intro wtb hwtb'
  cases wtb <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case forallE ty₂ body₂ =>
    have hwPi : WScoped d (Expr.forallE ty₂ body₂) :=
      whnf_WScoped henv fuel hwtb' hwtb
    simp only [WScoped] at hwPi
    simp only [shiftFrom]
    refine bind_congr_eq (ih.defeq hpd hwPi.1 hwty₁) ?_
    intro bb _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hwb₁ : WScoped (d + 1) (body₁.instantiate1 (.fvar d ty₁)) :=
      WScoped.instantiate1 hwty₁ 0 hwbody₁
    have h := ih.defeq (p := p) (d := d + 1) (by omega) hwb₁
      (show WScoped (d + 1) (Expr.app b (.fvar d ty₁)) by
        simp only [WScoped]
        exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwty₁⟩)
    rw [shiftFrom_instantiate1 hpd, show
        shiftFrom p (Expr.app b (.fvar d ty₁)) =
          Expr.app (shiftFrom p b) (.fvar (d + 1) (shiftFrom p ty₁))
      from by rw [shiftFrom_app, shiftFrom_fvar_ge hpd]] at h
    refine bind_congr_eq h ?_
    intro bb₂ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hi := ih.infer (p := p) (d := d + 1) (by omega) hwb₁
    rw [shiftFrom_instantiate1 hpd] at hi
    refine bind_congr _ hi ?_
    intro t₁ ht₁
    have hwt₁ : WScoped (d + 1) t₁ := inferTypeCore_WScoped henv fuel ht₁ hwb₁
    have hcod : WScoped (d + 1) (body₂.instantiate1 (.fvar d ty₁)) :=
      WScoped.instantiate1 hwty₁ 0 hwPi.2
    have hde := ih.defeq (p := p) (d := d + 1) (by omega) hwt₁ hcod
    rw [shiftFrom_instantiate1 hpd] at hde
    refine bind_congr_eq hde ?_
    intro _ _
    rfl

private theorem stuckIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    stuckIrrel (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      stuckIrrel (pureFns mode env fuel) env d a b := by
  simp only [stuckIrrel]
  refine bind_congr_eq (structEtaCert_shift henv ih hpd hwa hwb) ?_
  intro b₃ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr_eq (structEtaCert_shift henv ih hpd hwb hwa) ?_
  intro b₄ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr_eq (structUnitCert_shift henv ih hpd hwa hwb) ?_
  intro b₅ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  exact proofIrrel_shift henv ih hpd hwa hwb

/-- The hoisted `Prop`-branch test (task #168): the fast arm reads
head symbols only, which the shift preserves (`notProofFast_shiftFrom`);
the slow branch is `proofIrrel_shift`'s `Prop` branch. -/
private theorem propIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    propIrrel (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      propIrrel (pureFns mode env fuel) env d a b := by
  simp only [propIrrel, notProofFast_shiftFrom, isProofFast_shiftFrom]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr _ (ih.inferIO hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeIO_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.inferIO hpd hwta) ?_
  intro tta htta
  have hwtta : WScoped d tta := inferTypeIO_WScoped henv fuel htta hwta
  refine bind_congr _ (ih.whnf hpd hwtta) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case sort u =>
  refine bind_congr_eq rfl ?_
  intro okA _
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.inferIO hpd hwtb) ?_
  intro ttb httb
  have hwttb : WScoped d ttb := inferTypeIO_WScoped henv fuel httb hwtb
  refine bind_congr _ (ih.whnf hpd hwttb) ?_
  intro w' _
  cases w' <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- The projection fire's arity check reads the spine's length only. -/
private theorem projCertAt_shift {p : Nat} (v : Bool) (c : Name) (args : List Expr) :
    projCertAt env v c (args.map (shiftFrom p)) = projCertAt env v c args := by
  simp only [projCertAt, projCert, teleArityOk, List.length_map]

private theorem majorToCtor_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) (recName : Name)
    (rules : List RecRule) {major : Expr} (hwmaj : WScoped d major) :
    majorToCtor mode (pureFns mode env fuel) env (d + 1) recName rules
        (shiftFrom p major) =
      (majorToCtor mode (pureFns mode env fuel) env d recName rules major).map
        (shiftFrom p) := by
  simp only [majorToCtor]
  rw [isCtorApp_shiftFrom]
  refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
  cases rules with
  | nil => rfl
  | cons rl rest =>
    cases rest with
    | cons rl' rest' => rfl
    | nil =>
      dsimp only
      cases hfr : env.find? rl.ctor with
      | none => rfl
      | some ci =>
        cases ci <;> try rfl
        case ctorInfo cvj cnP cnF =>
        dsimp only
        cases hpi : (cvj.type.piResult).getAppFn <;> try rfl
        case const T us₀ =>
        dsimp only
        cases hfT : env.find? T with
        | none => rfl
        | some ciT =>
          cases ciT <;> try rfl
          case indInfo cvT caps =>
          dsimp only
          refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
          · -- K rescue
            refine bind_rel _ _ (ih.inferIO hpd hwmaj) ?_
            intro tmaj₀ htmaj₀
            have hwtmaj₀ : WScoped d tmaj₀ :=
              inferTypeIO_WScoped henv fuel htmaj₀ hwmaj
            refine bind_rel _ _ (ih.whnf hpd hwtmaj₀) ?_
            intro tmaj htmaj
            have hwtmaj : WScoped d tmaj :=
              whnf_WScoped henv fuel htmaj hwtmaj₀
            rw [getAppFn_shiftFrom]
            cases hfn : tmaj.getAppFn <;> try rfl
            case fvar => rw [shiftFrom_fvar]; rfl
            case const T' ust =>
            simp only [shiftFrom]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            rw [getAppArgs_shiftFrom, List.length_map]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            have hfab : Expr.mkAppN (Expr.const rl.ctor ust)
                ((List.map (shiftFrom p) tmaj.getAppArgs).take cnP) =
                shiftFrom p (Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs.take cnP)) := by
              rw [shiftFrom_mkAppN, List.map_take]
              rfl
            rw [hfab]
            have hwfab : WScoped d (Expr.mkAppN (.const rl.ctor ust)
                (tmaj.getAppArgs.take cnP)) := by
              refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
              intro x hx
              exact hwtmaj.getAppArgs x (List.mem_of_mem_take hx)
            rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
              fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel _ _ (ih.inferIO hpd hwfab) ?_
            intro tfab htfab
            have hwtfab : WScoped d tfab :=
              inferTypeIO_WScoped henv fuel htfab hwfab
            refine bind_rel_eq _ (ih.defeq hpd hwtmaj hwtfab) ?_
            intro bde _
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            -- Task #342 (r1): proof irrelevance is now gated on
            -- `mode.verifiedChecks`; the gate itself shifts trivially
            -- (`ite_congr'`, both arms unconditionally `rfl`/`proofIrrel_shift`).
            refine bind_rel_eq _
                (ite_congr' (fun _ => proofIrrel_shift henv ih hpd hwfab hwmaj)
                  (fun _ => rfl)) ?_
            intro bb _
            exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
          · -- the structure-eta rescue, then the `And`-only rescue
            refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
            · -- structure-eta rescue
              refine bind_rel _ _ (ih.inferIO hpd hwmaj) ?_
              intro tmaj₀ htmaj₀
              have hwtmaj₀ : WScoped d tmaj₀ :=
                inferTypeIO_WScoped henv fuel htmaj₀ hwmaj
              refine bind_rel _ _ (ih.whnf hpd hwtmaj₀) ?_
              intro tmaj htmaj
              have hwtmaj : WScoped d tmaj :=
                whnf_WScoped henv fuel htmaj hwtmaj₀
              rw [getAppFn_shiftFrom]
              cases hfn : tmaj.getAppFn <;> try rfl
              case fvar => rw [shiftFrom_fvar]; rfl
              case const T' ust =>
              simp only [shiftFrom]
              rw [getAppArgs_shiftFrom, List.length_map]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              rw [etaFabArgsE_shift]
              have hfab : Expr.mkAppN (Expr.const caps.etaCtor ust)
                  (List.map (shiftFrom p)
                    (etaFabArgsE T tmaj.getAppArgs major
                      caps.etaFields)) =
                  shiftFrom p (Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgsE T tmaj.getAppArgs major
                      caps.etaFields)) := by
                rw [shiftFrom_mkAppN]
                rfl
              rw [hfab]
              have hwfabArgs : ∀ x ∈ etaFabArgsE T tmaj.getAppArgs
                  major caps.etaFields, WScoped d x := by
                intro x hx
                unfold etaFabArgsE at hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hwtmaj.getAppArgs x hx
                · unfold etaProjs at hx
                  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                  simpa [WScoped] using hwmaj
              have hwfab : WScoped d (Expr.mkAppN (.const caps.etaCtor ust)
                  (etaFabArgsE T tmaj.getAppArgs major
                    caps.etaFields)) :=
                Expr.WScoped.mkAppN (by simp [WScoped]) hwfabArgs
              rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
                fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
              exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
            · -- the `And`-only rescue (or no rescue)
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel _ _ (ih.inferIO hpd hwmaj) ?_
              intro tmaj₀ htmaj₀
              have hwtmaj₀ : WScoped d tmaj₀ :=
                inferTypeIO_WScoped henv fuel htmaj₀ hwmaj
              refine bind_rel _ _ (ih.whnf hpd hwtmaj₀) ?_
              intro tmaj htmaj
              have hwtmaj : WScoped d tmaj :=
                whnf_WScoped henv fuel htmaj hwtmaj₀
              rw [getAppFn_shiftFrom]
              cases hfn : tmaj.getAppFn <;> try rfl
              case fvar => rw [shiftFrom_fvar]; rfl
              case const T' ust =>
              simp only [shiftFrom]
              rw [getAppArgs_shiftFrom, List.length_map]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              have hlist : List.map (shiftFrom p) tmaj.getAppArgs ++
                  [Expr.proj T 0 (shiftFrom p major),
                    Expr.proj T 1 (shiftFrom p major)] =
                  List.map (shiftFrom p)
                    (tmaj.getAppArgs ++
                      [Expr.proj T 0 major, Expr.proj T 1 major]) := by
                rw [List.map_append]; rfl
              rw [hlist]
              have hfab : Expr.mkAppN (Expr.const rl.ctor ust)
                  (List.map (shiftFrom p)
                    (tmaj.getAppArgs ++
                      [Expr.proj T 0 major, Expr.proj T 1 major])) =
                  shiftFrom p (Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs ++
                      [Expr.proj T 0 major, Expr.proj T 1 major])) := by
                rw [shiftFrom_mkAppN]
                rfl
              rw [hfab]
              have hwfabArgs : ∀ x ∈ tmaj.getAppArgs ++
                  [Expr.proj T 0 major, Expr.proj T 1 major], WScoped d x := by
                intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hwtmaj.getAppArgs x hx
                · have hx' : x = Expr.proj T 0 major ∨
                      x = Expr.proj T 1 major := by simpa using hx
                  rcases hx' with rfl | rfl <;> simpa [WScoped] using hwmaj
              have hwfab : WScoped d (Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs ++
                    [Expr.proj T 0 major, Expr.proj T 1 major])) :=
                Expr.WScoped.mkAppN (by simp [WScoped]) hwfabArgs
              rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
                fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel _ _ (ih.inferIO hpd hwfab) ?_
              intro tfab htfab
              have hwtfab : WScoped d tfab :=
                inferTypeIO_WScoped henv fuel htfab hwfab
              refine bind_rel_eq _ (ih.defeq hpd hwtmaj hwtfab) ?_
              intro bde _
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              -- Task #342 (r1): the `And` branch's proof irrelevance,
              -- gated the same way as the K branch's.
              refine bind_rel_eq _
                  (ite_congr' (fun _ => proofIrrel_shift henv ih hpd hwfab hwmaj)
                    (fun _ => rfl)) ?_
              intro bb _
              exact ite_rel _ (fun _ => rfl) (fun _ => rfl)

/-- The scoping of an iota reduct (the `iotaRec` slice of the
`whnfPres_WScoped` proof, factored for the bisimulation). -/
theorem iotaRec_WScoped (henv : EnvWF env)
    {d : Nat} {e e'' : Expr}
    (h : iotaRec mode (pureFns mode env fuel) env d e = .ok (some e''))
    (hw : WScoped d e) : WScoped d e'' := by
  obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj,
    cvj, cnP, cnF, r, hfn, hfc, hlen, -, hprep,
    hmfn, hfj,
    hrule,
    hml, hlev, hpeq, hmcerts, -, rfl⟩ :=
    iotaRec_inv h
  have hargs : ∀ x, x ∈ e.getAppArgs → WScoped d x :=
    fun x hx => hw.getAppArgs x hx
  have hrhs : WScoped d
      (r.rhs.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨-, -, -, -, -, hrules, -⟩ := henv.consts _ (Env.find?_mem hfc)
    obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl r
      (List.mem_of_find?_eq_some hrule)
    exact WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hrf)
  have hmajw : WScoped d major := prepareMajorFueled_WScoped henv hprep
    (hargs _ (getD_mem (by omega)))
  refine Expr.WScoped.mkAppN hrhs ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hargs _ (List.mem_of_mem_take hx)
  · exact hmajw.getAppArgs _ (List.mem_of_mem_drop hx)

/-- Shifting commutes with the literal-major conversion (the string
branch reduces a closed term, invariant under shifting). -/
private theorem litMajorToCtor_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {e : Expr}, WScoped d e →
    litMajorToCtor (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (litMajorToCtor (pureFns mode env fuel) env d e).map (shiftFrom p)
  | .lit (.strVal s), _ => by
    show litMajorToCtor (pureFns mode env fuel) env (d + 1) (.lit (.strVal s)) = _
    simp only [litMajorToCtor]
    split
    · have hres := ih.whnf (p := p) hpd (strLitToConstructor_WScoped s d)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    · rfl
  | .lit (.natVal n), _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.lit (.natVal n)))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .bvar i, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.bvar i))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .sort u, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.sort u))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .const n us, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.const n us))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .fvar idx ty, _ => by
    rw [shiftFrom_fvar]
    show pure (litToCtorIfNat env (.fvar (shiftIdx p idx) (shiftTy p idx ty))) = _
    rw [show (litToCtorIfNat env (.fvar (shiftIdx p idx) (shiftTy p idx ty))) =
      .fvar (shiftIdx p idx) (shiftTy p idx ty) from rfl]
    rw [show (litMajorToCtor (pureFns mode env fuel) env d (.fvar idx ty)) =
      pure (.fvar idx ty) from rfl]
    rw [show (Except.map (shiftFrom p) (pure (Expr.fvar idx ty)) :
        CheckM Expr) = pure (shiftFrom p (.fvar idx ty)) from rfl]
    rw [shiftFrom_fvar]
  | .app f a, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.app f a))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .lam ty body, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.lam ty body))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .forallE ty body, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.forallE ty body))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .letE ty v body, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.letE ty v body))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .proj sn i pe, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.proj sn i pe))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl

/-- Shifting commutes with the projection-scrutinee literal conversion
(the string branch reduces a closed term, invariant under shifting). -/
private theorem projLitToCtor_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {e : Expr}, WScoped d e →
    projLitToCtor (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (projLitToCtor (pureFns mode env fuel) env d e).map (shiftFrom p)
  | .lit (.strVal s), _ => by
    show projLitToCtor (pureFns mode env fuel) env (d + 1) (.lit (.strVal s)) = _
    simp only [projLitToCtor]
    split
    · have hres := ih.whnf (p := p) hpd (strLitToConstructor_WScoped s d)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    · rfl
  | .lit (.natVal n), _ => rfl
  | .bvar i, _ => rfl
  | .sort u, _ => rfl
  | .const n us, _ => rfl
  | .fvar idx ty, _ => by
    rw [shiftFrom_fvar]
    show pure (Expr.fvar (shiftIdx p idx) (shiftTy p idx ty)) = _
    rw [show (projLitToCtor (pureFns mode env fuel) env d (.fvar idx ty)) =
      pure (.fvar idx ty) from rfl]
    rw [show (Except.map (shiftFrom p) (pure (Expr.fvar idx ty)) :
        CheckM Expr) = pure (shiftFrom p (.fvar idx ty)) from rfl]
    rw [shiftFrom_fvar]
  | .app f a, _ => rfl
  | .lam ty body, _ => rfl
  | .forallE ty body, _ => rfl
  | .letE ty v body, _ => rfl
  | .proj sn i pe, _ => rfl

/-- The projection rule commutes with the shift. -/
private theorem reduceProjCore_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {sn : Name} {i : Nat}
    {c : Expr} (hw : WScoped d c) :
    reduceProjCore mode (pureFns mode env fuel) env (d + 1) sn i (shiftFrom p c) =
      (reduceProjCore mode (pureFns mode env fuel) env d sn i c).map
        (Option.map (shiftFrom p)) := by
  unfold reduceProjCore
  refine bind_rel _ _ (projLitToCtor_shift henv ih hpd hw) ?_
  intro e₃ he₃
  have hwe₃ : WScoped d e₃ := by
    rcases projLitToCtorFueled_inv he₃ with rfl | ⟨s, -, -, hred⟩
    · exact hw
    · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d)
  cases hfp : env.findProj? sn i with
  | none => rfl
  | some entry =>
    dsimp only
    rw [getAppFn_shiftFrom]
    cases hfn : e₃.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const k us₂ =>
    simp only [shiftFrom]
    simp only [getAppArgs_shiftFrom, List.length_map]
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    rw [projCertAt_shift]
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    simp only [pure, Except.pure, map_ok, Option.map_some]
    rw [getD_map_shiftFrom]
private theorem iotaIndexOk_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d)
    {mI rP cnP : Nat} {tyCtor : Expr} (htel : tyCtor.hasFvar = false)
    {margs idx : List Expr} (hwm : ∀ x ∈ margs, WScoped d x)
    (hwi : ∀ x ∈ idx, WScoped d x) :
    iotaIndexOk (pureFns mode env fuel) env (d + 1) mI rP cnP tyCtor
        (margs.map (shiftFrom p)) (idx.map (shiftFrom p)) =
      iotaIndexOk (pureFns mode env fuel) env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, ite_eq_left hmr]
  · simp only [iotaIndexOk, ite_eq_right hmr]
    have hres := piResidual_shiftFrom (p := p) margs tyCtor
    rw [shiftFrom_eq_self_of_not_hasFvar htel] at hres
    rw [hres]
    cases hresid : piResidual tyCtor margs with
    | none => rfl
    | some residual =>
      simp only [Option.map_some]
      have hwres : WScoped d residual :=
        piResidual_WScoped hresid (WScoped.of_not_hasFvar htel) hwm
      have h4 := defEqList_shift henv ih hpd
        (as := residual.getAppArgs.drop cnP) (bs := idx)
        (fun x hx => hwres.getAppArgs x (List.mem_of_mem_drop hx)) hwi
      simp only [List.map_drop] at h4
      rw [← getAppArgs_shiftFrom] at h4
      exact h4

private theorem isStrLit_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).isStrLit = e.isStrLit := by
  cases e <;> first | rfl | (rw [shiftFrom_fvar]; done) | (rw [shiftFrom_fvar]; rfl)

/-- The major chain commutes with the shift, in either order. -/
private theorem prepareMajor_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) (recName : Name)
    (rules : List RecRule) {major : Expr} (hwmaj : WScoped d major) :
    prepareMajor mode (pureFns mode env fuel) env (d + 1) recName rules
        (shiftFrom p major) =
      (prepareMajor mode (pureFns mode env fuel) env d recName rules major).map
        (shiftFrom p) := by
  simp only [prepareMajor]
  by_cases hk : recRuleK rules = true
  · rw [ite_eq_left hk, ite_eq_left hk]
    refine bind_rel _ _ (majorToCtor_shift henv ih hpd recName rules hwmaj) ?_
    intro m₁ hm₁
    have hw₁ : WScoped d m₁ := by
      rcases majorToCtor_inv hm₁ with rfl | ⟨hwsc, -, -, -⟩
      · exact hwmaj
      · exact WScoped.of_wscopedB hwsc
    rw [isCtorApp_shiftFrom]
    exact ite_rel _ (fun _ => litMajorToCtor_shift henv ih hpd hw₁) (fun _ => rfl)
  · rw [ite_eq_right hk, ite_eq_right hk, isStrLit_shiftFrom]
    -- the chain after the first rescue attempt (task #342 R2), at any
    -- scoped intermediate major
    have tail : ∀ {mE : Expr}, WScoped d mE →
        (if isCtorApp env (shiftFrom p mE) = true then pure (shiftFrom p mE)
          else do
            let major₀ ← (pureFns mode env fuel).whnf (d + 1) (shiftFrom p mE)
            let major₁ ← litMajorToCtor (pureFns mode env fuel) env (d + 1) major₀
            majorToCtor mode (pureFns mode env fuel) env (d + 1) recName rules major₁) =
          (if isCtorApp env mE = true then pure mE
            else do
              let major₀ ← (pureFns mode env fuel).whnf d mE
              let major₁ ← litMajorToCtor (pureFns mode env fuel) env d major₀
              majorToCtor mode (pureFns mode env fuel) env d recName rules major₁).map
            (shiftFrom p) := by
      intro mE hwE
      rw [isCtorApp_shiftFrom]
      refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
      refine bind_rel _ _ (ih.whnf hpd hwE) ?_
      intro m₀ hm₀
      have hw₀ : WScoped d m₀ := whnf_WScoped henv fuel hm₀ hwE
      refine bind_rel _ _ (litMajorToCtor_shift henv ih hpd hw₀) ?_
      intro m₁ hm₁
      have hw₁ : WScoped d m₁ := by
        rcases litMajorToCtorFueled_inv hm₁ with rfl | ⟨s, -, -, hred⟩
        · exact litToCtorIfNat_WScoped hw₀
        · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d)
      exact majorToCtor_shift henv ih hpd recName rules hw₁
    by_cases hs : major.isStrLit = true
    · rw [ite_eq_left hs, ite_eq_left hs]
      exact tail hwmaj
    · rw [ite_eq_right hs, ite_eq_right hs]
      refine bind_rel _ _ (majorToCtor_shift henv ih hpd recName rules hwmaj) ?_
      intro m₁ hm₁
      have hw₁ : WScoped d m₁ := by
        rcases majorToCtor_inv hm₁ with rfl | ⟨hwsc, -, -, -⟩
        · exact hwmaj
        · exact WScoped.of_wscopedB hwsc
      exact tail hw₁

private theorem iotaRec_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hwe : WScoped d e) :
    iotaRec mode (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (iotaRec mode (pureFns mode env fuel) env d e).map
        (Option.map (shiftFrom p)) := by
  simp only [iotaRec]
  rw [getAppFn_shiftFrom]
  cases hfn : e.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const c us =>
  simp only [shiftFrom]
  cases hfc : env.find? c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case recInfo cv mI rP rules =>
    dsimp only
    simp only [getAppArgs_shiftFrom, List.length_map]
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    rw [getD_map_shiftFrom]
    have hwgd : WScoped d (e.getAppArgs.getD mI (.bvar 0)) :=
      wscoped_getD (fun x hx => hwe.getAppArgs x hx) _
    refine bind_rel _ _ (prepareMajor_shift henv ih hpd c rules hwgd) ?_
    intro major hmaj
    have hwmaj : WScoped d major := prepareMajorFueled_WScoped henv hmaj hwgd
    rw [getAppFn_shiftFrom]
    cases hmfn : major.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const cj usj =>
    simp only [shiftFrom]
    cases hfj : env.find? cj with
    | none => rfl
    | some cij =>
      cases cij <;> try rfl
      case ctorInfo cvj cnP cnF =>
      dsimp only
      cases hrule : rules.find? (fun r' => r'.ctor == cj) with
      | none => rfl
      | some rl =>
        dsimp only
        simp only [getAppArgs_shiftFrom, List.length_map]
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        -- the level comparand does not read the argument spine
        rw [recFireComparands_fst_congr rl cv.levelParams us
            cvj.levelParams (e.getAppArgs.map (shiftFrom p))
            e.getAppArgs rP]
        -- the stored nested instantiations are fvar-free (`EnvWF`)
        have hpins : ∀ lvls pins, rl.fire = .nested lvls pins →
            ∀ pin ∈ pins, pin.hasFvar = false := by
          intro lvls pins hf' pin hpin
          obtain ⟨-, -, -, -, g5⟩ :=
            (henv.consts _ (Env.find?_mem hfc)).2.2.2.2.2.1 cv mI rP rules rfl rl
              (List.mem_of_find?_eq_some hrule)
          exact ((g5 lvls pins hf').2.2.1 pin hpin).1
        have h1 := defEqList_shift henv ih hpd
          (as := major.getAppArgs.take rl.ctorParams)
          (bs := (recFireComparands rl cv.levelParams us
            cvj.levelParams e.getAppArgs rP).2)
          (fun x hx => hwmaj.getAppArgs x (List.mem_of_mem_take hx))
          (recFireComparands_snd_WScoped rl cv.levelParams us
            cvj.levelParams e.getAppArgs rP
            (fun x hx => hwe.getAppArgs x hx) hpins)
        rw [← recFireComparands_snd_shift rl cv.levelParams us
          cvj.levelParams e.getAppArgs rP hpins,
          List.map_take] at h1
        have htel₂ : (cvj.type.instantiateLevelParams cvj.levelParams
            usj).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]
          exact (henv.consts _ (Env.find?_mem hfj)).1
        refine bind_rel_eq _ ?_ ?_
        · -- Task #342 (r1): the whole case-3 decision is now gated on
          -- `mode.verifiedChecks`, one `by_cases` outside the existing
          -- `iotaCase3` one; at the trusted mode both sides are
          -- `pure true`, closed by the `rw` alone.
          by_cases hμ : mode.verifiedChecks = true
          · rw [ite_eq_left hμ, ite_eq_left hμ]
            by_cases h3 : iotaCase3 env.find? rl cvj (recFireComparands rl cv.levelParams us
                cvj.levelParams e.getAppArgs rP).1 = true
            · rw [ite_eq_left h3, ite_eq_left h3]
              refine bind_congr_eq rfl ?_
              intro b₀ _
              refine ite_congr' (fun _ => ?_) (fun _ => rfl)
              refine bind_congr_eq h1 ?_
              intro b₁ _
              refine ite_congr' (fun _ => ?_) (fun _ => rfl)
              have h3c := iotaCertsFull_shift henv ih hpd
                (ty := cvj.type.instantiateLevelParams cvj.levelParams usj)
                (WScoped.of_not_hasFvar htel₂)
                (args := major.getAppArgs)
                (fun x hx => hwmaj.getAppArgs x hx)
              rw [shiftFrom_eq_self_of_not_hasFvar htel₂] at h3c
              refine bind_congr_eq h3c ?_
              intro b₃ _
              refine ite_congr' (fun _ => ?_) (fun _ => rfl)
              -- the index comparison (only where indices exist): the closed
              -- telescope peeled along the shifted spines
              have hidx := iotaIndexOk_shift henv ih hpd htel₂
                (mI := mI) (rP := rP) (cnP := rl.ctorParams)
                (margs := major.getAppArgs) (idx := (e.getAppArgs.take mI).drop rP)
                (fun x hx => hwmaj.getAppArgs x hx)
                (fun x hx => hwe.getAppArgs x
                  (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
              simp only [List.map_drop, List.map_take] at hidx
              exact hidx
            · rw [ite_eq_right h3, ite_eq_right h3]
          · rw [ite_eq_right hμ, ite_eq_right hμ]
        intro b₄ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have hrhs : (rl.rhs.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          obtain ⟨-, -, -, -, -, hrules, -⟩ := henv.consts _ (Env.find?_mem hfc)
          obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl rl
            (List.mem_of_find?_eq_some hrule)
          rw [hasFvar_instantiateLevelParams]
          exact hrf
        have hout : Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((List.map (shiftFrom p) e.getAppArgs).take rP ++
              (List.map (shiftFrom p) major.getAppArgs).drop rl.ctorParams) =
            shiftFrom p (Expr.mkAppN
              (rl.rhs.instantiateLevelParams cv.levelParams us)
              (e.getAppArgs.take rP ++
                major.getAppArgs.drop rl.ctorParams)) := by
          rw [shiftFrom_mkAppN,
            shiftFrom_eq_self_of_not_hasFvar hrhs, List.map_append,
            List.map_take, List.map_drop]
        rw [hout]
        rfl

/-! ## The body step lemmas -/

private theorem whnfCore_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : WhnfCoreShift mode env (fuel + 1) := by
  intro c p d hpd e hw
  rw [whnfCore_succ, whnfCore_succ]
  match e with
  | .bvar i => rfl
  | .sort u => rfl
  | .fvar idx ty =>
    rw [shiftFrom_fvar]
    simp only [whnfCoreBody, pure, Except.pure, map_ok, shiftFrom_fvar]
  | .forallE ty body => rfl
  | .lam ty body => rfl
  | .const n us => rfl
  | .lit l => rfl
  | .letE ty v body =>
    -- ζ: the body at the value
    simp only [WScoped] at hw
    show whnfCoreBody mode (pureFns mode env fuel) env c (d + 1)
        (.letE (shiftFrom p ty) (shiftFrom p v) (shiftFrom p body)) =
      (whnfCoreBody mode (pureFns mode env fuel) env c d (.letE ty v body)).map
        (shiftFrom p)
    simp only [whnfCoreBody]
    have h := ih.whnfCore (c := c) hpd (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
    rw [shiftFrom_instantiate1_gen] at h
    simp only [whnfCore_def]
    exact h
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [whnfCoreBody]
    refine bind_rel _ _ (ih.whnfCore hpd hw.1) ?_
    intro f' hf'
    have hwf' : WScoped d f' := whnfCore_WScoped henv fuel hf' hw.1
    have hiota : ∀ (f'' : Expr), WScoped d f'' →
        (iotaRec mode (pureFns mode env fuel) env (d + 1)
            (.app (shiftFrom p f'') (shiftFrom p a)) >>= fun o =>
          match o with
          | some e'' => (pureFns mode env fuel).whnfCore c (d + 1) e''
          | none => pure (.app (shiftFrom p f'') (shiftFrom p a))) =
        ((iotaRec mode (pureFns mode env fuel) env d (.app f'' a) >>= fun o =>
          match o with
          | some e'' => (pureFns mode env fuel).whnfCore c d e''
          | none => pure (.app f'' a)).map (shiftFrom p)) := by
      intro f'' hwf''
      have hwapp : WScoped d (Expr.app f'' a) := by
        simp only [WScoped]; exact ⟨hwf'', hw.2⟩
      refine bind_rel _ _ (iotaRec_shift henv ih hpd hwapp) ?_
      intro o ho
      cases o with
      | none => rfl
      | some e'' =>
        exact ih.whnfCore hpd (iotaRec_WScoped henv ho hwapp)
    cases f' with
    | lam ty₁ body₁ =>
      simp only [WScoped] at hwf'
      dsimp only [shiftFrom]
      -- uniform β: the reduct step, no certificate
      have h := ih.whnfCore (c := c) hpd
        (WScoped.instantiate1_gen hw.2 0 hwf'.2)
      rw [shiftFrom_instantiate1_gen] at h
      simp only [whnfCore_def]
      exact h
    | bvar i => exact hiota _ hwf'
    | fvar idx ty =>
      have h := hiota _ hwf'
      simp only [shiftFrom_fvar] at h ⊢
      exact h
    | sort u => exact hiota _ hwf'
    | const n' us => exact hiota _ hwf'
    | forallE ty' body' => exact hiota _ hwf'
    | letE ty' v' body' => exact hiota _ hwf'
    | lit l => exact hiota _ hwf'
    | proj s' i' e' => exact hiota _ hwf'
    | app f'' a'' => exact hiota _ hwf'
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show whnfCoreBody mode (pureFns mode env fuel) env c (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (whnfCoreBody mode (pureFns mode env fuel) env c d (.proj sn i pe)).map
        (shiftFrom p)
    cases c
    · simp only [whnfCoreBody, Bool.false_eq_true, ↓reduceIte]
      refine bind_rel (shiftFrom p) _ (ih.whnf hpd hw) ?_
      intro e₂ he₂
      have hwe₂ : WScoped d e₂ := whnf_WScoped henv fuel he₂ hw
      refine bind_rel _ _ (reduceProjCore_shift henv ih hpd hwe₂) ?_
      intro o ho
      cases o with
      | none => rfl
      | some m =>
        simp only [Option.map_some]
        exact ih.whnfCore hpd (reduceProjCore_pres (WScoped d)
          (fun hx => hx.getAppArgs) (fun h hx => whnf_WScoped henv fuel h hx)
          (fun s _ => strLitToConstructor_WScoped s d) ho hwe₂)
    · simp only [whnfCoreBody, ↓reduceIte]
      refine bind_rel (shiftFrom p) _ (ih.whnfCore hpd hw) ?_
      intro e₂ he₂
      have hwe₂ : WScoped d e₂ := whnfCore_WScoped henv fuel he₂ hw
      refine bind_rel _ _ (reduceProjCore_shift henv ih hpd hwe₂) ?_
      intro o ho
      cases o with
      | none => rfl
      | some m =>
        simp only [Option.map_some]
        exact ih.whnfCore hpd (reduceProjCore_pres (WScoped d)
          (fun hx => hx.getAppArgs) (fun h hx => whnf_WScoped henv fuel h hx)
          (fun s _ => strLitToConstructor_WScoped s d) ho hwe₂)

/-- The reduction *loop* commutes with the shift, by induction on its
own step budget (task #106); the per-step head normalization comes
from the knot hypothesis `ih`. -/
theorem whnfLoop_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) :
    ∀ (n : Nat) {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
      whnfLoop (pureFns mode env fuel) env (d + 1) n (shiftFrom p e) =
        (whnfLoop (pureFns mode env fuel) env d n e).map (shiftFrom p) := by
  intro n
  induction n with
  | zero => intro p d hpd e hw; rfl
  | succ n ihN =>
  intro p d hpd e hw
  simp only [whnfLoop, whnfStep]
  refine bind_rel _ _ (ih.whnfCore hpd hw) ?_
  intro e₁ he₁
  have hwe₁ : WScoped d e₁ := whnfCore_WScoped henv fuel he₁ hw
  refine bind_rel _ _ (reduceNat_shift henv ih hpd hwe₁) ?_
  intro o ho
  cases o with
  | some e₂ =>
    simp only [Option.map_some]
    have hwe₂ : WScoped d e₂ := by
      rcases reduceNat_inv ho with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ihN hpd hwe₂
  | none =>
    rw [unfoldDefinition_shiftFrom henv]
    cases hu : unfoldDefinition env e₁ with
    | none => rfl
    | some e₂ =>
      simp only [Option.map_some]
      exact ihN hpd (unfoldDefinition_WScoped henv hu hwe₁)

private theorem whnf_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : WhnfShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [whnf_succ, whnf_succ]
  exact whnfLoop_shift henv ih whnfLoopFuel hpd hw

private theorem infer_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : InferShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [inferTypeCore_succ, inferTypeCore_succ]
  match e with
  | .bvar i => rfl
  | .letE ty v body =>
    -- official `infer_let`: the type's sort, the value against the
    -- type, the body at the value
    simp only [WScoped] at hw
    show inferBody (pureFns mode env fuel) env (d + 1)
        (.letE (shiftFrom p ty) (shiftFrom p v) (shiftFrom p body)) =
      (inferBody (pureFns mode env fuel) env d (.letE ty v body)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel (shiftFrom p) _ (ih.infer hpd hw.1) ?_
    intro tty htty
    have hwtty : WScoped d tty := inferTypeCore_WScoped henv fuel htty hw.1
    refine bind_rel_eq _ (ensureSort_shift henv ih hpd hwtty) ?_
    intro u _
    refine bind_rel (shiftFrom p) _ (ih.infer hpd hw.2.1) ?_
    intro tv htv
    have hwtv : WScoped d tv := inferTypeCore_WScoped henv fuel htv hw.2.1
    refine bind_rel_eq _ (ih.defeq hpd hwtv hw.1) ?_
    intro bb _
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    have h := ih.infer hpd (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
    rw [shiftFrom_instantiate1_gen] at h
    exact h
  | .sort u => rfl
  | .lit (.natVal n) =>
    show inferBody (pureFns mode env fuel) env (d + 1) (.lit (.natVal n)) =
      (inferBody (pureFns mode env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [inferBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .lit (.strVal str) =>
    show inferBody (pureFns mode env fuel) env (d + 1) (.lit (.strVal str)) =
      (inferBody (pureFns mode env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [inferBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx ty =>
    simp only [WScoped] at hw
    rw [shiftFrom_fvar]
    simp only [inferBody]
    rw [ite_eq_left (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        ite_eq_left hw.1]
    by_cases hp : p ≤ idx
    · simp [shiftTy, hp, pure, Except.pure]
    · simp only [shiftTy, ite_eq_right hp, pure, Except.pure, map_ok]
      rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
  | .const n us =>
    show inferBody (pureFns mode env fuel) env (d + 1) (.const n us) =
      (inferBody (pureFns mode env fuel) env d (.const n us)).map (shiftFrom p)
    simp only [inferBody]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      have hty : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv.consts _ (Env.find?_mem hf)).1
      simp only [pure, Except.pure, map_ok,
        shiftFrom_eq_self_of_not_hasFvar hty]
  | .forallE ty body =>
    simp only [WScoped] at hw
    show inferBody (pureFns mode env fuel) env (d + 1)
        (.forallE (shiftFrom p ty) (shiftFrom p body)) =
      (inferBody (pureFns mode env fuel) env d (.forallE ty body)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tty htty
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htty hw.1)) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case sort u =>
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ih.infer (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv fuel hbt hwo
    refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
      (d := d + 1) (by omega) hwbt) ?_
    intro v _
    rfl
  | .lam ty body =>
    simp only [WScoped] at hw
    show inferBody (pureFns mode env fuel) env (d + 1)
        (.lam (shiftFrom p ty) (shiftFrom p body)) =
      (inferBody (pureFns mode env fuel) env d (.lam ty body)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tty htty
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htty hw.1)) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case sort u =>
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ih.infer (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv fuel hbt hwo
    show pure _ = Except.map _ (pure _)
    rw [← shiftFrom_abstract1 hpd]; rfl
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tf htf
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htf hw.1)) ?_
    intro w hww
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE ty' body' =>
    have hwPi : WScoped d (Expr.forallE ty' body') :=
      whnf_WScoped henv fuel hww (inferTypeCore_WScoped henv fuel htf hw.1)
    simp only [WScoped] at hwPi
    -- Task #368: the skip reads fvar-free terms
    simp only [shiftFrom]
    rw [bvUnsatSkip_shiftFrom]
    by_cases hsk : bvUnsatSkip env.find? env.findProj? f a body' = true
    · simp only [hsk, ite_true]
      show pure _ = Except.map _ (pure _)
      rw [← shiftFrom_instantiate1_gen]; rfl
    simp only [hsk]
    refine bind_rel _ _ (ih.infer hpd hw.2) ?_
    intro ta hta
    -- the argument check at the argument's mode (task #353): the
    -- shift keeps an `eagerReduce _ _` argument one
    have hdeq : defeqArg (pureFns mode env fuel) (d + 1) (shiftFrom p a)
        (shiftFrom p ta) (shiftFrom p ty') =
        defeqArg (pureFns mode env fuel) d a ta ty' := by
      rw [defeqArg_def, defeqArg_def]
      unfold CheckMode.argMode
      rw [isEagerReduce_shiftFrom]
      split
      · exact ih.defeqE hpd (inferTypeCore_WScoped henv fuel hta hw.2) hwPi.1
      · exact ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hw.2) hwPi.1
    refine bind_rel_eq _ hdeq ?_
    intro bb _
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    rw [← shiftFrom_instantiate1_gen]
    rfl
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show inferBody (pureFns mode env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (inferBody (pureFns mode env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw) ?_
    intro te hte
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel hte hw)) ?_
    intro w hww
    rw [getAppFn_shiftFrom]
    cases hfn : w.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const T us₂ =>
    simp only [shiftFrom]
    cases hfp : env.findProj? T i with
    | none => rfl
    | some entry =>
      dsimp only
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun hc => ?_) (fun _ => rfl)
      -- task #175 S1: the body's instantiation commutes with the
      -- shift — the body is fvar-free, so the shift passes to the
      -- spine and the subject
      obtain ⟨-, hlen, -⟩ := hc
      have hsh := ProjEntry.typeAt_shiftFrom (p := p) henv hfp us₂ hlen pe
      -- the Prop guard (task #175 W4c) is shift-independent: split it
      -- on both sides, then the residual
      by_cases hs : (entry.structSort.isEquiv Level.zero == some true) = true
      · rw [ite_eq_left hs, ite_eq_left hs]
        by_cases hfs : ((Level.subst entry.levelParams us₂
            entry.fieldSort).isEquiv Level.zero == some true) = true
        · rw [ite_eq_left hfs, ite_eq_left hfs, ← hsh]
          rfl
        · rw [ite_eq_right hfs, ite_eq_right hfs]
          rfl
      · rw [ite_eq_right hs, ite_eq_right hs, ← hsh]
        rfl

/-- The io *lane* (the leaf knot, `inferTypeCoreIO`) commutes with the
shift (task #172 B4): `infer_step`'s walk with the io folds and the io
scoping lemmas. -/
private theorem inferIOCore_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel)
    (ihio : ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
      inferTypeCoreIO mode env fuel (d + 1) (shiftFrom p e) =
        (inferTypeCoreIO mode env fuel d e).map (shiftFrom p)) :
    ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
      inferTypeCoreIO mode env (fuel + 1) (d + 1) (shiftFrom p e) =
        (inferTypeCoreIO mode env (fuel + 1) d e).map (shiftFrom p) := by
  intro p d hpd e hw
  rw [inferTypeCoreIO_succ, inferTypeCoreIO_succ]
  match e with
  | .bvar i => rfl
  | .letE ty v body =>
    -- official `infer_let` at `infer_only`: the body at the value
    simp only [WScoped] at hw
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1)
        (.letE (shiftFrom p ty) (shiftFrom p v) (shiftFrom p body)) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.letE ty v body)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def]
    have h := ihio hpd (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
    rw [shiftFrom_instantiate1_gen] at h
    exact h
  | .sort u => rfl
  | .lit (.natVal n) =>
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1) (.lit (.natVal n)) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [inferBodyIO]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .lit (.strVal str) =>
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1) (.lit (.strVal str)) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [inferBodyIO]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx ty =>
    simp only [WScoped] at hw
    rw [shiftFrom_fvar]
    simp only [inferBodyIO]
    rw [ite_eq_left (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        ite_eq_left hw.1]
    by_cases hp : p ≤ idx
    · simp [shiftTy, hp, pure, Except.pure]
    · simp only [shiftTy, ite_eq_right hp, pure, Except.pure, map_ok]
      rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
  | .const n us =>
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1) (.const n us) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.const n us)).map (shiftFrom p)
    simp only [inferBodyIO]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      have hty : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv.consts _ (Env.find?_mem hf)).1
      simp only [pure, Except.pure, map_ok,
        shiftFrom_eq_self_of_not_hasFvar hty]
  | .forallE ty body =>
    simp only [WScoped] at hw
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1)
        (.forallE (shiftFrom p ty) (shiftFrom p body)) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.forallE ty body)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def,
      pureFnsIO_whnf, ensureSortIO_def]
    refine bind_rel _ _ (ihio hpd hw.1) ?_
    intro tty htty
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCoreIO_WScoped henv fuel htty hw.1)) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case sort u =>
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ihio (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCoreIO_WScoped henv fuel hbt hwo
    refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
      (d := d + 1) (by omega) hwbt) ?_
    intro v _
    rfl
  | .lam ty body =>
    simp only [WScoped] at hw
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1)
        (.lam (shiftFrom p ty) (shiftFrom p body)) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.lam ty body)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def]
    -- task #168 stage 2: no domain-sort run at the io λ clause
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ihio (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCoreIO_WScoped henv fuel hbt hwo
    show pure _ = Except.map _ (pure _)
    rw [← shiftFrom_abstract1 hpd]; rfl
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [inferBodyIO, inferIO_def,
      pureFnsIO_whnf]
    refine bind_rel _ _ (ihio hpd hw.1) ?_
    intro tf htf
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCoreIO_WScoped henv fuel htf hw.1)) ?_
    intro w hww
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE ty' body' =>
    have hwPi : WScoped d (Expr.forallE ty' body') :=
      whnf_WScoped henv fuel hww (inferTypeCoreIO_WScoped henv fuel htf hw.1)
    simp only [WScoped] at hwPi
    dsimp only [shiftFrom]
    -- the io application checks no argument (task #346)
    simp only [pure, Except.pure, map_ok]
    rw [← shiftFrom_instantiate1_gen]
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show inferBodyIO (pureFnsIO mode env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (inferBodyIO (pureFnsIO mode env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def,
      pureFnsIO_whnf]
    refine bind_rel _ _ (ihio hpd hw) ?_
    intro te hte
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCoreIO_WScoped henv fuel hte hw)) ?_
    intro w hww
    rw [getAppFn_shiftFrom]
    cases hfn : w.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const T us₂ =>
    simp only [shiftFrom]
    cases hfp : env.findProj? T i with
    | none => rfl
    | some entry =>
      dsimp only
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun hc => ?_) (fun _ => rfl)
      -- task #175 S1: the body's instantiation commutes with the
      -- shift — the body is fvar-free, so the shift passes to the
      -- spine and the subject
      obtain ⟨-, hlen, -⟩ := hc
      have hsh := ProjEntry.typeAt_shiftFrom (p := p) henv hfp us₂ hlen pe
      -- the Prop guard (task #175 W4c) is shift-independent: split it
      -- on both sides, then the residual
      by_cases hs : (entry.structSort.isEquiv Level.zero == some true) = true
      · rw [ite_eq_left hs, ite_eq_left hs]
        by_cases hfs : ((Level.subst entry.levelParams us₂
            entry.fieldSort).isEquiv Level.zero == some true) = true
        · rw [ite_eq_left hfs, ite_eq_left hfs, ← hsh]
          rfl
        · rw [ite_eq_right hfs, ite_eq_right hfs]
          rfl
      · rw [ite_eq_right hs, ite_eq_right hs, ← hsh]
        rfl

/-- The knot's io *slot* commutes with the shift, at `fuel + 1`
(task #172 B4): it is the io lane's walk through `inferTypeIO_on`. -/
private theorem inferIOSlot_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : InferIOShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [inferTypeIO_on, inferTypeIO_on]
  refine inferIOCore_step henv ih ?_ hpd hw
  intro p' d' hpd' e' hw'
  rw [← inferTypeIO_on, ← inferTypeIO_on]
  exact ih.inferIO hpd' hw'

private theorem isBoolTrue_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).isBoolTrue = e.isBoolTrue := by
  cases e <;> first
    | rfl
    | (simp only [shiftFrom]; split <;> rfl)

/-- The eq-true shortcut (the audit's E2) is shift-invariant: one `whnf`
and a head test that ignores the shift. -/
private theorem boolTrueShortcut_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a : Expr}
    (hwa : WScoped d a) :
    boolTrueShortcut (pureFns mode env fuel) (d + 1) (shiftFrom p a) =
      boolTrueShortcut (pureFns mode env fuel) d a := by
  unfold boolTrueShortcut
  refine bind_congr (shiftFrom p) (ih.whnf hpd hwa) ?_
  intro w _
  rw [isBoolTrue_shiftFrom]

/-- `boolTrueShortcut_shift` under its guard. -/
private theorem boolTrueShortcutIf_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a : Expr}
    (hwa : WScoped d a) (g : Bool) :
    (if g then boolTrueShortcut (pureFns mode env fuel) (d + 1) (shiftFrom p a)
        else pure false) =
      (if g then boolTrueShortcut (pureFns mode env fuel) d a else pure false) := by
  cases g
  · rfl
  · exact boolTrueShortcut_shift henv ih hpd hwa

/-- A lazy-delta step's outcome under a map of its pair. -/
private def DeltaStep.mapE (σ : Expr → Expr) : DeltaStep → DeltaStep
  | .cont a b => .cont (σ a) (σ b)
  | .eq => .eq
  | .diff => .diff
  | .unknown => .unknown

/-- The lazy-delta loop's outcome under a map of its stuck pair. -/
private def LazyRes.mapE (σ : Expr → Expr) : LazyRes → LazyRes
  | .verdict v => .verdict v
  | .unknown a b => .unknown (σ a) (σ b)

private theorem headIsProj_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).headIsProj = e.headIsProj := by
  unfold Expr.headIsProj
  rw [getAppFn_shiftFrom]
  cases e.getAppFn <;> first | rfl | (rw [shiftFrom_fvar]; done) | (rw [shiftFrom_fvar]; rfl)

private theorem isNatZero_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).isNatZero = e.isNatZero := by
  cases e <;> first | rfl | (rw [shiftFrom_fvar]; done) | (rw [shiftFrom_fvar]; rfl)

private theorem isLit_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).isLit = e.isLit := by
  cases e <;> first | rfl | (rw [shiftFrom_fvar]; done) | (rw [shiftFrom_fvar]; rfl)

private theorem natPred?_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).natPred? = e.natPred?.map (shiftFrom p) := by
  match e with
  | .lit (.natVal 0) => rfl
  | .lit (.natVal (n + 1)) => rfl
  | .lit (.strVal _) => rfl
  | .app (.const c []) x =>
    simp only [shiftFrom, Expr.natPred?]
    split <;> rfl
  | .app (.const c (u :: us)) x => rfl
  | .app (.fvar i t) x =>
    simp only [shiftFrom]
    split <;> rfl
  | .app (.bvar _) _ | .app (.sort _) _ | .app (.app _ _) _ | .app (.lam _ _) _
  | .app (.forallE _ _) _ | .app (.letE _ _ _) _ | .app (.lit _) _
  | .app (.proj _ _ _) _ => rfl
  | .bvar _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _
  | .proj _ _ _ => rfl
  | .fvar i t =>
    simp only [shiftFrom]
    split <;> rfl

/-- The innermost level of `defeqLams` is shift-invariant. -/
private theorem defeqLamsInner_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {b₁ b₂ : Expr}
    (hw₁ : WScoped (d + 1) b₁) (hw₂ : WScoped (d + 1) b₂) :
    defeqLamsInner mode (pureFns mode env fuel) (d + 1) (shiftFrom p b₁) (shiftFrom p b₂) =
      defeqLamsInner mode (pureFns mode env fuel) d b₁ b₂ := by
  simp only [defeqLamsInner]
  refine bind_congr_eq (ih.defeq (p := p) (d := d + 1) (by omega) hw₁ hw₂) ?_
  intro bb _
  refine ite_congr' (fun _ => ?_) (fun _ => rfl)
  refine ite_congr' (fun _ => ?_) (fun _ => rfl)
  refine bind_congr _ (ih.infer (p := p) (d := d + 1) (by omega) hw₁) ?_
  intro t₁ ht₁
  refine bind_congr _ (ih.infer (p := p) (d := d + 1) (by omega) hw₂) ?_
  intro t₂ ht₂
  refine bind_congr_eq (ih.defeq (p := p) (d := d + 1) (by omega)
    (inferTypeCore_WScoped henv fuel ht₁ hw₁) (inferTypeCore_WScoped henv fuel ht₂ hw₂)) ?_
  intro _ _
  rfl

private theorem lamPair?_shiftFrom {p : Nat} (B₁ B₂ : Expr) :
    Expr.lamPair? (shiftFrom p B₁) (shiftFrom p B₂) =
      (Expr.lamPair? B₁ B₂).map fun q =>
        (shiftFrom p q.1, shiftFrom p q.2.1, shiftFrom p q.2.2.1, shiftFrom p q.2.2.2) := by
  cases B₁ <;> cases B₂ <;> (try rw [shiftFrom_fvar]) <;> (try rw [shiftFrom_fvar]) <;>
    simp [shiftFrom, Expr.lamPair?]

/-- The λ-telescope comparison is shift-invariant (by induction on its
descent budget). -/
private theorem defeqLams_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) :
    ∀ (k : Nat) {p d : Nat}, p ≤ d → ∀ {ty₁ body₁ ty₂ body₂ : Expr},
      WScoped d ty₁ → WScoped d body₁ → WScoped d ty₂ → WScoped d body₂ →
      defeqLams mode (pureFns mode env fuel) k (d + 1) (shiftFrom p ty₁)
          (shiftFrom p body₁) (shiftFrom p ty₂) (shiftFrom p body₂) =
        defeqLams mode (pureFns mode env fuel) k d ty₁ body₁ ty₂ body₂
  | k, p, d, hpd, ty₁, body₁, ty₂, body₂, hwt₁, hwb₁, hwt₂, hwb₂ => by
    rw [defeqLams.eq_def, defeqLams.eq_def]
    refine bind_congr_eq (ih.defeq hpd hwt₁ hwt₂) ?_
    intro bb _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    dsimp only
    have hB₁ : WScoped (d + 1) (body₁.instantiate1 (.fvar d ty₂)) :=
      WScoped.instantiate1 hwt₂ 0 hwb₁
    have hB₂ : WScoped (d + 1) (body₂.instantiate1 (.fvar d ty₂)) :=
      WScoped.instantiate1 hwt₂ 0 hwb₂
    rw [← shiftFrom_instantiate1 hpd, ← shiftFrom_instantiate1 hpd, lamPair?_shiftFrom]
    generalize body₁.instantiate1 (.fvar d ty₂) = B₁ at hB₁ ⊢
    generalize body₂.instantiate1 (.fvar d ty₂) = B₂ at hB₂ ⊢
    cases hlp : Expr.lamPair? B₁ B₂ with
    | none =>
      cases k <;> exact defeqLamsInner_shift henv ih hpd hB₁ hB₂
    | some q =>
      obtain ⟨t₁, b₁, t₂, b₂⟩ := q
      cases k with
      | zero => exact defeqLamsInner_shift henv ih hpd hB₁ hB₂
      | succ k =>
        obtain ⟨rfl, rfl⟩ := Expr.lamPair?_some hlp
        simp only [WScoped] at hB₁ hB₂
        dsimp only [Option.map_some]
        rw [shiftFrom_beq]
        refine ite_congr' (fun _ => rfl) (fun _ => ?_)
        exact defeqLams_shift henv ih k (by omega) hB₁.1 hB₁.2 hB₂.1 hB₂.2

/-- The easy cases are shift-invariant. -/
private theorem quickDefEq_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    quickDefEq mode (pureFns mode env fuel) (d + 1) (shiftFrom p a) (shiftFrom p b) =
      quickDefEq mode (pureFns mode env fuel) d a b := by
  unfold quickDefEq
  rw [shiftFrom_beq]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  cases a <;> cases b <;>
    first
    | rfl
    | (simp only [shiftFrom_fvar]; done)
    | (simp only [shiftFrom_fvar]; rfl)
    | skip
  case forallE.forallE ty₁ body₁ ty₂ body₂ =>
    simp only [WScoped] at hwa hwb
    simp only [shiftFrom]
    refine bind_congr_eq (ih.defeq hpd hwa.1 hwb.1) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hb := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 hwb.1 0 hwa.2)
      (WScoped.instantiate1 hwb.1 0 hwb.2)
    rw [shiftFrom_instantiate1 hpd, shiftFrom_instantiate1 hpd] at hb
    refine bind_congr_eq hb ?_
    intro b₂ _
    rfl
  case lam.lam ty₁ body₁ ty₂ body₂ =>
    simp only [WScoped] at hwa hwb
    simp only [shiftFrom]
    rw [defeqLams_shift henv ih lamsFuel hpd hwa.1 hwa.2 hwb.1 hwb.2]

/-- Offsets are shift-invariant. -/
private theorem defeqOffset_shift
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    defeqOffset (pureFns mode env fuel) (d + 1) (shiftFrom p a) (shiftFrom p b) =
      defeqOffset (pureFns mode env fuel) d a b := by
  unfold defeqOffset
  rw [isNatZero_shiftFrom, isNatZero_shiftFrom, isLit_shiftFrom, isLit_shiftFrom,
    natPred?_shiftFrom, natPred?_shiftFrom]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  cases hx : a.natPred? <;> cases hy : b.natPred? <;> try rfl
  rename_i x y
  simp only [Option.map_some]
  refine bind_congr_eq (ih.defeq hpd (natPred?_WScoped hx hwa)
    (natPred?_WScoped hy hwb)) ?_
  intro v _
  rfl

/-- `try_unfold_proj_app` commutes with the shift. -/
private theorem tryUnfoldProjApp_shift
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    tryUnfoldProjApp (pureFns mode env fuel) (d + 1) (shiftFrom p e) =
      (tryUnfoldProjApp (pureFns mode env fuel) d e).map (Option.map (shiftFrom p)) := by
  unfold tryUnfoldProjApp
  rw [headIsProj_shiftFrom]
  refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
  refine bind_rel (shiftFrom p) _ (ih.whnfCore hpd hw) ?_
  intro e' _
  rw [shiftFrom_beq]
  exact ite_rel _ (fun _ => rfl) (fun _ => rfl)

/-- The end of a step commutes with the shift. -/
private theorem deltaQuick_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    deltaQuick mode (pureFns mode env fuel) (d + 1) (shiftFrom p a) (shiftFrom p b) =
      (deltaQuick mode (pureFns mode env fuel) d a b).map (DeltaStep.mapE (shiftFrom p)) := by
  unfold deltaQuick
  refine bind_rel_eq _ (quickDefEq_shift henv ih hpd hwa hwb) ?_
  intro o _
  match o with
  | none => rfl
  | some true => rfl
  | some false => rfl

/-- The scoping of the step's and the loop's pairs. -/
private theorem lazyDeltaStep_WScoped (henv : EnvWF env) {d : Nat} {a b a' b' : Expr}
    (h : lazyDeltaStep mode (pureFns mode env fuel) env d a b = .ok (.cont a' b'))
    (hwa : WScoped d a) (hwb : WScoped d b) : WScoped d a' ∧ WScoped d b' :=
  lazyDeltaStep_pres (WScoped d) (fun hu hx => unfoldDefinition_WScoped henv hu hx)
    (fun hc hx => whnfCore_WScoped henv fuel hc hx) h hwa hwb

private theorem lazyDeltaReduction_WScoped (henv : EnvWF env) {d n : Nat}
    {a b a₁ b₁ : Expr}
    (h : lazyDeltaReduction mode (pureFns mode env fuel) env d n a b =
      .ok (.unknown a₁ b₁))
    (hwa : WScoped d a) (hwb : WScoped d b) : WScoped d a₁ ∧ WScoped d b₁ :=
  lazyDeltaReduction_pres (WScoped d) (fun hu hx => unfoldDefinition_WScoped henv hu hx)
    (fun hc hx => whnfCore_WScoped henv fuel hc hx) n h hwa hwb

/-- One unfolding put through the cheap `whnfCore`, then the step's end,
commutes with the shift. -/
private theorem unfoldQuickL_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    (match unfoldDefinition env (shiftFrom p a) with
      | some a₂ => do
        let a₃ ← (pureFns mode env fuel).whnfCore true (d + 1) a₂
        deltaQuick mode (pureFns mode env fuel) (d + 1) a₃ (shiftFrom p b)
      | none => pure .unknown) =
    (match unfoldDefinition env a with
      | some a₂ => do
        let a₃ ← (pureFns mode env fuel).whnfCore true d a₂
        deltaQuick mode (pureFns mode env fuel) d a₃ b
      | none => pure .unknown).map (DeltaStep.mapE (shiftFrom p)) := by
  rw [unfoldDefinition_shiftFrom henv]
  cases hu : unfoldDefinition env a with
  | none => rfl
  | some a₂ =>
    simp only [Option.map_some]
    have hwa₂ := unfoldDefinition_WScoped henv hu hwa
    refine bind_rel (shiftFrom p) _ (ih.whnfCore hpd hwa₂) ?_
    intro a₃ ha₃
    exact deltaQuick_shift henv ih hpd (whnfCore_WScoped henv fuel ha₃ hwa₂) hwb

private theorem unfoldQuickR_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    (match unfoldDefinition env (shiftFrom p b) with
      | some b₂ => do
        let b₃ ← (pureFns mode env fuel).whnfCore true (d + 1) b₂
        deltaQuick mode (pureFns mode env fuel) (d + 1) (shiftFrom p a) b₃
      | none => pure .unknown) =
    (match unfoldDefinition env b with
      | some b₂ => do
        let b₃ ← (pureFns mode env fuel).whnfCore true d b₂
        deltaQuick mode (pureFns mode env fuel) d a b₃
      | none => pure .unknown).map (DeltaStep.mapE (shiftFrom p)) := by
  rw [unfoldDefinition_shiftFrom henv]
  cases hu : unfoldDefinition env b with
  | none => rfl
  | some b₂ =>
    simp only [Option.map_some]
    have hwb₂ := unfoldDefinition_WScoped henv hu hwb
    refine bind_rel (shiftFrom p) _ (ih.whnfCore hpd hwb₂) ?_
    intro b₃ hb₃
    exact deltaQuick_shift henv ih hpd hwa (whnfCore_WScoped henv fuel hb₃ hwb₂)

/-- One lazy-delta step commutes with the shift. -/
private theorem lazyDeltaStep_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    lazyDeltaStep mode (pureFns mode env fuel) env (d + 1) (shiftFrom p a) (shiftFrom p b) =
      (lazyDeltaStep mode (pureFns mode env fuel) env d a b).map
        (DeltaStep.mapE (shiftFrom p)) := by
  unfold lazyDeltaStep
  rw [unfoldableHead_shiftFrom, unfoldableHead_shiftFrom]
  cases hda : unfoldableHead env a <;> cases hdb : unfoldableHead env b <;> dsimp only
  · rfl
  · refine bind_rel (Option.map (shiftFrom p)) _ (tryUnfoldProjApp_shift ih hpd hwa) ?_
    intro o ho
    cases o with
    | some a₂ =>
      simp only [Option.map_some]
      have hwa₂ : WScoped d a₂ := by
        simp only [tryUnfoldProjApp, Bind.bind, Except.bind] at ho
        split at ho
        · cases hw : (pureFns mode env fuel).whnfCore false d a with
          | error err => rw [hw] at ho; exact nomatch ho
          | ok x =>
          rw [hw] at ho
          dsimp only at ho
          split at ho
          · simp [pure, Except.pure] at ho
          · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ho
            subst ho
            exact whnfCore_WScoped henv fuel hw hwa
        · simp [pure, Except.pure] at ho
      exact deltaQuick_shift henv ih hpd hwa₂ hwb
    | none => exact unfoldQuickR_shift henv ih hpd hwa hwb
  · refine bind_rel (Option.map (shiftFrom p)) _ (tryUnfoldProjApp_shift ih hpd hwb) ?_
    intro o ho
    cases o with
    | some b₂ =>
      simp only [Option.map_some]
      have hwb₂ : WScoped d b₂ := by
        simp only [tryUnfoldProjApp, Bind.bind, Except.bind] at ho
        split at ho
        · cases hw : (pureFns mode env fuel).whnfCore false d b with
          | error err => rw [hw] at ho; exact nomatch ho
          | ok x =>
          rw [hw] at ho
          dsimp only at ho
          split at ho
          · simp [pure, Except.pure] at ho
          · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ho
            subst ho
            exact whnfCore_WScoped henv fuel hw hwb
        · simp [pure, Except.pure] at ho
      exact deltaQuick_shift henv ih hpd hwa hwb₂
    | none => exact unfoldQuickL_shift henv ih hpd hwa hwb
  · rw [headHint_shiftFrom, headHint_shiftFrom]
    refine ite_rel _ (fun _ => unfoldQuickL_shift henv ih hpd hwa hwb) (fun _ => ?_)
    refine ite_rel _ (fun _ => unfoldQuickR_shift henv ih hpd hwa hwb) (fun _ => ?_)
    rw [sameConstHeads_shiftFrom]
    have hsp : ∀ g : Bool,
        (if g then defeqSpine (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
          (shiftFrom p b) else pure false) =
        (if g then defeqSpine (pureFns mode env fuel) env d a b else pure false) := by
      intro g
      cases g
      · rfl
      · exact defeqSpine_shift henv ih hpd hwa hwb
    refine bind_rel_eq _ (hsp _) ?_
    intro bb _
    refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
    rw [unfoldDefinition_shiftFrom henv, unfoldDefinition_shiftFrom henv]
    cases hua : unfoldDefinition env a <;> cases hub : unfoldDefinition env b <;>
      simp only [Option.map_some, Option.map_none] <;> try rfl
    rename_i a₂ b₂
    have hwa₂ := unfoldDefinition_WScoped henv hua hwa
    have hwb₂ := unfoldDefinition_WScoped henv hub hwb
    refine bind_rel (shiftFrom p) _ (ih.whnfCore hpd hwa₂) ?_
    intro a₃ ha₃
    refine bind_rel (shiftFrom p) _ (ih.whnfCore hpd hwb₂) ?_
    intro b₃ hb₃
    exact deltaQuick_shift henv ih hpd (whnfCore_WScoped henv fuel ha₃ hwa₂)
      (whnfCore_WScoped henv fuel hb₃ hwb₂)

/-- The lazy-delta loop commutes with the shift, by induction on its
own step budget. -/
private theorem lazyDeltaReduction_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) :
    ∀ (n : Nat) {p d : Nat}, p ≤ d → ∀ {a b : Expr}, WScoped d a → WScoped d b →
      lazyDeltaReduction mode (pureFns mode env fuel) env (d + 1) n (shiftFrom p a)
          (shiftFrom p b) =
        (lazyDeltaReduction mode (pureFns mode env fuel) env d n a b).map
          (LazyRes.mapE (shiftFrom p)) := by
  intro n
  induction n with
  | zero => intro p d _ a b _ _; rfl
  | succ n ihN =>
  intro p d hpd a b hwa hwb
  simp only [lazyDeltaReduction]
  refine bind_rel_eq _ (defeqOffset_shift ih hpd hwa hwb) ?_
  intro o _
  cases o with
  | some v => rfl
  | none =>
  dsimp only
  simp only [hasFvar_shiftFrom]
  refine bind_rel (Option.map (shiftFrom p)) _ (reduceNatIf_shift henv ih hpd hwa _) ?_
  intro oa hoa
  cases oa with
  | some a₂ =>
    simp only [Option.map_some]
    have hwa₂ : WScoped d a₂ := by
      rcases reduceNat_inv (reduceNatIf_some hoa) with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    refine bind_rel id _ ?_ (fun v _ => rfl)
    rw [show ((pureFns mode env fuel).defeq (d + 1) (shiftFrom p a₂) (shiftFrom p b)) =
      isDefEqCore mode env fuel (d + 1) (shiftFrom p a₂) (shiftFrom p b) from rfl,
      ih.defeq hpd hwa₂ hwb,
      show (pureFns mode env fuel).defeq d a₂ b = isDefEqCore mode env fuel d a₂ b from rfl]
    cases isDefEqCore mode env fuel d a₂ b <;> rfl
  | none =>
  dsimp only
  refine bind_rel (Option.map (shiftFrom p)) _ (reduceNatIf_shift henv ih hpd hwb _) ?_
  intro ob hob
  cases ob with
  | some b₂ =>
    simp only [Option.map_some]
    have hwb₂ : WScoped d b₂ := by
      rcases reduceNat_inv (reduceNatIf_some hob) with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    refine bind_rel id _ ?_ (fun v _ => rfl)
    rw [show ((pureFns mode env fuel).defeq (d + 1) (shiftFrom p a) (shiftFrom p b₂)) =
      isDefEqCore mode env fuel (d + 1) (shiftFrom p a) (shiftFrom p b₂) from rfl,
      ih.defeq hpd hwa hwb₂,
      show (pureFns mode env fuel).defeq d a b₂ = isDefEqCore mode env fuel d a b₂ from rfl]
    cases isDefEqCore mode env fuel d a b₂ <;> rfl
  | none =>
  dsimp only
  refine bind_rel (DeltaStep.mapE (shiftFrom p)) _
    (lazyDeltaStep_shift henv ih hpd hwa hwb) ?_
  intro st hst
  cases st with
  | cont a' b' =>
    obtain ⟨hwa', hwb'⟩ := lazyDeltaStep_WScoped henv hst hwa hwb
    exact ihN hpd hwa' hwb'
  | eq => rfl
  | diff => rfl
  | unknown => rfl

/-- `lazy_delta_proj_reduction` is shift-invariant. -/
private theorem lazyDeltaProjReduction_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {sn : Name} {i : Nat} :
    ∀ (n : Nat) {p d : Nat}, p ≤ d → ∀ {a b : Expr}, WScoped d a → WScoped d b →
      lazyDeltaProjReduction mode (pureFns mode env fuel) env (d + 1) sn i n
          (shiftFrom p a) (shiftFrom p b) =
        lazyDeltaProjReduction mode (pureFns mode env fuel) env d sn i n a b := by
  intro n
  induction n with
  | zero => intro p d _ a b _ _; rfl
  | succ n ihN =>
  intro p d hpd a b hwa hwb
  simp only [lazyDeltaProjReduction]
  refine bind_congr (DeltaStep.mapE (shiftFrom p))
    (lazyDeltaStep_shift henv ih hpd hwa hwb) ?_
  intro st hst
  have hpc : ∀ {x : Expr}, WScoped d x → ∀ {o : Option Expr},
      reduceProjCore mode (pureFns mode env fuel) env d sn i x = .ok o →
      ∀ {m : Expr}, o = some m → WScoped d m := by
    intro x hx o ho m hm
    subst hm
    exact reduceProjCore_pres (WScoped d) (fun hx => hx.getAppArgs)
      (fun h hx => whnf_WScoped henv fuel h hx)
      (fun s _ => strLitToConstructor_WScoped s d) ho hx
  cases st
  case cont a' b' =>
    obtain ⟨hwa', hwb'⟩ := lazyDeltaStep_WScoped henv hst hwa hwb
    exact ihN hpd hwa' hwb'
  case eq => rfl
  all_goals
    simp only [DeltaStep.mapE]
    refine bind_congr (Option.map (shiftFrom p)) (reduceProjCore_shift henv ih hpd hwa) ?_
    intro ox hox
    cases ox with
    | none => exact ih.defeq hpd hwa hwb
    | some x =>
    simp only [Option.map_some]
    refine bind_congr (Option.map (shiftFrom p)) (reduceProjCore_shift henv ih hpd hwb) ?_
    intro oy hoy
    cases oy with
    | none => exact ih.defeq hpd hwa hwb
    | some y => exact ih.defeq hpd (hpc hwa hox rfl) (hpc hwb hoy rfl)

/-- The proj/proj check is shift-invariant. -/
private theorem defeqProjPair_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    defeqProjPair mode (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      defeqProjPair mode (pureFns mode env fuel) env d a b := by
  unfold defeqProjPair
  cases a with
  | proj s₁ i₁ e₁ =>
    cases b with
    | proj s₂ i₂ e₂ =>
      simp only [WScoped] at hwa hwb
      exact ite_congr' (fun _ => lazyDeltaProjReduction_shift henv ih _ hpd hwa hwb)
        (fun _ => rfl)
    | fvar => first | rfl | (rw [shiftFrom_fvar]; try rfl)
    | _ => rfl
  | fvar => first | rfl | (rw [shiftFrom_fvar]; try rfl)
  | _ => rfl

/-- The stuck comparison is shift-invariant. -/
private theorem defeqStuck_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {wa wb : Expr}
    (hwwa : WScoped d wa) (hwwb : WScoped d wb) :
    defeqStuck mode (pureFns mode env fuel) env (d + 1) (shiftFrom p wa)
        (shiftFrom p wb) =
      defeqStuck mode (pureFns mode env fuel) env d wa wb := by
  unfold defeqStuck
  have hstuck : stuckIrrel (pureFns mode env fuel) env (d + 1) (shiftFrom p wa)
      (shiftFrom p wb) = stuckIrrel (pureFns mode env fuel) env d wa wb :=
    stuckIrrel_shift henv ih hpd hwwa hwwb
  cases wa <;> cases wb <;>
    try (first
      | exact hstuck
      | (try simp only [shiftFrom_fvar] at hstuck
         simp only [shiftFrom_fvar]
         exact hstuck))
  case lit.app l f x =>
    simp only [WScoped] at hwwb
    cases l with
    | strVal str =>
      cases f <;>
        try (first
          | exact hstuck
          | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
             exact hstuck))
      case const cn cus =>
      refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
      have hres := ih.defeq (p := p) hpd
        (strLitToConstructor_WScoped str d)
        (show WScoped d (Expr.app (.const cn cus) x) by
          simp only [WScoped]; exact ⟨trivial, hwwb.2⟩)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    | natVal nn =>
      cases f <;>
        try (first
          | exact hstuck
          | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
             exact hstuck))
  case app.lit f x l =>
    simp only [WScoped] at hwwa
    cases l with
    | strVal str =>
      cases f <;>
        try (first
          | exact hstuck
          | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
             exact hstuck))
      case const cn cus =>
      refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
      have hres := ih.defeq (p := p) hpd
        (show WScoped d (Expr.app (.const cn cus) x) by
          simp only [WScoped]; exact ⟨trivial, hwwa.2⟩)
        (strLitToConstructor_WScoped str d)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    | natVal nn =>
      cases f <;>
        try (first
          | exact hstuck
          | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
             exact hstuck))
  case fvar.fvar idx₁ ty₁ idx₂ ty₂ =>
    simp only [shiftFrom_fvar] at hstuck ⊢
    rw [shiftIdx_beq]
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.const n us n' us' =>
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq rfl ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case app.app f₁ a₁ f₂ a₂ =>
    -- spine-wise congruence (task #106): one head comparison and the
    -- argument lists pairwise, all shift-invariant
    have hwa' : WScoped d (Expr.app f₁ a₁) := hwwa
    have hwb' : WScoped d (Expr.app f₂ a₂) := hwwb
    simp only [shiftFrom_app] at hstuck ⊢
    have hargs₁ : (Expr.app (shiftFrom p f₁) (shiftFrom p a₁)).getAppArgs
        = (Expr.app f₁ a₁).getAppArgs.map (shiftFrom p) :=
      getAppArgs_shiftFrom (.app f₁ a₁)
    have hargs₂ : (Expr.app (shiftFrom p f₂) (shiftFrom p a₂)).getAppArgs
        = (Expr.app f₂ a₂).getAppArgs.map (shiftFrom p) :=
      getAppArgs_shiftFrom (.app f₂ a₂)
    have hfn₁ : (Expr.app (shiftFrom p f₁) (shiftFrom p a₁)).getAppFn
        = shiftFrom p (Expr.app f₁ a₁).getAppFn :=
      getAppFn_shiftFrom (.app f₁ a₁)
    have hfn₂ : (Expr.app (shiftFrom p f₂) (shiftFrom p a₂)).getAppFn
        = shiftFrom p (Expr.app f₂ a₂).getAppFn :=
      getAppFn_shiftFrom (.app f₂ a₂)
    rw [hargs₁, hargs₂, List.length_map, List.length_map, hfn₁, hfn₂]
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq (ih.defeq hpd hwa'.getAppFn hwb'.getAppFn) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq
      (defEqList_shift henv ih hpd hwa'.getAppArgs hwb'.getAppArgs) ?_
    intro b₂ _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.fvar ty1 body1 ix tt =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    try simp only [shiftFrom_fvar] at hstuck
    try simp only [shiftFrom_fvar]
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.sort ty1 body1 u =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.const ty1 body1 cn cus =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.app ty1 body1 ff aa =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.forallE ty1 body1 fty fbody =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.lit ty1 body1 ll =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.proj ty1 body1 ps pi2 pe2 =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case fvar.lam ix tt ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    try simp only [shiftFrom_fvar] at hstuck
    try simp only [shiftFrom_fvar]
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case sort.lam u ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.lam cn cus ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case app.lam ff aa ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case forallE.lam fty fbody ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lit.lam ll ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case proj.lam ps pi2 pe2 ty2 body2 =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)

private theorem defeq_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : DefEqShift mode env (fuel + 1) := by
  intro p d hpd a b hwa hwb
  rw [isDefEqCore_succ, isDefEqCore_succ]
  simp only [defeqBody]
  rw [shiftFrom_beq]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  -- the eq-true shortcut (E2): its guard reads the shifted sides' head
  -- and fvar range, both shift-invariant
  rw [isBoolTrue_shiftFrom, hasFvar_shiftFrom]
  refine bind_congr_eq (boolTrueShortcutIf_shift henv ih hpd hwa _) ?_
  rintro rbt -
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr_eq (quickDefEq_shift henv ih hpd hwa hwb) ?_
  intro o₀ _
  cases o₀ with
  | some v => rfl
  | none =>
  dsimp only
  refine bind_congr_eq (propIrrel_shift henv ih hpd hwa hwb) ?_
  rintro rpi -
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr _ (ih.whnfCore hpd hwa) ?_
  intro wa hwa'
  refine bind_congr _ (ih.whnfCore hpd hwb) ?_
  intro wb hwb'
  have hwwa : WScoped d wa := whnfCore_WScoped henv fuel hwa' hwa
  have hwwb : WScoped d wb := whnfCore_WScoped henv fuel hwb' hwb
  refine bind_congr_eq (quickDefEq_shift henv ih hpd hwwa hwwb) ?_
  intro o _
  cases o with
  | some v => rfl
  | none =>
  dsimp only
  refine bind_congr (LazyRes.mapE (shiftFrom p))
    (lazyDeltaReduction_shift henv ih _ hpd hwwa hwwb) ?_
  intro lr hlr
  cases lr with
  | verdict v => rfl
  | unknown a₁ b₁ =>
  obtain ⟨hwa₁, hwb₁⟩ := lazyDeltaReduction_WScoped henv hlr hwwa hwwb
  simp only [LazyRes.mapE]
  refine bind_congr_eq (defeqProjPair_shift henv ih hpd hwa₁ hwb₁) ?_
  rintro rp -
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  rw [headIsProj_shiftFrom, headIsProj_shiftFrom]
  refine ite_congr' (fun _ => defeqStuck_shift henv ih hpd hwa₁ hwb₁) (fun _ => ?_)
  refine bind_congr _ (ih.whnfCore hpd hwa₁) ?_
  intro a₂ ha₂
  refine bind_congr _ (ih.whnfCore hpd hwb₁) ?_
  intro b₂ hb₂
  rw [shiftFrom_beq, shiftFrom_beq]
  exact ite_congr' (fun _ => defeqStuck_shift henv ih hpd hwa₁ hwb₁)
    (fun _ => ih.defeq hpd (whnfCore_WScoped henv fuel ha₂ hwa₁)
      (whnfCore_WScoped henv fuel hb₂ hwb₁))

end Helpers

/-- The bisimulation: every core entry point commutes with the fvar
shift, at every fuel. -/
theorem shiftClaims {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat), ShiftClaims mode env fuel := by
  intro fuel
  -- over every mode at once: the eager slot is the knot at
  -- `mode.toEager` (task #353)
  induction fuel generalizing mode with
  | zero =>
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ fuel ih =>
    exact ⟨whnfCore_step henv ih, whnf_step henv ih, infer_step henv ih,
      defeq_step henv ih, defeq_step henv (ih (mode := mode.toEager)),
      inferIOSlot_step henv ih⟩

/-! ## Depth invariance -/

section DepthInv

variable {env : Env}

private theorem whnfCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} {c : Bool} (hw : WScoped d e) :
    whnfCore mode env fuel (d + 1) e c = whnfCore mode env fuel d e c := by
  have h := (shiftClaims (mode := mode) henv fuel).whnfCore (c := c) (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : whnfCore mode env fuel d e c with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self (whnfCore_WScoped henv fuel hres hw).fvarsBelow]

private theorem whnf_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    whnf mode env fuel (d + 1) e = whnf mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).whnf (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : whnf mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self (whnf_WScoped henv fuel hres hw).fvarsBelow]

private theorem inferTypeCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    inferTypeCore mode env fuel (d + 1) e = inferTypeCore mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).infer (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : inferTypeCore mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (inferTypeCore_WScoped henv fuel hres hw).fvarsBelow]

private theorem isDefEqCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    isDefEqCore mode env fuel (d + 1) a b = isDefEqCore mode env fuel d a b := by
  have h := (shiftClaims (mode := mode) henv fuel).defeq (Nat.le_refl d) hwa hwb
  rwa [shiftFrom_eq_self hwa.fvarsBelow, shiftFrom_eq_self hwb.fvarsBelow]
    at h

private theorem whnfCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} {c : Bool} (hw : WScoped d₁ e) :
    whnfCore mode env fuel d₂ e c = whnfCore mode env fuel d₁ e c := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      whnfCore_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem whnf_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    whnf mode env fuel d₂ e = whnf mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      whnf_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem inferTypeCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    inferTypeCore mode env fuel d₂ e = inferTypeCore mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      inferTypeCore_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem isDefEqCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {a b : Expr} (hwa : WScoped d₁ a)
    (hwb : WScoped d₁ b) :
    isDefEqCore mode env fuel d₂ a b = isDefEqCore mode env fuel d₁ a b := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      isDefEqCore_depth_succ henv fuel (hwa.mono (by omega))
        (hwb.mono (by omega)), ih]

private theorem inferTypeIO_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    inferTypeIO mode env fuel (d + 1) e = inferTypeIO mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).inferIO (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : inferTypeIO mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (inferTypeIO_WScoped henv fuel hres hw).fvarsBelow]

private theorem inferTypeIO_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    inferTypeIO mode env fuel d₂ e = inferTypeIO mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      inferTypeIO_depth_succ henv fuel (hw.mono (by omega)), ih]

/-- **Depth invariance of head normalization**: `whnfCore`'s result
does not depend on the ambient binder depth, for inputs well-scoped at
both depths. -/
theorem whnfCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} {c : Bool} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    whnfCore mode env fuel d₁ e c = whnfCore mode env fuel d₂ e c := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (whnfCore_depth_le henv fuel hle (WScoped.of_wscopedB h₁)).symm
  · exact whnfCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of the reduction loop**. -/
theorem whnf_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    whnf mode env fuel d₁ e = whnf mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (whnf_depth_le henv fuel hle (WScoped.of_wscopedB h₁)).symm
  · exact whnf_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of inference**. -/
theorem inferTypeCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    inferTypeCore mode env fuel d₁ e = inferTypeCore mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (inferTypeCore_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact inferTypeCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of the io inference slot** (task #172 B4). -/
theorem inferTypeIO_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    inferTypeIO mode env fuel d₁ e = inferTypeIO mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (inferTypeIO_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact inferTypeIO_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of definitional equality**. -/
theorem isDefEqCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {a b : Expr} (ha₁ : a.wscopedB d₁ = true)
    (hb₁ : b.wscopedB d₁ = true) (ha₂ : a.wscopedB d₂ = true)
    (hb₂ : b.wscopedB d₂ = true) :
    isDefEqCore mode env fuel d₁ a b = isDefEqCore mode env fuel d₂ a b := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (isDefEqCore_depth_le henv fuel hle (WScoped.of_wscopedB ha₁)
      (WScoped.of_wscopedB hb₁)).symm
  · exact isDefEqCore_depth_le henv fuel hle (WScoped.of_wscopedB ha₂)
      (WScoped.of_wscopedB hb₂)

end DepthInv

end ConLeche
