import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift
import Setlec.Verify.EnvWF
import Setlec.Verify.InstLevels
import Setlec.Verify.Knot
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves
import Setlec.Verify.Abstract

/-!
# Depth invariance of the checker core

The checker core threads a binder depth, used only to name freshly
opened `fvar`s.  This module proves that every entry point's *result*
is independent of the ambient depth, for inputs well-scoped at both
depths — the theorem that justifies memoizing the cached knot
(`Setlec/Kernel/TypeCheckerC.lean`) under depth-free keys (see
`Setlec/Verify/Bridge.lean` for the retied cache invariant).

The proof is a bisimulation: a run at depth `d` on `e` is matched
against the run at depth `d + 1` on `shiftFrom p e` (all `fvar`s at
indices `≥ p` bumped by one, `p ≤ d` the shift point); the two runs
step in lock-step, results relating by the shift.  One claim per core
entry point (`ShiftClaims`), one helper lemma per record-parameterized
body helper (at the same fuel, against `pureFns env fuel`), one fuel
induction at the knot.  Setting `p := d` and shrinking with
`shiftFrom_eq_self` turns the bisimulation into
`whnfCore env fuel (d+1) e = whnfCore env fuel d e` for `e` scoped at
`d`, and chaining walks any two well-scoped depths
(`whnfCore_depth_inv` and friends).
-/

namespace Setlec

open Expr

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

@[local simp]
private theorem map_error {α β : Type} (σ : α → β) (e : CheckError) :
    (Except.error e : CheckM α).map σ = .error e := rfl

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
private theorem shiftFrom_fvar (p idx : Nat) (n : Name) (ty : Expr) :
    shiftFrom p (.fvar idx n ty) =
      .fvar (shiftIdx p idx) n (shiftTy p idx ty) := by
  by_cases h : p ≤ idx <;>
    simp [shiftFrom, shiftIdx, shiftTy, h, ge_iff_le]

private theorem shiftIdx_beq (p i j : Nat) :
    (shiftIdx p i == shiftIdx p j) = (i == j) := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [beq_iff_eq, beq_iff_eq]
  simp only [shiftIdx]
  by_cases hi : p ≤ i <;> by_cases hj : p ≤ j <;>
    simp only [hi, hj, if_true, if_false] <;> omega

/-- Shifting a freshly opened `fvar` at depth `d ≥ p`. -/
private theorem shiftFrom_fvar_ge {p d : Nat} (h : p ≤ d) (n : Name)
    (ty : Expr) :
    shiftFrom p (.fvar d n ty) = .fvar (d + 1) n (shiftFrom p ty) := by
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

/-- `getD` with the `bvar 0` default preserves well-scopedness. -/
private theorem WScoped_getD {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x (List.mem_cons_self ..)
    | succ n =>
      simpa [List.getD] using
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- `isCtorApp` only reads head constants, which shifting preserves. -/
private theorem isCtorApp_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    isCtorApp env (shiftFrom p e) = isCtorApp env e := by
  unfold isCtorApp
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- `isUnitLikeTy` only reads a head constant, which shifting
preserves. -/
private theorem isUnitLikeTy_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    isUnitLikeTy env (shiftFrom p e) = isUnitLikeTy env e := by
  cases e <;> try rfl
  case fvar => rw [shiftFrom_fvar]; simp [isUnitLikeTy]

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
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ => rfl
  | .fvar idx nn ty => simp [litToCtorIfNat, shiftFrom_fvar]

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
        obtain ⟨-, -, -, -, hvalwf, -⟩ := henv _ (find?_mem hf)
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
    case forallE n ty body mb =>
      show piResidual ((shiftFrom p body).instantiate1 (shiftFrom p a))
        (as.map (shiftFrom p)) = _
      rw [← shiftFrom_instantiate1_gen]
      exact piResidual_shiftFrom as _

/-! ## The bisimulation claims -/

/-- `whnfCore` commutes with the fvar shift. -/
def WhnfCoreShift (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    whnfCore env fuel (d + 1) (shiftFrom p e) =
      (whnfCore env fuel d e).map (shiftFrom p)

/-- The `whnf` reduction loop commutes with the fvar shift. -/
def WhnfShift (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    whnf env fuel (d + 1) (shiftFrom p e) =
      (whnf env fuel d e).map (shiftFrom p)

/-- `inferTypeCore` commutes with the fvar shift. -/
def InferShift (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    inferTypeCore env fuel (d + 1) (shiftFrom p e) =
      (inferTypeCore env fuel d e).map (shiftFrom p)

/-- `isDefEqCore` is invariant under the fvar shift. -/
def DefEqShift (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {a b : Expr}, WScoped d a → WScoped d b →
    isDefEqCore env fuel (d + 1) (shiftFrom p a) (shiftFrom p b) =
      isDefEqCore env fuel d a b

/-- `annotateCore` commutes with the fvar shift. -/
def AnnotShift (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    annotateCore env fuel (d + 1) (shiftFrom p e) =
      (annotateCore env fuel d e).map (shiftFrom p)

/-- All entry-point bisimulation claims at one fuel. -/
structure ShiftClaims (env : Env) (fuel : Nat) : Prop where
  whnfCore : WhnfCoreShift env fuel
  whnf : WhnfShift env fuel
  infer : InferShift env fuel
  defeq : DefEqShift env fuel
  annotate : AnnotShift env fuel

/-! ## Helper bodies at the same fuel

Every record-parameterized helper commutes with the shift, given the
entry-point claims at the same fuel (the helpers only call the record's
entry points; the three list helpers and `projFieldDom` recurse
structurally). -/

section Helpers

variable {env : Env} {fuel : Nat}

private theorem ensureSort_shift (_henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    ensureSort (pureFns env fuel) env (d + 1) (shiftFrom p e) =
      ensureSort (pureFns env fuel) env d e := by
  simp only [ensureSort]
  refine bind_congr _ (ih.whnf hpd hw) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem reduceNat_shift (_henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    reduceNat (pureFns env fuel) env (d + 1) (shiftFrom p e) =
      (reduceNat (pureFns env fuel) env d e).map
        (Option.map (shiftFrom p)) := by
  match e with
  | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    first
    | rfl
    | (simp only [shiftFrom_fvar]; rfl)
  | .app f a =>
    have hwfa : WScoped d f ∧ WScoped d a := by simpa only [WScoped] using hw
    match f with
    | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
    | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      first
      | rfl
      | (simp only [shiftFrom_app, shiftFrom_fvar]; rfl)
    | .const c us =>
      match us with
      | _ :: _ => rfl
      | [] =>
        show reduceNat _ env (d + 1) (.app (.const c []) (shiftFrom p a)) = _
        simp only [reduceNat]
        refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
        · refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
          intro w _
          rw [rawNatLit?_shiftFrom]
          cases rawNatLit? w <;> rfl
        · refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
          · refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
            intro w _
            rw [rawNatLit?_shiftFrom]
            cases rawNatLit? w with
            | none => rfl
            | some n =>
              dsimp only
              cases hres : natOpResult c n 0 with
              | none => rfl
              | some r =>
                rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                  rfl
          · refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
            intro w _
            rw [rawNatLit?_shiftFrom]
            cases rawNatLit? w <;> rfl
    | .app g b =>
      have hwgb : WScoped d g ∧ WScoped d b := by
        simpa only [WScoped] using hwfa.1
      match g with
      | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
      | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .app _ _ =>
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
          · refine bind_rel _ _ (ih.whnf hpd hwgb.2) ?_
            intro w₁ _
            refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
            intro w₂ _
            rw [rawNatLit?_shiftFrom, rawNatLit?_shiftFrom]
            cases rawNatLit? w₁ with
            | none => cases rawNatLit? w₂ <;> rfl
            | some n₁ =>
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
            refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
            intro w₂ _
            rw [rawNatLit?_shiftFrom, rawNatLit?_shiftFrom]
            cases rawNatLit? w₁ with
            | none => cases rawNatLit? w₂ <;> rfl
            | some n₁ => cases rawNatLit? w₂ <;> rfl

private theorem iotaCerts_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {args : List Expr} {ty : Expr}, WScoped d ty →
      (∀ x ∈ args, WScoped d x) →
      iotaCerts (pureFns env fuel) env (d + 1) (shiftFrom p ty)
          (args.map (shiftFrom p)) =
        iotaCerts (pureFns env fuel) env d ty args := by
  intro args
  induction args with
  | nil => intro ty _ _; rfl
  | cons arg rest ihrest =>
    intro ty hwty hwargs
    have hwarg : WScoped d arg := hwargs arg (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ rest, WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    match ty with
    | .forallE n ty' body mb =>
      have hwty' : WScoped d ty' ∧ WScoped d body := by
        simpa only [WScoped] using hwty
      show ((do
          let ta ← (pureFns env fuel).infer (d + 1) (shiftFrom p arg)
          if ← (pureFns env fuel).defeq (d + 1) ta (shiftFrom p ty') then
            iotaCerts (pureFns env fuel) env (d + 1)
              ((shiftFrom p body).instantiate1 (shiftFrom p arg))
              (rest.map (shiftFrom p))
          else pure false : CheckM Bool)) = _
      refine bind_congr _ (ih.infer hpd hwarg) ?_
      intro ta hta
      refine bind_congr_eq
        (ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hwarg)
          hwty'.1) ?_
      intro bb _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have h := ihrest (WScoped.instantiate1_gen hwarg 0 hwty'.2) hwrest
      rwa [shiftFrom_instantiate1_gen] at h
    | .bvar i => rfl
    | .fvar idx n' ty'' => rw [shiftFrom_fvar]; rfl
    | .sort u => rfl
    | .const n' us => rfl
    | .app f a => rfl
    | .lam n' ty'' body' m' => rfl
    | .letE n' ty'' v' b' => rfl
    | .lit l => rfl
    | .proj sp i' e' => rfl

private theorem defEqList_shift (_henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {as bs : List Expr}, (∀ x ∈ as, WScoped d x) →
      (∀ x ∈ bs, WScoped d x) →
      defEqList (pureFns env fuel) env (d + 1) (as.map (shiftFrom p))
          (bs.map (shiftFrom p)) =
        defEqList (pureFns env fuel) env d as bs := by
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
          if ← (pureFns env fuel).defeq (d + 1) (shiftFrom p a)
              (shiftFrom p b) then
            defEqList (pureFns env fuel) env (d + 1)
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
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    defeqSpine (pureFns env fuel) env (d + 1) (shiftFrom p a)
      (shiftFrom p b) = defeqSpine (pureFns env fuel) env d a b := by
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
      exact defEqList_shift _henv ih hpd hwa.getAppArgs hwb.getAppArgs
    | false => rfl

private theorem proofIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    proofIrrel (pureFns env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      proofIrrel (pureFns env fuel) env d a b := by
  simp only [proofIrrel]
  refine bind_congr _ (ih.infer hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeCore_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.whnf hpd hwta) ?_
  intro wta _
  rw [isUnitLikeTy_shiftFrom]
  refine ite_congr' (fun _ => ?_) (fun _ => ?_)
  · refine bind_congr _ (ih.infer hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeCore_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.whnf hpd hwtb) ?_
    intro wtb _
    rw [isUnitLikeTy_shiftFrom]
  · refine bind_congr _ (ih.infer hpd hwta) ?_
    intro tta htta
    have hwtta : WScoped d tta := inferTypeCore_WScoped henv fuel htta hwta
    refine bind_congr _ (ih.whnf hpd hwtta) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]
    case sort u =>
    refine bind_congr_eq rfl ?_
    intro okA _
    refine bind_congr _ (ih.infer hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeCore_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.infer hpd hwtb) ?_
    intro ttb httb
    have hwttb : WScoped d ttb := inferTypeCore_WScoped henv fuel httb hwtb
    refine bind_congr _ (ih.whnf hpd hwttb) ?_
    intro w' _
    cases w' <;> try rfl
    case fvar => rw [shiftFrom_fvar]

private theorem pairEtaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    pairEtaCert (pureFns env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      pairEtaCert (pureFns env fuel) env d a b := by
  cases a <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
  case app f₁ s₂ =>
  cases f₁ <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
  case app f₂ s₁ =>
  cases f₂ <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
  case app f₃ pβ =>
  cases f₃ <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
  case app f₄ pα =>
  cases f₄ <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
  case const c us =>
  simp only [WScoped] at hwa
  obtain ⟨⟨⟨⟨-, hwpα⟩, hwpβ⟩, hws₁⟩, hws₂⟩ := hwa
  simp only [shiftFrom, pairEtaCert]
  cases hfc : env.find? c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case ctorInfo cv nP nF =>
    match nP, nF with
    | 0, _ => rfl
    | 1, _ => rfl
    | _ + 3, _ => rfl
    | 2, 0 => rfl
    | 2, 1 => rfl
    | 2, _ + 3 => rfl
    | 2, 2 =>
    refine bind_congr _ (ih.infer hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeCore_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.whnf hpd hwtb) ?_
    intro wtb hwtb'
    cases wtb <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
    case app g₁ B =>
    cases g₁ <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
    case app g₂ A =>
    cases g₂ <;> try (first | rfl | (simp only [shiftFrom_app, shiftFrom_fvar]; first | done | rfl))
    case const c' us' =>
    simp only [shiftFrom]
    cases hfc' : env.find? c' with
    | none => rfl
    | some ci' =>
      cases ci' <;> try rfl
      case indInfo cvI capsI =>
      cases hfr : env.find? (c'.str "rec") with
      | none => rfl
      | some cir =>
        cases cir <;> try rfl
        case recInfo cvr rmI rrP rrules =>
        match rrules with
        | [] => rfl
        | _ :: _ :: _ => rfl
        | [rr] =>
        dsimp only
        refine ite_congr' (fun _ => ?_) (fun _ => rfl)
        refine bind_congr_eq rfl ?_
        intro okl _
        refine ite_congr' (fun _ => ?_) (fun _ => rfl)
        refine bind_congr_eq
          (ih.defeq hpd hws₁
            (show WScoped d (Expr.proj c' 0 b) by
              simpa only [WScoped] using hwb)) ?_
        intro bb _
        refine ite_congr' (fun _ => ?_) (fun _ => rfl)
        exact ih.defeq hpd hws₂
          (show WScoped d (Expr.proj c' 1 b) by
            simpa only [WScoped] using hwb)

private theorem structEtaProjCerts_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) (T : Name)
    (us' : List Level) {targs : List Expr} {b : Expr} (lpsT : List Name) :
    ∀ (idxs : List Nat), (∀ x ∈ targs, WScoped d x) → WScoped d b →
      structEtaProjCerts (pureFns env fuel) env (d + 1) T us'
          (targs.map (shiftFrom p)) (shiftFrom p b) lpsT idxs =
        structEtaProjCerts (pureFns env fuel) env d T us' targs b lpsT
          idxs := by
  intro idxs
  induction idxs with
  | nil => intro _ _; rfl
  | cons i rest ihrest =>
    intro hwtargs hwb
    show ((match env.find? (projFnName T i) with
      | some (.recInfo cvp _ _ _) =>
        if cvp.levelParams = lpsT ∧
            (cvp.type.stripPis ((targs.map (shiftFrom p)).length + 1)).isSome
              = true then do
          if ← iotaCerts (pureFns env fuel) env (d + 1)
              (cvp.type.instantiateLevelParams cvp.levelParams us')
              (targs.map (shiftFrom p) ++ [shiftFrom p b]) then
            structEtaProjCerts (pureFns env fuel) env (d + 1) T us'
              (targs.map (shiftFrom p)) (shiftFrom p b) lpsT rest
          else pure false
        else pure false
      | _ => pure false : CheckM Bool)) =
      ((match env.find? (projFnName T i) with
      | some (.recInfo cvp _ _ _) =>
        if cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (targs.length + 1)).isSome = true then do
          if ← iotaCerts (pureFns env fuel) env d
              (cvp.type.instantiateLevelParams cvp.levelParams us')
              (targs ++ [b]) then
            structEtaProjCerts (pureFns env fuel) env d T us' targs b
              lpsT rest
          else pure false
        else pure false
      | _ => pure false : CheckM Bool))
    cases hf : env.find? (projFnName T i) with
    | none => rfl
    | some ci =>
      cases ci <;> try rfl
      case recInfo cvp mI rP rules =>
      rw [List.length_map]
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have htel : (cvp.type.instantiateLevelParams cvp.levelParams
          us').hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1
      have h := iotaCerts_shift henv ih hpd
        (ty := cvp.type.instantiateLevelParams cvp.levelParams us')
        (WScoped.of_not_hasFvar htel) (args := targs ++ [b]) (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hwtargs x hx
          · rw [List.mem_singleton.mp hx]; exact hwb)
      rw [shiftFrom_eq_self_of_not_hasFvar htel, List.map_append] at h
      simp only [List.map] at h
      refine bind_congr_eq h ?_
      intro bb _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      exact ihrest hwtargs hwb

private theorem structEtaCertWith_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b wtb : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) (hwwtb : WScoped d wtb) :
    structEtaCertWith (pureFns env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) (shiftFrom p wtb) =
      structEtaCertWith (pureFns env fuel) env d a b wtb := by
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
      have htel : (cvT.type.instantiateLevelParams cvT.levelParams
          us').hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hfT)).1
      have h1 := iotaCerts_shift henv ih hpd
        (ty := cvT.type.instantiateLevelParams cvT.levelParams us')
        (WScoped.of_not_hasFvar htel)
        (args := wtb.getAppArgs) (fun x hx => hwwtb.getAppArgs x hx)
      rw [shiftFrom_eq_self_of_not_hasFvar htel] at h1
      refine bind_congr_eq h1 ?_
      intro b₁ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      refine bind_congr_eq
        (structEtaProjCerts_shift henv ih hpd T us' cvT.levelParams
          (List.range cnF)
          (fun x hx => hwwtb.getAppArgs x hx) hwb) ?_
      intro b₂ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have h2 := defEqList_shift henv ih hpd (as := a.getAppArgs.take cnP)
        (bs := wtb.getAppArgs)
        (fun x hx => hwa.getAppArgs x (List.mem_of_mem_take hx))
        (fun x hx => hwwtb.getAppArgs x hx)
      rw [List.map_take] at h2
      refine bind_congr_eq h2 ?_
      intro b₃ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have hlist : (List.range cnF).map (fun i =>
          Expr.mkAppN (.const (projFnName T i) us')
            (List.map (shiftFrom p) wtb.getAppArgs ++ [shiftFrom p b])) =
          List.map (shiftFrom p) ((List.range cnF).map (fun i =>
            Expr.mkAppN (.const (projFnName T i) us')
              (wtb.getAppArgs ++ [b]))) := by
        rw [List.map_map]
        refine List.map_congr_left fun i _ => ?_
        rw [Function.comp_apply, shiftFrom_mkAppN, List.map_append]
        rfl
      have h3 := defEqList_shift henv ih hpd (as := a.getAppArgs.drop cnP)
        (bs := (List.range cnF).map (fun i =>
          Expr.mkAppN (.const (projFnName T i) us') (wtb.getAppArgs ++ [b])))
        (fun x hx => hwa.getAppArgs x (List.mem_of_mem_drop hx))
        (fun x hx => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
          refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hwwtb.getAppArgs y hy
          · rw [List.mem_singleton.mp hy]; exact hwb)
      rw [List.map_drop, ← hlist] at h3
      exact h3

private theorem structEtaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    structEtaCert (pureFns env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      structEtaCert (pureFns env fuel) env d a b := by
  simp only [structEtaCert]
  refine bind_congr _ (ih.infer hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeCore_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.whnf hpd hwtb) ?_
  intro wtb hwtb'
  exact structEtaCertWith_shift henv ih hpd hwa hwb
    (whnf_WScoped henv fuel hwtb' hwtb)

private theorem structUnitCert_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    structUnitCert (pureFns env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      structUnitCert (pureFns env fuel) env d a b := by
  simp only [structUnitCert]
  refine bind_congr _ (ih.infer hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeCore_WScoped henv fuel hta hwa
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
    refine bind_congr _ (ih.infer hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeCore_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.whnf hpd hwtb) ?_
    intro wtb hwtb'
    refine bind_congr_eq
      (ih.defeq hpd hwwta (whnf_WScoped henv fuel hwtb' hwtb)) ?_
    intro bb _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have h := iotaCerts_shift henv ih hpd
      (ty := cvT.type.instantiateLevelParams cvT.levelParams us')
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1))
      (args := wta.getAppArgs) (fun x hx => hwwta.getAppArgs x hx)
    rw [shiftFrom_eq_self_of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]
      exact (henv _ (find?_mem hf)).1)] at h
    exact h

private theorem etaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) (n₁ : Name)
    {ty₁ body₁ : Expr} (m₁ : BinderMeta) {b : Expr}
    (hwty₁ : WScoped d ty₁) (hwbody₁ : WScoped d body₁)
    (hwb : WScoped d b) :
    etaCert (pureFns env fuel) env (d + 1) n₁ (shiftFrom p ty₁)
        (shiftFrom p body₁) m₁ (shiftFrom p b) =
      etaCert (pureFns env fuel) env d n₁ ty₁ body₁ m₁ b := by
  simp only [etaCert]
  refine bind_congr _ (ih.infer hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeCore_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.whnf hpd hwtb) ?_
  intro wtb hwtb'
  cases wtb <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case forallE n₂ ty₂ body₂ m₂ =>
    have hwPi : WScoped d (Expr.forallE n₂ ty₂ body₂ m₂) :=
      whnf_WScoped henv fuel hwtb' hwtb
    simp only [WScoped] at hwPi
    simp only [shiftFrom]
    cases m₁.cod <;> cases m₂.cod <;> try rfl
    case some.some v₁ v₂ =>
    refine bind_congr_eq rfl ?_
    intro okv _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    refine bind_congr_eq (ih.defeq hpd hwPi.1 hwty₁) ?_
    intro bb _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have h := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 (n := n₁) hwty₁ 0 hwbody₁)
      (show WScoped (d + 1) (Expr.app b (.fvar d n₁ ty₁)) by
        simp only [WScoped]
        exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwty₁⟩)
    rwa [shiftFrom_instantiate1 hpd, show
        shiftFrom p (Expr.app b (.fvar d n₁ ty₁)) =
          Expr.app (shiftFrom p b) (.fvar (d + 1) n₁ (shiftFrom p ty₁))
      from by rw [shiftFrom_app, shiftFrom_fvar_ge hpd]] at h

private theorem stuckIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    stuckIrrel (pureFns env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      stuckIrrel (pureFns env fuel) env d a b := by
  simp only [stuckIrrel]
  refine bind_congr_eq (pairEtaCert_shift henv ih hpd hwa hwb) ?_
  intro b₁ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr_eq (pairEtaCert_shift henv ih hpd hwb hwa) ?_
  intro b₂ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
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

private theorem projCert_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {e₂ : Expr}
    (hwe₂ : WScoped d e₂) (i : Nat) (fieldLvl structLvl : Level)
    (nP : Nat) :
    projCert (pureFns env fuel) env (d + 1) (shiftFrom p e₂) i
        fieldLvl structLvl nP =
      projCert (pureFns env fuel) env d e₂ i fieldLvl structLvl nP := by
  simp only [projCert]
  rw [getAppArgs_shiftFrom, getD_map_shiftFrom]
  have hwarg : WScoped d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) :=
    WScoped_getD (fun x hx => hwe₂.getAppArgs x hx) _
  refine bind_congr _ (ih.infer hpd hwarg) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeCore_WScoped henv fuel hta hwarg
  refine bind_congr _ (ih.infer hpd hwta) ?_
  intro tta htta
  have hwtta : WScoped d tta := inferTypeCore_WScoped henv fuel htta hwta
  refine bind_congr _ (ih.whnf hpd hwtta) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case sort uT =>
  refine bind_congr_eq rfl ?_
  intro okT _
  refine bind_congr _ (ih.infer hpd hwe₂) ?_
  intro te hte
  have hwte : WScoped d te := inferTypeCore_WScoped henv fuel hte hwe₂
  refine bind_congr _ (ih.infer hpd hwte) ?_
  intro tte htte
  have hwtte : WScoped d tte := inferTypeCore_WScoped henv fuel htte hwte
  refine bind_congr _ (ih.whnf hpd hwtte) ?_
  intro w₂ _
  cases w₂ <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem majorToCtor_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) (recName : Name)
    (rules : List RecRule) {major : Expr} (hwmaj : WScoped d major) :
    majorToCtor (pureFns env fuel) env (d + 1) recName rules
        (shiftFrom p major) =
      (majorToCtor (pureFns env fuel) env d recName rules major).map
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
            refine bind_rel _ _ (ih.infer hpd hwmaj) ?_
            intro tmaj₀ htmaj₀
            have hwtmaj₀ : WScoped d tmaj₀ :=
              inferTypeCore_WScoped henv fuel htmaj₀ hwmaj
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
            rw [getAppArgs_shiftFrom]
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
            refine bind_rel_eq _ (proofIrrel_shift henv ih hpd hwfab hwmaj) ?_
            intro bb _
            exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
          · -- structure-eta rescue (or no rescue)
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel _ _ (ih.infer hpd hwmaj) ?_
            intro tmaj₀ htmaj₀
            have hwtmaj₀ : WScoped d tmaj₀ :=
              inferTypeCore_WScoped henv fuel htmaj₀ hwmaj
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
            have hspine : (List.range caps.etaFields).map (fun j =>
                Expr.mkAppN (.const (projFnName T j) ust)
                  (List.map (shiftFrom p) tmaj.getAppArgs ++
                    [shiftFrom p major])) =
                List.map (shiftFrom p) ((List.range caps.etaFields).map
                  (fun j => Expr.mkAppN (.const (projFnName T j) ust)
                    (tmaj.getAppArgs ++ [major]))) := by
              rw [List.map_map]
              refine List.map_congr_left fun j _ => ?_
              rw [Function.comp_apply, shiftFrom_mkAppN, List.map_append]
              rfl
            have hfab : Expr.mkAppN (Expr.const caps.etaCtor ust)
                (List.map (shiftFrom p) tmaj.getAppArgs ++
                  (List.range caps.etaFields).map fun j =>
                    Expr.mkAppN (.const (projFnName T j) ust)
                      (List.map (shiftFrom p) tmaj.getAppArgs ++
                        [shiftFrom p major])) =
                shiftFrom p (Expr.mkAppN (.const caps.etaCtor ust)
                  (tmaj.getAppArgs ++
                    (List.range caps.etaFields).map fun j =>
                      Expr.mkAppN (.const (projFnName T j) ust)
                        (tmaj.getAppArgs ++ [major]))) := by
              rw [shiftFrom_mkAppN, List.map_append, ← hspine]
              rfl
            rw [hfab]
            have hwfab : WScoped d (Expr.mkAppN (.const caps.etaCtor ust)
                (tmaj.getAppArgs ++
                  (List.range caps.etaFields).map fun j =>
                    Expr.mkAppN (.const (projFnName T j) ust)
                      (tmaj.getAppArgs ++ [major]))) := by
              refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hwtmaj.getAppArgs x hx
              · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
                intro y hy
                rcases List.mem_append.mp hy with hy | hy
                · exact hwtmaj.getAppArgs y hy
                · rw [List.mem_singleton.mp hy]; exact hwmaj
            rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
              fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel_eq _
              (structEtaCertWith_shift henv ih hpd hwfab hwmaj hwtmaj) ?_
            intro bb _
            exact ite_rel _ (fun _ => rfl) (fun _ => rfl)

/-- The scoping of an iota reduct (the `iotaRec` slice of the
`whnfPres_WScoped` proof, factored for the bisimulation). -/
private theorem iotaRec_WScoped (henv : EnvWF env)
    {d : Nat} {e e'' : Expr}
    (h : iotaRec (pureFns env fuel) env d e = .ok (some e''))
    (hw : WScoped d e) : WScoped d e'' := by
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj,
    cvj, cnP, cnF, r, -, -, -, -, -, hfn, hfc, hlen, hmaj, hlit, hsub,
    hmfn, hfj,
    hrule,
    hml, har1, har2, -, hlev, hpeq, hcerts, hmcerts, -, -, -, -, rfl⟩ :=
    iotaRec_inv h
  have hargs : ∀ x, x ∈ e.getAppArgs → WScoped d x :=
    fun x hx => hw.getAppArgs x hx
  have hrhs : WScoped d
      (r.rhs.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨-, -, -, -, -, hrules⟩ := henv _ (find?_mem hfc)
    obtain ⟨hrf, -, -, -⟩ := hrules cv mI rP rules rfl r
      (List.mem_of_find?_eq_some hrule)
    exact WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hrf)
  have hmaj0w : WScoped d major₀ := whnf_WScoped henv fuel hmaj
    (hargs _ (getD_mem (by omega)))
  have hmaj1w : WScoped d major₁ := by
    rcases litMajorToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
    · exact litToCtorIfNat_WScoped hmaj0w
    · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d)
  have hmajw : WScoped d major := by
    rcases majorToCtor_inv hsub with rfl | ⟨hwsc, -, -, -⟩
    · exact hmaj1w
    · exact WScoped.of_wscopedB hwsc
  refine Expr.WScoped.mkAppN hrhs ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hargs _ (List.mem_of_mem_take hx)
  · exact hmajw.getAppArgs _ (List.mem_of_mem_drop hx)

/-- Shifting commutes with the literal-major conversion (the string
branch reduces a closed term, invariant under shifting). -/
private theorem litMajorToCtor_shift (_henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {e : Expr}, WScoped d e →
    litMajorToCtor (pureFns env fuel) env (d + 1) (shiftFrom p e) =
      (litMajorToCtor (pureFns env fuel) env d e).map (shiftFrom p)
  | .lit (.strVal s), _ => by
    show litMajorToCtor (pureFns env fuel) env (d + 1) (.lit (.strVal s)) = _
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
  | .fvar idx n ty, _ => by
    rw [shiftFrom_fvar]
    show pure (litToCtorIfNat env (.fvar (shiftIdx p idx) n (shiftTy p idx ty))) = _
    rw [show (litToCtorIfNat env (.fvar (shiftIdx p idx) n (shiftTy p idx ty))) =
      .fvar (shiftIdx p idx) n (shiftTy p idx ty) from rfl]
    rw [show (litMajorToCtor (pureFns env fuel) env d (.fvar idx n ty)) =
      pure (.fvar idx n ty) from rfl]
    rw [show (Except.map (shiftFrom p) (pure (Expr.fvar idx n ty)) :
        CheckM Expr) = pure (shiftFrom p (.fvar idx n ty)) from rfl]
    rw [shiftFrom_fvar]
  | .app f a, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.app f a))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .lam n ty body bi, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.lam n ty body bi))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .forallE n ty body bi, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.forallE n ty body bi))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .letE n ty v body, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.letE n ty v body))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .proj sn i pe, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.proj sn i pe))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl

private theorem iotaRec_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hwe : WScoped d e) :
    iotaRec (pureFns env fuel) env (d + 1) (shiftFrom p e) =
      (iotaRec (pureFns env fuel) env d e).map
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
      WScoped_getD (fun x hx => hwe.getAppArgs x hx) _
    refine bind_rel _ _ (ih.whnf hpd hwgd) ?_
    intro major₀ hmaj₀
    have hwmaj₀ : WScoped d major₀ := whnf_WScoped henv fuel hmaj₀ hwgd
    refine bind_rel _ _ (litMajorToCtor_shift henv ih hpd hwmaj₀) ?_
    intro major₁ hmaj₁
    have hwmaj₁ : WScoped d major₁ := by
      rcases litMajorToCtorP_inv hmaj₁ with rfl | ⟨s, -, -, hred⟩
      · exact litToCtorIfNat_WScoped hwmaj₀
      · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d)
    refine bind_rel _ _
      (majorToCtor_shift henv ih hpd c rules hwmaj₁) ?_
    intro major hmaj
    have hwmaj : WScoped d major := by
      rcases majorToCtor_inv hmaj with rfl | ⟨hwsc, -, -, -⟩
      · exact hwmaj₁
      · exact WScoped.of_wscopedB hwsc
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
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        refine bind_rel_eq _ rfl ?_
        intro okl _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have h1 := defEqList_shift henv ih hpd
          (as := major.getAppArgs.take rl.ctorParams)
          (bs := e.getAppArgs.take rl.ctorParams)
          (fun x hx => hwmaj.getAppArgs x (List.mem_of_mem_take hx))
          (fun x hx => hwe.getAppArgs x (List.mem_of_mem_take hx))
        simp only [List.map_take] at h1
        refine bind_rel_eq _ h1 ?_
        intro b₁ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have htel₁ : (cv.type.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]
          exact (henv _ (find?_mem hfc)).1
        have h2 := iotaCerts_shift henv ih hpd
          (ty := cv.type.instantiateLevelParams cv.levelParams us)
          (WScoped.of_not_hasFvar htel₁)
          (args := e.getAppArgs.take mI ++ [major])
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hwe.getAppArgs x (List.mem_of_mem_take hx)
            · rw [List.mem_singleton.mp hx]; exact hwmaj)
        rw [shiftFrom_eq_self_of_not_hasFvar htel₁] at h2
        simp only [List.map_append, List.map_take, List.map] at h2
        refine bind_rel_eq _ h2 ?_
        intro b₂ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have htel₂ : (cvj.type.instantiateLevelParams cvj.levelParams
            usj).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]
          exact (henv _ (find?_mem hfj)).1
        have h3 := iotaCerts_shift henv ih hpd
          (ty := cvj.type.instantiateLevelParams cvj.levelParams usj)
          (WScoped.of_not_hasFvar htel₂)
          (args := major.getAppArgs)
          (fun x hx => hwmaj.getAppArgs x hx)
        rw [shiftFrom_eq_self_of_not_hasFvar htel₂] at h3
        refine bind_rel_eq _ h3 ?_
        intro b₃ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        -- index-tuple check: closed telescope peeled along shifted spines
        have hres := piResidual_shiftFrom (p := p) major.getAppArgs
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
        rw [shiftFrom_eq_self_of_not_hasFvar htel₂] at hres
        rw [hres]
        cases hstrip : (cvj.type.instantiateLevelParams cvj.levelParams
            usj).stripPis (rl.ctorParams + rl.nfields) with
        | none =>
          cases hresid : piResidual (cvj.type.instantiateLevelParams
              cvj.levelParams usj) major.getAppArgs <;> rfl
        | some sb =>
          obtain ⟨sbs, sbody⟩ := sb
          cases hresid : piResidual (cvj.type.instantiateLevelParams
              cvj.levelParams usj) major.getAppArgs with
          | none => rfl
          | some residual =>
            simp only [Option.map_some]
            cases hcb : sbody.getAppFn <;> try rfl
            case const c₀ us₀ =>
            have hwres : WScoped d residual :=
              piResidual_WScoped hresid (WScoped.of_not_hasFvar htel₂)
                (fun x hx => hwmaj.getAppArgs x hx)
            have h4 := defEqList_shift henv ih hpd
              (as := residual.getAppArgs.drop rl.ctorParams)
              (bs := (e.getAppArgs.take mI).drop rP)
              (fun x hx => hwres.getAppArgs x (List.mem_of_mem_drop hx))
              (fun x hx => hwe.getAppArgs x
                (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
            simp only [List.map_drop, List.map_take] at h4
            rw [← getAppArgs_shiftFrom] at h4
            refine bind_rel_eq _ h4 ?_
            intro b₄ _
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            have hrhs : (rl.rhs.instantiateLevelParams cv.levelParams
                us).hasFvar = false := by
              obtain ⟨-, -, -, -, -, hrules⟩ := henv _ (find?_mem hfc)
              obtain ⟨hrf, -, -, -⟩ := hrules cv mI rP rules rfl rl
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

private theorem isPropType_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) {ty : Expr}
    (hwty : WScoped d ty) :
    isPropType (pureFns env fuel) env (d + 1) (shiftFrom p ty) =
      isPropType (pureFns env fuel) env d ty := by
  simp only [isPropType]
  refine bind_congr _ (ih.annotate hpd hwty) ?_
  intro ty' hty'
  have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty' hwty
  refine bind_congr _ (ih.infer hpd hwty') ?_
  intro t ht
  refine bind_congr_eq (ensureSort_shift henv ih hpd
    (inferTypeCore_WScoped henv fuel ht hwty')) ?_
  intro sk _
  rfl

private theorem projFieldDom_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d)
    (structProp : Bool) (sn : Name) {e' : Expr} (hwe' : WScoped d e') :
    ∀ (k j : Nat) {tel : Expr}, WScoped d tel →
      projFieldDom (pureFns env fuel) env (d + 1) structProp sn
          (shiftFrom p e') j k (shiftFrom p tel) =
        (projFieldDom (pureFns env fuel) env d structProp sn e' j k
          tel).map (shiftFrom p) := by
  intro k
  induction k with
  | zero =>
    intro j tel hwtel
    cases tel <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
  | succ k ihk =>
    intro j tel hwtel
    cases tel <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE n dom rest mb =>
    have hw' : WScoped d dom ∧ WScoped d rest := by
      simpa only [WScoped] using hwtel
    have hrec := ihk (j + 1)
      (tel := rest.instantiate1 (.proj sn j e'))
      (WScoped.instantiate1_gen (by simpa only [WScoped] using hwe') 0
        hw'.2)
    rw [shiftFrom_instantiate1_gen] at hrec
    simp only [shiftFrom, projFieldDom]
    rw [looseBVarsBounded_shiftFrom]
    refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
    · exact ihk (j + 1) hw'.2
    · refine ite_rel _ (fun _ => ?_) (fun _ => hrec)
      refine bind_rel_eq _ (isPropType_shift henv ih hpd hw'.1) ?_
      intro bb _
      cases bb with
      | true => exact hrec
      | false => rfl

private theorem projFieldDom_WScoped {d : Nat} {structProp : Bool}
    {sn : Name} {e' : Expr} (hwe' : WScoped d e') :
    ∀ (k j : Nat) {tel dom : Expr},
      projFieldDom (pureFns env fuel) env d structProp sn e' j k tel
        = .ok dom →
      WScoped d tel → WScoped d dom := by
  intro k
  induction k with
  | zero =>
    intro j tel dom h hwtel
    match tel, h with
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h
    | .app _ _, h | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h
    | .proj _ _ _, h => exact nomatch h
    | .forallE n ty rest mb, h =>
    have hw' : WScoped d ty ∧ WScoped d rest := by
      simpa only [WScoped] using hwtel
    simp only [projFieldDom, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw'.1
  | succ k ihk =>
    intro j tel dom h hwtel
    match tel, h with
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h
    | .app _ _, h | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h
    | .proj _ _ _, h => exact nomatch h
    | .forallE n ty rest mb, h =>
    have hw' : WScoped d ty ∧ WScoped d rest := by
      simpa only [WScoped] using hwtel
    have hwrec : WScoped d (rest.instantiate1 (.proj sn j e')) :=
      WScoped.instantiate1_gen (by simpa only [WScoped] using hwe') 0
        hw'.2
    simp only [projFieldDom] at h
    split at h
    · exact ihk (j + 1) h hw'.2
    · split at h
      · -- Prop-structure guard
        revert h
        cases hb : isPropType (pureFns env fuel) env d ty with
        | error err =>
          intro h
          exact nomatch h
        | ok bb =>
          intro h
          cases bb with
          | true => exact ihk (j + 1) h hwrec
          | false => exact nomatch h
      · exact ihk (j + 1) h hwrec

theorem instPis_WScoped {d : Nat} :
    ∀ {as : List Expr} {t res : Expr}, Expr.instPis t as = some res →
      WScoped d t → (∀ x ∈ as, WScoped d x) → WScoped d res
  | [], t, res, h, hw, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    exact h ▸ hw
  | a :: as, t, res, h, hw, has => by
    match t, h with
    | .forallE n ty body mb, h =>
      have hw' : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hw
      have h' : Expr.instPis (body.instantiate1 a) as = some res := h
      exact instPis_WScoped h'
        (WScoped.instantiate1_gen (has a (List.mem_cons_self ..)) 0 hw'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))

private theorem pisToLams_WScoped {d : Nat} :
    ∀ (k : Nat) {t body minor : Expr},
      Expr.pisToLams k t body = some minor →
      WScoped d t → WScoped d body → WScoped d minor
  | 0, t, body, minor, h, _, hwb => by
    simp only [Expr.pisToLams, Option.some.injEq] at h
    exact h ▸ hwb
  | k + 1, t, body, minor, h, hwt, hwb => by
    match t, h with
    | .forallE n ty rest mb, h =>
      have hw' : WScoped d ty ∧ WScoped d rest := by
        simpa only [WScoped] using hwt
      simp only [Expr.pisToLams] at h
      cases hin : Expr.pisToLams k rest body with
      | none => rw [hin] at h; exact nomatch h
      | some b' =>
        rw [hin] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [WScoped]
        exact ⟨hw'.1, pisToLams_WScoped k hin hw'.2 hwb⟩

private theorem annotateProjRec_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d)
    (entry : ProjEntry)
    (i : Nat) {te e' : Expr} (us : List Level)
    (hwte : WScoped d te) (hwe' : WScoped d e') :
    annotateProjRec (pureFns env fuel) env (d + 1) entry i
        (shiftFrom p te)
        (shiftFrom p e') us =
      (annotateProjRec (pureFns env fuel) env d entry i te e' us).map
        (shiftFrom p) := by
  simp only [annotateProjRec]
  split
  case h_2 => rfl
  case h_1 =>
  rename_i cvC cnP₂ cnF hf3
  simp only [getAppArgs_shiftFrom, List.length_map]
  refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
  have hcty : (cvC.type.instantiateLevelParams cvC.levelParams
      us).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact (henv _ (find?_mem hf3)).1
  have hip := instPis_shiftFrom (p := p) te.getAppArgs
    (cvC.type.instantiateLevelParams cvC.levelParams us)
  rw [shiftFrom_eq_self_of_not_hasFvar hcty] at hip
  rw [hip]
  cases htel : (cvC.type.instantiateLevelParams cvC.levelParams
      us).instPis te.getAppArgs with
  | none => rfl
  | some tel =>
    simp only [Option.map_some]
    have hwtel : WScoped d tel := instPis_WScoped htel
      (WScoped.of_not_hasFvar hcty)
      (fun x hx => hwte.getAppArgs x hx)
    refine bind_rel_eq _ (isPropType_shift henv ih hpd hwte) ?_
    intro structProp _
    refine bind_rel _ _
      (projFieldDom_shift henv ih hpd structProp entry.structName hwe'
        i 0 hwtel) ?_
    intro fi hfi
    have hwfi : WScoped d fi :=
      projFieldDom_WScoped hwe' i 0 hfi hwtel
    have hptl := pisToLams_shiftFrom (p := p) cnF tel
      (.bvar (cnF - 1 - i))
    simp only [shiftFrom] at hptl
    rw [hptl]
    cases hminor : Expr.pisToLams cnF tel (.bvar (cnF - 1 - i)) with
    | none => rfl
    | some minor =>
      simp only [Option.map_some]
      have hwminor : WScoped d minor :=
        pisToLams_WScoped cnF hminor hwtel (by simp [WScoped])
      refine bind_rel _ _ (ih.annotate hpd hwfi) ?_
      intro fi' hfi'
      have hwfi' : WScoped d fi' :=
        annotateCore_WScoped fuel fi hfi' hwfi
      refine bind_rel _ _ (ih.infer hpd hwfi') ?_
      intro tfi htfi
      refine bind_rel_eq _ (ensureSort_shift henv ih hpd
        (inferTypeCore_WScoped henv fuel htfi hwfi')) ?_
      intro sfi _
      have hraw : Expr.mkAppN
          (Expr.const (entry.structName.str "rec")
            ((if entry.recExtraLevel then [sfi]
              else []) ++ us))
          (te.getAppArgs.map (shiftFrom p) ++
            [.lam (.str .anonymous "t") (shiftFrom p te)
              (shiftFrom p fi) ⟨.default, none⟩,
             shiftFrom p minor, shiftFrom p e']) =
          shiftFrom p (Expr.mkAppN
            (.const (entry.structName.str "rec")
              ((if entry.recExtraLevel then [sfi]
                else []) ++ us))
            (te.getAppArgs ++
              [.lam (.str .anonymous "t") te fi ⟨.default, none⟩,
               minor, e'])) := by
        rw [shiftFrom_mkAppN, List.map_append]
        rfl
      rw [hraw]
      have hwraw : WScoped d (Expr.mkAppN
          (.const (entry.structName.str "rec")
            ((if entry.recExtraLevel then [sfi]
              else []) ++ us))
          (te.getAppArgs ++
            [.lam (.str .anonymous "t") te fi ⟨.default, none⟩,
             minor, e'])) := by
        refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwte.getAppArgs x hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · simp only [WScoped]
            exact ⟨hwte, hwfi⟩
          · exact hwminor
          · exact hwe'
      rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
        fvarLeaves_all_contains_shiftFrom hpd hwraw hwe']
      refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
      · refine bind_rel_eq _ rfl ?_
        intro ok _
        cases ok with
        | true =>
          refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
          refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
          exact ih.annotate hpd hwraw
        | false => rfl
      · refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        exact ih.annotate hpd hwraw

private theorem annotateProjElim_shift (henv : EnvWF env)
    (ih : ShiftClaims env fuel) {p d : Nat} (hpd : p ≤ d) (sn : Name)
    (i : Nat) {te e' : Expr} (hwte : WScoped d te) (hwe' : WScoped d e') :
    annotateProjElim (pureFns env fuel) env (d + 1) sn i (shiftFrom p te)
        (shiftFrom p e') =
      (annotateProjElim (pureFns env fuel) env d sn i te e').map
        (shiftFrom p) := by
  simp only [annotateProjElim]
  rw [getAppFn_shiftFrom]
  cases hfn : te.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const T us =>
  simp only [shiftFrom]
  refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
  cases hf : env.find? (projFnName T i) with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case projInfo entry =>
      dsimp only
      refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
      exact annotateProjRec_shift henv ih hpd entry i us hwte hwe'
    case recInfo cvp mI rP rules =>
    dsimp only
    simp only [getAppArgs_shiftFrom, List.length_map]
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    have hraw : Expr.mkAppN (Expr.const (projFnName T i) us)
        (te.getAppArgs.map (shiftFrom p) ++ [shiftFrom p e']) =
        shiftFrom p (Expr.mkAppN (.const (projFnName T i) us)
          (te.getAppArgs ++ [e'])) := by
      rw [shiftFrom_mkAppN, List.map_append]
      rfl
    rw [hraw]
    have hwraw : WScoped d (Expr.mkAppN (.const (projFnName T i) us)
        (te.getAppArgs ++ [e'])) := by
      refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hwte.getAppArgs x hx
      · rw [List.mem_singleton.mp hx]; exact hwe'
    rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
      fvarLeaves_all_contains_shiftFrom hpd hwraw hwe']
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    exact ih.annotate hpd hwraw

/-! ## The body step lemmas -/

private theorem whnfCore_step (henv : EnvWF env)
    (ih : ShiftClaims env fuel) : WhnfCoreShift env (fuel + 1) := by
  intro p d hpd e hw
  rw [whnfCore_succ, whnfCore_succ]
  match e with
  | .bvar i => rfl
  | .sort u => rfl
  | .fvar idx n ty =>
    rw [shiftFrom_fvar]
    simp only [whnfCoreBody, pure, Except.pure, map_ok, shiftFrom_fvar]
  | .forallE n ty body mb => rfl
  | .lam n ty body mb => rfl
  | .const n us => rfl
  | .lit l => rfl
  | .letE n ty v body => rfl
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [whnfCoreBody]
    refine bind_rel _ _ (ih.whnfCore hpd hw.1) ?_
    intro f' hf'
    have hwf' : WScoped d f' := whnfCore_WScoped henv fuel hf' hw.1
    have hiota : ∀ (f'' : Expr), WScoped d f'' →
        (iotaRec (pureFns env fuel) env (d + 1)
            (.app (shiftFrom p f'') (shiftFrom p a)) >>= fun o =>
          match o with
          | some e'' => (pureFns env fuel).whnfCore (d + 1) e''
          | none => pure (.app (shiftFrom p f'') (shiftFrom p a))) =
        ((iotaRec (pureFns env fuel) env d (.app f'' a) >>= fun o =>
          match o with
          | some e'' => (pureFns env fuel).whnfCore d e''
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
    | lam n₁ ty₁ body₁ m₁ =>
      simp only [WScoped] at hwf'
      dsimp only [shiftFrom]
      cases hc : m₁.cod with
      | none => rfl
      | some v =>
        dsimp only
        refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
        · have h := ih.whnfCore hpd
            (WScoped.instantiate1_gen hw.2 0 hwf'.2)
          rwa [shiftFrom_instantiate1_gen] at h
        · refine bind_rel _ _ (ih.infer hpd hw.2) ?_
          intro ta hta
          refine bind_rel_eq _
            (ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hw.2)
              hwf'.1) ?_
          intro bb _
          refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
          have h := ih.whnfCore hpd
            (WScoped.instantiate1_gen hw.2 0 hwf'.2)
          rwa [shiftFrom_instantiate1_gen] at h
    | bvar i => exact hiota _ hwf'
    | fvar idx n ty =>
      have h := hiota _ hwf'
      simp only [shiftFrom_fvar] at h ⊢
      exact h
    | sort u => exact hiota _ hwf'
    | const n' us => exact hiota _ hwf'
    | forallE n' ty' body' m' => exact hiota _ hwf'
    | letE n' ty' v' body' => exact hiota _ hwf'
    | lit l => exact hiota _ hwf'
    | proj s' i' e' => exact hiota _ hwf'
    | app f'' a'' => exact hiota _ hwf'
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show whnfCoreBody (pureFns env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (whnfCoreBody (pureFns env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [whnfCoreBody]
    refine bind_rel _ _ (ih.whnf hpd hw) ?_
    intro e₂ he₂
    have hwe₂ : WScoped d e₂ := whnf_WScoped henv fuel he₂ hw
    cases hfp : env.findProj? sn i with
    | none => rfl
    | some entry =>
      rw [getAppFn_shiftFrom]
      cases hfn : e₂.getAppFn <;> try rfl
      case fvar => rw [shiftFrom_fvar]; rfl
      case const c us₂ =>
      simp only [shiftFrom]
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      rw [getD_map_shiftFrom]
      have hwarg : WScoped d
          (e₂.getAppArgs.getD (entry.numParams + i) (.bvar 0)) :=
        WScoped_getD (fun x hx => hwe₂.getAppArgs x hx) _
      refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
      · exact ih.whnfCore hpd hwarg
      · refine bind_rel_eq _ (projCert_shift henv ih hpd hwe₂ i
          (Level.subst entry.levelParams us₂ entry.fieldSort)
          (Level.subst entry.levelParams us₂ entry.structSort)
          entry.numParams) ?_
        intro bb _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        exact ih.whnfCore hpd hwarg

private theorem whnf_step (henv : EnvWF env)
    (ih : ShiftClaims env fuel) : WhnfShift env (fuel + 1) := by
  intro p d hpd e hw
  rw [whnf_succ, whnf_succ]
  simp only [whnfBody]
  refine bind_rel _ _ (ih.whnfCore hpd hw) ?_
  intro e₁ he₁
  have hwe₁ : WScoped d e₁ := whnfCore_WScoped henv fuel he₁ hw
  refine bind_rel _ _ (reduceNat_shift henv ih hpd hwe₁) ?_
  intro o ho
  cases o with
  | some e₂ =>
    simp only [Option.map_some]
    have hwe₂ : WScoped d e₂ := by
      rcases reduceNat_inv ho with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ih.whnf hpd hwe₂
  | none =>
    rw [unfoldDefinition_shiftFrom henv]
    cases hu : unfoldDefinition env e₁ with
    | none => rfl
    | some e₂ =>
      simp only [Option.map_some]
      exact ih.whnf hpd (unfoldDefinition_WScoped henv hu hwe₁)

private theorem infer_step (henv : EnvWF env)
    (ih : ShiftClaims env fuel) : InferShift env (fuel + 1) := by
  intro p d hpd e hw
  rw [inferTypeCore_succ, inferTypeCore_succ]
  match e with
  | .bvar i => rfl
  | .letE n ty v body => rfl
  | .sort u => rfl
  | .lit (.natVal n) =>
    show inferBody (pureFns env fuel) env (d + 1) (.lit (.natVal n)) =
      (inferBody (pureFns env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [inferBody, viewM, Expr.view, pure_bind]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .lit (.strVal str) =>
    show inferBody (pureFns env fuel) env (d + 1) (.lit (.strVal str)) =
      (inferBody (pureFns env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [inferBody, viewM, Expr.view, pure_bind]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx n ty =>
    simp only [WScoped] at hw
    rw [shiftFrom_fvar]
    simp only [inferBody, viewM, Expr.view, pure_bind]
    rw [if_pos (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        if_pos hw.1]
    by_cases hp : p ≤ idx
    · simp [shiftTy, hp, pure, Except.pure]
    · simp only [shiftTy, if_neg hp, pure, Except.pure, map_ok]
      rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
  | .const n us =>
    show inferBody (pureFns env fuel) env (d + 1) (.const n us) =
      (inferBody (pureFns env fuel) env d (.const n us)).map (shiftFrom p)
    simp only [inferBody, viewM, Expr.view, pure_bind]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      have hty : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1
      simp only [pure, Except.pure, map_ok,
        shiftFrom_eq_self_of_not_hasFvar hty]
  | .forallE n ty body mb =>
    simp only [WScoped] at hw
    show inferBody (pureFns env fuel) env (d + 1)
        (.forallE n (shiftFrom p ty) (shiftFrom p body) mb) =
      (inferBody (pureFns env fuel) env d (.forallE n ty body mb)).map
        (shiftFrom p)
    simp only [inferBody, viewM, Expr.view, pure_bind]
    cases hc : mb.cod with
    | none => rfl
    | some v =>
      dsimp only
      refine bind_rel _ _ (ih.infer hpd hw.1) ?_
      intro tty htty
      refine bind_rel _ _
        (ih.whnf hpd (inferTypeCore_WScoped henv fuel htty hw.1)) ?_
      intro w _
      cases w <;> try rfl
      case fvar => rw [shiftFrom_fvar]; rfl
  | .lam n ty body mb =>
    simp only [WScoped] at hw
    show inferBody (pureFns env fuel) env (d + 1)
        (.lam n (shiftFrom p ty) (shiftFrom p body) mb) =
      (inferBody (pureFns env fuel) env d (.lam n ty body mb)).map
        (shiftFrom p)
    simp only [inferBody, viewM, Expr.view, pure_bind]
    cases hc : mb.cod with
    | none => rfl
    | some v =>
      dsimp only
      refine bind_rel _ _ (ih.infer hpd hw.1) ?_
      intro tty htty
      refine bind_rel _ _
        (ih.whnf hpd (inferTypeCore_WScoped henv fuel htty hw.1)) ?_
      intro w _
      cases w <;> try rfl
      case fvar => rw [shiftFrom_fvar]; rfl
      case sort u =>
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        WScoped.instantiate1 (n := n) hw.1 0 hw.2
      have hbody := ih.infer (p := p) (d := d + 1) (by omega) hwo
      rw [shiftFrom_instantiate1 hpd] at hbody
      refine bind_rel _ _ hbody ?_
      intro bt hbt
      have hwbt : WScoped (d + 1) bt :=
        inferTypeCore_WScoped henv fuel hbt hwo
      refine bind_rel _ _
        (ih.infer (p := p) (d := d + 1) (by omega) hwbt) ?_
      intro tbt htbt
      refine bind_rel _ _
        (ih.whnf (p := p) (d := d + 1) (by omega)
          (inferTypeCore_WScoped henv fuel htbt hwbt)) ?_
      intro w₂ _
      cases w₂ <;> try rfl
      case fvar => rw [shiftFrom_fvar]; rfl
      case sort v' =>
      refine bind_rel_eq _ rfl ?_
      intro okv _
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      rw [← shiftFrom_abstract1 hpd]
      rfl
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [inferBody, viewM, Expr.view, pure_bind]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tf htf
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htf hw.1)) ?_
    intro w hww
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE n' ty' body' m' =>
    have hwPi : WScoped d (Expr.forallE n' ty' body' m') :=
      whnf_WScoped henv fuel hww (inferTypeCore_WScoped henv fuel htf hw.1)
    simp only [WScoped] at hwPi
    refine bind_rel _ _ (ih.infer hpd hw.2) ?_
    intro ta hta
    refine bind_rel_eq _
      (ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hw.2) hwPi.1) ?_
    intro bb _
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    rw [← shiftFrom_instantiate1_gen]
    rfl
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show inferBody (pureFns env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (inferBody (pureFns env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [inferBody, viewM, Expr.view, pure_bind]
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
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      have hclosed : (entry.ty.instantiateLevelParams entry.levelParams
          us₂).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem (Env.findProj?_some hfp))).1
      have hres := piResidual_shiftFrom (p := p) (w.getAppArgs ++ [pe])
        (entry.ty.instantiateLevelParams entry.levelParams us₂)
      rw [shiftFrom_eq_self_of_not_hasFvar hclosed, List.map_append] at hres
      simp only [List.map] at hres
      rw [hres]
      cases hr : piResidual
          (entry.ty.instantiateLevelParams entry.levelParams us₂)
          (w.getAppArgs ++ [pe]) <;> rfl

private theorem defeq_step (henv : EnvWF env)
    (ih : ShiftClaims env fuel) : DefEqShift env (fuel + 1) := by
  intro p d hpd a b hwa hwb
  rw [isDefEqCore_succ, isDefEqCore_succ]
  simp only [defeqBody]
  rw [shiftFrom_beq]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr _ (ih.whnfCore hpd hwa) ?_
  intro wa hwa'
  refine bind_congr _ (ih.whnfCore hpd hwb) ?_
  intro wb hwb'
  have hwwa : WScoped d wa := whnfCore_WScoped henv fuel hwa' hwa
  have hwwb : WScoped d wb := whnfCore_WScoped henv fuel hwb' hwb
  rw [shiftFrom_beq]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  -- literal acceleration branches
  refine bind_congr (Option.map (shiftFrom p))
    (reduceNat_shift henv ih hpd hwwa) ?_
  intro oa hoa
  cases oa with
  | some a₂ =>
    have hwa₂ : WScoped d a₂ := by
      rcases reduceNat_inv hoa with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ih.defeq hpd hwa₂ hwwb
  | none =>
  refine bind_congr (Option.map (shiftFrom p))
    (reduceNat_shift henv ih hpd hwwb) ?_
  intro ob hob
  cases ob with
  | some b₂ =>
    have hwb₂ : WScoped d b₂ := by
      rcases reduceNat_inv hob with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ih.defeq hpd hwwa hwb₂
  | none =>
  -- the lazy delta unfolding decision
  rw [unfoldDefinition_shiftFrom henv, unfoldDefinition_shiftFrom henv]
  cases hua : unfoldDefinition env wa with
  | some a₂ =>
    have hwa₂ : WScoped d a₂ := unfoldDefinition_WScoped henv hua hwwa
    cases hub : unfoldDefinition env wb with
    | none =>
      simp only [Option.map_some, Option.map_none]
      exact ih.defeq hpd hwa₂ hwwb
    | some b₂ =>
      have hwb₂ : WScoped d b₂ := unfoldDefinition_WScoped henv hub hwwb
      simp only [Option.map_some]
      rw [headHint_shiftFrom, headHint_shiftFrom]
      refine ite_congr' (fun _ => ?_) (fun _ => ?_)
      · exact ih.defeq hpd hwa₂ hwwb
      refine ite_congr' (fun _ => ?_) (fun _ => ?_)
      · exact ih.defeq hpd hwwa hwb₂
      rw [sameConstHeads_shiftFrom]
      refine ite_congr' (fun _ => ?_) (fun _ => ?_)
      · refine bind_congr_eq (defeqSpine_shift henv ih hpd hwwa hwwb) ?_
        intro bb _
        refine ite_congr' (fun _ => rfl) (fun _ => ?_)
        exact ih.defeq hpd hwa₂ hwb₂
      · exact ih.defeq hpd hwa₂ hwb₂
  | none =>
  cases hub : unfoldDefinition env wb with
  | some b₂ =>
    have hwb₂ : WScoped d b₂ := unfoldDefinition_WScoped henv hub hwwb
    simp only [Option.map_some, Option.map_none]
    exact ih.defeq hpd hwwa hwb₂
  | none =>
  simp only [Option.map_none]
  have hstuck : stuckIrrel (pureFns env fuel) env (d + 1) (shiftFrom p wa)
      (shiftFrom p wb) = stuckIrrel (pureFns env fuel) env d wa wb :=
    stuckIrrel_shift henv ih hpd hwwa hwwb
  cases wa <;> cases wb <;>
    try (first
      | exact hstuck
      | (try simp only [shiftFrom_fvar] at hstuck
         simp only [shiftFrom_fvar]
         exact hstuck))
  case sort.sort => rfl
  case lit.lit => rfl
  case lit.const l cn cus hne =>
    cases l with
    | strVal str =>
      try simp only [shiftFrom_fvar] at hstuck
      exact hstuck
    | natVal n =>
      exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.lit cn cus l hne =>
    cases l with
    | strVal str =>
      try simp only [shiftFrom_fvar] at hstuck
      exact hstuck
    | natVal n =>
      exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lit.app l f x hne =>
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
      cases nn with
      | zero => exact hstuck
      | succ k =>
        cases f <;>
          try (first
            | exact hstuck
            | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
               exact hstuck))
        case const cn cus =>
        cases cus with
        | cons u us => exact hstuck
        | nil =>
          refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
          exact ih.defeq hpd (WScoped.of_not_hasFvar (e := .lit (.natVal k)) rfl) hwwb.2
  case app.lit f x l hne =>
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
      cases nn with
      | zero => exact hstuck
      | succ k =>
        cases f <;>
          try (first
            | exact hstuck
            | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
               exact hstuck))
        case const cn cus =>
        cases cus with
        | cons u us => exact hstuck
        | nil =>
          refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
          exact ih.defeq hpd hwwa.2 (WScoped.of_not_hasFvar (e := .lit (.natVal k)) rfl)
  case fvar.fvar idx₁ n₁ ty₁ idx₂ n₂ ty₂ hne =>
    simp only [shiftFrom_fvar] at hstuck ⊢
    rw [shiftIdx_beq]
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.const n us n' us' hne =>
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq rfl ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case forallE.forallE n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine bind_congr_eq (ih.defeq hpd hwwa.1 hwwb.1) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hb := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 (n := n₁) hwwa.1 0 hwwa.2)
      (WScoped.instantiate1 (n := n₂) hwwb.1 0 hwwb.2)
    rw [shiftFrom_instantiate1 hpd, shiftFrom_instantiate1 hpd] at hb
    refine bind_congr_eq hb ?_
    intro b₂ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    cases m₁.cod <;> cases m₂.cod <;> rfl
  case lam.lam n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine bind_congr_eq (ih.defeq hpd hwwa.1 hwwb.1) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hb := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 (n := n₁) hwwa.1 0 hwwa.2)
      (WScoped.instantiate1 (n := n₂) hwwb.1 0 hwwb.2)
    rw [shiftFrom_instantiate1 hpd, shiftFrom_instantiate1 hpd] at hb
    refine bind_congr_eq hb ?_
    intro b₂ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    cases m₁.cod <;> cases m₂.cod <;> rfl
  case app.app f₁ a₁ f₂ a₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine bind_congr_eq (ih.defeq hpd hwwa.1 hwwb.1) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq (ih.defeq hpd hwwa.2 hwwb.2) ?_
    intro b₂ _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case proj.proj s₁ i₁ e₁ s₂ i₂ e₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq (ih.defeq hpd hwwa hwwb) ?_
    intro b₁ _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.bvar n1 ty1 body1 m1 i hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.fvar n1 ty1 body1 m1 ix nn tt hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    try simp only [shiftFrom_fvar] at hstuck
    try simp only [shiftFrom_fvar]
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.sort n1 ty1 body1 m1 u hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.const n1 ty1 body1 m1 cn cus hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.app n1 ty1 body1 m1 ff aa hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.forallE n1 ty1 body1 m1 fn fty fbody fm hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.letE n1 ty1 body1 m1 ln lty lv lb hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.lit n1 ty1 body1 m1 ll hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.proj n1 ty1 body1 m1 ps pi2 pe2 hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd n1 m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case bvar.lam i n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case fvar.lam ix nn tt n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    try simp only [shiftFrom_fvar] at hstuck
    try simp only [shiftFrom_fvar]
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case sort.lam u n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.lam cn cus n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case app.lam ff aa n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case forallE.lam fn fty fbody fm n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case letE.lam ln lty lv lb n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lit.lam ll n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case proj.lam ps pi2 pe2 n2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd n2 m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)

private theorem annotate_step (henv : EnvWF env)
    (ih : ShiftClaims env fuel) : AnnotShift env (fuel + 1) := by
  intro p d hpd e hw
  rw [annotateCore_succ, annotateCore_succ]
  match e with
  | .bvar i => rfl
  | .sort u => rfl
  | .const n us => rfl
  | .lit (.strVal str) =>
    show annotateBody (pureFns env fuel) env (d + 1) (.lit (.strVal str)) =
      (annotateBody (pureFns env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [annotateBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .letE n ty v body => rfl
  | .lit (.natVal n) =>
    show annotateBody (pureFns env fuel) env (d + 1) (.lit (.natVal n)) =
      (annotateBody (pureFns env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [annotateBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx n ty =>
    have hw' : idx < d ∧ WScoped idx ty := by
      simpa only [WScoped] using hw
    rw [shiftFrom_fvar]
    simp only [annotateBody]
    rw [if_pos (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        if_pos hw'.1]
    simp only [pure, Except.pure, map_ok, shiftFrom_fvar]
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro f' hf'
    have hwf' : WScoped d f' := annotateCore_WScoped fuel f hf' hw.1
    refine bind_rel _ _ (ih.annotate hpd hw.2) ?_
    intro a' ha'
    have hwa' : WScoped d a' := annotateCore_WScoped fuel a ha' hw.2
    refine bind_rel _ _ (ih.infer hpd hwf') ?_
    intro tf htf
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htf hwf')) ?_
    intro w hww
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE n' ty' body' m' =>
    have hwPi : WScoped d (Expr.forallE n' ty' body' m') :=
      whnf_WScoped henv fuel hww (inferTypeCore_WScoped henv fuel htf hwf')
    simp only [WScoped] at hwPi
    refine bind_rel _ _ (ih.infer hpd hwa') ?_
    intro ta hta
    refine bind_rel_eq _
      (ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hwa') hwPi.1) ?_
    intro bb _
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .forallE n ty body mb =>
    simp only [WScoped] at hw
    show annotateBody (pureFns env fuel) env (d + 1)
        (.forallE n (shiftFrom p ty) (shiftFrom p body) mb) =
      (annotateBody (pureFns env fuel) env d (.forallE n ty body mb)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro ty' hty'
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty' hw.1
    have hopen : WScoped (d + 1) (body.instantiate1 (.fvar d n ty')) :=
      WScoped.instantiate1 (n := n) hwty' 0 hw.2
    have hbody := ih.annotate (p := p) (d := d + 1) (by omega) hopen
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro body' hbody'
    have hwbody' : WScoped (d + 1) body' :=
      annotateCore_WScoped fuel _ hbody' hopen
    refine bind_rel _ _
      (ih.infer (p := p) (d := d + 1) (by omega) hwbody') ?_
    intro tb htb
    refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
      (d := d + 1) (by omega)
      (inferTypeCore_WScoped henv fuel htb hwbody')) ?_
    intro v _
    rw [← shiftFrom_abstract1 hpd]
    rfl
  | .lam n ty body mb =>
    simp only [WScoped] at hw
    show annotateBody (pureFns env fuel) env (d + 1)
        (.lam n (shiftFrom p ty) (shiftFrom p body) mb) =
      (annotateBody (pureFns env fuel) env d (.lam n ty body mb)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro ty' hty'
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty' hw.1
    have hopen : WScoped (d + 1) (body.instantiate1 (.fvar d n ty')) :=
      WScoped.instantiate1 (n := n) hwty' 0 hw.2
    have hbody := ih.annotate (p := p) (d := d + 1) (by omega) hopen
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro body' hbody'
    have hwbody' : WScoped (d + 1) body' :=
      annotateCore_WScoped fuel _ hbody' hopen
    refine bind_rel _ _
      (ih.infer (p := p) (d := d + 1) (by omega) hwbody') ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv fuel hbt hwbody'
    refine bind_rel _ _
      (ih.infer (p := p) (d := d + 1) (by omega) hwbt) ?_
    intro tbt htbt
    refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
      (d := d + 1) (by omega)
      (inferTypeCore_WScoped henv fuel htbt hwbt)) ?_
    intro v _
    rw [← shiftFrom_abstract1 hpd]
    rfl
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show annotateBody (pureFns env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (annotateBody (pureFns env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw) ?_
    intro e'' he''
    have hwe'' : WScoped d e'' := annotateCore_WScoped fuel pe he'' hw
    refine bind_rel _ _ (ih.infer hpd hwe'') ?_
    intro te₀ hte₀
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel hte₀ hwe'')) ?_
    intro te hte
    have hwte : WScoped d te := whnf_WScoped henv fuel hte
      (inferTypeCore_WScoped henv fuel hte₀ hwe'')
    have helim := annotateProjElim_shift henv ih hpd sn i hwte hwe''
    rw [getAppFn_shiftFrom]
    cases hfn : te.getAppFn <;> try exact helim
    case fvar =>
      rw [shiftFrom_fvar]
      exact helim
    case const T cus =>
    simp only [shiftFrom]
    cases hfp : env.findProj? T i with
    | none => exact helim
    | some entry =>
      dsimp only
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun _ => ?_) (fun _ => helim)
      exact ite_rel _ (fun _ => rfl) (fun _ => rfl)

end Helpers


/-- The bisimulation: every core entry point commutes with the fvar
shift, at every fuel. -/
theorem shiftClaims {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat), ShiftClaims env fuel := by
  intro fuel
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ fuel ih =>
    exact ⟨whnfCore_step henv ih, whnf_step henv ih, infer_step henv ih,
      defeq_step henv ih, annotate_step henv ih⟩

/-! ## Depth invariance -/

section DepthInv

variable {env : Env}

private theorem whnfCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    whnfCore env fuel (d + 1) e = whnfCore env fuel d e := by
  have h := (shiftClaims henv fuel).whnfCore (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : whnfCore env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self (whnfCore_WScoped henv fuel hres hw).fvarsBelow]

private theorem whnf_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    whnf env fuel (d + 1) e = whnf env fuel d e := by
  have h := (shiftClaims henv fuel).whnf (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : whnf env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self (whnf_WScoped henv fuel hres hw).fvarsBelow]

private theorem inferTypeCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    inferTypeCore env fuel (d + 1) e = inferTypeCore env fuel d e := by
  have h := (shiftClaims henv fuel).infer (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : inferTypeCore env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (inferTypeCore_WScoped henv fuel hres hw).fvarsBelow]

private theorem isDefEqCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    isDefEqCore env fuel (d + 1) a b = isDefEqCore env fuel d a b := by
  have h := (shiftClaims henv fuel).defeq (Nat.le_refl d) hwa hwb
  rwa [shiftFrom_eq_self hwa.fvarsBelow, shiftFrom_eq_self hwb.fvarsBelow]
    at h

private theorem annotateCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    annotateCore env fuel (d + 1) e = annotateCore env fuel d e := by
  have h := (shiftClaims henv fuel).annotate (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : annotateCore env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (annotateCore_WScoped fuel e hres hw).fvarsBelow]

private theorem whnfCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    whnfCore env fuel d₂ e = whnfCore env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      whnfCore_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem whnf_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    whnf env fuel d₂ e = whnf env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      whnf_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem inferTypeCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    inferTypeCore env fuel d₂ e = inferTypeCore env fuel d₁ e := by
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
    isDefEqCore env fuel d₂ a b = isDefEqCore env fuel d₁ a b := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      isDefEqCore_depth_succ henv fuel (hwa.mono (by omega))
        (hwb.mono (by omega)), ih]

private theorem annotateCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    annotateCore env fuel d₂ e = annotateCore env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      annotateCore_depth_succ henv fuel (hw.mono (by omega)), ih]

/-- **Depth invariance of head normalization**: `whnfCore`'s result
does not depend on the ambient binder depth, for inputs well-scoped at
both depths. -/
theorem whnfCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    whnfCore env fuel d₁ e = whnfCore env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (whnfCore_depth_le henv fuel hle (WScoped.of_wscopedB h₁)).symm
  · exact whnfCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of the reduction loop**. -/
theorem whnf_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    whnf env fuel d₁ e = whnf env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (whnf_depth_le henv fuel hle (WScoped.of_wscopedB h₁)).symm
  · exact whnf_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of inference**. -/
theorem inferTypeCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    inferTypeCore env fuel d₁ e = inferTypeCore env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (inferTypeCore_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact inferTypeCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of definitional equality**. -/
theorem isDefEqCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {a b : Expr} (ha₁ : a.wscopedB d₁ = true)
    (hb₁ : b.wscopedB d₁ = true) (ha₂ : a.wscopedB d₂ = true)
    (hb₂ : b.wscopedB d₂ = true) :
    isDefEqCore env fuel d₁ a b = isDefEqCore env fuel d₂ a b := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (isDefEqCore_depth_le henv fuel hle (WScoped.of_wscopedB ha₁)
      (WScoped.of_wscopedB hb₁)).symm
  · exact isDefEqCore_depth_le henv fuel hle (WScoped.of_wscopedB ha₂)
      (WScoped.of_wscopedB hb₂)

/-- **Depth invariance of annotation**. -/
theorem annotateCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    annotateCore env fuel d₁ e = annotateCore env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (annotateCore_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact annotateCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

end DepthInv

end Setlec
