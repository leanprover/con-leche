module

import ConLeche.Verify.Mono
public import ConLeche.Verify.Deep

public section

/-!
# The cache-refinement bridge, part A: fueled families

`FueledM` packages a fuel-indexed family of pure computations that is
monotone in the fuel (monotonicity of the components is `Mono.lean`'s
result, carried pointwise through `bind`).  The `atF` battery relates
the core bodies instantiated at `FueledM` (with the fueled record) to
their plain instantiations at `pureFns mode eager env F` — the same projection
game as `PairM`, one component instead of two.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}
/- Task #172 B2: the ι cone's mode is decoupled from the knot's, so
that the `whnfCore` template's ι-cone mode can occupy it while the
knot stays at the tower's `mode`.  Generalization only — every landed
call site unifies `mi := mode`. -/
variable {mi : CheckMode} {ei : Bool}

/-- Monotone fuel-indexed families of pure computations. -/
@[expose] def FueledM (α : Type) : Type :=
  {p : Nat → CheckM α //
    ∀ {f f' : Nat} {v : α}, f ≤ f' → p f = .ok v → p f' = .ok v}

namespace FueledM

instance : Monad FueledM where
  pure a := ⟨fun _ => pure a, fun _ h => h⟩
  bind x f :=
    ⟨fun F => x.val F >>= fun a => (f a).val F, by
      intro F F' v hle h
      simp only [Bind.bind] at h ⊢
      cases hx : x.val F with
      | error e => rw [hx] at h; exact nomatch h
      | ok a =>
        rw [hx] at h
        dsimp only [Except.bind] at h
        rw [x.property hle hx]
        dsimp only [Except.bind]
        exact (f a).property hle h⟩

instance : MonadExceptOf CheckError FueledM where
  throw e := ⟨fun _ => throw e, fun _ h => nomatch h⟩
  tryCatch _ _ :=
    ⟨fun _ => throw (.internal "tryCatch unsupported"), fun _ h => nomatch h⟩

@[simp] theorem atF_bind {α β : Type} (x : FueledM α) (f : α → FueledM β)
    (F : Nat) :
    (x >>= f).val F = x.val F >>= fun a => (f a).val F := rfl

@[simp] theorem atF_pure {α : Type} (a : α) (F : Nat) :
    (pure a : FueledM α).val F = pure a := rfl

@[simp] theorem atF_throw {α : Type} (e : CheckError) (F : Nat) :
    (throw e : FueledM α).val F = throw e := rfl

@[simp] theorem atF_ite {α : Type} {c : Prop} [Decidable c]
    (x y : FueledM α) (F : Nat) :
    (if c then x else y).val F = if c then x.val F else y.val F := by
  by_cases hc : c <;> simp [hc]

end FueledM

/-- The fueled record: each entry is the family of its fueled runs,
monotone by `Mono.lean`. -/
@[expose] def fueledFns (mode : CheckMode) (eager : Bool) (env : Env) : CoreFns FueledM where
  whnfCore c d e := ⟨fun F => whnfCore mode eager env F d e c, fun hle h => whnfCore_mono hle h⟩
  whnf d e := ⟨fun F => whnf mode eager env F d e, fun hle h => whnf_mono hle h⟩
  infer d e := ⟨fun F => inferTypeCore mode eager env F d e,
    fun hle h => inferTypeCore_mono hle h⟩
  defeq d a b := ⟨fun F => isDefEqCore mode eager env F d a b,
    fun hle h => isDefEqCore_mono hle h⟩
  defeqE d a b := ⟨fun F => (pureFns mode eager env F).defeqE d a b,
    fun hle h => (pureFns_mono env hle).2.2.2.2.1 d a b _ h⟩
  inferIO d e := ⟨fun F => inferTypeIO mode eager env F d e,
    fun hle h => inferTypeIO_mono hle h⟩

section AtF

variable {env : Env}

theorem liftFueled_atF {α : Type} (what : String) (o : Option α) (F : Nat) :
    (liftFueled what o : FueledM α).val F = liftFueled what o := by
  cases o <;> rfl

theorem iotaCertsFull_atF (d : Nat) (F : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCertsFull (fueledFns mode eager env) env d ty args).val F =
        iotaCertsFull (pureFns mode eager env F) env d ty args
  | _, [] => rfl
  | .forallE ty body, arg :: rest => by
    show ((do
        let ta ← (fueledFns mode eager env).infer d arg
        if ← (fueledFns mode eager env).defeq d ta ty then
          iotaCertsFull (fueledFns mode eager env) env d (body.instantiate1 arg) rest
        else pure false : FueledM Bool)).val F = (do
        let ta ← (pureFns mode eager env F).infer d arg
        if ← (pureFns mode eager env F).defeq d ta ty then
          iotaCertsFull (pureFns mode eager env F) env d (body.instantiate1 arg) rest
        else pure false)
    rw [FueledM.atF_bind]
    congr 1
    funext ta
    rw [FueledM.atF_bind]
    congr 1
    funext b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact iotaCertsFull_atF d F (body.instantiate1 arg) rest
    | false => rfl
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _, _ :: _
  | .letE _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem defEqList_atF (d : Nat) (F : Nat) :
    ∀ (as bs : List Expr),
      (defEqList (fueledFns mode eager env) env d as bs).val F =
        defEqList (pureFns mode eager env F) env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (fueledFns mode eager env).defeq d a b then
          defEqList (fueledFns mode eager env) env d as bs
        else pure false : FueledM Bool)).val F = (do
        if ← (pureFns mode eager env F).defeq d a b then
          defEqList (pureFns mode eager env F) env d as bs
        else pure false)
    rw [FueledM.atF_bind]
    congr 1
    funext r
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact defEqList_atF d F as bs
    | false => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem defeqArg_atF (d : Nat) (a ta ty : Expr) (F : Nat) :
    (defeqArg (fueledFns mode eager env) d a ta ty).val F =
      defeqArg (pureFns mode eager env F) d a ta ty := by
  unfold defeqArg; split <;> rfl

theorem defeqSpine_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqSpine (fueledFns mode eager env) env d a b).val F =
      defeqSpine (pureFns mode eager env F) env d a b := by
  unfold defeqSpine
  repeat (first
    | rfl
    | (rw [defEqList_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem iotaIndexOk_atF (d : Nat) (F : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : List Expr) :
    (iotaIndexOk (fueledFns mode eager env) env d mI rP cnP tyCtor margs idx).val F =
      iotaIndexOk (pureFns mode eager env F) env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, ite_eq_left hmr]; rfl
  · simp only [iotaIndexOk, ite_eq_right hmr]
    cases piResidual tyCtor margs with
    | none => rfl
    | some residual => exact defEqList_atF d F _ _

macro "atF_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_atF])
    | (rw [iotaCertsFull_atF])
    | (rw [iotaIndexOk_atF])
    | (rw [defEqList_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_tac" : tactic =>
  `(tactic| atF_step <;> atF_step <;> atF_step <;> atF_step <;>
    atF_step <;> atF_step <;> atF_step <;> atF_step <;>
    atF_step <;> atF_step <;> atF_step <;> atF_step <;>
    atF_step <;> atF_step <;> atF_step)

theorem reduceNat_atF (d : Nat) (e : Expr) (F : Nat) :
    (reduceNat (fueledFns mode eager env) env d e).val F =
      reduceNat (pureFns mode eager env F) env d e := by
  unfold reduceNat
  atF_tac

theorem ensureSort_atF (d : Nat) (e : Expr) (F : Nat) :
    (ensureSort (fueledFns mode eager env) env d e).val F =
      ensureSort (pureFns mode eager env F) env d e := by
  unfold ensureSort
  atF_tac

theorem checkGuardRows_atF (bound : Level) (F : Nat) :
    ∀ rows, (checkGuardRows (fueledFns mode eager env).inferIO (fueledFns mode eager env).whnf bound rows).val F =
      checkGuardRows (pureFns mode eager env F).inferIO (pureFns mode eager env F).whnf bound rows
  | [] => rfl
  | (d, dom) :: rest => by
    unfold checkGuardRows
    rw [FueledM.atF_bind]
    refine congrArg _ (funext fun t => ?_)
    rw [FueledM.atF_bind]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> try rfl
    dsimp only []
    have hk := checkGuardRows_atF bound F rest
    split
    · exact hk
    · rw [FueledM.atF_bind, hk]; rfl

theorem formerSortLoop_atF (F : Nat) :
    ∀ (d n : Nat) (e : Expr),
      (formerSortLoop (fueledFns mode eager env).whnf d n e).val F =
        formerSortLoop (pureFns mode eager env F).whnf d n e
  | d, 0, e => by
    unfold formerSortLoop
    rw [FueledM.atF_bind]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> rfl
  | d, n + 1, e => by
    unfold formerSortLoop
    rw [FueledM.atF_bind]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> try rfl
    exact formerSortLoop_atF F (d + 1) n _

theorem formerNeverZeroAt_atF (cvT : ConstantVal) (caps : IndCaps) (us : List Level) (F : Nat) :
    (formerNeverZeroAt (fueledFns mode eager env).whnf cvT caps us).val F =
      formerNeverZeroAt (pureFns mode eager env F).whnf cvT caps us := by
  unfold formerNeverZeroAt
  split
  · rfl
  · rw [FueledM.atF_bind, formerSortLoop_atF]
    refine congrArg _ (funext fun o => ?_)
    cases o <;> rfl

theorem iotaCase3At_atF (isK : Bool) (cvj : ConstantVal) (us : List Level) (F : Nat) :
    (iotaCase3At (fueledFns mode eager env).whnf env.find? isK cvj us).val F =
      iotaCase3At (pureFns mode eager env F).whnf env.find? isK cvj us := by
  unfold iotaCase3At
  split
  · rfl
  · split
    · split
      · rw [FueledM.atF_bind, formerNeverZeroAt_atF]
        rfl
      · rfl
    · rfl

theorem projRowBound_atF (cvT : ConstantVal) (caps : IndCaps) (us : List Level) (F : Nat) :
    (projRowBound (fueledFns mode eager env).whnf cvT caps us).val F =
      projRowBound (pureFns mode eager env F).whnf cvT caps us := by
  unfold projRowBound
  split
  · rfl
  · rw [FueledM.atF_bind, formerSortLoop_atF]
    refine congrArg _ (funext fun o => ?_)
    cases o <;> rfl

theorem checkProjGuard_atF (entry : ProjEntry) (us : List Level) (F : Nat) :
    (checkProjGuard (fueledFns mode eager env).inferIO (fueledFns mode eager env).whnf env entry us).val F =
      checkProjGuard (pureFns mode eager env F).inferIO (pureFns mode eager env F).whnf env entry us := by
  unfold checkProjGuard
  split
  · rw [FueledM.atF_bind, projRowBound_atF]
    refine congrArg _ (funext fun o => ?_)
    cases o with
    | none => rfl
    | some bound =>
      dsimp only
      split
      · exact checkGuardRows_atF bound F _
      · rfl
  · rfl

theorem proofIrrel_atF (d : Nat) (a b : Expr) (F : Nat) :
    (proofIrrel (fueledFns mode eager env) d a b).val F =
      proofIrrel (pureFns mode eager env F) d a b := by
  unfold proofIrrel
  atF_tac

theorem propIrrel_atF (d : Nat) (a b : Expr) (F : Nat) :
    (propIrrel (fueledFns mode eager env) env d a b).val F =
      propIrrel (pureFns mode eager env F) env d a b := by
  unfold propIrrel
  atF_tac

theorem structEtaCertWith_atF (d : Nat) (a b wtb : Expr) (F : Nat) :
    (structEtaCertWith (fueledFns mode eager env) env d a b wtb).val F =
      structEtaCertWith (pureFns mode eager env F) env d a b wtb := by
  unfold structEtaCertWith
  atF_tac

theorem structUnitCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (structUnitCert (fueledFns mode eager env) env d a b).val F =
      structUnitCert (pureFns mode eager env F) env d a b := by
  unfold structUnitCert
  atF_tac

theorem etaCert_atF (d : Nat) (ty body : Expr) (b : Expr) (F : Nat) :
    (etaCert mi (fueledFns mode eager env) env d ty body b).val F =
      etaCert mi (pureFns mode eager env F) env d ty body b := by
  unfold etaCert
  atF_tac

macro "atF_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_atF])
    | (rw [iotaCertsFull_atF])
    | (rw [iotaIndexOk_atF])
    | (rw [defEqList_atF])
    | (rw [reduceNat_atF])
    | (rw [ensureSort_atF])
    | (rw [checkProjGuard_atF])
    | (rw [iotaCase3At_atF])
    | (rw [formerNeverZeroAt_atF])
    | (rw [proofIrrel_atF])
    | (rw [propIrrel_atF])
    | (rw [structEtaCertWith_atF])
    | (rw [structUnitCert_atF])
    | (rw [etaCert_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_tac2" : tactic =>
  `(tactic| atF_step2 <;> atF_step2 <;> atF_step2 <;> atF_step2 <;>
    atF_step2 <;> atF_step2 <;> atF_step2 <;> atF_step2 <;>
    atF_step2 <;> atF_step2 <;> atF_step2 <;> atF_step2 <;>
    atF_step2 <;> atF_step2 <;> atF_step2)

theorem structEtaCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (structEtaCert (fueledFns mode eager env) env d a b).val F =
      structEtaCert (pureFns mode eager env F) env d a b := by
  unfold structEtaCert
  atF_tac2

-- Outer casing peeled by hand (as in `ConLeche/Verify/PairM.lean`): the
-- body outgrew the split-driven macro.
set_option maxHeartbeats 800000 in
theorem majorToCtor_atF (d : Nat) (c : Name) (isK : Bool) (rules : List RecRule) (e : Expr) (F : Nat) :
    (majorToCtor mode (fueledFns mode eager env) env d c isK rules e).val F =
      majorToCtor mode (pureFns mode eager env F) env d c isK rules e := by
  unfold majorToCtor
  by_cases hca : isCtorApp env e = true
  · rw [ite_eq_left hca, ite_eq_left hca]; rfl
  rw [ite_eq_right hca, ite_eq_right hca]
  match rules with
  | [] => rfl
  | _ :: _ :: _ => rfl
  | [rl] =>
    dsimp only
    cases hfr : env.find? rl.ctor <;> try rfl
    case some ci =>
    cases ci <;> try rfl
    case ctorInfo cvj cnP cnF =>
    dsimp only
    cases (cvj.type.piResult).getAppFn <;> try rfl
    case const T us₀ =>
    dsimp only
    cases env.find? T <;> try rfl
    case some ciT =>
    cases ciT <;> try rfl
    case indInfo cvT caps =>
    dsimp only
    by_cases hK : isK = true
    · rw [ite_eq_left hK, ite_eq_left hK]
      atF_tac2
    rw [ite_eq_right hK, ite_eq_right hK]
    by_cases hE : etaRescueOk rl.ctor cvj cvT caps = true
    · rw [ite_eq_left hE, ite_eq_left hE]
      atF_tac2
    rw [ite_eq_right hE, ite_eq_right hE]
    by_cases hA : T = andName
    · rw [ite_eq_left hA, ite_eq_left hA]
      atF_tac2
    rw [ite_eq_right hA, ite_eq_right hA]
    rfl

theorem litMajorToCtor_atF (d : Nat) (e : Expr) (F : Nat) :
    (litMajorToCtor (fueledFns mode eager env) env d e).val F =
      litMajorToCtor (pureFns mode eager env F) env d e := by
  unfold litMajorToCtor
  atF_tac2

theorem prepareMajor_atF (d : Nat) (c : Name) (isK : Bool) (rules : List RecRule) (e : Expr)
    (F : Nat) :
    (prepareMajor mode (fueledFns mode eager env) env d c isK rules e).val F =
      prepareMajor mode (pureFns mode eager env F) env d c isK rules e := by
  unfold prepareMajor
  split
  · repeat (first
      | rfl
      | (rw [majorToCtor_atF])
      | (rw [litMajorToCtor_atF])
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | (split <;> (first | rfl | rw [litMajorToCtor_atF]))
      | (dsimp only []))
  · simp only [FueledM.atF_ite, FueledM.atF_bind, FueledM.atF_pure,
      majorToCtor_atF, litMajorToCtor_atF]
    rfl

theorem projLitToCtor_atF (d : Nat) (e : Expr) (F : Nat) :
    (projLitToCtor (fueledFns mode eager env) env d e).val F =
      projLitToCtor (pureFns mode eager env F) env d e := by
  unfold projLitToCtor
  atF_tac2

macro "atF_core3" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_atF])
    | (rw [iotaCertsFull_atF])
    | (rw [iotaIndexOk_atF])
    | (rw [defEqList_atF])
    | (rw [reduceNat_atF])
    | (rw [ensureSort_atF])
    | (rw [checkProjGuard_atF])
    | (rw [iotaCase3At_atF])
    | (rw [formerNeverZeroAt_atF])
    | (rw [proofIrrel_atF])
    | (rw [propIrrel_atF])
    | (rw [structEtaCertWith_atF])
    | (rw [structUnitCert_atF])
    | (rw [etaCert_atF])
    | (rw [structEtaCert_atF])
    | (rw [majorToCtor_atF])
    | (rw [litMajorToCtor_atF])
    | (rw [prepareMajor_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_step3" : tactic => `(tactic| atF_core3 (fail))

macro "atF_tac3" : tactic =>
  `(tactic| atF_step3 <;> atF_step3 <;> atF_step3 <;> atF_step3 <;>
    atF_step3 <;> atF_step3 <;> atF_step3 <;> atF_step3 <;>
    atF_step3 <;> atF_step3 <;> atF_step3 <;> atF_step3 <;>
    atF_step3 <;> atF_step3 <;> atF_step3)

theorem stuckIrrel_atF (d : Nat) (a b : Expr) (F : Nat) :
    (stuckIrrel (fueledFns mode eager env) env d a b).val F =
      stuckIrrel (pureFns mode eager env F) env d a b := by
  unfold stuckIrrel
  atF_tac3

theorem iotaRec_atF (d : Nat) (e : Expr) (F : Nat) :
    (iotaRec mode (fueledFns mode eager env) env d e).val F =
      iotaRec mode (pureFns mode eager env F) env d e := by
  unfold iotaRec
  atF_tac3

theorem reduceProjCore_atF (d : Nat) (sn : Name) (i : Nat) (e : Expr) (F : Nat) :
    (reduceProjCore mi (fueledFns mode eager env) env d sn i e).val F =
      reduceProjCore mi (pureFns mode eager env F) env d sn i e := by
  unfold reduceProjCore
  atF_core3 (rw [projLitToCtor_atF])

theorem defeqLamsInner_atF (d : Nat) (b₁ b₂ : Expr) (F : Nat) :
    (defeqLamsInner mi (fueledFns mode eager env) d b₁ b₂).val F =
      defeqLamsInner mi (pureFns mode eager env F) d b₁ b₂ := by
  unfold defeqLamsInner
  atF_tac

theorem defeqLams_atF (F : Nat) :
    ∀ (k d : Nat) (ty₁ body₁ ty₂ body₂ : Expr),
      (defeqLams mi (fueledFns mode eager env) k d ty₁ body₁ ty₂ body₂).val F =
        defeqLams mi (pureFns mode eager env F) k d ty₁ body₁ ty₂ body₂
  | k, d, ty₁, body₁, ty₂, body₂ => by
    rw [defeqLams.eq_def, defeqLams.eq_def]
    rw [FueledM.atF_bind]
    congr 1
    funext ok
    cases ok with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      split
      · split
        · rfl
        · exact defeqLams_atF F _ (d + 1) _ _ _ _
      · exact defeqLamsInner_atF d _ _ F

theorem quickDefEq_atF (d : Nat) (a b : Expr) (F : Nat) :
    (quickDefEq mi (fueledFns mode eager env) d a b).val F =
      quickDefEq mi (pureFns mode eager env F) d a b := by
  unfold quickDefEq
  atF_core3 (rw [defeqLams_atF])

theorem defeqOffset_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqOffset (fueledFns mode eager env) d a b).val F =
      defeqOffset (pureFns mode eager env F) d a b := by
  unfold defeqOffset
  atF_tac3

theorem tryUnfoldProjApp_atF (d : Nat) (e : Expr) (F : Nat) :
    (tryUnfoldProjApp (fueledFns mode eager env) d e).val F =
      tryUnfoldProjApp (pureFns mode eager env F) d e := by
  unfold tryUnfoldProjApp
  atF_tac3

theorem deltaQuick_atF (d : Nat) (a b : Expr) (F : Nat) :
    (deltaQuick mi (fueledFns mode eager env) d a b).val F =
      deltaQuick mi (pureFns mode eager env F) d a b := by
  unfold deltaQuick
  atF_core3 (rw [quickDefEq_atF])

theorem lazyDeltaStep_atF (d : Nat) (a b : Expr) (F : Nat) :
    (lazyDeltaStep mi (fueledFns mode eager env) env d a b).val F =
      lazyDeltaStep mi (pureFns mode eager env F) env d a b := by
  unfold lazyDeltaStep
  atF_core3 (first | rw [deltaQuick_atF] | rw [tryUnfoldProjApp_atF] | rw [defeqSpine_atF])

theorem lazyDeltaReduction_atF (d : Nat) (F : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (lazyDeltaReduction mi ei (fueledFns mode eager env) env d n a b).val F =
        lazyDeltaReduction mi ei (pureFns mode eager env F) env d n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    unfold lazyDeltaReduction
    atF_core3 (first | rw [lazyDeltaStep_atF] | rw [defeqOffset_atF] | rw [lazyDeltaReduction_atF d F n])

theorem lazyDeltaProjReduction_atF (d : Nat) (sn : Name) (i : Nat) (F : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (lazyDeltaProjReduction mi (fueledFns mode eager env) env d sn i n a b).val F =
        lazyDeltaProjReduction mi (pureFns mode eager env F) env d sn i n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    unfold lazyDeltaProjReduction
    atF_core3 (first | rw [lazyDeltaStep_atF] | rw [reduceProjCore_atF] | rw [lazyDeltaProjReduction_atF d sn i F n])

theorem defeqProjPair_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqProjPair mi (fueledFns mode eager env) env d a b).val F =
      defeqProjPair mi (pureFns mode eager env F) env d a b := by
  unfold defeqProjPair
  atF_core3 (rw [lazyDeltaProjReduction_atF])

theorem defeqStuck_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqStuck mi (fueledFns mode eager env) env d a b).val F =
      defeqStuck mi (pureFns mode eager env F) env d a b := by
  unfold defeqStuck
  atF_core3 (rw [stuckIrrel_atF])

/-- The level-4 cascade, parameterized over one extra alternative so
that the loop-body lemmas can feed in their continuation hypothesis
(`atF_step4k`) without duplicating the rewrite list. -/
macro "atF_core4" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_atF])
    | (rw [iotaCertsFull_atF])
    | (rw [iotaIndexOk_atF])
    | (rw [defEqList_atF])
    | (rw [reduceNat_atF])
    | (rw [ensureSort_atF])
    | (rw [checkProjGuard_atF])
    | (rw [iotaCase3At_atF])
    | (rw [formerNeverZeroAt_atF])
    | (rw [proofIrrel_atF])
    | (rw [propIrrel_atF])
    | (rw [structEtaCertWith_atF])
    | (rw [structUnitCert_atF])
    | (rw [etaCert_atF])
    | (rw [structEtaCert_atF])
    | (rw [majorToCtor_atF])
    | (rw [stuckIrrel_atF])
    | (rw [iotaRec_atF])
    | (rw [projLitToCtor_atF])
    | (rw [defeqSpine_atF])
    | (rw [defeqArg_atF])
    | (rw [reduceProjCore_atF])
    | (rw [quickDefEq_atF])
    | (rw [lazyDeltaReduction_atF])
    | (rw [defeqProjPair_atF])
    | (rw [defeqStuck_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    -- an `if` in the cascade: unfolding the `ite` primitive hands
    -- both arms back to the cascade's own `split`
    | ((rw [FueledM.atF_ite]; congr 1) <;> try rfl)
    | (dsimp only [])
    | split))

macro "atF_step4" : tactic => `(tactic| atF_core4 (fail))

macro "atF_step4k" hk:ident : tactic =>
  `(tactic| atF_core4 (rw [$hk:ident]))

macro "atF_tac4k" hk:ident : tactic =>
  `(tactic| atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk)

macro "atF_tac4" : tactic =>
  `(tactic| atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4)

theorem whnfCoreBody_atF (c : Bool) (d : Nat) (e : Expr) (F : Nat) :
    (whnfCoreBody mode (fueledFns mode eager env) env c d e).val F =
      whnfCoreBody mode (pureFns mode eager env F) env c d e := by
  unfold whnfCoreBody
  atF_tac4

theorem whnfStep_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (hk : ∀ e, (k e).val F = kF e) (e : Expr) :
    (whnfStep (fueledFns mode eager env) env d k e).val F =
      whnfStep (pureFns mode eager env F) env d kF e := by
  unfold whnfStep
  atF_tac4k hk

theorem whnfLoop_atF (d : Nat) (F : Nat) :
    ∀ (n : Nat) (e : Expr),
      (whnfLoop (fueledFns mode eager env) env d n e).val F =
        whnfLoop (pureFns mode eager env F) env d n e
  | 0, _ => rfl
  | n + 1, e => whnfStep_atF d _ _ (fun e' => whnfLoop_atF d F n e') e

theorem whnfBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (whnfBody (fueledFns mode eager env) env d e).val F =
      whnfBody (pureFns mode eager env F) env d e :=
  whnfLoop_atF d F whnfLoopFuel e

theorem inferBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (inferBody (fueledFns mode eager env) env d e).val F =
      inferBody (pureFns mode eager env F) env d e := by
  unfold inferBody
  atF_tac4

/-- The io inference body over the io-grade views (task #172 B4): the
same walk, the slot's family in the recursion sites. -/
theorem inferBodyIO_atF (d : Nat) (e : Expr) (F : Nat) :
    (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d e).val F =
      inferBodyIO (CoreFns.ioView (pureFns mode eager env F)) env d e := by
  unfold inferBodyIO CoreFns.ioView
  atF_tac4
  -- the residual `ensureSort` goals: the view leaves `whnf` (the only
  -- field `ensureSort` reads) untouched, so the plain lemma closes them
  all_goals exact ensureSort_atF _ _ _

theorem defeqBody_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqBody mode eager (fueledFns mode eager env) env d a b).val F =
      defeqBody mode eager (pureFns mode eager env F) env d a b := by
  unfold defeqBody
  atF_tac4

end AtF

end ConLeche
