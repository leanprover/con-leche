module

public import ConLeche.Verify.Fueled

public section

/-!
# Bulk beta: the spine loop and its identification with `whnfCoreBody`
(task #50)

The cached checker's app case (`whnfAppI`/`betaPeelI`,
`ConLeche/Cached/CoreC.lean`) consumes a whole application spine in one
loop, batching consecutive lambda binders into a single bulk
substitution; a fired ι or a peel with arguments left over hands the
head-normalization loop the term to continue with (`WhnfStep.cont`,
task #342 R2), so every step is the loop's own tail call.  This file
provides the pure mirrors — the step-returning `whnfAppW`/`betaPeelW`/
`whnfCoreStepW` the cached walk simulates, and the
continuation-passing `whnfApp`/`betaPeel`/`whnfCoreStepM` they equal
followed by `WhnfStep.run` (`whnfApp_run`, …), generic over the core
record like every helper — and proves the **soundness of the loop
against the chained spec**: a successful loop run at the pure fueled
knot is reproduced by the original one-argument-at-a-time
`whnfCoreBody` recursion at some fuel (`whnfApp_sound`,
`whnfCoreLoop_sound_body`).  The cached walk
(`ConLeche/Verify/Cached/DiscC4`) composes its simulation against the
mirror with this theorem, so the `Expr`-level specification — and
everything above it — is unchanged.

Key steps:

* `appStep` — the app clause's continuation after the function's
  whnf (`whnfCoreBody_app` re-expresses the body's app case with it);
* `whnfApp_snoc`/`betaPeel_snoc` — peeling the *last* argument off a
  loop run yields a loop run of the prefix followed by one `appStep`
  (the fold decomposition; bulk substitutions split by
  `Expr.instantiateList_cons`);
* `whnfApp_sound` — induction over the spine with the snoc
  decomposition, gluing with fuel monotonicity (every mirror is
  fuel-monotone via its `_atF` equation and the `FueledM` bundle).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ConLeche

variable {mode : CheckMode}
variable {mi : CheckMode}

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The continuation of `whnfCoreBody`'s app case after the function
part's head normalization: uniform beta on a lambda, iota otherwise. -/
def appStep (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (w a : Expr) : m Expr :=
  match w with
  | .lam _ body => k (body.instantiate1 a)
  | f' => do
    match ← iotaRec mode r env depth (.app f' a) with
    | some e'' => k e''
    | none => pure (.app f' a)

/-- `whnfCoreBody`'s app case is one head normalization followed by
`appStep`. -/
theorem whnfCoreBody_app (r : CoreFns m) (env : Env) (c : Bool) (depth : Nat)
    (f a : Expr) :
    whnfCoreBody mode r env c depth (.app f a)
      = r.whnfCore c depth f >>= fun w =>
          appStep mode r env depth (r.whnfCore c depth) w a := by rfl

mutual

/-- Pure mirror of the cached bulk-beta loop `whnfAppI`: consume the
spine against the whnf'd head. -/
@[expose] def whnfApp (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) :
    Expr → List Expr → m Expr
  | v, [] => pure v
  | v, a :: rest =>
    match v with
    | .lam _ body => betaPeel mode r env depth k body [a] rest
    | v => do
      match ← iotaRec mode r env depth (.app v a) with
      | some e'' => k (Expr.mkAppN e'' rest)
      | none => whnfApp mode r env depth k (.app v a) rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Pure mirror of the cached peel loop `betaPeelI`: `t` is the raw
lambda body after the binders consumed so far, `acc` their arguments
(innermost first). -/
def betaPeel (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) :
    Expr → List Expr → List Expr → m Expr
  | t, acc, [] => k (t.instantiateList acc)
  | t, acc, a :: rest =>
    match t with
    | .lam _ body => betaPeel mode r env depth k body (a :: acc) rest
    | t => k (Expr.mkAppN (t.instantiateList acc) (a :: rest))
termination_by _ _ args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- The iota arm of `whnfApp` (the loop body for a non-lambda head),
as a standalone computation: `whnfApp_ne_lam` identifies the loop with
it, giving every downstream proof a single equation instead of nine
head shapes. -/
@[expose] def whnfAppIota (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (v a : Expr) (rest : List Expr) : m Expr := do
  match ← iotaRec mode r env depth (.app v a) with
  | some e'' => k (Expr.mkAppN e'' rest)
  | none => whnfApp mode r env depth k (.app v a) rest

/-- The lambda arm of `whnfApp` (first binder of the peel), as a
standalone computation. -/
@[expose] def whnfAppLam (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (body : Expr) (a : Expr)
    (rest : List Expr) : m Expr :=
  betaPeel mode r env depth k body [a] rest

theorem whnfApp_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (v : Expr) :
    whnfApp mode r env depth k v [] = pure v := by
  rw [whnfApp]

theorem whnfApp_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (ty body : Expr) (a : Expr)
    (rest : List Expr) :
    whnfApp mode r env depth k (.lam ty body) (a :: rest)
      = whnfAppLam mode r env depth k body a rest := by
  rw [whnfApp, whnfAppLam]

theorem whnfApp_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    {v : Expr} (hv : ∀ ty body, v ≠ .lam ty body)
    (a : Expr) (rest : List Expr) :
    whnfApp mode r env depth k v (a :: rest)
      = whnfAppIota mode r env depth k v a rest := by
  cases v with
  | lam ty body => exact absurd rfl (hv ty body)
  | _ => rw [whnfApp, whnfAppIota] <;> exact fun _ _ h => nomatch h

/-- The non-lambda arm of `betaPeel` for a raw body that is not a
lambda: substitute and continue with the rest of the spine. -/
theorem betaPeel_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    {t : Expr} (ht : ∀ ty body, t ≠ .lam ty body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeel mode r env depth k t acc (a :: rest)
      = k (Expr.mkAppN (t.instantiateList acc) (a :: rest)) := by
  cases t with
  | lam ty body => exact absurd rfl (ht ty body)
  | _ => rw [betaPeel] <;> exact fun _ _ h => nomatch h

theorem betaPeel_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (t : Expr) (acc : List Expr) :
    betaPeel mode r env depth k t acc [] = k (t.instantiateList acc) := by
  rw [betaPeel]

/-- The lambda arm of `betaPeel` (peel one more binder). -/
@[expose] def betaPeelLam (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (body : Expr) (acc : List Expr)
    (a : Expr) (rest : List Expr) : m Expr :=
  betaPeel mode r env depth k body (a :: acc) rest

theorem betaPeel_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr)
    (ty body : Expr) (acc : List Expr)
    (a : Expr) (rest : List Expr) :
    betaPeel mode r env depth k (.lam ty body) acc (a :: rest)
      = betaPeelLam mode r env depth k body acc a rest := by
  rw [betaPeel, betaPeelLam]

/-! ## The step-returning mirrors (task #342 R2)

The cached loop (`whnfAppI`/`betaPeelI`/`whnfCoreStepI`) does not call
its continuation: it *returns* it (`WhnfStep.cont`), so that every
reduction step is the loop's own tail call.  `whnfAppW`/`betaPeelW`/
`whnfCoreStepW` are its pure mirrors; `whnfApp_run` and friends below
identify each with the continuation-passing mirror above followed by
`WhnfStep.run`, which is where the soundness argument lives. -/

/-- Continue a step's outcome with the continuation `k`. -/
@[expose] def WhnfStep.run (k : Expr → m Expr) : WhnfStep → m Expr
  | .done v => pure v
  | .cont e => k e

mutual

/-- Pure mirror of the cached `whnfAppI`. -/
@[expose] def whnfAppW (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → m WhnfStep
  | v, [] => pure (.done v)
  | v, a :: rest =>
    match v with
    | .lam _ body => betaPeelW mode r env depth body [a] rest
    | v => do
      match ← iotaRec mode r env depth (.app v a) with
      | some e'' => pure (.cont (Expr.mkAppN e'' rest))
      | none => whnfAppW mode r env depth (.app v a) rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Pure mirror of the cached `betaPeelI`. -/
@[expose] def betaPeelW (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → List Expr → m WhnfStep
  | t, acc, [] => pure (.cont (t.instantiateList acc))
  | t, acc, a :: rest =>
    match t with
    | .lam _ body => betaPeelW mode r env depth body (a :: acc) rest
    | t => pure (.cont (Expr.mkAppN (t.instantiateList acc) (a :: rest)))
termination_by _ _ args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

theorem whnfAppW_nil (r : CoreFns m) (env : Env) (depth : Nat) (v : Expr) :
    whnfAppW mode r env depth v [] = pure (.done v) := by
  rw [whnfAppW]

theorem whnfAppW_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (ty body : Expr) (a : Expr) (rest : List Expr) :
    whnfAppW mode r env depth (.lam ty body) (a :: rest)
      = betaPeelW mode r env depth body [a] rest := by
  rw [whnfAppW]

theorem whnfAppW_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    {v : Expr} (hv : ∀ ty body, v ≠ .lam ty body)
    (a : Expr) (rest : List Expr) :
    whnfAppW mode r env depth v (a :: rest)
      = (do
          match ← iotaRec mode r env depth (.app v a) with
          | some e'' => pure (.cont (Expr.mkAppN e'' rest))
          | none => whnfAppW mode r env depth (.app v a) rest) := by
  cases v with
  | lam ty body => exact absurd rfl (hv ty body)
  | _ => rw [whnfAppW] <;> exact fun _ _ h => nomatch h

theorem betaPeelW_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (t : Expr) (acc : List Expr) :
    betaPeelW mode r env depth t acc [] = pure (.cont (t.instantiateList acc)) := by
  rw [betaPeelW]

theorem betaPeelW_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (ty body : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeelW mode r env depth (.lam ty body) acc (a :: rest)
      = betaPeelW mode r env depth body (a :: acc) rest := by
  rw [betaPeelW]

theorem betaPeelW_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    {t : Expr} (ht : ∀ ty body, t ≠ .lam ty body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeelW mode r env depth t acc (a :: rest)
      = pure (.cont (Expr.mkAppN (t.instantiateList acc) (a :: rest))) := by
  cases t with
  | lam ty body => exact absurd rfl (ht ty body)
  | _ => rw [betaPeelW] <;> exact fun _ _ h => nomatch h

/-! ## The head-normalization loop mirror (task #106)

The cached `whnfCoreStepI`/`whnfCoreLoopI` run beta, iota and
projection steps as *iteration* on their own step budget instead of
chaining them through the knot.  These are the pure `Expr`-level
mirrors; `ConLeche/Verify/Cached/DiscC4.lean` simulates the cached loop
against them, and `whnfCoreLoop_sound_body` below reproduces a
successful mirror run by the chained specification `whnfCoreBody` at
some knot fuel — so the specification (and everything above it) is
unchanged. -/

/-- Pure mirror of `whnfCoreStepI`: one head-normalization step with
the loop's continuation `k` abstracted. -/
@[expose] def whnfCoreStepM (mode : CheckMode) (r : CoreFns m) (env : Env) (cheap : Bool)
    (depth : Nat) (k : Expr → m Expr) : Expr → m Expr
  | .sort u => pure (.sort u)
  | .fvar idx ty => pure (.fvar idx ty)
  | .forallE ty body => pure (.forallE ty body)
  | .lam ty body => pure (.lam ty body)
  | .const n us => pure (.const n us)
  | .lit l => pure (.lit l)
  | .app f a =>
    r.whnfCore cheap depth (Expr.app f a).getAppFn >>= fun v =>
      whnfApp mode r env depth k v (Expr.app f a).getAppArgs
  | .proj sn i pe => do
    let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
    match ← reduceProjCore mode r env depth sn i c with
    | some m' => k m'
    | none => pure (.proj sn i pe)
  | .letE _ v b => k (b.instantiate1 v)
  | .bvar _ => throw (.notImplemented "whnf beyond the supported fragment")

/-- Pure mirror of `whnfCoreStepI`: one head-normalization step,
returning the head normal form or the term to continue with. -/
@[expose] def whnfCoreStepW (mode : CheckMode) (r : CoreFns m) (env : Env) (cheap : Bool)
    (depth : Nat) : Expr → m WhnfStep
  | .sort u => pure (.done (.sort u))
  | .fvar idx ty => pure (.done (.fvar idx ty))
  | .forallE ty body => pure (.done (.forallE ty body))
  | .lam ty body => pure (.done (.lam ty body))
  | .const n us => pure (.done (.const n us))
  | .lit l => pure (.done (.lit l))
  | .app f a =>
    r.whnfCore cheap depth (Expr.app f a).getAppFn >>= fun v =>
      whnfAppW mode r env depth v (Expr.app f a).getAppArgs
  | .proj sn i pe => do
    let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
    match ← reduceProjCore mode r env depth sn i c with
    | some m' => pure (.cont m')
    | none => pure (.done (.proj sn i pe))
  | .letE _ v b => pure (.cont (b.instantiate1 v))
  | .bvar _ => throw (.notImplemented "whnf beyond the supported fragment")

/-- Pure mirror of `whnfCoreLoopI`: iterate `whnfCoreStepW` on the
step budget, continuing with the step's outcome. -/
@[expose] def whnfCoreLoopM (mode : CheckMode) (r : CoreFns m) (env : Env) (cheap : Bool)
    (depth : Nat) : Nat → Expr → m Expr
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e => do
    match ← whnfCoreStepW mode r env cheap depth e with
    | .done v => pure v
    | .cont e' => whnfCoreLoopM mode r env cheap depth n e'

/-! ## `atF` equations and fuel monotonicity for the mirrors -/

section AtF

variable {env : Env}

theorem appStep_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e)
    (w a : Expr) :
    (appStep mode (fueledFns mode env) env d k w a).val F
      = appStep mode (pureFns mode env F) env d kF w a := by
  unfold appStep
  atF_tac4k hk

mutual

theorem whnfApp_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e) :
    ∀ (xs : List Expr) (v : Expr),
      (whnfApp mode (fueledFns mode env) env d k v xs).val F
        = whnfApp mode (pureFns mode env F) env d kF v xs
  | [], v => by rw [whnfApp_nil, whnfApp_nil]; rfl
  | a :: rest, v => by
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfApp_lam, whnfApp_lam]
      unfold whnfAppLam
      exact betaPeel_atF d k kF F hk rest body [a]
    · have hv : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv, whnfApp_ne_lam _ _ _ _ hv]
      unfold whnfAppIota
      rw [FueledM.atF_bind, iotaRec_atF]
      congr 1
      funext o
      cases o with
      | some e'' => exact hk _
      | none => exact whnfApp_atF d k kF F hk rest (.app v a)
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (F : Nat) (hk : ∀ e, (k e).val F = kF e) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr),
      (betaPeel mode (fueledFns mode env) env d k t acc xs).val F
        = betaPeel mode (pureFns mode env F) env d kF t acc xs
  | [], t, acc => by rw [betaPeel_nil, betaPeel_nil]; exact hk _
  | a :: rest, t, acc => by
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeel_lam, betaPeel_lam]
      unfold betaPeelLam
      exact betaPeel_atF d k kF F hk rest body (a :: acc)
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht, betaPeel_ne_lam _ _ _ _ ht]
      exact hk _
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

mutual

theorem whnfAppW_atF (d : Nat) (F : Nat) :
    ∀ (xs : List Expr) (v : Expr),
      (whnfAppW mode (fueledFns mode env) env d v xs).val F
        = whnfAppW mode (pureFns mode env F) env d v xs
  | [], v => by rw [whnfAppW_nil, whnfAppW_nil]; rfl
  | a :: rest, v => by
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfAppW_lam, whnfAppW_lam]
      exact betaPeelW_atF d F rest body [a]
    · have hv : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfAppW_ne_lam _ _ _ hv, whnfAppW_ne_lam _ _ _ hv]
      rw [FueledM.atF_bind, iotaRec_atF]
      congr 1
      funext o
      cases o with
      | some e'' => rfl
      | none => exact whnfAppW_atF d F rest (.app v a)
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeelW_atF (d : Nat) (F : Nat) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr),
      (betaPeelW mode (fueledFns mode env) env d t acc xs).val F
        = betaPeelW mode (pureFns mode env F) env d t acc xs
  | [], t, acc => by rw [betaPeelW_nil, betaPeelW_nil]; rfl
  | a :: rest, t, acc => by
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeelW_lam, betaPeelW_lam]
      exact betaPeelW_atF d F rest body (a :: acc)
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeelW_ne_lam _ _ _ ht, betaPeelW_ne_lam _ _ _ ht]
      rfl
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

theorem whnfCoreStepW_atF (c : Bool) (d : Nat) (F : Nat) (e : Expr) :
    (whnfCoreStepW mode (fueledFns mode env) env c d e).val F
      = whnfCoreStepW mode (pureFns mode env F) env c d e := by
  cases e <;> (unfold whnfCoreStepW; try rfl)
  case app f a =>
    rw [FueledM.atF_bind]
    congr 1
    funext vh
    exact whnfAppW_atF d F _ vh
  case proj sn i pe =>
    atF_tac4

theorem whnfCoreLoopM_atF (c : Bool) (d : Nat) :
    ∀ (n : Nat) (e : Expr) (F : Nat),
      (whnfCoreLoopM mode (fueledFns mode env) env c d n e).val F
        = whnfCoreLoopM mode (pureFns mode env F) env c d n e
  | 0, _, _ => rfl
  | n + 1, e, F => by
    simp only [whnfCoreLoopM]
    rw [FueledM.atF_bind, whnfCoreStepW_atF]
    congr 1
    funext st
    cases st with
    | done v => rfl
    | cont e' => exact whnfCoreLoopM_atF c d n e' F

/-- Fuel monotonicity of the loop (via `whnfApp_atF` and the `FueledM`
bundle). -/
theorem whnfApp_mono {d : Nat} {xs : List Expr} {v : Expr} {F F' : Nat}
    (k : Expr → FueledM Expr) (kF kF' : Expr → CheckM Expr)
    (hkF : ∀ e, (k e).val F = kF e) (hkF' : ∀ e, (k e).val F' = kF' e)
    (hle : F ≤ F') {res : Expr}
    (h : whnfApp mode (pureFns mode env F) env d kF v xs = .ok res) :
    whnfApp mode (pureFns mode env F') env d kF' v xs = .ok res := by
  rw [← whnfApp_atF d k kF F hkF] at h
  rw [← whnfApp_atF d k kF' F' hkF']
  exact (whnfApp mode (fueledFns mode env) env d k v xs).property hle h

theorem betaPeel_mono {d : Nat} {xs acc : List Expr} {t : Expr}
    {F F' : Nat}
    (k : Expr → FueledM Expr) (kF kF' : Expr → CheckM Expr)
    (hkF : ∀ e, (k e).val F = kF e) (hkF' : ∀ e, (k e).val F' = kF' e)
    (hle : F ≤ F') {res : Expr}
    (h : betaPeel mode (pureFns mode env F) env d kF t acc xs = .ok res) :
    betaPeel mode (pureFns mode env F') env d kF' t acc xs = .ok res := by
  rw [← betaPeel_atF d k kF F hkF] at h
  rw [← betaPeel_atF d k kF' F' hkF']
  exact (betaPeel mode (fueledFns mode env) env d k t acc xs).property hle h

theorem appStep_mono {d : Nat} {w a : Expr} {F F' : Nat}
    (k : Expr → FueledM Expr) (kF kF' : Expr → CheckM Expr)
    (hkF : ∀ e, (k e).val F = kF e) (hkF' : ∀ e, (k e).val F' = kF' e)
    (hle : F ≤ F') {res : Expr}
    (h : appStep mode (pureFns mode env F) env d kF w a = .ok res) :
    appStep mode (pureFns mode env F') env d kF' w a = .ok res := by
  rw [← appStep_atF d k kF F hkF] at h
  rw [← appStep_atF d k kF' F' hkF']
  exact (appStep mode (fueledFns mode env) env d k w a).property hle h

theorem reduceProjCore_mono {d : Nat} {sn : Name} {i : Nat} {e : Expr} {F F' : Nat}
    (hle : F ≤ F') {o : Option Expr}
    (h : reduceProjCore mi (pureFns mode env F) env d sn i e = .ok o) :
    reduceProjCore mi (pureFns mode env F') env d sn i e = .ok o := by
  rw [← reduceProjCore_atF] at h ⊢
  exact (reduceProjCore mi (fueledFns mode env) env d sn i e).property hle h

theorem iotaRec_mono {d : Nat} {e : Expr} {F F' : Nat}
    (hle : F ≤ F') {o : Option Expr}
    (h : iotaRec mode (pureFns mode env F) env d e = .ok o) :
    iotaRec mode (pureFns mode env F') env d e = .ok o := by
  rw [← iotaRec_atF] at h ⊢
  exact (iotaRec mode (fueledFns mode env) env d e).property hle h

/-- `whnfCore` is the identity on a lambda (at nonzero fuel). -/
theorem whnfCore_lam (F d : Nat) (ty body : Expr)
    {c : Bool} :
    whnfCore mode env (F + 1) d (.lam ty body) c
      = .ok (.lam ty body) := rfl

end AtF

/-! ## The snoc decomposition -/

section Snoc

variable {env : Env} {c : Bool}

private theorem bind_ok {α β : Type} {x : Except CheckError α}
    {f : α → Except CheckError β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e =>
    rw [hx] at h
    exact nomatch h
  | ok a =>
    rw [hx] at h
    exact ⟨a, rfl, h⟩

/-- The bulk substitution of a lambda, exposed. -/
theorem instList_lam (ty body : Expr)
    (acc : List Expr) :
    (Expr.lam ty body).instantiateList acc
      = .lam (ty.instantiateList acc) (body.instantiateList acc 1) := by
  simp [Expr.instantiateList]

/-- The bulk substitution splits off its head as the innermost
`instantiate1` (the `d = 0`, one-binder-under form used by the peel). -/
theorem instList_cons0 (body : Expr) (a : Expr)
    (acc : List Expr) :
    body.instantiateList (a :: acc)
      = (body.instantiateList acc 1).instantiate1 a := by
  exact Expr.instantiateList_cons acc body a 0

theorem instList_single (body : Expr) (a : Expr) :
    body.instantiateList [a] = body.instantiate1 a := by
  rw [instList_cons0, Expr.instantiateList_nil]

private theorem ok_bind {α β : Type} (a : α)
    (f : α → Except CheckError β) :
    ((Except.ok a : Except CheckError α) >>= f) = f a := rfl

/-- The chained `whnfCore` of an application splits into the head
normalization of its function part and one `appStep` (the spec's own
app clause, at one fuel less). -/
theorem whnfCore_app_split {d F : Nat} {X a vres : Expr}
    (H : whnfCore mode env F d (.app X a) c = .ok vres) :
    ∃ G w, G < F ∧ whnfCore mode env G d X c = .ok w ∧
      appStep mode (pureFns mode env G) env d (fun x => whnfCore mode env G d x c) w a
        = .ok vres := by
  cases F with
  | zero => rw [whnfCore_zero] at H; exact nomatch H
  | succ G =>
    rw [whnfCore_succ, whnfCoreBody_app] at H
    obtain ⟨w, hw, H⟩ := bind_ok H
    exact ⟨G, w, Nat.lt_succ_self G, hw, H⟩

mutual

theorem whnfApp_snoc {d : Nat} :
    ∀ (xs : List Expr) (v a : Expr) (F : Nat) (vres : Expr),
      whnfApp mode (pureFns mode env F) env d (fun x => whnfCore mode env F d x c) v (xs ++ [a])
          = .ok vres →
      ∃ F' w,
        whnfApp mode (pureFns mode env F') env d (fun x => whnfCore mode env F' d x c) v xs = .ok w ∧
        appStep mode (pureFns mode env F') env d (fun x => whnfCore mode env F' d x c) w a = .ok vres
  | [], v, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      refine ⟨F, _, by rw [whnfApp_nil]; rfl, ?_⟩
      unfold appStep
      dsimp only
      rw [betaPeel_nil, instList_single] at H
      exact H
    · have hv : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      refine ⟨F, v, by rw [whnfApp_nil]; rfl, ?_⟩
      cases v with
      | lam ty body => exact absurd rfl (hv ty body)
      | _ =>
        unfold appStep
        dsimp only
        rw [ho, ok_bind]
        cases o with
        | some e'' => exact H
        | none =>
          rw [whnfApp_nil] at H
          injection H with h
          subst h
          rfl
  | x :: xs', v, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      obtain ⟨F₁, w, hw, hstep⟩ := betaPeel_snoc xs' body [x] a F vres H
      refine ⟨max F F₁, w, ?_,
        appStep_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
      rw [whnfApp_lam]
      unfold whnfAppLam
      exact betaPeel_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
        (fun _ => rfl) (Nat.le_max_right F F₁) hw
    · have hv : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | some e'' =>
        -- the ι reduct continues with the whole rest of the spine: split
        -- its last argument off by the chained app clause
        dsimp only at H
        rw [Expr.mkAppN_append_one] at H
        obtain ⟨G, w, hGF, hw, hstep⟩ := whnfCore_app_split H
        refine ⟨F, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_of_lt hGF) hstep⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [ho, ok_bind]
        exact whnfCore_mono (Nat.le_of_lt hGF) hw
      | none =>
        obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc xs' (.app v x) a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
            (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        exact whnfApp_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hw
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_snoc {d : Nat} :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      betaPeel mode (pureFns mode env F) env d (fun x => whnfCore mode env F d x c) t acc (xs ++ [a])
          = .ok vres →
      ∃ F' w,
        betaPeel mode (pureFns mode env F') env d (fun x => whnfCore mode env F' d x c) t acc xs
          = .ok w ∧
        appStep mode (pureFns mode env F') env d (fun x => whnfCore mode env F' d x c) w a = .ok vres
  | [], t, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      have hid : betaPeel mode (pureFns mode env (F + 1)) env d
          (fun x => whnfCore mode env (F + 1) d x c) (Expr.lam ty body) acc []
          = .ok (.lam (ty.instantiateList acc)
              (body.instantiateList acc 1)) := by
        rw [betaPeel_nil, instList_lam]
        exact whnfCore_lam F d _ _
      refine ⟨F + 1, _, hid, ?_⟩
      unfold appStep
      dsimp only
      rw [betaPeel_nil] at H
      rw [← instList_cons0]
      exact whnfCore_mono (Nat.le_succ F) H
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht] at H
      rw [show [a] = ([] : List Expr) ++ [a] from rfl, Expr.mkAppN_append_one] at H
      obtain ⟨G, w, -, hw, hstep⟩ := whnfCore_app_split H
      exact ⟨G, w, by rw [betaPeel_nil]; exact hw, hstep⟩
  | x :: xs', t, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      obtain ⟨F₁, w, hw, hstep⟩ :=
        betaPeel_snoc xs' body (x :: acc) a F vres H
      refine ⟨max F F₁, w, ?_,
        appStep_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
          (fun _ => rfl) (Nat.le_max_right F F₁) hstep⟩
      rw [betaPeel_lam]
      unfold betaPeelLam
      exact betaPeel_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
        (fun _ => rfl) (Nat.le_max_right F F₁) hw
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht] at H
      rw [← List.cons_append, Expr.mkAppN_append_one] at H
      obtain ⟨G, w, -, hw, hstep⟩ := whnfCore_app_split H
      exact ⟨G, w, by rw [betaPeel_ne_lam _ _ _ _ ht]; exact hw, hstep⟩
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

end Snoc

/-! ## Soundness of the loop against the chained body -/

section Sound

variable {env : Env} {c : Bool}

private theorem whnfApp_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h vh vres : Expr) (F₀ F : Nat),
      whnfCore mode env F₀ d h c = .ok vh →
      whnfApp mode (pureFns mode env F) env d (fun x => whnfCore mode env F d x c) vh rxs.reverse
          = .ok vres →
      ∃ F', whnfCore mode env F' d (Expr.mkAppN h rxs.reverse) c = .ok vres
  | [], h, vh, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, whnfApp_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, vh, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc rrs.reverse vh r F vres H
    obtain ⟨F₂, hP⟩ := whnfApp_sound_rev rrs h vh w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, whnfCore_succ,
      whnfCoreBody_app, whnfCore_def,
      whnfCore_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    exact appStep_mono ((fueledFns mode env).whnfCore c d) _ _ (fun _ => rfl)
      (fun _ => rfl) (Nat.le_max_right F₂ F₁) hstep

/-- A successful loop run over a normalized head is reproduced by the
chained `whnfCore` recursion on the whole application, at some fuel. -/
theorem whnfApp_sound {d : Nat} (xs : List Expr) (h vh vres : Expr)
    (F₀ F : Nat) (hh : whnfCore mode env F₀ d h c = .ok vh)
    (H : whnfApp mode (pureFns mode env F) env d (fun x => whnfCore mode env F d x c) vh xs
      = .ok vres) :
    ∃ F', whnfCore mode env F' d (Expr.mkAppN h xs) c = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := whnfApp_sound_rev (d := d) xs.reverse h vh vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-! ### From the loop's continuation to the chained `whnfCore`

A loop run whose continuation is *sound* (every success it reports is
reproduced by the chained `whnfCore` at some fuel) is itself
reproduced by a loop run whose continuation **is** `whnfCore`; the
existing `snoc`/`sound` machinery then reduces it to `whnfCoreBody`.
This is what lets the cached loop (task #106) run its reduction
chain on its own step budget while the specification stays
chained. -/

/-- The soundness hypothesis carried by a loop continuation. -/
def KSound (mode : CheckMode) (env : Env) (c : Bool) (d : Nat)
    (k : Expr → FueledM Expr) : Prop :=
  ∀ (G : Nat) (e v : Expr), (k e).val G = .ok v →
    ∃ M, whnfCore mode env M d e c = .ok v

mutual

theorem whnfApp_ksound {d : Nat} (k : Expr → FueledM Expr)
    (hks : KSound mode env c d k) :
    ∀ (xs : List Expr) (v res : Expr) (F : Nat),
      whnfApp mode (pureFns mode env F) env d (fun e => (k e).val F) v xs
        = .ok res →
      ∃ F', whnfApp mode (pureFns mode env F') env d (fun x => whnfCore mode env F' d x c) v xs
        = .ok res
  | [], v, res, F => by
    intro H
    rw [whnfApp_nil] at H
    injection H with h1
    subst h1
    exact ⟨F, by rw [whnfApp_nil]; rfl⟩
  | a :: rest, v, res, F => by
    intro H
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      obtain ⟨F₁, hP⟩ := betaPeel_ksound k hks rest body [a] res F H
      refine ⟨max F F₁, ?_⟩
      rw [whnfApp_lam]
      unfold whnfAppLam
      exact betaPeel_mono ((fueledFns mode env).whnfCore c d) _ _
        (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
    · have hv : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | some e'' =>
        obtain ⟨M, hM⟩ := hks F _ res H
        refine ⟨max F M, ?_⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F M) ho, ok_bind]
        exact whnfCore_mono (Nat.le_max_right F M) hM
      | none =>
        obtain ⟨F₁, hP⟩ := whnfApp_ksound k hks rest (.app v a) res F H
        refine ⟨max F F₁, ?_⟩
        rw [whnfApp_ne_lam _ _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        exact whnfApp_mono ((fueledFns mode env).whnfCore c d) _ _
          (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_ksound {d : Nat} (k : Expr → FueledM Expr)
    (hks : KSound mode env c d k) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr) (res : Expr)
      (F : Nat),
      betaPeel mode (pureFns mode env F) env d (fun e => (k e).val F) t acc xs
        = .ok res →
      ∃ F', betaPeel mode (pureFns mode env F') env d (fun x => whnfCore mode env F' d x c) t acc xs
        = .ok res
  | [], t, acc, res, F => by
    intro H
    rw [betaPeel_nil] at H
    obtain ⟨M, hM⟩ := hks F _ _ H
    exact ⟨M, by rw [betaPeel_nil]; exact hM⟩
  | a :: rest, t, acc, res, F => by
    intro H
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      obtain ⟨F₁, hP⟩ :=
        betaPeel_ksound k hks rest body (a :: acc) res F H
      refine ⟨max F F₁, ?_⟩
      rw [betaPeel_lam]
      unfold betaPeelLam
      exact betaPeel_mono ((fueledFns mode env).whnfCore c d) _ _
        (fun _ => rfl) (fun _ => rfl) (Nat.le_max_right F F₁) hP
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht] at H
      obtain ⟨M, hM⟩ := hks F _ _ H
      exact ⟨M, by rw [betaPeel_ne_lam _ _ _ _ ht]; exact hM⟩
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- One loop *step* whose continuation is sound is reproduced by the
chained specification body `whnfCoreBody` at some knot fuel. -/
theorem whnfCoreStepM_sound {d : Nat} (k : Expr → FueledM Expr)
    (hks : KSound mode env c d k) {e res : Expr} (F : Nat)
    (H : whnfCoreStepM mode (pureFns mode env F) env c d (fun x => (k x).val F) e
      = .ok res) :
    ∃ F', whnfCoreBody mode (pureFns mode env F') env c d e = .ok res := by
  cases e with
  | bvar j => exact absurd H (by simp [whnfCoreStepM])
  | sort u => exact ⟨F, H⟩
  | fvar idx ty => exact ⟨F, H⟩
  | const nm us => exact ⟨F, H⟩
  | lit l => exact ⟨F, H⟩
  | lam ty bd => exact ⟨F, H⟩
  | forallE ty bd => exact ⟨F, H⟩
  | letE ty v bd =>
    -- ζ: the body at the value
    simp only [whnfCoreStepM] at H
    obtain ⟨M, hM⟩ := hks F _ _ H
    exact ⟨M, by simp only [whnfCoreBody, whnfCore_def]; exact hM⟩
  | app f a =>
    simp only [whnfCoreStepM] at H
    obtain ⟨vh, hvh, H⟩ := bind_ok H
    obtain ⟨F₁, hP⟩ := whnfApp_ksound k hks _ vh res F H
    obtain ⟨F₂, hQ⟩ := whnfApp_sound (Expr.app f a).getAppArgs
      (Expr.app f a).getAppFn vh res F F₁ hvh hP
    rw [Expr.mkAppN_getApp] at hQ
    cases F₂ with
    | zero => rw [whnfCore_zero] at hQ; exact nomatch hQ
    | succ G => exact ⟨G, by rw [← whnfCore_succ]; exact hQ⟩
  | proj sn i pe =>
    cases c with
    | false =>
      simp only [whnfCoreStepM, Bool.false_eq_true, ↓reduceIte] at H
      obtain ⟨w, hw, H⟩ := bind_ok H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | none =>
        refine ⟨F, ?_⟩
        simp only [whnfCoreBody, Bool.false_eq_true, ↓reduceIte]
        rw [hw, ok_bind, ho, ok_bind]
        exact H
      | some m' =>
        obtain ⟨M, hM⟩ := hks F _ _ H
        refine ⟨max F M, ?_⟩
        simp only [whnfCoreBody, Bool.false_eq_true, ↓reduceIte]
        rw [whnf_def, whnf_mono (Nat.le_max_left F M) hw, ok_bind,
          reduceProjCore_mono (Nat.le_max_left F M) ho, ok_bind]
        dsimp only
        rw [whnfCore_def]
        exact whnfCore_mono (Nat.le_max_right F M) hM
    | true =>
      simp only [whnfCoreStepM, ↓reduceIte] at H
      obtain ⟨w, hw, H⟩ := bind_ok H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | none =>
        refine ⟨F, ?_⟩
        simp only [whnfCoreBody, ↓reduceIte]
        rw [hw, ok_bind, ho, ok_bind]
        exact H
      | some m' =>
        obtain ⟨M, hM⟩ := hks F _ _ H
        refine ⟨max F M, ?_⟩
        simp only [whnfCoreBody, ↓reduceIte]
        rw [whnfCore_def, whnfCore_mono (Nat.le_max_left F M) hw, ok_bind,
          reduceProjCore_mono (Nat.le_max_left F M) ho, ok_bind]
        dsimp only
        rw [whnfCore_def]
        exact whnfCore_mono (Nat.le_max_right F M) hM

/-! ### The step-returning mirrors are the continuation-passing ones

Every continuation call of `whnfApp`/`betaPeel`/`whnfCoreStepM` is a
tail call, so each is its step-returning mirror followed by
`WhnfStep.run` (task #342 R2). -/

mutual

theorem whnfApp_run {d F : Nat} (kF : Expr → CheckM Expr) :
    ∀ (xs : List Expr) (v : Expr),
      whnfApp mode (pureFns mode env F) env d kF v xs
        = whnfAppW mode (pureFns mode env F) env d v xs >>= WhnfStep.run kF
  | [], v => by rw [whnfApp_nil, whnfAppW_nil]; rfl
  | a :: rest, v => by
    by_cases hlam : ∃ ty body, v = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [whnfApp_lam, whnfAppW_lam]
      unfold whnfAppLam
      exact betaPeel_run kF rest body [a]
    · have hv : ∀ ty body, v ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [whnfApp_ne_lam _ _ _ _ hv, whnfAppW_ne_lam _ _ _ hv]
      unfold whnfAppIota
      cases ho : iotaRec mode (pureFns mode env F) env d (.app v a) with
      | error err => rfl
      | ok o =>
        cases o with
        | some e'' => rfl
        | none => exact whnfApp_run kF rest (.app v a)
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_run {d F : Nat} (kF : Expr → CheckM Expr) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr),
      betaPeel mode (pureFns mode env F) env d kF t acc xs
        = betaPeelW mode (pureFns mode env F) env d t acc xs >>= WhnfStep.run kF
  | [], t, acc => by rw [betaPeel_nil, betaPeelW_nil]; rfl
  | a :: rest, t, acc => by
    by_cases hlam : ∃ ty body, t = Expr.lam ty body
    · obtain ⟨ty, body, rfl⟩ := hlam
      rw [betaPeel_lam, betaPeelW_lam]
      unfold betaPeelLam
      exact betaPeel_run kF rest body (a :: acc)
    · have ht : ∀ ty body, t ≠ Expr.lam ty body :=
        fun ty b hh => hlam ⟨ty, b, hh⟩
      rw [betaPeel_ne_lam _ _ _ _ ht, betaPeelW_ne_lam _ _ _ ht]
      rfl
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

theorem whnfCoreStepM_run {d F : Nat} (kF : Expr → CheckM Expr) (e : Expr) :
    whnfCoreStepM mode (pureFns mode env F) env c d kF e
      = whnfCoreStepW mode (pureFns mode env F) env c d e >>= WhnfStep.run kF := by
  cases e with
  | app f a =>
    simp only [whnfCoreStepM, whnfCoreStepW]
    cases h : (pureFns mode env F).whnfCore c d (Expr.app f a).getAppFn with
    | error err => rfl
    | ok vh => exact whnfApp_run kF _ vh
  | proj sn i pe =>
    cases c with
    | false =>
      simp only [whnfCoreStepM, whnfCoreStepW, Bool.false_eq_true, ↓reduceIte]
      cases hw : (pureFns mode env F).whnf d pe with
      | error err => rfl
      | ok w =>
        simp only [Bind.bind, Except.bind]
        cases ho : reduceProjCore mode (pureFns mode env F) env d sn i w with
        | error err => rfl
        | ok o => cases o <;> rfl
    | true =>
      simp only [whnfCoreStepM, whnfCoreStepW, ↓reduceIte]
      cases hw : (pureFns mode env F).whnfCore true d pe with
      | error err => rfl
      | ok w =>
        simp only [Bind.bind, Except.bind]
        cases ho : reduceProjCore mode (pureFns mode env F) env d sn i w with
        | error err => rfl
        | ok o => cases o <;> rfl
  | _ => rfl

/-- `KSound` for the loop mirror itself: by induction on the step
budget.  This is the bridge the cached walk composes with — a
successful *loop* run is reproduced by the chained specification at
some knot fuel, so `whnfCoreBody` (and everything above it) never sees
the loop. -/
theorem whnfCoreLoopM_ksound {d : Nat} :
    ∀ (n : Nat),
      KSound mode env c d (fun e => whnfCoreLoopM mode (fueledFns mode env) env c d n e)
  | 0 => by
    intro G e v h
    rw [whnfCoreLoopM_atF c d 0 e G] at h
    exact absurd h (by simp [whnfCoreLoopM])
  | n + 1 => by
    intro G e v h
    rw [whnfCoreLoopM_atF c d (n + 1) e G] at h
    have h' : whnfCoreStepM mode (pureFns mode env G) env c d
        (whnfCoreLoopM mode (pureFns mode env G) env c d n) e = .ok v := by
      rw [whnfCoreStepM_run]
      simp only [whnfCoreLoopM] at h
      exact h
    obtain ⟨F', hF'⟩ :=
      whnfCoreStepM_sound (env := env) (d := d)
        (fun x => whnfCoreLoopM mode (fueledFns mode env) env c d n x)
        (whnfCoreLoopM_ksound n) (e := e) (res := v) G
        (by
          rw [show (fun x => (whnfCoreLoopM mode (fueledFns mode env) env c d n x).val G)
              = whnfCoreLoopM mode (pureFns mode env G) env c d n from
            funext fun x => whnfCoreLoopM_atF c d n x G]
          exact h')
    exact ⟨F' + 1, by rw [whnfCore_succ]; exact hF'⟩

/-- The bridge the cached walk uses: a successful *loop* run at the
fueled record is reproduced by `whnfCoreBody` on the same node, at
some knot fuel. -/
theorem whnfCoreLoop_sound_body (d : Nat) (e vres : Expr) (n F : Nat)
    (H : (whnfCoreLoopM mode (fueledFns mode env) env c d n e).val F = .ok vres) :
    ∃ F', (whnfCoreBody mode (fueledFns mode env) env c d e).val F' = .ok vres := by
  obtain ⟨M, hM⟩ := whnfCoreLoopM_ksound n F e vres H
  cases M with
  | zero => rw [whnfCore_zero] at hM; exact nomatch hM
  | succ G =>
    exact ⟨G, by rw [whnfCoreBody_atF, ← whnfCore_succ]; exact hM⟩

end Sound

/-! ## The application-inference spine loop (task #50)

Same construction for `inferBody`'s app case: the type of an
application spine is inferred by walking the Π-telescope with deferred
substitution — syntactic `∀`-binders are peeled against the arguments
(each argument checked against its *substituted domain* only), the
codomain substituted once per peeled group; a non-syntactic telescope
step substitutes and normalizes, exactly like the chained body. -/

/-- The continuation of `inferBody`'s app case after the function
part's inference. -/
def inferStep (r : CoreFns m) (depth : Nat) (tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE ty body => do
    let ta ← r.infer depth a
    unless ← defeqArg r depth a ta ty do
      throw (.invalid "application type mismatch")
    pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- `inferStep` with the bv_decide skip (task #368):
`inferBody`'s own continuation. -/
def inferStepS (r : CoreFns m) (env : Env) (depth : Nat) (f tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE ty body => do
    if bvUnsatSkip env.find? env.findProj? f a body then pure (body.instantiate1 a) else
    let ta ← r.infer depth a
    unless ← defeqArg r depth a ta ty do
      throw (.invalid "application type mismatch")
    pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- `inferBody`'s app case at the pure knot is one inference followed
by `inferStepS` (stated at `CheckM`, where the do-notation reduces). -/
theorem inferBody_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBody (pureFns mode env F) env depth (.app f a)
      = (pureFns mode env F).infer depth f >>= fun tf =>
          inferStepS (pureFns mode env F) env depth f tf a := by rfl

/-- A checked step's answer is the skipping step's: the skip returns the
same type without the argument check. -/
theorem inferStepS_of_inferStep {env : Env} {F d : Nat} {f tf a v : Expr}
    (h : inferStep (pureFns mode env F) d tf a = .ok v) :
    inferStepS (pureFns mode env F) env d f tf a = .ok v := by
  unfold inferStep at h
  unfold inferStepS
  cases hw : (pureFns mode env F).whnf d tf with
  | error e => rw [hw] at h; exact nomatch h
  | ok w =>
    rw [hw] at h
    simp only [bind, Except.bind] at h ⊢
    cases w with
    | forallE ty body =>
      dsimp only at h ⊢
      by_cases hsk : bvUnsatSkip env.find? env.findProj? f a body = true
      · rw [ite_eq_left hsk]
        cases hta : (pureFns mode env F).infer d a with
        | error e => rw [hta] at h; exact nomatch h
        | ok ta =>
          rw [hta] at h
          dsimp only at h
          cases hb : defeqArg (pureFns mode env F) d a ta ty with
          | error e => rw [hb] at h; exact nomatch h
          | ok b =>
            rw [hb] at h
            cases b <;> simp_all [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
      · rw [ite_eq_right hsk]; exact h
    | _ => exact h

/-- Pure mirror of the cached inference spine loop `inferSpineI`:
`ty` is the raw Π-telescope after the binders consumed so far, `acc`
their arguments (innermost first). -/
@[expose] def inferSpine (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE dom body => do
      let ta ← r.infer depth a
      unless ← defeqArg r depth a ta (dom.instantiateList acc) do
        throw (.invalid "application type mismatch")
      inferSpine r depth body (a :: acc) rest
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE dom body => do
        let ta ← r.infer depth a
        unless ← defeqArg r depth a ta dom do
          throw (.invalid "application type mismatch")
        inferSpine r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpine`. -/
@[expose] def inferSpinePi (r : CoreFns m) (depth : Nat) (dom body : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    m Expr := do
  let ta ← r.infer depth a
  unless ← defeqArg r depth a ta (dom.instantiateList acc) do
    throw (.invalid "application type mismatch")
  inferSpine r depth body (a :: acc) rest

/-- The normalize-and-retry arm of `inferSpine`. -/
@[expose] def inferSpineWhnf (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) : m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE dom body => do
    let ta ← r.infer depth a
    unless ← defeqArg r depth a ta dom do
      throw (.invalid "application type mismatch")
    inferSpine r depth body [a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpine_nil (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) :
    inferSpine r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpine]

theorem inferSpine_pi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (acc : List Expr) (a : Expr)
    (rest : List Expr) :
    inferSpine r depth (.forallE dom body) acc (a :: rest)
      = inferSpinePi r depth dom body acc a rest := by
  rw [inferSpine, inferSpinePi]

theorem inferSpine_ne_pi (r : CoreFns m) (depth : Nat) {ty : Expr}
    (hty : ∀ dom body, ty ≠ .forallE dom body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpine r depth ty acc (a :: rest)
      = inferSpineWhnf r depth ty acc a rest := by
  cases ty with
  | forallE dom body => exact absurd rfl (hty dom body)
  | _ => rw [inferSpine, inferSpineWhnf] <;> exact fun _ _ h => nomatch h

/-- The bulk substitution of a `∀`, exposed. -/
theorem instList_forallE (dom body : Expr)
    (acc : List Expr) :
    (Expr.forallE dom body).instantiateList acc
      = .forallE (dom.instantiateList acc)
          (body.instantiateList acc 1) := by
  simp [Expr.instantiateList]

section InferAtF

variable {env : Env}

theorem inferStep_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStep (fueledFns mode env) d tf a).val F
      = inferStep (pureFns mode env F) d tf a := by
  unfold inferStep
  atF_tac4

theorem inferSpine_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpine (fueledFns mode env) d ty acc xs).val F
        = inferSpine (pureFns mode env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpine_nil, inferSpine_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpine_pi, inferSpine_pi]
      unfold inferSpinePi
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      · exact defeqArg_atF d a ta _ F
      funext b
      cases b with
      | true =>
        show (inferSpine (fueledFns mode env) d body (a :: acc) rest).val F = _
        rw [inferSpine_atF d rest body (a :: acc) F]
        rfl
      | false => rfl
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpine_ne_pi _ _ hty, inferSpine_ne_pi _ _ hty]
      unfold inferSpineWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE dom body =>
        dsimp only
        rw [FueledM.atF_bind]
        congr 1
        funext ta
        rw [FueledM.atF_bind]
        congr 1
        · exact defeqArg_atF d a ta _ F
        funext b
        cases b with
        | true =>
          show (inferSpine (fueledFns mode env) d body [a] rest).val F = _
          rw [inferSpine_atF d rest body [a] F]
          rfl
        | false => rfl
      | _ => rfl

theorem inferSpine_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpine (pureFns mode env F) d ty acc xs = .ok res) :
    inferSpine (pureFns mode env F') d ty acc xs = .ok res := by
  rw [← inferSpine_atF] at h ⊢
  exact (inferSpine (fueledFns mode env) d ty acc xs).property hle h

theorem inferStep_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStep (pureFns mode env F) d tf a = .ok res) :
    inferStep (pureFns mode env F') d tf a = .ok res := by
  rw [← inferStep_atF] at h ⊢
  exact (inferStep (fueledFns mode env) d tf a).property hle h

/-- `whnf` is the identity on a `∀` (at fuel `≥ 2`: one level for the
`whnfCore` inside the loop). -/
theorem whnf_forallE (F d : Nat) (t b : Expr)
    :
    whnf mode env (F + 2) d (.forallE t b) = .ok (.forallE t b) := by
  -- one iteration of the reduction loop suffices (task #106: the step
  -- budget is `irreducible`, so peel it with its positivity witness)
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ
  rw [whnf_succ]
  show whnfLoop (pureFns mode env (F + 1)) env d whnfLoopFuel _ = _
  rw [hk]
  rfl

end InferAtF

section InferSnoc

variable {env : Env}

theorem inferSpine_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpine (pureFns mode env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpine (pureFns mode env F') d ty acc xs = .ok w ∧
        inferStep (pureFns mode env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpine_pi] at H
      unfold inferSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        rw [inferSpine_nil] at H
        injection H with h
        subst h
        refine ⟨F + 2, _, by rw [inferSpine_nil]; rfl, ?_⟩
        unfold inferStep
        rw [instList_forallE, whnf_def, whnf_forallE, ok_bind]
        dsimp only
        rw [infer_def, inferTypeCore_mono (Nat.le_add_right F 2) hta,
          ok_bind, defeqArg_mono (Nat.le_add_right F 2) hb,
          ok_bind]
        simp only [↓reduceIte]
        rw [← instList_cons0]
        rfl
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpine_nil]; rfl, ?_⟩
      unfold inferStep
      rw [whnf_def]
      show (whnf mode env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf mode env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE dom body =>
        dsimp only at H ⊢
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        rw [hta, ok_bind, hb, ok_bind]
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H ⊢
          rw [inferSpine_nil, instList_single] at H
          exact H
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpine_pi] at H
      unfold inferSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_ok H
      obtain ⟨b, hb, H⟩ := bind_ok H
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          inferSpine_snoc xs' body (x :: acc) a F vres H
        refine ⟨max F F₁, w, ?_,
          inferStep_mono (Nat.le_max_right F F₁) hstep⟩
        rw [inferSpine_pi]
        unfold inferSpinePi
        rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
          ok_bind, defeqArg_mono (Nat.le_max_left F F₁) hb,
          ok_bind]
        simp only [↓reduceIte]
        exact inferSpine_mono (Nat.le_max_right F F₁) hw
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE dom body =>
        dsimp only at H
        obtain ⟨ta, hta, H⟩ := bind_ok H
        obtain ⟨b, hb, H⟩ := bind_ok H
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H
          obtain ⟨F₁, w, hw, hstep⟩ :=
            inferSpine_snoc xs' body [x] a F vres H
          refine ⟨max F F₁, w, ?_,
            inferStep_mono (Nat.le_max_right F F₁) hstep⟩
          rw [inferSpine_ne_pi _ _ hty]
          unfold inferSpineWhnf
          rw [whnf_def]
          show (whnf mode env (max F F₁) d (ty.instantiateList acc) >>= _) = _
          rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
          dsimp only
          rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
            ok_bind, defeqArg_mono (Nat.le_max_left F F₁) hb, ok_bind]
          simp only [↓reduceIte]
          exact inferSpine_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpine_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeCore mode env F₀ d h = .ok th →
      inferSpine (pureFns mode env F) d th [] rxs.reverse = .ok vres →
      ∃ F', inferTypeCore mode env F' d (Expr.mkAppN h rxs.reverse) = .ok vres
  | [], h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, inferSpine_nil, Expr.instantiateList_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ := inferSpine_snoc rrs.reverse th [] r F vres H
    obtain ⟨F₂, hP⟩ := inferSpine_sound_rev rrs h th w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, inferTypeCore_succ,
      inferBody_app_pure, infer_def,
      inferTypeCore_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    exact inferStepS_of_inferStep (inferStep_mono (Nat.le_max_right F₂ F₁) hstep)

/-- A successful inference-spine run over the head's inferred type is
reproduced by the chained inference on the whole application, at some
fuel. -/
theorem inferSpine_sound {d : Nat} (xs : List Expr) (h th vres : Expr)
    (F₀ F : Nat) (hh : inferTypeCore mode env F₀ d h = .ok th)
    (H : inferSpine (pureFns mode env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeCore mode env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpine_sound_rev (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the cached walk uses. -/
theorem inferSpine_sound_body (d : Nat) (fx ax : Expr) (vres : Expr)
    (F : Nat)
    (H : ((fueledFns mode env).infer d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpine (fueledFns mode env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBody (fueledFns mode env) env d (.app fx ax)).val F'
      = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨th, hth, H⟩ := bind_ok H
  rw [inferSpine_atF] at H
  obtain ⟨F', hP⟩ := inferSpine_sound (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn th vres F F hth H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [inferTypeCore_zero] at hP
    exact nomatch hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [inferBody_atF, ← inferTypeCore_succ]
    exact hP

/-- **The skipped `U E C a` spine** (task #368):
the cached walk's bv branch — `U E C`'s type by the spine, its
whnf, the skip, the rest of the spine — is the chained inference. -/
theorem inferBody_bvUnsat_sound (d : Nat) {E C a tf t1 ty body v : Expr} {rest : List Expr}
    {F1 F2 F3 F4 : Nat}
    (h1 : inferTypeCore mode env F1 d (.const unsatThmName []) = .ok tf)
    (h2 : inferSpine (pureFns mode env F2) d tf [] [E, C] = .ok t1)
    (h3 : whnf mode env F3 d t1 = .ok (.forallE ty body))
    (hsk : bvUnsatSkip env.find? env.findProj? (.app (.app (.const unsatThmName []) E) C) a body = true)
    (h4 : inferSpine (pureFns mode env F4) d (body.instantiate1 a) [] rest = .ok v) :
    ∃ F', inferTypeCore mode env F' d
      (Expr.mkAppN (.const unsatThmName []) (E :: C :: a :: rest)) = .ok v := by
  obtain ⟨Fa, ha⟩ := inferSpine_sound [E, C] _ tf t1 F1 F2 h1 h2
  change inferTypeCore mode env Fa d (.app (.app (.const unsatThmName []) E) C) = .ok t1 at ha
  have hg : inferTypeCore mode env (max Fa F3 + 1) d
      (.app (.app (.app (.const unsatThmName []) E) C) a) = .ok (body.instantiate1 a) := by
    rw [inferTypeCore_succ, inferBody_app_pure, infer_def,
      inferTypeCore_mono (Nat.le_max_left Fa F3) ha, ok_bind]
    unfold inferStepS
    rw [whnf_def, whnf_mono (Nat.le_max_right Fa F3) h3, ok_bind]
    simp only [hsk, ite_true]
    rfl
  exact inferSpine_sound rest _ _ v _ F4 hg h4

end InferSnoc

section InferIOSpine

/-! ## The io-grade spine (task #172 B4, task #346)

The io twins of `inferStep`/`inferSpine` and their identification
with the io inference body over the io-grade view: what the cached
walks consume at the application clause.  The io grade is official's
`infer_only`: no argument is inferred or compared.  Everything is
stated over the knot's io *slot* family (`inferTypeIO` /
`CoreFns.inferIO`), which is the io lane (`inferTypeIO_on`). -/

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The io continuation of the application clause: the head's type
reduces to a `∀`, whose body at the argument is the result. -/
def inferStepIO (r : CoreFns m) (depth : Nat)
    (tf a : Expr) : m Expr := do
  match ← r.whnf depth tf with
  | .forallE _ body => pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- The io-grade spine mirror (the cached `inferSpineIOI`'s pure
twin): no argument is checked. -/
@[expose] def inferSpineIO (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE _ body => inferSpineIO r depth body (a :: acc) rest
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE _ body => inferSpineIO r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpineIO`. -/
@[expose] def inferSpineIOPi (r : CoreFns m) (depth : Nat)
    (body : Expr) (acc : List Expr) (a : Expr)
    (rest : List Expr) : m Expr :=
  inferSpineIO r depth body (a :: acc) rest

/-- The normalize-and-retry arm of `inferSpineIO`. -/
@[expose] def inferSpineIOWhnf (r : CoreFns m) (depth : Nat)
    (ty : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE _ body => inferSpineIO r depth body [a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpineIO_nil (r : CoreFns m) (depth : Nat)
    (ty : Expr) (acc : List Expr) :
    inferSpineIO r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpineIO]

theorem inferSpineIO_pi (r : CoreFns m) (depth : Nat)
    (dom body : Expr) (acc : List Expr)
    (a : Expr) (rest : List Expr) :
    inferSpineIO r depth (.forallE dom body) acc (a :: rest)
      = inferSpineIOPi r depth body acc a rest := by
  rw [inferSpineIO, inferSpineIOPi]

theorem inferSpineIO_ne_pi (r : CoreFns m) (depth : Nat)
    {ty : Expr} (hty : ∀ dom body, ty ≠ .forallE dom body)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpineIO r depth ty acc (a :: rest)
      = inferSpineIOWhnf r depth ty acc a rest := by
  cases ty with
  | forallE dom body => exact absurd rfl (hty dom body)
  | _ => rw [inferSpineIO, inferSpineIOWhnf] <;>
      exact fun _ _ h => nomatch h

end InferIOSpine

section InferIOAtF

variable {mode : CheckMode} {env : Env}

theorem inferStepIO_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStepIO (fueledFns mode env) d tf a).val F
      = inferStepIO (pureFns mode env F) d tf a := by
  unfold inferStepIO
  atF_tac4

theorem inferSpineIO_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpineIO (fueledFns mode env) d ty acc xs).val F
        = inferSpineIO (pureFns mode env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpineIO_nil, inferSpineIO_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpineIO_pi, inferSpineIO_pi]
      unfold inferSpineIOPi
      exact inferSpineIO_atF d rest body (a :: acc) F
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty, inferSpineIO_ne_pi _ _ hty]
      unfold inferSpineIOWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE dom body => exact inferSpineIO_atF d rest body [a] F
      | _ => rfl

theorem inferSpineIO_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpineIO (pureFns mode env F) d ty acc xs = .ok res) :
    inferSpineIO (pureFns mode env F') d ty acc xs = .ok res := by
  rw [← inferSpineIO_atF] at h ⊢
  exact (inferSpineIO (fueledFns mode env) d ty acc xs).property hle h

theorem inferStepIO_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStepIO (pureFns mode env F) d tf a = .ok res) :
    inferStepIO (pureFns mode env F') d tf a = .ok res := by
  rw [← inferStepIO_atF] at h ⊢
  exact (inferStepIO (fueledFns mode env) d tf a).property hle h

/-- The io inference body's app case over the io-grade view is one
io-slot inference followed by `inferStepIO` (stated at `CheckM`). -/
theorem inferBodyIO_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBodyIO (CoreFns.ioView (pureFns mode env F)) env depth
        (.app f a)
      = (pureFns mode env F).inferIO depth f >>= fun tf =>
          inferStepIO (CoreFns.ioView (pureFns mode env F)) depth
            tf a := by rfl

/-- The io mirrors read only `whnf`, `inferIO` and `defeq`, none of
which the io-grade view touches, so the view is transparent to them. -/
theorem inferStepIO_ioView (F d : Nat) (tf a : Expr) :
    inferStepIO (CoreFns.ioView (pureFns mode env F)) d tf a
      = inferStepIO (pureFns mode env F) d tf a := by rfl

end InferIOAtF

section InferIOSnoc

variable {mode : CheckMode} {env : Env}

theorem inferSpineIO_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpineIO (pureFns mode env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpineIO (pureFns mode env F') d ty acc xs = .ok w ∧
        inferStepIO (pureFns mode env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpineIO_pi] at H
      unfold inferSpineIOPi at H
      refine ⟨F + 2, _, by rw [inferSpineIO_nil]; rfl, ?_⟩
      unfold inferStepIO
      rw [instList_forallE, whnf_def, whnf_forallE, ok_bind]
      dsimp only
      rw [inferSpineIO_nil] at H
      injection H with h1
      subst h1
      rw [← instList_cons0]
      rfl
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty] at H
      unfold inferSpineIOWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpineIO_nil]; rfl, ?_⟩
      unfold inferStepIO
      rw [whnf_def]
      show (whnf mode env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf mode env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE dom body =>
        dsimp only at H ⊢
        rw [inferSpineIO_nil, instList_single] at H
        exact H
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ dom body, ty = Expr.forallE dom body
    · obtain ⟨dom, body, rfl⟩ := hpi
      rw [inferSpineIO_pi] at H
      unfold inferSpineIOPi at H
      obtain ⟨F₁, w, hw, hstep⟩ :=
        inferSpineIO_snoc xs' body (x :: acc) a F vres H
      refine ⟨F₁, w, ?_, hstep⟩
      rw [inferSpineIO_pi]
      unfold inferSpineIOPi
      exact hw
    · have hty : ∀ dom body, ty ≠ Expr.forallE dom body :=
        fun dom b hh => hpi ⟨dom, b, hh⟩
      rw [inferSpineIO_ne_pi _ _ hty] at H
      unfold inferSpineIOWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE dom body =>
        dsimp only at H
        obtain ⟨F₁, w, hw, hstep⟩ :=
          inferSpineIO_snoc xs' body [x] a F vres H
        refine ⟨max F F₁, w, ?_,
          inferStepIO_mono (Nat.le_max_right F F₁) hstep⟩
        rw [inferSpineIO_ne_pi _ _ hty]
        unfold inferSpineIOWhnf
        rw [whnf_def]
        show (whnf mode env (max F F₁) d (ty.instantiateList acc) >>= _) = _
        rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
        exact inferSpineIO_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam t b => exact nomatch H
      | letE t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpineIO_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeIO mode env F₀ d h = .ok th →
      inferSpineIO (pureFns mode env F) d th [] rxs.reverse
        = .ok vres →
      ∃ F', inferTypeIO mode env F' d (Expr.mkAppN h rxs.reverse)
        = .ok vres
  | [], h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_nil, inferSpineIO_nil, Expr.instantiateList_nil] at H
    injection H with h1
    subst h1
    exact ⟨F₀, hh⟩
  | r :: rrs, h, th, vres, F₀, F => by
    intro hh H
    rw [List.reverse_cons] at H
    obtain ⟨F₁, w, hw, hstep⟩ :=
      inferSpineIO_snoc rrs.reverse th [] r F vres H
    obtain ⟨F₂, hP⟩ := inferSpineIO_sound_rev rrs h th w F₀ F₁ hh hw
    refine ⟨max F₂ F₁ + 1, ?_⟩
    rw [List.reverse_cons, Expr.mkAppN_append_one, inferTypeIO_succ,
      inferBodyIO_app_pure]
    rw [show (pureFns mode env (max F₂ F₁)).inferIO d
        (Expr.mkAppN h rrs.reverse)
      = inferTypeIO mode env (max F₂ F₁) d (Expr.mkAppN h rrs.reverse)
      from rfl]
    rw [inferTypeIO_mono (Nat.le_max_left F₂ F₁) hP, ok_bind]
    rw [inferStepIO_ioView]
    exact inferStepIO_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful io-spine run over the head's io-inferred type is
reproduced by the chained io slot on the whole application, at some
fuel. -/
theorem inferSpineIO_sound {d : Nat}
    (xs : List Expr) (h th vres : Expr) (F₀ F : Nat)
    (hh : inferTypeIO mode env F₀ d h = .ok th)
    (H : inferSpineIO (pureFns mode env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeIO mode env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpineIO_sound_rev (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the cached io walk uses. -/
theorem inferSpineIO_sound_body (d : Nat)
    (fx ax : Expr) (vres : Expr) (F : Nat)
    (H : ((fueledFns mode env).inferIO d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpineIO (fueledFns mode env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d
      (.app fx ax)).val F' = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨th, hth, H⟩ := bind_ok H
  rw [inferSpineIO_atF] at H
  obtain ⟨F', hP⟩ := inferSpineIO_sound (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn th vres F F hth H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [inferTypeIO_zero] at hP
    simp [throw, throwThe, MonadExceptOf.throw] at hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [inferBodyIO_atF]
    rw [inferTypeIO_succ] at hP
    exact hP

end InferIOSnoc

end ConLeche
