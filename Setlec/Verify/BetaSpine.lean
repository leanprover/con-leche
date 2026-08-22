import Setlec.Verify.Fueled
import Setlec.Verify.Knot
import Setlec.Verify.InstList
import Setlec.Verify.InferLemmas

/-!
# Bulk beta: the spine loop and its identification with `whnfCoreBody`
(task #50)

The interned twin's app case (`whnfAppI`/`betaPeelI`,
`Setlec/Kernel/CoreI.lean`) consumes a whole application spine in one
loop, batching consecutive lambda binders into a single bulk
substitution.  This file provides the pure mirrors (`whnfApp` /
`betaPeel`, generic over the core record like every helper) and proves
the **soundness of the loop against the chained spec**: a successful
loop run at the pure fueled knot is reproduced by the original
one-argument-at-a-time `whnfCoreBody` recursion at some fuel
(`whnfApp_sound_body`).  The interned walk (`Setlec/Verify/DiscI4`)
composes its simulation against the mirror with this theorem, so the
`Expr`-level specification — and everything above it — is unchanged.

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

namespace Setlec

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The continuation of `whnfCoreBody`'s app case after the function
part's head normalization: beta with the possibly-Prop certificate on
a lambda, iota otherwise. -/
def appStep (r : CoreFns m) (env : Env) (depth : Nat) (w a : Expr) :
    m Expr :=
  match w with
  | .lam n ty body mb =>
    match mb.cod with
    | some v =>
      if v.isNonZero then r.whnfCore depth (body.instantiate1 a)
      else do
        let ta ← r.infer depth a
        if ← r.defeq depth ta ty then
          r.whnfCore depth (body.instantiate1 a)
        else pure (.app (.lam n ty body mb) a)
    | none => pure (.app (.lam n ty body mb) a)
  | f' => do
    match ← iotaRec r env depth (.app f' a) with
    | some e'' => r.whnfCore depth e''
    | none => pure (.app f' a)

/-- `whnfCoreBody`'s app case is one head normalization followed by
`appStep`. -/
theorem whnfCoreBody_app (r : CoreFns m) (env : Env) (depth : Nat)
    (f a : Expr) :
    whnfCoreBody r env depth (.app f a)
      = r.whnfCore depth f >>= fun w => appStep r env depth w a := rfl

mutual

/-- Pure mirror of the interned bulk-beta loop `whnfAppI`: consume the
spine against the whnf'd head. -/
def whnfApp (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → m Expr
  | v, [] => pure v
  | v, a :: rest =>
    match v with
    | .lam n ty body mb =>
      match mb.cod with
      | some lv =>
        if lv.isNonZero then betaPeel r env depth body [a] rest
        else do
          let ta ← r.infer depth a
          if ← r.defeq depth ta ty then betaPeel r env depth body [a] rest
          else pure (Expr.mkAppN (.app (.lam n ty body mb) a) rest)
      | none => pure (Expr.mkAppN (.app (.lam n ty body mb) a) rest)
    | v => do
      match ← iotaRec r env depth (.app v a) with
      | some e'' => do
        let v' ← r.whnfCore depth e''
        whnfApp r env depth v' rest
      | none => whnfApp r env depth (.app v a) rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Pure mirror of the interned peel loop `betaPeelI`: `t` is the raw
lambda body after the binders consumed so far, `acc` their arguments
(innermost first). -/
def betaPeel (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | t, acc, [] => r.whnfCore depth (t.instantiateList acc)
  | t, acc, a :: rest =>
    match t with
    | .lam n ty body mb =>
      match mb.cod with
      | some lv =>
        if lv.isNonZero then betaPeel r env depth body (a :: acc) rest
        else do
          let ta ← r.infer depth a
          if ← r.defeq depth ta (ty.instantiateList acc) then
            betaPeel r env depth body (a :: acc) rest
          else pure (Expr.mkAppN
            (.app ((Expr.lam n ty body mb).instantiateList acc) a) rest)
      | none => pure (Expr.mkAppN
          (.app ((Expr.lam n ty body mb).instantiateList acc) a) rest)
    | t => do
      let v ← r.whnfCore depth (t.instantiateList acc)
      whnfApp r env depth v (a :: rest)
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
def whnfAppIota (r : CoreFns m) (env : Env) (depth : Nat)
    (v a : Expr) (rest : List Expr) : m Expr := do
  match ← iotaRec r env depth (.app v a) with
  | some e'' => do
    let v' ← r.whnfCore depth e''
    whnfApp r env depth v' rest
  | none => whnfApp r env depth (.app v a) rest

/-- The lambda arm of `whnfApp` (first binder of the peel), as a
standalone computation. -/
def whnfAppLam (r : CoreFns m) (env : Env) (depth : Nat)
    (n : Name) (ty body : Expr) (mb : BinderMeta) (a : Expr)
    (rest : List Expr) : m Expr :=
  match mb.cod with
  | some lv =>
    if lv.isNonZero then betaPeel r env depth body [a] rest
    else do
      let ta ← r.infer depth a
      if ← r.defeq depth ta ty then betaPeel r env depth body [a] rest
      else pure (Expr.mkAppN (.app (.lam n ty body mb) a) rest)
  | none => pure (Expr.mkAppN (.app (.lam n ty body mb) a) rest)

theorem whnfApp_nil (r : CoreFns m) (env : Env) (depth : Nat) (v : Expr) :
    whnfApp r env depth v [] = pure v := by
  rw [whnfApp]

theorem whnfApp_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (n : Name) (ty body : Expr) (mb : BinderMeta) (a : Expr)
    (rest : List Expr) :
    whnfApp r env depth (.lam n ty body mb) (a :: rest)
      = whnfAppLam r env depth n ty body mb a rest := by
  rw [whnfApp, whnfAppLam]

theorem whnfApp_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    {v : Expr} (hv : ∀ n ty body mb, v ≠ .lam n ty body mb)
    (a : Expr) (rest : List Expr) :
    whnfApp r env depth v (a :: rest)
      = whnfAppIota r env depth v a rest := by
  cases v with
  | lam n ty body mb => exact absurd rfl (hv n ty body mb)
  | _ => rw [whnfApp, whnfAppIota] <;> exact fun _ _ _ _ h => nomatch h

/-- The non-lambda arm of `betaPeel` for a raw body that is not a
lambda: substitute and hand back to the argument loop. -/
theorem betaPeel_ne_lam (r : CoreFns m) (env : Env) (depth : Nat)
    {t : Expr} (ht : ∀ n ty body mb, t ≠ .lam n ty body mb)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    betaPeel r env depth t acc (a :: rest)
      = r.whnfCore depth (t.instantiateList acc) >>= fun v =>
          whnfApp r env depth v (a :: rest) := by
  cases t with
  | lam n ty body mb => exact absurd rfl (ht n ty body mb)
  | _ => rw [betaPeel] <;> exact fun _ _ _ _ h => nomatch h

theorem betaPeel_nil (r : CoreFns m) (env : Env) (depth : Nat)
    (t : Expr) (acc : List Expr) :
    betaPeel r env depth t acc []
      = r.whnfCore depth (t.instantiateList acc) := by
  rw [betaPeel]

/-- The lambda arm of `betaPeel` (peel one more binder). -/
def betaPeelLam (r : CoreFns m) (env : Env) (depth : Nat)
    (n : Name) (ty body : Expr) (mb : BinderMeta) (acc : List Expr)
    (a : Expr) (rest : List Expr) : m Expr :=
  match mb.cod with
  | some lv =>
    if lv.isNonZero then betaPeel r env depth body (a :: acc) rest
    else do
      let ta ← r.infer depth a
      if ← r.defeq depth ta (ty.instantiateList acc) then
        betaPeel r env depth body (a :: acc) rest
      else pure (Expr.mkAppN
        (.app ((Expr.lam n ty body mb).instantiateList acc) a) rest)
  | none => pure (Expr.mkAppN
      (.app ((Expr.lam n ty body mb).instantiateList acc) a) rest)

theorem betaPeel_lam (r : CoreFns m) (env : Env) (depth : Nat)
    (n : Name) (ty body : Expr) (mb : BinderMeta) (acc : List Expr)
    (a : Expr) (rest : List Expr) :
    betaPeel r env depth (.lam n ty body mb) acc (a :: rest)
      = betaPeelLam r env depth n ty body mb acc a rest := by
  rw [betaPeel, betaPeelLam]

/-- `iotaRec` is `none` whenever the spine head is not a constant. -/
theorem iotaRec_head_not_const (r : CoreFns m) (env : Env) (depth : Nat)
    {e : Expr} (h : ∀ c us, e.getAppFn ≠ .const c us) :
    iotaRec r env depth e = pure none := by
  unfold iotaRec
  split
  · rename_i c us hc
    exact absurd hc (h c us)
  · rfl

/-- The spine head of a well-scoped expression is well-scoped. -/
theorem Expr.WScoped.getAppFn {d : Nat} :
    ∀ {e : Expr}, WScoped d e → WScoped d e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    have hfa : WScoped d f ∧ WScoped d a := by
      simpa only [WScoped] using h
    exact ihf hfa.1
  | _ => intro h; exact h

/-! ## `atF` equations and fuel monotonicity for the mirrors -/

section AtF

variable {env : Env}

theorem appStep_atF (d : Nat) (w a : Expr) (F : Nat) :
    (appStep (fueledFns env) env d w a).val F
      = appStep (pureFns env F) env d w a := by
  unfold appStep
  atF_tac4

mutual

theorem whnfApp_atF (d : Nat) :
    ∀ (xs : List Expr) (v : Expr) (F : Nat),
      (whnfApp (fueledFns env) env d v xs).val F
        = whnfApp (pureFns env F) env d v xs
  | [], v, F => by rw [whnfApp_nil, whnfApp_nil]; rfl
  | a :: rest, v, F => by
    by_cases hlam : ∃ n ty body mb, v = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam, whnfApp_lam]
      unfold whnfAppLam
      obtain ⟨bi, cod⟩ := mb
      dsimp only
      cases cod with
      | none => rfl
      | some lv =>
        dsimp only
        by_cases hnz : lv.isNonZero
        · rw [if_pos hnz, if_pos hnz]
          exact betaPeel_atF d rest body [a] F
        · rw [if_neg hnz, if_neg hnz]
          rw [FueledM.atF_bind]
          congr 1
          funext ta
          rw [FueledM.atF_bind]
          congr 1
          funext b
          rw [FueledM.atF_ite]
          cases b with
          | true =>
            simp only [↓reduceIte]
            exact betaPeel_atF d rest body [a] F
          | false => rfl
    · have hv : ∀ n ty body mb, v ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ hv, whnfApp_ne_lam _ _ _ hv]
      unfold whnfAppIota
      rw [FueledM.atF_bind, iotaRec_atF]
      congr 1
      funext o
      cases o with
      | some e'' =>
        rw [FueledM.atF_bind]
        congr 1
        funext v'
        exact whnfApp_atF d rest v' F
      | none => exact whnfApp_atF d rest (.app v a) F
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_atF (d : Nat) :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr) (F : Nat),
      (betaPeel (fueledFns env) env d t acc xs).val F
        = betaPeel (pureFns env F) env d t acc xs
  | [], t, acc, F => by rw [betaPeel_nil, betaPeel_nil]; rfl
  | a :: rest, t, acc, F => by
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam, betaPeel_lam]
      unfold betaPeelLam
      obtain ⟨bi, cod⟩ := mb
      dsimp only
      cases cod with
      | none => rfl
      | some lv =>
        dsimp only
        by_cases hnz : lv.isNonZero
        · rw [if_pos hnz, if_pos hnz]
          exact betaPeel_atF d rest body (a :: acc) F
        · rw [if_neg hnz, if_neg hnz]
          rw [FueledM.atF_bind]
          congr 1
          funext ta
          rw [FueledM.atF_bind]
          congr 1
          funext b
          rw [FueledM.atF_ite]
          cases b with
          | true =>
            simp only [↓reduceIte]
            exact betaPeel_atF d rest body (a :: acc) F
          | false => rfl
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ ht, betaPeel_ne_lam _ _ _ ht]
      rw [FueledM.atF_bind]
      congr 1
      funext v
      exact whnfApp_atF d (a :: rest) v F
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Fuel monotonicity of the loop (via `whnfApp_atF` and the `FueledM`
bundle). -/
theorem whnfApp_mono {d : Nat} {xs : List Expr} {v : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : whnfApp (pureFns env F) env d v xs = .ok res) :
    whnfApp (pureFns env F') env d v xs = .ok res := by
  rw [← whnfApp_atF] at h ⊢
  exact (whnfApp (fueledFns env) env d v xs).property hle h

theorem betaPeel_mono {d : Nat} {xs acc : List Expr} {t : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : betaPeel (pureFns env F) env d t acc xs = .ok res) :
    betaPeel (pureFns env F') env d t acc xs = .ok res := by
  rw [← betaPeel_atF] at h ⊢
  exact (betaPeel (fueledFns env) env d t acc xs).property hle h

theorem appStep_mono {d : Nat} {w a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : appStep (pureFns env F) env d w a = .ok res) :
    appStep (pureFns env F') env d w a = .ok res := by
  rw [← appStep_atF] at h ⊢
  exact (appStep (fueledFns env) env d w a).property hle h

theorem iotaRec_mono {d : Nat} {e : Expr} {F F' : Nat}
    (hle : F ≤ F') {o : Option Expr}
    (h : iotaRec (pureFns env F) env d e = .ok o) :
    iotaRec (pureFns env F') env d e = .ok o := by
  rw [← iotaRec_atF] at h ⊢
  exact (iotaRec (fueledFns env) env d e).property hle h

theorem inferTypeCore_det {d F₁ F₂ : Nat} {e v₁ v₂ : Expr}
    (h1 : inferTypeCore env F₁ d e = .ok v₁)
    (h2 : inferTypeCore env F₂ d e = .ok v₂) : v₁ = v₂ := by
  have g1 := inferTypeCore_mono (Nat.le_max_left F₁ F₂) h1
  have g2 := inferTypeCore_mono (Nat.le_max_right F₁ F₂) h2
  rw [g1] at g2
  exact (Except.ok.injEq .. ▸ g2)

theorem isDefEqCore_det {d F₁ F₂ : Nat} {a b : Expr} {r₁ r₂ : Bool}
    (h1 : isDefEqCore env F₁ d a b = .ok r₁)
    (h2 : isDefEqCore env F₂ d a b = .ok r₂) : r₁ = r₂ := by
  have g1 := isDefEqCore_mono (Nat.le_max_left F₁ F₂) h1
  have g2 := isDefEqCore_mono (Nat.le_max_right F₁ F₂) h2
  rw [g1] at g2
  exact (Except.ok.injEq .. ▸ g2)

theorem whnfCore_det {d F₁ F₂ : Nat} {e v₁ v₂ : Expr}
    (h1 : whnfCore env F₁ d e = .ok v₁)
    (h2 : whnfCore env F₂ d e = .ok v₂) : v₁ = v₂ := by
  have g1 := whnfCore_mono (Nat.le_max_left F₁ F₂) h1
  have g2 := whnfCore_mono (Nat.le_max_right F₁ F₂) h2
  rw [g1] at g2
  exact (Except.ok.injEq .. ▸ g2)

theorem iotaRec_det {d F₁ F₂ : Nat} {e : Expr} {o₁ o₂ : Option Expr}
    (h1 : iotaRec (pureFns env F₁) env d e = .ok o₁)
    (h2 : iotaRec (pureFns env F₂) env d e = .ok o₂) : o₁ = o₂ := by
  have g1 := iotaRec_mono (Nat.le_max_left F₁ F₂) h1
  have g2 := iotaRec_mono (Nat.le_max_right F₁ F₂) h2
  rw [g1] at g2
  exact (Except.ok.injEq .. ▸ g2)

/-- `whnfCore` is the identity on a lambda (at nonzero fuel). -/
theorem whnfCore_lam (F d : Nat) (n : Name) (ty body : Expr)
    (mb : BinderMeta) :
    whnfCore env (F + 1) d (.lam n ty body mb)
      = .ok (.lam n ty body mb) := rfl

end AtF

/-! ## The snoc decomposition -/

section Snoc

variable {env : Env}

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

/-- An application chain over an application base is never a lambda. -/
private theorem mkAppN_app_ne_lam :
    ∀ (ys : List Expr) (f a₀ : Expr) (n : Name) (ty body : Expr)
      (mb : BinderMeta), Expr.mkAppN (.app f a₀) ys ≠ .lam n ty body mb
  | [], _, _, _, _, _, _ => by exact fun h => nomatch h
  | y :: ys, f, a₀, n, ty, body, mb => by
    rw [show Expr.mkAppN (.app f a₀) (y :: ys)
      = Expr.mkAppN (.app (.app f a₀) y) ys from rfl]
    exact mkAppN_app_ne_lam ys (.app f a₀) y n ty body mb

/-- The bulk substitution of a lambda, exposed. -/
theorem instList_lam (n : Name) (ty body : Expr)
    (mb : BinderMeta) (acc : List Expr) :
    (Expr.lam n ty body mb).instantiateList acc
      = .lam n (ty.instantiateList acc) (body.instantiateList acc 1) mb := by
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

/-- `appStep` on a stuck application chain with a non-constant head:
one more stuck application. -/
private theorem appStep_stuck (F d : Nat) {w : Expr} (a : Expr)
    (hnl : ∀ n ty body mb, w ≠ Expr.lam n ty body mb)
    (hnc : ∀ c us, w.getAppFn ≠ Expr.const c us) :
    appStep (pureFns env F) env d w a = .ok (.app w a) := by
  have hiota : iotaRec (pureFns env F) env d (.app w a) = pure none := by
    refine iotaRec_head_not_const _ env d ?_
    intro c us h
    exact hnc c us h
  cases w with
  | lam n ty body mb => exact absurd rfl (hnl n ty body mb)
  | _ =>
    unfold appStep
    dsimp only
    rw [hiota]
    rfl

private theorem ok_bind {α β : Type} (a : α)
    (f : α → Except CheckError β) :
    ((Except.ok a : Except CheckError α) >>= f) = f a := rfl

mutual

theorem whnfApp_snoc {d : Nat} :
    ∀ (xs : List Expr) (v a : Expr) (F : Nat) (vres : Expr),
      whnfApp (pureFns env F) env d v (xs ++ [a]) = .ok vres →
      ∃ F' w, whnfApp (pureFns env F') env d v xs = .ok w ∧
        appStep (pureFns env F') env d w a = .ok vres
  | [], v, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hlam : ∃ n ty body mb, v = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      obtain ⟨bi, cod⟩ := mb
      dsimp only at H
      cases cod with
      | none =>
        injection H with h
        subst h
        refine ⟨F, _, by rw [whnfApp_nil]; rfl, ?_⟩
        unfold appStep
        dsimp only
        rfl
      | some lv =>
        dsimp only at H
        by_cases hnz : lv.isNonZero
        · rw [if_pos hnz, betaPeel_nil, instList_single] at H
          refine ⟨F, _, by rw [whnfApp_nil]; rfl, ?_⟩
          unfold appStep
          dsimp only
          rw [if_pos hnz]
          exact H
        · rw [if_neg hnz] at H
          obtain ⟨ta, hta, H⟩ := bind_ok H
          obtain ⟨b, hb, H⟩ := bind_ok H
          refine ⟨F, _, by rw [whnfApp_nil]; rfl, ?_⟩
          unfold appStep
          dsimp only
          rw [if_neg hnz, hta, ok_bind, hb, ok_bind]
          cases b with
          | true =>
            simp only [↓reduceIte] at H ⊢
            rw [betaPeel_nil, instList_single] at H
            exact H
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at H ⊢
            injection H with h
            subst h
            rfl
    · have hv : ∀ n ty body mb, v ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      refine ⟨F, v, by rw [whnfApp_nil]; rfl, ?_⟩
      cases v with
      | lam n ty body mb => exact absurd rfl (hv n ty body mb)
      | _ =>
        unfold appStep
        dsimp only
        rw [ho, ok_bind]
        cases o with
        | some e'' =>
          obtain ⟨v', hv', H⟩ := bind_ok H
          rw [whnfApp_nil] at H
          injection H with h
          subst h
          exact hv'
        | none =>
          rw [whnfApp_nil] at H
          injection H with h
          subst h
          rfl
  | x :: xs', v, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hlam : ∃ n ty body mb, v = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [whnfApp_lam] at H
      unfold whnfAppLam at H
      obtain ⟨bi, cod⟩ := mb
      dsimp only at H
      cases cod with
      | none =>
        injection H with h
        subst h
        refine ⟨F, Expr.mkAppN
          (.app (.lam n ty body ⟨bi, none⟩) x) xs', ?_, ?_⟩
        · rw [whnfApp_lam]
          unfold whnfAppLam
          rfl
        · rw [Expr.mkAppN_append_one]
          refine appStep_stuck F d a (mkAppN_app_ne_lam xs' _ x) ?_
          intro c us hc
          rw [Expr.getAppFn_mkAppN] at hc
          exact nomatch hc
      | some lv =>
        dsimp only at H
        by_cases hnz : lv.isNonZero
        · rw [if_pos hnz] at H
          obtain ⟨F₁, w, hw, hstep⟩ := betaPeel_snoc xs' body [x] a F vres H
          refine ⟨F₁, w, ?_, hstep⟩
          rw [whnfApp_lam]
          unfold whnfAppLam
          dsimp only
          rw [if_pos hnz]
          exact hw
        · rw [if_neg hnz] at H
          obtain ⟨ta, hta, H⟩ := bind_ok H
          obtain ⟨b, hb, H⟩ := bind_ok H
          cases b with
          | true =>
            simp only [↓reduceIte] at H
            obtain ⟨F₁, w, hw, hstep⟩ := betaPeel_snoc xs' body [x] a F vres H
            refine ⟨max F F₁, w, ?_,
              appStep_mono (Nat.le_max_right F F₁) hstep⟩
            rw [whnfApp_lam]
            unfold whnfAppLam
            dsimp only
            rw [if_neg hnz, infer_def,
              inferTypeCore_mono (Nat.le_max_left F F₁) hta, ok_bind,
              defeq_def, isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
            simp only [↓reduceIte]
            exact betaPeel_mono (Nat.le_max_right F F₁) hw
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at H
            injection H with h
            subst h
            refine ⟨F, Expr.mkAppN
              (.app (.lam n ty body ⟨bi, some lv⟩) x) xs', ?_, ?_⟩
            · rw [whnfApp_lam]
              unfold whnfAppLam
              dsimp only
              rw [if_neg hnz, hta, ok_bind, hb, ok_bind]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rfl
            · rw [Expr.mkAppN_append_one]
              refine appStep_stuck F d a (mkAppN_app_ne_lam xs' _ x) ?_
              intro c us hc
              rw [Expr.getAppFn_mkAppN] at hc
              exact nomatch hc
    · have hv : ∀ n ty body mb, v ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [whnfApp_ne_lam _ _ _ hv] at H
      unfold whnfAppIota at H
      obtain ⟨o, ho, H⟩ := bind_ok H
      cases o with
      | some e'' =>
        obtain ⟨v', hv', H⟩ := bind_ok H
        obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc xs' v' a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_ne_lam _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        rw [whnfCore_def, whnfCore_mono (Nat.le_max_left F F₁) hv', ok_bind]
        exact whnfApp_mono (Nat.le_max_right F F₁) hw
      | none =>
        obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc xs' (.app v x) a F vres H
        refine ⟨max F F₁, w, ?_,
          appStep_mono (Nat.le_max_right F F₁) hstep⟩
        rw [whnfApp_ne_lam _ _ _ hv]
        unfold whnfAppIota
        rw [iotaRec_mono (Nat.le_max_left F F₁) ho, ok_bind]
        dsimp only
        exact whnfApp_mono (Nat.le_max_right F F₁) hw
termination_by xs => (xs.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

theorem betaPeel_snoc {d : Nat} :
    ∀ (xs : List Expr) (t : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      betaPeel (pureFns env F) env d t acc (xs ++ [a]) = .ok vres →
      ∃ F' w, betaPeel (pureFns env F') env d t acc xs = .ok w ∧
        appStep (pureFns env F') env d w a = .ok vres
  | [], t, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      obtain ⟨bi, cod⟩ := mb
      dsimp only at H
      have hid : betaPeel (pureFns env (F + 1)) env d
          (Expr.lam n ty body ⟨bi, cod⟩) acc []
          = .ok (.lam n (ty.instantiateList acc)
              (body.instantiateList acc 1) ⟨bi, cod⟩) := by
        rw [betaPeel_nil, instList_lam]
        exact whnfCore_lam F d n _ _ _
      cases cod with
      | none =>
        injection H with h
        subst h
        refine ⟨F + 1, _, hid, ?_⟩
        unfold appStep
        dsimp only
        rw [instList_lam]
        rfl
      | some lv =>
        dsimp only at H
        by_cases hnz : lv.isNonZero
        · rw [if_pos hnz, betaPeel_nil] at H
          refine ⟨F + 1, _, hid, ?_⟩
          unfold appStep
          dsimp only
          rw [if_pos hnz, ← instList_cons0]
          exact whnfCore_mono (Nat.le_succ F) H
        · rw [if_neg hnz] at H
          obtain ⟨ta, hta, H⟩ := bind_ok H
          obtain ⟨b, hb, H⟩ := bind_ok H
          refine ⟨F + 1, _, hid, ?_⟩
          unfold appStep
          dsimp only
          rw [if_neg hnz, infer_def, inferTypeCore_mono (Nat.le_succ F) hta,
            ok_bind, defeq_def, isDefEqCore_mono (Nat.le_succ F) hb, ok_bind]
          cases b with
          | true =>
            simp only [↓reduceIte] at H ⊢
            rw [betaPeel_nil] at H
            rw [← instList_cons0]
            exact whnfCore_mono (Nat.le_succ F) H
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at H ⊢
            injection H with h
            subst h
            rw [instList_lam]
            rfl
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ ht] at H
      obtain ⟨v₀, hv₀, H⟩ := bind_ok H
      obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc [] v₀ a F vres H
      rw [whnfApp_nil] at hw
      injection hw with hw'
      subst hw'
      refine ⟨max F F₁, v₀, ?_,
        appStep_mono (Nat.le_max_right F F₁) hstep⟩
      rw [betaPeel_nil]
      exact whnfCore_mono (Nat.le_max_left F F₁) hv₀
  | x :: xs', t, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hlam : ∃ n ty body mb, t = Expr.lam n ty body mb
    · obtain ⟨n, ty, body, mb, rfl⟩ := hlam
      rw [betaPeel_lam] at H
      unfold betaPeelLam at H
      obtain ⟨bi, cod⟩ := mb
      dsimp only at H
      cases cod with
      | none =>
        injection H with h
        subst h
        refine ⟨F, Expr.mkAppN
          (.app ((Expr.lam n ty body ⟨bi, none⟩).instantiateList acc) x)
          xs', ?_, ?_⟩
        · rw [betaPeel_lam]
          unfold betaPeelLam
          rfl
        · rw [Expr.mkAppN_append_one]
          refine appStep_stuck F d a (mkAppN_app_ne_lam xs' _ x) ?_
          intro c us hc
          rw [Expr.getAppFn_mkAppN] at hc
          rw [show Expr.getAppFn (.app
              ((Expr.lam n ty body ⟨bi, none⟩).instantiateList acc) x)
            = Expr.getAppFn
              ((Expr.lam n ty body ⟨bi, none⟩).instantiateList acc)
            from rfl, instList_lam] at hc
          exact nomatch hc
      | some lv =>
        dsimp only at H
        by_cases hnz : lv.isNonZero
        · rw [if_pos hnz] at H
          obtain ⟨F₁, w, hw, hstep⟩ :=
            betaPeel_snoc xs' body (x :: acc) a F vres H
          refine ⟨F₁, w, ?_, hstep⟩
          rw [betaPeel_lam]
          unfold betaPeelLam
          dsimp only
          rw [if_pos hnz]
          exact hw
        · rw [if_neg hnz] at H
          obtain ⟨ta, hta, H⟩ := bind_ok H
          obtain ⟨b, hb, H⟩ := bind_ok H
          cases b with
          | true =>
            simp only [↓reduceIte] at H
            obtain ⟨F₁, w, hw, hstep⟩ :=
              betaPeel_snoc xs' body (x :: acc) a F vres H
            refine ⟨max F F₁, w, ?_,
              appStep_mono (Nat.le_max_right F F₁) hstep⟩
            rw [betaPeel_lam]
            unfold betaPeelLam
            dsimp only
            rw [if_neg hnz, infer_def,
              inferTypeCore_mono (Nat.le_max_left F F₁) hta, ok_bind,
              defeq_def, isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
            simp only [↓reduceIte]
            exact betaPeel_mono (Nat.le_max_right F F₁) hw
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at H
            injection H with h
            subst h
            refine ⟨F, Expr.mkAppN
              (.app ((Expr.lam n ty body ⟨bi, some lv⟩).instantiateList acc)
                x) xs', ?_, ?_⟩
            · rw [betaPeel_lam]
              unfold betaPeelLam
              dsimp only
              rw [if_neg hnz, hta, ok_bind, hb, ok_bind]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rfl
            · rw [Expr.mkAppN_append_one]
              refine appStep_stuck F d a (mkAppN_app_ne_lam xs' _ x) ?_
              intro c us hc
              rw [Expr.getAppFn_mkAppN] at hc
              rw [show Expr.getAppFn (.app
                  ((Expr.lam n ty body ⟨bi, some lv⟩).instantiateList acc) x)
                = Expr.getAppFn
                  ((Expr.lam n ty body ⟨bi, some lv⟩).instantiateList acc)
                from rfl, instList_lam] at hc
              exact nomatch hc
    · have ht : ∀ n ty body mb, t ≠ Expr.lam n ty body mb :=
        fun n ty b mb hh => hlam ⟨n, ty, b, mb, hh⟩
      rw [betaPeel_ne_lam _ _ _ ht] at H
      obtain ⟨v₀, hv₀, H⟩ := bind_ok H
      obtain ⟨F₁, w, hw, hstep⟩ := whnfApp_snoc (x :: xs') v₀ a F vres H
      refine ⟨max F F₁, w, ?_,
        appStep_mono (Nat.le_max_right F F₁) hstep⟩
      rw [betaPeel_ne_lam _ _ _ ht, whnfCore_def,
        whnfCore_mono (Nat.le_max_left F F₁) hv₀, ok_bind]
      exact whnfApp_mono (Nat.le_max_right F F₁) hw
termination_by xs => (xs.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

end Snoc

/-! ## Soundness of the loop against the chained body -/

section Sound

variable {env : Env}

private theorem whnfApp_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h vh vres : Expr) (F₀ F : Nat),
      whnfCore env F₀ d h = .ok vh →
      whnfApp (pureFns env F) env d vh rxs.reverse = .ok vres →
      ∃ F', whnfCore env F' d (Expr.mkAppN h rxs.reverse) = .ok vres
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
    exact appStep_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful loop run over a normalized head is reproduced by the
chained `whnfCore` recursion on the whole application, at some fuel. -/
theorem whnfApp_sound {d : Nat} (xs : List Expr) (h vh vres : Expr)
    (F₀ F : Nat) (hh : whnfCore env F₀ d h = .ok vh)
    (H : whnfApp (pureFns env F) env d vh xs = .ok vres) :
    ∃ F', whnfCore env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := whnfApp_sound_rev (d := d) xs.reverse h vh vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the interned walk uses: a successful head-normalization
plus loop run (at the fueled record) is reproduced by `whnfCoreBody`
on the application node itself. -/
theorem whnfApp_sound_body (d : Nat) (fx ax : Expr) (vres : Expr)
    (F : Nat)
    (H : ((fueledFns env).whnfCore d (Expr.app fx ax).getAppFn >>=
        fun vh => whnfApp (fueledFns env) env d vh
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (whnfCoreBody (fueledFns env) env d (.app fx ax)).val F'
      = .ok vres := by
  rw [FueledM.atF_bind] at H
  obtain ⟨vh, hvh, H⟩ := bind_ok H
  rw [whnfApp_atF] at H
  obtain ⟨F', hP⟩ := whnfApp_sound (Expr.app fx ax).getAppArgs
    (Expr.app fx ax).getAppFn vh vres F F hvh H
  rw [Expr.mkAppN_getApp] at hP
  cases F' with
  | zero =>
    rw [whnfCore_zero] at hP
    exact nomatch hP
  | succ G =>
    refine ⟨G, ?_⟩
    rw [whnfCoreBody_atF, ← whnfCore_succ]
    exact hP

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
  | .forallE _ ty body _ => do
    let ta ← r.infer depth a
    unless ← r.defeq depth ta ty do
      throw (.invalid "application type mismatch")
    pure (body.instantiate1 a)
  | _ => throw (.invalid "function expected")

/-- `inferBody`'s app case at the pure knot is one inference followed
by `inferStep` (stated at `CheckM`, where the do-notation reduces). -/
theorem inferBody_app_pure (env : Env) (F depth : Nat) (f a : Expr) :
    inferBody (pureFns env F) env depth (.app f a)
      = (pureFns env F).infer depth f >>= fun tf =>
          inferStep (pureFns env F) depth tf a := rfl

/-- Pure mirror of the interned inference spine loop `inferSpineI`:
`ty` is the raw Π-telescope after the binders consumed so far, `acc`
their arguments (innermost first). -/
def inferSpine (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → List Expr → m Expr
  | ty, acc, [] => pure (ty.instantiateList acc)
  | ty, acc, a :: rest =>
    match ty with
    | .forallE _ dom body _ => do
      let ta ← r.infer depth a
      unless ← r.defeq depth ta (dom.instantiateList acc) do
        throw (.invalid "application type mismatch")
      inferSpine r depth body (a :: acc) rest
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE _ dom body _ => do
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom do
          throw (.invalid "application type mismatch")
        inferSpine r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- The syntactic-`∀` arm of `inferSpine`. -/
def inferSpinePi (r : CoreFns m) (depth : Nat) (dom body : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) : m Expr := do
  let ta ← r.infer depth a
  unless ← r.defeq depth ta (dom.instantiateList acc) do
    throw (.invalid "application type mismatch")
  inferSpine r depth body (a :: acc) rest

/-- The normalize-and-retry arm of `inferSpine`. -/
def inferSpineWhnf (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) (a : Expr) (rest : List Expr) : m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE _ dom body _ => do
    let ta ← r.infer depth a
    unless ← r.defeq depth ta dom do
      throw (.invalid "application type mismatch")
    inferSpine r depth body [a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpine_nil (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) :
    inferSpine r depth ty acc [] = pure (ty.instantiateList acc) := by
  rw [inferSpine]

theorem inferSpine_pi (r : CoreFns m) (depth : Nat) (n : Name)
    (dom body : Expr) (bi : BinderMeta) (acc : List Expr) (a : Expr)
    (rest : List Expr) :
    inferSpine r depth (.forallE n dom body bi) acc (a :: rest)
      = inferSpinePi r depth dom body acc a rest := by
  rw [inferSpine, inferSpinePi]

theorem inferSpine_ne_pi (r : CoreFns m) (depth : Nat) {ty : Expr}
    (hty : ∀ n dom body bi, ty ≠ .forallE n dom body bi)
    (acc : List Expr) (a : Expr) (rest : List Expr) :
    inferSpine r depth ty acc (a :: rest)
      = inferSpineWhnf r depth ty acc a rest := by
  cases ty with
  | forallE n dom body bi => exact absurd rfl (hty n dom body bi)
  | _ => rw [inferSpine, inferSpineWhnf] <;> exact fun _ _ _ _ h => nomatch h

/-- The bulk substitution of a `∀`, exposed. -/
theorem instList_forallE (n : Name) (dom body : Expr)
    (bi : BinderMeta) (acc : List Expr) :
    (Expr.forallE n dom body bi).instantiateList acc
      = .forallE n (dom.instantiateList acc)
          (body.instantiateList acc 1) bi := by
  simp [Expr.instantiateList]

section InferAtF

variable {env : Env}

theorem inferStep_atF (d : Nat) (tf a : Expr) (F : Nat) :
    (inferStep (fueledFns env) d tf a).val F
      = inferStep (pureFns env F) d tf a := by
  unfold inferStep
  atF_tac4

theorem inferSpine_atF (d : Nat) :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (F : Nat),
      (inferSpine (fueledFns env) d ty acc xs).val F
        = inferSpine (pureFns env F) d ty acc xs
  | [], ty, acc, F => by rw [inferSpine_nil, inferSpine_nil]; rfl
  | a :: rest, ty, acc, F => by
    by_cases hpi : ∃ n dom body bi, ty = Expr.forallE n dom body bi
    · obtain ⟨n, dom, body, bi, rfl⟩ := hpi
      rw [inferSpine_pi, inferSpine_pi]
      unfold inferSpinePi
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      funext b
      cases b with
      | true =>
        show (inferSpine (fueledFns env) d body (a :: acc) rest).val F = _
        rw [inferSpine_atF d rest body (a :: acc) F]
        rfl
      | false => rfl
    · have hty : ∀ n dom body bi, ty ≠ Expr.forallE n dom body bi :=
        fun n dom b bi hh => hpi ⟨n, dom, b, bi, hh⟩
      rw [inferSpine_ne_pi _ _ hty, inferSpine_ne_pi _ _ hty]
      unfold inferSpineWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE n dom body bi =>
        dsimp only
        rw [FueledM.atF_bind]
        congr 1
        funext ta
        rw [FueledM.atF_bind]
        congr 1
        funext b
        cases b with
        | true =>
          show (inferSpine (fueledFns env) d body [a] rest).val F = _
          rw [inferSpine_atF d rest body [a] F]
          rfl
        | false => rfl
      | _ => rfl

theorem inferSpine_mono {d : Nat} {xs acc : List Expr} {ty : Expr}
    {F F' : Nat} (hle : F ≤ F') {res : Expr}
    (h : inferSpine (pureFns env F) d ty acc xs = .ok res) :
    inferSpine (pureFns env F') d ty acc xs = .ok res := by
  rw [← inferSpine_atF] at h ⊢
  exact (inferSpine (fueledFns env) d ty acc xs).property hle h

theorem inferStep_mono {d : Nat} {tf a : Expr} {F F' : Nat}
    (hle : F ≤ F') {res : Expr}
    (h : inferStep (pureFns env F) d tf a = .ok res) :
    inferStep (pureFns env F') d tf a = .ok res := by
  rw [← inferStep_atF] at h ⊢
  exact (inferStep (fueledFns env) d tf a).property hle h

theorem whnf_mono' {d : Nat} {e : Expr} {F F' : Nat} (hle : F ≤ F')
    {res : Expr} (h : whnf env F d e = .ok res) :
    whnf env F' d e = .ok res := whnf_mono hle h

theorem whnf_det {d F₁ F₂ : Nat} {e v₁ v₂ : Expr}
    (h1 : whnf env F₁ d e = .ok v₁)
    (h2 : whnf env F₂ d e = .ok v₂) : v₁ = v₂ := by
  have g1 := whnf_mono (Nat.le_max_left F₁ F₂) h1
  have g2 := whnf_mono (Nat.le_max_right F₁ F₂) h2
  rw [g1] at g2
  exact (Except.ok.injEq .. ▸ g2)

/-- `whnf` is the identity on a `∀` (at fuel `≥ 2`: one level for the
`whnfCore` inside the loop). -/
theorem whnf_forallE (F d : Nat) (n : Name) (t b : Expr)
    (mb : BinderMeta) :
    whnf env (F + 2) d (.forallE n t b mb) = .ok (.forallE n t b mb) :=
  rfl

end InferAtF

section InferSnoc

variable {env : Env}

theorem inferSpine_snoc {d : Nat} :
    ∀ (xs : List Expr) (ty : Expr) (acc : List Expr) (a : Expr) (F : Nat)
      (vres : Expr),
      inferSpine (pureFns env F) d ty acc (xs ++ [a]) = .ok vres →
      ∃ F' w, inferSpine (pureFns env F') d ty acc xs = .ok w ∧
        inferStep (pureFns env F') d w a = .ok vres
  | [], ty, acc, a, F, vres => by
    intro H
    rw [List.nil_append] at H
    by_cases hpi : ∃ n dom body bi, ty = Expr.forallE n dom body bi
    · obtain ⟨n, dom, body, bi, rfl⟩ := hpi
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
          ok_bind, defeq_def, isDefEqCore_mono (Nat.le_add_right F 2) hb,
          ok_bind]
        simp only [↓reduceIte]
        rw [← instList_cons0]
        rfl
    · have hty : ∀ n dom body bi, ty ≠ Expr.forallE n dom body bi :=
        fun n dom b bi hh => hpi ⟨n, dom, b, bi, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      refine ⟨F, ty.instantiateList acc, by rw [inferSpine_nil]; rfl, ?_⟩
      unfold inferStep
      rw [whnf_def]
      show (whnf env F d (ty.instantiateList acc) >>= _) = _
      rw [show whnf env F d (ty.instantiateList acc) = .ok w₀ from hw₀,
        ok_bind]
      cases w₀ with
      | forallE n dom body bi =>
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
      | fvar idx nm t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam nm t b mb => exact nomatch H
      | letE nm t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  | x :: xs', ty, acc, a, F, vres => by
    intro H
    rw [List.cons_append] at H
    by_cases hpi : ∃ n dom body bi, ty = Expr.forallE n dom body bi
    · obtain ⟨n, dom, body, bi, rfl⟩ := hpi
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
          ok_bind, defeq_def, isDefEqCore_mono (Nat.le_max_left F F₁) hb,
          ok_bind]
        simp only [↓reduceIte]
        exact inferSpine_mono (Nat.le_max_right F F₁) hw
    · have hty : ∀ n dom body bi, ty ≠ Expr.forallE n dom body bi :=
        fun n dom b bi hh => hpi ⟨n, dom, b, bi, hh⟩
      rw [inferSpine_ne_pi _ _ hty] at H
      unfold inferSpineWhnf at H
      obtain ⟨w₀, hw₀, H⟩ := bind_ok H
      cases w₀ with
      | forallE n dom body bi =>
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
          show (whnf env (max F F₁) d (ty.instantiateList acc) >>= _) = _
          rw [whnf_mono (Nat.le_max_left F F₁) hw₀, ok_bind]
          dsimp only
          rw [infer_def, inferTypeCore_mono (Nat.le_max_left F F₁) hta,
            ok_bind, defeq_def,
            isDefEqCore_mono (Nat.le_max_left F F₁) hb, ok_bind]
          simp only [↓reduceIte]
          exact inferSpine_mono (Nat.le_max_right F F₁) hw
      | bvar i => exact nomatch H
      | fvar idx nm t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' a' => exact nomatch H
      | lam nm t b mb => exact nomatch H
      | letE nm t v b => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H

private theorem inferSpine_sound_rev {d : Nat} :
    ∀ (rxs : List Expr) (h th vres : Expr) (F₀ F : Nat),
      inferTypeCore env F₀ d h = .ok th →
      inferSpine (pureFns env F) d th [] rxs.reverse = .ok vres →
      ∃ F', inferTypeCore env F' d (Expr.mkAppN h rxs.reverse) = .ok vres
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
    exact inferStep_mono (Nat.le_max_right F₂ F₁) hstep

/-- A successful inference-spine run over the head's inferred type is
reproduced by the chained inference on the whole application, at some
fuel. -/
theorem inferSpine_sound {d : Nat} (xs : List Expr) (h th vres : Expr)
    (F₀ F : Nat) (hh : inferTypeCore env F₀ d h = .ok th)
    (H : inferSpine (pureFns env F) d th [] xs = .ok vres) :
    ∃ F', inferTypeCore env F' d (Expr.mkAppN h xs) = .ok vres := by
  have hx : xs.reverse.reverse = xs := List.reverse_reverse xs
  have := inferSpine_sound_rev (d := d) xs.reverse h th vres F₀ F hh
    (by rw [hx]; exact H)
  rwa [hx] at this

/-- The bridge the interned walk uses. -/
theorem inferSpine_sound_body (d : Nat) (fx ax : Expr) (vres : Expr)
    (F : Nat)
    (H : ((fueledFns env).infer d (Expr.app fx ax).getAppFn >>=
        fun tf => inferSpine (fueledFns env) d tf []
          (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (inferBody (fueledFns env) env d (.app fx ax)).val F'
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

end InferSnoc

end Setlec