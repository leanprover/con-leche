import Setlec.Verify.Cached.BinderLoopC
import Setlec.Verify.BetaSpine

/-!
# Cached body walks, part 4: head normalization and the whnf loop

The port of `Setlec/Verify/DiscI4.lean` under the recipe (DESIGN.md,
task #163): simulation walks for the cached `whnfAppI`/`betaPeelI`,
`whnfCoreStepI`/`whnfCoreLoopI`/`whnfCoreBodyI`,
`whnfStepI`/`whnfLoopI`/`whnfBodyI`, `inferSpineI` and `inferBodyI`
(`Setlec/Cached/CoreC.lean`) against the same pure fueled comparands
the interned walks use.  `SimAt → SimC`, denotation hypotheses →
`RelC`/`RelCL`, no `Ext`, node inversion by `WFc.*_inv` and `cases` on
the `ExprC` constructor.  The pure comparand side of every statement is
byte-identical to the interned original's.

The one code-shape deviation from the interned original (recorded at
the batch-10 re-sync) lives in `inferBodyI`: the binder-telescope peel
fuel is the clone's constant `peelFuelM` where the arena reads its node
count.  Both are opaque to the binder-loop tails, which quantify over
the fuel, so the walk peels a `peelFuelM_eff` where the interned walk
peels a `withStore`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec.Cached

open Setlec.Cached.ExprC

variable {mode : CheckMode}
variable {cfg : CoreCfg}

section Walks

variable {env : Env} {f : Nat}

private theorem whnfCoreStepM_unfold (env : Env) (d : Nat)
    (kM : Expr → FueledM Expr) (e : Expr) :
    whnfCoreStepM cfg (fueledFns mode env) env d kM e =
    (match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body mb => pure (.lam n ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app g' a =>
      (fueledFns mode env).whnfCore d (Expr.app g' a).getAppFn >>= fun v =>
        whnfApp cfg (fueledFns mode env) env d kM v (Expr.app g' a).getAppArgs
    | .proj sn i pe =>
      (fueledFns mode env).whnf d pe >>= fun e' =>
      projLitToCtor (fueledFns mode env) env d e' >>= fun e' =>
      match env.findProj? sn i with
      | some entry =>
        match e'.getAppFn with
        | .const c us =>
          if entry.native ∧ c = entry.ctor ∧ i < entry.numFields ∧
              e'.getAppArgs.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then
            projCert (fueledFns mode env) env d e' i
              entry.numParams >>= fun b =>
            if b then
              kM (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))
            else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | none => pure (.proj sn i e')
    | .letE _ _ v b => kM (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")) := by
  cases e <;> rfl

/-- The stuck/iota tail of `whnfCoreBodyI`'s application case. -/
private theorem whnfCoreC_iota_tail (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {f' a : ExprC} {f'x xa : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hf'd : RelC f' f'x)
    (had : RelC a xa)
    (hwf' : Expr.WScoped d f'x) (hwa : Expr.WScoped d xa) :
    SimC mode env s₀ (RelEC d)
      (internI (.app f' a) >>= fun fa =>
        iotaRecI cfg.iotaMode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa >>= fun o =>
        match o with
        | some e'' => (coreKnotI mode (mkFEnv env) f).whnfCore d e''
        | none => pure fa)
      (iotaRec cfg.iotaMode (fueledFns mode env) env d (.app f'x xa) >>= fun o =>
        match o with
        | some e'' => (fueledFns mode env).whnfCore d e''
        | none => pure (.app f'x xa)) := by
  have hwapp : Expr.WScoped d (Expr.app f'x xa) := by
    simp only [Expr.WScoped]
    exact ⟨hwf', hwa⟩
  refine SimC.bind_left
    (internI_eff hs (n := ExprView.app f' a) ⟨hf'd.1, had.1⟩)
    (fun s₁ fa hs₁ hQfa => ?_)
  have hQfa' : RelC fa (Expr.app f'x xa) := by
    refine ⟨hQfa.1, ?_⟩
    have h := hQfa.2
    rw [show ofViewE (eraseCV (ExprView.app f' a))
      = Expr.app (eraseC f') (eraseC a) from rfl, hf'd.2, had.2] at h
    exact h
  refine SimC.bind (iotaRecC_sim ih henv hs₁ hQfa' hwapp)
    (fun s₂ o ox hs₂ hPo => ?_)
  cases o with
  | some e'' =>
    cases ox with
    | none => exact absurd hPo (by simp [RelOC])
    | some e''x =>
      obtain ⟨hred, hwred⟩ := hPo
      exact ih.whnfCore hs₂ hred hwred
  | none =>
    cases ox with
    | some e''x => exact absurd hPo (by simp [RelOC])
    | none => exact SimC.pure hs₂ ⟨hQfa', hwapp⟩

mutual

/-- The bulk-beta argument loop simulates its pure mirror. -/
theorem whnfAppC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {kI : ExprC → CheckCM ExprC} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : ExprC} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex)) :
    ∀ {args : List ExprC} {xs : List Expr} {v : ExprC} {vx : Expr}
      {s₀ : CState}, CSOK mode env s₀ →
      RelC v vx → Expr.WScoped d vx →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (whnfAppI cfg (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI v args)
        (whnfApp cfg (fueledFns mode env) env d kM vx xs)
  | [], xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [whnfAppI.eq_def]
    dsimp only
    rw [whnfApp_nil]
    exact SimC.pure hs ⟨hv, hwv⟩
  | a :: rest, xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [whnfAppI.eq_def]
    dsimp only
    refine SimC.view ?_
    obtain ⟨hwc, rfl⟩ := hv
    have hvr : RelC v (eraseC v) := ⟨hwc, rfl⟩
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases v with
    | lam nm ty body mb h bb fb lp =>
      dsimp only [ExprC.view]
      obtain ⟨hwty, hwbody, -⟩ := hwc.lam_inv
      have hwtb : Expr.WScoped d (eraseC ty) ∧ Expr.WScoped d (eraseC body) := by
        have hw' : Expr.WScoped d
          (.lam nm (eraseC ty) (eraseC body) mb) := hwv
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
        rw [show (eraseC body).instantiateList [xa]
            = (eraseC body).instantiate1 xa by
          rw [Expr.instantiateList_cons, Expr.instantiateList_nil]]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
      rw [show eraseC (ExprC.lam nm ty body mb h bb fb lp)
        = Expr.lam nm (eraseC ty) (eraseC body) mb from rfl, whnfApp_lam]
      unfold whnfAppLam
      -- task #161: the β gate reads the *same* `mb` on both sides
      -- (`eraseC` copies the binder meta), so one `by_cases`
      by_cases hgate : cfg.betaSkip mb.pw = true
      · simp only [hgate, ↓reduceIte]
        exact betaPeelC_sim ih henv hk hs ⟨hwbody, rfl⟩
          (RelCL.cons hax RelCL.nil) hwsub hrest hwrest
      have hgf : cfg.betaSkip mb.pw = false := by
        simpa only [Bool.not_eq_true] using hgate
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind (ih.infer hs hax hwxa)
        (fun s₁ ta tax hs₁ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₁ htad ⟨hwty, rfl⟩ hwta hwtb.1)
        (fun s₂ b b' hs₂ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact betaPeelC_sim ih henv hk hs₂ ⟨hwbody, rfl⟩
          (RelCL.cons hax RelCL.nil) hwsub hrest hwrest
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind_left (internI_eff hs₂
          (n := ExprView.app (ExprC.lam nm ty body mb h bb fb lp) a)
          ⟨hwc, hax.1⟩) (fun s₃ fa hs₃ hQfa => ?_)
        have hQfa' : RelC fa
            (Expr.app (.lam nm (eraseC ty) (eraseC body) mb) xa) := by
          refine ⟨hQfa.1, ?_⟩
          have hh := hQfa.2
          rw [show ofViewE (eraseCV (ExprView.app
              (ExprC.lam nm ty body mb h bb fb lp) a))
            = Expr.app (.lam nm (eraseC ty) (eraseC body) mb) (eraseC a)
            from rfl, hax.2] at hh
          exact hh
        refine SimC.of_eff (mkAppNM_eff hs₃ hQfa' hrest) _
          (fun r hQ => ⟨hQ, ?_⟩)
        refine Expr.WScoped.mkAppN ?_ hwrest
        simp only [Expr.WScoped]
        exact ⟨hwtb, hwxa⟩
    | bvar k h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.bvar k h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | sort u h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.sort u h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | const nm us h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.const nm us h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | lit l h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.lit l h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | fvar idx nm t h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.fvar idx nm t h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | app f₂ a₂ h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.app f₂ a₂ h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | forallE nm t b mm h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.forallE nm t b mm h bb fb lp)
            ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | letE nm t vv b h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.letE nm t vv b h bb fb lp)
            ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
    | proj sn i pe h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.proj sn i pe h bb fb lp)
            ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [whnfApp_ne_lam _ _ _ _ hnl]
      exact whnfAppIotaC_sim ih henv hk hs hvr hwv hax hwxa hrest hwrest
  termination_by args _ => (args.length, 0)

/-- The iota arm of the loop simulates its mirror. -/
theorem whnfAppIotaC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {kI : ExprC → CheckCM ExprC} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : ExprC} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex))
    {v a : ExprC} {vx xa : Expr} {rest : List ExprC} {xs : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hv : RelC v vx) (hwv : Expr.WScoped d vx)
    (hax : RelC a xa) (hwxa : Expr.WScoped d xa)
    (hrest : RelCL rest xs) (hwrest : ∀ x ∈ xs, Expr.WScoped d x) :
    SimC mode env s₀ (RelEC d)
      (internI (.app v a) >>= fun fa =>
        iotaRecI cfg.iotaMode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa >>= fun o =>
        match o with
        | some e'' =>
          kI e'' >>= fun v' =>
            whnfAppI cfg (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI v' rest
        | none =>
          whnfAppI cfg (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI fa rest)
      (whnfAppIota cfg (fueledFns mode env) env d kM vx xa xs) := by
    unfold whnfAppIota
    have hwapp : Expr.WScoped d (.app vx xa) := by
      simp only [Expr.WScoped]
      exact ⟨hwv, hwxa⟩
    refine SimC.bind_left
      (internI_eff hs (n := ExprView.app v a) ⟨hv.1, hax.1⟩)
      (fun s₁ fa hs₁ hQfa => ?_)
    have hQfa' : RelC fa (Expr.app vx xa) := by
      refine ⟨hQfa.1, ?_⟩
      have h := hQfa.2
      rw [show ofViewE (eraseCV (ExprView.app v a))
        = Expr.app (eraseC v) (eraseC a) from rfl, hv.2, hax.2] at h
      exact h
    refine SimC.bind (iotaRecC_sim ih henv hs₁ hQfa' hwapp)
      (fun s₂ o ox hs₂ hPo => ?_)
    cases o with
    | some e'' =>
      cases ox with
      | none => exact absurd hPo (by simp [RelOC])
      | some e''x =>
        obtain ⟨hred, hwred⟩ := hPo
        refine SimC.bind (hk hs₂ hred hwred)
          (fun s₃ v' v'x hs₃ hP => ?_)
        obtain ⟨hv'd, hwv'⟩ := hP
        exact whnfAppC_sim ih henv hk hs₃ hv'd hwv' hrest hwrest
    | none =>
      cases ox with
      | some e''x => exact absurd hPo (by simp [RelOC])
      | none =>
        exact whnfAppC_sim ih henv hk hs₂ hQfa' hwapp hrest hwrest
  termination_by (rest.length, 1)

/-- The peel loop simulates its pure mirror. -/
theorem betaPeelC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {kI : ExprC → CheckCM ExprC} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : ExprC} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex)) :
    ∀ {args : List ExprC} {xs : List Expr} {t : ExprC} {tx : Expr}
      {acc : List ExprC} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC t tx → RelCL acc ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (betaPeelI cfg (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI t acc args)
        (betaPeel cfg (fueledFns mode env) env d kM tx ws xs)
  | [], xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [betaPeelI.eq_def]
    dsimp only
    rw [betaPeel_nil]
    refine SimC.bind_left (instListM_eff (d := 0) hs ht hacc)
      (fun s₁ e' hs₁ hQ => ?_)
    exact hk hs₁ hQ hwty
  | a :: rest, xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [betaPeelI.eq_def]
    dsimp only
    refine SimC.view ?_
    obtain ⟨hwc, rfl⟩ := ht
    have htr : RelC t (eraseC t) := ⟨hwc, rfl⟩
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases t with
    | lam nm ty body mb h bb fb lp =>
      dsimp only [ExprC.view]
      obtain ⟨hwty', hwbody, -⟩ := hwc.lam_inv
      rw [show eraseC (ExprC.lam nm ty body mb h bb fb lp)
        = Expr.lam nm (eraseC ty) (eraseC body) mb from rfl, betaPeel_lam]
      unfold betaPeelLam
      have hcomp : Expr.WScoped d ((eraseC ty).instantiateList ws)
          ∧ Expr.WScoped d ((eraseC body).instantiateList ws 1) := by
        have hw' : Expr.WScoped d
            ((Expr.lam nm (eraseC ty) (eraseC body) mb).instantiateList ws) :=
          hwty
        rw [instList_lam] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((eraseC body).instantiateList (xa :: ws)) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      -- task #161: the β gate, same datum on both sides
      by_cases hgate : cfg.betaSkip mb.pw = true
      · simp only [hgate, ↓reduceIte]
        exact betaPeelC_sim ih henv hk hs ⟨hwbody, rfl⟩
          (RelCL.cons hax hacc) hwsub hrest hwrest
      have hgf : cfg.betaSkip mb.pw = false := by
        simpa only [Bool.not_eq_true] using hgate
      simp only [hgf, Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind_left (instListM_eff (d := 0) hs ⟨hwty', rfl⟩ hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.infer hs₁ hax hwxa)
        (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htad hQty hwta hcomp.1)
        (fun s₃ b b' hs₃ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact betaPeelC_sim ih henv hk hs₃ ⟨hwbody, rfl⟩
          (RelCL.cons hax hacc) hwsub hrest hwrest
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind_left (instListM_eff (d := 0) hs₃ htr hacc)
          (fun s₄ f' hs₄ hQf' => ?_)
        refine SimC.bind_left (internI_eff hs₄ (n := ExprView.app f' a)
          ⟨hQf'.1, hax.1⟩) (fun s₅ fa hs₅ hQfa => ?_)
        have hQfa' : RelC fa
            (Expr.app ((Expr.lam nm (eraseC ty) (eraseC body)
              mb).instantiateList ws) xa) := by
          refine ⟨hQfa.1, ?_⟩
          have hh := hQfa.2
          rw [show ofViewE (eraseCV (ExprView.app f' a))
            = Expr.app (eraseC f') (eraseC a) from rfl, hQf'.2, hax.2] at hh
          exact hh
        refine SimC.of_eff (mkAppNM_eff hs₅ hQfa' hrest) _
          (fun r hQ => ⟨hQ, ?_⟩)
        refine Expr.WScoped.mkAppN ?_ hwrest
        simp only [Expr.WScoped]
        exact ⟨hwty, hwxa⟩
    | bvar k h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.bvar k h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | sort u h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.sort u h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | const nm us h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.const nm us h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | lit l h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.lit l h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | fvar idx nm tt h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.fvar idx nm tt h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | app f₂ a₂ h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.app f₂ a₂ h bb fb lp) ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | forallE nm tt b mm h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.forallE nm tt b mm h bb fb lp)
            ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | letE nm tt vv b h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.letE nm tt vv b h bb fb lp)
            ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv' vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
    | proj sn i pe h bb fb lp =>
      have hnl : ∀ n' ty' body' mb',
          eraseC (ExprC.proj sn i pe h bb fb lp)
            ≠ Expr.lam n' ty' body' mb' :=
        fun _ _ _ _ h => nomatch h
      rw [betaPeel_ne_lam _ _ _ _ hnl]
      refine SimC.bind_left (instListM_eff (d := 0) hs htr hacc)
        (fun s₁ e' hs₁ hQ => ?_)
      refine SimC.bind (hk hs₁ hQ hwty) (fun s₂ vv vvx hs₂ hP => ?_)
      obtain ⟨hvd, hwv'⟩ := hP
      exact whnfAppC_sim ih henv hk hs₂ hvd hwv'
        (RelCL.cons hax hrest) hwargs
  termination_by args _ => (args.length, 1)

end

theorem whnfCoreStepC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : ExprC → CheckCM ExprC} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {i : ExprC} {ex : Expr}, CSOK mode env s →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s (RelEC d) (kI i) (kM ex))
    {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfCoreStepI cfg (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfCoreStepM cfg (fueledFns mode env) env d kM ex) := by
  unfold whnfCoreStepI
  rw [whnfCoreStepM_unfold]
  refine SimC.view ?_
  obtain ⟨hwc, rfl⟩ := hden
  have hden : RelC i (eraseC i) := ⟨hwc, rfl⟩
  cases i with
  | sort u h bb fb lp => exact SimC.pure hs ⟨hden, hw⟩
  | fvar idx nm t h bb fb lp => exact SimC.pure hs ⟨hden, hw⟩
  | forallE nm t b m h bb fb lp => exact SimC.pure hs ⟨hden, hw⟩
  | lam nm t b m h bb fb lp => exact SimC.pure hs ⟨hden, hw⟩
  | const nm us h bb fb lp => exact SimC.pure hs ⟨hden, hw⟩
  | lit l h bb fb lp => exact SimC.pure hs ⟨hden, hw⟩
  | bvar k h bb fb lp => exact SimC.throw
  | letE nm t v b h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨-, hwvc, hwbc, -⟩ := hwc.letE_inv
    have hw' : Expr.WScoped d
      (.letE nm (eraseC t) (eraseC v) (eraseC b)) := hw
    simp only [Expr.WScoped] at hw'
    refine SimC.bind_left (inst1M_eff hs ⟨hwbc, rfl⟩ ⟨hwvc, rfl⟩)
      (fun s₁ e' hs₁ hQ => ?_)
    exact hk hs₁ hQ (Expr.WScoped.instantiate1_gen hw'.2.1 0 hw'.2.2)
  | app g' a h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    -- Bulk beta (task #50): the twin normalizes the spine head once and
    -- runs the argument loop against its mirror.
    refine SimC.withStore ?_
    refine SimC.withStore ?_
    dsimp only [CStore.getAppFnI, CStore.getAppArgsI]
    have hhead : RelC (ExprC.getAppFn (ExprC.app g' a h bb fb lp))
        ((Expr.app (eraseC g') (eraseC a)).getAppFn) :=
      ExprC.getAppFn_spec hwc
    have hargs : RelCL (ExprC.getAppArgs (ExprC.app g' a h bb fb lp))
        ((Expr.app (eraseC g') (eraseC a)).getAppArgs) :=
      ExprC.getAppArgs_spec hwc
    refine SimC.bind (ih.whnfCore hs hhead hw.getAppFn)
      (fun s₁ v vh hs₁ hP => ?_)
    exact whnfAppC_sim ih henv hk hs₁ hP.1 hP.2 hargs hw.getAppArgs
  | proj sn ip pe h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwpec, -⟩ := hwc.proj_inv
    have hwpe : Expr.WScoped d (eraseC pe) := by
      have hw' : Expr.WScoped d (Expr.proj sn ip (eraseC pe)) := hw
      simpa only [Expr.WScoped] using hw'
    refine SimC.bind (ih.whnf hs ⟨hwpec, rfl⟩ hwpe)
      (fun s₀' e₀ e₀x hs₀' hP₀ => ?_)
    obtain ⟨he₀d, hwe₀⟩ := hP₀
    refine SimC.bind (projLitToCtorC_sim ih hs₀' he₀d hwe₀)
      (fun s₁ e' e'x hs₁ hP => ?_)
    obtain ⟨⟨he'wf, rfl⟩, hwe'⟩ := hP
    have he'd : RelC e' (eraseC e') := ⟨he'wf, rfl⟩
    have hwproj : Expr.WScoped d (Expr.proj sn ip (eraseC e')) := by
      simpa only [Expr.WScoped] using hwe'
    refine SimC.bind_left (readbackNM_eff hs₁ sn)
      (fun s₁' snw hs₁ hsnw => ?_)
    subst snw
    rw [mkFEnv_findProj?]
    cases hfp : env.findProj? sn ip with
    | none =>
      dsimp only
      exact SimC.of_eff
        (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
        (fun pr hQ => ⟨hQ, hwproj⟩)
    | some entry =>
      dsimp only
      refine SimC.withStore ?_
      dsimp only [CStore.getNode, CStore.getAppFnI]
      obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec he'wf
      generalize hg : ExprC.getAppFn e' = g at hwfn hfn ⊢
      cases g with
      | const c us hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.const c us from hfn.symm]
        dsimp only
        refine SimC.withStore ?_
        dsimp only [CStore.getAppArgsI]
        have hargs : RelCL (ExprC.getAppArgs e') ((eraseC e').getAppArgs) :=
          ExprC.getAppArgs_spec he'wf
        refine SimC.bind_left (beqNameM_eff hs₁ c entry.ctor)
          (fun s₁b bq hs₁ hbq => ?_)
        subst bq
        rw [hargs.length]
        simp only [beq_iff_eq]
        have hwarg : Expr.WScoped d
            ((eraseC e').getAppArgs.getD (entry.numParams + ip) (.bvar 0)) :=
          wscoped_getD hwe'.getAppArgs _
        split
        · rename_i hcond
          obtain ⟨-, rfl, -, -, -⟩ := hcond
          refine SimC.bind_left
            (internI_eff hs₁ (n := ExprView.bvar 0) trivial)
            (fun s₂ bvar0 hs₂ hQ0 => ?_)
          refine SimC.bind (projCertC_sim ih hs₂ he'd hwe')
            (fun s₃ b b' hs₃ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | true =>
            simp only [↓reduceIte]
            exact hk hs₃
              (RelCL.getD hQ0 (entry.numParams + ip) hargs) hwarg
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.of_eff
              (internI_eff hs₃ (n := ExprView.proj sn ip e') he'wf) _
              (fun pr hQ => ⟨hQ, hwproj⟩)
        · exact SimC.of_eff
            (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
            (fun pr hQ => ⟨hQ, hwproj⟩)
      | bvar k hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.bvar k from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | sort u hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.sort u from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | lit l hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.lit l from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | fvar idx nm t hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.fvar idx nm (eraseC t)
          from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | app f₂ a₂ hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.app (eraseC f₂) (eraseC a₂)
          from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | lam nm t b m hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn
          = Expr.lam nm (eraseC t) (eraseC b) m from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | forallE nm t b m hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn
          = Expr.forallE nm (eraseC t) (eraseC b) m from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | letE nm t v b hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn
          = Expr.letE nm (eraseC t) (eraseC v) (eraseC b) from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)
      | proj s' j' e'' hc bbc fbc lpc =>
        rw [show (eraseC e').getAppFn = Expr.proj s' j' (eraseC e'')
          from hfn.symm]
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.proj sn ip e') he'wf) _
          (fun pr hQ => ⟨hQ, hwproj⟩)

/-- The head-normalization *loop* simulates its mirror, by induction on
the shared step budget (task #106). -/
theorem whnfCoreLoopC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} :
    ∀ (n : Nat) {i : ExprC} {ex : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s₀ (RelEC d)
        (whnfCoreLoopI cfg (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfCoreLoopM cfg (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimC.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfCoreLoopI, whnfCoreLoopM]
    exact whnfCoreStepC_sim ih henv
      (fun h1 h2 h3 => whnfCoreLoopC_sim ih henv n h1 h2 h3) hs hden hw

/-- The cached head-normalization body simulates the chained
specification body: the loop run is reproduced by `whnfCoreBody` at
some knot fuel (`whnfCoreLoop_sound_body`). -/
theorem whnfCoreBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfCoreBodyI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfCoreBody mode (fueledFns mode env) env d ex) := by
  unfold whnfCoreBodyI
  exact SimC.wr (whnfCoreLoopC_sim ih henv whnfCoreLoopFuel hs hden hw)
    (fun v F hF => whnfCoreLoop_sound_body d ex v whnfCoreLoopFuel F hF)

end Walks

section Walks2

variable {env : Env} {f : Nat}

private theorem whnfStep_unfold (env : Env) (d : Nat)
    (kM : Expr → FueledM Expr) (e : Expr) :
    whnfStep (fueledFns mode env) env d kM e =
    ((fueledFns mode env).whnfCore d e >>= fun e₁ =>
      reduceNat (fueledFns mode env) env d e₁ >>= fun o =>
      match o with
      | some e₂ => kM e₂
      | none =>
        match unfoldDefinition env e₁ with
        | some e₂ => kM e₂
        | none => pure e₁) := rfl

/-- One iteration of the reduction loop simulates its specification
(task #106; the continuation is abstract, as in the body). -/
theorem whnfStepC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {kI : ExprC → CheckCM ExprC} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : CState} {j : ExprC} {ey : Expr}, CSOK mode env s →
      RelC j ey → Expr.WScoped d ey →
      SimC mode env s (RelEC d) (kI j) (kM ey))
    {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfStepI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfStep (fueledFns mode env) env d kM ex) := by
  unfold whnfStepI
  rw [whnfStep_unfold]
  refine SimC.bind (ih.whnfCore hs hden hw)
    (fun s₁ e₁ e₁x hs₁ hP => ?_)
  obtain ⟨he₁d, hwe₁⟩ := hP
  refine SimC.bind (reduceNatC_sim ih hs₁ he₁d hwe₁)
    (fun s₂ o ox hs₂ hPo => ?_)
  cases o with
  | some e₂ =>
    cases ox with
    | none => exact absurd hPo (by simp [RelOC])
    | some e₂x =>
      obtain ⟨he₂d, hwe₂⟩ := hPo
      exact hk hs₂ he₂d hwe₂
  | none =>
    cases ox with
    | some e₂x => exact absurd hPo (by simp [RelOC])
    | none =>
      refine SimC.bind_left (unfoldDefinitionC_eff hs₂ he₁d)
        (fun s₃ o₂ hs₃ hQ => ?_)
      cases hu : unfoldDefinition env e₁x with
      | some e₂x =>
        rw [hu] at hQ
        cases o₂ with
        | none => exact absurd hQ (by simp [OptEr])
        | some e₂ =>
          exact hk hs₃ hQ (unfoldDefinition_WScoped henv hu hwe₁)
      | none =>
        rw [hu] at hQ
        cases o₂ with
        | some e₂ => exact absurd hQ (by simp [OptEr])
        | none => exact SimC.pure hs₃ ⟨he₁d, hwe₁⟩

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ (n : Nat) {i : ExprC} {ex : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i ex → Expr.WScoped d ex →
      SimC mode env s₀ (RelEC d)
        (whnfLoopI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfLoop (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimC.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfLoopI, whnfLoop]
    exact whnfStepC_sim ih henv
      (fun h1 h2 h3 => whnfLoopC_sim ih henv n h1 h2 h3) hs hden hw

theorem whnfBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfBody (fueledFns mode env) env d ex) :=
  whnfLoopC_sim ih henv whnfLoopFuel hs hden hw

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineC_sim (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List ExprC} {xs : List Expr} {ty : ExprC} {tx : Expr}
      {acc : Array ExprC} {ws : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tx →
      RelCL acc.toList.reverse ws →
      Expr.WScoped d (tx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ (RelEC d)
        (inferSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty acc args)
        (inferSpine (fueledFns mode env) d tx ws xs)
  | [], xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [inferSpineI.eq_def]
    dsimp only
    rw [inferSpine_nil]
    exact SimC.of_eff (instListRevM_eff (d := 0) hs ht hacc) _
      (fun r hQ => ⟨hQ, hwty⟩)
  | a :: rest, xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    obtain ⟨xa, xs, rfl, hax, hrest⟩ := hargs.cons_inv
    rw [inferSpineI.eq_def]
    dsimp only
    refine SimC.view ?_
    obtain ⟨hwc, rfl⟩ := ht
    have htr : RelC ty (eraseC ty) := ⟨hwc, rfl⟩
    have hwxa : Expr.WScoped d xa := hwargs xa (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ xs, Expr.WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE nm dom body mb h bb fb lp =>
      dsimp only [ExprC.view]
      obtain ⟨hwdom, hwbody, -⟩ := hwc.forallE_inv
      rw [show eraseC (ExprC.forallE nm dom body mb h bb fb lp)
        = Expr.forallE nm (eraseC dom) (eraseC body) mb from rfl, inferSpine_pi]
      unfold inferSpinePi
      have hcomp : Expr.WScoped d ((eraseC dom).instantiateList ws)
          ∧ Expr.WScoped d ((eraseC body).instantiateList ws 1) := by
        have hw' : Expr.WScoped d
          ((Expr.forallE nm (eraseC dom) (eraseC body) mb).instantiateList ws) :=
          hwty
        rw [instList_forallE] at hw'
        simpa only [Expr.WScoped] using hw'
      have hwsub : Expr.WScoped d ((eraseC body).instantiateList (xa :: ws)) := by
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwxa 0 hcomp.2
      dsimp only
      refine SimC.bind_left (instListRevM_eff (d := 0) hs ⟨hwdom, rfl⟩ hacc)
        (fun s₁ dom' hs₁ hQdom => ?_)
      refine SimC.bind (ih.infer hs₁ hax hwxa)
        (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htad, hwta⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htad hQdom hwta hcomp.1)
        (fun s₃ b b' hs₃ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw_bind
      | true =>
        simp only [↓reduceIte]
        exact inferSpineC_sim ih henv hs₃ ⟨hwbody, rfl⟩
          (by rw [toListRev_push]; exact RelCL.cons hax hacc) hwsub
          hrest hwrest
    | bvar k h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.bvar k h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | sort u h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.sort u h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | const nm us h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.const nm us h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | lit l h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.lit l h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | fvar idx nm tt h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.fvar idx nm tt h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | app f₂ a₂ h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.app f₂ a₂ h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | lam nm tt b mm h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.lam nm tt b mm h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | letE nm tt vv b h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.letE nm tt vv b h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
    | proj sn j pe h bb fb lp =>
      dsimp only [ExprC.view]
      have hnl : ∀ n' dom' body' bi',
          eraseC (ExprC.proj sn j pe h bb fb lp) ≠ Expr.forallE n' dom' body' bi' :=
        fun _ _ _ _ h => nomatch h
      rw [inferSpine_ne_pi _ _ hnl]
      unfold inferSpineWhnf
      refine SimC.bind_left (instListRevM_eff (d := 0) hs htr hacc)
        (fun s₁ ty' hs₁ hQty => ?_)
      refine SimC.bind (ih.whnf hs₁ hQty hwty)
        (fun s₂ w wx hs₂ hP => ?_)
      obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP
      refine SimC.view ?_
      cases w with
      | forallE nmw dom body mb wh wbb wfb wlp =>
        dsimp only [eraseC, ExprC.view]
        obtain ⟨hwdom, hwbody, -⟩ := hwwf.forallE_inv
        have hwtb : Expr.WScoped d (eraseC dom)
            ∧ Expr.WScoped d (eraseC body) := by
          have hw' : Expr.WScoped d
            (.forallE nmw (eraseC dom) (eraseC body) mb) := hww
          simpa only [Expr.WScoped] using hw'
        have hwsub : Expr.WScoped d ((eraseC body).instantiateList [xa]) := by
          rw [instList_single]
          exact Expr.WScoped.instantiate1_gen hwxa 0 hwtb.2
        refine SimC.bind (ih.infer hs₂ hax hwxa)
          (fun s₃ ta tax hs₃ hP₃ => ?_)
        obtain ⟨htad, hwta⟩ := hP₃
        refine SimC.bind (ih.defeq hs₃ htad ⟨hwdom, rfl⟩ hwta hwtb.1)
          (fun s₄ b b' hs₄ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          exact inferSpineC_sim ih henv hs₄ ⟨hwbody, rfl⟩
            (by rw [toListRev_singleton]; exact RelCL.cons hax RelCL.nil)
            hwsub hrest hwrest
      | bvar k' wh wbb wfb wlp => exact SimC.throw
      | sort u' wh wbb wfb wlp => exact SimC.throw
      | const nm' us' wh wbb wfb wlp => exact SimC.throw
      | lit l' wh wbb wfb wlp => exact SimC.throw
      | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
      | app f' a' wh wbb wfb wlp => exact SimC.throw
      | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
      | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
      | proj s' j' e' wh wbb wfb wlp => exact SimC.throw

theorem inferBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (inferBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (inferBody mode (fueledFns mode env) env d ex) := by
  unfold inferBodyI
  refine SimC.view ?_
  obtain ⟨hwc, rfl⟩ := hden
  have hden : RelC i (eraseC i) := ⟨hwc, rfl⟩
  cases i with
  | sort u h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind_left (internLM_eff hs (Level.succ u))
      (fun s₁ su hs₁ hsu => ?_)
    subst su
    exact SimC.of_eff
      (internI_eff hs₁ (n := ExprView.sort (Level.succ u)) trivial) _
      (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
  | bvar k h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    exact SimC.throw
  | letE nm t v b h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, hwvc, hwbc, -⟩ := hwc.letE_inv
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    have hw' : Expr.WScoped d
      (.letE nm (eraseC t) (eraseC v) (eraseC b)) := hw
    simp only [Expr.WScoped] at hw'
    -- task #100 stage 6: the `let` checks moved here from the deleted
    -- annotation pass (official `infer_let` order)
    refine SimC.bind (ih.infer hs ⟨hwtc, rfl⟩ hw'.1)
      (fun s₁ tty ttyx hs₁ hP₁ => ?_)
    obtain ⟨httyd, hwtty⟩ := hP₁
    refine SimC.bind (ensureSortC_sim ih hs₁ httyd hwtty)
      (fun s₂ u lu hs₂ _hPu => ?_)
    refine SimC.bind (ih.infer hs₂ ⟨hwvc, rfl⟩ hw'.2.1)
      (fun s₃ tv tvx hs₃ hP₃ => ?_)
    obtain ⟨htvd, hwtv⟩ := hP₃
    refine SimC.bind (ih.defeq hs₃ htvd ⟨hwtc, rfl⟩ hwtv hw'.1)
      (fun s₄ bb' bb'' hs₄ hPb => ?_)
    obtain rfl : bb' = bb'' := hPb
    cases bb' with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind_left (inst1M_eff hs₄ ⟨hwbc, rfl⟩ ⟨hwvc, rfl⟩)
        (fun s₅ e' hs₅ hQ => ?_)
      exact ih.infer hs₅ hQ (Expr.WScoped.instantiate1_gen hw'.2.1 0 hw'.2.2)
  | fvar idx nm t h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, -⟩ := hwc.fvar_inv
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    have h' : idx < d ∧ Expr.WScoped idx (eraseC t) := by
      have hw' : Expr.WScoped d (Expr.fvar idx nm (eraseC t)) := hw
      simpa only [Expr.WScoped] using hw'
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimC.pure hs
        ⟨⟨hwtc, rfl⟩, Expr.WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimC.throw
  | lit l h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (internNameM_eff hs natName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.const natName []) trivial) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (internNameM_eff hs stringName)
          (fun s₁ ni hs₁ hQni => ?_)
        subst ni
        exact SimC.of_eff
          (internI_eff hs₁ (n := ExprView.const stringName []) trivial) _
          (fun r hQ => ⟨hQ, by simp [Expr.WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
  | const nm us h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind_left (readbackNM_eff hs nm)
      (fun s₀' nw hs hnw => ?_)
    subst nw
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimC.throw
    | some ci =>
      dsimp only
      by_cases hlen : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hlen, if_pos hlen]
        refine SimC.of_eff (constTyAtM_eff hs hfn) _ (fun r hQ => ?_)
        refine ⟨hQ, ?_⟩
        obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
        exact wscoped_instLevels_of_not_hasFvar htf _ _
      · rw [if_neg hlen, if_neg hlen]
        exact SimC.throw_bind
  | forallE nm t b m h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, hwbc, -⟩ := hwc.forallE_inv
    have hwtb : Expr.WScoped d (eraseC t) ∧ Expr.WScoped d (eraseC b) := by
      have hw' : Expr.WScoped d
        (Expr.forallE nm (eraseC t) (eraseC b) m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind (ih.infer hs ⟨hwtc, rfl⟩ hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP₂
    refine SimC.view ?_
    cases w with
    | sort u wh wbb wfb wlp =>
      dsimp only [eraseC, ExprC.view]
      refine SimC.bind_left
        (internI_eff hs₂ (n := ExprView.fvar d nm t) hwtc)
        (fun s₃ fv hs₃ hQfv => ?_)
      refine SimC.bind_left (peelFuelM_eff hs₃)
        (fun s₃f fuel hs₃f _hQfuel => ?_)
      exact inferPisC_tail_sim ih hs₃f ⟨hwbc, rfl⟩ rfl hQfv hwtb.1 hwtb.2
    | bvar k' wh wbb wfb wlp => exact SimC.throw
    | const nm' us' wh wbb wfb wlp => exact SimC.throw
    | lit l' wh wbb wfb wlp => exact SimC.throw
    | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
    | app f' a' wh wbb wfb wlp => exact SimC.throw
    | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
    | forallE nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
    | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
    | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
  | lam nm t b m h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, hwbc, -⟩ := hwc.lam_inv
    have hwtb : Expr.WScoped d (eraseC t) ∧ Expr.WScoped d (eraseC b) := by
      have hw' : Expr.WScoped d
        (Expr.lam nm (eraseC t) (eraseC b) m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    obtain ⟨mbi, mpw⟩ := m
    refine SimC.bind (ih.infer hs ⟨hwtc, rfl⟩ hwtb.1)
      (fun s₁ tty ttyx hs₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimC.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hP₂ => ?_)
    obtain ⟨⟨hwwf, rfl⟩, hww⟩ := hP₂
    refine SimC.view ?_
    cases w with
    | sort u wh wbb wfb wlp =>
      dsimp only [eraseC, ExprC.view]
      refine SimC.bind_left
        (internI_eff hs₂ (n := ExprView.fvar d nm t) hwtc)
        (fun s₃ fv hs₃ hQfv => ?_)
      refine SimC.bind_left (peelFuelM_eff hs₃)
        (fun s₃f fuel hs₃f _hQfuel => ?_)
      exact inferLamsC_tail_sim ih henv hs₃f ⟨hwbc, rfl⟩ ⟨hwtc, rfl⟩ hQfv
        hwtb.1 hwtb.2
    | bvar k' wh wbb wfb wlp => exact SimC.throw
    | const nm' us' wh wbb wfb wlp => exact SimC.throw
    | lit l' wh wbb wfb wlp => exact SimC.throw
    | fvar idx' nm' t' wh wbb wfb wlp => exact SimC.throw
    | app f' a' wh wbb wfb wlp => exact SimC.throw
    | lam nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
    | forallE nm' t' b' m' wh wbb wfb wlp => exact SimC.throw
    | letE nm' t' v' b' wh wbb wfb wlp => exact SimC.throw
    | proj s' j' e' wh wbb wfb wlp => exact SimC.throw
  | app g' a h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    -- Bulk telescope consumption (task #50): the twin infers the spine
    -- head once and walks the Π-telescope; `inferSpine_sound_body`
    -- reproduces the loop's verdict in the chained body.
    refine SimC.wr ?_
      (fun v F hF => inferSpine_sound_body d (eraseC g') (eraseC a) v F hF)
    refine SimC.withStore ?_
    refine SimC.withStore ?_
    dsimp only [CStore.getAppFnI, CStore.getAppArgsI]
    have hhead : RelC (ExprC.getAppFn (ExprC.app g' a h bb fb lp))
        ((Expr.app (eraseC g') (eraseC a)).getAppFn) :=
      ExprC.getAppFn_spec hwc
    have hargsSpec : RelCL (ExprC.getAppArgs (ExprC.app g' a h bb fb lp))
        ((Expr.app (eraseC g') (eraseC a)).getAppArgs) :=
      ExprC.getAppArgs_spec hwc
    refine SimC.bind (ih.infer hs hhead hw.getAppFn)
      (fun s₁ tf tfx hs₁ hP => ?_)
    refine inferSpineC_sim ih henv hs₁ hP.1
      (by rw [toListRev_empty]; exact RelCL.nil) ?_
      hargsSpec hw.getAppArgs
    rw [Expr.instantiateList_nil]
    exact hP.2
  | proj sn ip pe h bb fb lp =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwpec, -⟩ := hwc.proj_inv
    have hwpe : Expr.WScoped d (eraseC pe) := by
      have hw' : Expr.WScoped d (Expr.proj sn ip (eraseC pe)) := hw
      simpa only [Expr.WScoped] using hw'
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimC.bind_pure_right ?_
    try dsimp only
    refine SimC.bind (ih.infer hs ⟨hwpec, rfl⟩ hwpe)
      (fun s₁ tpe tpex hs₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimC.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hP₂ => ?_)
    obtain ⟨⟨htewf, rfl⟩, hwte⟩ := hP₂
    refine SimC.withStore ?_
    dsimp only [CStore.getNode, CStore.getAppFnI]
    obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec htewf
    generalize hg : ExprC.getAppFn te = g at hwfn hfn ⊢
    cases g with
    | const T us hc bbc fbc lpc =>
      rw [show (eraseC te).getAppFn = Expr.const T us from hfn.symm]
      dsimp only
      refine SimC.bind_left (readbackNM_eff hs₂ T)
        (fun s₂' Tw hs₂ hTw => ?_)
      subst Tw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.withStore ?_
        dsimp only [CStore.getAppArgsI]
        have htargs : RelCL (ExprC.getAppArgs te) ((eraseC te).getAppArgs) :=
          ExprC.getAppArgs_spec htewf
        rw [htargs.length]
        split
        · -- task #161 item B2 (harvest site 21 / P10): the residual is
          -- the *computed* two-way branch on both sides.  `RelCL` maps
          -- the interned spine onto the spec's, so matching the
          -- interned list fixes both; the second branch's node is two
          -- `internI`s whose erasure is the spec's `Expr`.
          match hgt : ExprC.getAppArgs te, ip with
          | [], _ => exact SimC.throw
          | [_], _ => exact SimC.throw
          | _ :: _ :: _ :: _, _ => exact SimC.throw
          | [Ai, Bi], 0 =>
            rw [hgt] at htargs
            have hspec := htargs.2
            simp only [List.map] at hspec
            rw [← hspec]
            have hwA : WFc Ai := htargs.1.head
            refine SimC.pure hs₂ ⟨⟨hwA, rfl⟩, ?_⟩
            exact hwte.getAppArgs (eraseC Ai) (by rw [← hspec]; simp)
          | [Ai, Bi], 1 =>
            rw [hgt] at htargs
            have hspec := htargs.2
            simp only [List.map] at hspec
            rw [← hspec]
            have hwB : WFc Bi := htargs.1.tail.head
            refine SimC.bind_left
              (internI_eff hs₂ (n := ExprView.proj T 0 pe) hwpec)
              (fun s₃ p₀ hs₃ hQ₀ => ?_)
            refine SimC.of_eff
              (internI_eff hs₃ (n := ExprView.app Bi p₀)
                ⟨hwB, hQ₀.1⟩) _
              (fun pr hQ => ⟨⟨hQ.1, ?_⟩, ?_⟩)
            · rw [hQ.2]
              show Expr.app (eraseC Bi) (eraseC p₀) = _
              rw [hQ₀.2]
              rfl
            · simp only [Expr.WScoped]
              exact ⟨hwte.getAppArgs (eraseC Bi) (by rw [← hspec]; simp),
                hwpe⟩
          | [Ai, Bi], _ + 2 => exact SimC.throw
        · exact SimC.throw
    | bvar k' hc bbc fbc lpc => exact SimC.throw
    | sort u' hc bbc fbc lpc => exact SimC.throw
    | lit l' hc bbc fbc lpc => exact SimC.throw
    | fvar idx' nm' t' hc bbc fbc lpc => exact SimC.throw
    | app f' a' hc bbc fbc lpc => exact SimC.throw
    | lam nm' t' b' m' hc bbc fbc lpc => exact SimC.throw
    | forallE nm' t' b' m' hc bbc fbc lpc => exact SimC.throw
    | letE nm' t' v' b' hc bbc fbc lpc => exact SimC.throw
    | proj s' j' e' hc bbc fbc lpc => exact SimC.throw

end Walks3

end Setlec.Cached
