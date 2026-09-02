import Setlec.Verify.DiscI3
import Setlec.Verify.BinderLoopI
import Setlec.Verify.BetaSpine

/-!
# Interned body walks, part 4: head normalization and the whnf loop

Simulation walks for `whnfCoreBodyI` and `whnfBodyI`, mirroring
`whnfCoreBody_disc`/`whnfBody_disc` (`Setlec/Verify/Disc.lean`).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Setlec

variable {mode : CheckMode}

open EStore Expr

section Walks

variable {env : Env} {f : Nat}

private theorem whnfCoreStepM_unfold (env : Env) (d : Nat)
    (kM : Expr → FueledM Expr) (e : Expr) :
    whnfCoreStepM mode (fueledFns mode env) env d kM e =
    (match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body mb => pure (.lam n ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app g' a =>
      (fueledFns mode env).whnfCore d (Expr.app g' a).getAppFn >>= fun v =>
        whnfApp mode (fueledFns mode env) env d kM v (Expr.app g' a).getAppArgs
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
              (Level.subst entry.levelParams us entry.fieldSort)
              (Level.subst entry.levelParams us entry.structSort)
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
private theorem whnfCoreI_iota_tail (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} {f' a : EIdx} {f'x xa : Expr} {s₀ : IState}
    (hs : ISOK mode env s₀) (hf'd : s₀.store.denoteT f' = some f'x)
    (had : s₀.store.denoteT a = some xa)
    (hwf' : WScoped d f'x) (hwa : WScoped d xa) :
    SimAt mode env s₀ (RelE d)
      (internI (.app f' a) >>= fun fa =>
        iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa >>= fun o =>
        match o with
        | some e'' => (coreKnotI mode (mkFEnv env) f).whnfCore d e''
        | none => pure fa)
      (iotaRec mode (fueledFns mode env) env d (.app f'x xa) >>= fun o =>
        match o with
        | some e'' => (fueledFns mode env).whnfCore d e''
        | none => pure (.app f'x xa)) := by
  have hwapp : WScoped d (Expr.app f'x xa) := by
    simp only [WScoped]
    exact ⟨hwf', hwa⟩
  have hfa : denoteNode s₀.store.denoteT s₀.store.denoteL s₀.store.denoteN (ENode.app f' a)
      = some (.app f'x xa) := by
    rw [denoteNode, hf'd, had]; rfl
  refine SimAt.bind_left (internI_eff hs hfa)
    (fun s₁ fa hs₁ hext₁ hQfa => ?_)
  refine SimAt.bind (iotaRecI_sim ih henv hs₁ hQfa hwapp)
    (fun s₂ o ox hs₂ hext₂ hPo => ?_)
  cases o with
  | some e'' =>
    cases ox with
    | none => exact absurd hPo (by simp [RelO])
    | some e''x =>
      obtain ⟨hred, hwred⟩ := hPo
      exact ih.whnfCore hs₂ hred hwred
  | none =>
    cases ox with
    | some e''x => exact absurd hPo (by simp [RelO])
    | none =>
      exact SimAt.pure hs₂ ⟨denoteT_mono hext₂ hQfa, hwapp⟩

mutual

/-- The bulk-beta argument loop simulates its pure mirror. -/
theorem whnfAppI_sim (ih : SSimI mode env f) (henv : EnvWF env) {d : Nat}
    {kI : EIdx → CheckIM EIdx} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : IState} {i : EIdx} {ex : Expr}, ISOK mode env s →
      s.store.denoteT i = some ex → WScoped d ex →
      SimAt mode env s (RelE d) (kI i) (kM ex)) :
    ∀ {args : List EIdx} {xs : List Expr} {v : EIdx} {vx : Expr}
      {s₀ : IState}, ISOK mode env s₀ →
      s₀.store.denoteT v = some vx → WScoped d vx →
      DenL s₀.store args xs → (∀ x ∈ xs, WScoped d x) →
      SimAt mode env s₀ (RelE d)
        (whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI v args)
        (whnfApp mode (fueledFns mode env) env d kM vx xs)
  | [], xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    match xs, hargs with
    | [], _ =>
      rw [whnfAppI.eq_def]
      dsimp only
      rw [whnfApp_nil]
      exact SimAt.pure hs ⟨hv, hwv⟩
  | a :: rest, xs, v, vx, s₀, hs, hv, hwv, hargs, hwargs => by
    match xs, hargs with
    | xa :: xs, ⟨hax, hrest⟩ =>
      rw [whnfAppI.eq_def]
      dsimp only
      refine SimAt.view ?_
      obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hv
      rw [hn]
      have hwxa : WScoped d xa := hwargs xa (List.mem_cons_self ..)
      have hwrest : ∀ x ∈ xs, WScoped d x :=
        fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
      cases n with
      | lam nmᵢ ty body mb =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨tyx, hty, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bodyx, hbody, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
          simpa only [WScoped] using hwv
        have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
          rw [show bodyx.instantiateList [xa] = bodyx.instantiate1 xa by
            rw [Expr.instantiateList_cons, Expr.instantiateList_nil]]
          exact WScoped.instantiate1_gen hwxa 0 hwtb.2
        rw [whnfApp_lam]
        unfold whnfAppLam
        refine SimAt.bind (ih.infer hs hax hwxa)
          (fun s₁ ta tax hs₁ hext₁ hP => ?_)
        obtain ⟨htad, hwta⟩ := hP
        refine SimAt.bind (ih.defeq hs₁ htad
          (denoteT_mono hext₁ hty) hwta hwtb.1)
          (fun s₂ b b' hs₂ hext₂ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact betaPeelI_sim ih henv hk hs₂
            (denoteT_mono (hext₁.trans hext₂) hbody)
            ⟨denoteT_mono (hext₁.trans hext₂) hax, DenL.nil⟩
            hwsub (hrest.mono (hext₁.trans hext₂)) hwrest
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hfa : denoteNode s₂.store.denoteT s₂.store.denoteL
              s₂.store.denoteN (.app v a)
              = some (.app (.lam nm tyx bodyx bm) xa) := by
            rw [denoteNode,
              denoteT_mono (hext₁.trans hext₂) hv,
              denoteT_mono (hext₁.trans hext₂) hax]
            rfl
          refine SimAt.bind_left (internI_eff hs₂ hfa)
            (fun s₃ fa hs₃ hext₃ hQfa => ?_)
          refine SimAt.of_eff (mkAppNM_eff hs₃ hQfa
            (hrest.mono ((hext₁.trans hext₂).trans hext₃))) _
            (fun s r hQ => ⟨hQ, ?_⟩)
          refine Expr.WScoped.mkAppN ?_ hwrest
          simp only [WScoped]
          exact ⟨hwtb, hwxa⟩
      | bvar k =>
        cases hd
        have hnl : ∀ n' ty' body' mb',
            (.bvar k : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, _, rfl⟩ := hd
        have hnl : ∀ n' ty' body' mb',
            (.sort lu : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | const nmᵢ us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨lus, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        have hnl : ∀ n' ty' body' mb',
            (.const nm lus : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | lit l =>
        cases hd
        have hnl : ∀ n' ty' body' mb',
            (.lit l : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | fvar idx nmᵢ t =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨t', ht', hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.fvar idx nm t' : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | app f₂ a₂ =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ef, hef, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨ea, hea, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.app ef ea : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | forallE nmᵢ t b mm =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, het, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, heb, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.forallE nm et eb bm : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | letE nmᵢ t vv b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, het, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨ev, hev, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, heb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.letE nm et ev eb : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
      | proj snᵢ i pe =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ee, hee, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨sn, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.proj sn i ee : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [whnfApp_ne_lam _ _ _ _ hnl]
        exact whnfAppIotaI_sim ih henv hk hs hv hwv hax hwxa hrest hwrest
  termination_by args _ => (args.length, 0)

/-- The iota arm of the loop simulates its mirror. -/
theorem whnfAppIotaI_sim (ih : SSimI mode env f) (henv : EnvWF env) {d : Nat}
    {kI : EIdx → CheckIM EIdx} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : IState} {i : EIdx} {ex : Expr}, ISOK mode env s →
      s.store.denoteT i = some ex → WScoped d ex →
      SimAt mode env s (RelE d) (kI i) (kM ex))
    {v a : EIdx} {vx xa : Expr} {rest : List EIdx} {xs : List Expr}
    {s₀ : IState} (hs : ISOK mode env s₀)
    (hv : s₀.store.denoteT v = some vx) (hwv : WScoped d vx)
    (hax : s₀.store.denoteT a = some xa) (hwxa : WScoped d xa)
    (hrest : DenL s₀.store rest xs) (hwrest : ∀ x ∈ xs, WScoped d x) :
    SimAt mode env s₀ (RelE d)
      (internI (.app v a) >>= fun fa =>
        iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d fa >>= fun o =>
        match o with
        | some e'' =>
          kI e'' >>= fun v' =>
            whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI v' rest
        | none =>
          whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI fa rest)
      (whnfAppIota mode (fueledFns mode env) env d kM vx xa xs) := by
    unfold whnfAppIota
    have hwapp : WScoped d (.app vx xa) := by
      simp only [WScoped]
      exact ⟨hwv, hwxa⟩
    have hfa : denoteNode s₀.store.denoteT s₀.store.denoteL s₀.store.denoteN (.app v a)
        = some (.app vx xa) := by
      rw [denoteNode, hv, hax]; rfl
    refine SimAt.bind_left (internI_eff hs hfa)
      (fun s₁ fa hs₁ hext₁ hQfa => ?_)
    refine SimAt.bind (iotaRecI_sim ih henv hs₁ hQfa hwapp)
      (fun s₂ o ox hs₂ hext₂ hPo => ?_)
    cases o with
    | some e'' =>
      cases ox with
      | none => exact absurd hPo (by simp [RelO])
      | some e''x =>
        obtain ⟨hred, hwred⟩ := hPo
        refine SimAt.bind (hk hs₂ hred hwred)
          (fun s₃ v' v'x hs₃ hext₃ hP => ?_)
        obtain ⟨hv'd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₃ hv'd hwv'
          (hrest.mono ((hext₁.trans hext₂).trans hext₃)) hwrest
    | none =>
      cases ox with
      | some e''x => exact absurd hPo (by simp [RelO])
      | none =>
        exact whnfAppI_sim ih henv hk hs₂ (denoteT_mono hext₂ hQfa) hwapp
          (hrest.mono (hext₁.trans hext₂)) hwrest
  termination_by (rest.length, 1)

/-- The peel loop simulates its pure mirror. -/
theorem betaPeelI_sim (ih : SSimI mode env f) (henv : EnvWF env) {d : Nat}
    {kI : EIdx → CheckIM EIdx} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : IState} {i : EIdx} {ex : Expr}, ISOK mode env s →
      s.store.denoteT i = some ex → WScoped d ex →
      SimAt mode env s (RelE d) (kI i) (kM ex)) :
    ∀ {args : List EIdx} {xs : List Expr} {t : EIdx} {tx : Expr}
      {acc : List EIdx} {ws : List Expr} {s₀ : IState}, ISOK mode env s₀ →
      s₀.store.denoteT t = some tx → DenL s₀.store acc ws →
      WScoped d (tx.instantiateList ws) →
      DenL s₀.store args xs → (∀ x ∈ xs, WScoped d x) →
      SimAt mode env s₀ (RelE d)
        (betaPeelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI t acc args)
        (betaPeel mode (fueledFns mode env) env d kM tx ws xs)
  | [], xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    match xs, hargs with
    | [], _ =>
      rw [betaPeelI.eq_def]
      dsimp only
      rw [betaPeel_nil]
      refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
        (fun s₁ e' hs₁ hext₁ hQ => ?_)
      exact hk hs₁ hQ hwty
  | a :: rest, xs, t, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    match xs, hargs with
    | xa :: xs, ⟨hax, hrest⟩ =>
      rw [betaPeelI.eq_def]
      dsimp only
      refine SimAt.view ?_
      obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv ht
      rw [hn]
      have hwxa : WScoped d xa := hwargs xa (List.mem_cons_self ..)
      have hwrest : ∀ x ∈ xs, WScoped d x :=
        fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
      cases n with
      | lam nmᵢ ty body mb =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨tyx, hty, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bodyx, hbody, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        rw [betaPeel_lam]
        unfold betaPeelLam
        have hcomp : WScoped d (tyx.instantiateList ws)
            ∧ WScoped d (bodyx.instantiateList ws 1) := by
          rw [instList_lam] at hwty
          simpa only [WScoped] using hwty
        have hwsub : WScoped d (bodyx.instantiateList (xa :: ws)) := by
          rw [Expr.instantiateList_cons]
          exact WScoped.instantiate1_gen hwxa 0 hcomp.2
        refine SimAt.bind_left (instListM_eff (d := 0) hs hty hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.infer hs₁
          (denoteT_mono hext₁ hax) hwxa)
          (fun s₂ ta tax hs₂ hext₂ hP => ?_)
        obtain ⟨htad, hwta⟩ := hP
        refine SimAt.bind (ih.defeq hs₂ htad
          (denoteT_mono hext₂ hQty) hwta hcomp.1)
          (fun s₃ b b' hs₃ hext₃ hPb => ?_)
        obtain rfl : b = b' := hPb
        have hextAll := (hext₁.trans hext₂).trans hext₃
        cases b with
        | true =>
          simp only [↓reduceIte]
          exact betaPeelI_sim ih henv hk hs₃
            (denoteT_mono hextAll hbody)
            ⟨denoteT_mono hextAll hax, hacc.mono hextAll⟩
            hwsub (hrest.mono hextAll) hwrest
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine SimAt.bind_left (instListM_eff (d := 0) hs₃
            (denoteT_mono hextAll ht) (hacc.mono hextAll))
            (fun s₄ f' hs₄ hext₄ hQf' => ?_)
          have hfa : denoteNode s₄.store.denoteT s₄.store.denoteL s₄.store.denoteN (.app f' a)
              = some (.app ((Expr.lam nm tyx bodyx
                bm).instantiateList ws) xa) := by
            rw [denoteNode, hQf',
              denoteT_mono (hextAll.trans hext₄) hax]
            rfl
          refine SimAt.bind_left (internI_eff hs₄ hfa)
            (fun s₅ fa hs₅ hext₅ hQfa => ?_)
          refine SimAt.of_eff (mkAppNM_eff hs₅ hQfa
            (hrest.mono ((hextAll.trans hext₄).trans hext₅))) _
            (fun s r hQ => ⟨hQ, ?_⟩)
          refine Expr.WScoped.mkAppN ?_ hwrest
          simp only [WScoped]
          exact ⟨hwty, hwxa⟩
      | bvar k =>
        cases hd
        have hnl : ∀ n' ty' body' mb',
            (.bvar k : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, _, rfl⟩ := hd
        have hnl : ∀ n' ty' body' mb',
            (.sort lu : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | const nmᵢ us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨lus, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        have hnl : ∀ n' ty' body' mb',
            (.const nm lus : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | lit l =>
        cases hd
        have hnl : ∀ n' ty' body' mb',
            (.lit l : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | fvar idx nmᵢ tt =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨t', ht', hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.fvar idx nm t' : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | app f₂ a₂ =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ef, hef, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨ea, hea, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.app ef ea : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | forallE nmᵢ tt b mm =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, het, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, heb, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.forallE nm et eb bm : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | letE nmᵢ tt vv b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, het, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨ev, hev, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, heb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.letE nm et ev eb : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
      | proj snᵢ i pe =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ee, hee, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨sn, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' ty' body' mb',
            (.proj sn i ee : Expr) ≠ Expr.lam n' ty' body' mb' :=
          fun _ _ _ _ h => nomatch h
        rw [betaPeel_ne_lam _ _ _ _ hnl]
        refine SimAt.bind_left (instListM_eff (d := 0) hs ht hacc)
          (fun s₁ e' hs₁ hext₁ hQ => ?_)
        refine SimAt.bind (hk hs₁ hQ hwty)
          (fun s₂ vv vvx hs₂ hext₂ hP => ?_)
        obtain ⟨hvd, hwv'⟩ := hP
        exact whnfAppI_sim ih henv hk hs₂ hvd hwv'
          ⟨denoteT_mono (hext₁.trans hext₂) hax,
            hrest.mono (hext₁.trans hext₂)⟩ hwargs
  termination_by args _ => (args.length, 1)

end

theorem whnfCoreStepI_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} {kI : EIdx → CheckIM EIdx} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : IState} {i : EIdx} {ex : Expr}, ISOK mode env s →
      s.store.denoteT i = some ex → WScoped d ex →
      SimAt mode env s (RelE d) (kI i) (kM ex))
    {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK mode env s₀)
    (hden : s₀.store.denoteT i = some ex) (hw : WScoped d ex) :
    SimAt mode env s₀ (RelE d)
      (whnfCoreStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfCoreStepM mode (fueledFns mode env) env d kM ex) := by
  unfold whnfCoreStepI
  rw [whnfCoreStepM_unfold]
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hden
  rw [hn]
  cases n with
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | fvar idx nmᵢ t => invert_node hd; exact SimAt.pure hs ⟨hden, hw⟩

  | forallE nmᵢ t b m => invert_node hd; exact SimAt.pure hs ⟨hden, hw⟩

  | lam nmᵢ t b m => invert_node hd; exact SimAt.pure hs ⟨hden, hw⟩

  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | lit l => cases hd; exact SimAt.pure hs ⟨hden, hw⟩
  | bvar k => cases hd; exact SimAt.throw
  | letE nmᵢ t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, het, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, hev, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, heb, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    simp only [WScoped] at hw
    refine SimAt.bind_left (inst1M_eff hs heb hev)
      (fun s₁ e' hs₁ hext₁ hQ => ?_)
    exact hk hs₁ hQ (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
  | app g' a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨xg, hg, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨xa, ha, hd⟩ := hd
    subst hd
    -- Bulk beta (task #50): the twin normalizes the spine head once and
    -- runs the argument loop against its mirror.
    refine SimAt.withStore ?_
    refine SimAt.withStore ?_
    have hhead := getAppFnI_spec hs.wf hden
    have hargs := getAppArgsI_spec hs.wf hden
    refine SimAt.bind (ih.whnfCore hs hhead hw.getAppFn)
      (fun s₁ v vh hs₁ hext₁ hP => ?_)
    exact whnfAppI_sim ih henv hk hs₁ hP.1 hP.2 (hargs.mono hext₁)
      (hw.getAppArgs)
  | proj snᵢ ip pe =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨pex, hpe, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨sn, hnmDen, hd⟩ := hd
    subst hd
    have hwpe : WScoped d pex := by simpa only [WScoped] using hw
    refine SimAt.bind (ih.whnf hs hpe hwpe)
      (fun s₀' e₀ e₀x hs₀' hext₀ hP₀ => ?_)
    obtain ⟨he₀d, hwe₀⟩ := hP₀
    refine SimAt.bind (projLitToCtorI_sim ih hs₀' he₀d hwe₀)
      (fun s₁ e' e'x hs₁ hext₁ hP => ?_)
    obtain ⟨he'd, hwe'⟩ := hP
    have hwproj : WScoped d (Expr.proj sn ip e'x) := by
      simpa only [WScoped] using hwe'
    refine SimAt.bind_left (readbackNM_eff hs₁
      (denoteN_mono (hext₀.trans hext₁) hnmDen))
      (fun s₁' snw hs₁ hextsn hsnw => ?_)
    subst snw
    have hsnDen := denoteN_mono ((hext₀.trans hext₁).trans hextsn) hnmDen
    replace he'd := denoteT_mono hextsn he'd
    rw [mkFEnv_findProj?]
    cases hfp : env.findProj? sn ip with
    | none =>
      dsimp only
      refine SimAt.of_eff (internI_eff hs₁ (x := .proj sn ip e'x) ?_) _
        (fun s pr hQ => ⟨hQ, hwproj⟩)
      rw [denoteNode, he'd, hsnDen]; rfl
    | some entry =>
      dsimp only
      refine SimAt.withStore ?_
      obtain ⟨n', hn', hc', hd'⟩ :=
        denoteT_some_inv (getAppFnI_spec hs₁.wf he'd)
      rw [hn']
      cases n' with
      | const c us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd'
        obtain ⟨lus, hlusDen', hd'⟩ := hd'
        rw [Option.map_eq_some_iff] at hd'
        obtain ⟨cx, hcDen, hd'⟩ := hd'
        rw [← hd']
        have hlen := denoteLList_length hlusDen'
        dsimp only
        refine SimAt.withStore ?_
        have hargs := getAppArgsI_spec hs₁.wf he'd
        refine SimAt.bind_left (beqNameM_eff hs₁ hcDen entry.ctor)
          (fun s₁b bq hs₁ hextb hbq => ?_)
        subst bq
        replace he'd := denoteT_mono hextb he'd
        replace hlusDen' := denoteLList_mono hextb hlusDen'
        replace hargs := hargs.mono hextb
        replace hsnDen := denoteN_mono hextb hsnDen
        rw [hargs.length_eq, ← hlen]
        simp only [beq_iff_eq]
        have hwarg : WScoped d
            (e'x.getAppArgs.getD (entry.numParams + ip) (.bvar 0)) :=
          wscoped_getD hwe'.getAppArgs _
        split
        · rename_i hcond
          obtain ⟨-, rfl, -, -, -⟩ := hcond
          refine SimAt.bind_left (substLevelTreeM_eff hs₁
            (ks := entry.levelParams) entry.structSort hlusDen')
            (fun s₁m mx hs₁m hext₁m hQmx => ?_)
          have hbv : denoteNode s₁m.store.denoteT s₁m.store.denoteL
              s₁m.store.denoteN
              (.bvar 0) = some (.bvar 0) := rfl
          refine SimAt.bind_left (internI_eff hs₁m hbv)
            (fun s₂ bvar0 hs₂ hext₂ hQ0 => ?_)
          refine SimAt.bind_left (substLevelTreeM_eff hs₂
            (ks := entry.levelParams) entry.fieldSort
            (denoteLList_mono (hext₁m.trans hext₂) hlusDen'))
            (fun s₂f fl hs₂f hext₂f hQfl => ?_)
          refine SimAt.bind (projCertI_sim ih hs₂f
            (denoteT_mono ((hext₁m.trans hext₂).trans hext₂f) he'd)
            hwe' hQfl
            (denoteL_mono (hext₂.trans hext₂f) hQmx))
            (fun s₃ b b' hs₃ hext₃ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | true =>
            simp only [↓reduceIte]
            exact hk hs₃
              (DenL.getD
                (denoteT_mono (hext₂f.trans hext₃) hQ0)
                (entry.numParams + ip)
                (hargs.mono (((hext₁m.trans hext₂).trans
                  hext₂f).trans hext₃))) hwarg
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine SimAt.of_eff (internI_eff hs₃
              (x := .proj sn ip e'x) ?_) _
              (fun s pr hQ => ⟨hQ, hwproj⟩)
            rw [denoteNode,
              denoteT_mono (((hext₁m.trans hext₂).trans
                hext₂f).trans hext₃) he'd,
              denoteN_mono (((hext₁m.trans hext₂).trans
                hext₂f).trans hext₃) hsnDen]
            rfl
        · refine SimAt.of_eff (internI_eff hs₁
            (x := .proj sn ip e'x) ?_) _
            (fun s pr hQ => ⟨hQ, hwproj⟩)
          rw [denoteNode, he'd, hsnDen]; rfl
      | bvar k =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | sort u =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | lit l =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | fvar idx nm t =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | app f₂ a₂ =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | lam nm t b m =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | forallE nm t b m =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | letE nm t v b =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl
      | proj s' j' e'' =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd, hsnDen]; rfl

/-- The head-normalization *loop* simulates its mirror, by induction on
the shared step budget (task #106). -/
theorem whnfCoreLoopI_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} :
    ∀ (n : Nat) {i : EIdx} {ex : Expr} {s₀ : IState}, ISOK mode env s₀ →
      s₀.store.denoteT i = some ex → WScoped d ex →
      SimAt mode env s₀ (RelE d)
        (whnfCoreLoopI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfCoreLoopM mode (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimAt.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfCoreLoopI, whnfCoreLoopM]
    exact whnfCoreStepI_sim ih henv
      (fun h1 h2 h3 => whnfCoreLoopI_sim ih henv n h1 h2 h3) hs hden hw

/-- The interned head-normalization body simulates the chained
specification body: the loop run is reproduced by `whnfCoreBody` at
some knot fuel (`whnfCoreLoop_sound_body`). -/
theorem whnfCoreBodyI_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK mode env s₀)
    (hden : s₀.store.denoteT i = some ex) (hw : WScoped d ex) :
    SimAt mode env s₀ (RelE d)
      (whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfCoreBody mode (fueledFns mode env) env d ex) := by
  unfold whnfCoreBodyI
  exact SimAt.wr (whnfCoreLoopI_sim ih henv whnfCoreLoopFuel hs hden hw)
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
theorem whnfStepI_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} {kI : EIdx → CheckIM EIdx} {kM : Expr → FueledM Expr}
    (hk : ∀ {s : IState} {j : EIdx} {ey : Expr}, ISOK mode env s →
      s.store.denoteT j = some ey → WScoped d ey →
      SimAt mode env s (RelE d) (kI j) (kM ey))
    {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK mode env s₀)
    (hden : s₀.store.denoteT i = some ex) (hw : WScoped d ex) :
    SimAt mode env s₀ (RelE d)
      (whnfStepI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d kI i)
      (whnfStep (fueledFns mode env) env d kM ex) := by
  unfold whnfStepI
  rw [whnfStep_unfold]
  refine SimAt.bind (ih.whnfCore hs hden hw)
    (fun s₁ e₁ e₁x hs₁ hext₁ hP => ?_)
  obtain ⟨he₁d, hwe₁⟩ := hP
  refine SimAt.bind (reduceNatI_sim ih hs₁ he₁d hwe₁)
    (fun s₂ o ox hs₂ hext₂ hPo => ?_)
  cases o with
  | some e₂ =>
    cases ox with
    | none => exact absurd hPo (by simp [RelO])
    | some e₂x =>
      obtain ⟨he₂d, hwe₂⟩ := hPo
      exact hk hs₂ he₂d hwe₂
  | none =>
    cases ox with
    | some e₂x => exact absurd hPo (by simp [RelO])
    | none =>
      refine SimAt.bind_left (unfoldDefinitionI_eff hs₂
        (denoteT_mono hext₂ he₁d)) (fun s₃ o₂ hs₃ hext₃ hQ => ?_)
      cases hu : unfoldDefinition env e₁x with
      | some e₂x =>
        rw [hu] at hQ
        cases o₂ with
        | none => exact absurd hQ (by simp [OptDen])
        | some e₂ =>
          exact hk hs₃ hQ (unfoldDefinition_WScoped henv hu hwe₁)
      | none =>
        rw [hu] at hQ
        cases o₂ with
        | some e₂ => exact absurd hQ (by simp [OptDen])
        | none =>
          exact SimAt.pure hs₃
            ⟨denoteT_mono (hext₂.trans hext₃) he₁d, hwe₁⟩

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopI_sim (ih : SSimI mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ (n : Nat) {i : EIdx} {ex : Expr} {s₀ : IState}, ISOK mode env s₀ →
      s₀.store.denoteT i = some ex → WScoped d ex →
      SimAt mode env s₀ (RelE d)
        (whnfLoopI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i)
        (whnfLoop (fueledFns mode env) env d n ex)
  | 0, _, _, _, _, _, _ => SimAt.throw
  | n + 1, _, _, _, hs, hden, hw => by
    simp only [whnfLoopI, whnfLoop]
    exact whnfStepI_sim ih henv
      (fun h1 h2 h3 => whnfLoopI_sim ih henv n h1 h2 h3) hs hden hw

theorem whnfBodyI_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK mode env s₀)
    (hden : s₀.store.denoteT i = some ex) (hw : WScoped d ex) :
    SimAt mode env s₀ (RelE d)
      (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (whnfBody (fueledFns mode env) env d ex) :=
  whnfLoopI_sim ih henv whnfLoopFuel hs hden hw

end Walks2

section Walks3

variable {env : Env} {f : Nat}

set_option maxHeartbeats 4000000 in
/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineI_sim (ih : SSimI mode env f) (henv : EnvWF env) {d : Nat} :
    ∀ {args : List EIdx} {xs : List Expr} {ty : EIdx} {tx : Expr}
      {acc : Array EIdx} {ws : List Expr} {s₀ : IState}, ISOK mode env s₀ →
      s₀.store.denoteT ty = some tx →
      DenL s₀.store acc.toList.reverse ws →
      WScoped d (tx.instantiateList ws) →
      DenL s₀.store args xs → (∀ x ∈ xs, WScoped d x) →
      SimAt mode env s₀ (RelE d)
        (inferSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty acc args)
        (inferSpine (fueledFns mode env) d tx ws xs)
  | [], xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs, hwargs => by
    match xs, hargs with
    | [], _ =>
      rw [inferSpineI.eq_def]
      dsimp only
      rw [inferSpine_nil]
      exact SimAt.of_eff (instListRevM_eff (d := 0) hs ht hacc) _
        (fun s r hQ => ⟨hQ, hwty⟩)
  | a :: rest, xs, ty, tx, acc, ws, s₀, hs, ht, hacc, hwty, hargs,
      hwargs => by
    match xs, hargs with
    | xa :: xs, ⟨hax, hrest⟩ =>
      rw [inferSpineI.eq_def]
      dsimp only
      refine SimAt.view ?_
      obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv ht
      rw [hn]
      have hwxa : WScoped d xa := hwargs xa (List.mem_cons_self ..)
      have hwrest : ∀ x ∈ xs, WScoped d x :=
        fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
      cases n with
      | forallE nmᵢ dom body mb =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨domx, hdom, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bodyx, hbody, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        rw [inferSpine_pi]
        unfold inferSpinePi
        have hcomp : WScoped d (domx.instantiateList ws)
            ∧ WScoped d (bodyx.instantiateList ws 1) := by
          rw [instList_forallE] at hwty
          simpa only [WScoped] using hwty
        have hwsub : WScoped d (bodyx.instantiateList (xa :: ws)) := by
          rw [Expr.instantiateList_cons]
          exact WScoped.instantiate1_gen hwxa 0 hcomp.2
        dsimp only
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs
          hdom hacc)
          (fun s₁ dom' hs₁ hext₁ hQdom => ?_)
        refine SimAt.bind (ih.infer hs₁
          (denoteT_mono hext₁ hax) hwxa)
          (fun s₂ ta tax hs₂ hext₂ hP => ?_)
        obtain ⟨htad, hwta⟩ := hP
        refine SimAt.bind (ih.defeq hs₂ htad
          (denoteT_mono hext₂ hQdom) hwta hcomp.1)
          (fun s₃ b b' hs₃ hext₃ hPb => ?_)
        obtain rfl : b = b' := hPb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.throw_bind
        | true =>
          simp only [↓reduceIte]
          have hextAll := (hext₁.trans hext₂).trans hext₃
          exact inferSpineI_sim ih henv hs₃ (denoteT_mono hextAll hbody)
            (by rw [toListRev_push]; exact ⟨denoteT_mono hextAll hax, hacc.mono hextAll⟩) hwsub
            (hrest.mono hextAll) hwrest
      | bvar k =>
        cases hd
        have hnl : ∀ n' dom' body' bi',
            (.bvar k : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm'ᵢ dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nm', hnmDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm'ᵢ us => invert_node hd'; exact SimAt.throw

        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm'ᵢ t' => invert_node hd'; exact SimAt.throw

        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm'ᵢ t' b' m' => invert_node hd'; exact SimAt.throw

        | letE nm'ᵢ t' v' b' => invert_node hd'; exact SimAt.throw

        | proj s'ᵢ j' e' => invert_node hd'; exact SimAt.throw

      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, _, rfl⟩ := hd
        have hnl : ∀ n' dom' body' bi',
            (.sort lu : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm'ᵢ dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nm', hnmDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm'ᵢ us => invert_node hd'; exact SimAt.throw

        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm'ᵢ t' => invert_node hd'; exact SimAt.throw

        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm'ᵢ t' b' m' => invert_node hd'; exact SimAt.throw

        | letE nm'ᵢ t' v' b' => invert_node hd'; exact SimAt.throw

        | proj s'ᵢ j' e' => invert_node hd'; exact SimAt.throw

      | const nmᵢ us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨lus, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        have hnl : ∀ n' dom' body' bi',
            (.const nm lus : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm' dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nmw, hnmwDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm' us => invert_node hd'; exact SimAt.throw
        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm' t' => invert_node hd'; exact SimAt.throw
        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
        | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
        | proj s' j' e' => invert_node hd'; exact SimAt.throw
      | lit l =>
        cases hd
        have hnl : ∀ n' dom' body' bi',
            (.lit l : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm'ᵢ dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nm', hnmDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm'ᵢ us => invert_node hd'; exact SimAt.throw

        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm'ᵢ t' => invert_node hd'; exact SimAt.throw

        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm'ᵢ t' b' m' => invert_node hd'; exact SimAt.throw

        | letE nm'ᵢ t' v' b' => invert_node hd'; exact SimAt.throw

        | proj s'ᵢ j' e' => invert_node hd'; exact SimAt.throw

      | fvar idx nmᵢ tt =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨t', ht', hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' dom' body' bi',
            (.fvar idx nm t' : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm' dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nmw, hnmwDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm' us => invert_node hd'; exact SimAt.throw
        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm' t' => invert_node hd'; exact SimAt.throw
        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
        | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
        | proj s' j' e' => invert_node hd'; exact SimAt.throw
      | app f₂ a₂ =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ef, hef, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨ea, hea, hd⟩ := hd
        subst hd
        have hnl : ∀ n' dom' body' bi',
            (.app ef ea : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm'ᵢ dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nm', hnmDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm'ᵢ us => invert_node hd'; exact SimAt.throw

        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm'ᵢ t' => invert_node hd'; exact SimAt.throw

        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm'ᵢ t' b' m' => invert_node hd'; exact SimAt.throw

        | letE nm'ᵢ t' v' b' => invert_node hd'; exact SimAt.throw

        | proj s'ᵢ j' e' => invert_node hd'; exact SimAt.throw

      | lam nmᵢ tt b mm =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, het, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, heb, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' dom' body' bi',
            (.lam nm et eb bm : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm' dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nm, hnmDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm' us => invert_node hd'; exact SimAt.throw
        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm' t' => invert_node hd'; exact SimAt.throw
        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
        | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
        | proj s' j' e' => invert_node hd'; exact SimAt.throw
      | letE nmᵢ tt vv b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, het, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨ev, hev, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, heb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' dom' body' bi',
            (.letE nm et ev eb : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm' dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nm, hnmDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm' us => invert_node hd'; exact SimAt.throw
        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm' t' => invert_node hd'; exact SimAt.throw
        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
        | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
        | proj s' j' e' => invert_node hd'; exact SimAt.throw
      | proj snᵢ i pe =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ee, hee, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨sn, hnmDen, hd⟩ := hd
        subst hd
        have hnl : ∀ n' dom' body' bi',
            (.proj sn i ee : Expr) ≠ Expr.forallE n' dom' body' bi' :=
          fun _ _ _ _ h => nomatch h
        rw [inferSpine_ne_pi _ _ hnl]
        unfold inferSpineWhnf
        refine SimAt.bind_left (instListRevM_eff (d := 0) hs ht hacc)
          (fun s₁ ty' hs₁ hext₁ hQty => ?_)
        refine SimAt.bind (ih.whnf hs₁ hQty hwty)
          (fun s₂ w wx hs₂ hext₂ hP => ?_)
        obtain ⟨hwd, hww⟩ := hP
        refine SimAt.view ?_
        obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
        rw [hn']
        cases n' with
        | forallE nm' dom body mb =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd'
          obtain ⟨domx, hdom, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bodyx, hbody, hd'⟩ := hd'
          rw [Option.bind_eq_some_iff] at hd'
          obtain ⟨bm, hbmDen, hd'⟩ := hd'
          rw [Option.map_eq_some_iff] at hd'
          obtain ⟨nmw, hnmwDen, hd'⟩ := hd'
          subst hd'
          have hwtb : WScoped d domx ∧ WScoped d bodyx := by
            simpa only [WScoped] using hww
          have hwsub : WScoped d (bodyx.instantiateList [xa]) := by
            rw [instList_single]
            exact WScoped.instantiate1_gen hwxa 0 hwtb.2
          dsimp only
          refine SimAt.bind (ih.infer hs₂
            (denoteT_mono (hext₁.trans hext₂) hax) hwxa)
            (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htad, hwta⟩ := hP₃
          refine SimAt.bind (ih.defeq hs₃ htad
            (denoteT_mono hext₃ hdom) hwta hwtb.1)
            (fun s₄ b b' hs₄ hext₄ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hextAll := hext₃.trans hext₄
            exact inferSpineI_sim ih henv hs₄
              (denoteT_mono hextAll hbody)
              (by
              rw [toListRev_singleton]
              exact ⟨denoteT_mono ((hext₁.trans hext₂).trans hextAll) hax, DenL.nil⟩) hwsub
              (hrest.mono ((hext₁.trans hext₂).trans hextAll)) hwrest
        | bvar k => invert_node hd'; exact SimAt.throw
        | sort u => invert_node hd'; exact SimAt.throw
        | const nm' us => invert_node hd'; exact SimAt.throw
        | lit l => invert_node hd'; exact SimAt.throw
        | fvar idx' nm' t' => invert_node hd'; exact SimAt.throw
        | app f' a' => invert_node hd'; exact SimAt.throw
        | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
        | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
        | proj s' j' e' => invert_node hd'; exact SimAt.throw

theorem inferBodyI_sim (ih : SSimI mode env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK mode env s₀)
    (hden : s₀.store.denoteT i = some ex) (hw : WScoped d ex) :
    SimAt mode env s₀ (RelE d)
      (inferBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (inferBody mode (fueledFns mode env) env d ex) := by
  unfold inferBodyI
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hden
  rw [hn]
  cases n with
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, hlu, rfl⟩ := hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    refine SimAt.bind_left (internLM_eff hs (n := .succ u)
      (l := .succ lu) (by rw [denoteLNode, hlu]; rfl))
      (fun s₁ su hs₁ hext₁ hsu => ?_)
    exact SimAt.of_eff (internI_eff hs₁ (n := .sort su)
      (x := .sort (.succ lu)) (by rw [denoteNode, hsu]; rfl)) _
      (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
  | bvar k =>
    cases hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    exact SimAt.throw
  | letE nmᵢ t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, het, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, hev, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, heb, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    simp only [WScoped] at hw
    -- task #100 stage 6: the `let` checks moved here from the deleted
    -- annotation pass (official `infer_let` order)
    refine SimAt.bind (ih.infer hs het hw.1)
      (fun s₁ tty ttyx hs₁ hext₁ hP₁ => ?_)
    obtain ⟨httyd, hwtty⟩ := hP₁
    refine SimAt.bind (ensureSortI_sim ih hs₁ httyd hwtty)
      (fun s₂ u lu hs₂ hext₂ _hPu => ?_)
    refine SimAt.bind (ih.infer hs₂
      (denoteT_mono (hext₁.trans hext₂) hev) hw.2.1)
      (fun s₃ tv tvx hs₃ hext₃ hP₃ => ?_)
    obtain ⟨htvd, hwtv⟩ := hP₃
    refine SimAt.bind (ih.defeq hs₃ htvd
      (denoteT_mono ((hext₁.trans hext₂).trans hext₃) het) hwtv hw.1)
      (fun s₄ bb bb' hs₄ hext₄ hPb => ?_)
    obtain rfl : bb = bb' := hPb
    cases bb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.throw_bind
    | true =>
      simp only [↓reduceIte]
      refine SimAt.bind_left (inst1M_eff hs₄
        (denoteT_mono (((hext₁.trans hext₂).trans hext₃).trans hext₄) heb)
        (denoteT_mono (((hext₁.trans hext₂).trans hext₃).trans hext₄) hev))
        (fun s₅ e' hs₅ hext₅ hQ => ?_)
      exact ih.infer hs₅ hQ (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
  | fvar idx nmᵢ t =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    have h' : idx < d ∧ WScoped idx tyx := by
      simpa only [WScoped] using hw
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimAt.pure hs ⟨hty, WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimAt.throw
  | lit l =>
    cases hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimAt.bind_left (internNameM_eff hs natName)
          (fun s₁ ni hs₁ hext₁ hQni => ?_)
        exact SimAt.of_eff (internI_eff hs₁ (x := .const natName [])
          (by rw [denoteNode, hQni]; rfl))
          _ (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimAt.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimAt.bind_left (internNameM_eff hs stringName)
          (fun s₁ ni hs₁ hext₁ hQni => ?_)
        exact SimAt.of_eff (internI_eff hs₁ (x := .const stringName [])
          (by rw [denoteNode, hQni]; rfl))
          _ (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimAt.throw
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, hlusDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    refine SimAt.bind_left (readbackNM_eff hs hnmDen)
      (fun s₀' nw hs hext' hnw => ?_)
    subst nw
    replace hnmDen := denoteN_mono hext' hnmDen
    replace hlusDen := denoteLList_mono hext' hlusDen
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimAt.throw
    | some ci =>
      dsimp only
      rw [show lus.length = us.length from
        (denoteLList_length hlusDen).symm]
      by_cases hlen : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hlen, if_pos hlen]
        refine SimAt.of_eff (constTyAtM_eff hs hnmDen hlusDen hfn) _
          (fun s r hQ => ?_)
        refine ⟨hQ, ?_⟩
        obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
        exact wscoped_instLevels_of_not_hasFvar htf _ _
      · rw [if_neg hlen, if_neg hlen]
        exact SimAt.throw_bind
  | forallE nmᵢ t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    refine SimAt.bind (ih.infer hs hty hwtb.1)
      (fun s₁ tty ttyx hs₁ hext₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimAt.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hext₂ hP₂ => ?_)
    obtain ⟨hwd, hww⟩ := hP₂
    refine SimAt.view ?_
    obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
    rw [hn']
    cases n' with
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd'
      obtain ⟨lu, hlu, rfl⟩ := hd'
      have hext₀₂ := hext₁.trans hext₂
      have hfvd : denoteNode s₂.store.denoteT s₂.store.denoteL
          s₂.store.denoteN
          (.fvar d nmᵢ t) = some (.fvar d nm tyx) := by
        rw [denoteNode, denoteT_mono hext₀₂ hty,
          denoteN_mono hext₀₂ hnmDen]; rfl
      refine SimAt.bind_left (internI_eff hs₂ hfvd)
        (fun s₃ fv hs₃ hext₃ hQfv => ?_)
      refine SimAt.withStore ?_
      dsimp only
      rw [show bm.pw = (m : IBinderMeta).pw from denoteBM_pw hbmDen]
      exact inferPisI_tail_sim ih hs₃
        (denoteT_mono (hext₀₂.trans hext₃) hbody)
        (denoteL_mono hext₃ hlu) hQfv hwtb.1 hwtb.2
    | bvar k => invert_node hd'; exact SimAt.throw
    | const nm' us => invert_node hd'; exact SimAt.throw
    | lit l => invert_node hd'; exact SimAt.throw
    | fvar idx nm' t' => invert_node hd'; exact SimAt.throw
    | app f' a' => invert_node hd'; exact SimAt.throw
    | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
    | forallE nm' t' b' m' => invert_node hd'; exact SimAt.throw
    | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
    | proj s' j' e' => invert_node hd'; exact SimAt.throw
  | lam nmᵢ t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    obtain rfl : bm = ⟨(m : IBinderMeta).bi, (m : IBinderMeta).pw⟩ := by
      obtain ⟨mbi, mpw⟩ := m
      simpa [denoteBM] using hbmDen.symm
    refine SimAt.bind (ih.infer hs hty hwtb.1)
      (fun s₁ tty ttyx hs₁ hext₁ hP => ?_)
    obtain ⟨httyd, hwtty⟩ := hP
    refine SimAt.bind (ih.whnf hs₁ httyd hwtty)
      (fun s₂ w wx hs₂ hext₂ hP₂ => ?_)
    obtain ⟨hwd, hww⟩ := hP₂
    refine SimAt.view ?_
    obtain ⟨n', hn', hc', hd'⟩ := denoteT_some_inv hwd
    rw [hn']
    cases n' with
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd'
      obtain ⟨lu, hlu, rfl⟩ := hd'
      have hext₀₂ := hext₁.trans hext₂
      have hfvd : denoteNode s₂.store.denoteT s₂.store.denoteL
          s₂.store.denoteN
          (.fvar d nmᵢ t) = some (.fvar d nm tyx) := by
        rw [denoteNode, denoteT_mono hext₀₂ hty,
          denoteN_mono hext₀₂ hnmDen]; rfl
      refine SimAt.bind_left (internI_eff hs₂ hfvd)
        (fun s₃ fv hs₃ hext₃ hQfv => ?_)
      refine SimAt.withStore ?_
      exact inferLamsI_tail_sim ih henv hs₃
        (denoteN_mono (hext₀₂.trans hext₃) hnmDen)
        (denoteT_mono (hext₀₂.trans hext₃) hbody)
        (denoteT_mono (hext₀₂.trans hext₃) hty)
        hQfv hwtb.1 hwtb.2
    | bvar k => invert_node hd'; exact SimAt.throw
    | const nm' us => invert_node hd'; exact SimAt.throw
    | lit l => invert_node hd'; exact SimAt.throw
    | fvar idx nm' t' => invert_node hd'; exact SimAt.throw
    | app f' a' => invert_node hd'; exact SimAt.throw
    | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
    | forallE nm' t' b' m' => invert_node hd'; exact SimAt.throw
    | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
    | proj s' j' e' => invert_node hd'; exact SimAt.throw
  | app g' a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨xg, hg, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨xa, ha, hd⟩ := hd
    subst hd
    -- Bulk telescope consumption (task #50): the twin infers the spine
    -- head once and walks the Π-telescope; `inferSpine_sound_body`
    -- reproduces the loop's verdict in the chained body.
    refine SimAt.wr ?_ (fun v F hF => inferSpine_sound_body d xg xa v F hF)
    refine SimAt.withStore ?_
    refine SimAt.withStore ?_
    have hhead := getAppFnI_spec hs.wf hden
    have hargsSpec := getAppArgsI_spec hs.wf hden
    refine SimAt.bind (ih.infer hs hhead hw.getAppFn)
      (fun s₁ tf tfx hs₁ hext₁ hP => ?_)
    refine inferSpineI_sim ih henv hs₁ hP.1
      (by rw [toListRev_empty]; exact DenL.nil) ?_
      (hargsSpec.mono hext₁) hw.getAppArgs
    rw [Expr.instantiateList_nil]
    exact hP.2
  | proj snᵢ ip pe =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨pex, hpe, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨sn, hnmDen, hd⟩ := hd
    subst hd
    have hwpe : WScoped d pex := by simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    refine SimAt.bind (ih.infer hs hpe hwpe)
      (fun s₁ tpe tpex hs₁ hext₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimAt.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hext₂ hP₂ => ?_)
    obtain ⟨hted, hwte⟩ := hP₂
    refine SimAt.withStore ?_
    obtain ⟨n', hn', hc', hd'⟩ :=
      denoteT_some_inv (getAppFnI_spec hs₂.wf hted)
    rw [hn']
    cases n' with
    | const Tᵢ us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨lus, hlusDen, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨T, hTDen, hd'⟩ := hd'
      rw [← hd']
      dsimp only
      refine SimAt.bind_left (readbackNM_eff hs₂ hTDen)
        (fun s₂' Tw hs₂ hextT hTw => ?_)
      subst Tw
      replace hTDen := denoteN_mono hextT hTDen
      replace hted := denoteT_mono hextT hted
      replace hlusDen := denoteLList_mono hextT hlusDen
      replace hpe := denoteT_mono ((hext₁.trans hext₂).trans hextT) hpe
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimAt.throw
      | some entry =>
        dsimp only
        refine SimAt.withStore ?_
        have htargs := getAppArgsI_spec hs₂.wf hted
        rw [htargs.length_eq,
          show lus.length = us.length from
            (denoteLList_length hlusDen).symm]
        split
        · refine SimAt.bind_left (projFnIdxM_eff hs₂ hTDen ip)
            (fun s₂p pf hs₂ hextp hQpf => ?_)
          refine SimAt.bind_left (constTyAtM_eff hs₂ hQpf
            (denoteLList_mono hextp hlusDen)
            (Env.findProj?_some hfp))
            (fun s₃ pty hs₃ hext₃' hQty => ?_)
          have hext₃ := hextp.trans hext₃'
          simp only [ConstantInfo.toConstantVal] at hQty
          replace htargs := htargs.mono hext₃
          replace hpe := denoteT_mono hext₃ hpe
          refine SimAt.bind_left (piResidualM_eff hs₃ hQty
            (htargs.append (DenL.cons hpe DenL.nil)))
            (fun s₄ ores hs₄ hext₄ hQres => ?_)
          cases hres : piResidual
              (entry.ty.instantiateLevelParams entry.levelParams lus)
              (tex.getAppArgs ++ [pex]) with
          | some resTy =>
            rw [hres] at hQres
            cases ores with
            | none => exact absurd hQres (by simp [OptDen])
            | some res =>
              refine SimAt.pure hs₄ ⟨hQres, ?_⟩
              have hclosed := (henv _ (find?_mem
                (Env.findProj?_some hfp))).1
              refine piResidual_WScoped hres
                (WScoped.of_not_hasFvar (by
                  rw [hasFvar_instantiateLevelParams]
                  exact hclosed)) ?_
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hwte.getAppArgs x hx
              · rcases List.mem_singleton.mp hx with rfl
                exact hwpe
          | none =>
            rw [hres] at hQres
            cases ores with
            | some res => exact absurd hQres (by simp [OptDen])
            | none => exact SimAt.throw
        · exact SimAt.throw
    | bvar k => invert_head hd'; exact SimAt.throw
    | sort u => invert_head hd'; exact SimAt.throw
    | lit l => invert_head hd'; exact SimAt.throw
    | fvar idx nm' t' => invert_head hd'; exact SimAt.throw
    | app f' a' => invert_head hd'; exact SimAt.throw
    | lam nm' t' b' m' => invert_head hd'; exact SimAt.throw
    | forallE nm' t' b' m' => invert_head hd'; exact SimAt.throw
    | letE nm' t' v' b' => invert_head hd'; exact SimAt.throw
    | proj s' j' e' => invert_head hd'; exact SimAt.throw

end Walks3

end Setlec
