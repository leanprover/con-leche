import Setlec.Verify.SimIKnot
import Setlec.Verify.Disc

/-!
# Interned body walks, part 1: list helpers and small twins

Per-helper simulation walks: each interned twin
(`Setlec/Kernel/CoreI.lean`) is `SimAt`-related to its `Expr` original
at the fueled record, on denoting well-scoped inputs.  The walks mirror
`Setlec/Verify/Disc.lean`'s structure: bind-chains through the record
sites (the `SSimI` induction hypothesis), scoping facts threaded via
the `WScoped` toolkit, denote facts transported along store extensions.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

/-- Collapse a `denoteNode … = some x` hypothesis for a *default* match
arm: substitute `x`'s head shape (child denotations are discarded). -/
macro "invert_node" hd:ident : tactic => `(tactic| (
  first
  | (rw [denoteNode, Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, hInvEq⟩ := $hd:ident; subst hInvEq)
  | (rw [denoteNode, Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, hInvEq⟩ := $hd:ident; subst hInvEq)
  | (rw [denoteNode, Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, hInvEq⟩ := $hd:ident; subst hInvEq)
  | (rw [denoteNode, Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, hInvEq⟩ := $hd:ident; subst hInvEq)
  | (cases $hd:ident)))

/-- Like `invert_node`, but for a hypothesis whose right-hand side is a
compound expression (e.g. `some x.getAppFn`): rewrite it backwards
instead of substituting. -/
macro "invert_head" hd:ident : tactic => `(tactic| (
  first
  | (rw [denoteNode, Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident; rw [← $hd:ident])
  | (rw [denoteNode, Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident; rw [← $hd:ident])
  | (rw [denoteNode, Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident; rw [← $hd:ident])
  | (rw [denoteNode, Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.bind_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident;
     rw [Option.map_eq_some_iff] at $hd:ident;
     obtain ⟨_, _, $hd:ident⟩ := $hd:ident; rw [← $hd:ident])
  | (rw [← Option.some.inj $hd:ident])))

section Walks

variable {env : Env} {f : Nat}


theorem defEqListI_sim (ih : SSimI env f) {d : Nat} :
    ∀ {args : List EIdx} {xs : List Expr} {brgs : List EIdx}
      {ys : List Expr} {s₀ : IState}, ISOK env s₀ →
      DenL s₀.store args xs → DenL s₀.store brgs ys →
      (∀ x ∈ xs, WScoped d x) → (∀ y ∈ ys, WScoped d y) →
      SimAt env s₀ RelV (defEqListI (coreKnotI (mkFEnv env) f) (mkFEnv env) d args brgs)
        (defEqList (fueledFns env) env d xs ys) := by
  intro args
  induction args with
  | nil =>
    intro xs brgs ys s₀ hs hargs hbrgs _ _
    match xs, hargs with
    | [], _ =>
      match brgs, ys, hbrgs with
      | [], [], _ => exact SimAt.pure hs rfl
      | b :: bs, y :: ys, _ => exact SimAt.pure hs rfl
      | [], _ :: _, h | _ :: _, [], h => exact absurd h (by simp [DenL])
  | cons a as iha =>
    intro xs brgs ys s₀ hs hargs hbrgs hwx hwy
    match xs, hargs with
    | x :: xs, ⟨hax, hasxs⟩ =>
      match brgs, ys, hbrgs with
      | [], [], _ => exact SimAt.pure hs rfl
      | [], _ :: _, h | _ :: _, [], h => exact absurd h (by simp [DenL])
      | b :: bs, y :: ys, ⟨hby, hbsys⟩ =>
        show SimAt env s₀ RelV
          ((coreKnotI (mkFEnv env) f).defeq d a b >>= fun r =>
            if r then defEqListI (coreKnotI (mkFEnv env) f) (mkFEnv env) d as bs else pure false)
          ((fueledFns env).defeq d x y >>= fun r =>
            if r then defEqList (fueledFns env) env d xs ys else pure false)
        refine SimAt.bind (ih.defeq hs hax hby
          (hwx x (List.mem_cons_self ..)) (hwy y (List.mem_cons_self ..)))
          (fun s₁ rb r hs₁ hext₁ hP => ?_)
        obtain rfl : rb = r := hP
        cases rb with
        | true =>
          simp only [↓reduceIte]
          exact iha hs₁ (hasxs.mono hext₁) (hbsys.mono hext₁)
            (fun x hx => hwx x (List.mem_cons_of_mem _ hx))
            (fun y hy => hwy y (List.mem_cons_of_mem _ hy))
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.pure hs₁ rfl

theorem iotaCertsIAux_sim (ih : SSimI env f) {d : Nat} :
    ∀ {args : List EIdx} {xs : List Expr} {acc : List EIdx}
      {ws : List Expr} {ty : EIdx} {tyx : Expr} {s₀ : IState}, ISOK env s₀ →
      s₀.store.denote ty = some tyx → DenL s₀.store acc ws →
      WScoped d (tyx.instantiateList ws) →
      DenL s₀.store args xs → (∀ x ∈ xs, WScoped d x) →
      SimAt env s₀ RelV
        (iotaCertsIAux (coreKnotI (mkFEnv env) f) (mkFEnv env) d ty acc args)
        (iotaCerts (fueledFns env) env d (tyx.instantiateList ws) xs)
  | [], xs, acc, ws, ty, tyx, s₀, hs, hty, hacc, hwty, hargs, hwargs => by
    match xs, hargs with
    | [], _ =>
      rw [iotaCertsIAux.eq_def]
      dsimp only
      exact SimAt.pure hs rfl
  | a :: as, xs, acc, ws, ty, tyx, s₀, hs, hty, hacc, hwty, hargs, hwargs => by
    match xs, hargs with
    | x :: xs, ⟨hax, hasxs⟩ =>
      rw [iotaCertsIAux.eq_def]
      refine SimAt.view ?_
      obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hty
      have hn := getNode_of_stored hn
      rw [hn]
      cases n with
      | forallE nmᵢ t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, hth, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, hbh, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        rw [show (Expr.forallE nm et eb bm).instantiateList ws
            = .forallE nm (et.instantiateList ws)
                (eb.instantiateList ws 1) bm by
          simp [Expr.instantiateList]] at hwty ⊢
        have hwtb : WScoped d (et.instantiateList ws)
            ∧ WScoped d (eb.instantiateList ws 1) := by
          simpa only [WScoped] using hwty
        show SimAt env s₀ RelV
          (instListM t acc >>= fun dom' =>
            (coreKnotI (mkFEnv env) f).infer d a >>= fun ta =>
            (coreKnotI (mkFEnv env) f).defeq d ta dom' >>= fun r =>
            if r then iotaCertsIAux (coreKnotI (mkFEnv env) f)
              (mkFEnv env) d b (a :: acc) as
            else pure false)
          ((fueledFns env).infer d x >>= fun ta =>
            (fueledFns env).defeq d ta (et.instantiateList ws) >>= fun r =>
            if r then iotaCerts (fueledFns env) env d
              ((eb.instantiateList ws 1).instantiate1 x) xs
            else pure false)
        have hwx : WScoped d x := hwargs x (List.mem_cons_self ..)
        refine SimAt.bind_left (instListM_eff (d := 0) hs hth hacc)
          (fun s₁ dom' hs₁ hext₁ hQdom => ?_)
        refine SimAt.bind (ih.infer hs₁ (denote_mono hext₁ hax) hwx)
          (fun s₂ ta tax hs₂ hext₂ hP => ?_)
        obtain ⟨htax, hwtax⟩ := hP
        refine SimAt.bind (ih.defeq hs₂ htax
          (denote_mono hext₂ hQdom) hwtax hwtb.1)
          (fun s₃ rb r hs₃ hext₃ hP₂ => ?_)
        obtain rfl : rb = r := hP₂
        cases rb with
        | true =>
          simp only [↓reduceIte]
          rw [← Expr.instantiateList_cons]
          have hextAll := (hext₁.trans hext₂).trans hext₃
          refine iotaCertsIAux_sim ih hs₃
            (denote_mono hextAll hbh)
            ⟨denote_mono hextAll hax, hacc.mono hextAll⟩
            ?_ (hasxs.mono hextAll)
            (fun x' hx' => hwargs x' (List.mem_cons_of_mem _ hx'))
          rw [Expr.instantiateList_cons]
          exact WScoped.instantiate1_gen hwx 0 hwtb.2
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.pure hs₃ rfl
      | bvar k =>
        cases hd
        match hacceq : acc, ws, hacc with
        | [], [], _ =>
          rw [Expr.instantiateList_nil]
          exact SimAt.pure hs rfl
        | a' :: acc', w :: ws', hacc =>
          show SimAt env s₀ RelV
            (instListM ty (a' :: acc') >>= fun ty' =>
              iotaCertsIAux (coreKnotI (mkFEnv env) f) (mkFEnv env)
                d ty' [] (a :: as))
            (iotaCerts (fueledFns env) env d
              ((Expr.bvar k).instantiateList (w :: ws')) (x :: xs))
          refine SimAt.bind_left (instListM_eff (d := 0) hs hty hacc)
            (fun s₁ ty' hs₁ hext₁ hQty => ?_)
          have := iotaCertsIAux_sim ih (acc := []) (ws := [])
            (args := a :: as) (xs := x :: xs) hs₁ hQty DenL.nil
            (by rw [Expr.instantiateList_nil]; exact hwty)
            (⟨denote_mono hext₁ hax, hasxs.mono hext₁⟩) hwargs
          rwa [Expr.instantiateList_nil] at this
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, _, rfl⟩ := hd
        rw [show (Expr.sort lu).instantiateList ws = .sort lu by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | const nmᵢ us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨lus, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        rw [show (Expr.const nm lus).instantiateList ws = .const nm lus by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | lit l =>
        cases hd
        rw [show (Expr.lit l).instantiateList ws = .lit l by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | fvar idx nmᵢ t =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨t', _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        rw [show (Expr.fvar idx nm t').instantiateList ws
            = .fvar idx nm t' by simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | app f' a' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ef, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨ea, _, rfl⟩ := hd
        rw [show (Expr.app ef ea).instantiateList ws
            = .app (ef.instantiateList ws) (ea.instantiateList ws) by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | lam nmᵢ t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨bm, hbmDen, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        rw [show (Expr.lam nm et eb bm).instantiateList ws
            = .lam nm (et.instantiateList ws)
                (eb.instantiateList ws 1) bm by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | letE nmᵢ t v b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨ev, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨nm, hnmDen, rfl⟩ := hd
        rw [show (Expr.letE nm et ev eb).instantiateList ws
            = .letE nm (et.instantiateList ws) (ev.instantiateList ws)
                (eb.instantiateList ws 1) by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
      | proj s'ᵢ j e' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ee, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨s', hnmDen, rfl⟩ := hd
        rw [show (Expr.proj s' j ee).instantiateList ws
            = .proj s' j (ee.instantiateList ws) by
          simp [Expr.instantiateList]]
        exact SimAt.pure hs rfl
termination_by args _ acc => (args.length, acc.length)
decreasing_by
  · apply Prod.Lex.right'
    · simp
    · rw [hacceq]; simp
  · apply Prod.Lex.left; simp

theorem iotaCertsI_sim (ih : SSimI env f) {d : Nat} :
    ∀ {args : List EIdx} {xs : List Expr} {ty : EIdx} {tyx : Expr}
      {s₀ : IState}, ISOK env s₀ →
      s₀.store.denote ty = some tyx → WScoped d tyx →
      DenL s₀.store args xs → (∀ x ∈ xs, WScoped d x) →
      SimAt env s₀ RelV (iotaCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d ty args)
        (iotaCerts (fueledFns env) env d tyx xs) := by
  intro args xs ty tyx s₀ hs hty hwty hargs hwargs
  have := iotaCertsIAux_sim ih (acc := []) (ws := []) hs hty DenL.nil
    (by rw [Expr.instantiateList_nil]; exact hwty) hargs hwargs
  rw [Expr.instantiateList_nil] at this
  exact this

end Walks

section Walks2

variable {env : Env} {f : Nat}

theorem ensureSortI_sim (ih : SSimI env f) {d : Nat} {i : EIdx} {e : Expr}
    {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e) (hw : WScoped d e) :
    SimAt env s₀ RelL (ensureSortI (coreKnotI (mkFEnv env) f) d i)
      (ensureSort (fueledFns env) env d e) := by
  show SimAt env s₀ RelL
    ((coreKnotI (mkFEnv env) f).whnf d i >>= fun w =>
      viewI w >>= fun n =>
      match n with
      | some (.sort u) => pure u
      | _ => throw (.invalid "expected a sort"))
    ((fueledFns env).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
  refine SimAt.bind (ih.whnf hs hden hw) (fun s₁ w wx hs₁ hext₁ hP => ?_)
  obtain ⟨hwden, hww⟩ := hP
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hwden
  have hn := getNode_of_stored hn
  rw [hn]
  cases n with
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, hlu, rfl⟩ := hd
    exact SimAt.pure hs₁ hlu
  | bvar k => cases hd; exact SimAt.throw
  | const nmᵢ us => invert_node hd; exact SimAt.throw

  | lit l => cases hd; exact SimAt.throw
  | fvar idx nmᵢ t => invert_node hd; exact SimAt.throw

  | app f' a' => invert_node hd; exact SimAt.throw
  | lam nmᵢ t b m => invert_node hd; exact SimAt.throw

  | forallE nmᵢ t b m => invert_node hd; exact SimAt.throw

  | letE nmᵢ t v b => invert_node hd; exact SimAt.throw

  | proj s'ᵢ j e' => invert_node hd; exact SimAt.throw

/-- The **codomain-sort memo** (task #100) simulates the fueled
`codOfF`: a cache hit consumes the backed entry at the call's depth, a
miss runs `infer` then `ensureSort` and re-inserts the result in the
depth-universal form, exactly as the entry-point memos do. -/
theorem codOfI_sim (ih : SSimI env f) (henv : EnvWF env) {d : Nat}
    {i : EIdx} {e : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e) (hw : WScoped d e) :
    SimAt env s₀ RelL (codOfI (coreKnotI (mkFEnv env) f) d i)
      (codOfF env d e) := by
  have hbody : SimAt env s₀ RelL
      (codOfBodyI (coreKnotI (mkFEnv env) f) d i) (codOfF env d e) :=
    SimAt.bind (ih.infer hs hden hw)
      (fun _ _ _ hs₁ _ hP => ensureSortI_sim ih hs₁ hP.1 hP.2)
  intro v' s' hr
  rw [show codOfI (coreKnotI (mkFEnv env) f) d i =
    memoLI (·.codOfC) (fun st mp => { st with codOfC := mp })
      (fun d e => codOfBodyI (coreKnotI (mkFEnv env) f) d e) d i from rfl] at hr
  simp only [memoLI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.codOfC[i]? with
  | some u =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨a, l, hia, hul, F, hall⟩ := hs.codOfC i _ hl
    rw [hden] at hia
    cases hia
    exact ⟨hs, Ext.refl _, l, hul, F, by
      rw [codOfF_atF]; exact hall d hw.to_wscopedB⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : codOfBodyI (coreKnotI (mkFEnv env) f) d i s₀ with
    | error err =>
      rw [hb] at hr
      simp only [Bind.bind, Except.bind] at hr
      exact nomatch hr
    | ok pr =>
      obtain ⟨r, s₁⟩ := pr
      rw [hb] at hr
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      obtain ⟨hs₁, hext₁, l, hrv, F, hF⟩ := hbody r s₁ hb
      rw [codOfF_atF] at hF
      have hins := hs₁.insertCodOfC (denote_mono hext₁ hden) hrv
        ⟨F, fun d' hd' => by
          rw [codOfCore_depth_inv henv F hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, hext₁, l, hrv, F, by rw [codOfF_atF]; exact hF⟩

/-- `litToCtorIfNatI` computes (an index denoting) the spec's
`litToCtorIfNat`. -/
theorem litToCtorIfNatI_eff {s₀ : IState} (hs : ISOK env s₀)
    {i : EIdx} {e : Expr} (hden : s₀.store.denote i = some e) :
    IEff env s₀ (fun s r => s.store.denote r = some (litToCtorIfNat env e))
      (litToCtorIfNatI (mkFEnv env) i) := by
  show IEff env s₀ _ (viewI i >>= fun n =>
    match n with
    | some (.lit (.natVal n)) =>
      if natLitSupportedF (mkFEnv env) then
        internExprM (natLitToConstructor n)
      else pure i
    | _ => pure i)
  refine IEff.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  have hn := getNode_of_stored hn
  rw [hn]
  cases n with
  | lit l =>
    cases hd
    cases l with
    | natVal k =>
      dsimp only
      rw [natLitSupportedF_eq]
      rw [show litToCtorIfNat env (.lit (.natVal k)) =
        (if natLitSupported env then natLitToConstructor k
         else .lit (.natVal k)) from rfl]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact internExprM_eff hs _
      · rw [if_neg hg, if_neg hg]
        exact IEff.pure hs hden
    | strVal str => exact IEff.pure hs hden
  | bvar k =>
    cases hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | fvar idx nmᵢ t =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨t', ht', hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | app f' a' =>
    invert_node hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | lam nmᵢ t b m =>
    invert_node hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | forallE nmᵢ t b m =>
    invert_node hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | letE nmᵢ t v b =>
    invert_node hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)
  | proj s'ᵢ j e' =>
    invert_node hd
    exact IEff.pure hs (by simpa [litToCtorIfNat] using hden)

/-- `unfoldDefinitionI` computes (an optional index denoting) the
spec's pure `unfoldDefinition`. -/
theorem unfoldDefinitionI_eff {s₀ : IState} (hs : ISOK env s₀)
    {i : EIdx} {e : Expr} (hden : s₀.store.denote i = some e) :
    IEff env s₀ (fun s o => OptDen s.store o (unfoldDefinition env e))
      (unfoldDefinitionI (mkFEnv env) i) := by
  show IEff env s₀ _
    (Setlec.withStore (fun st => st.getNode (st.getAppFnI i)) >>= fun n =>
      match n with
      | some (.const n us) => do
        let nm ← readbackNM n
        match (mkFEnv env).find? nm with
        | some (.defnInfo cv _ _) =>
          if us.length = cv.levelParams.length then do
            let v ← constValAtM (mkFEnv env) n nm us
            let args ← Setlec.withStore (·.getAppArgsI i)
            let r ← mkAppNM v args
            pure (some r)
          else pure none
        | some (.thmInfo cv _) =>
          if us.length = cv.levelParams.length then do
            let v ← constValAtM (mkFEnv env) n nm us
            let args ← Setlec.withStore (·.getAppArgsI i)
            let r ← mkAppNM v args
            pure (some r)
          else pure none
        | _ => pure none
      | _ => pure none)
  refine IEff.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hs.wf hden)
  have hn := getNode_of_stored hn
  rw [hn]
  have hspec : unfoldDefinition env e =
      (match e.getAppFn with
      | .const n us =>
        match env.find? n with
        | some (.defnInfo cv value _) =>
          if us.length = cv.levelParams.length then
            some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
              e.getAppArgs)
          else none
        | some (.thmInfo cv value) =>
          if us.length = cv.levelParams.length then
            some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
              e.getAppArgs)
          else none
        | _ => none
      | _ => none) := rfl
  cases n with
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, hlusDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hxf⟩ := hd
    rw [hspec, ← hxf]
    dsimp only
    refine (readbackNM_eff hs hnmDen).bind ?_
    intro s₀' nmv hs hext' hnmv
    subst nmv
    replace hlusDen := denoteLList_mono hext' hlusDen
    replace hnmDen := denoteN_mono hext' hnmDen
    replace hden := denote_mono hext' hden
    rw [mkFEnv_find?]
    cases hfc : env.find? nm with
    | none => exact IEff.pure hs trivial
    | some ci =>
      cases ci with
      | defnInfo cv value hint =>
        dsimp only
        have hleneq : us.length = lus.length := denoteLList_length hlusDen
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos (by omega)]
          refine IEff.bind (constValAtM_eff hs hnmDen hlusDen
            (Or.inl hfc)) ?_
          intro s₁ v hs₁ hext₁ hQv
          refine IEff.withStore ?_
          have hargs := getAppArgsI_spec hs₁.wf (denote_mono hext₁ hden)
          refine IEff.bind (mkAppNM_eff hs₁ hQv hargs) ?_
          intro s₂ r hs₂ hext₂ hQr
          exact IEff.pure hs₂ hQr
        · rw [if_neg hlen, if_neg (by omega)]
          exact IEff.pure hs trivial
      | axiomInfo cv => exact IEff.pure hs trivial
      | thmInfo cv value =>
        dsimp only
        have hleneq : us.length = lus.length := denoteLList_length hlusDen
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos (by omega)]
          refine IEff.bind (constValAtM_eff (hint := .opaque) hs hnmDen
            hlusDen (Or.inr hfc)) ?_
          intro s₁ v hs₁ hext₁ hQv
          refine IEff.withStore ?_
          have hargs := getAppArgsI_spec hs₁.wf (denote_mono hext₁ hden)
          refine IEff.bind (mkAppNM_eff hs₁ hQv hargs) ?_
          intro s₂ r hs₂ hext₂ hQr
          exact IEff.pure hs₂ hQr
        · rw [if_neg hlen, if_neg (by omega)]
          exact IEff.pure hs trivial
      | indInfo cv caps => exact IEff.pure hs trivial
      | ctorInfo cv nP nF => exact IEff.pure hs trivial
      | recInfo cv mI rP rules => exact IEff.pure hs trivial
      | projInfo entry => exact IEff.pure hs trivial
  | bvar k =>
    have hxf := Option.some.inj hd
    rw [hspec, ← hxf]
    exact IEff.pure hs trivial
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, hluDen, hxf⟩ := hd
    rw [hspec, ← hxf]
    exact IEff.pure hs trivial
  | lit l =>
    have hxf := Option.some.inj hd
    rw [hspec, ← hxf]
    exact IEff.pure hs trivial
  | fvar idx nmᵢ t =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]
    exact IEff.pure hs trivial
  | app f' a' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [hspec, ← hd]
    exact IEff.pure hs trivial
  | lam nmᵢ t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]
    exact IEff.pure hs trivial
  | forallE nmᵢ t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]
    exact IEff.pure hs trivial
  | letE nmᵢ t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]
    exact IEff.pure hs trivial
  | proj s'ᵢ j e' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨s', hnmDen, hd⟩ := hd
    rw [hspec, ← hd]
    exact IEff.pure hs trivial

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- A twin-only effect against a pure fueled value. -/
theorem SimAt.of_eff {s₀ : IState} {β α : Type} {Q : IState → β → Prop}
    {P : IState → β → α → Prop} {c : CheckIM β}
    (h : IEff env s₀ Q c) (a : α) (hPa : ∀ s b, Q s b → P s b a) :
    SimAt env s₀ P c (pure a) := by
  intro v' s' hr
  obtain ⟨hs', hext, hQ⟩ := h v' s' hr
  exact ⟨hs', hext, a, hPa s' v' hQ, 0, rfl⟩

theorem litMajorToCtorI_sim (ih : SSimI env f) {d : Nat} {i : EIdx}
    {e : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e) (hw : WScoped d e) :
    SimAt env s₀ (RelE d)
      (litMajorToCtorI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (litMajorToCtor (fueledFns env) env d e) := by
  show SimAt env s₀ (RelE d)
    (viewI i >>= fun n =>
      match n with
      | some (.lit (.strVal s)) =>
        if strLitSupportedF (mkFEnv env) then do
          let x ← internExprM (strLitToConstructor s)
          (coreKnotI (mkFEnv env) f).whnf d x
        else pure i
      | _ => litToCtorIfNatI (mkFEnv env) i)
    (litMajorToCtor (fueledFns env) env d e)
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  have hn := getNode_of_stored hn
  rw [hn]
  cases n with
  | lit l =>
    cases hd
    cases l with
    | strVal str =>
      dsimp only
      rw [show litMajorToCtor (fueledFns env) env d (.lit (.strVal str)) =
        (if strLitSupported env then
          (fueledFns env).whnf d (strLitToConstructor str)
         else pure (.lit (.strVal str))) from rfl]
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimAt.bind_left (internExprM_eff hs (strLitToConstructor str))
          (fun s₁ x hs₁ hext₁ hQ => ?_)
        exact ih.whnf hs₁ hQ (strLitToConstructor_WScoped str d)
      · rw [if_neg hg, if_neg hg]
        exact SimAt.pure hs ⟨hden, hw⟩
    | natVal k =>
      refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _ ?_
      intro s b hQ
      exact ⟨hQ, litToCtorIfNat_WScoped hw⟩
  | bvar k =>
    cases hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | fvar idx nmᵢ t =>
    invert_node hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | app f' a' =>
    invert_node hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | lam nmᵢ t b m =>
    invert_node hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | forallE nmᵢ t b m =>
    invert_node hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | letE nmᵢ t v b =>
    invert_node hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | proj s'ᵢ j e' =>
    invert_node hd
    refine SimAt.of_eff (litToCtorIfNatI_eff hs hden) _
      (fun s b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)

theorem projLitToCtorI_sim (ih : SSimI env f) {d : Nat} {i : EIdx}
    {e : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e) (hw : WScoped d e) :
    SimAt env s₀ (RelE d)
      (projLitToCtorI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (projLitToCtor (fueledFns env) env d e) := by
  show SimAt env s₀ (RelE d)
    (viewI i >>= fun n =>
      match n with
      | some (.lit (.strVal s)) =>
        if strLitSupportedF (mkFEnv env) then do
          let x ← internExprM (strLitToConstructor s)
          (coreKnotI (mkFEnv env) f).whnf d x
        else pure i
      | _ => pure i)
    (projLitToCtor (fueledFns env) env d e)
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  have hn := getNode_of_stored hn
  rw [hn]
  cases n with
  | lit l =>
    cases hd
    cases l with
    | strVal str =>
      dsimp only
      rw [show projLitToCtor (fueledFns env) env d (.lit (.strVal str)) =
        (if strLitSupported env then
          (fueledFns env).whnf d (strLitToConstructor str)
         else pure (.lit (.strVal str))) from rfl]
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimAt.bind_left (internExprM_eff hs (strLitToConstructor str))
          (fun s₁ x hs₁ hext₁ hQ => ?_)
        exact ih.whnf hs₁ hQ (strLitToConstructor_WScoped str d)
      · rw [if_neg hg, if_neg hg]
        exact SimAt.pure hs ⟨hden, hw⟩
    | natVal k =>
      exact SimAt.pure hs ⟨hden, hw⟩
  | bvar k =>
    cases hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | fvar idx nmᵢ t =>
    invert_node hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | app f' a' =>
    invert_node hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | lam nmᵢ t b m =>
    invert_node hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | forallE nmᵢ t b m =>
    invert_node hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | letE nmᵢ t v b =>
    invert_node hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | proj s'ᵢ j e' =>
    invert_node hd
    exact SimAt.pure hs ⟨hden, hw⟩

theorem defeqSpineI_sim (ih : SSimI env f) {d : Nat} {i j : EIdx}
    {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (defeqSpineI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqSpine (fueledFns env) env d a b) := by
  show SimAt env s₀ RelV
    (Setlec.withStore (fun st => st.getNode (st.getAppFnI i)) >>= fun n =>
      match n with
      | some (.const nm us) =>
        Setlec.withStore (fun st => st.getNode (st.getAppFnI j)) >>= fun n' =>
        match n' with
        | some (.const nm' us') => do
          let aargs ← Setlec.withStore (·.getAppArgsI i)
          let bargs ← Setlec.withStore (·.getAppArgsI j)
          if nm = nm' ∧ aargs.length = bargs.length then do
            match ← isEquivListLM us us' with
            | some true =>
              defEqListI (coreKnotI (mkFEnv env) f) (mkFEnv env) d aargs bargs
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    (defeqSpine (fueledFns env) env d a b)
  refine SimAt.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hs.wf hdena)
  have hn := getNode_of_stored hn
  rw [hn]
  have hspec : defeqSpine (fueledFns env) env d a b =
      (match a.getAppFn with
      | .const nm us =>
        match b.getAppFn with
        | .const nm' us' =>
          if nm = nm' ∧ a.getAppArgs.length = b.getAppArgs.length then
            match Level.isEquivList us us' with
            | some true =>
              defEqList (fueledFns env) env d a.getAppArgs b.getAppArgs
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false) := rfl
  cases n with
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, hlusDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nmv, hnmDen, hxa⟩ := hd
    rw [hspec, ← hxa]
    dsimp only
    refine SimAt.withStore ?_
    obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv (getAppFnI_spec hs.wf hdenb)
    have hn' := getNode_of_stored hn'
    rw [hn']
    cases n' with
    | const nm' us' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨lus', hlusDen', hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨nm'v, hnmDen', hxb⟩ := hd'
      rw [← hxb]
      dsimp only
      refine SimAt.withStore ?_
      refine SimAt.withStore ?_
      have haargs := getAppArgsI_spec hs.wf hdena
      have hbargs := getAppArgsI_spec hs.wf hdenb
      have hnmiff : (nmᵢ = nm') ↔ (nmv = nm'v) :=
        denoteN_eq_iff hs.wf hnmDen hnmDen'
      by_cases hcnd : nmv = nm'v ∧
          a.getAppArgs.length = b.getAppArgs.length
      · rw [if_pos hcnd, if_pos ⟨hnmiff.mpr hcnd.1, by
          rw [haargs.length_eq, hbargs.length_eq]; exact hcnd.2⟩]
        refine SimAt.bind_left (isEquivListLM_eff hs hlusDen hlusDen') ?_
        intro s₁ ob hs₁ hext₁ hob
        subst hob
        cases hlv : Level.isEquivList lus lus' with
        | some tv =>
          cases tv with
          | true =>
            exact defEqListI_sim ih hs₁ (haargs.mono hext₁)
              (hbargs.mono hext₁) hwa.getAppArgs hwb.getAppArgs
          | false => exact SimAt.pure hs₁ rfl
        | none => exact SimAt.pure hs₁ rfl
      · rw [if_neg hcnd, if_neg (by
          rw [haargs.length_eq, hbargs.length_eq]
          intro hcc
          exact hcnd ⟨hnmiff.mp hcc.1, hcc.2⟩)]
        exact SimAt.pure hs rfl
    | bvar k => rw [← Option.some.inj hd']; exact SimAt.pure hs rfl
    | sort u' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd'
      obtain ⟨lu, hluDen, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
    | lit l' => rw [← Option.some.inj hd']; exact SimAt.pure hs rfl
    | fvar idx' nm₂ t' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨t'', _, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨nm, hnmDen, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
    | app f₂ a₂ =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨ef, _, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨ea, _, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
    | lam nm₂ t' b' m' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨et, _, hd'⟩ := hd'
      rw [Option.bind_eq_some_iff] at hd'
      obtain ⟨eb, _, hd'⟩ := hd'
      rw [Option.bind_eq_some_iff] at hd'
      obtain ⟨bm, hbmDen, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨_nmw, _hnmw, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
    | forallE nm₂ t' b' m' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨et, _, hd'⟩ := hd'
      rw [Option.bind_eq_some_iff] at hd'
      obtain ⟨eb, _, hd'⟩ := hd'
      rw [Option.bind_eq_some_iff] at hd'
      obtain ⟨bm, hbmDen, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨_nmw, _hnmw, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
    | letE nm₂ t' v' b' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨et, _, hd'⟩ := hd'
      rw [Option.bind_eq_some_iff] at hd'
      obtain ⟨ev, _, hd'⟩ := hd'
      rw [Option.bind_eq_some_iff] at hd'
      obtain ⟨eb, _, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨_nmw, _hnmw, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
    | proj s' j' e' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨ee, _, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨nm, hnmDen, hd'⟩ := hd'
      rw [← hd']; exact SimAt.pure hs rfl
  | bvar k => rw [hspec, ← Option.some.inj hd]; exact SimAt.pure hs rfl
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, hluDen, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl
  | lit l => rw [hspec, ← Option.some.inj hd]; exact SimAt.pure hs rfl
  | fvar idx nmᵢ t =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl
  | app f' a' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl
  | lam nmᵢ t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl
  | forallE nmᵢ t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl
  | letE nmᵢ t v b' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl
  | proj s'ᵢ j' e' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨s', hnmDen, hd⟩ := hd
    rw [hspec, ← hd]; exact SimAt.pure hs rfl

end Walks3

section Walks4

variable {env : Env} {f : Nat}

private theorem relO_some_lit {s : IState} {r : EIdx} {n : Nat} {d : Nat}
    (h : s.store.denote r = some (.lit (.natVal n))) :
    RelO d s (some r) (some (.lit (.natVal n))) :=
  ⟨h, by simp [WScoped]⟩

theorem reduceNatI_sim (ih : SSimI env f) {d : Nat} {i : EIdx}
    {e : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e) (hw : WScoped d e) :
    SimAt env s₀ (RelO d)
      (reduceNatI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (reduceNat (fueledFns env) env d e) := by
  show SimAt env s₀ (RelO d)
    (viewI i >>= fun n =>
      match n with
      | some (.app f₁ b) =>
        viewI f₁ >>= fun n' =>
        match n' with
        | some (.const c us) =>
          match us with
          | _ :: _ => pure none
          | [] =>
            readbackNM c >>= fun cn =>
            if cn = natSuccName ∧ natLitSupportedF (mkFEnv env) then
              (coreKnotI (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some n => do
                let r ← internExprM (.lit (.natVal (n + 1)))
                pure (some r)
              | none => pure none
            else if cn = natPredName ∧ natOpGuardF (mkFEnv env) cn = true then
              (coreKnotI (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some n =>
                match natOpResult cn n 0 with
                | some x => do
                  let r ← internExprM x
                  pure (some r)
                | none => pure none
              | none => pure none
            else if cn = natLog2Name ∧ natOpGuardF (mkFEnv env) cn = true then
              (coreKnotI (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some n =>
                match natOpResult cn n 0 with
                | some x => do
                  let r ← internExprM x
                  pure (some r)
                | none => pure none
              | none => pure none
            else if cn = natLog2Name ∧ natLitSupportedF (mkFEnv env) then
              (coreKnotI (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some _ => throw (.notImplemented
                  s!"native Nat computation on literals ({cn})")
              | none => pure none
            else pure none
        | some (.app f₂ a) =>
          viewI f₂ >>= fun n'' =>
          match n'' with
          | some (.const c us) =>
            match us with
            | _ :: _ => pure none
            | [] =>
              readbackNM c >>= fun cn =>
              if (cn = natAddName ∨ cn = natSubName ∨ cn = natMulName ∨
                  cn = natPowName ∨ cn = natBeqName ∨ cn = natBleName ∨
                  cn = natDivName ∨ cn = natModName ∨ cn = natGcdName ∨
                  cn = natLandName ∨ cn = natLorName ∨ cn = natXorName ∨
                  cn = natShiftLeftName ∨ cn = natShiftRightName) ∧
                  natOpGuardF (mkFEnv env) cn = true then
                (coreKnotI (mkFEnv env) f).whnf d a >>= fun w₁ =>
                (coreKnotI (mkFEnv env) f).whnf d b >>= fun w₂ =>
                Setlec.withStore (rawNatLitI? · w₁) >>= fun rn₁ =>
                Setlec.withStore (rawNatLitI? · w₂) >>= fun rn₂ =>
                match rn₁, rn₂ with
                | some n₁, some n₂ =>
                  match natOpResult cn n₁ n₂ with
                  | some x => do
                    let r ← internExprM x
                    pure (some r)
                  | none => pure none
                | _, _ => pure none
              else if natOpWfNames.contains cn ∧
                  natLitSupportedF (mkFEnv env) then
                (coreKnotI (mkFEnv env) f).whnf d a >>= fun w₁ =>
                (coreKnotI (mkFEnv env) f).whnf d b >>= fun w₂ =>
                Setlec.withStore (rawNatLitI? · w₁) >>= fun rn₁ =>
                Setlec.withStore (rawNatLitI? · w₂) >>= fun rn₂ =>
                match rn₁, rn₂ with
                | some _, some _ => throw (.notImplemented
                    s!"native Nat computation on literals ({cn})")
                | _, _ => pure none
              else pure none
          | _ => pure none
        | _ => pure none
      | _ => pure none)
    (reduceNat (fueledFns env) env d e)
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  have hn := getNode_of_stored hn
  rw [hn]
  cases n with
  | app f₁ b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨xf₁, hf₁, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨xb, hb, hd⟩ := hd
    subst hd
    have hwfb : WScoped d xf₁ ∧ WScoped d xb := by
      simpa only [WScoped] using hw
    refine SimAt.view ?_
    obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hf₁
    have hn' := getNode_of_stored hn'
    rw [hn']
    cases n' with
    | const cᵢ us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨lus, hlusDen, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨c, hcDen, hxf⟩ := hd'
      subst hxf
      cases us with
      | cons u us' =>
        simp only [denoteLList, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hlusDen
        obtain ⟨l0, -, ls0, -, rfl⟩ := hlusDen
        exact SimAt.pure hs trivial
      | nil =>
        cases hlusDen
        dsimp only
        refine SimAt.bind_left (readbackNM_eff hs hcDen)
          (fun s₀' cv hs hext' hcv => ?_)
        subst cv
        replace hb := denote_mono hext' hb
        rw [show reduceNat (fueledFns env) env d (.app (.const c []) xb) =
          (if c = natSuccName ∧ natLitSupported env then
            (fueledFns env).whnf d xb >>= fun w =>
            match rawNatLit? w with
            | some n => pure (some (.lit (.natVal (n + 1))))
            | none => pure none
          else if c = natPredName ∧ natOpGuard env c = true then
            (fueledFns env).whnf d xb >>= fun w =>
            match rawNatLit? w with
            | some n => pure (natOpResult c n 0)
            | none => pure none
          else if c = natLog2Name ∧ natOpGuard env c = true then
            (fueledFns env).whnf d xb >>= fun w =>
            match rawNatLit? w with
            | some n => pure (natOpResult c n 0)
            | none => pure none
          else if c = natLog2Name ∧ natLitSupported env then
            (fueledFns env).whnf d xb >>= fun w =>
            match rawNatLit? w with
            | some _ => throw (.notImplemented
                s!"native Nat computation on literals ({c})")
            | none => pure none
          else pure none) from rfl]
        rw [natLitSupportedF_eq, natOpGuardF_eq]
        by_cases hg1 : c = natSuccName ∧ natLitSupported env
        · rw [if_pos hg1, if_pos hg1]
          refine SimAt.bind (ih.whnf hs hb hwfb.2)
            (fun s₁ w wx hs₁ hext₁ hP => ?_)
          obtain ⟨hwden, hww⟩ := hP
          refine SimAt.withStore ?_
          rw [rawNatLitI?_spec hwden]
          cases rawNatLit? wx with
          | some k =>
            refine SimAt.bind_left (internExprM_eff hs₁ _)
              (fun s₂ r hs₂ hext₂ hQ => ?_)
            exact SimAt.pure hs₂ (relO_some_lit hQ)
          | none => exact SimAt.pure hs₁ trivial
        · rw [if_neg hg1, if_neg hg1]
          by_cases hg2 : c = natPredName ∧ natOpGuard env c = true
          · rw [if_pos hg2, if_pos hg2]
            refine SimAt.bind (ih.whnf hs hb hwfb.2)
              (fun s₁ w wx hs₁ hext₁ hP => ?_)
            obtain ⟨hwden, hww⟩ := hP
            refine SimAt.withStore ?_
            rw [rawNatLitI?_spec hwden]
            cases rawNatLit? wx with
            | some k =>
              dsimp only
              cases hres : natOpResult c k 0 with
              | some x =>
                dsimp only
                refine SimAt.bind_left (internExprM_eff hs₁ x)
                  (fun s₂ r hs₂ hext₂ hQ => ?_)
                refine SimAt.pure hs₂ ⟨hQ, ?_⟩
                rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                  simp [WScoped]
              | none => exact SimAt.pure hs₁ trivial
            | none => exact SimAt.pure hs₁ trivial
          · rw [if_neg hg2, if_neg hg2]
            by_cases hg3 : c = natLog2Name ∧ natOpGuard env c = true
            · rw [if_pos hg3, if_pos hg3]
              refine SimAt.bind (ih.whnf hs hb hwfb.2)
                (fun s₁ w wx hs₁ hext₁ hP => ?_)
              obtain ⟨hwden, hww⟩ := hP
              refine SimAt.withStore ?_
              rw [rawNatLitI?_spec hwden]
              cases rawNatLit? wx with
              | some k =>
                dsimp only
                cases hres : natOpResult c k 0 with
                | some x =>
                  dsimp only
                  refine SimAt.bind_left (internExprM_eff hs₁ x)
                    (fun s₂ r hs₂ hext₂ hQ => ?_)
                  refine SimAt.pure hs₂ ⟨hQ, ?_⟩
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                    simp [WScoped]
                | none => exact SimAt.pure hs₁ trivial
              | none => exact SimAt.pure hs₁ trivial
            · rw [if_neg hg3, if_neg hg3]
              by_cases hg4 : c = natLog2Name ∧ natLitSupported env
              · rw [if_pos hg4, if_pos hg4]
                refine SimAt.bind (ih.whnf hs hb hwfb.2)
                  (fun s₁ w wx hs₁ hext₁ hP => ?_)
                obtain ⟨hwden, hww⟩ := hP
                refine SimAt.withStore ?_
                rw [rawNatLitI?_spec hwden]
                cases rawNatLit? wx with
                | some k => exact SimAt.throw
                | none => exact SimAt.pure hs₁ trivial
              · rw [if_neg hg4, if_neg hg4]
                exact SimAt.pure hs trivial
    | app f₂ a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨xf₂, hf₂, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨xa, ha, hd'⟩ := hd'
      subst hd'
      have hwf₂a : WScoped d xf₂ ∧ WScoped d xa := by
        simpa only [WScoped] using hwfb.1
      refine SimAt.view ?_
      obtain ⟨n'', hn'', hc'', hd''⟩ := denote_some_inv hf₂
      have hn'' := getNode_of_stored hn''
      rw [hn'']
      cases n'' with
      | const cᵢ us =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd''
        obtain ⟨lus, hlusDen, hd''⟩ := hd''
        rw [Option.map_eq_some_iff] at hd''
        obtain ⟨c, hcDen, hxf⟩ := hd''
        subst hxf
        cases us with
        | cons u us' =>
          simp only [denoteLList, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hlusDen
          obtain ⟨l0, -, ls0, -, rfl⟩ := hlusDen
          exact SimAt.pure hs trivial
        | nil =>
          cases hlusDen
          dsimp only
          refine SimAt.bind_left (readbackNM_eff hs hcDen)
            (fun s₀' cv hs hext' hcv => ?_)
          subst cv
          replace hb := denote_mono hext' hb
          replace ha := denote_mono hext' ha
          rw [show reduceNat (fueledFns env) env d
            (.app (.app (.const c []) xa) xb) =
            (if (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
                c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
                c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
                c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
                c = natShiftLeftName ∨ c = natShiftRightName) ∧
                natOpGuard env c = true then
              (fueledFns env).whnf d xa >>= fun w₁ =>
              (fueledFns env).whnf d xb >>= fun w₂ =>
              match rawNatLit? w₁, rawNatLit? w₂ with
              | some n₁, some n₂ => pure (natOpResult c n₁ n₂)
              | _, _ => pure none
            else if natOpWfNames.contains c ∧ natLitSupported env then
              (fueledFns env).whnf d xa >>= fun w₁ =>
              (fueledFns env).whnf d xb >>= fun w₂ =>
              match rawNatLit? w₁, rawNatLit? w₂ with
              | some _, some _ => throw (.notImplemented
                  s!"native Nat computation on literals ({c})")
              | _, _ => pure none
            else pure none) from rfl]
          rw [natOpGuardF_eq, natLitSupportedF_eq]
          by_cases hg1 : (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
              c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
              c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
              c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
              c = natShiftLeftName ∨ c = natShiftRightName) ∧
              natOpGuard env c = true
          · rw [if_pos hg1, if_pos hg1]
            refine SimAt.bind (ih.whnf hs ha hwf₂a.2)
              (fun s₁ w₁ wx₁ hs₁ hext₁ hP₁ => ?_)
            obtain ⟨hw1den, hww1⟩ := hP₁
            refine SimAt.bind (ih.whnf hs₁ (denote_mono hext₁ hb) hwfb.2)
              (fun s₂ w₂ wx₂ hs₂ hext₂ hP₂ => ?_)
            obtain ⟨hw2den, hww2⟩ := hP₂
            refine SimAt.withStore ?_
            refine SimAt.withStore ?_
            rw [rawNatLitI?_spec (denote_mono hext₂ hw1den),
              rawNatLitI?_spec hw2den]
            cases rawNatLit? wx₁ with
            | some n₁ =>
              cases rawNatLit? wx₂ with
              | some n₂ =>
                dsimp only
                cases hres : natOpResult c n₁ n₂ with
                | some x =>
                  dsimp only
                  refine SimAt.bind_left (internExprM_eff hs₂ x)
                    (fun s₃ r hs₃ hext₃ hQ => ?_)
                  refine SimAt.pure hs₃ ⟨hQ, ?_⟩
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ |
                    ⟨bn, rfl⟩ <;> simp [WScoped]
                | none => exact SimAt.pure hs₂ trivial
              | none => exact SimAt.pure hs₂ trivial
            | none =>
              cases rawNatLit? wx₂ with
              | some n₂ => exact SimAt.pure hs₂ trivial
              | none => exact SimAt.pure hs₂ trivial
          · rw [if_neg hg1, if_neg hg1]
            by_cases hg2 : natOpWfNames.contains c ∧ natLitSupported env
            · rw [if_pos hg2, if_pos hg2]
              refine SimAt.bind (ih.whnf hs ha hwf₂a.2)
                (fun s₁ w₁ wx₁ hs₁ hext₁ hP₁ => ?_)
              obtain ⟨hw1den, hww1⟩ := hP₁
              refine SimAt.bind (ih.whnf hs₁ (denote_mono hext₁ hb) hwfb.2)
                (fun s₂ w₂ wx₂ hs₂ hext₂ hP₂ => ?_)
              obtain ⟨hw2den, hww2⟩ := hP₂
              refine SimAt.withStore ?_
              refine SimAt.withStore ?_
              rw [rawNatLitI?_spec (denote_mono hext₂ hw1den),
                rawNatLitI?_spec hw2den]
              cases rawNatLit? wx₁ with
              | some n₁ =>
                cases rawNatLit? wx₂ with
                | some n₂ => exact SimAt.throw
                | none => exact SimAt.pure hs₂ trivial
              | none =>
                cases rawNatLit? wx₂ with
                | some n₂ => exact SimAt.pure hs₂ trivial
                | none => exact SimAt.pure hs₂ trivial
            · rw [if_neg hg2, if_neg hg2]
              exact SimAt.pure hs trivial
      | bvar k => invert_node hd''; exact SimAt.pure hs trivial
      | sort u => invert_node hd''; exact SimAt.pure hs trivial
      | lit l => invert_node hd''; exact SimAt.pure hs trivial
      | fvar idx nmᵢ t => invert_node hd''; exact SimAt.pure hs trivial

      | app f₃ a₃ => invert_node hd''; exact SimAt.pure hs trivial
      | lam nmᵢ t b' m => invert_node hd''; exact SimAt.pure hs trivial

      | forallE nmᵢ t b' m => invert_node hd''; exact SimAt.pure hs trivial

      | letE nmᵢ t v b' => invert_node hd''; exact SimAt.pure hs trivial

      | proj s'ᵢ j e' => invert_node hd''; exact SimAt.pure hs trivial

    | bvar k => invert_node hd'; exact SimAt.pure hs trivial
    | sort u => invert_node hd'; exact SimAt.pure hs trivial
    | lit l => invert_node hd'; exact SimAt.pure hs trivial
    | fvar idx nmᵢ t => invert_node hd'; exact SimAt.pure hs trivial

    | lam nmᵢ t b' m => invert_node hd'; exact SimAt.pure hs trivial

    | forallE nmᵢ t b' m => invert_node hd'; exact SimAt.pure hs trivial

    | letE nmᵢ t v b' => invert_node hd'; exact SimAt.pure hs trivial

    | proj s'ᵢ j e' => invert_node hd'; exact SimAt.pure hs trivial

  | bvar k => invert_node hd; exact SimAt.pure hs trivial
  | sort u => invert_node hd; exact SimAt.pure hs trivial
  | const nmᵢ us => invert_node hd; exact SimAt.pure hs trivial

  | lit l => invert_node hd; exact SimAt.pure hs trivial
  | fvar idx nmᵢ t => invert_node hd; exact SimAt.pure hs trivial

  | lam nmᵢ t b' m => invert_node hd; exact SimAt.pure hs trivial

  | forallE nmᵢ t b' m => invert_node hd; exact SimAt.pure hs trivial

  | letE nmᵢ t v b' => invert_node hd; exact SimAt.pure hs trivial

  | proj s'ᵢ j e' => invert_node hd; exact SimAt.pure hs trivial

/-- `reduceNatI_sim` under the defeq-side fvar guard (the guard is the
same `Bool` on both sides after the `hasFvarI` read is peeled, so the
pruned branch is `pure none` twinned). -/
theorem reduceNatIfI_sim (ih : SSimI env f) {d : Nat} {i : EIdx}
    {e : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e) (hw : WScoped d e) (g : Bool) :
    SimAt env s₀ (RelO d)
      (if g then reduceNatI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i
        else pure none)
      (if g then reduceNat (fueledFns env) env d e else pure none) := by
  cases g
  · exact SimAt.pure hs trivial
  · exact reduceNatI_sim ih hs hden hw

end Walks4

end Setlec
