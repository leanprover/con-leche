import Setlec.Cached.CoreC
import Setlec.Verify.Cached.GuardsC
import Setlec.Verify.Cached.SimCEff
import Setlec.Verify.Disc

/-!
# Cached body walks, part 1: list helpers and small twins (task #163)

Per-helper simulation walks: each cached twin
(`Setlec/Cached/CoreC.lean`) is `SimC`-related to its `Expr` original
at the fueled record, on well-scoped inputs.  Ports of
`Setlec/Verify/DiscI1.lean`'s walks under the recipe (DESIGN.md,
task #163): `SimAt → SimC`, denotation hypotheses → `RelC`/`RelCL`,
no `Ext`, node inversion by `cases` instead of
`denoteNode` unpacking.  The pure comparand side of every statement is
byte-identical to the interned original's.
-/

namespace Setlec.Cached

open Setlec.Cached.ExprC

variable {mode : CheckMode}

/-- The cached conditional simulation at fuel `f` (the `SSimI` mirror):
every cached entry point simulates the corresponding fueled family on
well-scoped inputs.  Declared here so the per-body walks can
take it as their induction hypothesis; the knot batch proves it at
every fuel. -/
structure SSimC (mode : CheckMode) (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnfCore d i)
      ((fueledFns mode env).whnfCore d e)
  whnf : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnf d i)
      ((fueledFns mode env).whnf d e)
  infer : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).infer d i)
      ((fueledFns mode env).infer d e)
  defeq : ∀ {s₀ : CState} {d : Nat} {i j : ExprC} {a b : Expr},
    CSOK mode env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode env s₀ RelVC
      ((coreKnotI mode (mkFEnv env) f).defeq d i j)
      ((fueledFns mode env).defeq d a b)
  annotate : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).annotate d i)
      ((fueledFns mode env).annotate d e)
  /-- the io slot (task #172 B4): the memoized knot's `inferIO` entry
  simulates the fueled io-slot family -/
  inferIO : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).inferIO d i)
      ((fueledFns mode env).inferIO d e)

/-- The base case: fuel `0` throws everywhere. -/
theorem ssimC_zero (env : Env) : SSimC mode env 0 :=
  { whnfCore := fun _ _ _ => SimC.throw
    whnf := fun _ _ _ => SimC.throw
    infer := fun _ _ _ => SimC.throw
    defeq := fun _ _ _ _ _ => SimC.throw
    annotate := fun _ _ _ => SimC.throw
    inferIO := fun _ _ _ => SimC.throw }

section Walks

variable {env : Env} {f : Nat}

/-- Port of `defEqListI_sim`: the pairwise definitional-equality
helper simulates its fueled original on related, well-scoped lists. -/
theorem defEqListC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ {args : List ExprC} {xs : List Expr} {brgs : List ExprC}
      {ys : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelCL args xs → RelCL brgs ys →
      (∀ x ∈ xs, Expr.WScoped d x) → (∀ y ∈ ys, Expr.WScoped d y) →
      SimC mode env s₀ RelVC
        (defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d args brgs)
        (defEqList (fueledFns mode env) env d xs ys) := by
  intro args
  induction args with
  | nil =>
    intro xs brgs ys s₀ hs hargs hbrgs _ _
    obtain rfl := hargs.nil_inv
    match brgs, ys, hbrgs.length with
    | [], [], _ => exact SimC.pure hs rfl
    | b :: bs, y :: ys, _ => exact SimC.pure hs rfl
  | cons a as iha =>
    intro xs brgs ys s₀ hs hargs hbrgs hwx hwy
    obtain ⟨x, xs, rfl, hax, hasxs⟩ := hargs.cons_inv
    match brgs, ys, hbrgs.length with
    | [], [], _ => exact SimC.pure hs rfl
    | b :: bs, ys', hlen =>
      obtain ⟨y, ys, rfl, hby, hbsys⟩ := hbrgs.cons_inv
      show SimC mode env s₀ RelVC
        ((coreKnotI mode (mkFEnv env) f).defeq d a b >>= fun r =>
          if r then defEqListI (coreKnotI mode (mkFEnv env) f)
            (mkFEnv env) d as bs
          else pure false)
        ((fueledFns mode env).defeq d x y >>= fun r =>
          if r then defEqList (fueledFns mode env) env d xs ys
          else pure false)
      refine SimC.bind (ih.defeq hs hax hby
        (hwx x (List.mem_cons_self ..)) (hwy y (List.mem_cons_self ..)))
        (fun s₁ rb r hs₁ hP => ?_)
      obtain rfl : rb = r := hP
      cases rb with
      | true =>
        simp only [↓reduceIte]
        exact iha hs₁ hasxs hbsys
          (fun x hx => hwx x (List.mem_cons_of_mem _ hx))
          (fun y hy => hwy y (List.mem_cons_of_mem _ hy))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₁ rfl

/-- Port of `iotaCertsIAux_sim`: the bulk-accumulating iota-certificate
loop simulates its fueled original. -/
theorem iotaCertsCAux_sim (ih : SSimC mode env f) {d : Nat} {lic : Bool} :
    ∀ {args : List ExprC} {xs : List Expr} {acc : List ExprC}
      {ws : List Expr} {ty : ExprC} {tyx : Expr} {s₀ : CState},
      CSOK mode env s₀ →
      RelC ty tyx → RelCL acc ws →
      Expr.WScoped d (tyx.instantiateList ws) →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ RelVC
        (iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic ty acc
          args)
        (iotaCerts (fueledFns mode env) env d lic (tyx.instantiateList ws) xs)
  | [], xs, acc, ws, ty, tyx, s₀, hs, hty, hacc, hwty, hargs, hwargs => by
    obtain rfl := hargs.nil_inv
    rw [iotaCertsIAux.eq_def]
    dsimp only
    exact SimC.pure hs rfl
  | a :: as, xs, acc, ws, ty, tyx, s₀, hs, hty, hacc, hwty, hargs, hwargs => by
    obtain ⟨x, xs, rfl, hax, hasxs⟩ := hargs.cons_inv
    rw [iotaCertsIAux.eq_def]
    refine SimC.view ?_
    obtain rfl := hty
    cases ty with
    | forallE nm t b m =>
      rw [show (Expr.instantiateList (Expr.forallE nm t b m) ws)
          = .forallE nm ((Expr.instantiateList t ws))
              ((Expr.instantiateList b ws 1)) m by
        simp [Expr.instantiateList]] at hwty ⊢
      have hwtb : Expr.WScoped d ((Expr.instantiateList t ws))
          ∧ Expr.WScoped d ((Expr.instantiateList b ws 1)) := by
        simpa only [Expr.WScoped] using hwty
      show SimC mode env s₀ RelVC
        (if lic && m.pw.isNever then
          iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic b
            (a :: acc) as
        else
          instListM t acc >>= fun dom' =>
          (coreKnotI mode (mkFEnv env) f).inferIO d a >>= fun ta =>
          (coreKnotI mode (mkFEnv env) f).defeq d ta dom' >>= fun r =>
          if r then iotaCertsIAux (coreKnotI mode (mkFEnv env) f)
            (mkFEnv env) d lic b (a :: acc) as
          else pure false)
        (if lic && m.pw.isNever then
          iotaCerts (fueledFns mode env) env d lic
            (((Expr.instantiateList b ws 1)).instantiate1 x) xs
        else
          (fueledFns mode env).inferIO d x >>= fun ta =>
          (fueledFns mode env).defeq d ta ((Expr.instantiateList t ws)) >>=
            fun r =>
          if r then iotaCerts (fueledFns mode env) env d lic
            (((Expr.instantiateList b ws 1)).instantiate1 x) xs
          else pure false)
      have hwx : Expr.WScoped d x := hwargs x (List.mem_cons_self ..)
      -- the licensed slot: no run on either side
      have htail : SimC mode env s₀ RelVC
          (iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic b
            (a :: acc) as)
          (iotaCerts (fueledFns mode env) env d lic
            (((Expr.instantiateList b ws 1)).instantiate1 x) xs) := by
        rw [← Expr.instantiateList_cons]
        refine iotaCertsCAux_sim ih hs rfl (RelCL.cons hax hacc) ?_
          hasxs (fun x' hx' => hwargs x' (List.mem_cons_of_mem _ hx'))
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwx 0 hwtb.2
      by_cases hg : (lic && m.pw.isNever) = true
      · rw [if_pos hg, if_pos hg]
        exact htail
      rw [if_neg hg, if_neg hg]
      refine SimC.bind_left (instListM_eff (d := 0) hs rfl hacc)
        (fun s₁ dom' hs₁ hQdom => ?_)
      refine SimC.bind (ih.inferIO hs₁ hax hwx) (fun s₂ ta tax hs₂ hP => ?_)
      obtain ⟨htax, hwtax⟩ := hP
      refine SimC.bind (ih.defeq hs₂ htax hQdom hwtax hwtb.1)
        (fun s₃ rb r hs₃ hP₂ => ?_)
      obtain rfl : rb = r := hP₂
      cases rb with
      | true =>
        simp only [↓reduceIte]
        rw [← Expr.instantiateList_cons]
        refine iotaCertsCAux_sim ih hs₃ rfl (RelCL.cons hax hacc) ?_
          hasxs (fun x' hx' => hwargs x' (List.mem_cons_of_mem _ hx'))
        rw [Expr.instantiateList_cons]
        exact Expr.WScoped.instantiate1_gen hwx 0 hwtb.2
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₃ rfl
    | bvar k =>
      match acc with
      | [] =>
        obtain rfl := hacc.nil_inv
        rw [Expr.instantiateList_nil]
        exact SimC.pure hs rfl
      | a' :: acc' =>
        obtain ⟨w, ws', rfl, ha'w, hacc'⟩ := hacc.cons_inv
        show SimC mode env s₀ RelVC
          (instListM (Expr.bvar k) (a' :: acc') >>= fun ty' =>
            iotaCertsIAux (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
              d lic ty' [] (a :: as))
          (iotaCerts (fueledFns mode env) env d lic
            ((Expr.instantiateList (Expr.bvar k) (w :: ws')))
            (x :: xs))
        refine SimC.bind_left (instListM_eff (d := 0) hs rfl hacc)
          (fun s₁ ty' hs₁ hQty => ?_)
        have := iotaCertsCAux_sim ih (lic := lic) (acc := []) (ws := [])
          (args := a :: as) (xs := x :: xs) hs₁ hQty RelCL.nil
          (by rw [Expr.instantiateList_nil]; exact hwty)
          (RelCL.cons hax hasxs) hwargs
        rwa [Expr.instantiateList_nil] at this
    | sort u =>
      rw [show (Expr.instantiateList (Expr.sort u) ws)
          = .sort u by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | const nm us =>
      rw [show (Expr.instantiateList (Expr.const nm us) ws)
          = .const nm us by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | lit l =>
      rw [show (Expr.instantiateList (Expr.lit l) ws)
          = .lit l by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | fvar idx nm t =>
      rw [show (Expr.instantiateList (Expr.fvar idx nm t) ws)
          = .fvar idx nm t by simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | app f' a' =>
      rw [show (Expr.instantiateList (Expr.app f' a') ws)
          = .app ((Expr.instantiateList f' ws))
              ((Expr.instantiateList a' ws)) by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | lam nm t b m =>
      rw [show (Expr.instantiateList (Expr.lam nm t b m) ws)
          = .lam nm ((Expr.instantiateList t ws))
              ((Expr.instantiateList b ws 1)) m by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | letE nm t v b =>
      rw [show (Expr.instantiateList (Expr.letE nm t v b) ws)
          = .letE nm ((Expr.instantiateList t ws))
              ((Expr.instantiateList v ws))
              ((Expr.instantiateList b ws 1)) by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
    | proj sn j e' =>
      rw [show (Expr.instantiateList (Expr.proj sn j e') ws)
          = .proj sn j ((Expr.instantiateList e' ws)) by
        simp [Expr.instantiateList]]
      exact SimC.pure hs rfl
termination_by args _ acc => (args.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Port of `iotaCertsI_sim`. -/
theorem iotaCertsC_sim (ih : SSimC mode env f) {d : Nat} {lic : Bool} :
    ∀ {args : List ExprC} {xs : List Expr} {ty : ExprC} {tyx : Expr}
      {s₀ : CState}, CSOK mode env s₀ →
      RelC ty tyx → Expr.WScoped d tyx →
      RelCL args xs → (∀ x ∈ xs, Expr.WScoped d x) →
      SimC mode env s₀ RelVC
        (iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lic ty args)
        (iotaCerts (fueledFns mode env) env d lic tyx xs) := by
  intro args xs ty tyx s₀ hs hty hwty hargs hwargs
  have := iotaCertsCAux_sim ih (lic := lic) (acc := []) (ws := []) hs hty RelCL.nil
    (by rw [Expr.instantiateList_nil]; exact hwty) hargs hwargs
  rw [Expr.instantiateList_nil] at this
  exact this

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- Port of `ensureSortI_sim`. -/
theorem ensureSortC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ RelVC (ensureSortI (coreKnotI mode (mkFEnv env) f) d i)
      (ensureSort (fueledFns mode env) env d e) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).whnf d i >>= fun w =>
      viewI w >>= fun n =>
      match n with
      | some (.sort u) => pure u
      | _ => throw (.invalid "expected a sort"))
    ((fueledFns mode env).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
  refine SimC.bind (ih.whnf hs hden hw) (fun s₁ w wx hs₁ hP => ?_)
  obtain ⟨hwden, hww⟩ := hP
  refine SimC.view ?_
  obtain rfl := hwden
  cases w with
  | sort u => exact SimC.pure hs₁ rfl
  | bvar k => exact SimC.throw
  | const nm us => exact SimC.throw
  | lit l => exact SimC.throw
  | fvar idx nm t => exact SimC.throw
  | app f' a' => exact SimC.throw
  | lam nm t b m => exact SimC.throw
  | forallE nm t b m => exact SimC.throw
  | letE nm t v b => exact SimC.throw
  | proj sn j e' => exact SimC.throw

/-- Port of `litToCtorIfNatI_eff`: the cached twin computes the spec's
`litToCtorIfNat`. -/
theorem litToCtorIfNatC_eff {s₀ : CState} (hs : CSOK mode env s₀)
    {i : ExprC} {e : Expr} (hden : RelC i e) :
    CEff mode env s₀ (fun r => RelC r (litToCtorIfNat env e))
      (litToCtorIfNatI (mkFEnv env) i) := by
  show CEff mode env s₀ _ (viewI i >>= fun n =>
    match n with
    | some (.lit (.natVal n)) =>
      if natLitSupportedF (mkFEnv env) then
        internExprM (natLitToConstructor n)
      else pure i
    | _ => pure i)
  refine CEff.view ?_
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | lit l =>
    cases l with
    | natVal k =>
      dsimp only [ExprC.view]
      rw [natLitSupportedF_eq]
      rw [show litToCtorIfNat env ((Expr.lit (.natVal k))) =
        (if natLitSupported env then natLitToConstructor k
         else .lit (.natVal k)) from rfl]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact internExprM_eff hs _
      · rw [if_neg hg, if_neg hg]
        exact CEff.pure hs hden
    | strVal str => exact CEff.pure hs hden
  | bvar k =>
    exact CEff.pure hs hden
  | sort u =>
    exact CEff.pure hs hden
  | const nm us =>
    exact CEff.pure hs hden
  | fvar idx nm t =>
    exact CEff.pure hs hden
  | app f' a' =>
    exact CEff.pure hs hden
  | lam nm t b m =>
    exact CEff.pure hs hden
  | forallE nm t b m =>
    exact CEff.pure hs hden
  | letE nm t v b =>
    exact CEff.pure hs hden
  | proj sn j e' =>
    exact CEff.pure hs hden

/-- Port of `unfoldDefinitionI_eff`: the cached twin computes the
spec's pure `unfoldDefinition`. -/
theorem unfoldDefinitionC_eff {s₀ : CState} (hs : CSOK mode env s₀)
    {i : ExprC} {e : Expr} (hden : RelC i e) :
    CEff mode env s₀ (fun o => OptEr o (unfoldDefinition env e))
      (unfoldDefinitionI (mkFEnv env) i) := by
  show CEff mode env s₀ _
    (Setlec.Cached.withStore (fun st => st.getNode (st.getAppFnI i)) >>= fun n =>
      match n with
      | some (.const n us) => do
        let nm ← readbackNM n
        match (mkFEnv env).find? nm with
        | some (.defnInfo cv _ _) =>
          if us.length = cv.levelParams.length then do
            let v ← constValAtM (mkFEnv env) n nm us
            let args ← Setlec.Cached.withStore (·.getAppArgsI i)
            let r ← mkAppNM v args
            pure (some r)
          else pure none
        | some (.thmInfo cv _) =>
          if us.length = cv.levelParams.length then do
            let v ← constValAtM (mkFEnv env) n nm us
            let args ← Setlec.Cached.withStore (·.getAppArgsI i)
            let r ← mkAppNM v args
            pure (some r)
          else pure none
        | _ => pure none
      | _ => pure none)
  refine CEff.withStore ?_
  obtain rfl := hden
  have hspec : unfoldDefinition env i =
      (match (Expr.getAppFn i) with
      | .const n us =>
        match env.find? n with
        | some (.defnInfo cv value _) =>
          if us.length = cv.levelParams.length then
            some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
              (Expr.getAppArgs i))
          else none
        | some (.thmInfo cv value) =>
          if us.length = cv.levelParams.length then
            some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
              (Expr.getAppArgs i))
          else none
        | _ => none
      | _ => none) := rfl
  have hfn := ExprC.getAppFn_spec i
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hg : ExprC.getAppFn i = g at hfn ⊢
  cases g with
  | const nm us =>
    have hfn' : (Expr.getAppFn i) = Expr.const nm us := hfn.symm
    rw [hspec, hfn']
    dsimp only
    refine (readbackNM_eff hs nm).bind ?_
    intro s₀' nmv hs hnmv
    subst hnmv
    rw [mkFEnv_find?]
    cases hfc : env.find? nmv with
    | none => exact CEff.pure hs trivial
    | some ci =>
      cases ci with
      | defnInfo cv value hint =>
        dsimp only
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine CEff.bind (constValAtM_eff hs (Or.inl hfc)) ?_
          intro s₁ v hs₁ hQv
          refine CEff.withStore ?_
          dsimp only [CStore.getAppArgsI]
          refine CEff.bind (mkAppNM_eff hs₁ hQv (ExprC.getAppArgs_spec _)) ?_
          intro s₂ r hs₂ hQr
          exact CEff.pure hs₂ hQr
        · rw [if_neg hlen, if_neg hlen]
          exact CEff.pure hs trivial
      | axiomInfo cv => exact CEff.pure hs trivial
      | thmInfo cv value =>
        dsimp only
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine CEff.bind (constValAtM_eff (hint := .opaque) hs
            (Or.inr hfc)) ?_
          intro s₁ v hs₁ hQv
          refine CEff.withStore ?_
          dsimp only [CStore.getAppArgsI]
          refine CEff.bind (mkAppNM_eff hs₁ hQv (ExprC.getAppArgs_spec _)) ?_
          intro s₂ r hs₂ hQr
          exact CEff.pure hs₂ hQr
        · rw [if_neg hlen, if_neg hlen]
          exact CEff.pure hs trivial
      | indInfo cv caps => exact CEff.pure hs trivial
      | ctorInfo cv nP nF => exact CEff.pure hs trivial
      | recInfo cv mI rP rules => exact CEff.pure hs trivial
      | projInfo entry => exact CEff.pure hs trivial
  | bvar k =>
    have hfn' : (Expr.getAppFn i) = Expr.bvar k := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | sort u =>
    have hfn' : (Expr.getAppFn i) = Expr.sort u := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | lit l =>
    have hfn' : (Expr.getAppFn i) = Expr.lit l := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | fvar idx nm t =>
    have hfn' : (Expr.getAppFn i) = Expr.fvar idx nm t := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | app f' a' =>
    have hfn' : (Expr.getAppFn i) = Expr.app f' a' :=
      hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | lam nm t b m =>
    have hfn' : (Expr.getAppFn i) = Expr.lam nm t b m :=
      hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | forallE nm t b m =>
    have hfn' : (Expr.getAppFn i)
        = Expr.forallE nm t b m := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | letE nm t v b =>
    have hfn' : (Expr.getAppFn i)
        = Expr.letE nm t v b := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial
  | proj sn j e' =>
    have hfn' : (Expr.getAppFn i) = Expr.proj sn j e' := hfn.symm
    rw [hspec, hfn']
    exact CEff.pure hs trivial

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- A twin-only effect against a pure fueled value. -/
theorem SimC.of_eff {s₀ : CState} {β α : Type} {Q : β → Prop}
    {P : β → α → Prop} {c : CheckCM β}
    (h : CEff mode env s₀ Q c) (a : α) (hPa : ∀ b, Q b → P b a) :
    SimC mode env s₀ P c (pure a) := by
  intro v' s' hr
  obtain ⟨hs', hQ⟩ := h v' s' hr
  exact ⟨hs', a, hPa v' hQ, 0, rfl⟩

/-- Port of `litMajorToCtorI_sim`. -/
theorem litMajorToCtorC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d)
      (litMajorToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (litMajorToCtor (fueledFns mode env) env d e) := by
  show SimC mode env s₀ (RelEC d)
    (viewI i >>= fun n =>
      match n with
      | some (.lit (.strVal s)) =>
        if strLitSupportedF (mkFEnv env) then do
          let x ← internExprM (strLitToConstructor s)
          (coreKnotI mode (mkFEnv env) f).whnf d x
        else pure i
      | _ => litToCtorIfNatI (mkFEnv env) i)
    (litMajorToCtor (fueledFns mode env) env d e)
  refine SimC.view ?_
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | lit l =>
    cases l with
    | strVal str =>
      dsimp only [ExprC.view]
      rw [show litMajorToCtor (fueledFns mode env) env d
          ((Expr.lit (.strVal str))) =
        (if strLitSupported env then
          (fueledFns mode env).whnf d (strLitToConstructor str)
         else pure (.lit (.strVal str))) from rfl]
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (internExprM_eff hs (strLitToConstructor str))
          (fun s₁ x hs₁ hQ => ?_)
        exact ih.whnf hs₁ hQ (strLitToConstructor_WScoped str d)
      · rw [if_neg hg, if_neg hg]
        exact SimC.pure hs ⟨hden, hw⟩
    | natVal k =>
      refine SimC.of_eff (litToCtorIfNatC_eff hs hden) _ ?_
      intro b hQ
      exact ⟨hQ, litToCtorIfNat_WScoped hw⟩
  | bvar k =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | sort u =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | const nm us =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | fvar idx nm t =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | app f' a' =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | lam nm t b m =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | forallE nm t b m =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | letE nm t v b =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)
  | proj sn jj e' =>
    exact SimC.of_eff (litToCtorIfNatC_eff hs hden) _
      (fun b hQ => ⟨hQ, litToCtorIfNat_WScoped hw⟩)

/-- Port of `projLitToCtorI_sim`. -/
theorem projLitToCtorC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d)
      (projLitToCtorI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (projLitToCtor (fueledFns mode env) env d e) := by
  show SimC mode env s₀ (RelEC d)
    (viewI i >>= fun n =>
      match n with
      | some (.lit (.strVal s)) =>
        if strLitSupportedF (mkFEnv env) then do
          let x ← internExprM (strLitToConstructor s)
          (coreKnotI mode (mkFEnv env) f).whnf d x
        else pure i
      | _ => pure i)
    (projLitToCtor (fueledFns mode env) env d e)
  refine SimC.view ?_
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | lit l =>
    cases l with
    | strVal str =>
      dsimp only [ExprC.view]
      rw [show projLitToCtor (fueledFns mode env) env d
          ((Expr.lit (.strVal str))) =
        (if strLitSupported env then
          (fueledFns mode env).whnf d (strLitToConstructor str)
         else pure (.lit (.strVal str))) from rfl]
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        refine SimC.bind_left (internExprM_eff hs (strLitToConstructor str))
          (fun s₁ x hs₁ hQ => ?_)
        exact ih.whnf hs₁ hQ (strLitToConstructor_WScoped str d)
      · rw [if_neg hg, if_neg hg]
        exact SimC.pure hs ⟨hden, hw⟩
    | natVal k => exact SimC.pure hs ⟨hden, hw⟩
  | bvar k => exact SimC.pure hs ⟨hden, hw⟩
  | sort u => exact SimC.pure hs ⟨hden, hw⟩
  | const nm us => exact SimC.pure hs ⟨hden, hw⟩
  | fvar idx nm t => exact SimC.pure hs ⟨hden, hw⟩
  | app f' a' => exact SimC.pure hs ⟨hden, hw⟩
  | lam nm t b m => exact SimC.pure hs ⟨hden, hw⟩
  | forallE nm t b m => exact SimC.pure hs ⟨hden, hw⟩
  | letE nm t v b => exact SimC.pure hs ⟨hden, hw⟩
  | proj sn jj e' => exact SimC.pure hs ⟨hden, hw⟩

/-- Port of `defeqSpineI_sim`. -/
theorem defeqSpineC_sim (ih : SSimC mode env f) {d : Nat} {i j : ExprC}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqSpine (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (Setlec.Cached.withStore (fun st => st.getNode (st.getAppFnI i)) >>=
      fun n =>
      match n with
      | some (.const nm us) =>
        Setlec.Cached.withStore (fun st => st.getNode (st.getAppFnI j)) >>=
          fun n' =>
        match n' with
        | some (.const nm' us') => do
          let aargs ← Setlec.Cached.withStore (·.getAppArgsI i)
          let bargs ← Setlec.Cached.withStore (·.getAppArgsI j)
          if nm = nm' ∧ aargs.length = bargs.length then do
            match ← isEquivListLM us us' with
            | some true =>
              defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
                aargs bargs
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    (defeqSpine (fueledFns mode env) env d a b)
  refine SimC.withStore ?_
  obtain rfl := hdena
  obtain rfl := hdenb
  have hspec : defeqSpine (fueledFns mode env) env d i j =
      (match (Expr.getAppFn i) with
      | .const nm us =>
        match (Expr.getAppFn j) with
        | .const nm' us' =>
          if nm = nm' ∧
              (Expr.getAppArgs i).length = (Expr.getAppArgs j).length then
            match Level.isEquivList us us' with
            | some true =>
              defEqList (fueledFns mode env) env d
                (Expr.getAppArgs i) (Expr.getAppArgs j)
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false) := rfl
  have haargs := ExprC.getAppArgs_spec i
  have hbargs := ExprC.getAppArgs_spec j
  have hlena : (ExprC.getAppArgs i).length = (Expr.getAppArgs i).length :=
    RelCL.length haargs
  have hlenb : (ExprC.getAppArgs j).length = (Expr.getAppArgs j).length :=
    RelCL.length hbargs
  have hfa := ExprC.getAppFn_spec i
  have hfb := ExprC.getAppFn_spec j
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hga : ExprC.getAppFn i = ga at hfa ⊢
  cases ga with
  | const nm us =>
    have hfa' : (Expr.getAppFn i) = Expr.const nm us := hfa.symm
    rw [hspec, hfa']
    dsimp only
    refine SimC.withStore ?_
    generalize hgb : ExprC.getAppFn j = gb at hfb ⊢
    cases gb with
    | const nm' us' =>
      have hfb' : (Expr.getAppFn j) = Expr.const nm' us' := hfb.symm
      rw [hfb']
      dsimp only
      refine SimC.withStore ?_
      refine SimC.withStore ?_
      simp only [CStore.getAppArgsI, hlena, hlenb]
      by_cases hcnd : nm = nm' ∧
          (Expr.getAppArgs i).length = (Expr.getAppArgs j).length
      · rw [if_pos hcnd, if_pos hcnd]
        refine SimC.bind_left (isEquivListLM_eff hs) ?_
        intro s₁ ob hs₁ hob
        subst hob
        cases hlv : Level.isEquivList us us' with
        | some tv =>
          cases tv with
          | true =>
            exact defEqListC_sim ih hs₁ haargs hbargs
              hwa.getAppArgs hwb.getAppArgs
          | false => exact SimC.pure hs₁ rfl
        | none => exact SimC.pure hs₁ rfl
      · rw [if_neg hcnd, if_neg hcnd]
        exact SimC.pure hs rfl
    | bvar k =>
      rw [show (Expr.getAppFn j) = Expr.bvar k from hfb.symm]
      exact SimC.pure hs rfl
    | sort u' =>
      rw [show (Expr.getAppFn j) = Expr.sort u' from hfb.symm]
      exact SimC.pure hs rfl
    | lit l' =>
      rw [show (Expr.getAppFn j) = Expr.lit l' from hfb.symm]
      exact SimC.pure hs rfl
    | fvar idx' nm₂ t' =>
      rw [show (Expr.getAppFn j) = Expr.fvar idx' nm₂ t'
        from hfb.symm]
      exact SimC.pure hs rfl
    | app f₂ a₂ =>
      rw [show (Expr.getAppFn j) = Expr.app (f₂) (a₂)
        from hfb.symm]
      exact SimC.pure hs rfl
    | lam nm₂ t' b' m' =>
      rw [show (Expr.getAppFn j)
        = Expr.lam nm₂ t' b' m' from hfb.symm]
      exact SimC.pure hs rfl
    | forallE nm₂ t' b' m' =>
      rw [show (Expr.getAppFn j)
        = Expr.forallE nm₂ t' b' m' from hfb.symm]
      exact SimC.pure hs rfl
    | letE nm₂ t' v' b' =>
      rw [show (Expr.getAppFn j)
        = Expr.letE nm₂ t' v' b' from hfb.symm]
      exact SimC.pure hs rfl
    | proj sn' j' e' =>
      rw [show (Expr.getAppFn j) = Expr.proj sn' j' e'
        from hfb.symm]
      exact SimC.pure hs rfl
  | bvar k =>
    rw [hspec, show (Expr.getAppFn i) = Expr.bvar k from hfa.symm]
    exact SimC.pure hs rfl
  | sort u =>
    rw [hspec, show (Expr.getAppFn i) = Expr.sort u from hfa.symm]
    exact SimC.pure hs rfl
  | lit l =>
    rw [hspec, show (Expr.getAppFn i) = Expr.lit l from hfa.symm]
    exact SimC.pure hs rfl
  | fvar idx nm t =>
    rw [hspec, show (Expr.getAppFn i) = Expr.fvar idx nm t
      from hfa.symm]
    exact SimC.pure hs rfl
  | app f' a' =>
    rw [hspec, show (Expr.getAppFn i) = Expr.app f' a'
      from hfa.symm]
    exact SimC.pure hs rfl
  | lam nm t b' m =>
    rw [hspec, show (Expr.getAppFn i)
      = Expr.lam nm t b' m from hfa.symm]
    exact SimC.pure hs rfl
  | forallE nm t b' m =>
    rw [hspec, show (Expr.getAppFn i)
      = Expr.forallE nm t b' m from hfa.symm]
    exact SimC.pure hs rfl
  | letE nm t v b' =>
    rw [hspec, show (Expr.getAppFn i)
      = Expr.letE nm t v b' from hfa.symm]
    exact SimC.pure hs rfl
  | proj sn j' e' =>
    rw [hspec, show (Expr.getAppFn i) = Expr.proj sn j' e'
      from hfa.symm]
    exact SimC.pure hs rfl

end Walks3

section Walks4

variable {env : Env} {f : Nat}

private theorem relOC_some_lit {r : ExprC} {n : Nat} {d : Nat}
    (h : RelC r (.lit (.natVal n))) :
    RelOC d (some r) (some (.lit (.natVal n))) :=
  ⟨h, by simp [Expr.WScoped]⟩

/-- Port of `reduceNatI_sim`. -/
theorem reduceNatC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelOC d)
      (reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (reduceNat (fueledFns mode env) env d e) := by
  show SimC mode env s₀ (RelOC d)
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
              (coreKnotI mode (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.Cached.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some n => do
                let r ← internExprM (.lit (.natVal (n + 1)))
                pure (some r)
              | none => pure none
            else if cn = natPredName ∧ natOpStoredF (mkFEnv env) cn = true then
              (coreKnotI mode (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.Cached.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some n =>
                match natOpResult cn n 0 with
                | some x => do
                  let r ← internExprM x
                  pure (some r)
                | none => pure none
              | none => pure none
            else if cn = natLog2Name ∧ natOpStoredF (mkFEnv env) cn = true then
              (coreKnotI mode (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.Cached.withStore (rawNatLitI? · w) >>= fun rn =>
              match rn with
              | some n =>
                match natOpResult cn n 0 with
                | some x => do
                  let r ← internExprM x
                  pure (some r)
                | none => pure none
              | none => pure none
            else if cn = natLog2Name ∧ natLitSupportedF (mkFEnv env) then
              (coreKnotI mode (mkFEnv env) f).whnf d b >>= fun w =>
              Setlec.Cached.withStore (rawNatLitI? · w) >>= fun rn =>
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
                  natOpStoredF (mkFEnv env) cn = true then
                (coreKnotI mode (mkFEnv env) f).whnf d a >>= fun w₁ =>
                Setlec.Cached.withStore (rawNatLitI? · w₁) >>= fun rn₁ =>
                match rn₁ with
                | some n₁ =>
                  (coreKnotI mode (mkFEnv env) f).whnf d b >>= fun w₂ =>
                  Setlec.Cached.withStore (rawNatLitI? · w₂) >>= fun rn₂ =>
                  match rn₂ with
                  | some n₂ =>
                    match natOpResult cn n₁ n₂ with
                    | some x => do
                      let r ← internExprM x
                      pure (some r)
                    | none => pure none
                  | none => pure none
                | none => pure none
              else if natOpWfNames.contains cn ∧
                  natLitSupportedF (mkFEnv env) then
                (coreKnotI mode (mkFEnv env) f).whnf d a >>= fun w₁ =>
                Setlec.Cached.withStore (rawNatLitI? · w₁) >>= fun rn₁ =>
                match rn₁ with
                | some _ =>
                  (coreKnotI mode (mkFEnv env) f).whnf d b >>= fun w₂ =>
                  Setlec.Cached.withStore (rawNatLitI? · w₂) >>= fun rn₂ =>
                  match rn₂ with
                  | some _ => throw (.notImplemented
                      s!"native Nat computation on literals ({cn})")
                  | none => pure none
                | none => pure none
              else pure none
          | _ => pure none
        | _ => pure none
      | _ => pure none)
    (reduceNat (fueledFns mode env) env d e)
  refine SimC.view ?_
  obtain rfl := hden
  cases i with
  | app f₁ b =>
    rw [show (Expr.app f₁ b)
        = Expr.app (f₁) b from rfl] at hw ⊢
    have hwfb : Expr.WScoped d (f₁) ∧ Expr.WScoped d b := by
      simpa only [Expr.WScoped] using hw
    refine SimC.view ?_
    cases f₁ with
    | const c us =>
      rw [show (Expr.const c us)
          = Expr.const c us from rfl]
      cases us with
      | cons u us' => exact SimC.pure hs trivial
      | nil =>
        refine SimC.bind_left (readbackNM_eff hs c)
          (fun s₀' cv hs hcv => ?_)
        subst hcv
        rw [show reduceNat (fueledFns mode env) env d
          (.app (.const cv []) b) =
          (if cv = natSuccName ∧ natLitSupported env then
            (fueledFns mode env).whnf d b >>= fun w =>
            match rawNatLit? w with
            | some n => pure (some (.lit (.natVal (n + 1))))
            | none => pure none
          else if cv = natPredName ∧ natOpStored env cv = true then
            (fueledFns mode env).whnf d b >>= fun w =>
            match rawNatLit? w with
            | some n => pure (natOpResult cv n 0)
            | none => pure none
          else if cv = natLog2Name ∧ natOpStored env cv = true then
            (fueledFns mode env).whnf d b >>= fun w =>
            match rawNatLit? w with
            | some n => pure (natOpResult cv n 0)
            | none => pure none
          else if cv = natLog2Name ∧ natLitSupported env then
            (fueledFns mode env).whnf d b >>= fun w =>
            match rawNatLit? w with
            | some _ => throw (.notImplemented
                s!"native Nat computation on literals ({cv})")
            | none => pure none
          else pure none) from rfl]
        rw [natLitSupportedF_eq, natOpStoredF_eq]
        by_cases hg1 : cv = natSuccName ∧ natLitSupported env
        · rw [if_pos hg1, if_pos hg1]
          refine SimC.bind (ih.whnf hs rfl hwfb.2)
            (fun s₁ w wx hs₁ hP => ?_)
          obtain ⟨hwden, hww⟩ := hP
          refine SimC.withStore ?_
          rw [rawNatLitI?_spec hwden]
          cases rawNatLit? wx with
          | some k =>
            refine SimC.bind_left (internExprM_eff hs₁ _)
              (fun s₂ r hs₂ hQ => ?_)
            exact SimC.pure hs₂ (relOC_some_lit hQ)
          | none => exact SimC.pure hs₁ trivial
        · rw [if_neg hg1, if_neg hg1]
          by_cases hg2 : cv = natPredName ∧ natOpStored env cv = true
          · rw [if_pos hg2, if_pos hg2]
            refine SimC.bind (ih.whnf hs rfl hwfb.2)
              (fun s₁ w wx hs₁ hP => ?_)
            obtain ⟨hwden, hww⟩ := hP
            refine SimC.withStore ?_
            rw [rawNatLitI?_spec hwden]
            cases rawNatLit? wx with
            | some k =>
              dsimp only
              cases hres : natOpResult cv k 0 with
              | some x =>
                dsimp only
                refine SimC.bind_left (internExprM_eff hs₁ x)
                  (fun s₂ r hs₂ hQ => ?_)
                refine SimC.pure hs₂ ⟨hQ, ?_⟩
                rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                  simp [Expr.WScoped]
              | none => exact SimC.pure hs₁ trivial
            | none => exact SimC.pure hs₁ trivial
          · rw [if_neg hg2, if_neg hg2]
            by_cases hg3 : cv = natLog2Name ∧ natOpStored env cv = true
            · rw [if_pos hg3, if_pos hg3]
              refine SimC.bind (ih.whnf hs rfl hwfb.2)
                (fun s₁ w wx hs₁ hP => ?_)
              obtain ⟨hwden, hww⟩ := hP
              refine SimC.withStore ?_
              rw [rawNatLitI?_spec hwden]
              cases rawNatLit? wx with
              | some k =>
                dsimp only
                cases hres : natOpResult cv k 0 with
                | some x =>
                  dsimp only
                  refine SimC.bind_left (internExprM_eff hs₁ x)
                    (fun s₂ r hs₂ hQ => ?_)
                  refine SimC.pure hs₂ ⟨hQ, ?_⟩
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                    simp [Expr.WScoped]
                | none => exact SimC.pure hs₁ trivial
              | none => exact SimC.pure hs₁ trivial
            · rw [if_neg hg3, if_neg hg3]
              by_cases hg4 : cv = natLog2Name ∧ natLitSupported env
              · rw [if_pos hg4, if_pos hg4]
                refine SimC.bind (ih.whnf hs rfl hwfb.2)
                  (fun s₁ w wx hs₁ hP => ?_)
                obtain ⟨hwden, hww⟩ := hP
                refine SimC.withStore ?_
                rw [rawNatLitI?_spec hwden]
                cases rawNatLit? wx with
                | some k => exact SimC.throw
                | none => exact SimC.pure hs₁ trivial
              · rw [if_neg hg4, if_neg hg4]
                exact SimC.pure hs trivial
    | app f₂ a =>
      rw [show (Expr.app f₂ a)
          = Expr.app (f₂) a from rfl] at hwfb ⊢
      have hwf₂a : Expr.WScoped d (f₂) ∧ Expr.WScoped d a := by
        simpa only [Expr.WScoped] using hwfb.1
      refine SimC.view ?_
      cases f₂ with
      | const c us =>
        rw [show (Expr.const c us)
            = Expr.const c us from rfl]
        cases us with
        | cons u us' => exact SimC.pure hs trivial
        | nil =>
          refine SimC.bind_left (readbackNM_eff hs c)
            (fun s₀' cv hs hcv => ?_)
          subst hcv
          rw [show reduceNat (fueledFns mode env) env d
            (.app (.app (.const cv []) a) b) =
            (if (cv = natAddName ∨ cv = natSubName ∨ cv = natMulName ∨
                cv = natPowName ∨ cv = natBeqName ∨ cv = natBleName ∨
                cv = natDivName ∨ cv = natModName ∨ cv = natGcdName ∨
                cv = natLandName ∨ cv = natLorName ∨ cv = natXorName ∨
                cv = natShiftLeftName ∨ cv = natShiftRightName) ∧
                natOpStored env cv = true then
              (fueledFns mode env).whnf d a >>= fun w₁ =>
              match rawNatLit? w₁ with
              | some n₁ =>
                (fueledFns mode env).whnf d b >>= fun w₂ =>
                match rawNatLit? w₂ with
                | some n₂ => pure (natOpResult cv n₁ n₂)
                | none => pure none
              | none => pure none
            else if natOpWfNames.contains cv ∧ natLitSupported env then
              (fueledFns mode env).whnf d a >>= fun w₁ =>
              match rawNatLit? w₁ with
              | some _ =>
                (fueledFns mode env).whnf d b >>= fun w₂ =>
                match rawNatLit? w₂ with
                | some _ => throw (.notImplemented
                    s!"native Nat computation on literals ({cv})")
                | none => pure none
              | none => pure none
            else pure none) from rfl]
          rw [natOpStoredF_eq, natLitSupportedF_eq]
          by_cases hg1 : (cv = natAddName ∨ cv = natSubName ∨
              cv = natMulName ∨ cv = natPowName ∨ cv = natBeqName ∨
              cv = natBleName ∨ cv = natDivName ∨ cv = natModName ∨
              cv = natGcdName ∨ cv = natLandName ∨ cv = natLorName ∨
              cv = natXorName ∨ cv = natShiftLeftName ∨
              cv = natShiftRightName) ∧ natOpStored env cv = true
          · rw [if_pos hg1, if_pos hg1]
            -- first argument first; the second only behind a literal (D15)
            refine SimC.bind (ih.whnf hs rfl hwf₂a.2)
              (fun s₁ w₁ wx₁ hs₁ hP₁ => ?_)
            obtain ⟨hw1den, hww1⟩ := hP₁
            refine SimC.withStore ?_
            rw [rawNatLitI?_spec hw1den]
            cases rawNatLit? wx₁ with
            | some n₁ =>
              refine SimC.bind (ih.whnf hs₁ rfl hwfb.2)
                (fun s₂ w₂ wx₂ hs₂ hP₂ => ?_)
              obtain ⟨hw2den, hww2⟩ := hP₂
              refine SimC.withStore ?_
              rw [rawNatLitI?_spec hw2den]
              cases rawNatLit? wx₂ with
              | some n₂ =>
                dsimp only
                cases hres : natOpResult cv n₁ n₂ with
                | some x =>
                  dsimp only
                  refine SimC.bind_left (internExprM_eff hs₂ x)
                    (fun s₃ r hs₃ hQ => ?_)
                  refine SimC.pure hs₃ ⟨hQ, ?_⟩
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ |
                    ⟨bn, rfl⟩ <;> simp [Expr.WScoped]
                | none => exact SimC.pure hs₂ trivial
              | none => exact SimC.pure hs₂ trivial
            | none => exact SimC.pure hs₁ trivial
          · rw [if_neg hg1, if_neg hg1]
            by_cases hg2 : natOpWfNames.contains cv ∧ natLitSupported env
            · rw [if_pos hg2, if_pos hg2]
              refine SimC.bind (ih.whnf hs rfl hwf₂a.2)
                (fun s₁ w₁ wx₁ hs₁ hP₁ => ?_)
              obtain ⟨hw1den, hww1⟩ := hP₁
              refine SimC.withStore ?_
              rw [rawNatLitI?_spec hw1den]
              cases rawNatLit? wx₁ with
              | some n₁ =>
                refine SimC.bind (ih.whnf hs₁ rfl hwfb.2)
                  (fun s₂ w₂ wx₂ hs₂ hP₂ => ?_)
                obtain ⟨hw2den, hww2⟩ := hP₂
                refine SimC.withStore ?_
                rw [rawNatLitI?_spec hw2den]
                cases rawNatLit? wx₂ with
                | some n₂ => exact SimC.throw
                | none => exact SimC.pure hs₂ trivial
              | none => exact SimC.pure hs₁ trivial
            · rw [if_neg hg2, if_neg hg2]
              exact SimC.pure hs trivial
      | bvar k => exact SimC.pure hs trivial
      | sort u => exact SimC.pure hs trivial
      | lit l => exact SimC.pure hs trivial
      | fvar idx nm t => exact SimC.pure hs trivial
      | app f₃ a₃ => exact SimC.pure hs trivial
      | lam nm t b' m => exact SimC.pure hs trivial
      | forallE nm t b' m => exact SimC.pure hs trivial
      | letE nm t v b' => exact SimC.pure hs trivial
      | proj sn jj e' => exact SimC.pure hs trivial
    | bvar k => exact SimC.pure hs trivial
    | sort u => exact SimC.pure hs trivial
    | lit l => exact SimC.pure hs trivial
    | fvar idx nm t => exact SimC.pure hs trivial
    | lam nm t b' m => exact SimC.pure hs trivial
    | forallE nm t b' m => exact SimC.pure hs trivial
    | letE nm t v b' => exact SimC.pure hs trivial
    | proj sn jj e' => exact SimC.pure hs trivial
  | bvar k => exact SimC.pure hs trivial
  | sort u => exact SimC.pure hs trivial
  | const nm us => exact SimC.pure hs trivial
  | lit l => exact SimC.pure hs trivial
  | fvar idx nm t => exact SimC.pure hs trivial
  | lam nm t b' m => exact SimC.pure hs trivial
  | forallE nm t b' m => exact SimC.pure hs trivial
  | letE nm t v b' => exact SimC.pure hs trivial
  | proj sn jj e' => exact SimC.pure hs trivial

/-- `reduceNatC_sim` under the defeq-side fvar guard (the guard is the
same `Bool` on both sides after the `hasFvarI` read is peeled, so the
pruned branch is `pure none` twinned). -/
theorem reduceNatIfC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) (g : Bool) :
    SimC mode env s₀ (RelOC d)
      (if g then reduceNatI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
        else pure none)
      (if g then reduceNat (fueledFns mode env) env d e else pure none) := by
  cases g
  · exact SimC.pure hs trivial
  · exact reduceNatC_sim ih hs hden hw

end Walks4

end Setlec.Cached
