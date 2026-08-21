import Setlec.Verify.BridgeDecl

/-!
# `wfOpsM` runs to pure runs, per declaration-checker function

With the memo operations unguarded, part B's entry-point bridges carry
the arguments' well-scopedness, so `wfOpsM`'s condition is per call
(`EnvWF env ∧ wscopedB`) and can no longer be discharged wholesale per
function.  This module proves the run-level implications instead: a
successful `wfOpsM` run of each declaration-checker function over a
well-formed environment is the pure `fueledOps` run at the same fuel.
At each operation call site the argument's well-scopedness comes from

* the checker's own input validation (`looseBVarsBounded`/`hasFvar`
  guards precede every `annotate` of raw input — at depth 0
  fvar-freedom *is* well-scopedness),
* the scoping-preservation lemmas for the operations' outputs
  (`annotateCore_WScoped`, `inferTypeCore_WScoped`), and
* scoping of the iota-theorem check's opened telescopes
  (`openPisAtFvars_WScoped`, `instPisAt_WScoped`, `instLamsAt_WScoped`
  — the defeq comparisons run at the opened depth, over variables of
  that frame).

`Setlec/Model/BridgeWF.lean` composes these with the intermediate
`EnvWF` facts into `checkDecl_bridge`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

/-! ## Small syntactic toolkit -/

theorem wscopedB_of_not_hasFvar {e : Expr} (h : e.hasFvar = false)
    {d : Nat} : e.wscopedB d = true :=
  (WScoped.of_not_hasFvar h).to_wscopedB

theorem WScoped.to_wscopedB' {e : Expr} {d : Nat} (h : WScoped d e) :
    e.wscopedB d = true := h.to_wscopedB

theorem hasFvar_liftLooseBVars (n : Nat) :
    ∀ (c : Nat) (e : Expr), (e.liftLooseBVars n c).hasFvar = e.hasFvar := by
  intro c e
  induction e generalizing c <;>
    simp_all [Expr.liftLooseBVars, Expr.hasFvar]
  case bvar i => split <;> simp [Expr.hasFvar]

theorem hasFvar_renameConsts (f : Name → Name) :
    ∀ (e : Expr), (e.renameConsts f).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.hasFvar]

theorem hasFvar_mkAppN :
    ∀ (args : List Expr) (g : Expr), g.hasFvar = false →
      (∀ x ∈ args, x.hasFvar = false) → (Expr.mkAppN g args).hasFvar = false
  | [], g, hg, _ => hg
  | a :: as, g, hg, hargs => by
    simp only [Expr.mkAppN]
    refine hasFvar_mkAppN as _ ?_
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
    simp only [Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨hg, hargs a (List.mem_cons_self ..)⟩

theorem stripLams_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, Expr.stripLams k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.2.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripLams, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .lam n ty b m, h =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (n, ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripLams_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

theorem stripPis_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, Expr.stripPis k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.2.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripPis, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .forallE n ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (n, ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripPis_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

theorem atF_bind_ok {α β : Type} {x : FueledM α} {g : α → FueledM β}
    {F : Nat} {v : β} (h : (x >>= g).val F = .ok v) :
    ∃ a, x.val F = .ok a ∧ (g a).val F = .ok v := by
  rw [FueledM.atF_bind] at h
  revert h
  cases hx : x.val F with
  | error e =>
    intro h
    simp only [Bind.bind, Except.bind] at h
    exact nomatch h
  | ok a =>
    intro h
    simp only [Bind.bind, Except.bind] at h
    exact ⟨a, rfl, h⟩

theorem atF_throw_bind {α β : Type} {e : CheckError}
    {g : α → FueledM β} {F : Nat} {v : β}
    (h : ((throw e : FueledM α) >>= g).val F = .ok v) : False := by
  rw [FueledM.atF_bind] at h
  simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind,
    Except.bind] at h
  exact nomatch h

/-! ## The leaf checker functions, `wfOpsM` runs to pure runs -/

theorem checkConstantVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {F : Nat} {v : ConstantVal}
    (h : (checkConstantVal wfOpsM env cv).val F = .ok v) :
    checkConstantVal (fueledOps F) env cv = .ok v := by
  unfold checkConstantVal at h ⊢
  dsimp only [] at h ⊢
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h
    exact absurd h atF_throw_bind
  rw [if_neg h1] at h ⊢
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h
    exact absurd h atF_throw_bind
  rw [if_neg h3] at h ⊢
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg =>
    rw [if_neg h5] at h
    exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h
    exact absurd h atF_throw_bind
  rw [if_neg h6] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h6))] at h
  obtain ⟨type, hty, h⟩ := atF_bind_ok h
  have hty' : annotateCore env F 0 cv.type = .ok type := hty
  show (annotateCore env F 0 cv.type >>= _) = _
  rw [hty']
  simp only [Bind.bind, Except.bind]
  have hwty : WScoped 0 type := annotateCore_WScoped F cv.type hty'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6))
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg =>
    rw [if_neg h7] at h
    exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  by_cases h8 : Expr.constsResolve env type = true
  case neg =>
    rw [if_neg h8] at h
    exact absurd h atF_throw_bind
  rw [if_pos h8] at h ⊢
  rw [wfOpsM_inferType henv hwty.to_wscopedB] at h
  obtain ⟨stype, hsty, h⟩ := atF_bind_ok h
  have hsty' : inferTypeCore env F 0 type = .ok stype := hsty
  show (inferTypeCore env F 0 type >>= _) = _
  rw [hsty']
  simp only [Bind.bind, Except.bind]
  have hwsty : WScoped 0 stype := inferTypeCore_WScoped henv F hsty' hwty
  rw [wfOpsM_ensureSort henv hwsty.to_wscopedB] at h
  obtain ⟨u, hu, h⟩ := atF_bind_ok h
  have hu' : ensureSortCore env F 0 stype = .ok u := hu
  show (ensureSortCore env F 0 stype >>= _) = _
  rw [hu']
  simp only [Bind.bind, Except.bind]
  exact h

theorem checkDefnVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hcvty : cv.type.hasFvar = false) {F : Nat} {v : Env}
    (h : (checkDefnVal wfOpsM env cv value hint).val F = .ok v) :
    checkDefnVal (fueledOps F) env cv value hint = .ok v := by
  unfold checkDefnVal at h ⊢
  dsimp only [] at h ⊢
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h2))] at h
  obtain ⟨value', hval, h⟩ := atF_bind_ok h
  have hval' : annotateCore env F 0 value = .ok value' := hval
  show (annotateCore env F 0 value >>= _) = _
  rw [hval']
  simp only [Bind.bind, Except.bind]
  have hwval : WScoped 0 value' := annotateCore_WScoped F value hval'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2))
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
  case neg =>
    rw [if_neg h3] at h
    exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : Expr.constsResolve env value' = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  rw [wfOpsM_inferType henv hwval.to_wscopedB] at h
  obtain ⟨vtype, hvt, h⟩ := atF_bind_ok h
  have hvt' : inferTypeCore env F 0 value' = .ok vtype := hvt
  show (inferTypeCore env F 0 value' >>= _) = _
  rw [hvt']
  simp only [Bind.bind, Except.bind]
  have hwvt : WScoped 0 vtype := inferTypeCore_WScoped henv F hvt' hwval
  rw [wfOpsM_isDefEq henv hwvt.to_wscopedB
    (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨b, hb, h⟩ := atF_bind_ok h
  have hb' : isDefEqCore env F 0 vtype cv.type = .ok b := hb
  show (isDefEqCore env F 0 vtype cv.type >>= _) = _
  rw [hb']
  simp only [Bind.bind, Except.bind]
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h atF_throw_bind

theorem checkThmVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (hcvty : cv.type.hasFvar = false) {F : Nat} {v : Env}
    (h : (checkThmVal wfOpsM env cv value).val F = .ok v) :
    checkThmVal (fueledOps F) env cv value = .ok v := by
  unfold checkThmVal at h ⊢
  dsimp only [] at h ⊢
  rw [wfOpsM_inferType henv (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨stype, hst, h⟩ := atF_bind_ok h
  have hst' : inferTypeCore env F 0 cv.type = .ok stype := hst
  show (inferTypeCore env F 0 cv.type >>= _) = _
  rw [hst']
  simp only [Bind.bind, Except.bind]
  have hwst : WScoped 0 stype := inferTypeCore_WScoped henv F hst'
    (WScoped.of_not_hasFvar hcvty)
  rw [wfOpsM_ensureSort henv hwst.to_wscopedB] at h
  obtain ⟨u, hu, h⟩ := atF_bind_ok h
  have hu' : ensureSortCore env F 0 stype = .ok u := hu
  show (ensureSortCore env F 0 stype >>= _) = _
  rw [hu']
  simp only [Bind.bind, Except.bind]
  obtain ⟨ok₁, hok, h⟩ := atF_bind_ok h
  rw [liftFueled_atF] at hok
  show ((liftFueled "level comparison" (u.isEquiv .zero) :
    CheckM Bool) >>= _) = _
  rw [hok]
  simp only [Bind.bind, Except.bind]
  by_cases h0 : ok₁ = true
  case neg =>
    rw [if_neg h0] at h
    exact absurd h atF_throw_bind
  rw [if_pos h0] at h ⊢
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h2))] at h
  obtain ⟨value', hval, h⟩ := atF_bind_ok h
  have hval' : annotateCore env F 0 value = .ok value' := hval
  show (annotateCore env F 0 value >>= _) = _
  rw [hval']
  simp only [Bind.bind, Except.bind]
  have hwval : WScoped 0 value' := annotateCore_WScoped F value hval'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2))
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
  case neg =>
    rw [if_neg h3] at h
    exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : Expr.constsResolve env value' = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  rw [wfOpsM_inferType henv hwval.to_wscopedB] at h
  obtain ⟨vtype, hvt, h⟩ := atF_bind_ok h
  have hvt' : inferTypeCore env F 0 value' = .ok vtype := hvt
  show (inferTypeCore env F 0 value' >>= _) = _
  rw [hvt']
  simp only [Bind.bind, Except.bind]
  have hwvt : WScoped 0 vtype := inferTypeCore_WScoped henv F hvt' hwval
  rw [wfOpsM_isDefEq henv hwvt.to_wscopedB
    (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨b, hb, h⟩ := atF_bind_ok h
  have hb' : isDefEqCore env F 0 vtype cv.type = .ok b := hb
  show (isDefEqCore env F 0 vtype cv.type >>= _) = _
  rw [hb']
  simp only [Bind.bind, Except.bind]
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h atF_throw_bind

theorem checkOpaqueVal_wfimp {env : Env} (henv : EnvWF env)
    {cv : ConstantVal} {value : Expr}
    (hcvty : cv.type.hasFvar = false) {F : Nat} {v : Env}
    (h : (checkOpaqueVal wfOpsM env cv value).val F = .ok v) :
    checkOpaqueVal (fueledOps F) env cv value = .ok v := by
  unfold checkOpaqueVal at h ⊢
  dsimp only [] at h ⊢
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h
    exact absurd h atF_throw_bind
  rw [if_neg h2] at h ⊢
  rw [wfOpsM_annotate henv
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h2))] at h
  obtain ⟨value', hval, h⟩ := atF_bind_ok h
  have hval' : annotateCore env F 0 value = .ok value' := hval
  show (annotateCore env F 0 value >>= _) = _
  rw [hval']
  simp only [Bind.bind, Except.bind]
  have hwval : WScoped 0 value' := annotateCore_WScoped F value hval'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2))
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
  case neg =>
    rw [if_neg h3] at h
    exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : Expr.constsResolve env value' = true
  case neg =>
    rw [if_neg h4] at h
    exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  rw [wfOpsM_inferType henv hwval.to_wscopedB] at h
  obtain ⟨vtype, hvt, h⟩ := atF_bind_ok h
  have hvt' : inferTypeCore env F 0 value' = .ok vtype := hvt
  show (inferTypeCore env F 0 value' >>= _) = _
  rw [hvt']
  simp only [Bind.bind, Except.bind]
  have hwvt : WScoped 0 vtype := inferTypeCore_WScoped henv F hvt' hwval
  rw [wfOpsM_isDefEq henv hwvt.to_wscopedB
    (wscopedB_of_not_hasFvar hcvty)] at h
  obtain ⟨b, hb, h⟩ := atF_bind_ok h
  have hb' : isDefEqCore env F 0 vtype cv.type = .ok b := hb
  show (isDefEqCore env F 0 vtype cv.type >>= _) = _
  rw [hb']
  simp only [Bind.bind, Except.bind]
  cases b with
  | true =>
    simp only [↓reduceIte] at h ⊢
    exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h atF_throw_bind

theorem certifyNatEqs_wfimp {env : Env} (henv : EnvWF env) {F : Nat} :
    ∀ {eqs : List (Expr × Expr)},
      (∀ eq ∈ eqs, (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true)) →
      ∀ {v : Bool}, (certifyNatEqs wfOpsM env eqs).val F = .ok v →
      certifyNatEqs (fueledOps F) env eqs = .ok v
  | [], _, v, h => h
  | eq :: rest, hsc, v, h => by
    unfold certifyNatEqs at h ⊢
    have hh := hsc eq (List.mem_cons_self ..)
    rw [wfOpsM_isDefEq henv hh.1 hh.2] at h
    obtain ⟨b, hb, h⟩ := atF_bind_ok h
    have hb' : isDefEqCore env F 2 eq.1 eq.2 = .ok b := hb
    show (isDefEqCore env F 2 eq.1 eq.2 >>= _) = _
    rw [hb']
    simp only [Bind.bind, Except.bind]
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact certifyNatEqs_wfimp henv
        (fun e he => hsc e (List.mem_cons_of_mem _ he)) h
    | false =>
      simpa using h

set_option maxHeartbeats 1600000 in
/-- `getD` with the `bvar 0` default preserves well-scopedness. -/
theorem WScoped_getD' {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x List.mem_cons_self
    | succ n =>
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- Opening a `∀`-telescope at fresh free variables produces variables
and a body scoped at the extended frame. -/
theorem openPisAtFvars_WScoped :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) → WScoped i e →
      (∀ x ∈ fvs, WScoped (i + n) x) ∧ WScoped (i + n) body := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h hw
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hw⟩
  | succ n ih =>
    intro e i fvs body h hw
    cases e with
    | forallE nm dom bodyE mb =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i nm dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hw
        obtain ⟨hdom, hbody⟩ := hw
        have hinst : WScoped (i + 1)
            (bodyE.instantiate1 (.fvar i nm dom)) :=
          WScoped.instantiate1 hdom 0 hbody
        obtain ⟨hfvs', hbody'⟩ := ih _ _ hrec hinst
        have harith : i + 1 + n = i + (n + 1) := by omega
        rw [harith] at hfvs' hbody'
        refine ⟨?_, hbody'⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [WScoped]
          exact ⟨by omega, hdom⟩
        · exact hfvs' x hx
    | bvar k => exact nomatch h
    | fvar a b c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a => exact nomatch h
    | lam a b c d => exact nomatch h
    | letE a b c d => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- Instantiating a `∀`-telescope at scoped arguments produces scoped
domains and a scoped residual. -/
theorem instPisAt_WScoped {d : Nat} :
    ∀ (args : List Expr) (ty : Expr) {doms : List Expr} {res : Expr},
      Expr.instPisAt args ty = some (doms, res) → WScoped d ty →
      (∀ a ∈ args, WScoped d a) →
      (∀ x ∈ doms, WScoped d x) ∧ WScoped d res
  | [], ty, doms, res, h, hty, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hty⟩
  | a :: as, ty, doms, res, h, hty, hargs => by
    cases ty with
    | forallE nm dom body mb =>
      simp only [Expr.instPisAt] at h
      revert h
      cases hrec : Expr.instPisAt as (body.instantiate1 a) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨ds, rest⟩ := p
        intro h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hty
        obtain ⟨hdom, hbody⟩ := hty
        have hinst : WScoped d (body.instantiate1 a) :=
          WScoped.instantiate1_gen (hargs a List.mem_cons_self) 0 hbody
        obtain ⟨hds, hres⟩ := instPisAt_WScoped as _ hrec hinst
          (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
        refine ⟨?_, hres⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hds x hx
    | bvar k => exact nomatch h
    | fvar a' b c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a' => exact nomatch h
    | lam a' b c d' => exact nomatch h
    | letE a' b c d' => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- `instPisAt` for `λ`-binders, scoped. -/
theorem instLamsAt_WScoped {d : Nat} :
    ∀ (args : List Expr) (ty : Expr) {doms : List Expr} {res : Expr},
      Expr.instLamsAt args ty = some (doms, res) → WScoped d ty →
      (∀ a ∈ args, WScoped d a) →
      (∀ x ∈ doms, WScoped d x) ∧ WScoped d res
  | [], ty, doms, res, h, hty, _ => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hty⟩
  | a :: as, ty, doms, res, h, hty, hargs => by
    cases ty with
    | lam nm dom body mb =>
      simp only [Expr.instLamsAt] at h
      revert h
      cases hrec : Expr.instLamsAt as (body.instantiate1 a) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨ds, rest⟩ := p
        intro h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hty
        obtain ⟨hdom, hbody⟩ := hty
        have hinst : WScoped d (body.instantiate1 a) :=
          WScoped.instantiate1_gen (hargs a List.mem_cons_self) 0 hbody
        obtain ⟨hds, hres⟩ := instLamsAt_WScoped as _ hrec hinst
          (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
        refine ⟨?_, hres⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hds x hx
    | bvar k => exact nomatch h
    | fvar a' b c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a' => exact nomatch h
    | forallE a' b c d' => exact nomatch h
    | letE a' b c d' => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- The read-off type of an opened variable is scoped. -/
theorem fvarTypeD_WScoped {d : Nat} {e : Expr} (h : WScoped d e) :
    WScoped d (Expr.fvarTypeD e) := by
  cases e with
  | fvar idx nm ty =>
    simp only [WScoped] at h
    exact WScoped.mono (Nat.le_of_lt h.1) h.2
  | bvar k => exact h
  | sort u => exact h
  | const c us => exact h
  | app f a => exact h
  | lam a b c d' => exact h
  | forallE a b c d' => exact h
  | letE a b c d' => exact h
  | lit l => exact h
  | proj s k e => exact h

theorem unwrapOr_atF_ok {α : Type} {o : Option α} {err : CheckError}
    {F : Nat} {a : α}
    (h : (unwrapOr o err : FueledM α).val F = .ok a) : o = some a := by
  cases o with
  | none => exact nomatch h
  | some b =>
    have hb : b = a := by
      have h' : (Except.ok b : Except CheckError α) = .ok a := h
      exact Except.ok.inj h'
    rw [hb]

/-- Invert a stored-theorem lookup. -/
theorem findThm?_ok {env : Env} {n : Name} {cvt : ConstantVal}
    {tval : Expr} (h : env.findThm? n = some (cvt, tval)) :
    env.find? n = some (.thmInfo cvt tval) := by
  unfold Env.findThm? at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo cv v) =>
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- The pairwise defeq check, `wfOpsM` run to pure run (the arguments
are scoped at the check's depth). -/
theorem checkDefEqList_wfimp {env : Env} (henv : EnvWF env)
    {depth : Nat} {F : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, WScoped depth a) → (∀ b ∈ bs, WScoped depth b) →
      ∀ {v : Unit},
      (checkDefEqList wfOpsM env depth as bs).val F = .ok v →
      checkDefEqList (fueledOps F) env depth as bs = .ok v
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, _, h => nomatch h
  | _ :: _, [], _, _, _, h => nomatch h
  | a :: as, b :: bs, ha, hb, v, h => by
    unfold checkDefEqList at h ⊢
    rw [wfOpsM_isDefEq henv (ha a List.mem_cons_self).to_wscopedB
      (hb b List.mem_cons_self).to_wscopedB] at h
    obtain ⟨c, hc, h⟩ := atF_bind_ok h
    have hc' : isDefEqCore env F depth a b = .ok c := hc
    show (isDefEqCore env F depth a b >>= _) = _
    rw [hc']
    simp only [Bind.bind, Except.bind]
    cases c with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkDefEqList_wfimp henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) h

set_option maxHeartbeats 6400000 in
/-- The iota-theorem check, `wfOpsM` run to pure run.  The recursor
type, the constructor type and the annotated rule right-hand side are
closed; everything the check compares is scoped at the opened
telescope's depth. -/
theorem checkIotaThm_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {nP nM nm ni j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr} {F : Nat}
    {v : Unit}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false)
    (h : (checkIotaThm wfOpsM env' envSelf f cvName lps tyA
      nP nM nm ni j r cvj cnP cnF rhsA).val F = .ok v) :
    checkIotaThm (fueledOps F) env' envSelf f cvName lps tyA
      nP nM nm ni j r cvj cnP cnF rhsA = .ok v := by
  unfold checkIotaThm at h ⊢
  try dsimp only [] at h ⊢
  obtain ⟨p, hthm, h⟩ := atF_bind_ok h
  obtain ⟨cvt, tval⟩ := p
  have hthm' := unwrapOr_atF_ok hthm
  show ((unwrapOr (env'.findThm?
    ((cvName.str "_model").str s!"iota_{j}")) _ : CheckM _) >>= _) = _
  rw [hthm']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- the stored theorem's statement is closed
  have hcvtF : cvt.type.hasFvar = false :=
    (henv' _ (find?_mem (findThm?_ok hthm'))).1
  by_cases h1 : cvt.levelParams = lps
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨q, hopen, h⟩ := atF_bind_ok h
  obtain ⟨fvs, tbody⟩ := q
  have hopen' := unwrapOr_atF_ok hopen
  show ((unwrapOr (openPisAtFvars (nP + nM + nm + cnF) cvt.type 0) _ :
    CheckM _) >>= _) = _
  rw [hopen']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- scoping of the opened telescope
  have hopenW := openPisAtFvars_WScoped (nP + nM + nm + cnF) cvt.type 0
    hopen' (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (nP + nM + nm + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (nP + nM + nm + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (nP + nM + nm + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (nP + nM + nm + cnF) x := Expr.WScoped.getAppArgs hlhsW
  by_cases h2 : isEqHead tbody.getAppFn = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : tbody.getAppArgs.length = 3
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  try dsimp only [] at h ⊢
  by_cases h4 : ((tbody.getAppArgs.getD 1 (.bvar 0)).getAppFn ==
      Expr.const (f cvName) (lps.map .param)) = true
  case neg => rw [if_neg h4] at h; exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  by_cases h5 : (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs.length =
      nP + nM + nm + ni + 1
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take (nP + nM + nm) ==
      fvs.take (nP + nM + nm)) = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop (nP + nM + nm))) = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  by_cases h8 : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => rw [if_neg h8] at h; exact absurd h atF_throw_bind
  rw [if_pos h8] at h ⊢
  obtain ⟨q2, hcinst, h⟩ := atF_bind_ok h
  obtain ⟨cdoms, cres⟩ := q2
  have hcinst' := unwrapOr_atF_ok hcinst
  show ((unwrapOr (Expr.instPisAt (fvs.take cnP ++
    fvs.drop (nP + nM + nm)) (cvj.type.renameConsts f)) _ :
    CheckM _) >>= _) = _
  rw [hcinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcargW : ∀ a ∈ fvs.take cnP ++ fvs.drop (nP + nM + nm),
      WScoped (nP + nM + nm + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact hfvsW a (List.mem_of_mem_take hax)
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + ni
  case neg => rw [if_neg h9] at h; exact absurd h atF_throw_bind
  rw [if_pos h9] at h ⊢
  obtain ⟨u1, hd1, h⟩ := atF_bind_ok h
  have hd1' := checkDefEqList_wfimp henvSelf
    (fun a ha => hlargsW a
      (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
    (fun b hb => Expr.WScoped.getAppArgs hcresW b
      (List.mem_of_mem_drop hb)) hd1
  show (checkDefEqList (fueledOps F) envSelf _ _ _ >>= _) = _
  rw [hd1']
  simp only [Bind.bind, Except.bind]
  obtain ⟨u2, hd2, h⟩ := atF_bind_ok h
  have hd2' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_drop hx)))
    (fun b hb => hcdomsW b (List.mem_of_mem_drop hb)) hd2
  show (checkDefEqList (fueledOps F) envSelf _ _ _ >>= _) = _
  rw [hd2']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q3, hrinst, h⟩ := atF_bind_ok h
  obtain ⟨rdoms, rrest⟩ := q3
  have hrinst' := unwrapOr_atF_ok hrinst
  show ((unwrapOr (Expr.instPisAt (fvs.take (nP + nM + nm))
    (tyA.renameConsts f)) _ : CheckM _) >>= _) = _
  rw [hrinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hrinstW := instPisAt_WScoped _ _ hrinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact htyA))
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
  obtain ⟨hrdomsW, -⟩ := hrinstW
  obtain ⟨u3, hd3, h⟩ := atF_bind_ok h
  have hd3' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsW x (List.mem_of_mem_take hx)))
    (fun b hb => hrdomsW b hb) hd3
  show (checkDefEqList (fueledOps F) envSelf _ _ _ >>= _) = _
  rw [hd3']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q4, hopenP, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, restP⟩ := q4
  have hopenP' := unwrapOr_atF_ok hopenP
  show ((unwrapOr (openPisAtFvars (nP + nM + nm) tyA 0) _ :
    CheckM _) >>= _) = _
  rw [hopenP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenPW := openPisAtFvars_WScoped (nP + nM + nm) tyA 0 hopenP'
    (WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  obtain ⟨q5, hcinstP, h⟩ := atF_bind_ok h
  obtain ⟨cdomsP, crestP⟩ := q5
  have hcinstP' := unwrapOr_atF_ok hcinstP
  show ((unwrapOr (Expr.instPisAt (fvsP.take cnP) cvj.type) _ :
    CheckM _) >>= _) = _
  rw [hcinstP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcinstPW := instPisAt_WScoped (d := nP + nM + nm) _ _ hcinstP'
    (WScoped.of_not_hasFvar hctor)
    (fun a ha => hfvsPW a (List.mem_of_mem_take ha))
  obtain ⟨-, hcrestPW⟩ := hcinstPW
  obtain ⟨q6, hopenX, h⟩ := atF_bind_ok h
  obtain ⟨xFvsP, crest2⟩ := q6
  have hopenX' := unwrapOr_atF_ok hopenX
  show ((unwrapOr (openPisAtFvars cnF crestP (nP + nM + nm)) _ :
    CheckM _) >>= _) = _
  rw [hopenX']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenXW := openPisAtFvars_WScoped cnF crestP (nP + nM + nm)
    hopenX' hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (nP + nM + nm + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  obtain ⟨q7, hlinst, h⟩ := atF_bind_ok h
  obtain ⟨ldoms, lrest⟩ := q7
  have hlinst' := unwrapOr_atF_ok hlinst
  show ((unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA) _ :
    CheckM _) >>= _) = _
  rw [hlinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hlinstW := instLamsAt_WScoped _ _ hlinst'
    (WScoped.of_not_hasFvar hrhsA) hfvsPW'
  obtain ⟨hldomsW, -⟩ := hlinstW
  obtain ⟨u4, hd4, h⟩ := atF_bind_ok h
  have hd4' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hfvsPW' x hx))
    (fun b hb => hldomsW b hb) hd4
  show (checkDefEqList (fueledOps F) envSelf _ _ _ >>= _) = _
  rw [hd4']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_isDefEq henvSelf hrhsSW.to_wscopedB
    (Expr.WScoped.mkAppN
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact hrhsA))
      (fun x hx => hfvsW x hx)).to_wscopedB] at h
  obtain ⟨c, hde, h⟩ := atF_bind_ok h
  have hde' : isDefEqCore envSelf F (nP + nM + nm + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0))
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok c := hde
  show (isDefEqCore envSelf F _ _ _ >>= _) = _
  rw [hde']
  simp only [Bind.bind, Except.bind]
  cases c with
  | false =>
    rw [if_neg (by simp)] at h
    exact nomatch h
  | true =>
    rw [if_pos rfl] at h ⊢

theorem checkIotaRule_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {nP nM nm ni j : Nat} {r : RecRule}
    {F : Nat} {v : RecRule} (htyA : tyA.hasFvar = false)
    (h : (checkIotaRule wfOpsM env' envSelf f cvName lps tyA
      nP nM nm ni j r).val F = .ok v) :
    checkIotaRule (fueledOps F) env' envSelf f cvName lps tyA
      nP nM nm ni j r = .ok v := by
  unfold checkIotaRule at h ⊢
  dsimp only [] at h ⊢
  revert h
  match hf : env'.find? r.ctor with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) => ?_
  intro h
  dsimp only [] at h ⊢
  by_cases h2 : r.nfields = cnF
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : Expr.looseBVarsBounded 0 (RecRule.rhs r) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : (RecRule.rhs r).hasFvar = true
  · rw [if_pos h4] at h; exact absurd h atF_throw_bind
  rw [if_neg h4] at h ⊢
  rw [wfOpsM_annotate henvSelf
    (wscopedB_of_not_hasFvar (Bool.not_eq_true _ ▸ h4))] at h
  obtain ⟨rhsA, hann, h⟩ := atF_bind_ok h
  have hann' : annotateCore envSelf F 0 (RecRule.rhs r) = .ok rhsA := hann
  show (annotateCore envSelf F 0 (RecRule.rhs r) >>= _) = _
  rw [hann']
  simp only [Bind.bind, Except.bind]
  have hwrhsA : WScoped 0 rhsA := annotateCore_WScoped F _ hann'
    (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h4))
  have hrhsAF : rhsA.hasFvar = false :=
    not_hasFvar_of_fvarsBelow_zero hwrhsA.fvarsBelow
  by_cases h5 : Expr.allLevelParamsDefined lps rhsA = true
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : Expr.constsResolve envSelf rhsA = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : (rhsA.stripLams (nP + nM + nm + cnF)).isSome = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  rw [wfOpsM_inferType henvSelf hwrhsA.to_wscopedB] at h
  obtain ⟨rhsTy, hity, h⟩ := atF_bind_ok h
  have hity' : inferTypeCore envSelf F 0 rhsA = .ok rhsTy := hity
  show (inferTypeCore envSelf F 0 rhsA >>= _) = _
  rw [hity']
  simp only [Bind.bind, Except.bind]
  by_cases h8 : Expr.recRulePlain tyA nP nM nm ni cnP = true
  case neg =>
    rw [if_neg h8] at h ⊢
    exact h
  rw [if_pos h8] at h ⊢
  obtain ⟨u, hthm, h⟩ := atF_bind_ok h
  have hthm' := checkIotaThm_wfimp henv' henvSelf htyA
    (show cvj.type.hasFvar = false from (henv' _ (find?_mem hf)).1)
    hrhsAF hthm
  show (checkIotaThm (fueledOps F) env' envSelf f cvName lps tyA
    nP nM nm ni j r cvj cnP cnF rhsA >>= _) = _
  rw [hthm']
  simp only [Bind.bind, Except.bind]
  exact h

theorem checkIotaRules_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {nP nM nm ni : Nat} {F : Nat}
    (htyA : tyA.hasFvar = false) :
    ∀ {j : Nat} {rules rules' : List RecRule},
      (checkIotaRules wfOpsM env' envSelf f cvName lps tyA
        nP nM nm ni j rules).val F = .ok rules' →
      checkIotaRules (fueledOps F) env' envSelf f cvName lps tyA
        nP nM nm ni j rules = .ok rules'
  | _, [], rules', h => h
  | j, r :: rest, rules', h => by
    unfold checkIotaRules at h ⊢
    obtain ⟨r', hr, h⟩ := atF_bind_ok h
    have hr' := checkIotaRule_wfimp henv' henvSelf htyA hr
    show (checkIotaRule (fueledOps F) env' envSelf f cvName lps tyA
      nP nM nm ni j r >>= _) = _
    rw [hr']
    simp only [Bind.bind, Except.bind]
    obtain ⟨rest', hrest, h⟩ := atF_bind_ok h
    have hrest' := checkIotaRules_wfimp henv' henvSelf htyA hrest
    show (checkIotaRules (fueledOps F) env' envSelf f cvName lps tyA
      nP nM nm ni (j + 1) rest >>= _) = _
    rw [hrest']
    simp only [Bind.bind, Except.bind]
    exact h

/-- The member-against-model check, `wfOpsM` run to pure run. -/
theorem checkMemberVal_wfimp {blockNames : List Name} {env' : Env}
    (henv' : EnvWF env') {cv : ConstantVal} {F : Nat} {v : ConstantVal}
    (h : (checkMemberVal wfOpsM blockNames env' cv).val F = .ok v) :
    checkMemberVal (fueledOps F) blockNames env' cv = .ok v := by
  unfold checkMemberVal at h ⊢
  dsimp only [] at h ⊢
  obtain ⟨cvA, hccvW, h⟩ := atF_bind_ok h
  have hccv := checkConstantVal_wfimp henv' hccvW
  show (checkConstantVal (fueledOps F) env' cv >>= _) = _
  rw [hccv]
  simp only [Bind.bind, Except.bind]
  by_cases h1 : cvA.name.isModelSuffix = true
  · rw [if_pos h1] at h
    exact absurd h atF_throw_bind
  rw [if_neg h1] at h ⊢
  revert h
  match hm : env'.find? (cvA.name.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvm mval mhint) => ?_
  intro h
  dsimp only [] at h ⊢
  by_cases h2 : cvm.levelParams = cvA.levelParams
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : Expr.eqUpToNames (cvA.type.renameConsts
      (fun n => if blockNames.contains n then n.str "_model" else n))
      cvm.type = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  exact h

theorem checkProjRule_wfimp {env' : Env} (henv' : EnvWF env')
    {cvj : ConstantVal} {lps : List Name} {nP nF i F : Nat} {v : Expr}
    (h : (checkProjRule wfOpsM env' cvj lps nP nF i).val F = .ok v) :
    checkProjRule (fueledOps F) env' cvj lps nP nF i = .ok v := by
  unfold checkProjRule at h ⊢
  dsimp only [] at h ⊢
  revert h
  match hrhs : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => intro h; exact nomatch h
  | some rhs => ?_
  intro h
  dsimp only [] at h ⊢
  by_cases h1 : (!rhs.hasFvar && Expr.looseBVarsBounded 0 rhs) = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  have hrf : rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact h1.1
  rw [wfOpsM_annotate henv' (wscopedB_of_not_hasFvar hrf)] at h
  obtain ⟨rhsA, hann, h⟩ := atF_bind_ok h
  have hann' : annotateCore env' F 0 rhs = .ok rhsA := hann
  show (annotateCore env' F 0 rhs >>= _) = _
  rw [hann']
  simp only [Bind.bind, Except.bind]
  by_cases h2 : (Expr.allLevelParamsDefined lps rhsA &&
      Expr.constsResolve env' rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  revert h
  match hstrip : rhsA.stripLams (nP + nF) with
  | none => intro h; exact nomatch h
  | some pr₁ => ?_
  obtain ⟨rbinders, rrbody⟩ := pr₁
  intro h
  try dsimp only [] at h ⊢
  by_cases h3 : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  revert h
  match hstripC : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some pr₂ => ?_
  obtain ⟨cbindersR, cbodyR⟩ := pr₂
  intro h
  try dsimp only [] at h ⊢
  by_cases h4 : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => rw [if_neg h4] at h; exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  exact h

theorem checkProjFn_wfimp {env' : Env} (henv' : EnvWF env')
    {T ctorName : Name} {lps : List Name} {nP nF i F : Nat} {v : Env}
    (h : (checkProjFn wfOpsM env' T ctorName lps nP nF i).val F = .ok v) :
    checkProjFn (fueledOps F) env' T ctorName lps nP nF i = .ok v := by
  unfold checkProjFn at h ⊢
  obtain ⟨⟨cvj, mcv⟩, hlk, h⟩ := atF_bind_ok h
  rw [checkProjLookups_datF] at hlk
  show ((checkProjLookups env' T ctorName lps nP nF i :
    CheckM (ConstantVal × ConstantVal)) >>= _) = _
  rw [hlk]
  simp only [Bind.bind, Except.bind]
  obtain ⟨pty, hty, h⟩ := atF_bind_ok h
  rw [checkProjTy_datF] at hty
  show ((checkProjTy env' T ctorName lps mcv.type nP nF :
    CheckM Expr) >>= _) = _
  rw [hty]
  simp only [Bind.bind, Except.bind]
  dsimp only [] at h ⊢
  by_cases h1 : i < nF
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨rhsA, hrule, h⟩ := atF_bind_ok h
  have hrule' := checkProjRule_wfimp henv' hrule
  show (checkProjRule (fueledOps F) env' cvj lps nP nF i >>= _) = _
  rw [hrule']
  simp only [Bind.bind, Except.bind]
  obtain ⟨u, hiota, h⟩ := atF_bind_ok h
  rw [checkProjIota_datF] at hiota
  show ((checkProjIota env' T ctorName lps cvj nP nF i :
    CheckM Unit) >>= _) = _
  rw [hiota]
  simp only [Bind.bind, Except.bind]
  exact h

theorem installProjFnStep_wfimp {e : Env} (he : EnvWF e)
    {T ctorName : Name} {lps : List Name} {nP nF i F : Nat} {e' : Env}
    (h : (installProjFnStep wfOpsM T ctorName lps nP nF e i).val F =
      .ok e') :
    installProjFnStep (fueledOps F) T ctorName lps nP nF e i = .ok e' := by
  unfold installProjFnStep at h ⊢
  split at h
  · rw [if_pos (by assumption)]
    exact checkProjFn_wfimp he h
  · rw [if_neg (by assumption)]
    exact h

/-! ## Scoping of the structural-Nat certification equations -/

/-- The recurrence equations' sides are well-scoped at depth 2 (their
free variables are `fvar 0`/`fvar 1` with closed annotations). -/
theorem natOpEquations_wscopedB {c : Name} (hc : c ∈ natOpNames) :
    ∀ eq ∈ natOpEquations 0 c,
      eq.1.wscopedB 2 = true ∧ eq.2.wscopedB 2 = true := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro eq heq
     simp +decide [natOpEquations] at heq
     first
       | (rcases heq with rfl | rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl) <;>
           simp +decide [Expr.wscopedB])

/-- Substituting a closed value for a constant preserves scoping. -/
theorem wscopedB_substConst0 {n : Name} {r : Expr}
    (hr : r.hasFvar = false) :
    ∀ (e : Expr) {d : Nat}, e.wscopedB d = true →
      (Expr.substConst0 n r e).wscopedB d = true
  | .const c us, d, he => by
    simp only [Expr.substConst0]
    split
    · exact wscopedB_of_not_hasFvar hr
    · exact he
  | .app f a, d, he => by
    simp only [Expr.substConst0, Expr.wscopedB, Bool.and_eq_true] at he ⊢
    exact ⟨wscopedB_substConst0 hr f he.1, wscopedB_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _ _, _, he | .sort _, _, he | .lit _, _, he
  | .lam _ _ _ _, _, he | .forallE _ _ _ _, _, he
  | .letE _ _ _ _, _, he | .proj _ _ _, _, he => he

/-! ## The div/mod pin gate, `wfOpsM` runs to pure runs -/

theorem atF_throw {α : Type} {e : CheckError} {F : Nat} {v : α}
    (h : ((throw e : FueledM α)).val F = .ok v) : False := by
  simp only [throw, throwThe, MonadExceptOf.throw] at h
  exact nomatch h

/-- The pinned open certificate statements are well-scoped at the
certificate frame: hypotheses at their own binder index (they ride as
the `fvar 2`/`fvar 3` annotations), the equation at the full frame. -/
theorem divModCertStmts_wscopedB {c : Name} (hc : c ∈ natDivModNames) :
    ∀ st ∈ divModCertStmts c,
      (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧ st.2.wscopedB 4 = true := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  intro st hst
  rcases hc with rfl | rfl <;>
    (simp only [divModCertStmts, List.mem_cons, List.not_mem_nil,
      or_false, reduceIte] at hst
     rcases hst with rfl | rfl | rfl <;>
      refine ⟨fun hyp hh => ?_, by simp +decide [Expr.wscopedB]⟩ <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
       first
        | (rcases hh with rfl | rfl <;> simp +decide [Expr.wscopedB])
        | (rcases hh with rfl; simp +decide [Expr.wscopedB])))

/-- The applied certificate proof is well-scoped at the frame. -/
theorem divModCertApplied_wscopedB {proofS : Expr} {hyps : List Expr}
    (hp : proofS.hasFvar = false)
    (hh : ∀ hyp ∈ hyps, hyp.wscopedB 2 = true) :
    (divModCertApplied proofS hyps).wscopedB 4 = true := by
  have hpw : proofS.wscopedB 4 = true := wscopedB_of_not_hasFvar hp
  unfold divModCertApplied
  match hyps, hh with
  | [], hh => simp [Expr.wscopedB, hpw]
  | [h1], hh =>
    have h1w := hh h1 (by simp)
    simp [Expr.wscopedB, hpw, h1w]
  | [h1, h2], hh =>
    have h1w := hh h1 (by simp)
    have h2w3 : h2.wscopedB 3 = true :=
      (WScoped.mono (by omega) (WScoped.of_wscopedB
        (hh h2 (by simp)))).to_wscopedB
    simp [Expr.wscopedB, hpw, h1w, h2w3]
  | _ :: _ :: _ :: _, hh => simp [Expr.wscopedB, hpw]

theorem checkDivModCerts_wfimp {env : Env} (henv : EnvWF env) {F : Nat}
    {c : Name} {annVal : Expr} (hvf : annVal.hasFvar = false) :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
      (∀ st ∈ stmts, (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧
        st.2.wscopedB 4 = true) →
      ∀ {v : Bool},
        (checkDivModCerts wfOpsM env c annVal stmts proofs).val F = .ok v →
        checkDivModCerts (fueledOps F) env c annVal stmts proofs = .ok v
  | [], [], _, v, h => h
  | [], _ :: _, _, v, h => h
  | _ :: _, [], _, v, h => h
  | (hyps, eqE) :: srest, proof :: prest, hsc, v, h => by
    unfold checkDivModCerts at h ⊢
    obtain ⟨hhyps, heqw⟩ := hsc (hyps, eqE) (List.mem_cons_self ..)
    have hhypsS : ∀ hyp ∈ hyps.map (Expr.substConst0 c annVal),
        hyp.wscopedB 2 = true := by
      intro hyp hh
      obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.mp hh
      exact wscopedB_substConst0 hvf _ (hhyps h₀ hh₀)
    have heqS : (Expr.substConst0 c annVal eqE).wscopedB 4 = true :=
      wscopedB_substConst0 hvf _ heqw
    revert h
    by_cases hguards : divModCertGuard env c annVal hyps eqE proof = true
    case neg => rw [if_neg hguards, if_neg hguards]; intro h; exact h
    rw [if_pos hguards, if_pos hguards]
    have hguards' := hguards
    unfold divModCertGuard at hguards'
    simp only [Bool.and_eq_true] at hguards'
    have hpf : (Expr.substConstAll c annVal proof).hasFvar = false := by
      simpa using hguards'.1.1.1.1.2
    have happW : (divModCertApplied (Expr.substConstAll c annVal proof)
        (hyps.map (Expr.substConst0 c annVal))).wscopedB 4 = true :=
      divModCertApplied_wscopedB hpf hhypsS
    intro h
    rw [wfOpsM_annotate henv happW] at h
    obtain ⟨appliedA, hann, h⟩ := atF_bind_ok h
    have hann' : annotateCore env F 4 _ = .ok appliedA := hann
    show (annotateCore env F 4 _ >>= _) = _
    rw [hann']
    simp only [Bind.bind, Except.bind]
    have happAW : WScoped 4 appliedA :=
      annotateCore_WScoped F _ hann' (WScoped.of_wscopedB happW)
    rw [wfOpsM_inferType henv happAW.to_wscopedB] at h
    obtain ⟨tp, hinf, h⟩ := atF_bind_ok h
    have hinf' : inferTypeCore env F 4 appliedA = .ok tp := hinf
    show (inferTypeCore env F 4 appliedA >>= _) = _
    rw [hinf']
    simp only [Bind.bind, Except.bind]
    have htpW : WScoped 4 tp := inferTypeCore_WScoped henv F hinf' happAW
    rw [wfOpsM_isDefEq henv htpW.to_wscopedB heqS] at h
    obtain ⟨b, hde, h⟩ := atF_bind_ok h
    have hde' : isDefEqCore env F 4 tp _ = .ok b := hde
    show (isDefEqCore env F 4 tp _ >>= _) = _
    rw [hde']
    simp only [Bind.bind, Except.bind]
    cases b with
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact checkDivModCerts_wfimp henv hvf
        (fun st hs => hsc st (List.mem_cons_of_mem _ hs)) h
    | false => simpa using h

theorem checkDivModPin_wfimp {env env2 : Env} (henv : EnvWF env) {F : Nat}
    {c : Name} (hc : c ∈ natDivModNames)
    (hv'f : ∀ cv' v' h', env2.find? c = some (.defnInfo cv' v' h') →
      v'.hasFvar = false)
    {u : Unit} (h : (checkDivModPin wfOpsM env env2 c).val F = .ok u) :
    checkDivModPin (fueledOps F) env env2 c = .ok u := by
  unfold checkDivModPin at h ⊢
  by_cases h1 : divModEnvGuard env2 c = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw
  rw [if_pos h1] at h ⊢
  revert h
  cases hfind : env2.find? c with
  | none => intro h; exact absurd h atF_throw
  | some ci =>
    cases ci with
    | axiomInfo cv' => intro h; exact absurd h atF_throw
    | thmInfo cv' v' => intro h; exact absurd h atF_throw
    | indInfo cv' caps => intro h; exact absurd h atF_throw
    | ctorInfo cv' nP nF => intro h; exact absurd h atF_throw
    | recInfo cv' nP nM nm ni rules => intro h; exact absurd h atF_throw
    | defnInfo cv' value' hint' =>
      intro h
      dsimp only at h ⊢
      by_cases hping : (divModPinGuard env c &&
          divModCertsGuard env c value') = true
      case neg =>
        rw [if_neg hping] at h
        exact absurd h atF_throw
      rw [if_pos hping] at h ⊢
      have hping' := hping
      simp only [Bool.and_eq_true] at hping'
      have hping'' := hping'.1
      unfold divModPinGuard at hping''
      simp only [Bool.and_eq_true] at hping''
      have hpinF : (divModDeclPin c).hasFvar = false := by
        simpa using hping''.1.1.2
      rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hpinF)] at h
      obtain ⟨pinA, hann, h⟩ := atF_bind_ok h
      have hann' : annotateCore env F 0 _ = .ok pinA := hann
      show (annotateCore env F 0 _ >>= _) = _
      rw [hann']
      simp only [Bind.bind, Except.bind]
      have hvf : value'.hasFvar = false := hv'f _ _ _ hfind
      have hpinAW : WScoped 0 pinA :=
        annotateCore_WScoped F _ hann' (WScoped.of_not_hasFvar hpinF)
      rw [wfOpsM_isDefEq henv (wscopedB_of_not_hasFvar hvf)
        hpinAW.to_wscopedB] at h
      obtain ⟨b, hde, h⟩ := atF_bind_ok h
      have hde' : isDefEqCore env F 0 value' pinA = .ok b := hde
      show (isDefEqCore env F 0 value' pinA >>= _) = _
      rw [hde']
      simp only [Bind.bind, Except.bind]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact absurd h atF_throw
      | true =>
        simp only [↓reduceIte] at h ⊢
        obtain ⟨ok, hcert, h⟩ := atF_bind_ok h
        have hcert' := checkDivModCerts_wfimp henv hvf
          (divModCertStmts_wscopedB hc) hcert
        show (checkDivModCerts (fueledOps F) env c value' _ _ >>= _) = _
        rw [hcert']
        simp only [Bind.bind, Except.bind]
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact absurd h atF_throw
        | true =>
          simp only [↓reduceIte] at h ⊢
          exact h

end Setlec
