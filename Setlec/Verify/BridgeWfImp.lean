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

/-- `openPisAtFvars` puts the variable it creates for binder `j` at
index `i + j` — the positional companion of `openPisAtFvars_WScoped`,
needed wherever a check runs at each binder's *own* frame. -/
theorem openPisAtFvars_index :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) →
      ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ nm ty, x = Expr.fvar (i + j) nm ty := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h j x hx
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hx
    exact nomatch hx
  | succ n ih =>
    intro e i fvs body h j x hx
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
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          exact ⟨nm, dom, by rw [← hx, Nat.add_zero]⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨nm', ty', hx'⟩ := ih _ (i + 1) hrec j x hx
          exact ⟨nm', ty', by rw [hx']; congr 1; omega⟩
    | bvar _ | fvar _ _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
      exact nomatch h

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

/-- Per-index scoping of an instantiated telescope: the `i`-th domain
mentions only the binders before it, so it is scoped at `d + i` when the
spine entries climb one frame at a time.  This is what lets the
recursor's minor-premise pins run at each field's **own** frame. -/
theorem instPisAt_index_WScoped :
    ∀ (spine : List Expr) {d : Nat} {ty : Expr} {doms : List Expr}
      {res : Expr},
      Expr.instPisAt spine ty = some (doms, res) → WScoped d ty →
      (∀ (i : Nat) (a : Expr), spine[i]? = some a → WScoped (d + i + 1) a) →
      ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (d + i) x
  | [], d, ty, doms, res, h, hty, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro i x hx
    exact nomatch hx
  | a :: as, d, ty, doms, res, h, hty, hsp => by
    cases ty with
    | forallE nm dom body mb =>
      simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, hqe⟩ := h
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      have hty' : WScoped d dom ∧ WScoped d body := by
        simpa [WScoped] using hty
      have haw : WScoped (d + 1) a := by
        have h0 := hsp 0 a rfl
        rwa [Nat.add_zero] at h0
      intro i x hx
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx, Nat.add_zero]
        exact hty'.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have hrec := instPisAt_index_WScoped as (d := d + 1) hq
          (WScoped.instantiate1_gen haw 0 (hty'.2.mono (Nat.le_succ d)))
          (fun k b hb => by
            have h0 := hsp (k + 1) b (by simpa using hb)
            rw [show d + (k + 1) + 1 = d + 1 + k + 1 from by omega] at h0
            exact h0) i x hx
        rw [show d + (i + 1) = d + 1 + i from by omega]
        exact hrec
    | bvar _ | fvar _ _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ => exact nomatch h

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

/-- Invert a stored-constant lookup (kind-agnostic: the certificate
checks consume only the stored constant's type). -/
theorem findCV?_ok {env : Env} {n : Name} {cvt : ConstantVal}
    (h : env.findCV? n = some cvt) :
    ∃ ci, env.find? n = some ci ∧ ci.toConstantVal = cvt := by
  simp only [Env.findCV?, Option.map_eq_some_iff] at h
  exact h

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

/-- The pairwise inferred-type check, `wfOpsM` run to pure run. -/
theorem checkTypedList_wfimp {env : Env} (henv : EnvWF env)
    {depth : Nat} {F : Nat} :
    ∀ {as bs : List Expr},
      (∀ a ∈ as, WScoped depth a) → (∀ b ∈ bs, WScoped depth b) →
      ∀ {v : Unit},
      (checkTypedList wfOpsM env depth as bs).val F = .ok v →
      checkTypedList (fueledOps F) env depth as bs = .ok v
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, _, h => nomatch h
  | _ :: _, [], _, _, _, h => nomatch h
  | a :: as, b :: bs, ha, hb, v, h => by
    unfold checkTypedList at h ⊢
    rw [wfOpsM_inferType henv (ha a List.mem_cons_self).to_wscopedB] at h
    obtain ⟨ty, hty, h⟩ := atF_bind_ok h
    have hty' : inferTypeCore env F depth a = .ok ty := hty
    have htyW : WScoped depth ty :=
      inferTypeCore_WScoped henv F hty' (ha a List.mem_cons_self)
    show (inferTypeCore env F depth a >>= _) = _
    rw [hty']
    simp only [Bind.bind, Except.bind]
    rw [wfOpsM_isDefEq henv htyW.to_wscopedB
      (hb b List.mem_cons_self).to_wscopedB] at h
    obtain ⟨c, hc, h⟩ := atF_bind_ok h
    have hc' : isDefEqCore env F depth ty b = .ok c := hc
    show (isDefEqCore env F depth ty b >>= _) = _
    rw [hc']
    simp only [Bind.bind, Except.bind]
    cases c with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkTypedList_wfimp henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun y hy => hb y (List.mem_cons_of_mem _ hy)) h

/-- The annotate-idempotence check, `wfOpsM` run to pure run. -/
theorem checkAnnotList_wfimp {env : Env} (henv : EnvWF env)
    {depth : Nat} {F : Nat} :
    ∀ {as : List Expr},
      (∀ a ∈ as, WScoped depth a) →
      ∀ {v : Unit},
      (checkAnnotList wfOpsM env depth as).val F = .ok v →
      checkAnnotList (fueledOps F) env depth as = .ok v
  | [], _, _, h => h
  | a :: as, ha, v, h => by
    unfold checkAnnotList at h ⊢
    rw [wfOpsM_annotate henv (ha a List.mem_cons_self).to_wscopedB] at h
    obtain ⟨aA, hann, h⟩ := atF_bind_ok h
    have hann' : annotateCore env F depth a = .ok aA := hann
    show (annotateCore env F depth a >>= _) = _
    rw [hann']
    simp only [Bind.bind, Except.bind]
    by_cases hc : (aA == a) = true
    case neg =>
      rw [if_neg hc] at h
      exact absurd h atF_throw_bind
    case pos =>
      rw [if_pos hc] at h ⊢
      exact checkAnnotList_wfimp henv
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h

set_option maxHeartbeats 6400000 in
/-- The iota-theorem check, `wfOpsM` run to pure run.  The recursor
type, the constructor type and the annotated rule right-hand side are
closed; everything the check compares is scoped at the opened
telescope's depth. -/
theorem checkIotaThm_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr} {F : Nat}
    {v : Unit}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false)
    (h : (checkIotaThm wfOpsM env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val F = .ok v) :
    checkIotaThm (fueledOps F) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA = .ok v := by
  unfold checkIotaThm at h ⊢
  try dsimp only [] at h ⊢
  obtain ⟨cvt, hthm, h⟩ := atF_bind_ok h
  have hthm' := unwrapOr_atF_ok hthm
  show ((unwrapOr (env'.findCV?
    ((cvName.str "_model").str s!"iota_{j}")) _ : CheckM _) >>= _) = _
  rw [hthm']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- the stored constant's statement is closed (kind-agnostic)
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm'
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨q, hopen, h⟩ := atF_bind_ok h
  obtain ⟨fvs, tbody⟩ := q
  have hopen' := unwrapOr_atF_ok hopen
  show ((unwrapOr (openPisAtFvars (rP + cnF) cvt.type 0) _ :
    CheckM _) >>= _) = _
  rw [hopen']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- scoping of the opened telescope
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen' (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
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
      mI + 1
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP ==
      fvs.take rP) = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP)) = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  by_cases h8 : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => rw [if_neg h8] at h; exact absurd h atF_throw_bind
  rw [if_pos h8] at h ⊢
  obtain ⟨q2, hcinst, h⟩ := atF_bind_ok h
  obtain ⟨cdoms, cres⟩ := q2
  have hcinst' := unwrapOr_atF_ok hcinst
  show ((unwrapOr (Expr.instPisAt (fvs.take cnP ++
    fvs.drop rP) (cvj.type.renameConsts f)) _ :
    CheckM _) >>= _) = _
  rw [hcinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcargW : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
      WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact hfvsW a (List.mem_of_mem_take hax)
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
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
  show ((unwrapOr (Expr.instPisAt (fvs.take rP)
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
  show ((unwrapOr (openPisAtFvars rP tyA 0) _ :
    CheckM _) >>= _) = _
  rw [hopenP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP'
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
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP'
    (WScoped.of_not_hasFvar hctor)
    (fun a ha => hfvsPW a (List.mem_of_mem_take ha))
  obtain ⟨hcdomsPW, hcrestPW⟩ := hcinstPW
  obtain ⟨uP, hdP, h⟩ := atF_bind_ok h
  have hdP' := checkDefEqList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact (fvarTypeD_WScoped
        (hfvsPW x (List.mem_of_mem_take hx))).mono (by omega))
    (fun b hb => (hcdomsPW b hb).mono (by omega)) hdP
  show (checkDefEqList (fueledOps F) envSelf _ _ _ >>= _) = _
  rw [hdP']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q6, hopenX, h⟩ := atF_bind_ok h
  obtain ⟨xFvsP, crest2⟩ := q6
  have hopenX' := unwrapOr_atF_ok hopenX
  show ((unwrapOr (openPisAtFvars cnF crestP rP) _ :
    CheckM _) >>= _) = _
  rw [hopenX']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP
    hopenX' hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
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
  have hde' : isDefEqCore envSelf F (rP + cnF)
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

/-- A successful `nestedRuleShape` guards its stored parameter
instantiations: they are fvar-free. -/
theorem nestedRuleShape_pins {env' envSelf : Env} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP cnP j : Nat}
    {lvls : List Level} {pins : List Expr}
    (h : nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j =
      some (lvls, pins)) :
    ∀ p ∈ pins, p.hasFvar = false := by
  intro p hp
  simp only [nestedRuleShape] at h
  repeat split at h
  all_goals try (simp at h; done)
  rename_i hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hall := List.all_eq_true.mp hcond.2.2.2.1 p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  exact hall.1.1.1

set_option maxHeartbeats 6400000 in
/-- The nested-auxiliary iota-theorem check, `wfOpsM` run to pure run:
`checkIotaThm_wfimp` with the constructor's parameters and levels
fixed at the stored instantiations. -/
theorem checkIotaThmN_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {rhsA : Expr} {F : Nat}
    {v : RecRuleFire}
    (htyA : tyA.hasFvar = false) (hctor : cvj.type.hasFvar = false)
    (hrhsA : rhsA.hasFvar = false)
    (h : (checkIotaThmN wfOpsM env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val F = .ok v) :
    checkIotaThmN (fueledOps F) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA = .ok v := by
  unfold checkIotaThmN at h ⊢
  revert h
  cases hshape : nestedRuleShape env' envSelf cvName lps tyA mI rP
      cnP j with
  | none => intro h; exact h
  | some q =>
  obtain ⟨lvls, pins⟩ := q
  intro h
  try dsimp only [] at h ⊢
  have hpinsF : ∀ p ∈ pins, p.hasFvar = false :=
    nestedRuleShape_pins hshape
  obtain ⟨cvt, hthm, h⟩ := atF_bind_ok h
  have hthm' := unwrapOr_atF_ok hthm
  show ((unwrapOr (env'.findCV?
    ((cvName.str "_model").str s!"iota_{j}")) _ : CheckM _) >>= _) = _
  rw [hthm']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- the stored constant's statement is closed (kind-agnostic)
  have hcvtF : cvt.type.hasFvar = false := by
    obtain ⟨ci, hci, hcvt⟩ := findCV?_ok hthm'
    exact hcvt ▸ (henv' _ (find?_mem hci)).1
  by_cases h1 : cvt.levelParams = lps
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨q, hopen, h⟩ := atF_bind_ok h
  obtain ⟨fvs, tbody⟩ := q
  have hopen' := unwrapOr_atF_ok hopen
  show ((unwrapOr (openPisAtFvars (rP + cnF) cvt.type 0) _ :
    CheckM _) >>= _) = _
  rw [hopen']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  -- scoping of the opened telescope
  have hopenW := openPisAtFvars_WScoped (rP + cnF) cvt.type 0
    hopen' (WScoped.of_not_hasFvar hcvtF)
  rw [Nat.zero_add] at hopenW
  obtain ⟨hfvsW, htbodyW⟩ := hopenW
  have htargsW : ∀ x ∈ tbody.getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs htbodyW
  have hlhsW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 1 (.bvar 0)) := WScoped_getD' htargsW 1
  have hrhsSW : WScoped (rP + cnF)
      (tbody.getAppArgs.getD 2 (.bvar 0)) := WScoped_getD' htargsW 2
  have hlargsW : ∀ x ∈ (tbody.getAppArgs.getD 1 (.bvar 0)).getAppArgs,
      WScoped (rP + cnF) x := Expr.WScoped.getAppArgs hlhsW
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
      mI + 1
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw_bind
  rw [if_pos h5] at h ⊢
  by_cases h6 : ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.take rP ==
      fvs.take rP) = true
  case neg => rw [if_neg h6] at h; exact absurd h atF_throw_bind
  rw [if_pos h6] at h ⊢
  by_cases h7 : Expr.eqUpToNames ((tbody.getAppArgs.getD 1
      (.bvar 0)).getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f r.ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)) = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  obtain ⟨q8, hstrip8, h⟩ := atF_bind_ok h
  obtain ⟨bs8, cbody8⟩ := q8
  have hstrip8' := unwrapOr_atF_ok hstrip8
  show ((unwrapOr (cvj.type.stripPis (cnP + cnF)) _ :
    CheckM _) >>= _) = _
  rw [hstrip8']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  obtain ⟨Dc, usc, hfnC⟩ : ∃ Dc usc,
      cbody8.getAppFn = Expr.const Dc usc := by
    revert h
    cases hfn0 : cbody8.getAppFn <;> intro h
    case const => exact ⟨_, _, rfl⟩
    all_goals
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
  rw [hfnC] at h ⊢
  rw [if_pos rfl] at h ⊢
  try dsimp only [] at h ⊢
  obtain ⟨q2, hcinst, h⟩ := atF_bind_ok h
  obtain ⟨cdoms, cres⟩ := q2
  have hcinst' := unwrapOr_atF_ok hcinst
  show ((unwrapOr (Expr.instPisAt
    (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
      (p.renameConsts f)) ++ fvs.drop rP)
    ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f)) _ : CheckM _) >>= _) = _
  rw [hcinst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcargW : ∀ a ∈ pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)) ++
      fvs.drop rP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hax
      exact instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hpinsF x hx))
        (fun a' ha' => hfvsW a' (List.mem_of_mem_take ha'))
    · exact hfvsW a (List.mem_of_mem_drop hax)
  have hcinstW := instPisAt_WScoped _ _ hcinst'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_renameConsts, hasFvar_instantiateLevelParams]
      exact hctor)) hcargW
  obtain ⟨hcdomsW, hcresW⟩ := hcinstW
  by_cases h9 : cres.getAppArgs.length = cnP + (mI - rP)
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
  show ((unwrapOr (Expr.instPisAt (fvs.take rP)
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
  show ((unwrapOr (openPisAtFvars rP tyA 0) _ :
    CheckM _) >>= _) = _
  rw [hopenP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenPW := openPisAtFvars_WScoped rP tyA 0 hopenP'
    (WScoped.of_not_hasFvar htyA)
  rw [Nat.zero_add] at hopenPW
  obtain ⟨hfvsPW, -⟩ := hopenPW
  obtain ⟨uA, hdA, h⟩ := atF_bind_ok h
  have hdA' := checkAnnotList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact (instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha'))).mono
        (by omega)) hdA
  show (checkAnnotList (fueledOps F) envSelf _ _ >>= _) = _
  rw [hdA']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q5, hcinstP, h⟩ := atF_bind_ok h
  obtain ⟨cdomsP, crestP⟩ := q5
  have hcinstP' := unwrapOr_atF_ok hcinstP
  show ((unwrapOr (Expr.instPisAt
    (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
    (cvj.type.instantiateLevelParams cvj.levelParams lvls)) _ :
    CheckM _) >>= _) = _
  rw [hcinstP']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hcinstPW := instPisAt_WScoped (d := rP) _ _ hcinstP'
    (WScoped.of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]
      exact hctor))
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha')))
  obtain ⟨hcdomsPW, hcrestPW⟩ := hcinstPW
  obtain ⟨uP, hdP, h⟩ := atF_bind_ok h
  have hdP' := checkTypedList_wfimp henvSelf
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact (instSpine_WScoped (rP - 1)
        (WScoped.of_not_hasFvar (hpinsF x hx))
        (fun a' ha' => hfvsPW a' (List.mem_of_mem_take ha'))).mono
        (by omega))
    (fun b hb => (hcdomsPW b hb).mono (by omega)) hdP
  show (checkTypedList (fueledOps F) envSelf _ _ _ >>= _) = _
  rw [hdP']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q6, hopenX, h⟩ := atF_bind_ok h
  obtain ⟨xFvsP, crest2⟩ := q6
  have hopenX' := unwrapOr_atF_ok hopenX
  show ((unwrapOr (openPisAtFvars cnF crestP rP) _ :
    CheckM _) >>= _) = _
  rw [hopenX']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  have hopenXW := openPisAtFvars_WScoped cnF crestP rP
    hopenX' hcrestPW
  obtain ⟨hxFvsPW, -⟩ := hopenXW
  have hfvsPW' : ∀ a ∈ fvsP ++ xFvsP, WScoped (rP + cnF) a := by
    intro a hax
    rcases List.mem_append.mp hax with hax | hax
    · exact WScoped.mono (by omega) (hfvsPW a hax)
    · exact hxFvsPW a hax
  by_cases harX : (crest2.getAppArgs.length == cnP + (mI - rP)) = true
  case neg => rw [if_neg harX] at h; exact absurd h atF_throw_bind
  rw [if_pos harX] at h ⊢
  try dsimp only [] at h ⊢
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
  have hde' : isDefEqCore envSelf F (rP + cnF)
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
    exact h

theorem checkIotaRule_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP j : Nat} {r : RecRule}
    {F : Nat} {v : RecRule} (htyA : tyA.hasFvar = false)
    (h : (checkIotaRule wfOpsM env' envSelf f cvName lps tyA
      mI rP j r).val F = .ok v) :
    checkIotaRule (fueledOps F) env' envSelf f cvName lps tyA
      mI rP j r = .ok v := by
  unfold checkIotaRule at h ⊢
  dsimp only [] at h ⊢
  revert h
  match hf : env'.find? r.ctor with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
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
  by_cases h7 : (rhsA.stripLams (rP + cnF)).isSome = true
  case neg => rw [if_neg h7] at h; exact absurd h atF_throw_bind
  rw [if_pos h7] at h ⊢
  rw [wfOpsM_inferType henvSelf hwrhsA.to_wscopedB] at h
  obtain ⟨rhsTy, hity, h⟩ := atF_bind_ok h
  have hity' : inferTypeCore envSelf F 0 rhsA = .ok rhsTy := hity
  show (inferTypeCore envSelf F 0 rhsA >>= _) = _
  rw [hity']
  simp only [Bind.bind, Except.bind]
  by_cases h8 : Expr.recRulePlain tyA mI rP cnP = true
  case neg =>
    rw [if_neg h8] at h ⊢
    obtain ⟨fire, hthmN, h⟩ := atF_bind_ok h
    have hthmN' := checkIotaThmN_wfimp henv' henvSelf htyA
      (show cvj.type.hasFvar = false from (henv' _ (find?_mem hf)).1)
      hrhsAF hthmN
    show (checkIotaThmN (fueledOps F) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA >>= _) = _
    rw [hthmN']
    simp only [Bind.bind, Except.bind]
    exact h
  rw [if_pos h8] at h ⊢
  obtain ⟨u, hthm, h⟩ := atF_bind_ok h
  have hthm' := checkIotaThm_wfimp henv' henvSelf htyA
    (show cvj.type.hasFvar = false from (henv' _ (find?_mem hf)).1)
    hrhsAF hthm
  show (checkIotaThm (fueledOps F) env' envSelf f cvName lps tyA
    mI rP j r cvj cnP cnF rhsA >>= _) = _
  rw [hthm']
  simp only [Bind.bind, Except.bind]
  exact h

theorem checkIotaRules_wfimp {env' envSelf : Env} (henv' : EnvWF env')
    (henvSelf : EnvWF envSelf) {f : Name → Name} {cvName : Name}
    {lps : List Name} {tyA : Expr} {mI rP : Nat} {F : Nat}
    (htyA : tyA.hasFvar = false) :
    ∀ {j : Nat} {rules rules' : List RecRule},
      (checkIotaRules wfOpsM env' envSelf f cvName lps tyA
        mI rP j rules).val F = .ok rules' →
      checkIotaRules (fueledOps F) env' envSelf f cvName lps tyA
        mI rP j rules = .ok rules'
  | _, [], rules', h => h
  | j, r :: rest, rules', h => by
    unfold checkIotaRules at h ⊢
    obtain ⟨r', hr, h⟩ := atF_bind_ok h
    have hr' := checkIotaRule_wfimp henv' henvSelf htyA hr
    show (checkIotaRule (fueledOps F) env' envSelf f cvName lps tyA
      mI rP j r >>= _) = _
    rw [hr']
    simp only [Bind.bind, Except.bind]
    obtain ⟨rest', hrest, h⟩ := atF_bind_ok h
    have hrest' := checkIotaRules_wfimp henv' henvSelf htyA hrest
    show (checkIotaRules (fueledOps F) env' envSelf f cvName lps tyA
      mI rP (j + 1) rest >>= _) = _
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
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
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
    {pty : Expr} {cvj : ConstantVal} {lps : List Name}
    {nP nF i F : Nat} {v : Expr}
    (hptyf : pty.hasFvar = false)
    (_hptyb : pty.looseBVarsBounded 0 = true)
    (hCf : cvj.type.hasFvar = false)
    (_hCb : cvj.type.looseBVarsBounded 0 = true)
    (h : (checkProjRule wfOpsM env' pty cvj lps nP nF i).val F = .ok v) :
    checkProjRule (fueledOps F) env' pty cvj lps nP nF i = .ok v := by
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
  -- the frame walks and pins
  revert h
  match hopenP : openPisAtFvars nP pty 0 with
  | none => intro h; exact nomatch h
  | some pr₃ => ?_
  obtain ⟨fvsP, rest0⟩ := pr₃
  intro h
  try dsimp only [] at h ⊢
  revert h
  match hcinstP : Expr.instPisAt fvsP cvj.type with
  | none => intro h; exact nomatch h
  | some pr₄ => ?_
  obtain ⟨cdomsP, crestP⟩ := pr₄
  intro h
  try dsimp only [] at h ⊢
  obtain ⟨hfvsW0, -⟩ := openPisAtFvars_WScoped nP pty 0 hopenP
    (WScoped.of_not_hasFvar hptyf)
  have hfvsW : ∀ x ∈ fvsP, WScoped nP x := by
    intro x hx
    have h0 := hfvsW0 x hx
    rwa [Nat.zero_add] at h0
  have hannW : ∀ a ∈ fvsP.map Expr.fvarTypeD, WScoped (nP + nF) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hw := hfvsW x hx
    cases x with
    | fvar idx nm ty =>
      simp only [WScoped] at hw
      exact hw.2.mono (by omega)
    | bvar _ => exact hw.mono (by omega)
    | sort _ => exact hw.mono (by omega)
    | const _ _ => exact hw.mono (by omega)
    | app _ _ => exact hw.mono (by omega)
    | lam _ _ _ _ => exact hw.mono (by omega)
    | forallE _ _ _ _ => exact hw.mono (by omega)
    | letE _ _ _ _ => exact hw.mono (by omega)
    | lit _ => exact hw.mono (by omega)
    | proj _ _ _ => exact hw.mono (by omega)
  obtain ⟨hcdW, hcrW⟩ := instPisAt_WScoped (d := nP) fvsP cvj.type
    hcinstP (WScoped.of_not_hasFvar hCf) hfvsW
  obtain ⟨u₁, hde1, h⟩ := atF_bind_ok h
  have hde1' := checkDefEqList_wfimp henv' hannW
    (fun b hb => (hcdW b hb).mono (by omega)) hde1
  show (checkDefEqList (fueledOps F) env' (nP + nF)
    (fvsP.map Expr.fvarTypeD) cdomsP >>= _) = _
  rw [hde1']
  simp only [Bind.bind, Except.bind]
  revert h
  match hopenX : openPisAtFvars nF crestP nP with
  | none => intro h; exact nomatch h
  | some pr₅ => ?_
  obtain ⟨xFvs, crest2X⟩ := pr₅
  intro h
  try dsimp only [] at h ⊢
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvs) rhsA with
  | none => intro h; exact nomatch h
  | some pr₆ => ?_
  obtain ⟨ldoms, lrestL⟩ := pr₆
  intro h
  try dsimp only [] at h ⊢
  have hrhsAf : rhsA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h2
    exact h2.2
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped nF crestP nP hopenX hcrW
  have hspineW : ∀ a ∈ fvsP ++ xFvs, WScoped (nP + nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsW a ha).mono (by omega)
    · exact hxW a ha
  have hannW2 : ∀ a ∈ (fvsP ++ xFvs).map Expr.fvarTypeD,
      WScoped (nP + nF) a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hw := hspineW x hx
    cases x with
    | fvar idx nm ty =>
      simp only [WScoped] at hw
      exact hw.2.mono (by omega)
    | bvar _ => exact hw.mono (by omega)
    | sort _ => exact hw.mono (by omega)
    | const _ _ => exact hw.mono (by omega)
    | app _ _ => exact hw.mono (by omega)
    | lam _ _ _ _ => exact hw.mono (by omega)
    | forallE _ _ _ _ => exact hw.mono (by omega)
    | letE _ _ _ _ => exact hw.mono (by omega)
    | lit _ => exact hw.mono (by omega)
    | proj _ _ _ => exact hw.mono (by omega)
  obtain ⟨hldW, -⟩ := instLamsAt_WScoped (fvsP ++ xFvs) rhsA hlinst
    (WScoped.of_not_hasFvar hrhsAf) hspineW
  obtain ⟨u₂, hde2, h⟩ := atF_bind_ok h
  have hde2' := checkDefEqList_wfimp henv' hannW2
    (fun b hb => hldW b hb) hde2
  show (checkDefEqList (fueledOps F) env' (nP + nF)
    ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms >>= _) = _
  rw [hde2']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_inferType henv' (wscopedB_of_not_hasFvar hrhsAf)] at h
  obtain ⟨rhsTy, hity, h⟩ := atF_bind_ok h
  have hity' : inferTypeCore env' F 0 rhsA = .ok rhsTy := hity
  show (inferTypeCore env' F 0 rhsA >>= _) = _
  rw [hity']
  simp only [Bind.bind, Except.bind]
  exact h

/-- The stored constructor behind a successful projection lookup. -/
theorem checkProjLookups_ctor {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {cvj mcv : ConstantVal}
    (h : (checkProjLookups env' T ctorName lps nP nF i :
      CheckM (ConstantVal × ConstantVal)) = .ok (cvj, mcv)) :
    ∃ cnP cnF, env'.find? ctorName = some (.ctorInfo cvj cnP cnF) := by
  unfold checkProjLookups at h
  revert h
  match hf : env'.find? ctorName with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj' cnP cnF) => ?_
  intro h
  try dsimp only at h
  split at h
  next harm =>
    refine ⟨cnP, cnF, ?_⟩
    -- the remaining guards only gate success; the head is fixed
    revert h
    match env'.find? (projModelName T i) with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) => intro h; exact nomatch h
    | some (.projInfo _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.defnInfo mcv' _ _) => ?_
    intro h
    try dsimp only at h
    split at h
    next =>
      split at h
      next =>
        split at h
        next =>
          split at h
          next =>
            simp only [pure, Except.pure, Except.ok.injEq,
              Prod.mk.injEq] at h
            rw [h.1]
          next => exact nomatch h
        next => exact nomatch h
      next => exact nomatch h
    next => exact nomatch h
  next => exact nomatch h

/-- Well-formedness of a successfully checked projection type. -/
theorem checkProjTy_wf {env' : Env} {T ctorName : Name}
    {lps : List Name} {mty pty : Expr} {nP nF : Nat}
    (h : (checkProjTy env' T ctorName lps mty nP nF : CheckM Expr) =
      .ok pty) :
    pty.hasFvar = false ∧ pty.looseBVarsBounded 0 = true := by
  unfold checkProjTy at h
  try dsimp only at h
  split at h
  next =>
    split at h
    next =>
      split at h
      next hwf =>
        split at h
        next =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true] at hwf
          rw [← h]
          exact ⟨hwf.1.2, hwf.1.1⟩
        next => exact nomatch h
      next => exact nomatch h
    next => exact nomatch h
  next => exact nomatch h

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
  obtain ⟨u0, hshape, h⟩ := atF_bind_ok h
  rw [checkProjShape_datF] at hshape
  show ((checkProjShape pty cvj.type nP nF : CheckM Unit) >>= _) = _
  rw [hshape]
  simp only [Bind.bind, Except.bind]
  dsimp only [] at h ⊢
  by_cases h1 : i < nF
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨rhsA, hrule, h⟩ := atF_bind_ok h
  obtain ⟨cnP0, cnF0, hctor⟩ := checkProjLookups_ctor hlk
  obtain ⟨hptyf, hptyb⟩ := checkProjTy_wf hty
  have hrule' := checkProjRule_wfimp henv' hptyf hptyb
    (show cvj.type.hasFvar = false from (henv' _ (find?_mem hctor)).1)
    (show cvj.type.looseBVarsBounded 0 = true from
      (henv' _ (find?_mem hctor)).2.2.2.1)
    hrule
  show (checkProjRule (fueledOps F) env' pty cvj lps nP nF i >>= _) = _
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
    simp only [FueledM.atF_pure] at h
    exact h ▸ rfl

/-- The template-install step, `wfOpsM` run to pure run (the step is
ops-free, so the runs coincide). -/
theorem installProjTemplateStep_wfimp {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} {e e' : Env} {i F : Nat}
    (h : (installProjTemplateStep T ctorName lps nP nF e i :
      FueledM _).val F = .ok e') :
    (installProjTemplateStep T ctorName lps nP nF e i : CheckM _)
      = .ok e' := by
  rw [installProjTemplateStep_datF] at h
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
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

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
    | recInfo cv' mI rP rules => intro h; exact absurd h atF_throw
    | projInfo _ => intro h; exact absurd h atF_throw
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

/-- The compiler-trust install gate, `wfOpsM` run to pure run (the
raw witness value's scoping comes from the preceding opaque check). -/
theorem checkReducePin_wfimp {env env2 : Env} (henv : EnvWF env)
    {F : Nat} {c : Name} {value : Expr}
    (hvf : value.hasFvar = false)
    {u : Unit}
    (h : (checkReducePin wfOpsM env env2 c value).val F = .ok u) :
    checkReducePin (fueledOps F) env env2 c value = .ok u := by
  unfold checkReducePin at h ⊢
  by_cases h1 : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg =>
    rw [if_neg h1] at h
    exact absurd h atF_throw
  rw [if_pos h1] at h ⊢
  by_cases h2 : reducePinGuard env c = true
  case neg =>
    rw [if_neg h2] at h
    exact absurd h atF_throw
  rw [if_pos h2] at h ⊢
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hvf)] at h
  obtain ⟨valA, hannv, h⟩ := atF_bind_ok h
  have hannv' : annotateCore env F 0 value = .ok valA := hannv
  show (annotateCore env F 0 value >>= _) = _
  rw [hannv']
  simp only [Bind.bind, Except.bind]
  have h2' := h2
  unfold reducePinGuard at h2'
  simp only [Bool.and_eq_true] at h2'
  have hpinF : (reduceDeclPin c).hasFvar = false := by
    simpa using h2'.1.1.2
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hpinF)] at h
  obtain ⟨pinA, hannp, h⟩ := atF_bind_ok h
  have hannp' : annotateCore env F 0 (reduceDeclPin c) = .ok pinA := hannp
  show (annotateCore env F 0 (reduceDeclPin c) >>= _) = _
  rw [hannp']
  simp only [Bind.bind, Except.bind]
  have hvalAW : WScoped 0 valA :=
    annotateCore_WScoped F value hannv' (WScoped.of_not_hasFvar hvf)
  have hpinAW : WScoped 0 pinA :=
    annotateCore_WScoped F _ hannp' (WScoped.of_not_hasFvar hpinF)
  rw [wfOpsM_isDefEq henv hvalAW.to_wscopedB hpinAW.to_wscopedB] at h
  obtain ⟨b, hde, h⟩ := atF_bind_ok h
  have hde' : isDefEqCore env F 0 valA pinA = .ok b := hde
  show (isDefEqCore env F 0 valA pinA >>= _) = _
  rw [hde']
  simp only [Bind.bind, Except.bind]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact absurd h atF_throw
  | true =>
    simp only [↓reduceIte] at h ⊢
    have hxW : WScoped 1 (reduceCertVar c) := by
      unfold reduceCertVar
      simp only [WScoped]
      refine ⟨Nat.zero_lt_one, ?_⟩
      unfold reduceElemTy
      split <;> simp only [WScoped]
    have happW : WScoped 1 (Expr.app valA (reduceCertVar c)) := by
      simp only [WScoped]
      exact ⟨WScoped.mono (Nat.zero_le 1) hvalAW, hxW⟩
    rw [wfOpsM_isDefEq henv happW.to_wscopedB hxW.to_wscopedB] at h
    obtain ⟨b2, hde2, h⟩ := atF_bind_ok h
    have hde2' : isDefEqCore env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) = .ok b2 := hde2
    show (isDefEqCore env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) >>= _) = _
    rw [hde2']
    simp only [Bind.bind, Except.bind]
    cases b2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h atF_throw
    | true =>
      simp only [↓reduceIte] at h ⊢
      exact h

/-! ## The direct simple-structure path (task #82)

Run-level implications for the checks `checkDirectStruct` composes.
The fabricated terms whose scoping has to be established here are the
openings of the recursor and constructor telescopes (at the pin frame
`nP + 2 + nF`), the generated projection type and the rule's
right-hand side — the last two are checked closed by the checker's own
`!hasFvar && looseBVarsBounded 0` guards before they are annotated. -/

/-- The per-frame parameter-domain pins, `wfOpsM` run to pure run: each
domain is scoped at its own frame. -/
theorem checkDirectDomsAt_wfimp {env : Env} (henv : EnvWF env)
    {F off : Nat} {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {v : Unit},
      (checkDirectDomsAt wfOpsM env off fvs doms j).val F = .ok v →
      checkDirectDomsAt (fueledOps F) env off fvs doms j = .ok v
  | 0, _, h => h
  | j + 1, v, h => by
    unfold checkDirectDomsAt at h ⊢
    obtain ⟨a, ha, h⟩ := atF_bind_ok h
    have ha' := unwrapOr_atF_ok ha
    show ((unwrapOr fvs[j]? _ : CheckM _) >>= _) = _
    rw [ha']
    simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
    obtain ⟨b, hb, h⟩ := atF_bind_ok h
    have hb' := unwrapOr_atF_ok hb
    show ((unwrapOr doms[j]? _ : CheckM _) >>= _) = _
    rw [hb']
    simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
    rw [wfOpsM_isDefEq henv (hc j a ha').to_wscopedB
      (ht j b hb').to_wscopedB] at h
    obtain ⟨c, hc2, h⟩ := atF_bind_ok h
    have hc2' : isDefEqCore env F (off + j) (Expr.fvarTypeD a) b = .ok c := hc2
    show (isDefEqCore env F (off + j) (Expr.fvarTypeD a) b >>= _) = _
    rw [hc2']
    simp only [Bind.bind, Except.bind]
    cases c with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkDirectDomsAt_wfimp henv hc ht h

/-- The per-field universe bound, `wfOpsM` run to pure run. -/
theorem checkDirectFieldUniv_wfimp {env : Env} (henv : EnvWF env)
    {s : Level} {nP F : Nat} {fvs : List Expr}
    (hfvs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x)) :
    ∀ {j : Nat} {v : Unit},
      (checkDirectFieldUniv wfOpsM env s nP fvs j).val F = .ok v →
      checkDirectFieldUniv (fueledOps F) env s nP fvs j = .ok v
  | 0, _, h => h
  | j + 1, v, h => by
    unfold checkDirectFieldUniv at h ⊢
    obtain ⟨fv, hfv, h⟩ := atF_bind_ok h
    have hfv' := unwrapOr_atF_ok hfv
    show ((unwrapOr fvs[j]? _ : CheckM _) >>= _) = _
    rw [hfv']
    simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
    have htyW : WScoped (nP + j) fv.fvarTypeD := hfvs j fv hfv'
    rw [wfOpsM_inferType henv htyW.to_wscopedB] at h
    obtain ⟨ty, hty, h⟩ := atF_bind_ok h
    have hty' : inferTypeCore env F (nP + j) fv.fvarTypeD = .ok ty := hty
    show (inferTypeCore env F (nP + j) fv.fvarTypeD >>= _) = _
    rw [hty']
    simp only [Bind.bind, Except.bind]
    have htyW' : WScoped (nP + j) ty := inferTypeCore_WScoped henv F hty' htyW
    rw [wfOpsM_ensureSort henv htyW'.to_wscopedB] at h
    obtain ⟨u, hu, h⟩ := atF_bind_ok h
    have hu' : ensureSortCore env F (nP + j) ty = .ok u := hu
    show (ensureSortCore env F (nP + j) ty >>= _) = _
    rw [hu']
    simp only [Bind.bind, Except.bind]
    obtain ⟨b, hb, h⟩ := atF_bind_ok h
    rw [liftFueled_atF] at hb
    show ((liftFueled "level comparison" (Level.leq u s) : CheckM Bool)
      >>= _) = _
    rw [hb]
    simp only [Bind.bind, Except.bind]
    cases b with
    | false =>
      rw [if_neg (by simp)] at h
      exact absurd h atF_throw_bind
    | true =>
      rw [if_pos rfl] at h ⊢
      exact checkDirectFieldUniv_wfimp henv hfvs h


/-- Close a goal whose hypothesis is a pure run that begins with a
`throw`: such a run never succeeds. -/
macro "throwM_elim" h:ident : tactic =>
  `(tactic| simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, reduceCtorEq] at $h:ident)

/-- The type-slot `ConstWF` facts of a successfully checked constant:
level parameters and constant resolution are checked outright, and the
annotated type inherits closedness and fvar-freedom from the raw
checks through `annotate`. -/
theorem checkConstantVal_typeWF {env : Env} {cv cvA : ConstantVal}
    {F : Nat} (h : checkConstantVal (fueledOps F) env cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  unfold checkConstantVal at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; throwM_elim h
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; throwM_elim h
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; throwM_elim h
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; throwM_elim h
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; throwM_elim h
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h; throwM_elim h
  rw [if_neg h6] at h
  revert h
  match hann : (fueledOps F).annotate env 0 cv.type with
  | .error e => intro h; exact nomatch h
  | .ok type => ?_
  intro h
  simp only [Bind.bind, Except.bind] at h
  have hann' : annotateCore env F 0 cv.type = .ok type := hann
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg => rw [if_neg h7] at h; exact nomatch h
  rw [if_pos h7] at h
  by_cases h8 : Expr.constsResolve env type = true
  case neg => rw [if_neg h8] at h; exact nomatch h
  rw [if_pos h8] at h
  revert h
  match hity : (fueledOps F).inferType env 0 type with
  | .error e => intro h; exact nomatch h
  | .ok stype => ?_
  intro h
  simp only [Bind.bind, Except.bind] at h
  revert h
  match hsty : (fueledOps F).ensureSort env 0 stype with
  | .error e => intro h; exact nomatch h
  | .ok u => ?_
  intro h
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  refine ⟨?_, h7, h8, annotateCore_looseBVars F cv.type hann' h5⟩
  exact not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F cv.type hann'
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ |>.mp h6))).fvarsBelow)

/-- Peeling a `∀`-telescope (without instantiating) keeps every binder
domain and the body scoped at the same frame. -/
theorem stripPis_WScoped {d : Nat} :
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr}, Expr.stripPis k e = some (bs, body) → WScoped d e →
      (∀ b ∈ bs, WScoped d b.2.1) ∧ WScoped d body
  | 0, e, bs, body, h, hw => by
    simp only [Expr.stripPis, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hw⟩
  | k + 1, e, bs, body, h, hw => by
    match e, h with
    | .forallE n ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (n, ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [WScoped] at hw
      obtain ⟨hrest, hbody⟩ := stripPis_WScoped k hstrip hw.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hw.1
      · exact hrest b hb

/-- The head domain of a peeled telescope is scoped. -/
theorem stripPis_head_WScoped {d k : Nat} {e : Expr}
    {bs : List (Name × Expr × BinderMeta)} {body dom : Expr}
    (hst : Expr.stripPis k e = some (bs, body)) (hw : WScoped d e)
    (hd : (bs[0]?).map (·.2.1) = some dom) : WScoped d dom := by
  have hb : ∃ b, bs[0]? = some b ∧ b.2.1 = dom := by
    revert hd
    cases hbs : bs[0]? with
    | none => intro hd; exact nomatch hd
    | some b => intro hd; exact ⟨b, rfl, Option.some.inj hd⟩
  obtain ⟨b, hb0, rfl⟩ := hb
  exact (stripPis_WScoped k hst hw).1 b (List.mem_of_getElem? hb0)

/-- Stage 1 of the direct install, `wfOpsM` run to pure run. -/
theorem checkDirectInd_wfimp {env : Env} (henv : EnvWF env)
    {p : DirectParts} {F : Nat} {v : Env × ConstantVal}
    (h : (checkDirectInd wfOpsM env p).val F = .ok v) :
    checkDirectInd (fueledOps F) env p = .ok v := by
  unfold checkDirectInd at h ⊢
  obtain ⟨cvTa, hcv, h⟩ := atF_bind_ok h
  have hcv' := checkConstantVal_wfimp henv hcv
  show (checkConstantVal (fueledOps F) env p.cvT >>= _) = _
  rw [hcv']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q, hst, h⟩ := atF_bind_ok h
  obtain ⟨tbs, tbody⟩ := q
  dsimp only [] at h
  have hst' := unwrapOr_atF_ok hst
  show ((unwrapOr (cvTa.type.stripPis p.nP) _ : CheckM _) >>= _) = _
  rw [hst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  by_cases h1 : (tbody == Expr.sort p.resSort) = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  exact h

/-- Stage 2 of the direct install, `wfOpsM` run to pure run.  The
opened constructor telescope is scoped at its own frame because the
annotated constructor type is closed. -/
theorem checkDirectCtor_wfimp {env₀ env : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa : ConstantVal} {F : Nat} {v : Env × ConstantVal}
    (hTf : cvTa.type.hasFvar = false)
    (h : (checkDirectCtor wfOpsM env₀ env p cvTa).val F = .ok v) :
    checkDirectCtor (fueledOps F) env₀ env p cvTa = .ok v := by
  unfold checkDirectCtor at h ⊢
  obtain ⟨cvCa, hcv, h⟩ := atF_bind_ok h
  have hcv' := checkConstantVal_wfimp henv hcv
  obtain ⟨hCf, -, -, -⟩ := checkConstantVal_typeWF hcv'
  show (checkConstantVal (fueledOps F) env p.cvC >>= _) = _
  rw [hcv']
  simp only [Bind.bind, Except.bind]
  obtain ⟨q, hst, h⟩ := atF_bind_ok h
  obtain ⟨cbs, cbody⟩ := q
  dsimp only [] at h
  have hst' := unwrapOr_atF_ok hst
  show ((unwrapOr (cvCa.type.stripPis (p.nP + p.nF)) _ : CheckM _) >>= _) = _
  rw [hst']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  by_cases h1 : (cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF)
      = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  -- the block's shared opening: the constructor's parameter telescope
  obtain ⟨q2, hop, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, crest⟩ := q2
  dsimp only [] at h
  have hop' := unwrapOr_atF_ok hop
  show ((unwrapOr (openPisAtFvars p.nP cvCa.type 0) _ : CheckM _) >>= _) = _
  rw [hop']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hfvsW0, hcrW0⟩ := openPisAtFvars_WScoped p.nP cvCa.type 0 hop'
    (WScoped.of_not_hasFvar hCf)
  have hfvsW : ∀ x ∈ fvsP, WScoped p.nP x := by
    intro x hx
    have h0 := hfvsW0 x hx
    rwa [Nat.zero_add] at h0
  have hcrW : WScoped p.nP crest := by rwa [Nat.zero_add] at hcrW0
  -- the type former's telescope, opened at its own variables
  obtain ⟨q3, hci, h⟩ := atF_bind_ok h
  obtain ⟨tfvs, trest⟩ := q3
  dsimp only [] at h
  have hci' := unwrapOr_atF_ok hci
  show ((unwrapOr (openPisAtFvars p.nP cvTa.type 0) _ : CheckM _) >>= _) = _
  rw [hci']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  -- the parameter domains, definitionally, each at its own frame
  obtain ⟨u1, hd1, h⟩ := atF_bind_ok h
  obtain ⟨htfvsW0, -⟩ := openPisAtFvars_WScoped p.nP cvTa.type 0 hci'
    (WScoped.of_not_hasFvar hTf)
  have hd1' := checkDirectDomsAt_wfimp (off := 0) henv
    (fun i x hx => by
      obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index p.nP cvCa.type 0 hop' i x hx
      have hw := hfvsW0 _ (List.mem_of_getElem? hx)
      simp only [WScoped] at hw
      exact hw.2)
    (fun i x hx => by
      rw [List.getElem?_map] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
      obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index p.nP cvTa.type 0 hci' i y hy
      have hw := htfvsW0 _ (List.mem_of_getElem? hy)
      simp only [WScoped] at hw
      exact hw.2)
    hd1
  show (checkDirectDomsAt (fueledOps F) env 0 fvsP
    (tfvs.map Expr.fvarTypeD) p.nP >>= _) = _
  rw [hd1']
  simp only [Bind.bind, Except.bind]
  -- the field telescope
  obtain ⟨q4, hox, h⟩ := atF_bind_ok h
  obtain ⟨xFvs, cresid⟩ := q4
  dsimp only [] at h
  have hox' := unwrapOr_atF_ok hox
  show ((unwrapOr (openPisAtFvars p.nF crest p.nP) _ : CheckM _) >>= _) = _
  rw [hox']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF crest p.nP hox' hcrW
  have hxPos : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      WScoped (p.nP + i) (Expr.fvarTypeD x) := by
    intro i x hx
    obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index p.nF crest p.nP hox' i x hx
    have hw := hxW _ (List.mem_of_getElem? hx)
    simp only [WScoped] at hw
    exact hw.2
  by_cases h2 : (cresid == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) fvsP) = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  obtain ⟨u0, hfu, h⟩ := atF_bind_ok h
  have hfu' := checkDirectFieldUniv_wfimp henv hxPos hfu
  show (checkDirectFieldUniv (fueledOps F) env p.resSort p.nP xFvs p.nF
    >>= _) = _
  rw [hfu']
  simp only [Bind.bind, Except.bind]
  exact h

/-- Stage 3 of the direct install, `wfOpsM` run to pure run.  The
annotated recursor and constructor types are closed, so the one shared
opening of the recursor telescope — and everything read off it: the
motive's domain, the minor premise's own opening, the instantiated
constructor domains and the major's domain — is scoped at the frame the
definitional pins run at (`nP + 2 + nF`). -/
theorem checkDirectRecTy_wfimp {env : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {F : Nat} {v : Unit}
    (hCf : cvCa.type.hasFvar = false) (hRf : cvRa.type.hasFvar = false)
    (h : (checkDirectRecTy wfOpsM env p cvTa cvCa cvRa).val F = .ok v) :
    checkDirectRecTy (fueledOps F) env p cvTa cvCa cvRa = .ok v := by
  unfold checkDirectRecTy at h ⊢
  by_cases h0 : directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim
      p.nP p.nF cvTa.type cvCa.type cvRa.type = true
  case neg => rw [if_neg h0] at h; exact absurd h atF_throw_bind
  rw [if_pos h0] at h ⊢
  -- the shared opening of the recursor telescope
  obtain ⟨q, hop, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, rest⟩ := q
  dsimp only [] at h
  have hop' := unwrapOr_atF_ok hop
  show ((unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0) _ :
    CheckM _) >>= _) = _
  rw [hop']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  have hopW := openPisAtFvars_WScoped (p.nP + 2) cvRa.type 0 hop'
    (WScoped.of_not_hasFvar hRf)
  rw [Nat.zero_add] at hopW
  obtain ⟨hfvsW0, hrestW0⟩ := hopW
  have hfvsW : ∀ x ∈ fvsP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => (hfvsW0 x hx).mono (by omega)
  have hpsW : ∀ x ∈ fvsP.take p.nP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => hfvsW x (List.mem_of_mem_take hx)
  have hfamW : WScoped (p.nP + 2 + p.nF)
      (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP)) :=
    Expr.WScoped.mkAppN (by simp [WScoped]) hpsW
  -- the family application mentions only the parameters, so it is
  -- scoped at `nP` — the frame the motive's domain is pinned at
  have hfamWn : WScoped p.nP
      (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP)) := by
    refine Expr.WScoped.mkAppN (by simp [WScoped]) (fun x hx => ?_)
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_take] at hi
    split at hi
    · next hlt =>
      obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop' i x hi
      have hw := hfvsW0 _ (List.mem_of_getElem? hi)
      simp only [WScoped] at hw ⊢
      exact ⟨by omega, hw.2⟩
    · exact nomatch hi
  -- the parameters against the constructor's parameter domains
  obtain ⟨q2, hci, h⟩ := atF_bind_ok h
  obtain ⟨cdomsP, crest⟩ := q2
  dsimp only [] at h
  have hci' := unwrapOr_atF_ok hci
  show ((unwrapOr (Expr.instPisAt (fvsP.take p.nP) cvCa.type) _ :
    CheckM _) >>= _) = _
  rw [hci']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hcdW, hcrW⟩ := instPisAt_WScoped (d := p.nP + 2 + p.nF) _ _ hci'
    (WScoped.of_not_hasFvar hCf) hpsW
  have hpsWn : ∀ x ∈ fvsP.take p.nP, WScoped p.nP x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_take] at hi
    split at hi
    · next hlt =>
      obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop' i x hi
      have hw := hfvsW0 _ (List.mem_of_getElem? hi)
      simp only [WScoped] at hw ⊢
      exact ⟨by omega, hw.2⟩
    · exact nomatch hi
  obtain ⟨-, hcrWn⟩ := instPisAt_WScoped (d := p.nP) _ _ hci'
    (WScoped.of_not_hasFvar hCf) hpsWn
  obtain ⟨u1, hd1, h⟩ := atF_bind_ok h
  have hpsIdx : ∀ (i : Nat) (x : Expr), (fvsP.take p.nP)[i]? = some x →
      WScoped (0 + i) (Expr.fvarTypeD x) := by
    intro i x hx
    rw [List.getElem?_take] at hx
    split at hx
    · obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop' i x hx
      have hw := hfvsW0 _ (List.mem_of_getElem? hx)
      simp only [WScoped] at hw
      exact hw.2
    · exact nomatch hx
  have hcdIdx : ∀ (i : Nat) (x : Expr), cdomsP[i]? = some x →
      WScoped (0 + i) x := by
    intro i x hx
    refine instPisAt_index_WScoped (fvsP.take p.nP) (d := 0) hci'
      (WScoped.of_not_hasFvar hCf) ?_ i x hx
    intro k a hk
    rw [List.getElem?_take] at hk
    split at hk
    · obtain ⟨nm, ty, rfl⟩ :=
        openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop' k a hk
      have hw := hfvsW0 _ (List.mem_of_getElem? hk)
      simp only [WScoped] at hw
      simp only [WScoped]
      exact ⟨by omega, hw.2⟩
    · exact nomatch hk
  have hd1' := checkDirectDomsAt_wfimp (off := 0) henv hpsIdx hcdIdx hd1
  show (checkDirectDomsAt (fueledOps F) env 0 (fvsP.take p.nP) cdomsP p.nP
    >>= _) = _
  rw [hd1']
  simp only [Bind.bind, Except.bind]
  -- the motive
  obtain ⟨mfv, hmf, h⟩ := atF_bind_ok h
  have hmf' := unwrapOr_atF_ok hmf
  show ((unwrapOr fvsP[p.nP]? _ : CheckM _) >>= _) = _
  rw [hmf']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have hmftW : WScoped (p.nP + 2 + p.nF) mfv.fvarTypeD :=
    fvarTypeD_WScoped (hfvsW mfv (List.mem_of_getElem? hmf'))
  obtain ⟨q3, hms, h⟩ := atF_bind_ok h
  obtain ⟨mbs, mbody⟩ := q3
  dsimp only [] at h
  have hms' := unwrapOr_atF_ok hms
  show ((unwrapOr (mfv.fvarTypeD.stripPis 1) _ : CheckM _) >>= _) = _
  rw [hms']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨mdom, hmd, h⟩ := atF_bind_ok h
  have hmd' := unwrapOr_atF_ok hmd
  show ((unwrapOr ((mbs[0]?).map (·.2.1)) _ : CheckM _) >>= _) = _
  rw [hmd']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have hmdW : WScoped (p.nP + 2 + p.nF) mdom :=
    stripPis_head_WScoped hms' hmftW hmd'
  have hmftWn : WScoped p.nP mfv.fvarTypeD := by
    obtain ⟨nm, ty, hmfv⟩ :=
      openPisAtFvars_index (p.nP + 2) cvRa.type 0 hop' p.nP mfv hmf'
    have hw := hfvsW0 _ (List.mem_of_getElem? hmf')
    rw [hmfv] at hw ⊢
    simp only [WScoped] at hw
    show WScoped p.nP ty
    simpa using hw.2
  have hmdWn : WScoped p.nP mdom :=
    stripPis_head_WScoped hms' hmftWn hmd'
  rw [wfOpsM_isDefEq henv hmdWn.to_wscopedB hfamWn.to_wscopedB] at h
  obtain ⟨b1, hb1, h⟩ := atF_bind_ok h
  have hb1' : isDefEqCore env F p.nP mdom
    (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
      (fvsP.take p.nP)) = .ok b1 := hb1
  show (isDefEqCore env F p.nP mdom _ >>= _) = _
  rw [hb1']
  simp only [Bind.bind, Except.bind]
  have hb1t : b1 = true := by
    cases b1
    · rw [if_neg (by simp)] at h; exact absurd h atF_throw_bind
    · rfl
  subst hb1t
  rw [if_pos rfl] at h ⊢
  by_cases h2 : (mbody == Expr.sort (.param p.elim)) = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  -- the minor premise
  obtain ⟨minfv, hmi, h⟩ := atF_bind_ok h
  have hmi' := unwrapOr_atF_ok hmi
  show ((unwrapOr fvsP[p.nP + 1]? _ : CheckM _) >>= _) = _
  rw [hmi']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have hmitW : WScoped (p.nP + 2) minfv.fvarTypeD :=
    fvarTypeD_WScoped (hfvsW0 minfv (List.mem_of_getElem? hmi'))
  obtain ⟨q4, hox, h⟩ := atF_bind_ok h
  obtain ⟨xFvs, minBody⟩ := q4
  dsimp only [] at h
  have hox' := unwrapOr_atF_ok hox
  show ((unwrapOr (openPisAtFvars p.nF minfv.fvarTypeD (p.nP + 2)) _ :
    CheckM _) >>= _) = _
  rw [hox']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF minfv.fvarTypeD (p.nP + 2)
    hox' hmitW
  obtain ⟨q5, hcf, h⟩ := atF_bind_ok h
  obtain ⟨cdomsF, crest2⟩ := q5
  dsimp only [] at h
  have hcf' := unwrapOr_atF_ok hcf
  show ((unwrapOr (Expr.instPisAt xFvs crest) _ : CheckM _) >>= _) = _
  rw [hcf']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hcdFW, -⟩ := instPisAt_WScoped (d := p.nP + 2 + p.nF) _ _ hcf'
    hcrW hxW
  obtain ⟨u2, hd2, h⟩ := atF_bind_ok h
  have hxIdx : ∀ (i : Nat) (x : Expr), xFvs[i]? = some x →
      WScoped (p.nP + 2 + i) (Expr.fvarTypeD x) := by
    intro i x hx
    obtain ⟨nm, ty, rfl⟩ :=
      openPisAtFvars_index p.nF minfv.fvarTypeD (p.nP + 2) hox' i x hx
    have hw := hxW _ (List.mem_of_getElem? hx)
    simp only [WScoped] at hw
    exact hw.2
  have hcdFIdx : ∀ (i : Nat) (x : Expr), cdomsF[i]? = some x →
      WScoped (p.nP + 2 + i) x := by
    intro i x hx
    refine instPisAt_index_WScoped xFvs (d := p.nP + 2) hcf'
      (hcrWn.mono (by omega)) ?_ i x hx
    intro k a hk
    obtain ⟨nm, ty, rfl⟩ :=
      openPisAtFvars_index p.nF minfv.fvarTypeD (p.nP + 2) hox' k a hk
    have hw := hxW _ (List.mem_of_getElem? hk)
    simp only [WScoped] at hw ⊢
    exact ⟨by omega, hw.2⟩
  have hd2' := checkDirectDomsAt_wfimp (off := p.nP + 2) henv hxIdx hcdFIdx hd2
  show (checkDirectDomsAt (fueledOps F) env (p.nP + 2) xFvs cdomsF p.nF
    >>= _) = _
  rw [hd2']
  simp only [Bind.bind, Except.bind]
  by_cases h3 : (crest2 ==
      Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP)) = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  by_cases h4 : (minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP ++ xFvs))) = true
  case neg => rw [if_neg h4] at h; exact absurd h atF_throw_bind
  rw [if_pos h4] at h ⊢
  -- the major premise and the conclusion
  obtain ⟨q6, hjs, h⟩ := atF_bind_ok h
  obtain ⟨jbs, jbody⟩ := q6
  dsimp only [] at h
  have hjs' := unwrapOr_atF_ok hjs
  show ((unwrapOr (rest.stripPis 1) _ : CheckM _) >>= _) = _
  rw [hjs']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨jdom, hjd, h⟩ := atF_bind_ok h
  have hjd' := unwrapOr_atF_ok hjd
  show ((unwrapOr ((jbs[0]?).map (·.2.1)) _ : CheckM _) >>= _) = _
  rw [hjd']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have hjdW : WScoped (p.nP + 2) jdom :=
    stripPis_head_WScoped hjs' hrestW0 hjd'
  rw [wfOpsM_isDefEq henv hjdW.to_wscopedB
    (hfamWn.mono (by omega)).to_wscopedB] at h
  obtain ⟨b2, hb2, h⟩ := atF_bind_ok h
  have hb2' : isDefEqCore env F (p.nP + 2) jdom
    (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
      (fvsP.take p.nP)) = .ok b2 := hb2
  show (isDefEqCore env F (p.nP + 2) jdom _ >>= _) = _
  rw [hb2']
  simp only [Bind.bind, Except.bind]
  have hb2t : b2 = true := by
    cases b2
    · rw [if_neg (by simp)] at h; exact absurd h atF_throw_bind
    · rfl
  subst hb2t
  rw [if_pos rfl] at h ⊢
  by_cases h5 : (jbody == Expr.app mfv (.bvar 0)) = true
  case neg => rw [if_neg h5] at h; exact absurd h atF_throw
  rw [if_pos h5] at h ⊢

set_option maxHeartbeats 6400000 in
/-- Stage 4 of the direct install, `wfOpsM` run to pure run, together
with the annotated right-hand side's own well-formedness facts (the
checker's guard, read off for the environment extension).  The rule's
right-hand side is checked closed before it is annotated, and the
λ-domain pins run over the same opening as stage 3. -/
theorem checkDirectRule_wfimp {env : Env} (henv : EnvWF env)
    {p : DirectParts} {cvCa cvRa : ConstantVal} {F : Nat} {v : Expr}
    (hCf : cvCa.type.hasFvar = false) (hRf : cvRa.type.hasFvar = false)
    (h : (checkDirectRule wfOpsM env p cvCa cvRa).val F = .ok v) :
    checkDirectRule (fueledOps F) env p cvCa cvRa = .ok v ∧
      v.hasFvar = false ∧
      v.allLevelParamsDefined cvRa.levelParams = true ∧
      v.constsResolve env = true ∧ v.looseBVarsBounded 0 = true := by
  unfold checkDirectRule at h ⊢
  by_cases h0 : (!p.rhs.hasFvar && Expr.looseBVarsBounded 0 p.rhs) = true
  case neg => rw [if_neg h0] at h; exact absurd h atF_throw_bind
  rw [if_pos h0] at h ⊢
  try dsimp only [] at h ⊢
  have hrawf : p.rhs.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
    exact h0.1
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hrawf)] at h
  obtain ⟨rhsA, hann, h⟩ := atF_bind_ok h
  have hann' : (fueledOps F).annotate env 0 p.rhs = .ok rhsA := hann
  rw [hann']
  simp only [Bind.bind, Except.bind]
  by_cases h1 : (Expr.allLevelParamsDefined cvRa.levelParams rhsA &&
      Expr.constsResolve env rhsA && Expr.looseBVarsBounded 0 rhsA &&
      !rhsA.hasFvar) = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨hlp, hres, hlb, hfv⟩ : Expr.allLevelParamsDefined cvRa.levelParams
      rhsA = true ∧ Expr.constsResolve env rhsA = true ∧
      Expr.looseBVarsBounded 0 rhsA = true ∧ rhsA.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
  obtain ⟨q, hsl, h⟩ := atF_bind_ok h
  obtain ⟨rbs, rbody⟩ := q
  dsimp only [] at h
  have hsl' := unwrapOr_atF_ok hsl
  rw [hsl']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  by_cases h2 : (rbody == directRuleBody p.nF) = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  obtain ⟨q2, hop, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, rrest⟩ := q2
  dsimp only [] at h
  have hop' := unwrapOr_atF_ok hop
  rw [hop']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  have hopW := openPisAtFvars_WScoped (p.nP + 2) cvRa.type 0 hop'
    (WScoped.of_not_hasFvar hRf)
  rw [Nat.zero_add] at hopW
  obtain ⟨hfvsW0, -⟩ := hopW
  have hfvsW : ∀ x ∈ fvsP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => (hfvsW0 x hx).mono (by omega)
  have hpsW : ∀ x ∈ fvsP.take p.nP, WScoped (p.nP + 2 + p.nF) x :=
    fun x hx => hfvsW x (List.mem_of_mem_take hx)
  obtain ⟨q3, hci, h⟩ := atF_bind_ok h
  obtain ⟨cdomsP, crest⟩ := q3
  dsimp only [] at h
  have hci' := unwrapOr_atF_ok hci
  rw [hci']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  have hpsW2 : ∀ x ∈ fvsP.take p.nP, WScoped (p.nP + 2) x :=
    fun x hx => hfvsW0 x (List.mem_of_mem_take hx)
  obtain ⟨-, hcrW2⟩ := instPisAt_WScoped (d := p.nP + 2) _ _ hci'
    (WScoped.of_not_hasFvar hCf) hpsW2
  obtain ⟨q4, hox, h⟩ := atF_bind_ok h
  obtain ⟨xFvs, xrest⟩ := q4
  dsimp only [] at h
  have hox' := unwrapOr_atF_ok hox
  rw [hox']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hxW, -⟩ := openPisAtFvars_WScoped p.nF crest (p.nP + 2)
    hox' hcrW2
  obtain ⟨q6, hli, h⟩ := atF_bind_ok h
  obtain ⟨ldoms, lrest⟩ := q6
  dsimp only [] at h
  have hli' := unwrapOr_atF_ok hli
  rw [hli']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  have hspineW : ∀ a ∈ fvsP ++ xFvs, WScoped (p.nP + 2 + p.nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsW a ha
    · exact hxW a ha
  obtain ⟨hldW, -⟩ := instLamsAt_WScoped (fvsP ++ xFvs) rhsA hli'
    (WScoped.of_not_hasFvar hfv) hspineW
  obtain ⟨u1, hd1, h⟩ := atF_bind_ok h
  have hd1' := checkDefEqList_wfimp henv
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact fvarTypeD_WScoped (hspineW x hx))
    hldW hd1
  rw [hd1']
  simp only [Bind.bind, Except.bind]
  rw [wfOpsM_inferType henv (wscopedB_of_not_hasFvar hfv)] at h
  obtain ⟨rhsTy, hity, h⟩ := atF_bind_ok h
  have hity' : (fueledOps F).inferType env 0 rhsA = .ok rhsTy := hity
  rw [hity']
  simp only [Bind.bind, Except.bind]
  have hv : rhsA = v := by
    have h' : (Except.ok rhsA : Except CheckError Expr) = .ok v := h
    exact Except.ok.inj h'
  subst hv
  exact ⟨h, hfv, hlp, hres, hlb⟩

set_option maxHeartbeats 6400000 in
/-- The projection-function install of the direct path, `wfOpsM` run to
pure run.  The generated projection type is checked closed by the
checker's own guard before it is annotated, and the annotated type's
own guard supplies what `checkProjRule` needs. -/
theorem checkDirectProj_wfimp {env : Env} (henv : EnvWF env)
    {T C : Name} {lps : List Name} {nP nF i F : Nat}
    {cvTa cvCa : ConstantVal} {v : Env}
    (hCf : cvCa.type.hasFvar = false)
    (hCb : cvCa.type.looseBVarsBounded 0 = true)
    (h : (checkDirectProj wfOpsM T C lps nP nF cvTa cvCa env i).val F =
      .ok v) :
    checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa env i = .ok v := by
  unfold checkDirectProj at h ⊢
  obtain ⟨pty, hpt, h⟩ := atF_bind_ok h
  have hpt' := unwrapOr_atF_ok hpt
  rw [hpt']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only [] at h ⊢
  by_cases h0 : (!pty.hasFvar && Expr.looseBVarsBounded 0 pty) = true
  case neg => rw [if_neg h0] at h; exact absurd h atF_throw_bind
  rw [if_pos h0] at h ⊢
  have hptyf : pty.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0
    exact h0.1
  rw [wfOpsM_annotate henv (wscopedB_of_not_hasFvar hptyf)] at h
  obtain ⟨ptyA, hann, h⟩ := atF_bind_ok h
  have hann' : (fueledOps F).annotate env 0 pty = .ok ptyA := hann
  rw [hann']
  simp only [Bind.bind, Except.bind]
  by_cases h1 : (Expr.allLevelParamsDefined lps ptyA &&
      Expr.constsResolve env ptyA && Expr.looseBVarsBounded 0 ptyA &&
      !ptyA.hasFvar) = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  obtain ⟨hAf, hAb⟩ : ptyA.hasFvar = false ∧
      Expr.looseBVarsBounded 0 ptyA = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    exact ⟨h1.2, h1.1.2⟩
  by_cases h2 : (ptyA.stripPis (nP + 1)).isSome = true
  case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
  rw [if_pos h2] at h ⊢
  rw [wfOpsM_inferType henv (wscopedB_of_not_hasFvar hAf)] at h
  obtain ⟨sty, hity, h⟩ := atF_bind_ok h
  have hity' : (fueledOps F).inferType env 0 ptyA = .ok sty := hity
  rw [hity']
  simp only [Bind.bind, Except.bind]
  have hstyW : WScoped 0 sty :=
    inferTypeCore_WScoped henv F hity (WScoped.of_not_hasFvar hAf)
  rw [wfOpsM_ensureSort henv hstyW.to_wscopedB] at h
  obtain ⟨u, hu, h⟩ := atF_bind_ok h
  have hu' : (fueledOps F).ensureSort env 0 sty = .ok u := hu
  rw [hu']
  simp only [Bind.bind, Except.bind]
  by_cases h3 : (env.find? (projFnName T i)).isNone = true
  case neg => rw [if_neg h3] at h; exact absurd h atF_throw_bind
  rw [if_pos h3] at h ⊢
  obtain ⟨u0, hsh, h⟩ := atF_bind_ok h
  rw [checkProjShape_datF] at hsh
  rw [hsh]
  simp only [Bind.bind, Except.bind]
  -- the annotated projection type's own frame walk (task #82): the
  -- subject's domain against the family, the residual against the
  -- constructor's `i`-th field domain
  obtain ⟨q1, hop, h⟩ := atF_bind_ok h
  obtain ⟨fvsP, prest⟩ := q1
  dsimp only [] at h
  have hop' := unwrapOr_atF_ok hop
  show ((unwrapOr (openPisAtFvars nP ptyA 0) _ : CheckM _) >>= _) = _
  rw [hop']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨hfvsW, hprestW⟩ :=
    openPisAtFvars_WScoped nP ptyA 0 hop' (WScoped.of_not_hasFvar hAf)
  rw [Nat.zero_add] at hfvsW hprestW
  have hfamW : WScoped nP (Expr.mkAppN (.const T (lps.map .param)) fvsP) :=
    Expr.WScoped.mkAppN (by simp [WScoped]) hfvsW
  obtain ⟨q2, hsb, h⟩ := atF_bind_ok h
  obtain ⟨sbs, sbody⟩ := q2
  dsimp only [] at h
  have hsb' := unwrapOr_atF_ok hsb
  show ((unwrapOr (prest.stripPis 1) _ : CheckM _) >>= _) = _
  rw [hsb']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨sdom, hsd, h⟩ := atF_bind_ok h
  have hsd' := unwrapOr_atF_ok hsd
  show ((unwrapOr ((sbs[0]?).map (·.2.1)) _ : CheckM _) >>= _) = _
  rw [hsd']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have hsdW : WScoped nP sdom := stripPis_head_WScoped hsb' hprestW hsd'
  rw [wfOpsM_isDefEq henv hsdW.to_wscopedB hfamW.to_wscopedB] at h
  obtain ⟨b1, hb1, h⟩ := atF_bind_ok h
  have hb1' : isDefEqCore env F nP sdom
      (Expr.mkAppN (.const T (lps.map .param)) fvsP) = .ok b1 := hb1
  show (isDefEqCore env F nP sdom _ >>= _) = _
  rw [hb1']
  simp only [Bind.bind, Except.bind]
  have hb1t : b1 = true := by
    cases b1
    · rw [if_neg (by simp)] at h; exact absurd h atF_throw_bind
    · rfl
  subst hb1t
  rw [if_pos rfl] at h ⊢
  obtain ⟨q3, hot, h⟩ := atF_bind_ok h
  obtain ⟨tFvs, resid⟩ := q3
  dsimp only [] at h
  have hot' := unwrapOr_atF_ok hot
  show ((unwrapOr (openPisAtFvars 1 prest nP) _ : CheckM _) >>= _) = _
  rw [hot']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨htfW, hresidW⟩ := openPisAtFvars_WScoped 1 prest nP hot' hprestW
  obtain ⟨tfv, htf, h⟩ := atF_bind_ok h
  have htf' := unwrapOr_atF_ok htf
  show ((unwrapOr tFvs[0]? _ : CheckM _) >>= _) = _
  rw [htf']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  have htfvW : WScoped (nP + 1) tfv := htfW tfv (List.mem_of_getElem? htf')
  have hargsW : ∀ x ∈ fvsP ++ (List.range i).map (fun j =>
      Expr.mkAppN (.const (projFnName T j) (lps.map .param))
        (fvsP ++ [tfv])), WScoped (nP + 1) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hfvsW x hx).mono (by omega)
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      refine Expr.WScoped.mkAppN (by simp [WScoped]) (fun y hy => ?_)
      rcases List.mem_append.mp hy with hy | hy
      · exact (hfvsW y hy).mono (by omega)
      · rcases List.mem_singleton.mp hy with rfl
        exact htfvW
  obtain ⟨q4, hci, h⟩ := atF_bind_ok h
  obtain ⟨cdoms, cresid⟩ := q4
  dsimp only [] at h
  have hci' := unwrapOr_atF_ok hci
  show ((unwrapOr (Expr.instPisAt (fvsP ++ _) cvCa.type) _ : CheckM _)
    >>= _) = _
  rw [hci']
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  obtain ⟨-, hcresW⟩ := instPisAt_WScoped (d := nP + 1) _ _ hci'
    (WScoped.of_not_hasFvar hCf) hargsW
  obtain ⟨fdom, hfd, h⟩ := atF_bind_ok h
  have hfd' := unwrapOr_atF_ok hfd
  obtain ⟨nmC, bodyC, mbC, hcres⟩ :
      ∃ nmC bodyC mbC, cresid = .forallE nmC fdom bodyC mbC := by
    match cresid, hfd' with
    | .forallE nmC d bodyC mbC, hfd' =>
      obtain rfl : d = fdom := by simpa using hfd'
      exact ⟨nmC, bodyC, mbC, rfl⟩
    | .bvar _, hfd' | .fvar _ _ _, hfd' | .sort _, hfd' | .const _ _, hfd'
    | .app _ _, hfd' | .lam _ _ _ _, hfd' | .letE _ _ _ _, hfd'
    | .lit _, hfd' | .proj _ _ _, hfd' => exact nomatch hfd'
  have hfdW : WScoped (nP + 1) fdom := by
    rw [hcres] at hcresW
    simp only [WScoped] at hcresW
    exact hcresW.1
  show ((unwrapOr (match cresid with
      | .forallE _ d _ _ => some d | _ => none) _ : CheckM _) >>= _) = _
  rw [hcres]
  simp only [unwrapOr, Bind.bind, Except.bind, pure, Except.pure]
  try dsimp only []
  rw [wfOpsM_isDefEq henv hresidW.to_wscopedB hfdW.to_wscopedB] at h
  obtain ⟨b2, hb2, h⟩ := atF_bind_ok h
  have hb2' : isDefEqCore env F (nP + 1) resid fdom = .ok b2 := hb2
  show (isDefEqCore env F (nP + 1) resid fdom >>= _) = _
  rw [hb2']
  simp only [Bind.bind, Except.bind]
  have hb2t : b2 = true := by
    cases b2
    · rw [if_neg (by simp)] at h; exact absurd h atF_throw_bind
    · rfl
  subst hb2t
  rw [if_pos rfl] at h ⊢
  obtain ⟨rhsA, hrule, h⟩ := atF_bind_ok h
  have hrule' := checkProjRule_wfimp henv hAf hAb hCf hCb hrule
  rw [hrule']
  simp only [Bind.bind, Except.bind]
  exact h

/-- The projection-install fold of the direct path, `wfOpsM` run to
pure run.  The accumulators' well-formedness is a *run-tied*
hypothesis: `checkDirectProj` stores a constant whose `ConstWF` needs
the declaration inversions, which live with the model
(`Setlec/Model/`), exactly as `installProjFnStep`'s does. -/
theorem foldDirectProj_wfimp {T C : Name} {lps : List Name}
    {nP nF F : Nat} {cvTa cvCa : ConstantVal}
    (hCf : cvCa.type.hasFvar = false)
    (hCb : cvCa.type.looseBVarsBounded 0 = true)
    (hstep : ∀ (e e' : Env) (i : Nat), EnvWF e →
      checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa e i = .ok e' →
      EnvWF e') :
    ∀ (idxs : List Nat) (e : Env) {e₂ : Env}, EnvWF e →
      (idxs.foldlM (checkDirectProj wfOpsM T C lps nP nF cvTa cvCa)
        e).val F = .ok e₂ →
      idxs.foldlM (checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa)
        e = .ok e₂
  | [], e, e₂, _, h => by
    have h' : (Except.ok e : CheckM Env) = Except.ok e₂ := h
    cases h'
    rfl
  | i :: idxs, e, e₂, he, h => by
    have h' : ((checkDirectProj wfOpsM T C lps nP nF cvTa cvCa e i >>=
        fun e₁ => idxs.foldlM
          (checkDirectProj wfOpsM T C lps nP nF cvTa cvCa) e₁ :
        FueledM Env)).val F = .ok e₂ := h
    rw [FueledM.atF_bind] at h'
    cases hm : (checkDirectProj wfOpsM T C lps nP nF cvTa cvCa e i).val F
      with
    | error err => rw [hm] at h'; exact nomatch h'
    | ok e₁ =>
      rw [hm] at h'
      have h'' : (idxs.foldlM
        (checkDirectProj wfOpsM T C lps nP nF cvTa cvCa) e₁).val F =
          .ok e₂ := h'
      have hp := checkDirectProj_wfimp he hCf hCb hm
      have hrest := foldDirectProj_wfimp hCf hCb hstep idxs e₁
        (hstep e e₁ i he hp) h''
      show (checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa e i >>=
        fun e₁ => idxs.foldlM
          (checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa) e₁) =
        .ok e₂
      rw [hp]
      exact hrest

set_option maxHeartbeats 6400000 in
/-- The whole direct install, `wfOpsM` run to pure run.

`checkDirectStruct` extends the environment three times before the
projection fold and runs its operations at *every* one of those
environments, so their well-formedness is owed here.  It is taken as a
hypothesis, and every hypothesis is **run-tied** — it speaks about the
environments and constants the run itself produces — because
establishing it needs the declaration inversions that live with the
model (`Setlec/Model/Extend/`), exactly as `installProjFnStep`'s
does. -/
theorem checkDirectStruct_wfimp {env : Env} (henv : EnvWF env)
    {p : DirectParts} {F : Nat} {v : Env}
    (hwf₁ : ∀ (e₁ : Env) (cvTa : ConstantVal),
      (checkDirectInd wfOpsM env p).val F = .ok (e₁, cvTa) →
      EnvWF e₁ ∧ cvTa.type.hasFvar = false)
    (hwf₂ : ∀ (e₁ e₂ : Env) (cvTa cvCa : ConstantVal),
      (checkDirectInd wfOpsM env p).val F = .ok (e₁, cvTa) →
      (checkDirectCtor wfOpsM env e₁ p cvTa).val F = .ok (e₂, cvCa) →
      EnvWF e₂ ∧ cvCa.type.hasFvar = false ∧
        cvCa.type.looseBVarsBounded 0 = true)
    (hwf₃ : ∀ (e₂ : Env) (cvCa cvRa : ConstantVal) (rhsA : Expr),
      EnvWF e₂ →
      checkConstantVal (fueledOps F) e₂ p.cvR = .ok cvRa →
      checkDirectRule (fueledOps F) e₂ p cvCa cvRa = .ok rhsA →
      EnvWF ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
            .plain else .inert, rhsA⟩] :: e₂.consts⟩)
    (hstep : ∀ (cvTa cvCa : ConstantVal) (e e' : Env) (i : Nat), EnvWF e →
      checkDirectProj (fueledOps F) p.cvT.name p.cvC.name p.cvT.levelParams
        p.nP p.nF cvTa cvCa e i = .ok e' → EnvWF e')
    (h : (checkDirectStruct wfOpsM env p).val F = .ok v) :
    checkDirectStruct (fueledOps F) env p = .ok v := by
  unfold checkDirectStruct at h ⊢
  obtain ⟨q1, hind, h⟩ := atF_bind_ok h
  obtain ⟨env₁, cvTa⟩ := q1
  dsimp only [] at h
  have hind' := checkDirectInd_wfimp henv hind
  rw [hind']
  simp only [Bind.bind, Except.bind]
  obtain ⟨henv₁, hTf⟩ := hwf₁ env₁ cvTa hind
  obtain ⟨q2, hct, h⟩ := atF_bind_ok h
  obtain ⟨env₂, cvCa⟩ := q2
  dsimp only [] at h
  have hct' := checkDirectCtor_wfimp henv₁ hTf hct
  rw [hct']
  simp only [Bind.bind, Except.bind]
  obtain ⟨henv₂, hCf, hCb⟩ := hwf₂ env₁ env₂ cvTa cvCa hind hct
  obtain ⟨cvRa, hcv, h⟩ := atF_bind_ok h
  have hcv' := checkConstantVal_wfimp henv₂ hcv
  rw [hcv']
  simp only [Bind.bind, Except.bind]
  obtain ⟨hRf, -, -, -⟩ := checkConstantVal_typeWF hcv'
  obtain ⟨u0, hrt, h⟩ := atF_bind_ok h
  have hrt' := checkDirectRecTy_wfimp henv₂ hCf hRf hrt
  rw [hrt']
  simp only [Bind.bind, Except.bind]
  obtain ⟨rhsA, hru, h⟩ := atF_bind_ok h
  obtain ⟨hru', -⟩ := checkDirectRule_wfimp henv₂ hCf hRf hru
  rw [hru']
  simp only [Bind.bind, Except.bind]
  have henv₃ := hwf₃ env₂ cvCa cvRa rhsA henv₂ hcv' hru'
  by_cases h1 : (List.range p.nF).all (fun j =>
      (Env.find? ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
            .plain else .inert, rhsA⟩] :: env₂.consts⟩
        (projFnName p.cvT.name j)).isNone) = true
  case neg => rw [if_neg h1] at h; exact absurd h atF_throw_bind
  rw [if_pos h1] at h ⊢
  exact foldDirectProj_wfimp hCf hCb (hstep cvTa cvCa) (List.range p.nF)
    _ henv₃ h

end Setlec
