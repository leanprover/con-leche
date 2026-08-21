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
* closedness of checker-constructed terms (`buildIotaStmt`'s statement
  is assembled from closed pieces — proven below).

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

/-- The iota statement is assembled from closed pieces (rule rhs
components, constructor-type components lifted and renamed, `bvar`
spines), so it is closed. -/
theorem buildIotaStmt_not_hasFvar {f : Name → Name}
    {recName ctorName : Name} {recLPs ctorLPs : List Name}
    {nP nM nm ni nF : Nat} {recTy ctorTy ruleRhs stmt : Expr}
    (h : buildIotaStmt f recName ctorName recLPs ctorLPs nP nM nm ni nF
      recTy ctorTy ruleRhs = some stmt)
    (hrhs : ruleRhs.hasFvar = false) (hctor : ctorTy.hasFvar = false) :
    stmt.hasFvar = false := by
  unfold buildIotaStmt at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Option.guard_eq_some_iff] at h
  obtain ⟨⟨binders₀, body⟩, hstrip, bisR, hbisR, bisC, hbisC,
    ⟨cbinders, cbody⟩, hstripC, mB, hnth, ℓ, hsort, htail⟩ := h
  obtain ⟨-, -, hstmt⟩ := htail
  obtain ⟨hbdoms, hbody⟩ := stripLams_not_hasFvar _ hstrip hrhs
  obtain ⟨-, hcbody⟩ := stripPis_not_hasFvar _ hstripC hctor
  subst hstmt
  -- the domains of the final telescope come from the rule's λ-domains
  have hdoms : ∀ b ∈ (binders₀.zip (bisR ++ bisC.drop nP)).mapIdx
      (fun i (b : (Name × Expr × BinderMeta) × BinderInfo) =>
        ((if i < nP + nM + nm then b.1.1
          else (cbinders.getD (i - (nM + nm)) b.1).1),
         b.1.2.1, b.2)),
      (b.2.1).hasFvar = false := by
    intro b hb
    rw [List.mem_mapIdx] at hb
    obtain ⟨i, hi, hbe⟩ := hb
    have hilt : i < binders₀.length := by
      have := hi
      rw [List.length_zip] at this
      omega
    have hfst : ((binders₀.zip (bisR ++ bisC.drop nP))[i]'hi).1 ∈
        binders₀ := by
      rw [List.getElem_zip]
      exact List.getElem_mem _
    have : b.2.1 = ((binders₀.zip (bisR ++ bisC.drop nP))[i]'hi).1.2.1 := by
      rw [← hbe]
    rw [this]
    exact hbdoms _ hfst
  -- the equation body is closed
  have hiargs : ∀ x ∈ (cbody.getAppArgs.drop nP).map
      (fun e => (e.liftLooseBVars (nM + nm) nF).renameConsts f),
      x.hasFvar = false := by
    intro x hx
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hx
    rw [hasFvar_renameConsts, hasFvar_liftLooseBVars]
    exact hasFvar_getAppArgs hcbody _ (List.mem_of_mem_drop he₀)
  have hbvars : ∀ (l : List Nat) (g : Nat → Expr),
      (∀ k, (g k).hasFvar = false) → ∀ x ∈ l.map g, x.hasFvar = false := by
    intro l g hg x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact hg k
  have hctorApp : (Expr.mkAppN (.const (f ctorName) (ctorLPs.map .param))
      (((List.range nP).map fun k =>
          Expr.bvar (nP + nM + nm + nF - 1 - k)) ++
        ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))).hasFvar
      = false := by
    refine hasFvar_mkAppN _ _ rfl ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        rfl
  have heqApp : ∀ {g : Expr}, g.hasFvar = false →
      ∀ {args : List Expr}, (∀ x ∈ args, x.hasFvar = false) →
      (Expr.mkAppN g args).hasFvar = false :=
    fun hg _ hargs => hasFvar_mkAppN _ _ hg hargs
  -- fold the telescope
  generalize hglist : (binders₀.zip (bisR ++ bisC.drop nP)).mapIdx _ =
    bs at hdoms ⊢
  clear hglist
  induction bs with
  | nil =>
    simp only [List.foldr_nil]
    refine heqApp rfl ?_
    intro x hx
    simp only [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | hx
    · -- α: motive bvar applied to iArgs and the ctor app
      refine heqApp rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hiargs y hy
      · rcases List.mem_singleton.mp hy with rfl
        exact hctorApp
    · -- lhs
      refine heqApp rfl ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · rcases List.mem_append.mp hy with hy | hy
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
            rfl
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
            rfl
        · exact hiargs y hy
      · rcases List.mem_singleton.mp hy with rfl
        exact hctorApp
    · -- rhs
      rw [hasFvar_renameConsts]
      exact hbody
    · exact nomatch hx
  | cons b bs ih =>
    simp only [List.foldr_cons, Expr.hasFvar, Bool.or_eq_false_iff]
    refine ⟨?_, ih (fun x hx => hdoms x (List.mem_cons_of_mem _ hx))⟩
    rw [hasFvar_renameConsts]
    exact hdoms b (List.mem_cons_self ..)

/-! ## Run plumbing -/

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

end Setlec
