import Setlec.Model.DirectInstall
import Setlec.Model.InterpLemmas

/-!
# Level-parameter extensionality of the direct construction

`EnvModel.val_params` demands that a constant's value only reads its own
level parameters.  The direct simple-structure values are built from
`interpExpr` and `Level.eval` over the block's stored types, so the
property is inherited: this module carries it through the λ-tower and
the dependent-pair tower.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env}
variable {cval : ConstVal V}

open SetTheory Expr

/-- `openPisAtFvars` keeps every level parameter inside the declared
set (the fvar annotations are the binders' own domains). -/
theorem openPisAtFvars_allLevelParamsDefined {ps : List Name} :
    ∀ (k : Nat) (e : Expr) (i : Nat) (fvs : List Expr) (rest : Expr),
      openPisAtFvars k e i = some (fvs, rest) →
      e.allLevelParamsDefined ps = true →
      rest.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro e i fvs rest h he
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | succ k ih =>
    intro e i fvs rest h he
    match e with
    | .forallE n dom body m =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (body.instantiate1 (.fvar i n dom)) (i + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some q =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
        have hq := ih (body.instantiate1 (.fvar i n dom)) (i + 1) q.1 q.2 hop
          (allLevelParamsDefined_instantiate1 he.1.1 0 he.1.2)
        rw [← h.2]
        exact hq
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch h

/-- `instantiate1` at an arbitrary replacement keeps level parameters
inside the declared set (the `fvar`-specialised
`allLevelParamsDefined_instantiate1` does not cover the open
replacements a telescope instantiation uses). -/
theorem allLevelParamsDefined_instantiate1_gen {ps : List Name} {v : Expr}
    (hv : v.allLevelParamsDefined ps = true) :
    ∀ {e : Expr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 v k).allLevelParamsDefined ps = true := by
  intro e
  induction e <;> intro k h <;>
    simp_all [Expr.instantiate1, Expr.allLevelParamsDefined]
  case bvar i =>
    split
    · exact hv
    · split <;> simp [Expr.allLevelParamsDefined]

/-- Every variable `openPisAtFvars` produces carries a binder domain of
the telescope, hence only declared level parameters. -/
theorem openPisAtFvars_fvar_allLevelParamsDefined {ps : List Name} :
    ∀ (k : Nat) (e : Expr) (i : Nat) (fvs : List Expr) (rest : Expr),
      openPisAtFvars k e i = some (fvs, rest) →
      e.allLevelParamsDefined ps = true →
      ∀ a ∈ fvs, a.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro e i fvs rest h _ a ha
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at ha
    exact absurd ha List.not_mem_nil
  | succ k ih =>
    intro e i fvs rest h he a ha
    match e with
    | .forallE n dom body m =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (body.instantiate1 (.fvar i n dom)) (i + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some q =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
        rw [← h.1] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact he.1.1
        · exact ih _ (i + 1) q.1 q.2 hop
            (allLevelParamsDefined_instantiate1 he.1.1 0 he.1.2) a ha
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch h

/-- Instantiating a telescope at arguments with declared level
parameters keeps the residual's within the declared set. -/
theorem instPisAt_allLevelParamsDefined {ps : List Name} :
    ∀ (args : List Expr) (e : Expr) (ds : List Expr) (rest : Expr),
      Expr.instPisAt args e = some (ds, rest) →
      e.allLevelParamsDefined ps = true →
      (∀ a ∈ args, a.allLevelParamsDefined ps = true) →
      rest.allLevelParamsDefined ps = true := by
  intro args
  induction args with
  | nil =>
    intro e ds rest h he _
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | cons a args ih =>
    intro e ds rest h he ha
    match e with
    | .forallE n dom body m =>
      simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, hqe⟩ := h
      simp only [Prod.mk.injEq] at hqe
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at he
      rw [← hqe.2]
      exact ih _ q.1 q.2 hq
        (allLevelParamsDefined_instantiate1_gen (ha a List.mem_cons_self) 0
          he.1.2)
        (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact nomatch h

/-- The dependent-pair tower only reads the declared level parameters. -/
theorem sigmaTowerV_params (hcp : ConstValParams cval env) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) (w : Nat) :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr),
      ty.allLevelParamsDefined ps = true →
      sigmaTowerV V cval env φ₁ w k d ρ ty =
        sigmaTowerV V cval env φ₂ w k d ρ ty := by
  intro k
  induction k with
  | zero => intro d ρ ty _; rfl
  | succ k ih =>
    intro d ρ ty hty
    match ty with
    | .forallE n dom body m =>
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hty
      rw [sigmaTowerV_forallE, sigmaTowerV_forallE,
        interp_params_ext hcp hφ dom d ρ hty.1.1]
      refine congrArg _ (funext fun x => ?_)
      exact ih (d + 1) (updV V ρ d x) _
        (allLevelParamsDefined_instantiate1 hty.1.1 0 hty.1.2)
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

/-- The λ-tower only reads the declared level parameters (given a body
that does). -/
theorem teleLamV_params (hcp : ConstValParams cval env) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (k d : Nat) (ρ : Nat → V) (ty : Expr)
      (S₁ S₂ : Nat → (Nat → V) → List V → V),
      ty.allLevelParamsDefined ps = true →
      (∀ d' ρ' xs, S₁ d' ρ' xs = S₂ d' ρ' xs) →
      teleLamV V cval env φ₁ k d ρ ty S₁ =
        teleLamV V cval env φ₂ k d ρ ty S₂ := by
  intro k
  induction k with
  | zero => intro d ρ ty S₁ S₂ _ hS; exact hS d ρ []
  | succ k ih =>
    intro d ρ ty S₁ S₂ hty hS
    match ty with
    | .forallE n dom body m =>
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hty
      have hcod : (m.cod.getD Level.zero).eval φ₁ =
          (m.cod.getD Level.zero).eval φ₂ := by
        cases hm : m.cod with
        | none => rfl
        | some v =>
          have : v.allParamsDefined ps = true := by
            rw [hm] at hty; exact hty.2
          simpa [hm] using Level.eval_ext this hφ
      rw [teleLamV_forallE, teleLamV_forallE, hcod,
        interp_params_ext hcp hφ dom d ρ hty.1.1]
      refine congrArg _ (funext fun x => ?_)
      exact ih (d + 1) (updV V ρ d x) _ _ _
        (allLevelParamsDefined_instantiate1 hty.1.1 0 hty.1.2)
        (fun d' ρ' xs => hS d' ρ' (x :: xs))
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

/-- The type former's value only reads the declared level parameters. -/
theorem directTyVal_params (hcp : ConstValParams cval env) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p)
    {tty cty : Expr} {nP nF : Nat} {s : Level}
    (htty : tty.allLevelParamsDefined ps = true)
    (hcty : cty.allLevelParamsDefined ps = true)
    (hs : s.allParamsDefined ps = true) :
    directTyVal V cval env tty cty nP nF s φ₁ =
      directTyVal V cval env tty cty nP nF s φ₂ := by
  have hcrest : (directCRest tty cty nP).allLevelParamsDefined ps = true := by
    unfold directCRest
    cases hop : openPisAtFvars nP tty 0 with
    | none => rfl
    | some q =>
      dsimp only []
      cases hci : Expr.instPisAt q.1 cty with
      | none => rfl
      | some q2 =>
        dsimp only []
        exact instPisAt_allLevelParamsDefined q.1 cty q2.1 q2.2 hci hcty
          (openPisAtFvars_fvar_allLevelParamsDefined nP tty 0 q.1 q.2 hop htty)
  unfold directTyVal
  rw [Level.eval_ext hs hφ]
  refine teleLamV_params hcp hφ nP 0 (rho0 V) tty _ _ htty
    (fun d ρ _ => ?_)
  unfold directTyBody
  rw [sigmaTowerV_params hcp hφ _ nF d ρ _ hcrest]

/-- The constructor's value only reads the declared level parameters. -/
theorem directCtorVal_params (hcp : ConstValParams cval env) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p)
    {cty : Expr} {nP nF : Nat}
    (hcty : cty.allLevelParamsDefined ps = true) :
    directCtorVal V cval env cty nP nF φ₁ =
      directCtorVal V cval env cty nP nF φ₂ :=
  teleLamV_params hcp hφ (nP + nF) 0 (rho0 V) cty _ _ hcty
    (fun _ _ _ => rfl)

/-- A projection's value only reads the declared level parameters. -/
theorem directProjVal_params (hcp : ConstValParams cval env) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p)
    {pty : Expr} {nP i : Nat}
    (hpty : pty.allLevelParamsDefined ps = true) :
    directProjVal V cval env pty nP i φ₁ =
      directProjVal V cval env pty nP i φ₂ :=
  teleLamV_params hcp hφ (nP + 1) 0 (rho0 V) pty _ _ hpty
    (fun _ _ _ => rfl)

/-- The recursor's value only reads the declared level parameters. -/
theorem directRecVal_params (hcp : ConstValParams cval env) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p)
    {rty : Expr} {nP nF : Nat}
    (hrty : rty.allLevelParamsDefined ps = true) :
    directRecVal V cval env rty nP nF φ₁ =
      directRecVal V cval env rty nP nF φ₂ :=
  teleLamV_params hcp hφ (nP + 3) 0 (rho0 V) rty _ _ hrty
    (fun _ _ _ => rfl)

end Setlec
