import Setlec.Verify.Mono
import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift
import Setlec.Verify.InstLevels
import Setlec.Verify.EnvWF
import Setlec.Verify.Knot
import Setlec.Verify.StrLitExpr

/-!
# Preservation and inversion lemmas for the checker core

Under environment well-formedness (`EnvWF`), reduction preserves the
syntactic invariants the model soundness proofs thread (well-scopedness
here; the free-variable leaf closure in `Setlec.Verify.InferLeaves`),
and the new mutual-core branches get inversion lemmas so the many
consumers don't re-destructure the do-chains.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

open Expr

theorem find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts :=
  List.mem_of_find?_eq_some h

/-! ## Inversion lemmas -/

set_option linter.unusedSimpArgs false in
/-- Inversion for `whnfCore` on applications: either a beta step
happened, or an iota step (with the stuck-major machinery), or the
application is stuck.

**Task #161, the β gate.**  The beta disjunct's certificate premise is
a *disjunction* — "either the mode's gate fired at a `.never` binder,
or the certificate ran and passed" (`betaGateTest`,
`Verify/BetaGate.lean`).  The statement is therefore mode-generic and
true at every mode, gated or not, which is what keeps the whole
population of consumers that *discard* the certificate component
(`whnfPres_*`, the leaf/level/bridge/simulation families) verbatim.

Consumers that *consume* the certificate use `whnf_app_inv_ungated`
below and owe a `mode.betaGate = false` hypothesis: they are the R
lane, whose `Red.beta` needs the argument's domain membership and has
no annotation to read it off. -/
theorem whnf_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr}
    (h : whnfCore mode env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f', whnfCore mode env fuel d f = .ok f' ∧
      ((∃ n ty body m, f' = .lam n ty body m ∧
          whnfCore mode env fuel d (body.instantiate1 a) = .ok e' ∧
          (betaGateFires mode m.pw = true ∨
            ∃ ta, inferTypeIO mode env fuel d a = .ok ta ∧
              isDefEqCore mode env fuel d ta ty = .ok true)) ∨
        (∃ e'', iotaRecP mode env fuel d (.app f' a) = .ok (some e'') ∧
          whnfCore mode env fuel d e'' = .ok e') ∨
        e' = .app f' a) := by
  rw [whnfCore_succ] at h
  simp only [whnfCoreBody, Bind.bind, Except.bind] at h
  simp only [whnfCore_def, infer_def, inferTypeIO_def, defeq_def,
    iotaRec_fold] at h
  cases hwf : whnfCore mode env fuel d f with
  | error err => rw [hwf] at h; exact nomatch h
  | ok f' =>
  rw [hwf] at h
  dsimp only at h
  refine ⟨f', rfl, ?_⟩
  match f', h with
  | .lam n ty body m, h => ?_
  | .sort u, h => ?_
  | .fvar i n' t', h => ?_
  | .const n' us, h => ?_
  | .forallE n' t' b' m', h => ?_
  | .bvar i, h => ?_
  | .app f'' a'', h => ?_
  | .letE n' t' v' b', h => ?_
  | .lit l', h => ?_
  | .proj s' i' e'', h => ?_
  case _ =>
    dsimp only at h
    by_cases hg : betaGateFires mode m.pw = true
    · rw [if_pos hg] at h
      exact Or.inl ⟨n, ty, body, m, rfl, h, Or.inl hg⟩
    · rw [if_neg hg] at h
      try simp only [Bind.bind, Except.bind] at h
      try dsimp only at h
      cases hta : inferTypeIO mode env fuel d a with
      | error err => rw [hta] at h; exact nomatch h
      | ok ta =>
      rw [hta] at h
      dsimp only at h
      cases hde : isDefEqCore mode env fuel d ta ty with
      | error err => rw [hde] at h; exact nomatch h
      | ok bb =>
      rw [hde] at h
      cases bb with
      | true =>
        simp only [if_true] at h
        exact Or.inl ⟨n, ty, body, m, rfl, h, Or.inr ⟨ta, rfl, hde⟩⟩
      | false =>
        simp only [Bool.false_eq_true, if_false, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    cases hio : iotaRecP mode env fuel d (.app _ a) with
    | error err => rw [hio] at h; exact nomatch h
    | ok o =>
      rw [hio] at h
      dsimp only at h
      cases o with
      | some e'' => exact Or.inr (Or.inl ⟨e'', rfl, h⟩)
      | none =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)

/-- `whnf_app_inv` at a mode whose β gate is off — the **pre-gate
letter**, verbatim: the beta disjunct carries the certificate itself.
The dead-branch collapse (`betaGateTest_off`) is the whole proof. -/
theorem whnf_app_inv_ungated {env : Env} {fuel d : Nat} {f a e' : Expr}
    (hg : mode.betaGate = false)
    (h : whnfCore mode env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f', whnfCore mode env fuel d f = .ok f' ∧
      ((∃ n ty body m, f' = .lam n ty body m ∧
          whnfCore mode env fuel d (body.instantiate1 a) = .ok e' ∧
          ∃ ta, inferTypeCore mode env fuel d a = .ok ta ∧
            isDefEqCore mode env fuel d ta ty = .ok true) ∨
        (∃ e'', iotaRecP mode env fuel d (.app f' a) = .ok (some e'') ∧
          whnfCore mode env fuel d e'' = .ok e') ∨
        e' = .app f' a) := by
  obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
  refine ⟨f', hwf, ?_⟩
  rcases hcase with ⟨n, ty, body, m, hf', hbeta, hc⟩ | hrest
  · rcases hc with hfired | hcert
    · rw [betaGateFires_off hg] at hfired; exact absurd hfired (by simp)
    · obtain ⟨ta, hta, hde⟩ := hcert
      rw [inferTypeIO_off hg] at hta
      exact Or.inl ⟨n, ty, body, m, hf', hbeta, ta, hta, hde⟩
  · exact Or.inr hrest

/-- Inversion for one iteration of the reduction loop
(`whnfStep`): head-normalize, then either the literal acceleration or
one definition unfolding hands the reduct to the loop's continuation
`k`, or the head normal form is final.  Task #106: the loop steps are
iteration on `whnfLoop`'s own budget, so this is stated about the
continuation-parameterized body; `whnfLoop … (n+1)` *is*
`whnfStep … (whnfLoop … n)`, so consumers apply it after `cases` on
the budget and use the budget induction hypothesis for `k`. -/
theorem whnfStep_inv {env : Env} {fuel d : Nat} {k : Expr → CheckM Expr}
    {e e' : Expr}
    (h : whnfStep (pureFns mode env fuel) env d k e = .ok e') :
    ∃ e₁, whnfCore mode env fuel d e = .ok e₁ ∧
      ((∃ e₂, reduceNatP mode env fuel d e₁ = .ok (some e₂) ∧
          k e₂ = .ok e') ∨
       (reduceNatP mode env fuel d e₁ = .ok none ∧
        ∃ e₂, unfoldDefinition env e₁ = some e₂ ∧
          k e₂ = .ok e') ∨
       (reduceNatP mode env fuel d e₁ = .ok none ∧
        unfoldDefinition env e₁ = none ∧ e' = e₁)) := by
  simp only [whnfStep, Bind.bind, Except.bind] at h
  simp only [whnfCore_def] at h
  cases hwc : whnfCore mode env fuel d e with
  | error err => rw [hwc] at h; exact nomatch h
  | ok e₁ =>
  rw [hwc] at h
  dsimp only at h
  simp only [reduceNat_fold] at h
  cases hrn : reduceNatP mode env fuel d e₁ with
  | error err => rw [hrn] at h; exact nomatch h
  | ok o =>
  rw [hrn] at h
  dsimp only at h
  cases o with
  | some e₂ => exact ⟨e₁, rfl, Or.inl ⟨e₂, hrn, h⟩⟩
  | none =>
  dsimp only at h
  cases hu : unfoldDefinition env e₁ with
  | some e₂ =>
    rw [hu] at h
    dsimp only at h
    exact ⟨e₁, rfl, Or.inr (Or.inl ⟨hrn, e₂, hu, h⟩)⟩
  | none =>
    rw [hu] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨e₁, rfl, Or.inr (Or.inr ⟨hrn, hu, h.symm⟩)⟩

/-- Inversion for the λ-rule of `inferTypeCore` (infer-only: the
annotation is reused whole).  The last conjunct is the **codomain
sort** (task #152), delivered at the verified modes only: it is the
`HasSort (A :: Δ) B v` premise the set lane's annotation pass needs at
every λ node, in the shape the checker computes it (infer, then whnf
to a sort — `Setlec/SetR/Annot/Pass.lean`'s `HasSort` unfolded along
the bridge).  At `.noModel` — the official-parity lane, which does not
run the check — it is vacuous. -/
theorem inferTypeCore_lam_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCore mode env (fuel + 1) d (.lam n ty body m) = .ok t) :
    ∃ tty u bt,
      inferTypeCore mode env fuel d ty = .ok tty ∧
      whnf mode env fuel d tty = .ok (.sort u) ∧
      inferTypeCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) = .ok bt ∧
      (mode.verified = true → body.isLam = false → ∃ btt v,
        inferTypeCore mode env fuel (d + 1) bt = .ok btt ∧
        whnf mode env fuel (d + 1) btt = .ok (.sort v) ∧
        (Level.zeronessOf v).equiv m.pw = true) ∧
      (mode.verified = true → ∀ pwI, body.lamPw = some pwI →
        m.pw.equiv pwI = true) ∧
      t = .forallE n ty (bt.abstract1 d) m := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def] at h
  cases htty : inferTypeCore mode env fuel d ty with
  | error err => rw [htty] at h; exact nomatch h
  | ok tty =>
  rw [htty] at h
  dsimp only at h
  cases hwtty : whnf mode env fuel d tty with
  | error err => rw [hwtty] at h; exact nomatch h
  | ok wtty =>
  rw [hwtty] at h
  dsimp only at h
  revert h
  match wtty with
  | .sort u => ?_
  | .bvar _ | .fvar _ _ _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  -- the annotation-validation block (tasks #152/#161), verified modes
  by_cases hv : mode.verified = true
  case neg =>
    rw [if_neg hv] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, rfl, hwtty, rfl,
      fun hv' _ => absurd hv' hv,
      fun hv' _ _ => absurd hv' hv, h.symm⟩
  rw [if_pos hv] at h
  revert h
  match body with
  | .lam nI tyI bI mbI =>
    intro h
    simp only [Expr.lamPw] at h
    by_cases hpw : m.pw.equiv mbI.pw = true
    · rw [if_pos hpw] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨tty, u, bt, rfl, hwtty, rfl, ?_, ?_, h.symm⟩
      · intro _ hlam; simp [Expr.isLam] at hlam
      · intro _ pwI heq
        try simp only [Expr.lamPw, Option.some.injEq] at heq
        first
          | (cases heq; exact hpw)
          | (rw [← heq]; exact hpw)
          | (injection heq with heq; rw [← heq]; exact hpw)
    · rw [if_neg hpw] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h
    simp only [Expr.lamPw] at h
    simp only [ensureSort, whnf_def, Bind.bind, Except.bind] at h
    revert h
    cases hbtt : inferTypeCore mode env fuel (d + 1) bt with
    | error err => intro h; exact nomatch h
    | ok btt => ?_
    dsimp only
    cases hwbtt : whnf mode env fuel (d + 1) btt with
    | error err => intro h; exact nomatch h
    | ok wbtt => ?_
    dsimp only
    match wbtt with
    | .sort v =>
      intro h
      dsimp only [pure, Except.pure] at h
      by_cases hz : (Level.zeronessOf v).equiv m.pw = true
      · rw [if_pos hz] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        refine ⟨tty, u, bt, rfl, hwtty, rfl,
          fun _ _ => ⟨btt, v, hbtt, hwbtt, hz⟩, ?_, h.symm⟩
        intro _ pwI heq
        first
          | exact nomatch heq
          | simp [Expr.lamPw] at heq
      · rw [if_neg hz] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | .bvar _ | .fvar _ _ _ | .const _ _ | .app _ _ | .lam _ _ _ _
    | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      intro h; simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The λ→∀ meta copy, named** (task #161 P3, piece 3): the type
`inferTypeCore` returns for a λ is a `∀` carrying the λ's *own*
binder meta — annotation included.  This is definitional
(`Core.lean`'s λ clause returns `.forallE n ty (bt.abstract1 depth)
mb`), and it is why an inferred type needs no ∀-front-door pass of its
own: the codomain check the λ clause ran (chain or leaf) *is* the
validation of the copied datum, and the `denoteP` readings of the λ
and of its inferred type dispatch on the same regime numeral
`pwBit φ m.pw` by their clause equations. -/
theorem infer_lam_meta_copy {env : Env} {fuel d : Nat} {n : Name}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCore mode env (fuel + 1) d (.lam n ty body m) = .ok t) :
    ∃ bt, t = .forallE n ty bt m := by
  obtain ⟨tty, u, bt, -, -, -, -, -, ht⟩ := inferTypeCore_lam_inv h
  exact ⟨bt.abstract1 d, ht⟩

/-- Inversion for the application rule of `inferTypeCore` (task #100
de-gating: the per-argument re-check runs unconditionally — the former
possibly-Prop gate of task #49 is unsound-to-model under the
domain-relative collapse). -/
theorem inferTypeCore_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m', inferTypeCore mode env fuel d f = .ok tf ∧
      whnf mode env fuel d tf = .ok (.forallE n' ty' body' m') ∧
      t = body'.instantiate1 a ∧
      ∃ ta, inferTypeCore mode env fuel d a = .ok ta ∧
        isDefEqCore mode env fuel d ta ty' = .ok true := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeq_def] at h
  cases htf : inferTypeCore mode env fuel d f with
  | error err => rw [htf] at h; exact nomatch h
  | ok tf =>
  rw [htf] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tf with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  dsimp only at h
  match w, h with
  | .forallE n' ty' body' m', h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i n2 t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  cases hta : inferTypeCore mode env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore mode env fuel d ta ty' with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  cases r with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
    simp only [if_true, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tf, n', ty', body', m', rfl, hw, h.symm, ta, rfl, hde⟩

/-- Inversion for the ∀-rule of `inferTypeCore` (task #100 stage 6:
the codomain sort is inferred from the opened body — the stored
annotation is not read). -/
theorem inferTypeCore_forall_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCore mode env (fuel + 1) d (.forallE n ty body m) = .ok t) :
    ∃ tty u bt v, inferTypeCore mode env fuel d ty = .ok tty ∧
      whnf mode env fuel d tty = .ok (.sort u) ∧
      inferTypeCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) = .ok bt ∧
      ensureSortCore mode env fuel (d + 1) bt = .ok v ∧
      (mode.verified = true → (Level.zeronessOf v).equiv m.pw = true) ∧
      t = .sort (.imax u v) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, ensureSort_def] at h
  try dsimp only at h
  cases hty : inferTypeCore mode env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hwt : whnf mode env fuel d tty with
  | error err => rw [hwt] at h; exact nomatch h
  | ok w =>
  rw [hwt] at h
  dsimp only at h
  revert h
  match w with
  | .sort u => ?_
  | .bvar _ | .fvar _ _ _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  cases hes : ensureSortCore mode env fuel (d + 1) bt with
  | error err => rw [hes] at h; exact nomatch h
  | ok v =>
  rw [hes] at h
  dsimp only at h
  by_cases hv : mode.verified = true
  case neg =>
    rw [if_neg hv] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes,
      fun hv' => absurd hv' hv, h.symm⟩
  rw [if_pos hv] at h
  by_cases hz : (Level.zeronessOf v).equiv m.pw = true
  · rw [if_pos hz] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes, fun _ => hz, h.symm⟩
  · rw [if_neg hz] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Inversion for `ensureSortCore`: the subject whnfs to the sort. -/
theorem ensureSortCore_inv {env : Env} {fuel d : Nat} {t : Expr} {u : Level}
    (h : ensureSortCore mode env fuel d t = .ok u) :
    whnf mode env fuel d t = .ok (.sort u) := by
  unfold ensureSortCore ensureSort at h
  simp only [Bind.bind, Except.bind, whnf_def] at h
  cases hw : whnf mode env fuel d t with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  revert h
  match w with
  | .sort u' => ?_
  | .bvar _ | .fvar _ _ _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [h]

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

/-- Inversion for the let-rule of `inferTypeCore` (task #100 stage 6:
the official kernel's `infer_let` checks moved here from the deleted
annotation pass). -/
theorem inferTypeCore_letE_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty v b t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.letE n ty v b) = .ok t) :
    ∃ tty s tv, inferTypeCore mode env fuel d ty = .ok tty ∧
      ensureSortCore mode env fuel d tty = .ok s ∧
      inferTypeCore mode env fuel d v = .ok tv ∧
      isDefEqCore mode env fuel d tv ty = .ok true ∧
      inferTypeCore mode env fuel d (b.instantiate1 v) = .ok t := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeq_def, ensureSort_def] at h
  cases hty : inferTypeCore mode env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hes : ensureSortCore mode env fuel d tty with
  | error err => rw [hes] at h; exact nomatch h
  | ok s =>
  rw [hes] at h
  dsimp only at h
  cases htv : inferTypeCore mode env fuel d v with
  | error err => rw [htv] at h; exact nomatch h
  | ok tv =>
  rw [htv] at h
  dsimp only at h
  cases hde : isDefEqCore mode env fuel d tv ty with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  cases r with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
    simp only [↓reduceIte] at h
    exact ⟨tty, s, tv, rfl, hes, rfl, hde, h⟩

/-! ## Fuel-lifted inversions

The three inversions the native-pair projection's certificate walk
needs, in the form that walk consumes: stated at an arbitrary fuel
rather than at `fuel + 1`, by lifting the one-level forms through
`Verify/Mono.lean`.  (Task #100 introduced them for the walk that
replaced the collapse-refuted `PairMkFacts` domain clauses.)

Relocated here from `Setlec/Model/Core/Whnf.lean` (task #148, T3),
where they were `private`: they are V-free inversions of the checker,
which is what this module is for, and both the set model's proj case
and the `Setlec/SetR/*` bridge's R6 clause consume them.  Statements
unchanged. -/

theorem whnf_forallE_eq {env : Env} {fuel d : Nat} {n : Name}
    {t b e' : Expr} {mb : BinderMeta}
    (h : whnf mode env fuel d (.forallE n t b mb) = .ok e') :
    e' = .forallE n t b mb := by
  have h1 := whnf_mono (Nat.le_add_right fuel 2) h
  have h2 : whnf mode env (fuel + 2) d (.forallE n t b mb) =
      .ok (.forallE n t b mb) := by
    -- one iteration of the reduction loop suffices (task #106: the
    -- budget is `irreducible`, so peel it with its positivity witness)
    obtain ⟨k, hk⟩ := whnfLoopFuel_succ
    rw [whnf_succ]
    show whnfLoop (pureFns mode env (fuel + 1)) env d whnfLoopFuel _ = _
    rw [hk]
    rfl
  rw [h1] at h2
  exact Except.ok.inj h2

theorem inferTypeCore_app_inv' {env : Env} {fuel d : Nat}
    {f a t : Expr} (h : inferTypeCore mode env fuel d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m', inferTypeCore mode env fuel d f = .ok tf ∧
      whnf mode env fuel d tf = .ok (.forallE n' ty' body' m') ∧
      t = body'.instantiate1 a ∧
      ∃ ta, inferTypeCore mode env fuel d a = .ok ta ∧
        isDefEqCore mode env fuel d ta ty' = .ok true := by
  match fuel, h with
  | 0, h => rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    obtain ⟨tf, n', ty', body', m', h1, h2, h3, ta, h4, h5⟩ :=
      inferTypeCore_app_inv h
    exact ⟨tf, n', ty', body', m', inferTypeCore_mono (Nat.le_succ _) h1,
      whnf_mono (Nat.le_succ _) h2, h3, ta,
      inferTypeCore_mono (Nat.le_succ _) h4,
      isDefEqCore_mono (Nat.le_succ _) h5⟩

theorem inferTypeCore_const_inv {env : Env} {fuel d : Nat}
    {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCore mode env fuel d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      t = ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us := by
  match fuel, h with
  | 0, h => rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [inferTypeCore_succ] at h
    simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h
    revert h
    cases hf : env.find? n with
    | none =>
      intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    | some ci =>
      intro h
      dsimp only at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨ci, rfl, h.symm⟩
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Application-spine helpers -/

theorem getD_mem {α : Type _} {l : List α} {i : Nat} {dflt : α} (h : i < l.length) :
    l.getD i dflt ∈ l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [List.getD]
    | succ j =>
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih (by simpa using h))

theorem Expr.WScoped.getAppArgs {d : Nat} :
    ∀ {e : Expr}, WScoped d e → ∀ x ∈ e.getAppArgs, WScoped d x := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hw x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [WScoped] at hw
    rcases hx with hx | rfl
    · exact ihf hw.1 x hx
    · exact hw.2
  | _ => intro hw x hx; simp [Expr.getAppArgs] at hx

theorem Expr.WScoped.mkAppN {d : Nat} : ∀ {xs : List Expr} {f : Expr},
    WScoped d f → (∀ x ∈ xs, WScoped d x) → WScoped d (Expr.mkAppN f xs) := by
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hxs
    simp only [Expr.mkAppN]
    refine ih ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [WScoped]
    exact ⟨hf, hxs x List.mem_cons_self⟩

theorem looseBVarsBounded_getAppFn {k : Nat} :
    ∀ {e : Expr}, e.looseBVarsBounded k = true →
      e.getAppFn.looseBVarsBounded k = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ihf hb.1
  | _ => intro hb; exact hb

theorem looseBVarsBounded_getAppArgs {k : Nat} :
    ∀ {e : Expr}, e.looseBVarsBounded k = true →
      ∀ x ∈ e.getAppArgs, x.looseBVarsBounded k = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hb x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rcases hx with hx | rfl
    · exact ihf hb.1 x hx
    · exact hb.2
  | _ => intro hb x hx; simp [Expr.getAppArgs] at hx

theorem hasFvar_getAppArgs :
    ∀ {e : Expr}, e.hasFvar = false →
      ∀ x ∈ e.getAppArgs, x.hasFvar = false := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hb x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hb
    rcases hx with hx | rfl
    · exact ihf hb.1 x hx
    · exact hb.2
  | _ => intro hb x hx; simp [Expr.getAppArgs] at hx

theorem Expr.mkAppN_append_one (f : Expr) (l : List Expr) (a : Expr) :
    Expr.mkAppN f (l ++ [a]) = .app (Expr.mkAppN f l) a := by
  induction l generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, Expr.mkAppN]; exact ih _

/-- An expression is its spine head applied to its spine arguments. -/
theorem Expr.mkAppN_getApp : ∀ (e : Expr), Expr.mkAppN e.getAppFn e.getAppArgs = e := by
  intro e
  induction e with
  | app f a ih _ =>
    simp only [Expr.getAppFn, Expr.getAppArgs]
    rw [Expr.mkAppN_append_one]
    exact congrArg (Expr.app · a) ih
  | _ => rfl

/-- The spine head of an application chain is the base's spine head. -/
theorem Expr.getAppFn_mkAppN : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      Expr.getAppFn_mkAppN as]
    rfl

/-- The spine arguments of an application chain extend the base's. -/
theorem Expr.getAppArgs_mkAppN : ∀ (args : List Expr) (f : Expr),
    (Expr.mkAppN f args).getAppArgs = f.getAppArgs ++ args
  | [], _ => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [show Expr.mkAppN f (a :: as) = Expr.mkAppN (.app f a) as from rfl,
      Expr.getAppArgs_mkAppN as]
    simp [Expr.getAppArgs]

theorem List.length_four {α : Type _} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem List.length_two {α : Type _} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- Inversion for `whnfCore` on projections: the scrutinee whnf, then
the string-literal expansion step (`projLitToCtorP`), then either a
stuck projection of the converted scrutinee or a firing table entry. -/
theorem whnf_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat} {e e' : Expr}
    (h : whnfCore mode env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂ e₃, whnf mode env fuel d e = .ok e₂ ∧
      projLitToCtorP mode env fuel d e₂ = .ok e₃ ∧
      (e' = .proj sn i e₃ ∨
        ∃ us entry, e₃.getAppFn = .const entry.ctor us ∧
          env.findProj? sn i = some entry ∧ entry.native = true ∧
          i < entry.numFields ∧
          e₃.getAppArgs.length = entry.numParams + entry.numFields ∧
          us.length = entry.levelParams.length ∧
          whnfCore mode env fuel d
            (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)) = .ok e' ∧
          projCertP mode env fuel d e₃ i entry.numParams = .ok true) := by
  rw [whnfCore_succ] at h
  simp only [whnfCoreBody, Bind.bind, Except.bind] at h
  simp only [whnfCore_def, whnf_def, projCert_fold,
    projLitToCtor_fold] at h
  cases he : whnf mode env fuel d e with
  | error err => rw [he] at h; exact nomatch h
  | ok e₂ =>
  rw [he] at h
  dsimp only at h
  cases hlit : projLitToCtorP mode env fuel d e₂ with
  | error err => rw [hlit] at h; exact nomatch h
  | ok e₃ =>
  rw [hlit] at h
  dsimp only at h
  refine ⟨e₂, e₃, rfl, hlit, ?_⟩
  cases hfp : env.findProj? sn i with
  | none => rw [hfp] at h; exact Or.inl (Except.ok.inj h).symm
  | some entry =>
  rw [hfp] at h
  dsimp only at h
  cases hfn : e₃.getAppFn with
  | const c us =>
    rw [hfn] at h
    dsimp only at h
    split at h
    next hcond =>
      obtain ⟨hnat, rfl, hi, hlen, hus⟩ := hcond
      try simp only [Bind.bind, Except.bind] at h
      try dsimp only at h
      cases hcert : projCertP mode env fuel d e₃ i entry.numParams with
      | error err => rw [hcert] at h; exact nomatch h
      | ok b =>
      rw [hcert] at h
      cases b with
      | true =>
        simp only [if_true] at h
        try dsimp only at h
        exact Or.inr ⟨us, entry, rfl, rfl, hnat, hi, hlen, hus, h, hcert⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact Or.inl (Except.ok.inj h).symm
    next hcond =>
      exact Or.inl (Except.ok.inj h).symm
  | bvar i2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | sort u => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | fvar i2 n2 t2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | app f2 a2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | lam n2 t2 b2 m2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | forallE n2 t2 b2 m2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | letE n2 t2 v2 b2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | lit l2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | proj s2 i2 e3 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm

/-- Inversion for a successful projection certification.

Task #161 de-gating item B1 (harvest site 18 / list entry P9): the
clause's four sort legs — the two `infer`+`whnf`-to-a-sort runs and the
two `Level.isEquiv` comparisons — are deleted, so the inversion now
delivers exactly the two `inferTypeCore` runs the clause still makes.
Conjunct 5 of the old statement (the subject's own run) is the only one
`projStepP_of_claims` ever consumed; the field's run is kept because it
is still performed (the ratified negative verdict of the harvest
list). -/
theorem projCert_inv {env : Env} {fuel d : Nat} {e₂ : Expr} {i : Nat}
    {nP : Nat}
    (h : projCertP mode env fuel d e₂ i nP = .ok true) :
    ∃ ta te,
      inferTypeCore mode env fuel d (e₂.getAppArgs.getD (nP + i) (.bvar 0))
        = .ok ta ∧
      inferTypeCore mode env fuel d e₂ = .ok te := by
  dsimp only [projCertP] at h
  simp only [projCert, Bind.bind, Except.bind] at h
  simp only [infer_def] at h
  cases hta : inferTypeCore mode env fuel d
      (e₂.getAppArgs.getD (nP + i) (.bvar 0)) with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hte : inferTypeCore mode env fuel d e₂ with
  | error err => rw [hte] at h; exact nomatch h
  | ok te =>
  exact ⟨ta, te, rfl, rfl⟩

/-- Inversion of a successful iota step. -/
theorem iotaRec_inv {env : Env} {fuel d : Nat} {e eout : Expr}
    (h : iotaRecP mode env fuel d e = .ok (some eout)) :
    ∃ c us cv mI rP rules major₀ major₁ major cj usj cvj cnP cnF r cbinders
      cbody residual cr usr,
      e.getAppFn = .const c us ∧
      env.find? c = some (.recInfo cv mI rP rules) ∧
      e.getAppArgs.length = mI + 1 ∧
      us.length = cv.levelParams.length ∧
      whnf mode env fuel d (e.getAppArgs.getD mI (.bvar 0)) =
        .ok major₀ ∧
      litMajorToCtorP mode env fuel d major₀ = .ok major₁ ∧
      majorToCtorP mode env fuel d c rules major₁ = .ok major ∧
      major.getAppFn = .const cj usj ∧
      env.find? cj = some (.ctorInfo cvj cnP cnF) ∧
      rules.find? (fun r' => r'.ctor == cj) = some r ∧
      major.getAppArgs.length = r.ctorParams + r.nfields ∧
      (cv.type.stripPis (mI + 1)).isSome = true ∧
      (cvj.type.stripPis (r.ctorParams + r.nfields)).isSome = true ∧
      r.fire ≠ .inert ∧
      Level.isEquivList usj
        (recFireComparands r cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = some true ∧
      defEqListP mode env fuel d (major.getAppArgs.take r.ctorParams)
        (recFireComparands r cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2 = .ok true ∧
      iotaCertsP mode env fuel d (cv.type.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take mI ++ [major]) = .ok true ∧
      iotaCertsP mode env fuel d (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = .ok true ∧
      (cvj.type.instantiateLevelParams cvj.levelParams usj).stripPis
        (r.ctorParams + r.nfields) = some (cbinders, cbody) ∧
      piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = some residual ∧
      cbody.getAppFn = .const cr usr ∧
      defEqListP mode env fuel d (residual.getAppArgs.drop r.ctorParams)
        ((e.getAppArgs.take mI).drop rP) =
        .ok true ∧
      eout = Expr.mkAppN (r.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++
          major.getAppArgs.drop r.ctorParams) := by
  dsimp only [iotaRecP] at h
  simp only [iotaRec, Bind.bind, Except.bind] at h
  simp only [whnf_def, majorToCtor_fold, litMajorToCtor_fold, defEqList_fold,
    iotaCerts_fold] at h
  revert h
  cases hfn : e.getAppFn with
  | bvar i => intro h; exact nomatch h
  | fvar i n ty => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | app f a => intro h; exact nomatch h
  | lam n ty body m => intro h; exact nomatch h
  | forallE n ty body m => intro h; exact nomatch h
  | letE n ty v body => intro h; exact nomatch h
  | lit l => intro h; exact nomatch h
  | proj sn i pe => intro h; exact nomatch h
  | const c us =>
  intro h
  dsimp only at h
  revert h
  match hfc : env.find? c with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo cv mI rP rules) => ?_
  intro h
  dsimp only at h
  by_cases hlen : e.getAppArgs.length = mI + 1 ∧
      us.length = cv.levelParams.length
  case neg => rw [if_neg hlen] at h; exact nomatch h
  rw [if_pos hlen] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hmaj : whnf mode env fuel d
      (e.getAppArgs.getD mI (.bvar 0)) with
  | error err => rw [hmaj] at h; exact nomatch h
  | ok major₀ =>
  rw [hmaj] at h
  dsimp only at h
  cases hlit : litMajorToCtorP mode env fuel d major₀ with
  | error err => rw [hlit] at h; exact nomatch h
  | ok major₁ =>
  rw [hlit] at h
  dsimp only at h
  cases hsub : majorToCtorP mode env fuel d c rules major₁ with
  | error err => rw [hsub] at h; exact nomatch h
  | ok major =>
  rw [hsub] at h
  dsimp only at h
  revert h
  cases hmfn : major.getAppFn with
  | bvar i => intro h; exact nomatch h
  | fvar i n ty => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | app f a => intro h; exact nomatch h
  | lam n ty body m => intro h; exact nomatch h
  | forallE n ty body m => intro h; exact nomatch h
  | letE n ty v body => intro h; exact nomatch h
  | lit l => intro h; exact nomatch h
  | proj sn i pe => intro h; exact nomatch h
  | const cj usj =>
  intro h
  dsimp only at h
  revert h
  match hfj : env.find? cj with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) => ?_
  intro h
  dsimp only at h
  revert h
  cases hrule : rules.find? (fun r' => r'.ctor == cj) with
  | none => intro h; exact nomatch h
  | some r =>
  intro h
  dsimp only at h
  by_cases hml : major.getAppArgs.length = r.ctorParams + r.nfields
  case neg => rw [if_neg hml] at h; exact nomatch h
  rw [if_pos hml] at h
  try simp only [Bind.bind, Except.bind] at h
  by_cases hplain0 : r.fire = .inert
  case pos => rw [if_pos hplain0] at h; exact nomatch h
  rw [if_neg hplain0] at h
  try simp only [Bind.bind, Except.bind] at h
  by_cases harities : (cv.type.stripPis (mI + 1)).isSome = true ∧
      (cvj.type.stripPis (r.ctorParams + r.nfields)).isSome = true
  case neg => rw [if_neg harities] at h; exact nomatch h
  obtain ⟨har1, har2⟩ := harities
  rw [if_pos ⟨har1, har2⟩] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hlev : Level.isEquivList usj
      (recFireComparands r cv.levelParams us cvj.levelParams
        e.getAppArgs rP).1 with
  | none => rw [hlev] at h; simp [liftFueled] at h
  | some bl =>
  rw [hlev] at h
  simp only [liftFueled, pure, Except.pure] at h
  try dsimp only at h
  cases bl with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hpeq : defEqListP mode env fuel d (major.getAppArgs.take r.ctorParams)
      (recFireComparands r cv.levelParams us cvj.levelParams e.getAppArgs rP).2 with
  | error err => rw [hpeq] at h; exact nomatch h
  | ok rp =>
  rw [hpeq] at h
  dsimp only at h
  cases rp with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hcerts : iotaCertsP mode env fuel d
      (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take mI ++ [major]) with
  | error err => rw [hcerts] at h; exact nomatch h
  | ok rc =>
  rw [hcerts] at h
  dsimp only at h
  cases rc with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hmcerts : iotaCertsP mode env fuel d
      (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs with
  | error err => rw [hmcerts] at h; exact nomatch h
  | ok rmc =>
  rw [hmcerts] at h
  dsimp only at h
  cases rmc with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  revert h
  cases hstrip : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).stripPis (r.ctorParams + r.nfields) with
  | none => intro h; exact nomatch h
  | some pr =>
  obtain ⟨cbinders, cbody⟩ := pr
  cases hres : piResidual
      (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs with
  | none => intro h; exact nomatch h
  | some residual =>
  intro h
  dsimp only at h
  revert h
  cases hrfn : cbody.getAppFn with
  | bvar i => intro h; exact nomatch h
  | fvar i n ty => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | app f a => intro h; exact nomatch h
  | lam n ty body m => intro h; exact nomatch h
  | forallE n ty body m => intro h; exact nomatch h
  | letE n ty v body => intro h; exact nomatch h
  | lit l => intro h; exact nomatch h
  | proj sn i pe => intro h; exact nomatch h
  | const cr usr =>
  intro h
  dsimp only at h
  try simp only [Bind.bind, Except.bind] at h
  cases hieq : defEqListP mode env fuel d (residual.getAppArgs.drop r.ctorParams)
      ((e.getAppArgs.take mI).drop rP) with
  | error err => rw [hieq] at h; exact nomatch h
  | ok ri =>
  rw [hieq] at h
  dsimp only at h
  cases ri with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq,
    Option.some.injEq] at h
  exact ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj, cvj, cnP,
    cnF, r, cbinders, cbody, residual, cr, usr, rfl, hfc, hlen.1, hlen.2,
    hmaj, hlit,
    hsub, hmfn, hfj, hrule, hml, har1, har2, hplain0, hlev, hpeq, hcerts,
    hmcerts, hstrip, hres, hrfn, hieq, h.symm⟩

/-- Inversion of the stuck-major rescue: either the major is returned
unchanged, or a constructor application was fabricated — in the
K branch certified by proof irrelevance, in the structure-eta branch by
the structure-eta certificate (or, at zero fields, by proof
irrelevance) — and its scoping was checked syntactically (the scope
guard). -/
theorem majorToCtor_inv {env : Env} {fuel d : Nat} {recName : Name}
    {rules : List RecRule} {major major' : Expr}
    (h : majorToCtorP mode env fuel d recName rules major = .ok major') :
    major' = major ∨
    (major'.wscopedB d = true ∧ major'.looseBVarsBounded 0 = true ∧
     major'.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true ∧
     ∃ rl cvj cnP cnF tmaj₀ tmaj T us₀ ust cvT caps,
       rules = [rl] ∧
       env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) ∧
       (cvj.type.piResult).getAppFn = .const T us₀ ∧
       env.find? T = some (.indInfo cvT caps) ∧
       inferTypeCore mode env fuel d major = .ok tmaj₀ ∧
       whnf mode env fuel d tmaj₀ = .ok tmaj ∧
       tmaj.getAppFn = .const T ust ∧
       ((caps.ruleK = true ∧ cnF = 0 ∧
         cvj.levelParams.length = ust.length ∧
         cnP ≤ tmaj.getAppArgs.length ∧
         (cvj.type.stripPis cnP).isSome = true ∧
         major' = Expr.mkAppN (.const rl.ctor ust)
           (tmaj.getAppArgs.take cnP) ∧
         iotaCertsP mode env fuel d
           (cvj.type.instantiateLevelParams cvj.levelParams ust)
           (tmaj.getAppArgs.take cnP) = .ok true ∧
         (∃ tfab, inferTypeCore mode env fuel d major' = .ok tfab ∧
           isDefEqCore mode env fuel d tmaj tfab = .ok true) ∧
         proofIrrelP mode env fuel d major' major = .ok true) ∨
        (caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
         Name.isProjFnShape recName = false ∧
         piResultNeverZero cvT.levelParams ust cvT.type = true ∧
         tmaj.getAppArgs.length = caps.etaParams ∧
         ust.length = cvT.levelParams.length ∧
         cvj.levelParams.length = ust.length ∧
         (cvj.type.stripPis
           (caps.etaParams + caps.etaFields)).isSome = true ∧
         major' = Expr.mkAppN (.const caps.etaCtor ust)
           (etaFabArgs T ust tmaj.getAppArgs major caps.etaFields) ∧
         iotaCertsP mode env fuel d
           (cvj.type.instantiateLevelParams cvj.levelParams ust)
           (etaFabArgs T ust tmaj.getAppArgs major caps.etaFields)
           = .ok true ∧
         (structEtaCertWithP mode env fuel d major' major tmaj = .ok true ∨
          (caps.etaFields = 0 ∧ cvj.levelParams.length = ust.length ∧
           proofIrrelP mode env fuel d major' major = .ok true))))) := by
  dsimp only [majorToCtorP] at h
  simp only [majorToCtor, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeq_def, proofIrrel_fold,
    iotaCerts_fold, structEtaCertWith_fold] at h
  revert h
  cases hca : isCtorApp env major with
  | true =>
    intro h
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  match hrs : rules with
  | [] =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | _ :: _ :: _ =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | [rl] =>
  intro h
  dsimp only at h
  revert h
  match hfj : env.find? rl.ctor with
  | none =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _ _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _)
  | some (.projInfo _) =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.ctorInfo cvj cnP cnF) =>
  intro h
  dsimp only at h
  revert h
  match hpr : (cvj.type.piResult).getAppFn with
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | .const T us₀ =>
  intro h
  dsimp only at h
  revert h
  match hfT : env.find? T with
  | none =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _ _)
  | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _)
  | some (.projInfo _) =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.indInfo cvT caps) =>
  intro h
  dsimp only at h
  by_cases hK : caps.ruleK = true ∧ cnF = 0
  · rw [if_pos hK] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hti : inferTypeCore mode env fuel d major with
    | error err => rw [hti] at h; exact nomatch h
    | ok tmaj₀ =>
    rw [hti] at h
    dsimp only at h
    cases htw : whnf mode env fuel d tmaj₀ with
    | error err => rw [htw] at h; exact nomatch h
    | ok tmaj =>
    rw [htw] at h
    dsimp only at h
    revert h
    cases hth : tmaj.getAppFn with
    | bvar i =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | fvar i n ty =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | sort u =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | app f a =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lam n ty body m =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | forallE n ty body m =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | letE n ty v body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lit l =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | proj sn i pe =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | const T' ust =>
    intro h
    dsimp only at h
    by_cases hTl : T' = T ∧ cvj.levelParams.length = ust.length
    case neg =>
      rw [if_neg hTl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    obtain ⟨rfl, hlvl⟩ := hTl
    rw [if_pos ⟨rfl, hlvl⟩] at h
    by_cases harK : cnP ≤ tmaj.getAppArgs.length ∧
        (cvj.type.stripPis cnP).isSome = true
    case neg =>
      rw [if_neg harK] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    obtain ⟨harK1, harK2⟩ := harK
    rw [if_pos ⟨harK1, harK2⟩] at h
    cases hguard : (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)).wscopedB d &&
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)).looseBVarsBounded 0 &&
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)).fvarLeaves.all
          (fun l => major.fvarLeaves.contains l) with
    | false =>
      rw [hguard] at h
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    rw [hguard] at h
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hcertK : iotaCertsP mode env fuel d
        (cvj.type.instantiateLevelParams cvj.levelParams ust)
        (tmaj.getAppArgs.take cnP) with
    | error err => rw [hcertK] at h; exact nomatch h
    | ok bck =>
    rw [hcertK] at h
    dsimp only at h
    cases bck with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases htf : inferTypeCore mode env fuel d
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)) with
    | error err => rw [htf] at h; exact nomatch h
    | ok tfab =>
    rw [htf] at h
    dsimp only at h
    cases hdeq : isDefEqCore mode env fuel d tmaj tfab with
    | error err => rw [hdeq] at h; exact nomatch h
    | ok bde =>
    rw [hdeq] at h
    dsimp only at h
    cases bde with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hpi : proofIrrelP mode env fuel d
        (Expr.mkAppN (.const rl.ctor ust)
          (tmaj.getAppArgs.take cnP)) major with
    | error err => rw [hpi] at h; exact nomatch h
    | ok bpi =>
    rw [hpi] at h
    dsimp only at h
    cases bpi with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hguard
    exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
      rl, cvj, cnP, cnF, tmaj₀, tmaj, T', us₀, ust, cvT, caps,
      rfl, hfj, hpr, hfT, rfl, htw, hth,
      Or.inl ⟨hK.1, hK.2, hlvl, harK1, harK2, rfl, hcertK,
        ⟨tfab, htf, hdeq⟩, hpi⟩⟩
  · rw [if_neg hK] at h
    by_cases hE : caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
        Name.isProjFnShape recName = false
    case neg =>
      rw [if_neg hE] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    rw [if_pos hE] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hti : inferTypeCore mode env fuel d major with
    | error err => rw [hti] at h; exact nomatch h
    | ok tmaj₀ =>
    rw [hti] at h
    dsimp only at h
    cases htw : whnf mode env fuel d tmaj₀ with
    | error err => rw [htw] at h; exact nomatch h
    | ok tmaj =>
    rw [htw] at h
    dsimp only at h
    revert h
    cases hth : tmaj.getAppFn with
    | bvar i =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | fvar i n ty =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | sort u =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | app f a =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lam n ty body m =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | forallE n ty body m =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | letE n ty v body =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | lit l =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | proj sn i pe =>
      intro h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | const T' ust =>
    intro h
    dsimp only at h
    by_cases hTl : T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        piResultNeverZero cvT.levelParams ust cvT.type = true
    case neg =>
      rw [if_neg hTl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    obtain ⟨rfl, hplen, hlvl, hnz⟩ := hTl
    rw [if_pos ⟨rfl, hplen, hlvl, hnz⟩] at h
    by_cases harE : cvj.levelParams.length = ust.length ∧
        (cvj.type.stripPis
          (caps.etaParams + caps.etaFields)).isSome = true
    case neg =>
      rw [if_neg harE] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    obtain ⟨harE1, harE2⟩ := harE
    rw [if_pos ⟨harE1, harE2⟩] at h
    cases hguard : (Expr.mkAppN (.const caps.etaCtor ust)
          (etaFabArgs T' ust tmaj.getAppArgs major
            caps.etaFields)).wscopedB d &&
        (Expr.mkAppN (.const caps.etaCtor ust)
          (etaFabArgs T' ust tmaj.getAppArgs major
            caps.etaFields)).looseBVarsBounded 0 &&
        (Expr.mkAppN (.const caps.etaCtor ust)
          (etaFabArgs T' ust tmaj.getAppArgs major
            caps.etaFields)).fvarLeaves.all
          (fun l => major.fvarLeaves.contains l) with
    | false =>
      rw [hguard] at h
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    rw [hguard] at h
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hcertE : iotaCertsP mode env fuel d
        (cvj.type.instantiateLevelParams cvj.levelParams ust)
        (etaFabArgs T' ust tmaj.getAppArgs major caps.etaFields) with
    | error err => rw [hcertE] at h; exact nomatch h
    | ok bce =>
    rw [hcertE] at h
    dsimp only at h
    cases bce with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hse : structEtaCertWithP mode env fuel d
        (Expr.mkAppN (.const caps.etaCtor ust)
          (etaFabArgs T' ust tmaj.getAppArgs major caps.etaFields))
        major tmaj with
    | error err => rw [hse] at h; exact nomatch h
    | ok bse =>
    rw [hse] at h
    dsimp only at h
    cases bse with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      by_cases hZ : caps.etaFields = 0 ∧
          cvj.levelParams.length = ust.length
      case neg =>
        rw [if_neg hZ] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      rw [if_pos hZ] at h
      try simp only [Bind.bind, Except.bind] at h
      cases hpi : proofIrrelP mode env fuel d
          (Expr.mkAppN (.const caps.etaCtor ust)
            (etaFabArgs T' ust tmaj.getAppArgs major caps.etaFields))
          major with
      | error err => rw [hpi] at h; exact nomatch h
      | ok bpi =>
      rw [hpi] at h
      dsimp only at h
      cases bpi with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inl h.symm
      | true =>
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hguard
      exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
        rl, cvj, cnP, cnF, tmaj₀, tmaj, T', us₀, ust, cvT, caps,
        rfl, hfj, hpr, hfT, rfl, htw, hth,
        Or.inr ⟨hE.1, hE.2.1, hE.2.2, hnz, hplen, hlvl,
          harE1, harE2, rfl, hcertE,
          Or.inr ⟨hZ.1, hZ.2, hpi⟩⟩⟩
    | true =>
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hguard
    exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
      rl, cvj, cnP, cnF, tmaj₀, tmaj, T', us₀, ust, cvT, caps,
      rfl, hfj, hpr, hfT, rfl, htw, hth,
      Or.inr ⟨hE.1, hE.2.1, hE.2.2, hnz, hplen, hlvl,
        harE1, harE2, rfl, hcertE,
        Or.inl hse⟩⟩

/-- Inversion of one pairwise-defeq step. -/
theorem defEqList_step_inv {env : Env} {fuel d : Nat} {a b : Expr}
    {as bs : List Expr}
    (h : defEqListP mode env fuel d (a :: as) (b :: bs) = .ok true) :
    isDefEqCore mode env fuel d a b = .ok true ∧
    defEqListP mode env fuel d as bs = .ok true := by
  dsimp only [defEqListP] at h
  simp only [defEqList, Bind.bind, Except.bind] at h
  simp only [defeq_def, defEqList_fold] at h
  cases hde : isDefEqCore mode env fuel d a b with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨rfl, h⟩

/-- Inversion of the lazy delta same-head spine congruence: both sides
are applications of the same constant, at pointwise-equivalent levels,
with pairwise definitionally equal spines of equal length. -/
theorem defeqSpine_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : defeqSpineP mode env fuel d a b = .ok true) :
    ∃ n us us', a.getAppFn = .const n us ∧ b.getAppFn = .const n us' ∧
      a.getAppArgs.length = b.getAppArgs.length ∧
      Level.isEquivList us us' = some true ∧
      defEqListP mode env fuel d a.getAppArgs b.getAppArgs = .ok true := by
  dsimp only [defeqSpineP] at h
  simp only [defeqSpine, defEqList_fold] at h
  revert h
  match hfa : a.getAppFn with
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [pure, Except.pure] at h
  | .const n us => ?_
  intro h
  dsimp only at h
  revert h
  match hfb : b.getAppFn with
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [pure, Except.pure] at h
  | .const n' us' => ?_
  intro h
  dsimp only at h
  revert h
  split
  case isTrue hcond =>
    obtain ⟨rfl, hlen⟩ := hcond
    intro h
    revert h
    match hlev : Level.isEquivList us us' with
    | some true => intro h; exact ⟨n, us, us', rfl, rfl, hlen, hlev, h⟩
    | some false => intro h; simp [pure, Except.pure] at h
    | none => intro h; simp [pure, Except.pure] at h
  case isFalse =>
    intro h; simp [pure, Except.pure] at h

/-- Inversion of one certification step. -/
theorem iotaCerts_step_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty body : Expr} {m : BinderMeta} {arg : Expr} {rest : List Expr}
    (h : iotaCertsP mode env fuel d (.forallE n ty body m) (arg :: rest) =
      .ok true) :
    ∃ ta, inferTypeCore mode env fuel d arg = .ok ta ∧
      isDefEqCore mode env fuel d ta ty = .ok true ∧
      iotaCertsP mode env fuel d (body.instantiate1 arg) rest = .ok true := by
  dsimp only [iotaCertsP] at h
  simp only [iotaCerts, Bind.bind, Except.bind] at h
  simp only [infer_def, defeq_def, iotaCerts_fold] at h
  cases hta : inferTypeCore mode env fuel d arg with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore mode env fuel d ta ty with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨ta, rfl, hde, h⟩

/-- Inversion of the unit-type check.

Task #161 item C1: the test is now the pinned-name one, so the
inversion additionally reads off `c = punitName` — the conclusion is
unchanged (`reservedBasisNames.contains (punitName.str "rec")` is
`true` by computation), which is what keeps `unitLike_eq_punit` and
every downstream consumer working verbatim. -/
theorem isUnitLikeTy_inv {env : Env} {e : Expr}
    (h : isUnitLikeTy env e = true) :
    ∃ c us cvi capsi cvr mI rP r, e = .const c us ∧
      env.find? c = some (.indInfo cvi capsi) ∧
      env.find? (c.str "rec") = some (.recInfo cvr mI rP [r]) ∧
      mI = rP ∧ r.nfields = 0 ∧
      reservedBasisNames.contains (c.str "rec") = true := by
  match e, h with
  | .const c us, h =>
    simp only [isUnitLikeTy, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hc, h1⟩, h2⟩ := h
    subst hc
    revert h1
    match hfc : env.find? punitName with
    | none => intro h1; exact nomatch h1
    | some (.axiomInfo _) => intro h1; exact nomatch h1
    | some (.projInfo _) => intro h1; exact nomatch h1
    | some (.defnInfo _ _ _) => intro h1; exact nomatch h1
    | some (.thmInfo _ _) => intro h1; exact nomatch h1
    | some (.ctorInfo _ _ _) => intro h1; exact nomatch h1
    | some (.recInfo _ _ _ _) => intro h1; exact nomatch h1
    | some (.indInfo cvi capsi) => ?_
    intro _
    revert h2
    match hfr : env.find? punitRecName with
    | none => intro h2; exact nomatch h2
    | some (.axiomInfo _) => intro h2; exact nomatch h2
    | some (.projInfo _) => intro h2; exact nomatch h2
    | some (.defnInfo _ _ _) => intro h2; exact nomatch h2
    | some (.thmInfo _ _) => intro h2; exact nomatch h2
    | some (.ctorInfo _ _ _) => intro h2; exact nomatch h2
    | some (.indInfo _ _) => intro h2; exact nomatch h2
    | some (.recInfo cvr mI rP rules) => ?_
    intro h2
    match rules, h2 with
    | [r], h2 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨punitName, us, cvi, capsi, cvr, mI, rP, r, rfl, hfc, hfr,
        h2.1, h2.2, by decide⟩
    | [], h2 => exact nomatch h2
    | _ :: _ :: _, h2 => exact nomatch h2

/-- Inversion of a successful proof-irrelevance certification: either
both sides' types whnf to the basis unit type, or both types' sorts are
`Prop`. -/
theorem proofIrrel_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : proofIrrelP mode env fuel d a b = .ok true) :
    ∃ ta wta,
      inferTypeCore mode env fuel d a = .ok ta ∧
      whnf mode env fuel d ta = .ok wta ∧
      ((isUnitLikeTy env wta = true ∧
        ∃ tb wtb, inferTypeCore mode env fuel d b = .ok tb ∧
          whnf mode env fuel d tb = .ok wtb ∧ isUnitLikeTy env wtb = true) ∨
       (∃ sta uT tb stb vT,
        inferTypeCore mode env fuel d ta = .ok sta ∧
        whnf mode env fuel d sta = .ok (.sort uT) ∧
        Level.isEquiv uT .zero = some true ∧
        inferTypeCore mode env fuel d b = .ok tb ∧
        inferTypeCore mode env fuel d tb = .ok stb ∧
        whnf mode env fuel d stb = .ok (.sort vT) ∧
        Level.isEquiv vT .zero = some true)) := by
  dsimp only [proofIrrelP] at h
  simp only [proofIrrel, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def] at h
  cases hta : inferTypeCore mode env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hwta0 : whnf mode env fuel d ta with
  | error err => rw [hwta0] at h; exact nomatch h
  | ok wta0 =>
  rw [hwta0] at h
  dsimp only at h
  refine ⟨ta, wta0, rfl, hwta0, ?_⟩
  by_cases hu : isUnitLikeTy env wta0 = true
  · -- unit branch
    rw [if_pos hu] at h
    try simp only [Bind.bind, Except.bind] at h
    cases htb : inferTypeCore mode env fuel d b with
    | error err => rw [htb] at h; exact nomatch h
    | ok tb =>
    rw [htb] at h
    dsimp only at h
    cases hwtb : whnf mode env fuel d tb with
    | error err => rw [hwtb] at h; exact nomatch h
    | ok wtb =>
    rw [hwtb] at h
    dsimp only at h
    by_cases hub : isUnitLikeTy env wtb = true
    · exact Or.inl ⟨hu, tb, wtb, rfl, hwtb, hub⟩
    · rw [if_neg hub] at h
      simp [pure, Except.pure] at h
  · -- Prop branch
    rw [if_neg hu] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hsta : inferTypeCore mode env fuel d ta with
    | error err => rw [hsta] at h; exact nomatch h
    | ok sta =>
    rw [hsta] at h
    dsimp only at h
    cases hwta : whnf mode env fuel d sta with
    | error err => rw [hwta] at h; exact nomatch h
    | ok wta =>
    rw [hwta] at h
    match wta, h with
    | .sort uT, h => ?_
    | .bvar i2, h => exact nomatch h
    | .fvar i2 n2 t2, h => exact nomatch h
    | .const n2 us2, h => exact nomatch h
    | .app f2 a2, h => exact nomatch h
    | .lam n2 t2 b2 m2, h => exact nomatch h
    | .forallE n2 t2 b2 m2, h => exact nomatch h
    | .letE n2 t2 v2 b2, h => exact nomatch h
    | .lit l2, h => exact nomatch h
    | .proj s2 i2 e3, h => exact nomatch h
    dsimp only at h
    cases heq1 : Level.isEquiv uT .zero with
    | none => rw [heq1] at h; simp [liftFueled] at h
    | some okA =>
    rw [heq1] at h
    try dsimp only [liftFueled] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    cases htb : inferTypeCore mode env fuel d b with
    | error err => rw [htb] at h; exact nomatch h
    | ok tb =>
    rw [htb] at h
    dsimp only at h
    cases hstb : inferTypeCore mode env fuel d tb with
    | error err => rw [hstb] at h; exact nomatch h
    | ok stb =>
    rw [hstb] at h
    dsimp only at h
    cases hwtb : whnf mode env fuel d stb with
    | error err => rw [hwtb] at h; exact nomatch h
    | ok wtb =>
    rw [hwtb] at h
    match wtb, h with
    | .sort vT, h => ?_
    | .bvar i2, h => exact nomatch h
    | .fvar i2 n2 t2, h => exact nomatch h
    | .const n2 us2, h => exact nomatch h
    | .app f2 a2, h => exact nomatch h
    | .lam n2 t2 b2 m2, h => exact nomatch h
    | .forallE n2 t2 b2 m2, h => exact nomatch h
    | .letE n2 t2 v2 b2, h => exact nomatch h
    | .lit l2, h => exact nomatch h
    | .proj s2 i2 e3, h => exact nomatch h
    dsimp only at h
    cases heq2 : Level.isEquiv vT .zero with
    | none => rw [heq2] at h; simp [liftFueled] at h
    | some okB =>
    rw [heq2] at h
    try dsimp only [liftFueled] at h
    try simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ : okA = true ∧ okB = true := by
      have := h
      cases okA <;> cases okB <;> simp_all
    exact Or.inr ⟨sta, uT, tb, stb, vT, rfl, hwta, heq1, rfl, hstb, hwtb, heq2⟩

/-- Inversion of a successful pair-eta certification.

Task #161 de-gating item A (harvest site 23): the former last conjunct
— task #130's parameter-telescope certification, delivered only under
`mode.ttChecks = true` and therefore vacuous since #148 T7b — is gone
with the code that produced it. -/
theorem pairEtaCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : pairEtaCertP mode env fuel d a b = .ok true) :
    ∃ c us pα pβ s₁ s₂ cvm tb c' us' A B cvi capsi cvr mI rP rr,
      a = .app (.app (.app (.app (.const c us) pα) pβ) s₁) s₂ ∧
      env.find? c = some (.ctorInfo cvm 2 2) ∧
      inferTypeCore mode env fuel d b = .ok tb ∧
      whnf mode env fuel d tb = .ok (.app (.app (.const c' us') A) B) ∧
      env.find? c' = some (.indInfo cvi capsi) ∧
      env.find? (c'.str "rec") = some (.recInfo cvr mI rP [rr]) ∧
      rr.ctor = c ∧ rr.nfields = 2 ∧ mI = rP ∧
      reservedBasisNames.contains (c'.str "rec") = true ∧
      Level.isEquivList us us' = some true ∧
      isDefEqCore mode env fuel d pα A = .ok true ∧
      isDefEqCore mode env fuel d pβ B = .ok true ∧
      isDefEqCore mode env fuel d s₁ (.proj c' 0 b) = .ok true ∧
      isDefEqCore mode env fuel d s₂ (.proj c' 1 b) = .ok true := by
  dsimp only [pairEtaCertP] at h
  simp only [pairEtaCert, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeq_def] at h
  revert h
  match a with
  | .app (.app (.app (.app (.const c us) pα) pβ) s₁) s₂ => ?_
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .const _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .app (.bvar _) _ => intro h; exact nomatch h
  | .app (.fvar _ _ _) _ => intro h; exact nomatch h
  | .app (.sort _) _ => intro h; exact nomatch h
  | .app (.const _ _) _ => intro h; exact nomatch h
  | .app (.lam _ _ _ _) _ => intro h; exact nomatch h
  | .app (.forallE _ _ _ _) _ => intro h; exact nomatch h
  | .app (.letE _ _ _ _) _ => intro h; exact nomatch h
  | .app (.lit _) _ => intro h; exact nomatch h
  | .app (.proj _ _ _) _ => intro h; exact nomatch h
  | .app (.app (.bvar _) _) _ => intro h; exact nomatch h
  | .app (.app (.fvar _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.sort _) _) _ => intro h; exact nomatch h
  | .app (.app (.const _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.lam _ _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.forallE _ _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.letE _ _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.lit _) _) _ => intro h; exact nomatch h
  | .app (.app (.proj _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.bvar _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.fvar _ _ _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.sort _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.lam _ _ _ _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.forallE _ _ _ _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.letE _ _ _ _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.lit _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.proj _ _ _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.app (.bvar _) _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.app (.fvar _ _ _) _) _) _) _ =>
    intro h; exact nomatch h
  | .app (.app (.app (.app (.sort _) _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.app (.lam _ _ _ _) _) _) _) _ =>
    intro h; exact nomatch h
  | .app (.app (.app (.app (.forallE _ _ _ _) _) _) _) _ =>
    intro h; exact nomatch h
  | .app (.app (.app (.app (.letE _ _ _ _) _) _) _) _ =>
    intro h; exact nomatch h
  | .app (.app (.app (.app (.lit _) _) _) _) _ => intro h; exact nomatch h
  | .app (.app (.app (.app (.proj _ _ _) _) _) _) _ =>
    intro h; exact nomatch h
  | .app (.app (.app (.app (.app _ _) _) _) _) _ =>
    intro h; exact nomatch h
  | .app (.app (.app (.const _ _) _) _) _ => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hfc : env.find? c with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvm nPm nFm) => ?_
  intro h
  try dsimp only at h
  revert h
  match nPm, nFm with
  | 2, 2 => ?_
  | 0, _ => intro h; exact nomatch h
  | 1, _ => intro h; exact nomatch h
  | _ + 3, _ => intro h; exact nomatch h
  | 2, 0 => intro h; exact nomatch h
  | 2, 1 => intro h; exact nomatch h
  | 2, _ + 3 => intro h; exact nomatch h
  intro h
  try dsimp only at h
  try simp only [Bind.bind, Except.bind] at h
  cases htb : inferTypeCore mode env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnf mode env fuel d tb with
  | error err => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  dsimp only at h
  revert h
  match wtb with
  | .app (.app (.const c' us') A) B => ?_
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .const _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .app (.bvar _) _ => intro h; exact nomatch h
  | .app (.fvar _ _ _) _ => intro h; exact nomatch h
  | .app (.sort _) _ => intro h; exact nomatch h
  | .app (.const _ _) _ => intro h; exact nomatch h
  | .app (.lam _ _ _ _) _ => intro h; exact nomatch h
  | .app (.forallE _ _ _ _) _ => intro h; exact nomatch h
  | .app (.letE _ _ _ _) _ => intro h; exact nomatch h
  | .app (.lit _) _ => intro h; exact nomatch h
  | .app (.proj _ _ _) _ => intro h; exact nomatch h
  | .app (.app (.bvar _) _) _ => intro h; exact nomatch h
  | .app (.app (.fvar _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.sort _) _) _ => intro h; exact nomatch h
  | .app (.app (.lam _ _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.forallE _ _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.letE _ _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.lit _) _) _ => intro h; exact nomatch h
  | .app (.app (.proj _ _ _) _) _ => intro h; exact nomatch h
  | .app (.app (.app _ _) _) _ => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hfi : env.find? c' with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.indInfo cvi capsi) => ?_
  intro h
  dsimp only at h
  revert h
  match hfr : env.find? (c'.str "rec") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo cvr mI rP rules) => ?_
  intro h
  match rules, h with
  | [], h => exact nomatch h
  | _ :: _ :: _, h => exact nomatch h
  | [rr], h => ?_
  simp only [reduceCtorEq] at h
  try dsimp only at h
  try simp only [] at h
  by_cases hcond : rr.ctor = c ∧ rr.nfields = 2 ∧ mI = rP ∧
      reservedBasisNames.contains (c'.str "rec") = true
  case neg => rw [if_neg hcond] at h; exact nomatch h
  rw [if_pos hcond] at h
  obtain ⟨hrc, hrf, hmirp, hres⟩ := hcond
  try simp only [Bind.bind, Except.bind] at h
  cases hlev : Level.isEquivList us us' with
  | none => rw [hlev] at h; simp [liftFueled] at h
  | some okL =>
  rw [hlev] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases okL with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hdA : isDefEqCore mode env fuel d pα A with
  | error err => rw [hdA] at h; exact nomatch h
  | ok bA =>
  rw [hdA] at h
  dsimp only at h
  cases bA with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hdB : isDefEqCore mode env fuel d pβ B with
  | error err => rw [hdB] at h; exact nomatch h
  | ok bB =>
  rw [hdB] at h
  dsimp only at h
  cases bB with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hd1 : isDefEqCore mode env fuel d s₁ (.proj c' 0 b) with
  | error err => rw [hd1] at h; exact nomatch h
  | ok b1 =>
  rw [hd1] at h
  dsimp only at h
  cases b1 with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hd2 : isDefEqCore mode env fuel d s₂ (.proj c' 1 b) with
  | error err => rw [hd2] at h; exact nomatch h
  | ok b2 =>
  rw [hd2] at h
  dsimp only at h
  cases b2 with
  | false => simp [pure, Except.pure] at h
  | true =>
  exact ⟨c, us, pα, pβ, s₁, s₂, cvm, tb, c', us', A, B, cvi, capsi, cvr,
    mI, rP, rr, rfl, hfc, rfl, hwtb, hfi, hfr, hrc, hrf, hmirp, hres,
    hlev, hdA, hdB, hd1, hd2⟩

/-- Invert the per-projection telescope certificates. -/
theorem structEtaProjCerts_inv {env : Env} {fuel d : Nat} {T : Name}
    {us' : List Level} {targs : List Expr} {b : Expr} {lpsT : List Name} :
    ∀ (idxs : List Nat),
      structEtaProjCertsP mode env fuel d T us' targs b lpsT idxs = .ok true →
      ∀ i ∈ idxs, ∃ (cvp : ConstantVal)
        (mIp rPp : Nat) (rulesp : List RecRule),
        env.find? (projFnName T i) =
          some (.recInfo cvp mIp rPp rulesp) ∧
        cvp.levelParams = lpsT ∧
        (cvp.type.stripPis (targs.length + 1)).isSome = true ∧
        iotaCertsP mode env fuel d
          (cvp.type.instantiateLevelParams cvp.levelParams us')
          (targs ++ [b]) = .ok true
  | [], _, i, hi => nomatch hi
  | i₀ :: rest, h, i, hi => by
    dsimp only [structEtaProjCertsP] at h
    rw [structEtaProjCerts] at h
    simp only [iotaCerts_fold, structEtaProjCerts_fold] at h
    revert h
    match hfp : env.find? (projFnName T i₀) with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.projInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _ _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.recInfo cvp mIp rPp rulesp) => ?_
    intro h
    dsimp only at h
    by_cases hlps : cvp.levelParams = lpsT ∧
        (cvp.type.stripPis (targs.length + 1)).isSome = true
    case neg => rw [if_neg hlps] at h; exact nomatch h
    rw [if_pos hlps] at h
    obtain ⟨hlps, hstrp⟩ := hlps
    simp only [Bind.bind, Except.bind] at h
    cases hic : iotaCertsP mode env fuel d
        (cvp.type.instantiateLevelParams cvp.levelParams us')
        (targs ++ [b]) with
    | error e => rw [hic] at h; exact nomatch h
    | ok r => ?_
    rw [hic] at h
    cases r with
    | false => exact nomatch h
    | true => ?_
    simp only [↓reduceIte] at h
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact ⟨cvp, mIp, rPp, rulesp, hfp, hlps, hstrp, hic⟩
    · exact structEtaProjCerts_inv rest h i hi'

set_option maxHeartbeats 3200000 in
/-- Inversion of a successful structural eta certification. -/
theorem structEtaCertWith_inv {env : Env} {fuel d : Nat} {a b wtb : Expr}
    (h : structEtaCertWithP mode env fuel d a b wtb = .ok true) :
    ∃ (c : Name) (us : List Level) (cvc : ConstantVal) (cnP cnF : Nat)
      (T : Name) (us' : List Level)
      (cvT : ConstantVal) (caps : IndCaps),
      a.getAppFn = .const c us ∧
      env.find? c = some (.ctorInfo cvc cnP cnF) ∧
      a.getAppArgs.length = cnP + cnF ∧
      wtb.getAppFn = .const T us' ∧
      env.find? T = some (.indInfo cvT caps) ∧
      caps.eta = true ∧ caps.etaCtor = c ∧ caps.etaParams = cnP ∧
      caps.etaFields = cnF ∧
      reservedBasisNames.contains T = false ∧
      reservedBasisNames.contains c = false ∧
      wtb.getAppArgs.length = cnP ∧
      us'.length = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧
      (cvT.type.stripPis cnP).isSome = true ∧
      Level.isEquivList us us' = some true ∧
      iotaCertsP mode env fuel d
        (cvT.type.instantiateLevelParams cvT.levelParams us')
        wtb.getAppArgs = .ok true ∧
      structEtaProjCertsP mode env fuel d T us' wtb.getAppArgs b
        cvT.levelParams (List.range cnF) = .ok true ∧
      defEqListP mode env fuel d (a.getAppArgs.take cnP) wtb.getAppArgs
        = .ok true ∧
      -- task #137's constructor-telescope certificate is a TT-lane
      -- check (task #147): delivered only at `mode.ttChecks`
      (mode.ttChecks = true →
        iotaCertsP mode env fuel d
          (cvc.type.instantiateLevelParams cvc.levelParams us)
          (wtb.getAppArgs ++ (List.range cnF).map fun i =>
            Expr.mkAppN (.const (projFnName T i) us')
              (wtb.getAppArgs ++ [b])) = .ok true) ∧
      defEqListP mode env fuel d (a.getAppArgs.drop cnP)
        ((List.range cnF).map fun i =>
          Expr.mkAppN (.const (projFnName T i) us')
            (wtb.getAppArgs ++ [b])) = .ok true := by
  dsimp only [structEtaCertWithP] at h
  rw [structEtaCertWith] at h
  simp only [iotaCerts_fold, structEtaProjCerts_fold, defEqList_fold] at h
  revert h
  match hfn : a.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const c us => ?_
  intro h
  dsimp only at h
  revert h
  match hfc : env.find? c with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvc cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hal : a.getAppArgs.length = cnP + cnF
  case neg => rw [if_neg hal] at h; exact nomatch h
  rw [if_pos hal] at h
  revert h
  match hwfn : wtb.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const T us' => ?_
  intro h
  dsimp only at h
  revert h
  match hfT : env.find? T with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.indInfo cvT caps) => ?_
  intro h
  dsimp only at h
  by_cases hcond : caps.eta = true ∧ caps.etaCtor = c ∧
      caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
      reservedBasisNames.contains T = false ∧
      reservedBasisNames.contains c = false ∧
      wtb.getAppArgs.length = cnP ∧
      us'.length = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧
      (cvT.type.stripPis cnP).isSome = true
  case neg => rw [if_neg hcond] at h; exact nomatch h
  rw [if_pos hcond] at h
  obtain ⟨he1, he2, he3, he4, he5, he5b, he6, he7, he8, he9⟩ := hcond
  try simp only [Bind.bind, Except.bind] at h
  cases hlev : Level.isEquivList us us' with
  | none => rw [hlev] at h; simp [liftFueled] at h
  | some okL => ?_
  rw [hlev] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  cases okL with
  | false => simp at h
  | true => ?_
  simp only [↓reduceIte] at h
  cases hic : iotaCertsP mode env fuel d
      (cvT.type.instantiateLevelParams cvT.levelParams us')
      wtb.getAppArgs with
  | error e => rw [hic] at h; exact nomatch h
  | ok r₁ => ?_
  rw [hic] at h
  try dsimp only at h
  cases r₁ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  cases hpc : structEtaProjCertsP mode env fuel d T us' wtb.getAppArgs b
      cvT.levelParams (List.range cnF) with
  | error e => rw [hpc] at h; exact nomatch h
  | ok r₂ => ?_
  rw [hpc] at h
  try dsimp only at h
  cases r₂ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  cases hd1 : defEqListP mode env fuel d (a.getAppArgs.take cnP)
      wtb.getAppArgs with
  | error e => rw [hd1] at h; exact nomatch h
  | ok r₃ => ?_
  rw [hd1] at h
  try dsimp only at h
  cases r₃ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  -- task #137's constructor-telescope certificate, exposed for the
  -- bridge's `EtaLawTT` premise (task #119: the `EtaRhsTyped` binder
  -- moved into the law); a TT-lane check since task #147 — split on
  -- the mode gate first
  cases htt : mode.ttChecks with
  | false =>
    rw [htt] at h
    simp only [Bool.false_eq_true, if_false, pure, Except.pure,
      Bind.bind, Except.bind, if_true] at h
    try dsimp only at h
    exact ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps,
      rfl, hfc, hal, rfl, hfT, he1, he2, he3, he4, he5,
      he5b, he6, he7, he8, he9, hlev, hic, hpc, hd1,
      fun hc => absurd hc (by simp [htt]), h⟩
  | true => ?_
  rw [htt] at h
  simp only [↓reduceIte] at h
  cases hic2 : iotaCertsP mode env fuel d
      (cvc.type.instantiateLevelParams cvc.levelParams us)
      (wtb.getAppArgs ++ (List.range cnF).map fun i =>
        Expr.mkAppN (.const (projFnName T i) us')
          (wtb.getAppArgs ++ [b])) with
  | error e => rw [hic2] at h; exact nomatch h
  | ok r₄ => ?_
  rw [hic2] at h
  try dsimp only at h
  cases r₄ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  exact ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps,
    rfl, hfc, hal, rfl, hfT, he1, he2, he3, he4, he5,
    he5b, he6, he7, he8, he9, hlev, hic, hpc, hd1, fun _ => hic2, h⟩

/-- Inversion of the structure-eta certificate through its type
reduction: the stuck side's type is inferred and reduced, and the
`With` form of the certificate ran on the result. -/
theorem structEtaCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structEtaCertP mode env fuel d a b = .ok true) :
    ∃ tb wtb, inferTypeCore mode env fuel d b = .ok tb ∧
      whnf mode env fuel d tb = .ok wtb ∧
      structEtaCertWithP mode env fuel d a b wtb = .ok true := by
  dsimp only [structEtaCertP] at h
  rw [structEtaCert] at h
  simp only [Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, structEtaCertWith_fold] at h
  cases htb : inferTypeCore mode env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnf mode env fuel d tb with
  | error e => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  dsimp only at h
  exact ⟨tb, wtb, rfl, hwtb, h⟩

/-- Inversion of a successful unit-likeness certification. -/
theorem structUnitCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structUnitCertP mode env fuel d a b = .ok true) :
    ∃ (ta wta : Expr) (T : Name) (us' : List Level)
      (cvT : ConstantVal) (caps : IndCaps) (tb wtb : Expr),
      inferTypeCore mode env fuel d a = .ok ta ∧
      whnf mode env fuel d ta = .ok wta ∧
      wta.getAppFn = .const T us' ∧
      env.find? T = some (.indInfo cvT caps) ∧
      caps.unitlike = true ∧
      reservedBasisNames.contains T = false ∧
      wta.getAppArgs.length = caps.unitParams ∧
      us'.length = cvT.levelParams.length ∧
      (cvT.type.stripPis caps.unitParams).isSome = true ∧
      inferTypeCore mode env fuel d b = .ok tb ∧
      whnf mode env fuel d tb = .ok wtb ∧
      isDefEqCore mode env fuel d wta wtb = .ok true ∧
      iotaCertsP mode env fuel d
        (cvT.type.instantiateLevelParams cvT.levelParams us')
        wta.getAppArgs = .ok true := by
  dsimp only [structUnitCertP] at h
  rw [structUnitCert] at h
  simp only [Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeq_def, iotaCerts_fold] at h
  cases hta : inferTypeCore mode env fuel d a with
  | error e => rw [hta] at h; exact nomatch h
  | ok ta => ?_
  rw [hta] at h
  try dsimp only at h
  cases hwta : whnf mode env fuel d ta with
  | error e => rw [hwta] at h; exact nomatch h
  | ok wta => ?_
  rw [hwta] at h
  try dsimp only at h
  revert h
  match hwfn : wta.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const T us' => ?_
  intro h
  dsimp only at h
  revert h
  match hfT : env.find? T with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.indInfo cvT caps) => ?_
  intro h
  dsimp only at h
  by_cases hcond : caps.unitlike = true ∧
      reservedBasisNames.contains T = false ∧
      wta.getAppArgs.length = caps.unitParams ∧
      us'.length = cvT.levelParams.length ∧
      (cvT.type.stripPis caps.unitParams).isSome = true
  case neg => rw [if_neg hcond] at h; exact nomatch h
  rw [if_pos hcond] at h
  obtain ⟨he1, he2, he3, he4, he5⟩ := hcond
  try simp only [Bind.bind, Except.bind] at h
  cases htb : inferTypeCore mode env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb => ?_
  rw [htb] at h
  try dsimp only at h
  cases hwtb : whnf mode env fuel d tb with
  | error e => rw [hwtb] at h; exact nomatch h
  | ok wtb => ?_
  rw [hwtb] at h
  try dsimp only at h
  cases hde : isDefEqCore mode env fuel d wta wtb with
  | error e => rw [hde] at h; exact nomatch h
  | ok r₁ => ?_
  rw [hde] at h
  try dsimp only at h
  cases r₁ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  exact ⟨ta, wta, T, us', cvT, caps, tb, wtb, rfl, hwta, hwfn, hfT,
    he1, he2, he3, he4, he5, rfl, hwtb, hde, h⟩

/-- Inversion of a successful eta certification. -/
theorem etaCert_inv {env : Env} {fuel d : Nat} {n₁ : Name} {ty₁ body₁ b : Expr}
    {m₁ : BinderMeta}
    (h : etaCertP mode env fuel d n₁ ty₁ body₁ m₁ b = .ok true) :
    ∃ tb n₂ ty₂ fb m₂,
      inferTypeCore mode env fuel d b = .ok tb ∧
      whnf mode env fuel d tb = .ok (.forallE n₂ ty₂ fb m₂) ∧
      isDefEqCore mode env fuel d ty₂ ty₁ = .ok true ∧
      isDefEqCore mode env fuel (d + 1) (body₁.instantiate1 (.fvar d n₁ ty₁))
        (.app b (.fvar d n₁ ty₁)) = .ok true ∧
      (mode.verified = true → m₁.pw.equiv m₂.pw = true) := by
  dsimp only [etaCertP] at h
  simp only [etaCert, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def, defeq_def] at h
  cases htb : inferTypeCore mode env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnf mode env fuel d tb with
  | error err => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  match wtb, h with
  | .forallE n₂ ty₂ fb m₂, h => ?_
  | .bvar i2, h => exact nomatch h
  | .fvar i2 n2 t2, h => exact nomatch h
  | .sort u2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e3, h => exact nomatch h
  dsimp only at h
  cases hd1 : isDefEqCore mode env fuel d ty₂ ty₁ with
  | error err => rw [hd1] at h; exact nomatch h
  | ok r₁ =>
  rw [hd1] at h
  dsimp only at h
  cases r₁ with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  cases hd2 : isDefEqCore mode env fuel (d + 1)
      (body₁.instantiate1 (.fvar d n₁ ty₁)) (.app b (.fvar d n₁ ty₁)) with
  | error err => rw [hd2] at h; exact nomatch h
  | ok r₂ =>
  rw [hd2] at h
  dsimp only at h
  cases r₂ with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  by_cases hpw : (mode.verified && !(m₁.pw.equiv m₂.pw)) = true
  · rw [if_pos hpw] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hpw] at h
    refine ⟨tb, n₂, ty₂, fb, m₂, rfl, hwtb, hd1, rfl, ?_⟩
    intro hv
    by_cases he : m₁.pw.equiv m₂.pw = true
    · exact he
    · exact absurd (by simp [hv, he]) hpw

/-- Inversion for the projection rule of `inferTypeCore`: the subject's
type whnfs to a type application whose head has a native
projection-table entry, and the result is the entry type's residual
along the arguments and the subject. -/
theorem inferTypeCore_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat}
    {e t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.proj sn i e) = .ok t) :
    ∃ tpe te T us entry,
      inferTypeCore mode env fuel d e = .ok tpe ∧
      whnf mode env fuel d tpe = .ok te ∧
      te.getAppFn = .const T us ∧
      env.findProj? T i = some entry ∧ entry.native = true ∧
      te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length ∧
      -- task #161 item B2 (harvest site 21 / P10): the returned type
      -- is *computed*, not walked, so the inversion reads it off the
      -- two-way branch.  `projResidualP`'s conclusion, verbatim — see
      -- `SetR/Interp2/Step2/ProjPinsP.lean`, where the same shape used
      -- to be *derived* from a `piResidual` premise.
      (∃ A B, te.getAppArgs = [A, B] ∧
        ((i = 0 ∧ t = A) ∨ (i = 1 ∧ t = .app B (.proj T 0 e)))) := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind, Except.bind] at h
  simp only [infer_def, whnf_def] at h
  cases hte : inferTypeCore mode env fuel d e with
  | error err => rw [hte] at h; exact nomatch h
  | ok tpe =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tpe with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  revert h
  cases hfn : te.getAppFn with
  | const T us => ?_
  | bvar i2 => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | fvar i2 n2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam n2 t2 b2 m2 => intro h; exact nomatch h
  | forallE n2 t2 b2 m2 => intro h; exact nomatch h
  | letE n2 t2 v2 b2 => intro h; exact nomatch h
  | lit l2 => intro h; exact nomatch h
  | proj s2 i2 e2 => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  cases hfp : env.findProj? T i with
  | none => intro h; exact nomatch h
  | some entry => ?_
  intro h
  dsimp only at h
  split at h
  case isFalse => exact nomatch h
  case isTrue hcond =>
    obtain ⟨hnat, hlen, hus⟩ := hcond
    revert h
    match hargs : te.getAppArgs, i with
    | [A, B], 0 => ?_
    | [A, B], 1 => ?_
    | [], _ => intro h; exact nomatch h
    | [_], _ => intro h; exact nomatch h
    | _ :: _ :: _ :: _, _ => intro h; exact nomatch h
    | [_, _], _ + 2 => intro h; exact nomatch h
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hnat, hlen, hus,
        A, B, hargs, Or.inl ⟨rfl, rfl⟩⟩
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hnat, hlen, hus,
        A, B, hargs, Or.inr ⟨rfl, rfl⟩⟩

/-! ## Well-scopedness preservation through reduction -/

/-- The constructor form of a literal is closed. -/
theorem natLitToConstructor_WScoped (n : Nat) {d : Nat} :
    WScoped d (natLitToConstructor n) := by
  cases n <;> simp [natLitToConstructor, WScoped]

/-- Inversion of the literal-major conversion: either the one-layer
`Nat` conversion applied, or the major was a supported string literal
and the result is the reduced constructor form. -/
theorem litMajorToCtorP_inv {env : Env} {fuel d : Nat} {e e₁ : Expr}
    (h : litMajorToCtorP mode env fuel d e = .ok e₁) :
    e₁ = litToCtorIfNat env e ∨
    ∃ s, e = .lit (.strVal s) ∧ strLitSupported env = true ∧
      whnf mode env fuel d (strLitToConstructor s) = .ok e₁ := by
  match e with
  | .lit (.strVal s) =>
    dsimp only [litMajorToCtorP, litMajorToCtor] at h
    revert h
    split
    · intro h
      exact Or.inr ⟨s, rfl, by assumption, h⟩
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Or.inl rfl
  | .lit (.natVal n) =>
    simp only [litMajorToCtorP, litMajorToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ =>
    simp only [litMajorToCtorP, litMajorToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm

/-- Inversion of the projection-scrutinee literal conversion: either the
identity, or the scrutinee was a supported string literal and the
result is the reduced constructor form. -/
theorem projLitToCtorP_inv {env : Env} {fuel d : Nat} {e e₁ : Expr}
    (h : projLitToCtorP mode env fuel d e = .ok e₁) :
    e₁ = e ∨
    ∃ s, e = .lit (.strVal s) ∧ strLitSupported env = true ∧
      whnf mode env fuel d (strLitToConstructor s) = .ok e₁ := by
  match e with
  | .lit (.strVal s) =>
    dsimp only [projLitToCtorP, projLitToCtor] at h
    revert h
    split
    · intro h
      exact Or.inr ⟨s, rfl, by assumption, h⟩
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact Or.inl rfl
  | .lit (.natVal n) =>
    simp only [projLitToCtorP, projLitToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ =>
    simp only [projLitToCtorP, projLitToCtor, pure, Except.pure,
      Except.ok.injEq] at h
    exact Or.inl h.symm

/-- The literal-major conversion preserves well-scopedness. -/
theorem litToCtorIfNat_WScoped {env : Env} {d : Nat} {e : Expr}
    (hw : WScoped d e) : WScoped d (litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · exact natLitToConstructor_WScoped n
    · exact hw
  | .lit (.strVal _) => exact hw
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ =>
    exact hw

/-- The fast-path reducts are closed atoms. -/
theorem natOpResult_shape {c : Name} {a b : Nat} {e₂ : Expr}
    (h : natOpResult c a b = some e₂) :
    (∃ n, e₂ = .lit (.natVal n)) ∨ (∃ bn, e₂ = .const bn []) := by
  unfold natOpResult at h
  by_cases h1 : c = natPredName
  · rw [if_pos h1] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h1] at h
  by_cases h2 : c = natAddName
  · rw [if_pos h2] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h2] at h
  by_cases h3 : c = natSubName
  · rw [if_pos h3] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h3] at h
  by_cases h4 : c = natMulName
  · rw [if_pos h4] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h4] at h
  by_cases h5 : c = natPowName
  · rw [if_pos h5] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h5] at h
  by_cases h6 : c = natDivName
  · rw [if_pos h6] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h6] at h
  by_cases h7 : c = natModName
  · rw [if_pos h7] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h7] at h
  by_cases h8 : c = natGcdName
  · rw [if_pos h8] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h8] at h
  by_cases h9 : c = natLandName
  · rw [if_pos h9] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h9] at h
  by_cases h10 : c = natLorName
  · rw [if_pos h10] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h10] at h
  by_cases h11 : c = natXorName
  · rw [if_pos h11] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h11] at h
  by_cases h12 : c = natShiftLeftName
  · rw [if_pos h12] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h12] at h
  by_cases h13 : c = natShiftRightName
  · rw [if_pos h13] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h13] at h
  by_cases h14 : c = natLog2Name
  · rw [if_pos h14] at h
    exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h14] at h
  by_cases h15 : c = natBeqName
  · rw [if_pos h15] at h
    exact Or.inr ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h15] at h
  by_cases h16 : c = natBleName
  · rw [if_pos h16] at h
    exact Or.inr ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h16] at h
  exact nomatch h

/-- The fast-path reducts, **identified**: every arithmetic branch
returns a `Nat` literal, and the only branches returning a constant are
the two comparisons, whose result is one of the two `Bool`
constructors.  The strengthening of `natOpResult_shape` that a bridge
needs in order to *denote* the reduct: `natOpGuard` pins exactly
`boolTrueName`/`boolFalseName` (and only for `beq`/`ble`/div-mod), so
knowing "some constant" is not enough. -/
theorem natOpResult_atom {c : Name} {a b : Nat} {e₂ : Expr}
    (h : natOpResult c a b = some e₂) :
    (∃ n, e₂ = .lit (.natVal n)) ∨
      ((c = natBeqName ∨ c = natBleName) ∧
        (e₂ = .const boolTrueName [] ∨ e₂ = .const boolFalseName [])) := by
  unfold natOpResult at h
  by_cases h1 : c = natPredName
  · rw [if_pos h1] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h1] at h
  by_cases h2 : c = natAddName
  · rw [if_pos h2] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h2] at h
  by_cases h3 : c = natSubName
  · rw [if_pos h3] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h3] at h
  by_cases h4 : c = natMulName
  · rw [if_pos h4] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h4] at h
  by_cases h5 : c = natPowName
  · rw [if_pos h5] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h5] at h
  by_cases h6 : c = natDivName
  · rw [if_pos h6] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h6] at h
  by_cases h7 : c = natModName
  · rw [if_pos h7] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h7] at h
  by_cases h8 : c = natGcdName
  · rw [if_pos h8] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h8] at h
  by_cases h9 : c = natLandName
  · rw [if_pos h9] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h9] at h
  by_cases h10 : c = natLorName
  · rw [if_pos h10] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h10] at h
  by_cases h11 : c = natXorName
  · rw [if_pos h11] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h11] at h
  by_cases h12 : c = natShiftLeftName
  · rw [if_pos h12] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h12] at h
  by_cases h13 : c = natShiftRightName
  · rw [if_pos h13] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h13] at h
  by_cases h14 : c = natLog2Name
  · rw [if_pos h14] at h; exact Or.inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h14] at h
  by_cases h15 : c = natBeqName
  · rw [if_pos h15] at h
    refine Or.inr ⟨Or.inl h15, ?_⟩
    rw [← Option.some.inj h]
    by_cases hab : a = b
    · exact Or.inl (by rw [if_pos hab])
    · exact Or.inr (by rw [if_neg hab])
  rw [if_neg h15] at h
  by_cases h16 : c = natBleName
  · rw [if_pos h16] at h
    refine Or.inr ⟨Or.inr h16, ?_⟩
    rw [← Option.some.inj h]
    by_cases hab : a ≤ b
    · exact Or.inl (by rw [if_pos hab])
    · exact Or.inr (by rw [if_neg hab])
  rw [if_neg h16] at h
  exact nomatch h

/-- Literal acceleration produces closed atoms: a literal or a
`Bool`-constant head. -/
theorem reduceNat_inv {env : Env} {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatP mode env fuel d e = .ok (some e₂)) :
    (∃ n, e₂ = .lit (.natVal n)) ∨ (∃ bn, e₂ = .const bn []) := by
  dsimp only [reduceNatP] at h
  revert h
  match e with
  | .app (.const c []) a => ?_
  | .app (.app (.const c []) a) b => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _ | .app (.fvar _ _ _) _ | .app (.sort _) _
  | .app (.lam _ _ _ _) _ | .app (.forallE _ _ _ _) _
  | .app (.letE _ _ _ _) _ | .app (.lit _) _ | .app (.proj _ _ _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _ | .app (.app (.fvar _ _ _) _) _
  | .app (.app (.sort _) _) _ | .app (.app (.app _ _) _) _
  | .app (.app (.lam _ _ _ _) _) _ | .app (.app (.forallE _ _ _ _) _) _
  | .app (.app (.letE _ _ _ _) _) _ | .app (.app (.lit _) _) _
  | .app (.app (.proj _ _ _) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  · -- unary heads: `succ` folding or the `pred` fast path
    intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    · intro h
      revert h
      cases hw0 : whnf mode env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a0 =>
      intro h
      dsimp only at h
      revert h
      match rawNatLit? a0 with
      | some n =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        exact Or.inl ⟨n + 1, h.symm⟩
      | none => intro h; simp [pure, Except.pure] at h
    · split
      · intro h
        revert h
        cases hw : whnf mode env fuel d a with
        | error err => intro h; exact nomatch h
        | ok a' =>
        intro h
        dsimp only at h
        revert h
        match rawNatLit? a' with
        | some n =>
          intro h
          dsimp only at h
          cases hres : natOpResult c n 0 with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            exact h ▸ natOpResult_shape hres
        | none => intro h; simp [pure, Except.pure] at h
      · -- the certified `log2` branch mirrors `pred`'s
        split
        · intro h
          revert h
          cases hw : whnf mode env fuel d a with
          | error err => intro h; exact nomatch h
          | ok a' =>
          intro h
          dsimp only at h
          revert h
          match rawNatLit? a' with
          | some n =>
            intro h
            dsimp only at h
            cases hres : natOpResult c n 0 with
            | none => rw [hres] at h; simp [pure, Except.pure] at h
            | some r =>
              rw [hres] at h
              simp only [pure, Except.pure, Except.ok.injEq,
                Option.some.injEq] at h
              exact h ▸ natOpResult_shape hres
          | none => intro h; simp [pure, Except.pure] at h
        · -- the capless `log2` decline branch never returns a reduct
          split
          · intro h
            revert h
            cases hw : whnf mode env fuel d a with
            | error err => intro h; exact nomatch h
            | ok a' =>
            intro h
            dsimp only at h
            revert h
            match rawNatLit? a' with
            | some _ => intro h; exact nomatch h
            | none => intro h; simp [pure, Except.pure] at h
          · intro h; simp [pure, Except.pure] at h
  · -- binary fast paths
    intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    · intro h
      revert h
      cases hw1 : whnf mode env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a' =>
      intro h
      dsimp only at h
      revert h
      cases hw2 : whnf mode env fuel d b with
      | error err => intro h; exact nomatch h
      | ok b' =>
      intro h
      dsimp only at h
      revert h
      match rawNatLit? a', rawNatLit? b' with
      | some n₁, some n₂ =>
        intro h
        dsimp only at h
        cases hres : natOpResult c n₁ n₂ with
        | none => rw [hres] at h; simp [pure, Except.pure] at h
        | some r =>
          rw [hres] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at h
          exact h ▸ natOpResult_shape hres
      | some _, none => intro h; simp [pure, Except.pure] at h
      | none, some _ => intro h; simp [pure, Except.pure] at h
      | none, none => intro h; simp [pure, Except.pure] at h
    · -- the WF-op decline branch never returns a reduct
      split
      · intro h
        revert h
        cases hw1 : whnf mode env fuel d a with
        | error err => intro h; exact nomatch h
        | ok a' =>
        intro h
        dsimp only at h
        revert h
        cases hw2 : whnf mode env fuel d b with
        | error err => intro h; exact nomatch h
        | ok b' =>
        intro h
        dsimp only at h
        revert h
        match rawNatLit? a', rawNatLit? b' with
        | some _, some _ => intro h; exact nomatch h
        | some _, none => intro h; simp [pure, Except.pure] at h
        | none, some _ => intro h; simp [pure, Except.pure] at h
        | none, none => intro h; simp [pure, Except.pure] at h
      · intro h; simp [pure, Except.pure] at h

/-- Unfolding a definition at the head preserves well-scopedness (the
stored value is closed by environment well-formedness). -/
theorem unfoldDefinition_WScoped {env : Env} (henv : EnvWF env)
    {d : Nat} {e e₂ : Expr}
    (h : unfoldDefinition env e = some e₂) (hw : WScoped d e) :
    WScoped d e₂ := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo cv value) =>
    intro h
    dsimp only at h
    revert h
    split
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, -, -, hval⟩ := henv _ (find?_mem hf)
      obtain ⟨hvc, -, -, -⟩ := hval cv value rfl
      refine Expr.WScoped.mkAppN
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_instantiateLevelParams]; exact hvc)) ?_
      intro x hx
      exact hw.getAppArgs x hx
    · intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
    obtain ⟨hvc, -, -, -⟩ := hval cv value hint rfl
    refine Expr.WScoped.mkAppN
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]; exact hvc)) ?_
    intro x hx
    exact hw.getAppArgs x hx
  · intro h; exact nomatch h

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop preserve
well-scopedness. -/
theorem whnfPres_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {d : Nat} {e e' : Expr}, whnfCore mode env fuel d e = .ok e' →
        WScoped d e → WScoped d e') ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode env fuel d e = .ok e' →
        WScoped d e → WScoped d e')
  | 0 => ⟨(fun {_ _ _} h _ => nomatch h), (fun {_ _ _} h _ => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_WScoped henv fuel
    constructor
    · -- whnfCore
      intro d e e' h hw
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | fvar idx n ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | forallE n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | lam n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | lit l =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hw
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE nn tt vv bb =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, whnfCore_def] at h
        simp only [WScoped] at hw
        exact ihCore h (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
      | app f a =>
        simp only [WScoped] at hw
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        have hwf' : WScoped d f' := ihCore hwf hw.1
        rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · simp only [WScoped] at hwf'
          exact ihCore hbeta (WScoped.instantiate1_gen hw.2 0 hwf'.2)
        · -- iota step
          obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj,
            cvj, cnP, cnF, r, -, -, -, -, -, hfn, hfc, hlen, -, hmaj, hlit,
            hsub, hmfn, hfj,
            hrule,
            hml, har1, har2, -, hlev, hpeq, hcerts, hmcerts, -, -, -, -, rfl⟩ :=
            iotaRec_inv hio
          have hwapp : WScoped d (Expr.app f' a) := by
            simp only [WScoped]
            exact ⟨hwf', hw.2⟩
          have hargs : ∀ x, x ∈ (Expr.app f' a).getAppArgs → WScoped d x :=
            fun x hx => hwapp.getAppArgs x hx
          have hrhs : WScoped d
              (r.rhs.instantiateLevelParams cv.levelParams us) := by
            obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
            obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl r
              (List.mem_of_find?_eq_some hrule)
            exact WScoped.of_not_hasFvar
              (by rw [hasFvar_instantiateLevelParams]; exact hrf)
          have hmaj0w : WScoped d major₀ := ihLoop hmaj
            (hargs _ (getD_mem (by omega)))
          have hmaj1w : WScoped d major₁ := by
            rcases litMajorToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
            · exact litToCtorIfNat_WScoped hmaj0w
            · exact ihLoop hred (strLitToConstructor_WScoped s d)
          have hmajw : WScoped d major := by
            rcases majorToCtor_inv hsub with rfl | ⟨hwsc, -, -, -⟩
            · exact hmaj1w
            · exact WScoped.of_wscopedB hwsc
          refine ihCore hwe'' ?_
          refine Expr.WScoped.mkAppN hrhs ?_
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hargs _ (List.mem_of_mem_take hx)
          · exact hmajw.getAppArgs _ (List.mem_of_mem_drop hx)
        · simp only [WScoped]
          exact ⟨hwf', hw.2⟩
      | proj sn i pe =>
        simp only [WScoped] at hw
        obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
        have hwe₂ : WScoped d e₂ := ihLoop he hw
        have hwe₃ : WScoped d e₃ := by
          rcases projLitToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
          · exact hwe₂
          · exact ihLoop hred (strLitToConstructor_WScoped s d)
        rcases hcase with rfl |
          ⟨us, entry, hfn, hf, hnat, hi, hlen, hus, hred, -⟩
        · simpa [WScoped] using hwe₃
        · exact ihCore hred (hwe₃.getAppArgs _ (getD_mem (by omega)))
    · -- whnf loop: the reduction chain is iteration on the loop's own
      -- step budget (task #106), so this is an induction on that
      -- budget at the *same* knot fuel; `ihCore` covers the per-step
      -- head normalization.
      have hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr},
          whnfLoop (pureFns mode env fuel) env d n e = .ok e' →
          WScoped d e → WScoped d e' := by
        intro n
        induction n with
        | zero => intro _ _ _ h _; exact nomatch h
        | succ n ihN =>
          intro d e e' h hw
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          have hwe₁ : WScoped d e₁ := ihCore hwc hw
          rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
          · rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
              exact ihN hcont (by simp [WScoped])
          · exact ihN hcont (unfoldDefinition_WScoped henv hu hwe₁)
          · exact hwe₁
      intro d e e' h hw
      exact hloop whnfLoopFuel h hw

/-- Head normalization preserves well-scopedness. -/
theorem whnfCore_WScoped {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnfCore mode env fuel d e = .ok e') (hw : WScoped d e) : WScoped d e' :=
  (whnfPres_WScoped henv fuel).1 h hw

/-- The reduction loop preserves well-scopedness. -/
theorem whnf_WScoped {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf mode env fuel d e = .ok e' ) (hw : WScoped d e) : WScoped d e' :=
  (whnfPres_WScoped henv fuel).2 h hw

end Setlec
