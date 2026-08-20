import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift
import Setlec.Verify.InstLevels
import Setlec.Verify.EnvWF

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

open Expr

theorem find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts :=
  List.mem_of_find?_eq_some h

/-! ## Inversion lemmas -/

/-- Inversion for `whnfCore` on applications: either a (guarded or
certified) beta step happened, or the application is stuck. -/
theorem whnf_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr}
    (h : whnfCore env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f', whnfCore env fuel d f = .ok f' ∧
      ((∃ n ty body m v, f' = .lam n ty body m ∧ m.cod = some v ∧
          whnfCore env fuel d (body.instantiate1 a) = .ok e' ∧
          (v.isNonZero = true ∨
            ∃ ta, inferTypeCore env fuel d a = .ok ta ∧
              isDefEqCore env fuel d ta ty = .ok true)) ∨
        (∃ e'', iotaRec env fuel d (.app f' a) = .ok (some e'') ∧
          whnfCore env fuel d e'' = .ok e') ∨
        e' = .app f' a) := by
  simp only [whnfCore, Bind.bind, Except.bind] at h
  cases hwf : whnfCore env fuel d f with
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
    cases hc : m.cod with
    | none =>
      rw [hc] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inr h.symm)
    | some v =>
      rw [hc] at h
      dsimp only at h
      split at h
      next hnz => exact Or.inl ⟨n, ty, body, m, v, rfl, hc, h, Or.inl hnz⟩
      next hnz =>
        try simp only [Bind.bind, Except.bind] at h
        try dsimp only at h
        cases hta : inferTypeCore env fuel d a with
        | error err => rw [hta] at h; exact nomatch h
        | ok ta =>
        rw [hta] at h
        dsimp only at h
        cases hde : isDefEqCore env fuel d ta ty with
        | error err => rw [hde] at h; exact nomatch h
        | ok bb =>
        rw [hde] at h
        cases bb with
        | true =>
          simp only [if_true] at h
          exact Or.inl ⟨n, ty, body, m, v, rfl, hc, h, Or.inr ⟨ta, rfl, hde⟩⟩
        | false =>
          simp only [Bool.false_eq_true, if_false, pure, Except.pure,
            Except.ok.injEq] at h
          exact Or.inr (Or.inr h.symm)
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    cases hio : iotaRec env fuel d (.app _ a) with
    | error err => rw [hio] at h; exact nomatch h
    | ok o =>
      rw [hio] at h
      dsimp only at h
      cases o with
      | some e'' => exact Or.inr (Or.inl ⟨e'', rfl, h⟩)
      | none =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)

/-- Inversion for the λ-rule of `inferTypeCore`. -/
theorem inferTypeCore_lam_inv {env : Env} {fuel d : Nat} {n : Name} {ty body t : Expr}
    {m : BinderMeta}
    (h : inferTypeCore env (fuel + 1) d (.lam n ty body m) = .ok t) :
    ∃ v tty u bt tbt v', m.cod = some v ∧
      inferTypeCore env fuel d ty = .ok tty ∧
      whnfCore env fuel d tty = .ok (.sort u) ∧
      inferTypeCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty)) = .ok bt ∧
      inferTypeCore env fuel (d + 1) bt = .ok tbt ∧
      whnfCore env fuel (d + 1) tbt = .ok (.sort v') ∧
      Level.isEquiv v v' = some true ∧
      t = .forallE n ty (bt.abstract1 d) ⟨m.bi, some v⟩ := by
  simp only [inferTypeCore, Bind.bind, Except.bind] at h
  cases hc : m.cod with
  | none => rw [hc] at h; exact nomatch h
  | some v =>
  rw [hc] at h
  dsimp only at h
  cases hty : inferTypeCore env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hwt : whnfCore env fuel d tty with
  | error err => rw [hwt] at h; exact nomatch h
  | ok w =>
  rw [hwt] at h
  dsimp only at h
  match w, h with
  | .sort u, h => ?_
  | .fvar i n2 t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .forallE n2 t2 b2 m2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  cases hbt : inferTypeCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  cases htbt : inferTypeCore env fuel (d + 1) bt with
  | error err => rw [htbt] at h; exact nomatch h
  | ok tbt =>
  rw [htbt] at h
  dsimp only at h
  cases hwv : whnfCore env fuel (d + 1) tbt with
  | error err => rw [hwv] at h; exact nomatch h
  | ok w' =>
  rw [hwv] at h
  dsimp only at h
  match w', h with
  | .sort v', h => ?_
  | .fvar i n2 t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .forallE n2 t2 b2 m2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  cases heq : Level.isEquiv v v' with
  | none => rw [heq] at h; simp [liftFueled] at h
  | some b =>
  rw [heq] at h
  cases b with
  | false => simp [liftFueled, pure, Except.pure] at h
  | true =>
    simp only [liftFueled, pure, Except.pure, ↓reduceIte, Except.ok.injEq] at h
    exact ⟨v, tty, u, bt, tbt, v', rfl, rfl, hwt, rfl, htbt, hwv, heq, h.symm⟩

/-- Inversion for the application rule of `inferTypeCore`. -/
theorem inferTypeCore_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m' ta, inferTypeCore env fuel d f = .ok tf ∧
      whnfCore env fuel d tf = .ok (.forallE n' ty' body' m') ∧
      inferTypeCore env fuel d a = .ok ta ∧
      isDefEqCore env fuel d ta ty' = .ok true ∧
      t = body'.instantiate1 a := by
  simp only [inferTypeCore, Bind.bind, Except.bind] at h
  cases htf : inferTypeCore env fuel d f with
  | error err => rw [htf] at h; exact nomatch h
  | ok tf =>
  rw [htf] at h
  dsimp only at h
  cases hw : whnfCore env fuel d tf with
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
  cases hta : inferTypeCore env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore env fuel d ta ty' with
  | error err => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => simp [pure, Except.pure] at h
  | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tf, n', ty', body', m', ta, rfl, hw, rfl, hde, h.symm⟩

/-- Inversion for the ∀-rule of `inferTypeCore`. -/
theorem inferTypeCore_forall_inv {env : Env} {fuel d : Nat} {n : Name} {ty body t : Expr}
    {m : BinderMeta} {v : Level}
    (hc : m.cod = some v)
    (h : inferTypeCore env (fuel + 1) d (.forallE n ty body m) = .ok t) :
    ∃ tty u, inferTypeCore env fuel d ty = .ok tty ∧
      whnfCore env fuel d tty = .ok (.sort u) ∧
      t = .sort (.imax u v) := by
  simp only [inferTypeCore, Bind.bind, Except.bind, hc] at h
  try dsimp only at h
  cases hty : inferTypeCore env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hwt : whnfCore env fuel d tty with
  | error err => rw [hwt] at h; exact nomatch h
  | ok w =>
  rw [hwt] at h
  dsimp only at h
  match w, h with
  | .sort u, h =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, rfl, hwt, h.symm⟩
  | .fvar i n2 t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .forallE n2 t2 b2 m2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h

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

theorem List.length_four {α : Type _} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem List.length_two {α : Type _} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- Inversion for `whnfCore` on projections. -/
theorem whnf_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat} {e e' : Expr}
    (h : whnfCore env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂, whnfCore env fuel d e = .ok e₂ ∧
      (e' = .proj sn i e₂ ∨
        ∃ us cv nP nF, e₂.getAppFn = .const psigmaMkName us ∧
          env.find? psigmaMkName = some (.ctorInfo cv nP nF) ∧
          i < nF ∧ e₂.getAppArgs.length = nP + nF ∧ us.length = 2 ∧
          whnfCore env fuel d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) = .ok e' ∧
          ((Level.max (us.getD 0 .zero) (us.getD 1 .zero)).isNonZero = true ∨
            projCert env fuel d e₂ i us nP = .ok true)) := by
  simp only [whnfCore, Bind.bind, Except.bind] at h
  cases he : whnfCore env fuel d e with
  | error err => rw [he] at h; exact nomatch h
  | ok e₂ =>
  rw [he] at h
  dsimp only at h
  refine ⟨e₂, rfl, ?_⟩
  cases hfn : e₂.getAppFn with
  | const c us =>
    rw [hfn] at h
    dsimp only at h
    cases hf : env.find? c with
    | none =>
      rw [hf] at h
      exact Or.inl (Except.ok.inj h).symm
    | some ci =>
      rw [hf] at h
      cases ci with
      | ctorInfo cv nP nF =>
        dsimp only at h
        split at h
        next hcond =>
          obtain ⟨rfl, hi, hlen, hus⟩ := hcond
          split at h
          next hnz =>
            exact Or.inr ⟨us, cv, nP, nF, rfl, hf, hi, hlen, hus, h, Or.inl hnz⟩
          next hnz =>
            try simp only [Bind.bind, Except.bind] at h
            try dsimp only at h
            cases hcert : projCert env fuel d e₂ i us nP with
            | error err => rw [hcert] at h; exact nomatch h
            | ok b =>
            rw [hcert] at h
            cases b with
            | true =>
              simp only [if_true] at h
              try dsimp only at h
              exact Or.inr ⟨us, cv, nP, nF, rfl, hf, hi, hlen, hus, h, Or.inr hcert⟩
            | false =>
              simp only [Bool.false_eq_true, if_false] at h
              exact Or.inl (Except.ok.inj h).symm
        next hcond =>
          exact Or.inl (Except.ok.inj h).symm
      | axiomInfo cv => exact Or.inl (Except.ok.inj h).symm
      | defnInfo cv value => exact Or.inl (Except.ok.inj h).symm
      | thmInfo cv value => exact Or.inl (Except.ok.inj h).symm
      | indInfo cv _ => exact Or.inl (Except.ok.inj h).symm
      | recInfo cv nP nM nm ni rules => exact Or.inl (Except.ok.inj h).symm
  | bvar i2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | sort u => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | fvar i2 n2 t2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | app f2 a2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | lam n2 t2 b2 m2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | forallE n2 t2 b2 m2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | letE n2 t2 v2 b2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | lit l2 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm
  | proj s2 i2 e3 => rw [hfn] at h; exact Or.inl (Except.ok.inj h).symm

/-- Inversion for a successful projection certification. -/
theorem projCert_inv {env : Env} {fuel d : Nat} {e₂ : Expr} {i : Nat}
    {us : List Level} {nP : Nat}
    (h : projCert env (fuel + 1) d e₂ i us nP = .ok true) :
    ∃ ta sta uT te ste wT,
      inferTypeCore env fuel d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) = .ok ta ∧
      inferTypeCore env fuel d ta = .ok sta ∧
      whnfCore env fuel d sta = .ok (.sort uT) ∧
      Level.isEquiv uT (us.getD i .zero) = some true ∧
      inferTypeCore env fuel d e₂ = .ok te ∧
      inferTypeCore env fuel d te = .ok ste ∧
      whnfCore env fuel d ste = .ok (.sort wT) ∧
      Level.isEquiv wT (.max (us.getD 0 .zero) (us.getD 1 .zero)) = some true := by
  simp only [projCert, Bind.bind, Except.bind] at h
  cases hta : inferTypeCore env fuel d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hsta : inferTypeCore env fuel d ta with
  | error err => rw [hsta] at h; exact nomatch h
  | ok sta =>
  rw [hsta] at h
  dsimp only at h
  cases hwta : whnfCore env fuel d sta with
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
  cases heq1 : Level.isEquiv uT (us.getD i .zero) with
  | none => rw [heq1] at h; simp [liftFueled] at h
  | some okT =>
  rw [heq1] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  try dsimp only at h
  cases hte : inferTypeCore env fuel d e₂ with
  | error err => rw [hte] at h; exact nomatch h
  | ok te =>
  rw [hte] at h
  dsimp only at h
  cases hste : inferTypeCore env fuel d te with
  | error err => rw [hste] at h; exact nomatch h
  | ok ste =>
  rw [hste] at h
  dsimp only at h
  cases hwte : whnfCore env fuel d ste with
  | error err => rw [hwte] at h; exact nomatch h
  | ok wte =>
  rw [hwte] at h
  match wte, h with
  | .sort wT, h => ?_
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
  cases heq2 : Level.isEquiv wT (.max (us.getD 0 .zero) (us.getD 1 .zero)) with
  | none => rw [heq2] at h; simp [liftFueled] at h
  | some okW =>
  rw [heq2] at h
  try dsimp only [liftFueled] at h
  try simp only [pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨rfl, rfl⟩ : okT = true ∧ okW = true := by
    have := h
    cases okT <;> cases okW <;> simp_all
  exact ⟨ta, sta, uT, te, ste, wT, rfl, hsta, hwta, heq1, rfl, hste, hwte, heq2⟩

/-- Inversion of a successful iota step. -/
theorem iotaRec_inv {env : Env} {fuel d : Nat} {e eout : Expr}
    (h : iotaRec env (fuel + 1) d e = .ok (some eout)) :
    ∃ c us cv nP nM nm ni rules major₀ major cj usj cvj cnP cnF r,
      e.getAppFn = .const c us ∧
      env.find? c = some (.recInfo cv nP nM nm ni rules) ∧
      e.getAppArgs.length = nP + nM + nm + ni + 1 ∧
      whnfCore env fuel d (e.getAppArgs.getD (nP + nM + nm + ni) (.bvar 0)) =
        .ok major₀ ∧
      majorToCtor env fuel d c rules major₀ = .ok major ∧
      major.getAppFn = .const cj usj ∧
      env.find? cj = some (.ctorInfo cvj cnP cnF) ∧
      rules.find? (fun r' => r'.ctor == cj) = some r ∧
      major.getAppArgs.length = cnP + cnF ∧ r.nfields = cnF ∧
      (cv.type.stripPis (nP + nM + nm + ni + 1)).isSome = true ∧
      (cvj.type.stripPis (cnP + cnF)).isSome = true ∧
      Level.isEquivList usj (cvj.levelParams.map fun p =>
        Level.subst cv.levelParams us (.param p)) = some true ∧
      defEqList env fuel d (major.getAppArgs.take cnP)
        (e.getAppArgs.take cnP) = .ok true ∧
      iotaCerts env fuel d (cv.type.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take (nP + nM + nm + ni) ++ [major]) = .ok true ∧
      iotaCerts env fuel d (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = .ok true ∧
      eout = Expr.mkAppN (r.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take (nP + nM + nm) ++
          major.getAppArgs.drop cnP) := by
  simp only [iotaRec] at h
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
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo cv nP nM nm ni rules) => ?_
  intro h
  dsimp only at h
  by_cases hlen : e.getAppArgs.length = nP + nM + nm + ni + 1
  case neg => rw [if_neg hlen] at h; exact nomatch h
  rw [if_pos hlen] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hmaj : whnfCore env fuel d
      (e.getAppArgs.getD (nP + nM + nm + ni) (.bvar 0)) with
  | error err => rw [hmaj] at h; exact nomatch h
  | ok major₀ =>
  rw [hmaj] at h
  dsimp only at h
  cases hsub : majorToCtor env fuel d c rules major₀ with
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
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) => ?_
  intro h
  dsimp only at h
  revert h
  cases hrule : rules.find? (fun r' => r'.ctor == cj) with
  | none => intro h; exact nomatch h
  | some r =>
  intro h
  dsimp only at h
  by_cases hml : major.getAppArgs.length = cnP + cnF ∧ r.nfields = cnF
  case neg => rw [if_neg hml] at h; exact nomatch h
  obtain ⟨hml1, hml2⟩ := hml
  rw [if_pos ⟨hml1, hml2⟩] at h
  try simp only [Bind.bind, Except.bind] at h
  by_cases harities : (cv.type.stripPis (nP + nM + nm + ni + 1)).isSome = true ∧
      (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => rw [if_neg harities] at h; exact nomatch h
  obtain ⟨har1, har2⟩ := harities
  rw [if_pos ⟨har1, har2⟩] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hlev : Level.isEquivList usj (cvj.levelParams.map fun p =>
      Level.subst cv.levelParams us (.param p)) with
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
  cases hpeq : defEqList env fuel d (major.getAppArgs.take cnP)
      (e.getAppArgs.take cnP) with
  | error err => rw [hpeq] at h; exact nomatch h
  | ok rp =>
  rw [hpeq] at h
  dsimp only at h
  cases rp with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hcerts : iotaCerts env fuel d
      (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take (nP + nM + nm + ni) ++ [major]) with
  | error err => rw [hcerts] at h; exact nomatch h
  | ok rc =>
  rw [hcerts] at h
  dsimp only at h
  cases rc with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hmcerts : iotaCerts env fuel d
      (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs with
  | error err => rw [hmcerts] at h; exact nomatch h
  | ok rmc =>
  rw [hmcerts] at h
  dsimp only at h
  cases rmc with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq,
    Option.some.injEq] at h
  exact ⟨c, us, cv, nP, nM, nm, ni, rules, major₀, major, cj, usj, cvj, cnP,
    cnF, r, rfl, hfc, hlen, hmaj, hsub, hmfn, hfj, hrule, hml1, hml2, har1,
    har2, hlev, hpeq, hcerts, hmcerts, h.symm⟩

/-- Inversion of the stuck-major rescue: either the major is returned
unchanged, or a constructor application was fabricated — in the
K branch certified by proof irrelevance, in the structure-eta branch by
the structure-eta certificate — and its scoping was checked
syntactically (the scope guard). -/
theorem majorToCtor_inv {env : Env} {fuel d : Nat} {recName : Name}
    {rules : List RecRule} {major major' : Expr}
    (h : majorToCtor env (fuel + 1) d recName rules major = .ok major') :
    major' = major ∨
    (major'.wscopedB d = true ∧ major'.looseBVarsBounded 0 = true ∧
     major'.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true ∧
     ∃ r cvj cnP cnF tmaj₀ tmaj T us₀ ust cvT caps,
       rules = [r] ∧
       env.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
       (cvj.type.piResult).getAppFn = .const T us₀ ∧
       env.find? T = some (.indInfo cvT caps) ∧
       inferTypeCore env fuel d major = .ok tmaj₀ ∧
       whnfCore env fuel d tmaj₀ = .ok tmaj ∧
       tmaj.getAppFn = .const T ust ∧
       ((caps.ruleK = true ∧ cnF = 0 ∧
         cvj.levelParams.length = ust.length ∧
         major' = Expr.mkAppN (.const r.ctor ust)
           (tmaj.getAppArgs.take cnP) ∧
         proofIrrel env fuel d major' major = .ok true) ∨
        (caps.eta = true ∧ r.ctor = caps.etaCtor ∧
         Name.isProjFnShape recName = false ∧
         tmaj.getAppArgs.length = caps.etaParams ∧
         ust.length = cvT.levelParams.length ∧
         major' = Expr.mkAppN (.const caps.etaCtor ust)
           (tmaj.getAppArgs ++
             (List.range caps.etaFields).map fun j =>
               Expr.mkAppN (.const (projFnName T j) ust)
                 (tmaj.getAppArgs ++ [major])) ∧
         structEtaCert env fuel d major' major = .ok true))) := by
  simp only [majorToCtor] at h
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
  | [r] =>
  intro h
  dsimp only at h
  revert h
  match hfj : env.find? r.ctor with
  | none =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.axiomInfo _) | some (.defnInfo _ _) | some (.thmInfo _ _)
  | some (.indInfo _ _) | some (.recInfo _ _ _ _ _ _) =>
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
  | some (.axiomInfo _) | some (.defnInfo _ _) | some (.thmInfo _ _)
  | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _ _ _) =>
    intro h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some (.indInfo cvT caps) =>
  intro h
  dsimp only at h
  by_cases hK : caps.ruleK = true ∧ cnF = 0
  · rw [if_pos hK] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hti : inferTypeCore env fuel d major with
    | error err => rw [hti] at h; exact nomatch h
    | ok tmaj₀ =>
    rw [hti] at h
    dsimp only at h
    cases htw : whnfCore env fuel d tmaj₀ with
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
    cases hguard : (Expr.mkAppN (.const r.ctor ust)
          (tmaj.getAppArgs.take cnP)).wscopedB d &&
        (Expr.mkAppN (.const r.ctor ust)
          (tmaj.getAppArgs.take cnP)).looseBVarsBounded 0 &&
        (Expr.mkAppN (.const r.ctor ust)
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
    cases hpi : proofIrrel env fuel d
        (Expr.mkAppN (.const r.ctor ust)
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
      r, cvj, cnP, cnF, tmaj₀, tmaj, T', us₀, ust, cvT, caps,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inl ⟨hK.1, hK.2, hlvl, rfl, hpi⟩⟩
  · rw [if_neg hK] at h
    by_cases hE : caps.eta = true ∧ r.ctor = caps.etaCtor ∧
        Name.isProjFnShape recName = false
    case neg =>
      rw [if_neg hE] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    rw [if_pos hE] at h
    try simp only [Bind.bind, Except.bind] at h
    cases hti : inferTypeCore env fuel d major with
    | error err => rw [hti] at h; exact nomatch h
    | ok tmaj₀ =>
    rw [hti] at h
    dsimp only at h
    cases htw : whnfCore env fuel d tmaj₀ with
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
        ust.length = cvT.levelParams.length
    case neg =>
      rw [if_neg hTl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    obtain ⟨rfl, hplen, hlvl⟩ := hTl
    rw [if_pos ⟨rfl, hplen, hlvl⟩] at h
    cases hguard : (Expr.mkAppN (.const caps.etaCtor ust)
          (tmaj.getAppArgs ++
            (List.range caps.etaFields).map fun j =>
              Expr.mkAppN (.const (projFnName T' j) ust)
                (tmaj.getAppArgs ++ [major]))).wscopedB d &&
        (Expr.mkAppN (.const caps.etaCtor ust)
          (tmaj.getAppArgs ++
            (List.range caps.etaFields).map fun j =>
              Expr.mkAppN (.const (projFnName T' j) ust)
                (tmaj.getAppArgs ++ [major]))).looseBVarsBounded 0 &&
        (Expr.mkAppN (.const caps.etaCtor ust)
          (tmaj.getAppArgs ++
            (List.range caps.etaFields).map fun j =>
              Expr.mkAppN (.const (projFnName T' j) ust)
                (tmaj.getAppArgs ++ [major]))).fvarLeaves.all
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
    cases hse : structEtaCert env fuel d
        (Expr.mkAppN (.const caps.etaCtor ust)
          (tmaj.getAppArgs ++
            (List.range caps.etaFields).map fun j =>
              Expr.mkAppN (.const (projFnName T' j) ust)
                (tmaj.getAppArgs ++ [major]))) major with
    | error err => rw [hse] at h; exact nomatch h
    | ok bse =>
    rw [hse] at h
    dsimp only at h
    cases bse with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl h.symm
    | true =>
    simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hguard
    exact Or.inr ⟨hguard.1.1, hguard.1.2, hguard.2,
      r, cvj, cnP, cnF, tmaj₀, tmaj, T', us₀, ust, cvT, caps,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      Or.inr ⟨hE.1, hE.2.1, hE.2.2, hplen, hlvl, rfl, hse⟩⟩


/-- Inversion of one pairwise-defeq step. -/
theorem defEqList_step_inv {env : Env} {fuel d : Nat} {a b : Expr}
    {as bs : List Expr}
    (h : defEqList env (fuel + 1) d (a :: as) (b :: bs) = .ok true) :
    isDefEqCore env fuel d a b = .ok true ∧
    defEqList env fuel d as bs = .ok true := by
  simp only [defEqList, Bind.bind, Except.bind] at h
  cases hde : isDefEqCore env fuel d a b with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨rfl, h⟩

/-- Inversion of one certification step. -/
theorem iotaCerts_step_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty body : Expr} {m : BinderMeta} {arg : Expr} {rest : List Expr}
    (h : iotaCerts env (fuel + 1) d (.forallE n ty body m) (arg :: rest) =
      .ok true) :
    ∃ ta, inferTypeCore env fuel d arg = .ok ta ∧
      isDefEqCore env fuel d ta ty = .ok true ∧
      iotaCerts env fuel d (body.instantiate1 arg) rest = .ok true := by
  simp only [iotaCerts, Bind.bind, Except.bind] at h
  cases hta : inferTypeCore env fuel d arg with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hde : isDefEqCore env fuel d ta ty with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  dsimp only at h
  cases r with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨ta, rfl, hde, h⟩

/-- Inversion of the unit-type check. -/
theorem isUnitLikeTy_inv {env : Env} {e : Expr}
    (h : isUnitLikeTy env e = true) :
    ∃ c us cvi capsi cvr nP nM nm r, e = .const c us ∧
      env.find? c = some (.indInfo cvi capsi) ∧
      env.find? (c.str "rec") = some (.recInfo cvr nP nM nm 0 [r]) ∧
      r.nfields = 0 ∧
      reservedBasisNames.contains (c.str "rec") = true := by
  match e, h with
  | .const c us, h =>
    simp only [isUnitLikeTy, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, hres⟩ := h
    revert h1
    match hfc : env.find? c with
    | none => intro h1; exact nomatch h1
    | some (.axiomInfo _) => intro h1; exact nomatch h1
    | some (.defnInfo _ _) => intro h1; exact nomatch h1
    | some (.thmInfo _ _) => intro h1; exact nomatch h1
    | some (.ctorInfo _ _ _) => intro h1; exact nomatch h1
    | some (.recInfo _ _ _ _ _ _) => intro h1; exact nomatch h1
    | some (.indInfo cvi capsi) => ?_
    intro _
    revert h2
    match hfr : env.find? (c.str "rec") with
    | none => intro h2; exact nomatch h2
    | some (.axiomInfo _) => intro h2; exact nomatch h2
    | some (.defnInfo _ _) => intro h2; exact nomatch h2
    | some (.thmInfo _ _) => intro h2; exact nomatch h2
    | some (.ctorInfo _ _ _) => intro h2; exact nomatch h2
    | some (.indInfo _ _) => intro h2; exact nomatch h2
    | some (.recInfo cvr nP nM nm ni rules) => ?_
    intro h2
    match ni, rules, h2 with
    | 0, [r], h2 =>
      have hr0 : r.nfields = 0 := by simpa using h2
      exact ⟨c, us, cvi, capsi, cvr, nP, nM, nm, r, rfl, hfc, hfr, hr0, hres⟩
    | 0, [], h2 => exact nomatch h2
    | 0, _ :: _ :: _, h2 => exact nomatch h2
    | _ + 1, _, h2 => exact nomatch h2

/-- Inversion of a successful proof-irrelevance certification: either
both sides' types whnf to the basis unit type, or both types' sorts are
`Prop`. -/
theorem proofIrrel_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : proofIrrel env (fuel + 1) d a b = .ok true) :
    ∃ ta wta,
      inferTypeCore env fuel d a = .ok ta ∧
      whnfCore env fuel d ta = .ok wta ∧
      ((isUnitLikeTy env wta = true ∧
        ∃ tb wtb, inferTypeCore env fuel d b = .ok tb ∧
          whnfCore env fuel d tb = .ok wtb ∧ isUnitLikeTy env wtb = true) ∨
       (∃ sta uT tb stb vT,
        inferTypeCore env fuel d ta = .ok sta ∧
        whnfCore env fuel d sta = .ok (.sort uT) ∧
        Level.isEquiv uT .zero = some true ∧
        inferTypeCore env fuel d b = .ok tb ∧
        inferTypeCore env fuel d tb = .ok stb ∧
        whnfCore env fuel d stb = .ok (.sort vT) ∧
        Level.isEquiv vT .zero = some true)) := by
  simp only [proofIrrel, Bind.bind, Except.bind] at h
  cases hta : inferTypeCore env fuel d a with
  | error err => rw [hta] at h; exact nomatch h
  | ok ta =>
  rw [hta] at h
  dsimp only at h
  cases hwta0 : whnfCore env fuel d ta with
  | error err => rw [hwta0] at h; exact nomatch h
  | ok wta0 =>
  rw [hwta0] at h
  dsimp only at h
  refine ⟨ta, wta0, rfl, hwta0, ?_⟩
  by_cases hu : isUnitLikeTy env wta0 = true
  · -- unit branch
    rw [if_pos hu] at h
    try simp only [Bind.bind, Except.bind] at h
    cases htb : inferTypeCore env fuel d b with
    | error err => rw [htb] at h; exact nomatch h
    | ok tb =>
    rw [htb] at h
    dsimp only at h
    cases hwtb : whnfCore env fuel d tb with
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
    cases hsta : inferTypeCore env fuel d ta with
    | error err => rw [hsta] at h; exact nomatch h
    | ok sta =>
    rw [hsta] at h
    dsimp only at h
    cases hwta : whnfCore env fuel d sta with
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
    cases htb : inferTypeCore env fuel d b with
    | error err => rw [htb] at h; exact nomatch h
    | ok tb =>
    rw [htb] at h
    dsimp only at h
    cases hstb : inferTypeCore env fuel d tb with
    | error err => rw [hstb] at h; exact nomatch h
    | ok stb =>
    rw [hstb] at h
    dsimp only at h
    cases hwtb : whnfCore env fuel d stb with
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

/-- Inversion of a successful pair-eta certification. -/
theorem pairEtaCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : pairEtaCert env (fuel + 1) d a b = .ok true) :
    ∃ c us pα pβ s₁ s₂ cvm tb c' us' A B cvi capsi cvr nP nM nm r,
      a = .app (.app (.app (.app (.const c us) pα) pβ) s₁) s₂ ∧
      env.find? c = some (.ctorInfo cvm 2 2) ∧
      inferTypeCore env fuel d b = .ok tb ∧
      whnfCore env fuel d tb = .ok (.app (.app (.const c' us') A) B) ∧
      env.find? c' = some (.indInfo cvi capsi) ∧
      env.find? (c'.str "rec") = some (.recInfo cvr nP nM nm 0 [r]) ∧
      r.ctor = c ∧ r.nfields = 2 ∧
      reservedBasisNames.contains (c'.str "rec") = true ∧
      Level.isEquivList us us' = some true ∧
      isDefEqCore env fuel d s₁ (.proj c' 0 b) = .ok true ∧
      isDefEqCore env fuel d s₂ (.proj c' 1 b) = .ok true := by
  match a, h with
  | .app (.app (.app (.app (.const c us) pα) pβ) s₁) s₂, h => ?_
  | .bvar _, h => exact nomatch h
  | .fvar _ _ _, h => exact nomatch h
  | .sort _, h => exact nomatch h
  | .const _ _, h => exact nomatch h
  | .lam _ _ _ _, h => exact nomatch h
  | .forallE _ _ _ _, h => exact nomatch h
  | .letE _ _ _ _, h => exact nomatch h
  | .lit _, h => exact nomatch h
  | .proj _ _ _, h => exact nomatch h
  | .app (.bvar _) _, h => exact nomatch h
  | .app (.fvar _ _ _) _, h => exact nomatch h
  | .app (.sort _) _, h => exact nomatch h
  | .app (.const _ _) _, h => exact nomatch h
  | .app (.lam _ _ _ _) _, h => exact nomatch h
  | .app (.forallE _ _ _ _) _, h => exact nomatch h
  | .app (.letE _ _ _ _) _, h => exact nomatch h
  | .app (.lit _) _, h => exact nomatch h
  | .app (.proj _ _ _) _, h => exact nomatch h
  | .app (.app (.bvar _) _) _, h => exact nomatch h
  | .app (.app (.fvar _ _ _) _) _, h => exact nomatch h
  | .app (.app (.sort _) _) _, h => exact nomatch h
  | .app (.app (.const _ _) _) _, h => exact nomatch h
  | .app (.app (.lam _ _ _ _) _) _, h => exact nomatch h
  | .app (.app (.forallE _ _ _ _) _) _, h => exact nomatch h
  | .app (.app (.letE _ _ _ _) _) _, h => exact nomatch h
  | .app (.app (.lit _) _) _, h => exact nomatch h
  | .app (.app (.proj _ _ _) _) _, h => exact nomatch h
  | .app (.app (.app (.bvar _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.fvar _ _ _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.sort _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.const _ _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.bvar _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.fvar _ _ _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.sort _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.app _ _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.lam _ _ _ _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.forallE _ _ _ _) _) _) _) _, h =>
    exact nomatch h
  | .app (.app (.app (.app (.letE _ _ _ _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.lit _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.app (.proj _ _ _) _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.lam _ _ _ _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.forallE _ _ _ _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.letE _ _ _ _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.lit _) _) _) _, h => exact nomatch h
  | .app (.app (.app (.proj _ _ _) _) _) _, h => exact nomatch h
  dsimp only [pairEtaCert] at h
  revert h
  match hfc : env.find? c with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvm nP0 nF0) => ?_
  intro h
  dsimp only at h
  by_cases hpf : nP0 = 2 ∧ nF0 = 2
  case neg => rw [if_neg hpf] at h; exact nomatch h
  obtain ⟨rfl, rfl⟩ := hpf
  rw [if_pos ⟨rfl, rfl⟩] at h
  try simp only [Bind.bind, Except.bind] at h
  cases htb : inferTypeCore env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnfCore env fuel d tb with
  | error err => rw [hwtb] at h; exact nomatch h
  | ok wtb =>
  rw [hwtb] at h
  match wtb, h with
  | .app (.app (.const c' us') A) B, h => ?_
  | .bvar _, h => exact nomatch h
  | .fvar _ _ _, h => exact nomatch h
  | .sort _, h => exact nomatch h
  | .const _ _, h => exact nomatch h
  | .lam _ _ _ _, h => exact nomatch h
  | .forallE _ _ _ _, h => exact nomatch h
  | .letE _ _ _ _, h => exact nomatch h
  | .lit _, h => exact nomatch h
  | .proj _ _ _, h => exact nomatch h
  | .app (.bvar _) _, h => exact nomatch h
  | .app (.fvar _ _ _) _, h => exact nomatch h
  | .app (.sort _) _, h => exact nomatch h
  | .app (.const _ _) _, h => exact nomatch h
  | .app (.lam _ _ _ _) _, h => exact nomatch h
  | .app (.forallE _ _ _ _) _, h => exact nomatch h
  | .app (.letE _ _ _ _) _, h => exact nomatch h
  | .app (.lit _) _, h => exact nomatch h
  | .app (.proj _ _ _) _, h => exact nomatch h
  | .app (.app (.bvar _) _) _, h => exact nomatch h
  | .app (.app (.fvar _ _ _) _) _, h => exact nomatch h
  | .app (.app (.sort _) _) _, h => exact nomatch h
  | .app (.app (.app _ _) _) _, h => exact nomatch h
  | .app (.app (.lam _ _ _ _) _) _, h => exact nomatch h
  | .app (.app (.forallE _ _ _ _) _) _, h => exact nomatch h
  | .app (.app (.letE _ _ _ _) _) _, h => exact nomatch h
  | .app (.app (.lit _) _) _, h => exact nomatch h
  | .app (.app (.proj _ _ _) _) _, h => exact nomatch h
  dsimp only at h
  revert h
  match hfc' : env.find? c' with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.indInfo cvi capsi) => ?_
  intro h
  dsimp only at h
  revert h
  match hfr : env.find? (c'.str "rec") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo cvr nP nM nm ni rules) => ?_
  intro h
  dsimp only at h
  match rules, h with
  | [], h => exact nomatch h
  | _ :: _ :: _, h => exact nomatch h
  | [r], h => ?_
  dsimp only at h
  by_cases hg : ni = 0 ∧ r.ctor = c ∧ r.nfields = 2 ∧
      reservedBasisNames.contains (c'.str "rec") = true
  case neg => rw [if_neg hg] at h; exact nomatch h
  obtain ⟨rfl, hrc, hrf, hgres⟩ := hg
  rw [if_pos ⟨rfl, hrc, hrf, hgres⟩] at h
  try simp only [Bind.bind, Except.bind] at h
  cases hlev : Level.isEquivList us us' with
  | none => rw [hlev] at h; simp [liftFueled] at h
  | some okL =>
  rw [hlev] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  cases okL with
  | false => simp at h
  | true =>
  simp only [↓reduceIte] at h
  cases hd1 : isDefEqCore env fuel d s₁ (.proj c' 0 b) with
  | error err => rw [hd1] at h; exact nomatch h
  | ok r₁ =>
  rw [hd1] at h
  dsimp only at h
  cases r₁ with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨c, us, pα, pβ, s₁, s₂, cvm, tb, c', us', A, B, cvi, capsi, cvr,
    nP, nM, nm, r, rfl, hfc, rfl, hwtb, hfc', hfr, hrc, hrf, hgres,
    hlev, hd1, h⟩

/-- Invert the per-projection telescope certificates. -/
theorem structEtaProjCerts_inv {env : Env} {d : Nat} {T : Name}
    {us' : List Level} {targs : List Expr} {b : Expr} {lpsT : List Name} :
    ∀ (idxs : List Nat) (fuel : Nat),
      structEtaProjCerts env (fuel + 1) d T us' targs b lpsT idxs
        = .ok true →
      ∀ i ∈ idxs, ∃ (fl : Nat) (cvp : ConstantVal)
        (nPp nMp nmp nip : Nat) (rulesp : List RecRule),
        fl ≤ fuel ∧
        env.find? (projFnName T i) =
          some (.recInfo cvp nPp nMp nmp nip rulesp) ∧
        cvp.levelParams = lpsT ∧
        (cvp.type.stripPis (targs.length + 1)).isSome = true ∧
        iotaCerts env fl d
          (cvp.type.instantiateLevelParams cvp.levelParams us')
          (targs ++ [b]) = .ok true
  | [], _, _, i, hi => nomatch hi
  | i₀ :: rest, fuel, h, i, hi => by
    rw [structEtaProjCerts] at h
    revert h
    match hfp : env.find? (projFnName T i₀) with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.recInfo cvp nPp nMp nmp nip rulesp) => ?_
    intro h
    dsimp only at h
    by_cases hlps : cvp.levelParams = lpsT ∧
        (cvp.type.stripPis (targs.length + 1)).isSome = true
    case neg => rw [if_neg hlps] at h; exact nomatch h
    rw [if_pos hlps] at h
    obtain ⟨hlps, hstrp⟩ := hlps
    simp only [Bind.bind, Except.bind] at h
    cases hic : iotaCerts env fuel d
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
    · exact ⟨fuel, cvp, nPp, nMp, nmp, nip, rulesp, Nat.le_refl _,
        hfp, hlps, hstrp, hic⟩
    · match fuel, h with
      | fuel + 1, h =>
        obtain ⟨fl, cvp', nPp', nMp', nmp', nip', rulesp', hfl, hfp',
          hlps', hstrp', hic'⟩ := structEtaProjCerts_inv rest fuel h i hi'
        exact ⟨fl, cvp', nPp', nMp', nmp', nip', rulesp',
          Nat.le_trans hfl (Nat.le_succ _), hfp', hlps', hstrp', hic'⟩

set_option maxHeartbeats 3200000 in
/-- Inversion of a successful structural eta certification. -/
theorem structEtaCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structEtaCert env (fuel + 1) d a b = .ok true) :
    ∃ (c : Name) (us : List Level) (cvc : ConstantVal) (cnP cnF : Nat)
      (tb wtb : Expr) (T : Name) (us' : List Level)
      (cvT : ConstantVal) (caps : IndCaps),
      a.getAppFn = .const c us ∧
      env.find? c = some (.ctorInfo cvc cnP cnF) ∧
      a.getAppArgs.length = cnP + cnF ∧
      inferTypeCore env fuel d b = .ok tb ∧
      whnfCore env fuel d tb = .ok wtb ∧
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
      iotaCerts env fuel d
        (cvT.type.instantiateLevelParams cvT.levelParams us')
        wtb.getAppArgs = .ok true ∧
      structEtaProjCerts env fuel d T us' wtb.getAppArgs b
        cvT.levelParams (List.range cnF) = .ok true ∧
      defEqList env fuel d (a.getAppArgs.take cnP) wtb.getAppArgs
        = .ok true ∧
      defEqList env fuel d (a.getAppArgs.drop cnP)
        ((List.range cnF).map fun i =>
          Expr.mkAppN (.const (projFnName T i) us')
            (wtb.getAppArgs ++ [b])) = .ok true := by
  rw [structEtaCert] at h
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
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvc cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hal : a.getAppArgs.length = cnP + cnF
  case neg => rw [if_neg hal] at h; exact nomatch h
  rw [if_pos hal] at h
  simp only [Bind.bind, Except.bind] at h
  cases htb : inferTypeCore env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb => ?_
  rw [htb] at h
  try dsimp only at h
  cases hwtb : whnfCore env fuel d tb with
  | error e => rw [hwtb] at h; exact nomatch h
  | ok wtb => ?_
  rw [hwtb] at h
  try dsimp only at h
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
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
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
  cases hic : iotaCerts env fuel d
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
  cases hpc : structEtaProjCerts env fuel d T us' wtb.getAppArgs b
      cvT.levelParams (List.range cnF) with
  | error e => rw [hpc] at h; exact nomatch h
  | ok r₂ => ?_
  rw [hpc] at h
  try dsimp only at h
  cases r₂ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  cases hd1 : defEqList env fuel d (a.getAppArgs.take cnP)
      wtb.getAppArgs with
  | error e => rw [hd1] at h; exact nomatch h
  | ok r₃ => ?_
  rw [hd1] at h
  try dsimp only at h
  cases r₃ with
  | false => simp [pure, Except.pure] at h
  | true => ?_
  simp only [↓reduceIte] at h
  exact ⟨c, us, cvc, cnP, cnF, tb, wtb, T, us', cvT, caps,
    rfl, hfc, hal, rfl, hwtb, hwfn, hfT, he1, he2, he3, he4, he5,
    he5b, he6, he7, he8, he9, hlev, hic, hpc, hd1, h⟩

/-- Inversion of a successful unit-likeness certification. -/
theorem structUnitCert_inv {env : Env} {fuel d : Nat} {a b : Expr}
    (h : structUnitCert env (fuel + 1) d a b = .ok true) :
    ∃ (ta wta : Expr) (T : Name) (us' : List Level)
      (cvT : ConstantVal) (caps : IndCaps) (tb wtb : Expr),
      inferTypeCore env fuel d a = .ok ta ∧
      whnfCore env fuel d ta = .ok wta ∧
      wta.getAppFn = .const T us' ∧
      env.find? T = some (.indInfo cvT caps) ∧
      caps.unitlike = true ∧
      reservedBasisNames.contains T = false ∧
      wta.getAppArgs.length = caps.unitParams ∧
      us'.length = cvT.levelParams.length ∧
      (cvT.type.stripPis caps.unitParams).isSome = true ∧
      inferTypeCore env fuel d b = .ok tb ∧
      whnfCore env fuel d tb = .ok wtb ∧
      isDefEqCore env fuel d wta wtb = .ok true ∧
      iotaCerts env fuel d
        (cvT.type.instantiateLevelParams cvT.levelParams us')
        wta.getAppArgs = .ok true := by
  rw [structUnitCert] at h
  simp only [Bind.bind, Except.bind] at h
  cases hta : inferTypeCore env fuel d a with
  | error e => rw [hta] at h; exact nomatch h
  | ok ta => ?_
  rw [hta] at h
  try dsimp only at h
  cases hwta : whnfCore env fuel d ta with
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
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
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
  cases htb : inferTypeCore env fuel d b with
  | error e => rw [htb] at h; exact nomatch h
  | ok tb => ?_
  rw [htb] at h
  try dsimp only at h
  cases hwtb : whnfCore env fuel d tb with
  | error e => rw [hwtb] at h; exact nomatch h
  | ok wtb => ?_
  rw [hwtb] at h
  try dsimp only at h
  cases hde : isDefEqCore env fuel d wta wtb with
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
    (h : etaCert env (fuel + 1) d n₁ ty₁ body₁ m₁ b = .ok true) :
    ∃ tb n₂ ty₂ fb m₂ v₁ v₂,
      inferTypeCore env fuel d b = .ok tb ∧
      whnfCore env fuel d tb = .ok (.forallE n₂ ty₂ fb m₂) ∧
      m₁.cod = some v₁ ∧ m₂.cod = some v₂ ∧
      Level.isEquiv v₁ v₂ = some true ∧
      isDefEqCore env fuel d ty₂ ty₁ = .ok true ∧
      isDefEqCore env fuel (d + 1) (body₁.instantiate1 (.fvar d n₁ ty₁))
        (.app b (.fvar d n₁ ty₁)) = .ok true := by
  simp only [etaCert, Bind.bind, Except.bind] at h
  cases htb : inferTypeCore env fuel d b with
  | error err => rw [htb] at h; exact nomatch h
  | ok tb =>
  rw [htb] at h
  dsimp only at h
  cases hwtb : whnfCore env fuel d tb with
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
  cases hm₁ : m₁.cod with
  | none => rw [hm₁] at h; exact nomatch h
  | some v₁ =>
  rw [hm₁] at h
  cases hm₂ : m₂.cod with
  | none => rw [hm₂] at h; exact nomatch h
  | some v₂ =>
  rw [hm₂] at h
  dsimp only at h
  cases heq : Level.isEquiv v₁ v₂ with
  | none => rw [heq] at h; simp [liftFueled] at h
  | some okL =>
  rw [heq] at h
  try dsimp only [liftFueled] at h
  try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  cases okL with
  | false => simp at h
  | true =>
  simp only [↓reduceIte] at h
  cases hd1 : isDefEqCore env fuel d ty₂ ty₁ with
  | error err => rw [hd1] at h; exact nomatch h
  | ok r₁ =>
  rw [hd1] at h
  dsimp only at h
  cases r₁ with
  | false => simp [pure, Except.pure] at h
  | true =>
  simp only [↓reduceIte] at h
  exact ⟨tb, n₂, ty₂, fb, m₂, v₁, v₂, rfl, hwtb, rfl, hm₂, heq, hd1, h⟩

/-- Inversion for the projection rule of `inferTypeCore`. -/
theorem inferTypeCore_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat}
    {e t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.proj sn i e) = .ok t) :
    ∃ te us A B cv caps, inferTypeCore env fuel d e = .ok te ∧
      whnfCore env fuel d te = .ok (.app (.app (.const psigmaName us) A) B) ∧
      env.find? psigmaName = some (.indInfo cv caps) ∧
      ((i = 0 ∧ t = A) ∨ (i = 1 ∧ t = .app B (.proj sn 0 e))) := by
  simp only [inferTypeCore, Bind.bind, Except.bind] at h
  cases hte : inferTypeCore env fuel d e with
  | error err => rw [hte] at h; exact nomatch h
  | ok te =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnfCore env fuel d te with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  dsimp only at h
  match w, h with
  | .app w1 B, h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i2 n2 t2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .forallE n2 t2 b2 m2, h => exact nomatch h
  | .bvar i2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  match w1, h with
  | .app w2 A, h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i2 n2 t2, h => exact nomatch h
  | .const n2 us2, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .forallE n2 t2 b2 m2, h => exact nomatch h
  | .bvar i2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  match w2, h with
  | .const c us, h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i2 n2 t2, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .forallE n2 t2 b2 m2, h => exact nomatch h
  | .bvar i2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  cases hfind : env.find? c with
  | none => rw [hfind] at h; exact nomatch h
  | some ci =>
  rw [hfind] at h
  cases ci with
  | indInfo cv _ => ?_
  | axiomInfo cv => exact nomatch h
  | defnInfo cv value => exact nomatch h
  | thmInfo cv value => exact nomatch h
  | ctorInfo cv nP nF => exact nomatch h
  | recInfo cv nP nM nm ni rules => exact nomatch h
  dsimp only at h
  by_cases hc : c = psigmaName
  · rw [if_pos hc] at h
    subst hc
    match i, h with
    | 0, h =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨te, us, A, B, cv, _, rfl, hw, hfind, Or.inl ⟨rfl, h.symm⟩⟩
    | 1, h =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨te, us, A, B, cv, _, rfl, hw, hfind, Or.inr ⟨rfl, h.symm⟩⟩
    | (n + 2), h => exact nomatch h
  · rw [if_neg hc] at h
    exact nomatch h

/-! ## Well-scopedness preservation through reduction -/

set_option maxRecDepth 2048 in
theorem whnf_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr},
      whnfCore env fuel d e = .ok e' → WScoped d e → WScoped d e'
  | 0, d, e, e', h, _ => nomatch h
  | fuel + 1, d, e, e', h, hw => by
    match e, h with
    | .sort u, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hw
    | .fvar idx n ty, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hw
    | .forallE n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hw
    | .lam n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hw
    | .const n ws, h =>
      simp only [whnfCore] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ hw
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
            obtain ⟨hvc, -, -, -⟩ := hval cv value rfl
            exact whnf_WScoped henv fuel h
              (WScoped.of_not_hasFvar (by
                rw [hasFvar_instantiateLevelParams]; exact hvc))
          next hal => exact (Except.ok.inj h) ▸ hw
        | axiomInfo cv => exact (Except.ok.inj h) ▸ hw
        | thmInfo cv value => exact (Except.ok.inj h) ▸ hw
        | indInfo cv _ => exact (Except.ok.inj h) ▸ hw
        | ctorInfo cv nP nF => exact (Except.ok.inj h) ▸ hw
        | recInfo cv nP nM nm ni rules => exact (Except.ok.inj h) ▸ hw
    | .app f a, h =>
      simp only [WScoped] at hw
      obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
      have hwf' : WScoped d f' := whnf_WScoped henv fuel hwf hw.1
      rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, -⟩ |
        ⟨e'', hio, hwe''⟩ | rfl
      · simp only [WScoped] at hwf'
        exact whnf_WScoped henv fuel hbeta
          (WScoped.instantiate1_gen hw.2 0 hwf'.2)
      · -- iota step
        cases fuel with
        | zero => exact nomatch hio
        | succ fuel' =>
        obtain ⟨c, us, cv, nP, nM, nm, ni, rules, major, cj, usj, cvj,
          cnP, cnF, r, hfn, hfc, hlen, hmaj, hmfn, hfj, hrule, hml1, hml2,
          har1, har2, hlev, hpeq, hcerts, hmcerts, rfl⟩ := iotaRec_inv hio
        have hwapp : WScoped d (Expr.app f' a) := by
          simp only [WScoped]
          exact ⟨hwf', hw.2⟩
        have hargs : ∀ x, x ∈ (Expr.app f' a).getAppArgs → WScoped d x :=
          fun x hx => hwapp.getAppArgs x hx
        have hrhs : WScoped d
            (r.rhs.instantiateLevelParams cv.levelParams us) := by
          obtain ⟨-, -, -, -, -, hrules⟩ := henv _ (find?_mem hfc)
          obtain ⟨hrf, -, -, -⟩ := hrules cv nP nM nm ni rules rfl r
            (List.mem_of_find?_eq_some hrule)
          exact WScoped.of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact hrf)
        have hmajw : WScoped d major := whnf_WScoped henv fuel' hmaj
          (hargs _ (getD_mem (by omega)))
        refine whnf_WScoped henv _ hwe'' ?_
        refine Expr.WScoped.mkAppN hrhs ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hargs _ (List.mem_of_mem_take hx)
        · exact hmajw.getAppArgs _ (List.mem_of_mem_drop hx)
      · simp only [WScoped]
        exact ⟨hwf', hw.2⟩
    | .proj sn i e, h =>
      simp only [WScoped] at hw
      obtain ⟨e₂, he, hcase⟩ := whnf_proj_inv h
      have hwe₂ : WScoped d e₂ := whnf_WScoped henv fuel he hw
      rcases hcase with rfl | ⟨us, cv, nP, nF, hfn, hf, hi, hlen, hus, hred, -⟩
      · simpa [WScoped] using hwe₂
      · exact whnf_WScoped henv fuel hred
          (hwe₂.getAppArgs _ (getD_mem (by omega)))
  termination_by fuel => fuel
  decreasing_by all_goals omega

end Setlec
