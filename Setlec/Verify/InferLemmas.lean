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
      exact Or.inr h.symm
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
          exact Or.inr h.symm
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inr h.symm

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
      | indInfo cv => exact Or.inl (Except.ok.inj h).symm
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

/-- Inversion for the projection rule of `inferTypeCore`. -/
theorem inferTypeCore_proj_inv {env : Env} {fuel d : Nat} {sn : Name} {i : Nat}
    {e t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.proj sn i e) = .ok t) :
    ∃ te us A B cv, inferTypeCore env fuel d e = .ok te ∧
      whnfCore env fuel d te = .ok (.app (.app (.const psigmaName us) A) B) ∧
      env.find? psigmaName = some (.indInfo cv) ∧
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
  | indInfo cv => ?_
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
      exact ⟨te, us, A, B, cv, rfl, hw, hfind, Or.inl ⟨rfl, h.symm⟩⟩
    | 1, h =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨te, us, A, B, cv, rfl, hw, hfind, Or.inr ⟨rfl, h.symm⟩⟩
    | (n + 2), h => exact nomatch h
  · rw [if_neg hc] at h
    exact nomatch h

/-! ## Well-scopedness preservation through reduction -/

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
            obtain ⟨-, -, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨hvc, -, -, -⟩ := hval cv value rfl
            exact whnf_WScoped henv fuel h
              (WScoped.of_not_hasFvar (by
                rw [hasFvar_instantiateLevelParams]; exact hvc))
          next hal => exact (Except.ok.inj h) ▸ hw
        | axiomInfo cv => exact (Except.ok.inj h) ▸ hw
        | thmInfo cv value => exact (Except.ok.inj h) ▸ hw
        | indInfo cv => exact (Except.ok.inj h) ▸ hw
        | ctorInfo cv nP nF => exact (Except.ok.inj h) ▸ hw
        | recInfo cv nP nM nm ni rules => exact (Except.ok.inj h) ▸ hw
    | .app f a, h =>
      simp only [WScoped] at hw
      obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
      have hwf' : WScoped d f' := whnf_WScoped henv fuel hwf hw.1
      rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, -⟩ | rfl
      · simp only [WScoped] at hwf'
        exact whnf_WScoped henv fuel hbeta
          (WScoped.instantiate1_gen hw.2 0 hwf'.2)
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

end Setlec
