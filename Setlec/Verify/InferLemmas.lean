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

/-! ## Well-scopedness preservation through reduction -/

theorem whnf_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr},
      whnfCore env fuel d e = .ok e' → WScoped d e → WScoped d e'
  | 0, d, e, e', h, _ => nomatch h
  | fuel + 1, d, e, e', h, hw => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hw
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hw
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hw
    | .lam n ty body bi, h => exact (Except.ok.inj h) ▸ hw
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

end Setlec
