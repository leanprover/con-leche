import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift
import Setlec.Verify.InstLevels
import Setlec.Verify.EnvWF

/-!
# Preservation lemmas for `whnf` and `inferType`

Under environment well-formedness (`EnvWF`), reduction and inference
preserve the syntactic invariants the model soundness proofs thread:
well-scopedness here; the free-variable leaf closure in
`Setlec.Verify.InferLeaves`.

(The instLevels/mono/constsResolve commutation family that used to live
here was only needed while the interpretation re-ran inference; it died
with the sort-annotation design.)
-/

namespace Setlec

open Expr

theorem find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts :=
  List.mem_of_find?_eq_some h

theorem whnf_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {e e' : Expr} {d : Nat},
      whnf env fuel e = .ok e' → WScoped d e → WScoped d e'
  | 0, e, e', d, h, _ => nomatch h
  | fuel + 1, e, e', d, h, hw => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hw
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hw
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hw
    | .lam n ty body bi, h => exact (Except.ok.inj h) ▸ hw
    | .const n ws, h =>
      simp only [whnf] at h
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
      simp only [whnf] at h
      cases hwf : whnf env fuel f with
      | error err => rw [hwf] at h; exact nomatch h
      | ok f' =>
        rw [hwf] at h
        simp only [Bind.bind, Except.bind] at h
        have hwf' : WScoped d f' := whnf_WScoped henv fuel hwf hw.1
        match f', h with
        | .lam n ty body m, h =>
          simp only [WScoped] at hwf'
          dsimp only at h
          cases hc : m.cod with
          | none =>
            rw [hc] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp only [WScoped]
            exact ⟨hwf', hw.2⟩
          | some v =>
            rw [hc] at h
            dsimp only at h
            split at h
            next =>
              exact whnf_WScoped henv fuel h
                (WScoped.instantiate1_gen hw.2 0 hwf'.2)
            next =>
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp only [WScoped]
              exact ⟨hwf', hw.2⟩
        | .sort u, h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .fvar i n' t', h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .const n' us, h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .forallE n' t' b' m', h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .bvar i, h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .app f'' a'', h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .letE n' t' v' b', h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .lit l', h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩
        | .proj s' i' e'', h =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [WScoped]
          exact ⟨by simp_all [WScoped], hw.2⟩


/-! ## Inversion lemmas for the new kernel branches -/

/-- Inversion for `whnf` on applications. -/
theorem whnf_app_inv {env : Env} {fuel : Nat} {f a e' : Expr}
    (h : whnf env (fuel + 1) (.app f a) = .ok e') :
    ∃ f', whnf env fuel f = .ok f' ∧
      ((∃ n ty body m v, f' = .lam n ty body m ∧ m.cod = some v ∧
          v.isNonZero = true ∧ whnf env fuel (body.instantiate1 a) = .ok e') ∨
        e' = .app f' a) := by
  simp only [whnf, Bind.bind, Except.bind] at h
  cases hwf : whnf env fuel f with
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
      next hnz => exact Or.inl ⟨n, ty, body, m, v, rfl, hc, hnz, h⟩
      next hnz =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
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
      ensureSort env tty = .ok u ∧
      inferTypeCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty)) = .ok bt ∧
      inferTypeCore env fuel (d + 1) bt = .ok tbt ∧
      ensureSort env tbt = .ok v' ∧
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
  cases hu : ensureSort env tty with
  | error err => rw [hu] at h; exact nomatch h
  | ok u =>
  rw [hu] at h
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
  cases hes : ensureSort env tbt with
  | error err => rw [hes] at h; exact nomatch h
  | ok v' =>
  rw [hes] at h
  dsimp only at h
  cases heq : Level.isEquiv v v' with
  | none => rw [heq] at h; simp [liftFueled] at h
  | some b =>
  rw [heq] at h
  cases b with
  | false => simp [liftFueled, pure, Except.pure] at h
  | true =>
    simp only [liftFueled, Bool.false_eq_true, pure, Except.pure, ↓reduceIte,
      Except.ok.injEq] at h
    exact ⟨v, tty, u, bt, tbt, v', rfl, rfl, hu, rfl, htbt, hes, heq, h.symm⟩

/-- Inversion for the application rule of `inferTypeCore`. -/
theorem inferTypeCore_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m' ta, inferTypeCore env fuel d f = .ok tf ∧
      whnf env whnfFuel tf = .ok (.forallE n' ty' body' m') ∧
      inferTypeCore env fuel d a = .ok ta ∧
      isDefEq env d ta ty' = .ok true ∧
      t = body'.instantiate1 a := by
  simp only [inferTypeCore, Bind.bind, Except.bind] at h
  cases htf : inferTypeCore env fuel d f with
  | error err => rw [htf] at h; exact nomatch h
  | ok tf =>
  rw [htf] at h
  dsimp only at h
  cases hw : whnf env whnfFuel tf with
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
  cases hde : isDefEq env d ta ty' with
  | error err => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => simp [pure, Except.pure] at h
  | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tf, n', ty', body', m', ta, rfl, hw, rfl, hde, h.symm⟩

end Setlec
