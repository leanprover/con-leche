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
            obtain ⟨-, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨hvc, -, -⟩ := hval cv value rfl
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

end Setlec
