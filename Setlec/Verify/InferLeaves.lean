import Setlec.Verify.InferLemmas
import Setlec.Verify.Leaves
import Setlec.Verify.Subst
import Setlec.Verify.Abstract

/-!
# Leaf-closure and loose-bvar preservation for `whnf` and `inferTypeCore`

Reduction and inference only ever *copy* material from the input (delta
unfoldings are closed), so their outputs' free-variable leaves are a
subset of the input's — which transports every leaf-closure condition
(`FvarsOk`, `LeavesBounded`, `LeafCond`) for free.  Loose-bvar bounds
are threaded via `LeavesBounded` (the `fvar` rule jumps into the
annotation).
-/

namespace Setlec

open Expr

/-- Every leaf annotation is bvar-closed. -/
def Expr.LeavesBounded (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, Expr.looseBVarsBounded 0 l.2.2 = true

/-- The per-index leaf condition backing `fvarConsistent`. -/
def Expr.LeafCond (d : Nat) (n : Name) (ty : Expr) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, l.1 = d → l.2.1 = n ∧ l.2.2 = ty

theorem Expr.fvarConsistent_of_leafCond {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr), Expr.LeafCond d n ty e → fvarConsistent d n ty e := by
  intro e
  induction e with
  | fvar idx n' ty' ih =>
    intro hc
    simp only [fvarConsistent]
    intro hd
    exact hc (idx, n', ty') (by simp [fvarLeaves]) hd
  | app f a ihf iha =>
    intro hc
    exact ⟨ihf (fun l hl => hc l (by simp [fvarLeaves, hl])),
      iha (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | lam n' ty' body m ihty ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | forallE n' ty' body m ihty ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | letE n' ty' val body ihty ihval ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihval (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | proj s i e ih =>
    intro hc
    exact ih (fun l hl => hc l (by simp [fvarLeaves, hl]))
  | _ => intro _; simp [fvarConsistent]

/-- The leaf condition holds for a freshly opened binder body. -/
theorem Expr.LeafCond_opened {d : Nat} {n : Name} {ty body : Expr}
    (hwty : WScoped d ty) (hwbody : WScoped d body) (k : Nat) :
    Expr.LeafCond d n ty (body.instantiate1 (.fvar d n ty) k) := by
  intro l hl hld
  rcases fvarLeaves_instantiate1 body k hl with hl' | hl'
  · obtain ⟨hlt, -⟩ := WScoped_leaves body hwbody l hl'
    omega
  · simp only [fvarLeaves, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · exact ⟨rfl, rfl⟩
    · obtain ⟨hlt, -⟩ := WScoped_leaves ty hwty l hl'
      omega

/-- Abstraction removes exactly the index-`d` leaves (for scoped terms). -/
theorem Expr.fvarLeaves_abstract1_ne {D : Nat} :
    ∀ (e : Expr) (k : Nat), WScoped (D + 1) e →
      ∀ l ∈ (e.abstract1 D k).fvarLeaves, l ∈ e.fvarLeaves ∧ l.1 ≠ D := by
  intro e
  induction e with
  | fvar idx n ty ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · next hne =>
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨by simp [fvarLeaves], hne⟩
      · obtain ⟨hlt, -⟩ := WScoped_leaves ty hw.2 l hl
        exact ⟨by simp [fvarLeaves, hl], by omega⟩
  | app f a ihf iha =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihf k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := iha k hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | lam n ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | forallE n ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihval k hw.2.1 l hl
      exact ⟨Or.inl (Or.inr h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | proj s i e ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih k hw l hl
  | bvar i => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | sort u => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | const n us => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | lit ll => intro k _ l hl; simp [abstract1, fvarLeaves] at hl

theorem Expr.LeavesBounded.of_not_hasFvar {e : Expr} (h : e.hasFvar = false) :
    Expr.LeavesBounded e := by
  intro l hl
  rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  cases hl

/-! ## Preservation through `whnf` -/

theorem whnf_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {e e' : Expr}, whnf env fuel e = .ok e' →
      ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves
  | 0, e, e', h => nomatch h
  | fuel + 1, e, e', h => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ fun l hl => hl
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ fun l hl => hl
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ fun l hl => hl
    | .lam n ty body bi, h => exact (Except.ok.inj h) ▸ fun l hl => hl
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ fun l hl => hl
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            intro l hl
            obtain ⟨-, -, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨hvc, -, -, -⟩ := hval cv value rfl
            have := whnf_fvarLeaves henv fuel h l hl
            rw [fvarLeaves_eq_nil_of_not_hasFvar
              (by rw [hasFvar_instantiateLevelParams]; exact hvc)] at this
            cases this
          next hal => exact (Except.ok.inj h) ▸ fun l hl => hl
        | axiomInfo cv => exact (Except.ok.inj h) ▸ fun l hl => hl
        | thmInfo cv value => exact (Except.ok.inj h) ▸ fun l hl => hl
    | .app f a, h =>
      intro l hl
      obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
      simp only [fvarLeaves, List.mem_append]
      rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hnz, hbeta⟩ | rfl
      · have hl' := whnf_fvarLeaves henv fuel hbeta l hl
        rcases fvarLeaves_instantiate1 body 0 hl' with hb | hb
        · exact Or.inl (whnf_fvarLeaves henv fuel hwf l (by simp [fvarLeaves, hb]))
        · exact Or.inr hb
      · simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact Or.inl (whnf_fvarLeaves henv fuel hwf l hl)
        · exact Or.inr hl

theorem whnf_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {e e' : Expr}, whnf env fuel e = .ok e' →
      e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true
  | 0, e, e', h, _ => nomatch h
  | fuel + 1, e, e', h, hb => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hb
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hb
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hb
    | .lam n ty body bi, h => exact (Except.ok.inj h) ▸ hb
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ hb
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨-, -, -, hvb⟩ := hval cv value rfl
            refine whnf_looseBVars henv fuel h ?_
            rw [looseBVarsBounded_instantiateLevelParams]
            exact hvb
          next hal => exact (Except.ok.inj h) ▸ hb
        | axiomInfo cv => exact (Except.ok.inj h) ▸ hb
        | thmInfo cv value => exact (Except.ok.inj h) ▸ hb
    | .app f a, h =>
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
      have hbf' := whnf_looseBVars henv fuel hwf hb.1
      rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hnz, hbeta⟩ | rfl
      · simp only [looseBVarsBounded, Bool.and_eq_true] at hbf'
        exact whnf_looseBVars henv fuel hbeta
          (looseBVarsBounded_instantiate1_gen hb.2 hbf'.2)
      · simp only [looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hbf', hb.2⟩

/-! ## Preservation through `inferTypeCore` -/

theorem inferTypeCore_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore env fuel d e = .ok t → WScoped d e → WScoped d t
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    match e, h with
    | .sort u, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [WScoped]
    | .fvar idx n ty, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [WScoped] at hw
      exact hw.2.mono (by omega)
    | .const n ws, h =>
      simp only [inferTypeCore] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact nomatch h
      | some ci =>
        rw [hf] at h
        dsimp only at h
        split at h
        next hal =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
          exact WScoped.of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact htc)
        next hal => exact nomatch h
    | .forallE n ty body m, h =>
      simp only [inferTypeCore] at h
      cases hc : m.cod with
      | none => rw [hc] at h; exact nomatch h
      | some v =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind] at h
        cases hty : inferTypeCore env fuel d ty with
        | error err => rw [hty] at h; exact nomatch h
        | ok tty =>
        rw [hty] at h
        dsimp only at h
        cases hes : ensureSort env tty with
        | error err => rw [hes] at h; exact nomatch h
        | ok u =>
        rw [hes] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [WScoped]
    | .lam n ty body m, h =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, hty2, hu2, hbt, htbt, hes, heq, rfl⟩ := inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCore_WScoped henv fuel hbt hwo
      simp only [WScoped]
      exact ⟨hw.1, WScoped.abstract1 0 hwbt⟩
    | .app f a, h =>
      obtain ⟨tf, n', ty', body', m', ta, htf, hwh, hta, hde, rfl⟩ := inferTypeCore_app_inv h
      simp only [WScoped] at hw
      have hwtf := inferTypeCore_WScoped henv fuel htf hw.1
      have hwPi := whnf_WScoped henv whnfFuel hwh hwtf
      simp only [WScoped] at hwPi
      exact WScoped.instantiate1_gen hw.2 0 hwPi.2
    | .bvar i, h => simp [inferTypeCore] at h
    | .letE n' t' v' b', h => simp [inferTypeCore] at h
    | .lit l', h => simp [inferTypeCore] at h
    | .proj s' i' e', h => simp [inferTypeCore] at h

theorem inferTypeCore_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore env fuel d e = .ok t → WScoped d e →
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    match e, h with
    | .sort u, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h; intro l hl; simp [fvarLeaves] at hl
    | .fvar idx n ty, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro l hl
      simp [fvarLeaves, hl]
    | .const n ws, h =>
      simp only [inferTypeCore] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact nomatch h
      | some ci =>
        rw [hf] at h
        dsimp only at h
        split at h
        next hal =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
          intro l hl
          rw [fvarLeaves_eq_nil_of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact htc)] at hl
          cases hl
        next hal => exact nomatch h
    | .forallE n ty body m, h =>
      simp only [inferTypeCore] at h
      cases hc : m.cod with
      | none => rw [hc] at h; exact nomatch h
      | some v =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind] at h
        cases hty : inferTypeCore env fuel d ty with
        | error err => rw [hty] at h; exact nomatch h
        | ok tty =>
        rw [hty] at h
        dsimp only at h
        cases hes : ensureSort env tty with
        | error err => rw [hes] at h; exact nomatch h
        | ok u =>
        rw [hes] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro l hl
        simp [fvarLeaves] at hl
    | .lam n ty body m, h =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, hty2, hu2, hbt, htbt, hes, heq, rfl⟩ := inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCore_WScoped henv fuel hbt hwo
      intro l hl
      simp only [fvarLeaves, List.mem_append] at hl ⊢
      rcases hl with hl | hl
      · exact Or.inl hl
      · obtain ⟨hlbt, hlne⟩ := fvarLeaves_abstract1_ne bt 0 hwbt l hl
        have hlo := inferTypeCore_fvarLeaves henv fuel hbt hwo l hlbt
        rcases fvarLeaves_instantiate1 body 0 hlo with hb | hb
        · exact Or.inr hb
        · simp only [fvarLeaves, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd rfl hlne
          · exact Or.inl hb
    | .app f a, h =>
      obtain ⟨tf, n', ty', body', m', ta, htf, hwh, hta, hde, rfl⟩ := inferTypeCore_app_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves, List.mem_append]
      rcases fvarLeaves_instantiate1 body' 0 hl with hb | hb
      · refine Or.inl (inferTypeCore_fvarLeaves henv fuel htf hw.1 l ?_)
        refine whnf_fvarLeaves henv whnfFuel hwh l ?_
        simp [fvarLeaves, hb]
      · exact Or.inr hb
    | .bvar i, h => simp [inferTypeCore] at h
    | .letE n' t' v' b', h => simp [inferTypeCore] at h
    | .lit l', h => simp [inferTypeCore] at h
    | .proj s' i' e', h => simp [inferTypeCore] at h

theorem inferTypeCore_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore env fuel d e = .ok t → WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      t.looseBVarsBounded 0 = true
  | 0, d, e, t, h, _, _, _ => nomatch h
  | fuel + 1, d, e, t, h, hw, hb, hLb => by
    match e, h with
    | .sort u, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [looseBVarsBounded]
    | .fvar idx n ty, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hLb (idx, n, ty) (by simp [fvarLeaves])
    | .const n ws, h =>
      simp only [inferTypeCore] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact nomatch h
      | some ci =>
        rw [hf] at h
        dsimp only at h
        split at h
        next hal =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨-, -, -, htb, -⟩ := henv _ (find?_mem hf)
          rw [looseBVarsBounded_instantiateLevelParams]
          exact htb
        next hal => exact nomatch h
    | .forallE n ty body m, h =>
      simp only [inferTypeCore] at h
      cases hc : m.cod with
      | none => rw [hc] at h; exact nomatch h
      | some v =>
        rw [hc] at h
        simp only [Bind.bind, Except.bind] at h
        cases hty : inferTypeCore env fuel d ty with
        | error err => rw [hty] at h; exact nomatch h
        | ok tty =>
        rw [hty] at h
        dsimp only at h
        cases hes : ensureSort env tty with
        | error err => rw [hes] at h; exact nomatch h
        | ok u =>
        rw [hes] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [looseBVarsBounded]
    | .lam n ty body m, h =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, hty2, hu2, hbt, htbt, hes, heq, rfl⟩ := inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hbo : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true :=
        looseBVarsBounded_instantiate1 body 0 hb.2
      have hLbo : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
        · exact hLb l (by simp [fvarLeaves, hb'])
        · simp only [fvarLeaves, List.mem_cons] at hb'
          rcases hb' with rfl | hb'
          · exact hb.1
          · exact hLb l (by simp [fvarLeaves, hb'])
      have hbbt := inferTypeCore_looseBVars henv fuel hbt hwo hbo hLbo
      simp only [looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 bt 0 hbbt⟩
    | .app f a, h =>
      obtain ⟨tf, n', ty', body', m', ta, htf, hwh, hta, hde, rfl⟩ := inferTypeCore_app_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
      have hbtf := inferTypeCore_looseBVars henv fuel htf hw.1 hb.1 hLbf
      have hbPi := whnf_looseBVars henv whnfFuel hwh hbtf
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      exact looseBVarsBounded_instantiate1_gen hb.2 hbPi.2
    | .bvar i, h => simp [inferTypeCore] at h
    | .letE n' t' v' b', h => simp [inferTypeCore] at h
    | .lit l', h => simp [inferTypeCore] at h
    | .proj s' i' e', h => simp [inferTypeCore] at h

end Setlec
