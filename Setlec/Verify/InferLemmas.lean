import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift
import Setlec.Verify.InstLevels
import Setlec.Verify.EnvWF

/-!
# Invariance and preservation lemmas for `whnf` and `inferType`

Under environment well-formedness (`EnvWF`):

* commutation with level instantiation (`whnf_instLevels`,
  `inferType_instLevels`) — needed because the interpretation classifies
  codomain sorts by re-running inference;
* preservation of well-scopedness and level-parameter bounds through
  reduction and inference;
* monotonicity under extending the environment with a fresh constant.
-/

namespace Setlec

open Expr

set_option linter.unusedSimpArgs false

private theorem find?_mem {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci ∈ env.consts :=
  List.mem_of_find?_eq_some h

/-! ## Level instantiation commutes with reduction and inference -/

theorem whnf_instLevels {env : Env} (henv : EnvWF env) (ks : List Name) (vs : List Level) :
    ∀ (fuel : Nat) (e : Expr),
      whnf env fuel (e.instantiateLevelParams ks vs) =
        Except.map (·.instantiateLevelParams ks vs) (whnf env fuel e)
  | 0, e => by simp [whnf, throw, throwThe, MonadExceptOf.throw, Except.map]
  | fuel + 1, e => by
    match e with
    | .sort u => simp [whnf, instantiateLevelParams, Except.map, pure, Except.pure]
    | .fvar idx n ty => simp [whnf, instantiateLevelParams, Except.map, pure, Except.pure]
    | .forallE n ty body bi =>
      simp [whnf, instantiateLevelParams, Except.map, pure, Except.pure]
    | .const n ws =>
      simp only [instantiateLevelParams, whnf]
      cases hf : env.find? n with
      | none => simp [Except.map, pure, Except.pure, instantiateLevelParams]
      | some ci =>
        cases ci with
        | defnInfo cv value =>
          simp only []
          have hlen : (ws.map (Level.subst ks vs)).length = ws.length := by simp
          by_cases hal : ws.length = cv.levelParams.length
          · rw [if_pos (by simpa [hlen] using hal), if_pos hal]
            obtain ⟨-, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨-, hvb, -⟩ := hval cv value rfl
            rw [← instantiateLevelParams_instantiateLevelParams
              (by simpa using hal) hvb]
            exact whnf_instLevels henv ks vs fuel (value.instantiateLevelParams cv.levelParams ws)
          · rw [if_neg (by simpa [hlen] using hal), if_neg hal]
            simp [Except.map, pure, Except.pure, instantiateLevelParams]
        | axiomInfo cv => simp [Except.map, pure, Except.pure, instantiateLevelParams]
        | thmInfo cv value => simp [Except.map, pure, Except.pure, instantiateLevelParams]
    | .bvar i => simp [whnf, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .app f a => simp [whnf, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .lam n ty body bi => simp [whnf, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .letE n ty val body => simp [whnf, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .lit l => simp [whnf, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .proj s i e' => simp [whnf, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]

theorem ensureSort_instLevels {env : Env} (henv : EnvWF env) (ks : List Name) (vs : List Level)
    (t : Expr) :
    ensureSort env (t.instantiateLevelParams ks vs) =
      Except.map (Level.subst ks vs) (ensureSort env t) := by
  unfold ensureSort
  rw [whnf_instLevels henv]
  cases h : whnf env whnfFuel t with
  | error e => rfl
  | ok w =>
    simp only [Except.map, Bind.bind, Except.bind]
    cases w <;>
      simp [instantiateLevelParams, pure, Except.pure, Except.map, throw, throwThe,
        MonadExceptOf.throw]

theorem inferType_instLevels {env : Env} (henv : EnvWF env) (ks : List Name) (vs : List Level) :
    ∀ (e : Expr) (d : Nat),
      inferType env d (e.instantiateLevelParams ks vs) =
        Except.map (·.instantiateLevelParams ks vs) (inferType env d e)
  | .sort u, d => by
    simp [inferType, instantiateLevelParams, Except.map, pure, Except.pure, Level.subst]
  | .fvar idx n ty, d => by
    simp [inferType, instantiateLevelParams, Except.map, pure, Except.pure]
  | .const n ws, d => by
    simp only [instantiateLevelParams, inferType]
    cases hf : env.find? n with
    | none => simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | some ci =>
      simp only []
      have hlen : (ws.map (Level.subst ks vs)).length = ws.length := by simp
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos (by simpa [hlen] using hal), if_pos hal]
        obtain ⟨-, htb, -, -⟩ := henv _ (find?_mem hf)
        simp only [Except.map, pure, Except.pure, Except.ok.injEq]
        exact (instantiateLevelParams_instantiateLevelParams (by simpa using hal) htb).symm
      · rw [if_neg (by simpa [hlen] using hal), if_neg hal]
        simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .forallE n ty body bi, d => by
    simp only [instantiateLevelParams, inferType]
    rw [← instantiateLevelParams_instantiate1]
    rw [inferType_instLevels henv ks vs ty d,
      inferType_instLevels henv ks vs (body.instantiate1 (.fvar d n ty)) (d + 1)]
    cases hty : inferType env d ty with
    | error e => simp [Except.map, Bind.bind, Except.bind]
    | ok tty =>
      simp only [Except.map, Bind.bind, Except.bind, ensureSort_instLevels henv]
      cases hsty : ensureSort env tty with
      | error e => simp [Except.map]
      | ok u =>
        simp only [Except.map]
        cases hb : inferType env (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | error e => simp [Except.map]
        | ok tb =>
          simp only [ensureSort_instLevels henv, Except.map]
          cases hsb : ensureSort env tb <;>
            simp [Except.map, pure, Except.pure, instantiateLevelParams, Level.subst]
  | .bvar i, d => by simp [inferType, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .app f a, d => by simp [inferType, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .lam n ty body bi, d => by simp [inferType, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .letE n ty val body, d => by simp [inferType, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .lit l, d => by simp [inferType, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .proj s i e', d => by simp [inferType, instantiateLevelParams, Except.map, throw, throwThe, MonadExceptOf.throw]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega


/-! ## Preservation of scoping and level-parameter bounds -/

theorem whnf_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {e e' : Expr} {d : Nat},
      whnf env fuel e = .ok e' → WScoped d e → WScoped d e'
  | 0, e, e', d, h, _ => nomatch h
  | fuel + 1, e, e', d, h, hw => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hw
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hw
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hw
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

theorem whnf_allLevelParams {env : Env} (henv : EnvWF env) {ps' : List Name} :
    ∀ (fuel : Nat) {e e' : Expr},
      whnf env fuel e = .ok e' → e.allLevelParamsDefined ps' = true →
      e'.allLevelParamsDefined ps' = true
  | 0, e, e', h, _ => nomatch h
  | fuel + 1, e, e', h, hp => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hp
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hp
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hp
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ hp
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨-, hvb, -⟩ := hval cv value rfl
            refine whnf_allLevelParams henv fuel h ?_
            exact allLevelParamsDefined_instantiateLevelParams hal
              (by simpa [allLevelParamsDefined] using hp) hvb
          next hal => exact (Except.ok.inj h) ▸ hp
        | axiomInfo cv => exact (Except.ok.inj h) ▸ hp
        | thmInfo cv value => exact (Except.ok.inj h) ▸ hp

theorem inferType_allLevelParams {env : Env} (henv : EnvWF env) {ps' : List Name} :
    ∀ (e : Expr) {d : Nat} {t : Expr},
      inferType env d e = .ok t → e.allLevelParamsDefined ps' = true →
      t.allLevelParamsDefined ps' = true
  | .sort u, d, t, h, hp => by
    simp only [inferType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simpa [allLevelParamsDefined, Level.allParamsDefined] using hp
  | .fvar idx n ty, d, t, h, hp => by
    simp only [inferType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simpa [allLevelParamsDefined] using hp
  | .const n ws, d, t, h, hp => by
    simp only [inferType] at h
    cases hf : env.find? n with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      next hal =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨-, htb, -, -⟩ := henv _ (find?_mem hf)
        exact allLevelParamsDefined_instantiateLevelParams hal
          (by simpa [allLevelParamsDefined] using hp) htb
      next hal => exact nomatch h
  | .forallE n ty body bi, d, t, h, hp => by
    simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
    obtain ⟨⟨hpty, hpbody⟩, -⟩ := hp
    simp only [inferType, Bind.bind, Except.bind] at h
    cases hty : inferType env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok tty =>
    rw [hty] at h
    dsimp only at h
    cases hsty : ensureSort env tty with
    | error e => rw [hsty] at h; exact nomatch h
    | ok u =>
    rw [hsty] at h
    dsimp only at h
    cases hb : inferType env (d + 1) (body.instantiate1 (.fvar d n ty)) with
    | error e => rw [hb] at h; exact nomatch h
    | ok tb =>
    rw [hb] at h
    dsimp only at h
    cases hsb : ensureSort env tb with
    | error e => rw [hsb] at h; exact nomatch h
    | ok v =>
    rw [hsb] at h
    dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hu : (Expr.sort u).allLevelParamsDefined ps' = true := by
      have h1 := inferType_allLevelParams henv ty hty hpty
      unfold ensureSort at hsty
      cases hw : whnf env whnfFuel tty with
      | error e => rw [hw] at hsty; exact nomatch hsty
      | ok w =>
        have h2 := whnf_allLevelParams henv whnfFuel hw h1
        rw [hw] at hsty
        cases w <;>
          simp_all [Bind.bind, Except.bind, pure, Except.pure, allLevelParamsDefined]
    have hv : (Expr.sort v).allLevelParamsDefined ps' = true := by
      have h1 := inferType_allLevelParams henv (body.instantiate1 (.fvar d n ty)) hb
        (allLevelParamsDefined_instantiate1 hpty 0 hpbody)
      unfold ensureSort at hsb
      cases hw : whnf env whnfFuel tb with
      | error e => rw [hw] at hsb; exact nomatch hsb
      | ok w =>
        have h2 := whnf_allLevelParams henv whnfFuel hw h1
        rw [hw] at hsb
        cases w <;>
          simp_all [Bind.bind, Except.bind, pure, Except.pure, allLevelParamsDefined]
    simp only [allLevelParamsDefined, Level.allParamsDefined] at hu hv ⊢
    simp [hu, hv]
  | .bvar _, _, _, h, _ => by simp [inferType] at h
  | .app _ _, _, _, h, _ => by simp [inferType] at h
  | .lam _ _ _ _, _, _, h, _ => by simp [inferType] at h
  | .letE _ _ _ _, _, _, h, _ => by simp [inferType] at h
  | .lit _, _, _, h, _ => by simp [inferType] at h
  | .proj _ _ _, _, _, h, _ => by simp [inferType] at h
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

theorem whnf_constsResolve {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {e e' : Expr},
      whnf env fuel e = .ok e' → e.constsResolve env = true →
      e'.constsResolve env = true
  | 0, e, e', h, _ => nomatch h
  | fuel + 1, e, e', h, hres => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hres
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hres
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hres
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ hres
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨-, -, hvr⟩ := hval cv value rfl
            exact whnf_constsResolve henv fuel h
              (by rw [constsResolve_instantiateLevelParams]; exact hvr)
          next hal => exact (Except.ok.inj h) ▸ hres
        | axiomInfo cv => exact (Except.ok.inj h) ▸ hres
        | thmInfo cv value => exact (Except.ok.inj h) ▸ hres

theorem inferType_constsResolve {env : Env} (henv : EnvWF env) :
    ∀ (e : Expr) {d : Nat} {t : Expr},
      inferType env d e = .ok t → e.constsResolve env = true →
      t.constsResolve env = true
  | .sort u, d, t, h, _ => by
    simp only [inferType, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [constsResolve]
  | .fvar idx n ty, d, t, h, hres => by
    simp only [inferType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simpa [constsResolve] using hres
  | .const n ws, d, t, h, hres => by
    simp only [inferType] at h
    cases hf : env.find? n with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      next hal =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨-, -, htr, -⟩ := henv _ (find?_mem hf)
        rw [constsResolve_instantiateLevelParams]
        exact htr
      next hal => exact nomatch h
  | .forallE n ty body bi, d, t, h, hres => by
    simp only [inferType, Bind.bind, Except.bind] at h
    cases hty : inferType env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok tty =>
    rw [hty] at h; dsimp only at h
    cases hsty : ensureSort env tty with
    | error e => rw [hsty] at h; exact nomatch h
    | ok u =>
    rw [hsty] at h; dsimp only at h
    cases hb : inferType env (d + 1) (body.instantiate1 (.fvar d n ty)) with
    | error e => rw [hb] at h; exact nomatch h
    | ok tb =>
    rw [hb] at h; dsimp only at h
    cases hsb : ensureSort env tb with
    | error e => rw [hsb] at h; exact nomatch h
    | ok v =>
    rw [hsb] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [constsResolve]
  | .bvar _, _, _, h, _ => by simp [inferType] at h
  | .app _ _, _, _, h, _ => by simp [inferType] at h
  | .lam _ _ _ _, _, _, h, _ => by simp [inferType] at h
  | .letE _ _ _ _, _, _, h, _ => by simp [inferType] at h
  | .lit _, _, _, h, _ => by simp [inferType] at h
  | .proj _ _ _, _, _, h, _ => by simp [inferType] at h

/-! ## Monotonicity under a fresh extension -/

variable {c₀ : ConstantInfo} {env : Env}

theorem whnf_mono (henv : EnvWF env) (hfresh : env.find? c₀.name = none) :
    ∀ (fuel : Nat) (e : Expr), e.constsResolve env = true →
      whnf ⟨c₀ :: env.consts⟩ fuel e = whnf env fuel e
  | 0, e, _ => rfl
  | fuel + 1, e, hres => by
    match e with
    | .sort u => rfl
    | .fvar idx n ty => rfl
    | .forallE n ty body bi => rfl
    | .const n ws =>
      simp only [constsResolve] at hres
      simp only [whnf, Env.find?_cons_of_isSome hfresh hres]
      cases hf : env.find? n with
      | none => rw [hf] at hres
      | some ci =>
        cases ci with
        | defnInfo cv value =>
          dsimp only
          split
          next hal =>
            obtain ⟨-, -, -, hval⟩ := henv _ (find?_mem hf)
            obtain ⟨-, -, hvr⟩ := hval cv value rfl
            exact whnf_mono henv hfresh fuel _
              (by rw [constsResolve_instantiateLevelParams]; exact hvr)
          next hal => rfl
        | axiomInfo cv => rfl
        | thmInfo cv value => rfl
    | .bvar i => rfl
    | .app f a => rfl
    | .lam n ty body bi => rfl
    | .letE n ty val body => rfl
    | .lit l => rfl
    | .proj s i e' => rfl

theorem ensureSort_mono (henv : EnvWF env) (hfresh : env.find? c₀.name = none)
    {t : Expr} (hres : t.constsResolve env = true) :
    ensureSort ⟨c₀ :: env.consts⟩ t = ensureSort env t := by
  unfold ensureSort
  rw [whnf_mono henv hfresh whnfFuel t hres]

theorem inferType_mono (henv : EnvWF env) (hfresh : env.find? c₀.name = none) :
    ∀ (e : Expr) (d : Nat), e.constsResolve env = true →
      inferType ⟨c₀ :: env.consts⟩ d e = inferType env d e
  | .sort u, d, _ => by simp [inferType]
  | .fvar idx n ty, d, _ => by simp [inferType]
  | .const n ws, d, hres => by
    simp only [constsResolve] at hres
    simp only [inferType, Env.find?_cons_of_isSome hfresh hres]
  | .forallE n ty body bi, d, hres => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [inferType]
    rw [inferType_mono henv hfresh ty d hres.1,
      inferType_mono henv hfresh (body.instantiate1 (.fvar d n ty)) (d + 1)
        (constsResolve_instantiate1 hres.1 0 hres.2)]
    cases hty : inferType env d ty with
    | error e => simp [Bind.bind, Except.bind]
    | ok tty =>
      simp only [Bind.bind, Except.bind]
      rw [ensureSort_mono henv hfresh (inferType_constsResolve henv ty hty hres.1)]
      cases hsty : ensureSort env tty with
      | error e => simp
      | ok u =>
        simp only []
        cases hb : inferType env (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | error e => simp
        | ok tb =>
          simp only []
          rw [ensureSort_mono henv hfresh
            (inferType_constsResolve henv _ hb (constsResolve_instantiate1 hres.1 0 hres.2))]
  | .bvar i, d, _ => by simp [inferType]
  | .app f a, d, _ => by simp [inferType]
  | .lam n ty body bi, d, _ => by simp [inferType]
  | .letE n ty val body, d, _ => by simp [inferType]
  | .lit l, d, _ => by simp [inferType]
  | .proj s i e', d, _ => by simp [inferType]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

end Setlec
