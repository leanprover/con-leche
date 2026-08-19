import Setlec.Kernel.TypeChecker
import Setlec.Model.InterpLemmas

/-!
# Soundness of the type checker functions

All statements are relative to a model `m : EnvModel V env` of the current
environment and interpret with `m.val`:

* `whnf_sound`: reduction preserves the interpretation (delta unfolding is
  justified by `m.defn_eq`).
* `ensureSort_sound`: a successful `ensureSort env t = .ok u` means
  `⟦t⟧ = univ (eval φ u)`.
* `inferType_sound`: a successful inference means expression and type are
  interpreted and `⟦e⟧ ∈ ⟦t⟧`, under the local-context assumptions
  (`FvarsOk`) and well-scopedness.
* `isDefEqCore_sound`: a positive definitional-equality verdict means the
  interpretations agree whenever both are defined.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

private theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- `whnf` preserves the local-context assumptions. -/
theorem whnf_FvarsOk {cval : ConstVal V} (henv : EnvWF env) :
    ∀ (fuel : Nat) {e e' : Expr} {d : Nat} {ρ : Nat → V},
      whnf env fuel e = .ok e' →
      FvarsOk V cval env φ d ρ e → FvarsOk V cval env φ d ρ e'
  | 0, e, e', d, ρ, h, _ => nomatch h
  | fuel + 1, e, e', d, ρ, h, hok => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ hok
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ hok
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ hok
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ hok
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, hval⟩ := henv _ (List.mem_of_find?_eq_some hf)
            obtain ⟨hvc, -, -⟩ := hval cv value rfl
            exact whnf_FvarsOk henv fuel h
              (FvarsOk.of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact hvc))
          next hal => exact (Except.ok.inj h) ▸ hok
        | axiomInfo cv => exact (Except.ok.inj h) ▸ hok
        | thmInfo cv value => exact (Except.ok.inj h) ▸ hok

/-- Reduction preserves the interpretation. -/
theorem whnf_sound (m : EnvModel V env) :
    ∀ (fuel : Nat) {e e' : Expr} {d : Nat} {ρ : Nat → V},
      whnf env fuel e = .ok e' →
      interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e
  | 0, e, e', d, ρ, h => nomatch h
  | fuel + 1, e, e', d, ρ, h => by
    match e, h with
    | .sort u, h => rw [Except.ok.inj h]
    | .fvar idx n ty, h => rw [Except.ok.inj h]
    | .forallE n ty body bi, h => rw [Except.ok.inj h]
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; rw [Except.ok.inj h]
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, hval⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
            obtain ⟨hvc, -, -⟩ := hval cv value rfl
            rw [whnf_sound m fuel h]
            have hcl : (value.instantiateLevelParams cv.levelParams ws).hasFvar = false := by
              rw [hasFvar_instantiateLevelParams]; exact hvc
            rw [interp_closed_invariant m.wf hcl]
            unfold interpClosed
            rw [interp_instLevels m.wf m.val_params]
            have hmem : ConstantInfo.defnInfo cv value ∈ env.consts :=
              List.mem_of_find?_eq_some hf
            have hde := m.defn_eq cv value hmem (Level.substFn φ cv.levelParams ws)
            unfold interpClosed at hde
            rw [hde]
            have hname : cv.name = n := by
              have := find?_name hf
              simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
            rw [interp_const hf hal, hname]
            rfl
          next hal => rw [Except.ok.inj h]
        | axiomInfo cv => rw [Except.ok.inj h]
        | thmInfo cv value => rw [Except.ok.inj h]

/-- A successful `ensureSort` identifies the interpretation of the type
with a universe. -/
theorem ensureSort_sound (m : EnvModel V env) {t : Expr} {u : Level}
    (h : ensureSort env t = .ok u) {d : Nat} {ρ : Nat → V} :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSort at h
  cases hw : whnf env whnfFuel t with
  | error e => rw [hw] at h; exact nomatch h
  | ok w =>
    rw [hw] at h
    have hpres := whnf_sound (φ := φ) m whnfFuel (d := d) (ρ := ρ) hw
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure, interpExpr]

/-- Successful inference is sound. -/
theorem inferType_sound (m : EnvModel V env) : ∀ (e : Expr) {d : Nat} {t : Expr} {ρ : Nat → V},
    inferType env d e = .ok t → WScoped d e → FvarsOk V m.val env φ d ρ e →
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
      WScoped d t ∧ FvarsOk V m.val env φ d ρ t
  | .sort u, d, t, ρ, h, _, _ => by
    simp only [inferType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨⟨univ (u.eval φ), univ (u.eval φ + 1), ?_, ?_, univ_mem_univ _⟩, ?_, ?_⟩ <;>
      simp [interpExpr, Level.eval, WScoped, FvarsOk]
  | .fvar idx n ty, d, t, ρ, h, hw, hok => by
    simp only [inferType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    obtain ⟨hidx, hFty, T, hT, hmem⟩ := hok
    exact ⟨⟨ρ idx, T, by simp [interpExpr], hT, hmem⟩, hw.2.mono (by omega), hFty⟩
  | .const n ws, d, t, ρ, h, hw, hok => by
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
        obtain ⟨htc, -, -, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
        have hcl : (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams ws).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]; exact htc
        obtain ⟨T, hT, hmem⟩ :=
          m.mem_type ci (List.mem_of_find?_eq_some hf)
            (Level.substFn φ ci.toConstantVal.levelParams ws)
        refine ⟨⟨m.val n (Level.substFn φ ci.toConstantVal.levelParams ws), T, ?_, ?_, ?_⟩,
          WScoped.of_not_hasFvar hcl, FvarsOk.of_not_hasFvar hcl⟩
        · simp only [interpExpr, hf]
          rw [if_pos hal]
        · rw [interp_closed_invariant m.wf hcl]
          unfold interpClosed
          rw [interp_instLevels m.wf m.val_params]
          exact hT
        · have hname : ci.name = n := find?_name hf
          simp only [ConstantInfo.name] at hname
          rw [← hname]
          exact hmem
      next hal => exact nomatch h
  | .forallE n ty body bi, d, t, ρ, h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
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
    obtain ⟨⟨A, tA, hA, htA, hmemA⟩, -, -⟩ := inferType_sound m ty hty hw.1 hok.1
    rw [ensureSort_sound m hsty] at htA
    obtain rfl := Option.some.inj htA
    have hsl : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) =
        some (v.eval φ) := by
      unfold sortLevelOf
      rw [hb]
      simp [Bind.bind, Except.bind, hsb]
    refine ⟨⟨pi (v.eval φ) A (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      univ ((Level.imax u v).eval φ), ?_, ?_, ?_⟩, by simp [WScoped], by simp [FvarsOk]⟩
    · simp only [interpExpr, hA, hsl]
    · simp only [interpExpr]
    · have hpi := pi_mem_univ (V := V) (v := v.eval φ)
        (B := fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
        hmemA
        (fun x hx => by
          obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, -, -⟩ :=
            inferType_sound m (body.instantiate1 (.fvar d n ty)) hb
              (hw.1.instantiate1 0 hw.2)
              (FvarsOk.instantiate1 m.wf hw.1 hok.1 hA hx body 0 hw.2 hok.2)
          rw [ensureSort_sound m hsb] at htw
          obtain rfl := Option.some.inj htw
          simpa [hwi] using hmemw)
      have heq : Level.eval φ (.imax u v) =
          if v.eval φ = 0 then 0 else Nat.max (u.eval φ) (v.eval φ) := rfl
      rw [heq]
      exact hpi
  | .bvar _, _, _, _, h, _, _ => by simp [inferType] at h
  | .app _ _, _, _, _, h, _, _ => by simp [inferType] at h
  | .lam _ _ _ _, _, _, _, h, _, _ => by simp [inferType] at h
  | .letE _ _ _ _, _, _, _, h, _, _ => by simp [inferType] at h
  | .lit _, _, _, _, h, _, _ => by simp [inferType] at h
  | .proj _ _ _, _, _, _, h, _, _ => by simp [inferType] at h
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- A positive definitional-equality verdict means the interpretations
agree, whenever both are defined. -/
theorem isDefEqCore_sound (m : EnvModel V env) :
    ∀ (fuel : Nat) {d : Nat} {a b : Expr} {ρ : Nat → V},
    isDefEqCore env fuel d a b = .ok true →
    WScoped d a → WScoped d b → FvarsOk V m.val env φ d ρ a → FvarsOk V m.val env φ d ρ b →
    ∀ {va vb : V}, interpExpr V m.val env φ d ρ a = some va →
      interpExpr V m.val env φ d ρ b = some vb → va = vb := by
  intro fuel
  induction fuel with
  | zero => intro d a b ρ h; exact nomatch h
  | succ fuel ih =>
    intro d a b ρ h hwa hwb hoka hokb va vb hva hvb
    unfold isDefEqCore at h
    simp only [Bind.bind, Except.bind] at h
    cases hwha : whnf env whnfFuel a with
    | error e => rw [hwha] at h; exact nomatch h
    | ok a' =>
    rw [hwha] at h
    dsimp only at h
    cases hwhb : whnf env whnfFuel b with
    | error e => rw [hwhb] at h; exact nomatch h
    | ok b' =>
    rw [hwhb] at h
    dsimp only at h
    -- transfer facts through reduction
    rw [← whnf_sound (φ := φ) m whnfFuel hwha] at hva
    rw [← whnf_sound (φ := φ) m whnfFuel hwhb] at hvb
    have hwa' := whnf_WScoped m.wf whnfFuel hwha hwa
    have hwb' := whnf_WScoped m.wf whnfFuel hwhb hwb
    have hoka' := whnf_FvarsOk (cval := m.val) m.wf whnfFuel hwha hoka
    have hokb' := whnf_FvarsOk (cval := m.val) m.wf whnfFuel hwhb hokb
    clear hwha hwhb hwa hwb hoka hokb
    match a', b', h with
    | Expr.sort u, Expr.sort v, h =>
      dsimp only at h
      simp only [interpExpr, Option.some.injEq] at hva hvb
      subst hva; subst hvb
      have : Level.isEquiv u v = some true := by
        revert h
        cases hEq : Level.isEquiv u v with
        | none => simp [liftFueled]
        | some x => cases x <;> simp [liftFueled, pure, Except.pure]
      rw [Level.isEquiv_sound this φ]
    | Expr.fvar i ni tyi, Expr.fvar j nj tyj, h =>
      dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      have hij : i = j := by simpa using h.symm
      subst hij
      simp only [interpExpr, Option.some.injEq] at hva hvb
      subst hva; subst hvb
      rfl
    | Expr.const n us, Expr.const n' us', h =>
      dsimp only at h
      split at h
      next hnn =>
        subst hnn
        have hlev : Level.isEquivList us us' = some true := by
          revert h
          cases hEq : Level.isEquivList us us' with
          | none => simp [liftFueled]
          | some x => cases x <;> simp [liftFueled, pure, Except.pure]
        simp only [interpExpr] at hva hvb
        cases hf : env.find? n with
        | none => rw [hf] at hva; exact nomatch hva
        | some ci =>
        rw [hf] at hva hvb
        dsimp only at hva hvb
        by_cases hal : us.length = ci.toConstantVal.levelParams.length
        · rw [if_pos hal] at hva
          have hal' : us'.length = ci.toConstantVal.levelParams.length := by
            have := Level.isEquivList_length hlev
            omega
          rw [if_pos hal'] at hvb
          simp only [Option.some.injEq] at hva hvb
          subst hva; subst hvb
          rw [Level.substFn_congr (Level.isEquivList_sound hlev φ)]
        · rw [if_neg hal] at hva
          exact nomatch hva
      next hnn => simp [pure, Except.pure] at h
    | Expr.forallE n₁ ty₁ body₁ bi₁, Expr.forallE n₂ ty₂ body₂ bi₂, h =>
      dsimp only at h
      simp only [WScoped] at hwa' hwb'
      simp only [FvarsOk] at hoka' hokb'
      cases hd1 : isDefEqCore env fuel d ty₁ ty₂ with
      | error e => rw [hd1] at h; exact nomatch h
      | ok r₁ =>
      rw [hd1] at h
      dsimp only at h
      cases r₁ with
      | false => simp [pure, Except.pure] at h
      | true =>
      simp only [] at h
      cases hd2 : isDefEqCore env fuel (d + 1)
          (body₁.instantiate1 (.fvar d n₁ ty₁)) (body₂.instantiate1 (.fvar d n₂ ty₂)) with
      | error e => rw [hd2] at h; exact nomatch h
      | ok r₂ =>
      rw [hd2] at h
      dsimp only at h
      cases r₂ with
      | false => simp [pure, Except.pure] at h
      | true =>
      simp only [] at h
      cases hi1 : inferType env (d + 1) (body₁.instantiate1 (.fvar d n₁ ty₁)) with
      | error e => rw [hi1] at h; exact nomatch h
      | ok t₁ =>
      rw [hi1] at h
      dsimp only at h
      cases hs1 : ensureSort env t₁ with
      | error e => rw [hs1] at h; exact nomatch h
      | ok v₁ =>
      rw [hs1] at h
      dsimp only at h
      cases hi2 : inferType env (d + 1) (body₂.instantiate1 (.fvar d n₂ ty₂)) with
      | error e => rw [hi2] at h; exact nomatch h
      | ok t₂ =>
      rw [hi2] at h
      dsimp only at h
      cases hs2 : ensureSort env t₂ with
      | error e => rw [hs2] at h; exact nomatch h
      | ok v₂ =>
      rw [hs2] at h
      dsimp only at h
      have hlev : Level.isEquiv v₁ v₂ = some true := by
        revert h
        cases hEq : Level.isEquiv v₁ v₂ with
        | none => simp [liftFueled]
        | some x => cases x <;> simp [liftFueled, pure, Except.pure]
      simp only [interpExpr] at hva hvb
      cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
      | none => rw [hA1] at hva; exact nomatch hva
      | some A₁ =>
      rw [hA1] at hva
      cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
      | none => rw [hA2] at hvb; exact nomatch hvb
      | some A₂ =>
      rw [hA2] at hvb
      have hsl1 : sortLevelOf env φ (d + 1) (body₁.instantiate1 (.fvar d n₁ ty₁)) =
          some (v₁.eval φ) := by
        unfold sortLevelOf; rw [hi1]; simp [Bind.bind, Except.bind, hs1]
      have hsl2 : sortLevelOf env φ (d + 1) (body₂.instantiate1 (.fvar d n₂ ty₂)) =
          some (v₂.eval φ) := by
        unfold sortLevelOf; rw [hi2]; simp [Bind.bind, Except.bind, hs2]
      rw [hsl1] at hva
      rw [hsl2] at hvb
      simp only [Option.some.injEq] at hva hvb
      subst hva; subst hvb
      have hAeq : A₁ = A₂ := ih hd1 hwa'.1 hwb'.1 hoka'.1 hokb'.1 hA1 hA2
      subst hAeq
      have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
      rw [← hveq]
      refine pi_congr fun x hx => ?_
      obtain ⟨⟨w₁, tw₁, hw₁, -, -⟩, -, -⟩ :=
        inferType_sound (φ := φ) m (body₁.instantiate1 (.fvar d n₁ ty₁)) hi1
          (hwa'.1.instantiate1 0 hwa'.2)
          (FvarsOk.instantiate1 m.wf hwa'.1 hoka'.1 hA1 hx body₁ 0 hwa'.2 hoka'.2)
      obtain ⟨⟨w₂, tw₂, hw₂, -, -⟩, -, -⟩ :=
        inferType_sound (φ := φ) m (body₂.instantiate1 (.fvar d n₂ ty₂)) hi2
          (hwb'.1.instantiate1 0 hwb'.2)
          (FvarsOk.instantiate1 m.wf hwb'.1 hokb'.1 hA2 hx body₂ 0 hwb'.2 hokb'.2)
      rw [hw₁, hw₂]
      simpa using ih hd2
        (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
        (FvarsOk.instantiate1 m.wf hwa'.1 hoka'.1 hA1 hx body₁ 0 hwa'.2 hoka'.2)
        (FvarsOk.instantiate1 m.wf hwb'.1 hokb'.1 hA2 hx body₂ 0 hwb'.2 hokb'.2)
        hw₁ hw₂
    | Expr.sort _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h

theorem isDefEq_sound (m : EnvModel V env) {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : isDefEq env d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  isDefEqCore_sound m defEqFuel h hwa hwb hoka hokb hva hvb

end Setlec
