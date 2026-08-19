import Setlec.Kernel.TypeChecker
import Setlec.Model.InterpLemmas

/-!
# Soundness of the type checker functions

* `whnf_id`: in the current fragment `whnf` is the identity on success
  (this lemma will be replaced by an interpretation-preservation lemma once
  reduction does real work).
* `ensureSort_sound`: a successful `ensureSort` means the expression *is*
  that sort (current fragment).
* `inferType_sound`: a successful inference means expression and type are
  interpreted and `⟦e⟧ ∈ ⟦t⟧`, under the local-context assumptions
  (`FvarsOk`) and well-scopedness.
* `isDefEqCore_sound`: a positive definitional-equality verdict means the
  interpretations agree whenever both are defined.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

theorem whnf_id {e e' : Expr} (h : whnf env e = .ok e') : e' = e := by
  cases e <;> simp_all [whnf, pure, Except.pure]

theorem ensureSort_sound {t : Expr} {u : Level} (h : ensureSort env t = .ok u) :
    t = .sort u := by
  unfold ensureSort at h
  cases hw : whnf env t with
  | error e => rw [hw] at h; exact nomatch h
  | ok w =>
    rw [hw] at h
    obtain rfl := whnf_id hw
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure]

/-- Successful inference is sound: the expression and its inferred type are
interpreted, the former a member of the latter, and the inferred type is
again well-scoped with valid context assumptions. -/
theorem inferType_sound : ∀ (e : Expr) {d : Nat} {t : Expr} {ρ : Nat → V},
    inferType env d e = .ok t → WScoped d e → FvarsOk V env φ d ρ e →
    (∃ v tv, interpExpr V env φ d ρ e = some v ∧ interpExpr V env φ d ρ t = some tv ∧
      v ∈ˢ tv) ∧ WScoped d t ∧ FvarsOk V env φ d ρ t
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
    obtain ⟨⟨A, tA, hA, htA, hmemA⟩, -, -⟩ := inferType_sound ty hty hw.1 hok.1
    obtain rfl := ensureSort_sound hsty
    simp only [interpExpr, Option.some.injEq] at htA
    subst htA
    have hsl : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) =
        some (v.eval φ) := by
      unfold sortLevelOf
      rw [hb]
      simp [Bind.bind, Except.bind, hsb]
    refine ⟨⟨pi (v.eval φ) A (fun x => (interpExpr V env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      univ ((Level.imax u v).eval φ), ?_, ?_, ?_⟩, by simp [WScoped], by simp [FvarsOk]⟩
    · simp only [interpExpr, hA, hsl]
    · simp only [interpExpr]
    · -- pi vE A B ∈ univ (eval (imax u v))
      have hpi := pi_mem_univ (V := V) (v := v.eval φ)
        (B := fun x => (interpExpr V env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
        hmemA
        (fun x hx => by
          obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, -, -⟩ :=
            inferType_sound (body.instantiate1 (.fvar d n ty)) hb
              (hw.1.instantiate1 0 hw.2)
              (FvarsOk.instantiate1 hw.1 hok.1 hA hx body 0 hw.2 hok.2)
          obtain rfl := ensureSort_sound hsb
          simp only [interpExpr, Option.some.injEq] at htw
          subst htw
          simpa [hwi] using hmemw)
      have heq : Level.eval φ (.imax u v) =
          if v.eval φ = 0 then 0 else Nat.max (u.eval φ) (v.eval φ) := rfl
      rw [heq]
      exact hpi
  | .bvar _, _, _, _, h, _, _ => by simp [inferType] at h
  | .const _ _, _, _, _, h, _, _ => by simp [inferType] at h
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
theorem isDefEqCore_sound : ∀ (fuel : Nat) {d : Nat} {a b : Expr} {ρ : Nat → V},
    isDefEqCore env fuel d a b = .ok true →
    WScoped d a → WScoped d b → FvarsOk V env φ d ρ a → FvarsOk V env φ d ρ b →
    ∀ {va vb : V}, interpExpr V env φ d ρ a = some va →
      interpExpr V env φ d ρ b = some vb → va = vb := by
  intro fuel
  induction fuel with
  | zero => intro d a b ρ h; exact nomatch h
  | succ fuel ih =>
    intro d a b ρ h hwa hwb hoka hokb va vb hva hvb
    unfold isDefEqCore at h
    simp only [Bind.bind, Except.bind] at h
    cases hwha : whnf env a with
    | error e => rw [hwha] at h; exact nomatch h
    | ok a' =>
    rw [hwha] at h
    dsimp only at h
    obtain rfl := whnf_id hwha
    cases hwhb : whnf env b with
    | error e => rw [hwhb] at h; exact nomatch h
    | ok b' =>
    rw [hwhb] at h
    dsimp only at h
    obtain rfl := whnf_id hwhb
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
    | Expr.forallE n₁ ty₁ body₁ bi₁, Expr.forallE n₂ ty₂ body₂ bi₂, h =>
      dsimp only at h
      simp only [WScoped] at hwa hwb
      simp only [FvarsOk] at hoka hokb
      -- decompose the algorithm
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
      -- decompose the interpretations
      simp only [interpExpr] at hva hvb
      cases hA1 : interpExpr V env φ d ρ ty₁ with
      | none => rw [hA1] at hva; exact nomatch hva
      | some A₁ =>
      rw [hA1] at hva
      cases hA2 : interpExpr V env φ d ρ ty₂ with
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
      -- domains agree
      have hAeq : A₁ = A₂ := ih hd1 hwa.1 hwb.1 hoka.1 hokb.1 hA1 hA2
      subst hAeq
      -- codomain levels agree
      have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
      rw [← hveq]
      -- fibres agree on the domain
      refine pi_congr fun x hx => ?_
      obtain ⟨⟨w₁, tw₁, hw₁, -, -⟩, -, -⟩ :=
        inferType_sound (V := V) (φ := φ) (body₁.instantiate1 (.fvar d n₁ ty₁)) hi1
          (hwa.1.instantiate1 0 hwa.2)
          (FvarsOk.instantiate1 hwa.1 hoka.1 hA1 hx body₁ 0 hwa.2 hoka.2)
      obtain ⟨⟨w₂, tw₂, hw₂, -, -⟩, -, -⟩ :=
        inferType_sound (V := V) (φ := φ) (body₂.instantiate1 (.fvar d n₂ ty₂)) hi2
          (hwb.1.instantiate1 0 hwb.2)
          (FvarsOk.instantiate1 hwb.1 hokb.1 hA2 hx body₂ 0 hwb.2 hokb.2)
      rw [hw₁, hw₂]
      simpa using ih hd2
        (hwa.1.instantiate1 0 hwa.2) (hwb.1.instantiate1 0 hwb.2)
        (FvarsOk.instantiate1 hwa.1 hoka.1 hA1 hx body₁ 0 hwa.2 hoka.2)
        (FvarsOk.instantiate1 hwb.1 hokb.1 hA2 hx body₂ 0 hwb.2 hokb.2)
        hw₁ hw₂
    | Expr.sort _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h

theorem isDefEq_sound {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : isDefEq env d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hoka : FvarsOk V env φ d ρ a) (hokb : FvarsOk V env φ d ρ b)
    {va vb : V} (hva : interpExpr V env φ d ρ a = some va)
    (hvb : interpExpr V env φ d ρ b = some vb) : va = vb :=
  isDefEqCore_sound defEqFuel h hwa hwb hoka hokb hva hvb

end Setlec
