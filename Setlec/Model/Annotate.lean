import Setlec.Model.TypeChecker

/-!
# Soundness of the annotation pass

`annotate_sound`: the annotations `annotate` computes are truthful
(`AnnotOk`) — each binder's stored codomain sort really bounds the fibres
of its interpreted body.  This is where the one-time type-checking of
binder bodies pays out; `inferType` afterwards trusts the annotations,
and this theorem is what justifies that trust in the model.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

theorem annotate_sound (m : EnvModel V env) :
    ∀ (e : Expr) {d : Nat} {e' : Expr},
      annotate env d e = .ok e' → WScoped d e → e.looseBVarsBounded 0 = true →
      ∀ (ρ : Nat → V), FvarsOk V m.val env φ d ρ e →
        AnnotOk V m.val env φ d ρ e'
  | .bvar i, d, e', h, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .fvar idx n ty, d, e', h, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .sort u, d, e', h, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .const n us, d, e', h, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .app f a, d, e', h, hw, hb, ρ, hok => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [FvarsOk] at hok
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hf : annotate env d f with
    | error e => rw [hf] at h; exact nomatch h
    | ok f' =>
    rw [hf] at h; dsimp only at h
    cases ha : annotate env d a with
    | error e => rw [ha] at h; exact nomatch h
    | ok a' =>
    rw [ha] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [AnnotOk]
    exact ⟨annotate_sound m f hf hw.1 hb.1 ρ hok.1,
      annotate_sound m a ha hw.2 hb.2 ρ hok.2⟩
  | .forallE n ty body mb, d, e', h, hw, hb, ρ, hok => by
    have hle := annotate_leafEquiv (env := env) (.forallE n ty body mb) h hw hb
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [FvarsOk] at hok
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSort env bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- shared syntactic facts
    have hwty' : WScoped d ty' := annotate_WScoped ty hty hw.1
    have hwin : WScoped (d + 1) (body.instantiate1 (.fvar d n ty')) :=
      hwty'.instantiate1 0 hw.2
    have hbin : (body.instantiate1 (.fvar d n ty')).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    have hwbody' : WScoped (d + 1) body' := annotate_WScoped _ hbody hwin
    have hrt : (body'.abstract1 d).instantiate1 (.fvar d n ty') 0 = body' :=
      abstract1_instantiate1 body' 0
        (annotate_fvarConsistent _ (by omega) hbody
          (fvarConsistent_instantiate1 body 0 hw.2.fvarsBelow))
        (annotate_looseBVars _ hbody hbin)
    have hlebody : Expr.LeafEquiv body (body'.abstract1 d) := by
      simp only [Expr.LeafEquiv] at hle
      exact hle.2
    have haty' := annotate_sound m ty hty hw.1 hb.1 ρ hok.1
    -- the annotation-truthfulness goal
    simp only [AnnotOk]
    refine ⟨haty', ⟨v, rfl⟩, ?_⟩
    intro x A hA hx
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' haty' hA hx body 0 hw.2 hok.2
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d x) body' :=
      annotate_sound m _ hbody hwin hbin (updV V ρ d x) hfin
    have hfbody' : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) body' := by
      rw [← hrt]
      refine FvarsOk.instantiate1 hwty' haty' hA hx (body'.abstract1 d) 0
        (WScoped.abstract1 0 hwbody') ?_
      exact FvarsOk.congr body (body'.abstract1 d) hlebody hok.2
    constructor
    · rw [hrt]
      exact habody
    · intro v' hv'
      obtain rfl := Option.some.inj hv'
      obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, -, -⟩ :=
        inferType_sound m body' hit hwbody' hfbody' habody
      rw [ensureSort_sound m hes] at htw
      obtain rfl := Option.some.inj htw
      exact ⟨w, by rw [hrt]; exact hwi, hmemw⟩
  | .lam n ty body mb, d, e', h, hw, hb, ρ, hok => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [FvarsOk] at hok
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferType env (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSort env bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hwty' : WScoped d ty' := annotate_WScoped ty hty hw.1
    have hwin : WScoped (d + 1) (body.instantiate1 (.fvar d n ty')) :=
      hwty'.instantiate1 0 hw.2
    have hbin : (body.instantiate1 (.fvar d n ty')).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    have hrt : (body'.abstract1 d).instantiate1 (.fvar d n ty') 0 = body' :=
      abstract1_instantiate1 body' 0
        (annotate_fvarConsistent _ (by omega) hbody
          (fvarConsistent_instantiate1 body 0 hw.2.fvarsBelow))
        (annotate_looseBVars _ hbody hbin)
    have haty' := annotate_sound m ty hty hw.1 hb.1 ρ hok.1
    simp only [AnnotOk]
    refine ⟨haty', ?_⟩
    intro x A hA hx
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' haty' hA hx body 0 hw.2 hok.2
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d x) body' :=
      annotate_sound m _ hbody hwin hbin (updV V ρ d x) hfin
    rw [hrt]
    exact habody
  | .letE _ _ _ _, d, e', h, _, _, ρ, _ => by simp [annotate] at h
  | .lit _, d, e', h, _, _, ρ, _ => by simp [annotate] at h
  | .proj _ _ _, d, e', h, _, _, ρ, _ => by simp [annotate] at h
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

end Setlec
