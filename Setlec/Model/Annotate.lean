import Setlec.Model.TypeChecker

/-!
# Soundness of the annotation pass

`annotate_sound`: the annotations `annotate` computes are truthful
(`AnnotOk`) — each binder's stored codomain sort really bounds the fibres
of its interpreted body, and each application node carries the semantic
well-typedness clause (function in a `pi`, argument in its domain) that
beta-reduction soundness relies on.  This is where the one-time
type-checking of binder bodies and applications pays out; `inferType`
afterwards trusts the annotations, and this theorem is what justifies
that trust in the model.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

theorem annotate_sound (m : EnvModel V env) :
    ∀ (e : Expr) {d : Nat} {e' : Expr},
      annotate env d e = .ok e' → WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∀ (ρ : Nat → V), FvarsOk V m.val env φ d ρ e →
        AnnotOk V m.val env φ d ρ e'
  | .bvar i, d, e', h, _, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .fvar idx n ty, d, e', h, _, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .sort u, d, e', h, _, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .const n us, d, e', h, _, _, _, ρ, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | .app f a, d, e', h, hw, hb, hLb, ρ, hok => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    obtain ⟨f', a', hf, ha, rfl, tf, n1, ty1, body1, m1, ta, hit, hwh, hia, hde⟩ :=
      annotate_app_inv h
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hAf := annotate_sound m f hf hw.1 hb.1 hLbf ρ hokf
    have hAa := annotate_sound m a ha hw.2 hb.2 hLba ρ hoka
    -- syntactic facts about the annotated pieces
    have hlef := annotate_leafEquiv f hf hw.1 hb.1
    have hlea := annotate_leafEquiv a ha hw.2 hb.2
    have hwf' : WScoped d f' := annotate_WScoped f hf hw.1
    have hwa' : WScoped d a' := annotate_WScoped a ha hw.2
    have hbf' : f'.looseBVarsBounded 0 = true := annotate_looseBVars f hf hb.1
    have hba' : a'.looseBVarsBounded 0 = true := annotate_looseBVars a ha hb.2
    have hLbf' : Expr.LeavesBounded f' := fun l hl => by
      rw [fvarLeaves_of_leafEquiv f f' hlef] at hl
      exact hLbf l hl
    have hLba' : Expr.LeavesBounded a' := fun l hl => by
      rw [fvarLeaves_of_leafEquiv a a' hlea] at hl
      exact hLba l hl
    have hFf' : FvarsOk V m.val env φ d ρ f' := FvarsOk.of_leafEquiv hlef hokf
    have hFa' : FvarsOk V m.val env φ d ρ a' := FvarsOk.of_leafEquiv hlea hoka
    -- run the application rule semantically
    obtain ⟨⟨vf, vtf, hfi, htfi, hmemf⟩, hwtf, hAtf⟩ :=
      inferType_sound m hit hwf' hbf' hLbf' hFf' hAf
    have hbtf : tf.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf checkFuel hit hwf' hbf' hLbf'
    have hLbtf : Expr.LeavesBounded tf := fun l hl =>
      hLbf' l (inferTypeCore_fvarLeaves m.wf checkFuel hit hwf' l hl)
    have hoktf : FvarsOk V m.val env φ d ρ tf :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hit hwf') hFf'
    obtain ⟨hiw, haPi⟩ := whnf_facts m hwh hwtf hbtf hLbtf hoktf hAtf
    have hwPi := whnf_WScoped m.wf checkFuel hwh hwtf
    have hbPi := whnf_looseBVars m.wf checkFuel hwh hbtf
    simp only [WScoped] at hwPi
    simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
    have hPii : interpExpr V m.val env φ d ρ (.forallE n1 ty1 body1 m1) = some vtf := by
      rw [hiw]; exact htfi
    rw [interpExpr] at hPii
    cases hcPi : m1.cod with
    | none => rw [hcPi] at hPii; exact nomatch hPii
    | some vPi =>
    rw [hcPi] at hPii
    dsimp only at hPii
    cases htyPi : interpExpr V m.val env φ d ρ ty1 with
    | none => rw [htyPi] at hPii; exact nomatch hPii
    | some A' =>
    rw [htyPi] at hPii
    simp only [Option.some.injEq] at hPii
    obtain ⟨⟨va, vta, hai, htai, hmema⟩, hwta, hAta⟩ :=
      inferType_sound m hia hwa' hba' hLba' hFa' hAa
    simp only [AnnotOk] at haPi
    obtain ⟨haty1, -, hcond1⟩ := haPi
    have hLbta : Expr.LeavesBounded ta := fun l hl =>
      hLba' l (inferTypeCore_fvarLeaves m.wf checkFuel hia hwa' l hl)
    have hLbPi : Expr.LeavesBounded (Expr.forallE n1 ty1 body1 m1) := fun l hl =>
      hLbtf l (whnf_fvarLeaves m.wf checkFuel hwh l hl)
    have hokPi : FvarsOk V m.val env φ d ρ (.forallE n1 ty1 body1 m1) :=
      whnf_FvarsOk m.wf checkFuel hwh hoktf
    have hAeq : vta = A' :=
      isDefEq_sound m hde hwta hwPi.1
        (inferTypeCore_looseBVars m.wf checkFuel hia hwa' hba' hLba') hbPi.1
        hLbta (fun l hl => hLbPi l (by simp [fvarLeaves, hl]))
        (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hia hwa') hFa')
        ((FvarsOk.of_forallE hokPi).1)
        hAta haty1 htai htyPi
    have hva : va ∈ˢ A' := hAeq ▸ hmema
    have hfib : ∀ x, x ∈ˢ A' →
        ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body1.instantiate1 (.fvar d n1 ty1))).getD SetTheory.empty) ∈ˢ
          univ (vPi.eval φ) := by
      intro x hx
      obtain ⟨-, hwf_x⟩ := hcond1 x A' htyPi hx
      obtain ⟨w_x, hwi_x, hm_x⟩ := hwf_x vPi hcPi
      rw [hwi_x]
      simpa using hm_x
    simp only [AnnotOk]
    refine ⟨hAf, hAa, vf, va, vPi.eval φ, A',
      (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body1.instantiate1 (.fvar d n1 ty1))).getD SetTheory.empty),
      hfi, hai, ?_, hva, hfib⟩
    rw [hPii]
    exact hmemf
  | .forallE n ty body mb, d, e', h, hw, hb, hLb, ρ, hok => by
    have hle := annotate_leafEquiv (env := env) (.forallE n ty body mb) h hw hb
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_forallE hok
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
    cases hes : ensureSort env (d + 1) bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- shared syntactic facts
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hwty' : WScoped d ty' := annotate_WScoped ty hty hw.1
    have hbty' : ty'.looseBVarsBounded 0 = true := annotate_looseBVars ty hty hb.1
    have hwin : WScoped (d + 1) (body.instantiate1 (.fvar d n ty')) :=
      hwty'.instantiate1 0 hw.2
    have hbin : (body.instantiate1 (.fvar d n ty')).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    have hLbin : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty')) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
      · exact hLb l (by simp [fvarLeaves, hb'])
      · simp only [fvarLeaves, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact hbty'
        · rw [fvarLeaves_of_leafEquiv ty ty' (annotate_leafEquiv ty hty hw.1 hb.1)] at hb'
          exact hLbty l hb'
    have hwbody' : WScoped (d + 1) body' := annotate_WScoped _ hbody hwin
    have hbbody' : body'.looseBVarsBounded 0 = true := annotate_looseBVars _ hbody hbin
    have hLbbody' : Expr.LeavesBounded body' := fun l hl => by
      rw [fvarLeaves_of_leafEquiv _ _ (annotate_leafEquiv _ hbody hwin hbin)] at hl
      exact hLbin l hl
    have hrt : (body'.abstract1 d).instantiate1 (.fvar d n ty') 0 = body' :=
      abstract1_instantiate1 body' 0
        (annotate_fvarConsistent _ (by omega) hbody
          (fvarConsistent_instantiate1 body 0 hw.2.fvarsBelow))
        hbbody'
    have hlebody : Expr.LeafEquiv body (body'.abstract1 d) := by
      simp only [Expr.LeafEquiv] at hle
      exact hle.2
    have haty' := annotate_sound m ty hty hw.1 hb.1 hLbty ρ hokty
    have hFty' : FvarsOk V m.val env φ d ρ ty' :=
      FvarsOk.of_leafEquiv (annotate_leafEquiv ty hty hw.1 hb.1) hokty
    -- the annotation-truthfulness goal
    simp only [AnnotOk]
    refine ⟨haty', ⟨v, rfl⟩, ?_⟩
    intro x A hA hx
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' hFty' haty' hA hx body 0 hw.2 hokbody
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d x) body' :=
      annotate_sound m _ hbody hwin hbin hLbin (updV V ρ d x) hfin
    have hfbody' : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) body' := by
      rw [← hrt]
      refine FvarsOk.instantiate1 hwty' hFty' haty' hA hx (body'.abstract1 d) 0
        (WScoped.abstract1 0 hwbody') ?_
      exact FvarsOk.of_leafEquiv hlebody hokbody
    constructor
    · rw [hrt]
      exact habody
    · intro v' hv'
      obtain rfl := Option.some.inj hv'
      obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, hwbt, hAbt⟩ :=
        inferType_sound m hit hwbody' hbbody' hLbbody' hfbody' habody
      have hLbbt : Expr.LeavesBounded bt := fun l hl =>
        hLbbody' l (inferTypeCore_fvarLeaves m.wf checkFuel hit hwbody' l hl)
      have hokbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hit hwbody') hfbody'
      rw [ensureSort_sound m hes hwbt
        (inferTypeCore_looseBVars m.wf checkFuel hit hwbody' hbbody' hLbbody')
        hLbbt hokbt hAbt] at htw
      obtain rfl := Option.some.inj htw
      exact ⟨w, by rw [hrt]; exact hwi, hmemw⟩
  | .lam n ty body mb, d, e', h, hw, hb, hLb, ρ, hok => by
    have hle := annotate_leafEquiv (env := env) (.lam n ty body mb) h hw hb
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_lam hok
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
    cases hes : ensureSort env (d + 1) bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hwty' : WScoped d ty' := annotate_WScoped ty hty hw.1
    have hbty' : ty'.looseBVarsBounded 0 = true := annotate_looseBVars ty hty hb.1
    have hwin : WScoped (d + 1) (body.instantiate1 (.fvar d n ty')) :=
      hwty'.instantiate1 0 hw.2
    have hbin : (body.instantiate1 (.fvar d n ty')).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    have hLbin : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty')) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
      · exact hLb l (by simp [fvarLeaves, hb'])
      · simp only [fvarLeaves, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact hbty'
        · rw [fvarLeaves_of_leafEquiv ty ty' (annotate_leafEquiv ty hty hw.1 hb.1)] at hb'
          exact hLbty l hb'
    have hwbody' : WScoped (d + 1) body' := annotate_WScoped _ hbody hwin
    have hbbody' : body'.looseBVarsBounded 0 = true := annotate_looseBVars _ hbody hbin
    have hLbbody' : Expr.LeavesBounded body' := fun l hl => by
      rw [fvarLeaves_of_leafEquiv _ _ (annotate_leafEquiv _ hbody hwin hbin)] at hl
      exact hLbin l hl
    have hrt : (body'.abstract1 d).instantiate1 (.fvar d n ty') 0 = body' :=
      abstract1_instantiate1 body' 0
        (annotate_fvarConsistent _ (by omega) hbody
          (fvarConsistent_instantiate1 body 0 hw.2.fvarsBelow))
        hbbody'
    have hlebody : Expr.LeafEquiv body (body'.abstract1 d) := by
      simp only [Expr.LeafEquiv] at hle
      exact hle.2
    have haty' := annotate_sound m ty hty hw.1 hb.1 hLbty ρ hokty
    have hFty' : FvarsOk V m.val env φ d ρ ty' :=
      FvarsOk.of_leafEquiv (annotate_leafEquiv ty hty hw.1 hb.1) hokty
    simp only [AnnotOk]
    refine ⟨haty', ⟨v, rfl⟩, ?_⟩
    intro x A hA hx
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' hFty' haty' hA hx body 0 hw.2 hokbody
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d x) body' :=
      annotate_sound m _ hbody hwin hbin hLbin (updV V ρ d x) hfin
    have hfbody' : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) body' := by
      rw [← hrt]
      refine FvarsOk.instantiate1 hwty' hFty' haty' hA hx (body'.abstract1 d) 0
        (WScoped.abstract1 0 hwbody') ?_
      exact FvarsOk.of_leafEquiv hlebody hokbody
    refine ⟨by rw [hrt]; exact habody, ?_⟩
    intro v' hv'
    obtain rfl := Option.some.inj hv'
    obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, hwbt, hAbt⟩ :=
      inferType_sound m hit hwbody' hbbody' hLbbody' hfbody' habody
    -- the sort of the body's type, via the second inference
    have hbbt : bt.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf checkFuel hit hwbody' hbbody' hLbbody'
    have hLbbt : Expr.LeavesBounded bt := fun l hl =>
      hLbbody' l (inferTypeCore_fvarLeaves m.wf checkFuel hit hwbody' l hl)
    have hfbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hit hwbody') hfbody'
    obtain ⟨⟨vbt, tvbt, hbti, htbti, hmem2⟩, hwbt2, hAbt2⟩ :=
      inferType_sound m hit2 hwbt hbbt hLbbt hfbt hAbt
    have hLbbt2 : Expr.LeavesBounded bt2 := fun l hl =>
      hLbbt l (inferTypeCore_fvarLeaves m.wf checkFuel hit2 hwbt l hl)
    have hokbt2 : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt2 :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hit2 hwbt) hfbt
    rw [ensureSort_sound m hes hwbt2
      (inferTypeCore_looseBVars m.wf checkFuel hit2 hwbt hbbt hLbbt)
      hLbbt2 hokbt2 hAbt2] at htbti
    obtain rfl := Option.some.inj htbti
    rw [htw] at hbti
    have htweq : tw = vbt := Option.some.inj hbti
    refine ⟨w, tw, by rw [hrt]; exact hwi, hmemw, ?_⟩
    rw [htweq]
    exact hmem2
  | .letE _ _ _ _, d, e', h, _, _, _, ρ, _ => by simp [annotate] at h
  | .lit _, d, e', h, _, _, _, ρ, _ => by simp [annotate] at h
  | .proj _ _ _, d, e', h, _, _, _, ρ, _ => by simp [annotate] at h
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

end Setlec
