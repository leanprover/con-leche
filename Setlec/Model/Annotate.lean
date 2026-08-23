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

theorem annotateCore_sound (m : EnvModel V env) :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore env fuel d e = .ok e' → WScoped d e →
      e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∀ (ρ : Nat → V), FvarsOk V m.val env φ d ρ e →
        AnnotOk V m.val env φ d ρ e'
  | 0, _, _, _, h, _, _, _, _, _ => by
    rw [annotateCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, _, _, _, ρ, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | fuel + 1, .fvar idx n ty, d, e', h, _, _, _, ρ, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody] at h
    revert h
    split
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [AnnotOk]
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .sort u, d, e', h, _, _, _, ρ, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | fuel + 1, .const n us, d, e', h, _, _, _, ρ, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [AnnotOk]
  | fuel + 1, .app f a, d, e', h, hw, hb, hLb, ρ, hok => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    obtain ⟨f', a', hf, ha, rfl, tf, n1, ty1, body1, m1, ta, hit, hwh, hia, hde⟩ :=
      annotateCore_app_inv h
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hAf := annotateCore_sound m fuel f hf hw.1 hb.1 hLbf ρ hokf
    have hAa := annotateCore_sound m fuel a ha hw.2 hb.2 hLba ρ hoka
    -- syntactic facts about the annotated pieces
    have hslf := annotateCore_leaves_sub fuel f hf hw.1 hb.1
    have hsla := annotateCore_leaves_sub fuel a ha hw.2 hb.2
    have hwf' : WScoped d f' := annotateCore_WScoped fuel f hf hw.1
    have hwa' : WScoped d a' := annotateCore_WScoped fuel a ha hw.2
    have hbf' : f'.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel f hf hb.1
    have hba' : a'.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel a ha hb.2
    have hLbf' : Expr.LeavesBounded f' := fun l hl => hLbf l (hslf l hl)
    have hLba' : Expr.LeavesBounded a' := fun l hl => hLba l (hsla l hl)
    have hFf' : FvarsOk V m.val env φ d ρ f' := fun l hl => hokf l (hslf l hl)
    have hFa' : FvarsOk V m.val env φ d ρ a' := fun l hl => hoka l (hsla l hl)
    -- run the application rule semantically
    obtain ⟨⟨vf, vtf, hfi, htfi, hmemf⟩, hwtf, hAtf⟩ :=
      inferTypeCore_sound m fuel hit hwf' hbf' hLbf' hFf' hAf
    have hbtf : tf.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fuel hit hwf' hbf' hLbf'
    have hLbtf : Expr.LeavesBounded tf := fun l hl =>
      hLbf' l (inferTypeCore_fvarLeaves m.wf fuel hit hwf' l hl)
    have hoktf : FvarsOk V m.val env φ d ρ tf :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hit hwf') hFf'
    obtain ⟨hiw, haPi⟩ := whnf_facts m fuel hwh hwtf hbtf hLbtf hoktf hAtf
    have hwPi := whnf_WScoped m.wf fuel hwh hwtf
    have hbPi := whnf_looseBVars m.wf fuel hwh hbtf
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
      inferTypeCore_sound m fuel hia hwa' hba' hLba' hFa' hAa
    simp only [AnnotOk] at haPi
    obtain ⟨haty1, -, hcond1⟩ := haPi
    have hLbta : Expr.LeavesBounded ta := fun l hl =>
      hLba' l (inferTypeCore_fvarLeaves m.wf fuel hia hwa' l hl)
    have hLbPi : Expr.LeavesBounded (Expr.forallE n1 ty1 body1 m1) := fun l hl =>
      hLbtf l (whnf_fvarLeaves m.wf fuel hwh l hl)
    have hokPi : FvarsOk V m.val env φ d ρ (.forallE n1 ty1 body1 m1) :=
      whnf_FvarsOk m.wf fuel hwh hoktf
    have hAeq : vta = A' :=
      isDefEqCore_sound m fuel hde hwta hwPi.1
        (inferTypeCore_looseBVars m.wf fuel hia hwa' hba' hLba') hbPi.1
        hLbta (fun l hl => hLbPi l (by simp [fvarLeaves, hl]))
        (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hia hwa') hFa')
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
  | fuel + 1, .forallE n ty body mb, d, e', h, hw, hb, hLb, ρ, hok => by
    have hsle := annotateCore_leaves_sub (fuel + 1) (env := env)
      (.forallE n ty body mb) h hw hb
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_forallE hok
    rw [annotateCore_succ] at h
    simp only [annotateBody, Bind.bind, Except.bind] at h
    simp only [annotate_def, infer_def, ensureSort_def] at h
    cases hty : annotateCore env fuel d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotateCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferTypeCore env fuel (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSortCore env fuel (d + 1) bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- shared syntactic facts
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty hw.1
    have hbty' : ty'.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel ty hty hb.1
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
        · exact hLbty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1 l hb')
    have hwbody' : WScoped (d + 1) body' := annotateCore_WScoped fuel _ hbody hwin
    have hbbody' : body'.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel _ hbody hbin
    have hLbbody' : Expr.LeavesBounded body' := fun l hl =>
      hLbin l (annotateCore_leaves_sub fuel _ hbody hwin hbin l hl)
    have hrt : (body'.abstract1 d).instantiate1 (.fvar d n ty') 0 = body' :=
      abstract1_instantiate1 body' 0
        (Expr.fvarConsistent_of_leafCond body'
          (fun l hl hld => Expr.LeafCond_opened hwty' hw.2 0 l
            (annotateCore_leaves_sub fuel _ hbody hwin hbin l hl) hld))
        hbbody'
    have hsabs : ∀ l ∈ (body'.abstract1 d).fvarLeaves,
        l ∈ ty.fvarLeaves ∨ l ∈ body.fvarLeaves := fun l hl => by
      have := hsle l (by
        simp only [fvarLeaves, List.mem_append]; exact Or.inr hl)
      simpa [fvarLeaves, List.mem_append] using this
    have haty' := annotateCore_sound m fuel ty hty hw.1 hb.1 hLbty ρ hokty
    have hFty' : FvarsOk V m.val env φ d ρ ty' := fun l hl =>
      hokty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1 l hl)
    -- the annotation-truthfulness goal
    simp only [AnnotOk]
    refine ⟨haty', ⟨v, rfl⟩, ?_⟩
    intro x A hA hx
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' hFty' haty' hA hx body 0 hw.2 hokbody
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d x) body' :=
      annotateCore_sound m fuel _ hbody hwin hbin hLbin (updV V ρ d x) hfin
    have hfbody' : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) body' := by
      rw [← hrt]
      refine FvarsOk.instantiate1 hwty' hFty' haty' hA hx (body'.abstract1 d) 0
        (WScoped.abstract1 0 hwbody') ?_
      intro l hl
      rcases hsabs l hl with h2 | h2
      · exact hokty l h2
      · exact hokbody l h2
    constructor
    · rw [hrt]
      exact habody
    · intro v' hv'
      obtain rfl := Option.some.inj hv'
      obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, hwbt, hAbt⟩ :=
        inferTypeCore_sound m fuel hit hwbody' hbbody' hLbbody' hfbody' habody
      have hLbbt : Expr.LeavesBounded bt := fun l hl =>
        hLbbody' l (inferTypeCore_fvarLeaves m.wf fuel hit hwbody' l hl)
      have hokbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hit hwbody') hfbody'
      rw [ensureSortCore_sound m fuel hes hwbt
        (inferTypeCore_looseBVars m.wf fuel hit hwbody' hbbody' hLbbody')
        hLbbt hokbt hAbt] at htw
      obtain rfl := Option.some.inj htw
      exact ⟨w, by rw [hrt]; exact hwi, hmemw⟩
  | fuel + 1, .lam n ty body mb, d, e', h, hw, hb, hLb, ρ, hok => by
    have hsle := annotateCore_leaves_sub (fuel + 1) (env := env)
      (.lam n ty body mb) h hw hb
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_lam hok
    rw [annotateCore_succ] at h
    simp only [annotateBody, Bind.bind, Except.bind] at h
    simp only [annotate_def, infer_def, ensureSort_def] at h
    cases hty : annotateCore env fuel d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotateCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferTypeCore env fuel (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferTypeCore env fuel (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSortCore env fuel (d + 1) bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty hw.1
    have hbty' : ty'.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel ty hty hb.1
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
        · exact hLbty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1 l hb')
    have hwbody' : WScoped (d + 1) body' := annotateCore_WScoped fuel _ hbody hwin
    have hbbody' : body'.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel _ hbody hbin
    have hLbbody' : Expr.LeavesBounded body' := fun l hl =>
      hLbin l (annotateCore_leaves_sub fuel _ hbody hwin hbin l hl)
    have hrt : (body'.abstract1 d).instantiate1 (.fvar d n ty') 0 = body' :=
      abstract1_instantiate1 body' 0
        (Expr.fvarConsistent_of_leafCond body'
          (fun l hl hld => Expr.LeafCond_opened hwty' hw.2 0 l
            (annotateCore_leaves_sub fuel _ hbody hwin hbin l hl) hld))
        hbbody'
    have hsabs : ∀ l ∈ (body'.abstract1 d).fvarLeaves,
        l ∈ ty.fvarLeaves ∨ l ∈ body.fvarLeaves := fun l hl => by
      have := hsle l (by
        simp only [fvarLeaves, List.mem_append]; exact Or.inr hl)
      simpa [fvarLeaves, List.mem_append] using this
    have haty' := annotateCore_sound m fuel ty hty hw.1 hb.1 hLbty ρ hokty
    have hFty' : FvarsOk V m.val env φ d ρ ty' := fun l hl =>
      hokty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1 l hl)
    simp only [AnnotOk]
    refine ⟨haty', ⟨v, rfl⟩, ?_⟩
    intro x A hA hx
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' hFty' haty' hA hx body 0 hw.2 hokbody
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d x) body' :=
      annotateCore_sound m fuel _ hbody hwin hbin hLbin (updV V ρ d x) hfin
    have hfbody' : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) body' := by
      rw [← hrt]
      refine FvarsOk.instantiate1 hwty' hFty' haty' hA hx (body'.abstract1 d) 0
        (WScoped.abstract1 0 hwbody') ?_
      intro l hl
      rcases hsabs l hl with h2 | h2
      · exact hokty l h2
      · exact hokbody l h2
    refine ⟨by rw [hrt]; exact habody, ?_⟩
    intro v' hv'
    obtain rfl := Option.some.inj hv'
    obtain ⟨⟨w, tw, hwi, htw, hmemw⟩, hwbt, hAbt⟩ :=
      inferTypeCore_sound m fuel hit hwbody' hbbody' hLbbody' hfbody' habody
    -- the sort of the body's type, via the second inference
    have hbbt : bt.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fuel hit hwbody' hbbody' hLbbody'
    have hLbbt : Expr.LeavesBounded bt := fun l hl =>
      hLbbody' l (inferTypeCore_fvarLeaves m.wf fuel hit hwbody' l hl)
    have hfbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hit hwbody') hfbody'
    obtain ⟨⟨vbt, tvbt, hbti, htbti, hmem2⟩, hwbt2, hAbt2⟩ :=
      inferTypeCore_sound m fuel hit2 hwbt hbbt hLbbt hfbt hAbt
    have hLbbt2 : Expr.LeavesBounded bt2 := fun l hl =>
      hLbbt l (inferTypeCore_fvarLeaves m.wf fuel hit2 hwbt l hl)
    have hokbt2 : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt2 :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hit2 hwbt) hfbt
    rw [ensureSortCore_sound m fuel hes hwbt2
      (inferTypeCore_looseBVars m.wf fuel hit2 hwbt hbbt hLbbt)
      hLbbt2 hokbt2 hAbt2] at htbti
    obtain rfl := Option.some.inj htbti
    rw [htw] at hbti
    have htweq : tw = vbt := Option.some.inj hbti
    refine ⟨w, tw, by rw [hrt]; exact hwi, hmemw, ?_⟩
    rw [htweq]
    exact hmem2
  | fuel + 1, .proj sn i e, d, e', h, hw, hb, hLb, ρ, hok => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded] at hb
    have hLbe : Expr.LeavesBounded e := fun l hl => hLb l (by
      simp only [fvarLeaves]; exact hl)
    have hoke : FvarsOk V m.val env φ d ρ e := fun l hl => hok l (by
      simp only [fvarLeaves]; exact hl)
    obtain ⟨e₂, tt, te', he, hte, hwh0, hres⟩ := annotateCore_proj_inv h
    -- the annotated struct's facts
    have hsl := annotateCore_leaves_sub fuel e he hw hb
    have hwe₂ : WScoped d e₂ := annotateCore_WScoped fuel e he hw
    have hbe₂ : e₂.looseBVarsBounded 0 = true := annotateCore_looseBVars fuel e he hb
    have hLbe₂ : Expr.LeavesBounded e₂ := fun l hl => hLbe l (hsl l hl)
    have hoke₂ : FvarsOk V m.val env φ d ρ e₂ := fun l hl => hoke l (hsl l hl)
    have hAe₂ : AnnotOk V m.val env φ d ρ e₂ :=
      annotateCore_sound m fuel e he hw hb hLbe ρ hoke
    rcases hres with ⟨T, us, entry, hfn, hf, hnat, hlen, rfl⟩ | hel
    case inr =>
      obtain ⟨raw, hwsb, hrb, hall, hann⟩ := annotateProjElim_inv hel
      have hsubR : ∀ l ∈ raw.fvarLeaves, l ∈ e₂.fvarLeaves := fun l hl => by
        have := List.all_eq_true.mp hall l hl
        simpa using this
      have hLbraw : Expr.LeavesBounded raw :=
        fun l hl => hLbe l (hsl l (hsubR l hl))
      have hokraw : FvarsOk V m.val env φ d ρ raw :=
        fun l hl => hoke l (hsl l (hsubR l hl))
      exact annotateCore_sound m fuel _ hann (WScoped.of_wscopedB hwsb)
        hrb hLbraw ρ hokraw
    -- identify the pinned pair through `ProjOk`
    obtain ⟨hpin, hpsig, hpsigMk⟩ :=
      m.proj_ok _ _ (Env.findProj?_some hf) hnat
    have hidx : entry.idx = i ∧ entry.structName = T := by
      have h1 := List.find?_some (Env.findProj?_some hf)
      have h2 : (ConstantInfo.projInfo entry).name = projFnName T i :=
        eq_of_beq (by simpa using h1)
      simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
      exact ⟨(projFnName_inj h2).2, (projFnName_inj h2).1⟩
    have hT : T = psigmaName := by
      rw [← hidx.2]
      rcases hpin with rfl | rfl <;> rfl
    subst hT
    have hi2 : i < 2 := by
      rw [← hidx.1]
      rcases hpin with rfl | rfl <;> decide
    have hlen2 : te'.getAppArgs.length = 2 := by
      rw [hlen]
      rcases hpin with rfl | rfl <;> rfl
    obtain ⟨A, B, hargs2⟩ := List.length_two hlen2
    have hteq : te' = .app (.app (.const psigmaName us) A) B := by
      have h0 := Expr.mkAppN_getApp te'
      rw [hfn, hargs2] at h0
      exact h0.symm
    obtain ⟨cv, caps, hfind⟩ : ∃ cv caps, env.find? psigmaName =
        some (.indInfo cv caps) := ⟨_, _, by rw [hpsig]; rfl⟩
    rw [hteq] at hwh0
    obtain ⟨⟨ve, vte, hei, htei, hmem⟩, hwte, hAte⟩ :=
      inferTypeCore_sound m fuel hte hwe₂ hbe₂ hLbe₂ hoke₂ hAe₂
    -- reduce the type to the pair form
    have hbte : tt.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fuel hte hwe₂ hbe₂ hLbe₂
    have hLbte : Expr.LeavesBounded tt := fun l hl =>
      hLbe₂ l (inferTypeCore_fvarLeaves m.wf fuel hte hwe₂ l hl)
    have hokte : FvarsOk V m.val env φ d ρ tt :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hte hwe₂) hoke₂
    obtain ⟨hiw, haPi⟩ := whnf_facts m fuel hwh0 hwte hbte hLbte hokte hAte
    have hPii : interpExpr V m.val env φ d ρ
        (.app (.app (.const psigmaName us) A) B) = some vte := by
      rw [hiw]; exact htei
    try simp only [AnnotOk] at haPi
    obtain ⟨haCA, haB, vf₁, vB, vE₁, A₁, B₁, hf₁i, hBi, hpi₁, hvB₁, hfib₁⟩ := haPi
    try simp only [AnnotOk] at haCA
    obtain ⟨hac, haA, vf₀, vA, vE₀, A₀, B₀, hci, hAi, hpi₀, hvA₀, hfib₀⟩ := haCA
    rw [interpExpr, hfind] at hci
    dsimp only [ConstantInfo.toConstantVal] at hci
    obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = Level.substFn φ cv.levelParams us := ⟨_, rfl⟩
    rw [← hψ'] at hci
    by_cases hal : us.length = cv.levelParams.length
    case neg => simp only [hal, if_false] at hci; exact nomatch hci
    simp only [hal, if_true] at hci
    have hval : interpExpr V m.val env φ d ρ (.const psigmaName us) =
        some (m.val psigmaName ψ') := by
      rw [interpExpr, hfind]
      dsimp only [ConstantInfo.toConstantVal]
      rw [← hψ']
      simp only [hal, if_true]
    have hvf₀ : vf₀ = m.val psigmaName ψ' := (Option.some.inj hci).symm
    have hfacts := ((m.ind_ok.1 cv caps hfind).2 ψ')
    have hAmem : vA ∈ˢ univ (ψ' uN) := hfacts.dom₀ (hvf₀ ▸ hpi₀) hvA₀
    have hf₁ : vf₁ = app (m.val psigmaName ψ') vA := by
      rw [interpExpr, hval, hAi] at hf₁i
      dsimp only at hf₁i
      exact (Option.some.inj hf₁i).symm
    have hBmem : vB ∈ˢ pi (ψ' vN + 1) vA (fun _ => univ (ψ' vN)) :=
      hfacts.dom₁ hAmem (hf₁ ▸ hpi₁) hvB₁
    have hfold : vte = sigmaSet (Nat.max (ψ' uN) (ψ' vN)) vA (fun x => app vB x) := by
      rw [interpExpr, hf₁i, hBi] at hPii
      dsimp only at hPii
      have := Option.some.inj hPii
      rw [← this, hf₁, hfacts.fold hAmem hBmem]
    -- the proj clause
    simp only [AnnotOk]
    refine ⟨hAe₂, hi2, ve, ψ' uN, ψ' vN, vA, (fun x => app vB x), hei, ?_, hAmem, ?_⟩
    · rw [← hfold]
      exact hmem
    · intro x hx
      exact app_mem hBmem hx fun _ _ => univ_mem_univ _
  | fuel + 1, .letE n ty v b, d, e', h, hw, hb, hLb, ρ, hok => by
    have hsle := annotateCore_leaves_sub (fuel + 1) (env := env)
      (.letE n ty v b) h hw hb
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hokty : FvarsOk V m.val env φ d ρ ty := fun l hl => hok l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inl hl))
    have hokv : FvarsOk V m.val env φ d ρ v := fun l hl => hok l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inr hl))
    have hokbody : FvarsOk V m.val env φ d ρ b := fun l hl => hok l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inr hl)
    obtain ⟨ty', v', b', hty, hv, hbody, rfl, tty, u, tv, hitty, hes, hiv, hde⟩ :=
      annotateCore_letE_inv h
    -- syntactic facts about the annotated pieces
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inl hl))
    have hLbv : Expr.LeavesBounded v := fun l hl => hLb l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inr hl))
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty hw.1
    have hbty' : ty'.looseBVarsBounded 0 = true :=
      annotateCore_looseBVars fuel ty hty hb.1.1
    have hLbty' : Expr.LeavesBounded ty' := fun l hl =>
      hLbty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1.1 l hl)
    have hwv' : WScoped d v' := annotateCore_WScoped fuel v hv hw.2.1
    have hbv' : v'.looseBVarsBounded 0 = true :=
      annotateCore_looseBVars fuel v hv hb.1.2
    have hLbv' : Expr.LeavesBounded v' := fun l hl =>
      hLbv l (annotateCore_leaves_sub fuel v hv hw.2.1 hb.1.2 l hl)
    have hwin : WScoped (d + 1) (b.instantiate1 (.fvar d n ty')) :=
      hwty'.instantiate1 0 hw.2.2
    have hbin : (b.instantiate1 (.fvar d n ty')).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 b 0 hb.2
    have hLbin : Expr.LeavesBounded (b.instantiate1 (.fvar d n ty')) := by
      intro l hl
      rcases fvarLeaves_instantiate1 b 0 hl with hb' | hb'
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]; exact Or.inr hb')
      · simp only [fvarLeaves, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact hbty'
        · exact hLbty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1.1 l hb')
    have hwbody' : WScoped (d + 1) b' := annotateCore_WScoped fuel _ hbody hwin
    have hbbody' : b'.looseBVarsBounded 0 = true :=
      annotateCore_looseBVars fuel _ hbody hbin
    have hrt : (b'.abstract1 d).instantiate1 (.fvar d n ty') 0 = b' :=
      abstract1_instantiate1 b' 0
        (Expr.fvarConsistent_of_leafCond b'
          (fun l hl hld => Expr.LeafCond_opened hwty' hw.2.2 0 l
            (annotateCore_leaves_sub fuel _ hbody hwin hbin l hl) hld))
        hbbody'
    -- semantic facts
    have haty' := annotateCore_sound m fuel ty hty hw.1 hb.1.1 hLbty ρ hokty
    have hav' := annotateCore_sound m fuel v hv hw.2.1 hb.1.2 hLbv ρ hokv
    have hFty' : FvarsOk V m.val env φ d ρ ty' := fun l hl =>
      hokty l (annotateCore_leaves_sub fuel ty hty hw.1 hb.1.1 l hl)
    have hFv' : FvarsOk V m.val env φ d ρ v' := fun l hl =>
      hokv l (annotateCore_leaves_sub fuel v hv hw.2.1 hb.1.2 l hl)
    obtain ⟨⟨vty, vtty, htyi, -, -⟩, -, -⟩ :=
      inferTypeCore_sound m fuel hitty hwty' hbty' hLbty' hFty' haty'
    obtain ⟨⟨xv, vtv, hvi, htvi, hmemv⟩, hwtv, hAtv⟩ :=
      inferTypeCore_sound m fuel hiv hwv' hbv' hLbv' hFv' hav'
    have hLbtv : Expr.LeavesBounded tv := fun l hl =>
      hLbv' l (inferTypeCore_fvarLeaves m.wf fuel hiv hwv' l hl)
    have hoktv : FvarsOk V m.val env φ d ρ tv :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hiv hwv') hFv'
    have heq : vtv = vty :=
      isDefEqCore_sound m fuel hde hwtv hwty'
        (inferTypeCore_looseBVars m.wf fuel hiv hwv' hbv' hLbv') hbty'
        hLbtv hLbty' hoktv hFty' hAtv haty' htvi htyi
    have hxmem : xv ∈ˢ vty := heq ▸ hmemv
    have hfin : FvarsOk V m.val env φ (d + 1) (updV V ρ d xv)
        (b.instantiate1 (.fvar d n ty')) :=
      FvarsOk.instantiate1 hwty' hFty' haty' htyi hxmem b 0 hw.2.2 hokbody
    have habody : AnnotOk V m.val env φ (d + 1) (updV V ρ d xv) b' :=
      annotateCore_sound m fuel _ hbody hwin hbin hLbin (updV V ρ d xv) hfin
    simp only [AnnotOk]
    refine ⟨haty', hav', xv, hvi, ?_⟩
    rw [hrt]
    exact habody
  | fuel + 1, .lit l0, d, e', h, _, _, _, ρ, _ => by
    rw [annotateCore_succ] at h
    match l0, h with
    | .natVal n, h => ?_
    | .strVal sv, h => ?strCase
    case strCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [AnnotOk]
    dsimp only [annotateBody] at h
    revert h
    split
    case isFalse =>
      intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    case isTrue =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [AnnotOk]



/-- `annotate` (at any fuel) computes truthful annotations. -/
theorem annotate_sound (m : EnvModel V env) {F : Nat} :
    ∀ (e : Expr) {d : Nat} {e' : Expr},
      annotateCore env F d e = .ok e' → WScoped d e →
      e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∀ (ρ : Nat → V), FvarsOk V m.val env φ d ρ e →
        AnnotOk V m.val env φ d ρ e' := by
  intro e d e' h hw hb hLb ρ hok
  exact annotateCore_sound m F e h hw hb hLb ρ hok

end Setlec
