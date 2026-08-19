import Setlec.Kernel.TypeChecker
import Setlec.Model.FvarsOkLemmas
import Setlec.Model.Subst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves

/-!
# Soundness of the type checker functions

All statements are relative to a model `m : EnvModel V env` of the current
environment and interpret with `m.val`:

* `whnf_facts`: reduction preserves the interpretation and annotation
  truthfulness (delta unfolding is justified by `m.defn_eq`; beta by the
  substitution lemma, `SetTheory.app_lam`, and the proof-point axioms —
  see DESIGN.md); `whnf_FvarsOk` transports the local-context
  assumptions by the output-leaves-subset lemma.
* `ensureSort_sound`: a successful `ensureSort env t = .ok u` means
  `⟦t⟧ = univ (eval φ u)`.
* `inferTypeCore_sound`: a successful inference means expression and type
  are interpreted and `⟦e⟧ ∈ ⟦t⟧`, under well-scopedness, bvar bounds,
  the local-context assumptions (`FvarsOk`) and annotation truthfulness
  (`AnnotOk`).
* `isDefEqCore_sound`: a positive definitional-equality verdict means the
  interpretations agree whenever both are defined.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

private theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- `whnf` preserves the local-context assumptions (a leaf-subset
argument). -/
theorem whnf_FvarsOk {cval : ConstVal V} (henv : EnvWF env)
    (fuel : Nat) {e e' : Expr} {d : Nat} {ρ : Nat → V}
    (h : whnf env fuel e = .ok e')
    (hok : FvarsOk V cval env φ d ρ e) : FvarsOk V cval env φ d ρ e' :=
  FvarsOk.of_subset (whnf_fvarLeaves henv fuel h) hok

/-- Reduction preserves the interpretation and annotation truthfulness. -/
theorem whnf_facts (m : EnvModel V env) :
    ∀ (fuel : Nat) {e e' : Expr} {d : Nat} {ρ : Nat → V},
      whnf env fuel e = .ok e' →
      WScoped d e → e.looseBVarsBounded 0 = true →
      AnnotOk V m.val env φ d ρ e →
      interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
      AnnotOk V m.val env φ d ρ e'
  | 0, e, e', d, ρ, h, _, _, _ => nomatch h
  | fuel + 1, e, e', d, ρ, h, hw, hb, ha => by
    match e, h with
    | .sort u, h => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | .fvar idx n ty, h => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | .forallE n ty body bi, h => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | .lam n ty body bi, h => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | .const n ws, h =>
      simp only [whnf] at h
      cases hf : env.find? n with
      | none => rw [hf] at h; exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | some ci =>
        rw [hf] at h
        cases ci with
        | defnInfo cv value =>
          dsimp only at h
          split at h
          next hal =>
            obtain ⟨-, -, -, -, hval⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
            obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
            have hcl : (value.instantiateLevelParams cv.levelParams ws).hasFvar = false := by
              rw [hasFvar_instantiateLevelParams]; exact hvc
            have hstored := (m.annot_ok _ (List.mem_of_find?_eq_some hf)
              (Level.substFn φ cv.levelParams ws)).2 cv value rfl
            have hinst := AnnotOk.instLevels m.val_params value 0 (rho0 V) hstored
            obtain ⟨hi, ha'⟩ := whnf_facts m fuel h
              (WScoped.of_not_hasFvar hcl)
              (by rw [looseBVarsBounded_instantiateLevelParams]; exact hvb)
              (AnnotOk.closed_invariant hcl d ρ hinst)
            refine ⟨?_, ha'⟩
            rw [hi]
            rw [interp_closed_invariant hcl]
            unfold interpClosed
            rw [interp_instLevels m.val_params]
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
          next hal => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
        | axiomInfo cv => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
        | thmInfo cv value => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | .app f a, h =>
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [AnnotOk] at ha
      obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hvA, hfib⟩ := ha
      obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
      obtain ⟨hif, haf'⟩ := whnf_facts m fuel hwf hw.1 hb.1 haf
      rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hnz, hbeta⟩ | rfl
      · -- beta: the redex's codomain sort is certainly nonzero
        have hwlam := whnf_WScoped m.wf fuel hwf hw.1
        have hblam := whnf_looseBVars m.wf fuel hwf hb.1
        simp only [WScoped] at hwlam
        simp only [looseBVarsBounded, Bool.and_eq_true] at hblam
        have hfi' : interpExpr V m.val env φ d ρ (.lam n ty body mm) = some vf := by
          rw [hif]; exact hfi
        rw [interpExpr, hc] at hfi'
        dsimp only at hfi'
        cases hty : interpExpr V m.val env φ d ρ ty with
        | none => rw [hty] at hfi'; exact nomatch hfi'
        | some Aty =>
        rw [hty] at hfi'
        simp only [Option.some.injEq] at hfi'
        have hnz' : Level.eval φ v ≠ 0 := Level.isNonZero_sound hnz φ
        by_cases hvE : vE = 0
        · -- vacuous: a genuine graph is never the proof point
          subst hvE
          exact absurd (hfi'.trans (mem_pi_zero hpi)) (lam_ne_pt hnz')
        · have hpil : SetTheory.lam (v.eval φ) Aty
              (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
                (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ
              pi vE A B := by
            rw [hfi']; exact hpi
          have hdom : va ∈ˢ Aty := lam_dom hpil hvE hnz' va hvA
          simp only [AnnotOk] at haf'
          obtain ⟨haty, -, hcond⟩ := haf'
          obtain ⟨hbodyA, hwfact⟩ := hcond va Aty hty hdom
          obtain ⟨w, Bl, hwi, hwB, hBu⟩ := hwfact v hc
          have hfb : fvarsBelow d body := hwlam.2.fvarsBelow
          have hred_w : WScoped d (body.instantiate1 a) :=
            WScoped.instantiate1_gen hw.2 0 hwlam.2
          have hred_b : (body.instantiate1 a).looseBVarsBounded 0 = true :=
            looseBVarsBounded_instantiate1_gen hb.2 hblam.2
          have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
            (n := n) (ty := ty) hfb hw.2 hb.2 hai 0
          have hred_A : AnnotOk V m.val env φ d ρ (body.instantiate1 a) :=
            AnnotOk_beta hfb hw.2 hb.2 hai haa 0 hbodyA
          obtain ⟨hi2, ha2⟩ := whnf_facts m fuel hbeta hred_w hred_b hred_A
          refine ⟨?_, ha2⟩
          have hfibres : ∀ x, x ∈ˢ Aty →
              ∃ B', ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
                (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ B' ∧
                B' ∈ˢ univ (v.eval φ) := by
            intro x hx
            obtain ⟨-, hwfact_x⟩ := hcond x Aty hty hx
            obtain ⟨w_x, B_x, hwi_x, hwB_x, hBu_x⟩ := hwfact_x v hc
            exact ⟨B_x, by rw [hwi_x]; exact hwB_x, hBu_x⟩
          obtain ⟨Bf, hBf1, hBf2⟩ := choose_fibres (V := V) hfibres
          have happi : interpExpr V m.val env φ d ρ (.app f a) =
              some (SetTheory.app vf va) := by
            rw [interpExpr, hfi, hai]
          rw [hi2, hbeta_eq, hwi, happi]
          simp only [Option.some.injEq]
          rw [← hfi', app_lam hdom hBf1 hBf2]
          simp [hwi]
      · -- stuck application
        refine ⟨?_, ?_⟩
        · simp only [interpExpr]
          rw [hif]
        · simp only [AnnotOk]
          refine ⟨haf', haa, vf, va, vE, A, B, ?_, hai, hpi, hvA, hfib⟩
          rw [hif]; exact hfi

/-- A successful `ensureSort` identifies the interpretation of the type
with a universe. -/
theorem ensureSort_sound (m : EnvModel V env) {t : Expr} {u : Level}
    (h : ensureSort env t = .ok u) {d : Nat} {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSort at h
  cases hwh : whnf env whnfFuel t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnf_facts m whnfFuel hwh hw hb ha
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure, interpExpr]

/-- A positive definitional-equality verdict means the interpretations
agree, whenever both are defined. -/
theorem isDefEqCore_sound (m : EnvModel V env) :
    ∀ (fuel : Nat) {d : Nat} {a b : Expr} {ρ : Nat → V},
    isDefEqCore env fuel d a b = .ok true →
    WScoped d a → WScoped d b →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    AnnotOk V m.val env φ d ρ a → AnnotOk V m.val env φ d ρ b →
    ∀ {va vb : V}, interpExpr V m.val env φ d ρ a = some va →
      interpExpr V m.val env φ d ρ b = some vb → va = vb := by
  intro fuel
  induction fuel with
  | zero => intro d a b ρ h; exact nomatch h
  | succ fuel ih =>
    intro d a b ρ h hwa hwb hba hbb haa hab va vb hva hvb
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
    obtain ⟨hia, haa'⟩ := whnf_facts m whnfFuel hwha hwa hba haa
    obtain ⟨hib, hab'⟩ := whnf_facts m whnfFuel hwhb hwb hbb hab
    rw [← hia] at hva
    rw [← hib] at hvb
    have hwa' := whnf_WScoped m.wf whnfFuel hwha hwa
    have hwb' := whnf_WScoped m.wf whnfFuel hwhb hwb
    have hba' := whnf_looseBVars m.wf whnfFuel hwha hba
    have hbb' := whnf_looseBVars m.wf whnfFuel hwhb hbb
    clear hwha hwhb hwa hwb haa hab hia hib hba hbb
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
    | Expr.forallE n₁ ty₁ body₁ m₁, Expr.forallE n₂ ty₂ body₂ m₂, h =>
      dsimp only at h
      simp only [WScoped] at hwa' hwb'
      simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
      simp only [AnnotOk] at haa' hab'
      obtain ⟨haty₁, ⟨v₁, hv₁⟩, hcond₁⟩ := haa'
      obtain ⟨haty₂, ⟨v₂, hv₂⟩, hcond₂⟩ := hab'
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
      rw [hv₁, hv₂] at h
      dsimp only at h
      have hlev : Level.isEquiv v₁ v₂ = some true := by
        revert h
        cases hEq : Level.isEquiv v₁ v₂ with
        | none => simp [liftFueled]
        | some x => cases x <;> simp [liftFueled, pure, Except.pure]
      simp only [interpExpr, hv₁, hv₂] at hva hvb
      cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
      | none => rw [hA1] at hva; exact nomatch hva
      | some A₁ =>
      rw [hA1] at hva
      cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
      | none => rw [hA2] at hvb; exact nomatch hvb
      | some A₂ =>
      rw [hA2] at hvb
      simp only [Option.some.injEq] at hva hvb
      subst hva; subst hvb
      have hAeq : A₁ = A₂ :=
        ih hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 haty₁ haty₂ hA1 hA2
      subst hAeq
      have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
      rw [← hveq]
      refine pi_congr fun x hx => ?_
      obtain ⟨habody₁, hwfact₁⟩ := hcond₁ x A₁ hA1 hx
      obtain ⟨habody₂, hwfact₂⟩ := hcond₂ x A₁ hA2 hx
      obtain ⟨w₁, hw₁, -⟩ := hwfact₁ v₁ hv₁
      obtain ⟨w₂, hw₂, -⟩ := hwfact₂ v₂ hv₂
      rw [hw₁, hw₂]
      simpa using ih hd2
        (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
        (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
        (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
        habody₁ habody₂ hw₁ hw₂
    | Expr.lam n₁ ty₁ body₁ m₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
      dsimp only at h
      simp only [WScoped] at hwa' hwb'
      simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
      simp only [AnnotOk] at haa' hab'
      obtain ⟨haty₁, ⟨v₁, hv₁⟩, hcond₁⟩ := haa'
      obtain ⟨haty₂, ⟨v₂, hv₂⟩, hcond₂⟩ := hab'
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
      rw [hv₁, hv₂] at h
      dsimp only at h
      have hlev : Level.isEquiv v₁ v₂ = some true := by
        revert h
        cases hEq : Level.isEquiv v₁ v₂ with
        | none => simp [liftFueled]
        | some x => cases x <;> simp [liftFueled, pure, Except.pure]
      simp only [interpExpr, hv₁, hv₂] at hva hvb
      cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
      | none => rw [hA1] at hva; exact nomatch hva
      | some A₁ =>
      rw [hA1] at hva
      cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
      | none => rw [hA2] at hvb; exact nomatch hvb
      | some A₂ =>
      rw [hA2] at hvb
      simp only [Option.some.injEq] at hva hvb
      subst hva; subst hvb
      have hAeq : A₁ = A₂ :=
        ih hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 haty₁ haty₂ hA1 hA2
      subst hAeq
      have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
      rw [← hveq]
      refine lam_congr fun x hx => ?_
      obtain ⟨habody₁, hwfact₁⟩ := hcond₁ x A₁ hA1 hx
      obtain ⟨habody₂, hwfact₂⟩ := hcond₂ x A₁ hA2 hx
      obtain ⟨w₁, B₁, hw₁, -, -⟩ := hwfact₁ v₁ hv₁
      obtain ⟨w₂, B₂, hw₂, -, -⟩ := hwfact₂ v₂ hv₂
      rw [hw₁, hw₂]
      simpa using ih hd2
        (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
        (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
        (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
        habody₁ habody₂ hw₁ hw₂
    | Expr.app f₁ a₁, Expr.app f₂ a₂, h =>
      dsimp only at h
      simp only [WScoped] at hwa' hwb'
      simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
      simp only [AnnotOk] at haa' hab'
      obtain ⟨haf₁, haa₁, -⟩ := haa'
      obtain ⟨haf₂, haa₂, -⟩ := hab'
      cases hd1 : isDefEqCore env fuel d f₁ f₂ with
      | error e => rw [hd1] at h; exact nomatch h
      | ok r₁ =>
      rw [hd1] at h
      dsimp only at h
      cases r₁ with
      | false => simp [pure, Except.pure] at h
      | true =>
      simp only [] at h
      simp only [interpExpr] at hva hvb
      cases hf1 : interpExpr V m.val env φ d ρ f₁ with
      | none => rw [hf1] at hva; exact nomatch hva
      | some vf₁ =>
      rw [hf1] at hva
      cases ha1 : interpExpr V m.val env φ d ρ a₁ with
      | none => rw [ha1] at hva; exact nomatch hva
      | some va₁ =>
      rw [ha1] at hva
      cases hf2 : interpExpr V m.val env φ d ρ f₂ with
      | none => rw [hf2] at hvb; exact nomatch hvb
      | some vf₂ =>
      rw [hf2] at hvb
      cases ha2 : interpExpr V m.val env φ d ρ a₂ with
      | none => rw [ha2] at hvb; exact nomatch hvb
      | some va₂ =>
      rw [ha2] at hvb
      simp only [Option.some.injEq] at hva hvb
      subst hva; subst hvb
      have hfe : vf₁ = vf₂ :=
        ih hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 haf₁ haf₂ hf1 hf2
      have hae : va₁ = va₂ :=
        ih h hwa'.2 hwb'.2 hba'.2 hbb'.2 haa₁ haa₂ ha1 ha2
      rw [hfe, hae]
    | Expr.sort _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.lam _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.sort _, Expr.app _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.lam _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.fvar _ _ _, Expr.app _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.lam _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.forallE _ _ _ _, Expr.app _ _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.lam _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.const _ _, Expr.app _ _, h => simp [pure, Except.pure] at h
    | Expr.lam _ _ _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.lam _ _ _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.lam _ _ _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.lam _ _ _ _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.lam _ _ _ _, Expr.app _ _, h => simp [pure, Except.pure] at h
    | Expr.app _ _, Expr.sort _, h => simp [pure, Except.pure] at h
    | Expr.app _ _, Expr.fvar _ _ _, h => simp [pure, Except.pure] at h
    | Expr.app _ _, Expr.forallE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.app _ _, Expr.const _ _, h => simp [pure, Except.pure] at h
    | Expr.app _ _, Expr.lam _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.bvar _, _, h => simp [pure, Except.pure] at h
    | _, Expr.bvar _, h => simp [pure, Except.pure] at h
    | Expr.letE _ _ _ _, _, h => simp [pure, Except.pure] at h
    | _, Expr.letE _ _ _ _, h => simp [pure, Except.pure] at h
    | Expr.lit _, _, h => simp [pure, Except.pure] at h
    | _, Expr.lit _, h => simp [pure, Except.pure] at h
    | Expr.proj _ _ _, _, h => simp [pure, Except.pure] at h
    | _, Expr.proj _ _ _, h => simp [pure, Except.pure] at h

theorem isDefEq_sound (m : EnvModel V env) {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : isDefEq env d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  isDefEqCore_sound m defEqFuel h hwa hwb hba hbb haa hab hva hvb

/-- Successful inference is sound. -/
theorem inferTypeCore_sound (m : EnvModel V env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr} {ρ : Nat → V},
      inferTypeCore env fuel d e = .ok t →
      WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      FvarsOk V m.val env φ d ρ e → AnnotOk V m.val env φ d ρ e →
      (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
        interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
      AnnotOk V m.val env φ d ρ t
  | 0, d, e, t, ρ, h, _, _, _, _, _ => nomatch h
  | fuel + 1, d, e, t, ρ, h, hw, hb, hLb, hok, ha => by
    match e, h with
    | .sort u, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨⟨univ (u.eval φ), univ (u.eval φ + 1), ?_, ?_, univ_mem_univ _⟩, ?_⟩ <;>
        simp [interpExpr, Level.eval, AnnotOk]
    | .fvar idx n ty, h =>
      simp only [inferTypeCore, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨⟨hidx, hAty, T, hT, hmem⟩, hFty⟩ := FvarsOk.of_fvar hok
      exact ⟨⟨ρ idx, T, by simp [interpExpr], hT, hmem⟩, hAty⟩
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
          obtain ⟨htc, -, -, -, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
          have hcl : (ci.toConstantVal.type.instantiateLevelParams
              ci.toConstantVal.levelParams ws).hasFvar = false := by
            rw [hasFvar_instantiateLevelParams]; exact htc
          obtain ⟨T, hT, hmem⟩ :=
            m.mem_type ci (List.mem_of_find?_eq_some hf)
              (Level.substFn φ ci.toConstantVal.levelParams ws)
          have hAstored := (m.annot_ok ci (List.mem_of_find?_eq_some hf)
            (Level.substFn φ ci.toConstantVal.levelParams ws)).1
          refine ⟨⟨m.val n (Level.substFn φ ci.toConstantVal.levelParams ws), T, ?_, ?_, ?_⟩, ?_⟩
          · simp only [interpExpr, hf]
            rw [if_pos hal]
          · rw [interp_closed_invariant hcl]
            unfold interpClosed
            rw [interp_instLevels m.val_params]
            exact hT
          · have hname : ci.name = n := find?_name hf
            simp only [ConstantInfo.name] at hname
            rw [← hname]
            exact hmem
          · exact AnnotOk.closed_invariant hcl d ρ
              (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hAstored)
        next hal => exact nomatch h
    | .forallE n ty body m', h =>
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨hokty, hokbody⟩ := FvarsOk.of_forallE hok
      simp only [AnnotOk] at ha
      obtain ⟨haty, ⟨v₀, hv₀⟩, hcond⟩ := ha
      simp only [inferTypeCore] at h
      rw [hv₀] at h
      simp only [Bind.bind, Except.bind] at h
      cases hty : inferTypeCore env fuel d ty with
      | error e => rw [hty] at h; exact nomatch h
      | ok tty =>
      rw [hty] at h
      dsimp only at h
      cases hsty : ensureSort env tty with
      | error e => rw [hsty] at h; exact nomatch h
      | ok u =>
      rw [hsty] at h
      dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
      obtain ⟨⟨A, tA, hA, htA, hmemA⟩, hAtA⟩ :=
        inferTypeCore_sound m fuel hty hw.1 hb.1 hLbty hokty haty
      rw [ensureSort_sound m hsty (inferTypeCore_WScoped m.wf fuel hty hw.1)
        (inferTypeCore_looseBVars m.wf fuel hty hw.1 hb.1 hLbty) hAtA] at htA
      obtain rfl := Option.some.inj htA
      refine ⟨⟨pi (v₀.eval φ) A (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
        univ ((Level.imax u v₀).eval φ), ?_, ?_, ?_⟩, by simp [AnnotOk]⟩
      · simp only [interpExpr, hv₀, hA]
      · simp only [interpExpr]
      · have hpi := pi_mem_univ (V := V) (v := v₀.eval φ)
          (B := fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
          hmemA
          (fun x hx => by
            obtain ⟨-, hwfact⟩ := hcond x A hA hx
            obtain ⟨w, hwi, hmem⟩ := hwfact v₀ hv₀
            simpa [hwi] using hmem)
        have heq : Level.eval φ (.imax u v₀) =
            if v₀.eval φ = 0 then 0 else Nat.max (u.eval φ) (v₀.eval φ) := rfl
        rw [heq]
        exact hpi
    | .lam n ty body m', h =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, htyi, hu, hbt, htbt, hes, heqv, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨hokty, hokbody⟩ := FvarsOk.of_lam hok
      simp only [AnnotOk] at ha
      obtain ⟨haty, -, hcond⟩ := ha
      have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
      -- the domain interprets (via its own inference)
      obtain ⟨⟨A, tA, hA, -, -⟩, -⟩ :=
        inferTypeCore_sound m fuel htyi hw.1 hb.1 hLbty hokty haty
      -- facts about the opened body
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
      -- the abstraction roundtrip
      have hwbt := inferTypeCore_WScoped m.wf fuel hbt hwo
      have hrt : (bt.abstract1 d).instantiate1 (.fvar d n ty) = bt :=
        abstract1_instantiate1 bt 0
          (Expr.fvarConsistent_of_leafCond bt (fun l hl hld =>
            Expr.LeafCond_opened hw.1 hw.2 0 l
              (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl) hld))
          (inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo)
      -- per-member facts about the body and its type
      have hfacts : ∀ x, x ∈ˢ A →
          (∃ w tw, interpExpr V m.val env φ (d + 1) (updV V ρ d x)
              (body.instantiate1 (.fvar d n ty)) = some w ∧
            interpExpr V m.val env φ (d + 1) (updV V ρ d x) bt = some tw ∧
            w ∈ˢ tw ∧ tw ∈ˢ univ (v.eval φ)) ∧
          AnnotOk V m.val env φ (d + 1) (updV V ρ d x) bt := by
        intro x hx
        obtain ⟨hbodyA⟩ := hcond x A hA hx
        have hoko : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) :=
          FvarsOk.instantiate1 hw.1 hokty haty hA hx body 0 hw.2 hokbody
        obtain ⟨⟨w, tw, hwi, hbti, hmem⟩, hAbt⟩ :=
          inferTypeCore_sound m fuel hbt hwo hbo hLbo hoko hbodyA
        -- the re-check gives the fibre's universe
        have hokbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hbt hwo) hoko
        have hbbt : bt.looseBVarsBounded 0 = true :=
          inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo
        have hLbbt : Expr.LeavesBounded bt := fun l hl =>
          hLbo l (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl)
        obtain ⟨⟨vbt, tvbt, hbti2, htbti, hmem2⟩, hAtbt⟩ :=
          inferTypeCore_sound m fuel htbt hwbt hbbt hLbbt hokbt hAbt
        rw [ensureSort_sound m hes (inferTypeCore_WScoped m.wf fuel htbt hwbt)
          (inferTypeCore_looseBVars m.wf fuel htbt hwbt hbbt hLbbt) hAtbt] at htbti
        obtain rfl := Option.some.inj htbti
        rw [hbti] at hbti2
        have hvbt : tw = vbt := Option.some.inj hbti2
        refine ⟨⟨w, tw, hwi, hbti, hmem, ?_⟩, hAbt⟩
        rw [Level.isEquiv_sound heqv φ, hvbt]
        exact hmem2
      -- assemble
      refine ⟨⟨SetTheory.lam (v.eval φ) A (fun x =>
          (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
        pi (v.eval φ) A (fun x =>
          (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            ((bt.abstract1 d).instantiate1 (.fvar d n ty))).getD SetTheory.empty),
        ?_, ?_, ?_⟩, ?_⟩
      · simp only [interpExpr, hc, hA]
      · simp only [interpExpr, hA]
      · refine lam_mem fun x hx => ?_
        obtain ⟨⟨w, tw, hwi, hbti, hmem, -⟩, -⟩ := hfacts x hx
        rw [hrt, hwi, hbti]
        simpa using hmem
      · -- annotation truthfulness of the inferred Π-type
        simp only [AnnotOk]
        refine ⟨haty, ⟨v, rfl⟩, ?_⟩
        intro x A' hA' hx
        rw [hA] at hA'
        obtain rfl := Option.some.inj hA'
        obtain ⟨⟨w, tw, hwi, hbti, hmem, htwu⟩, hAbt⟩ := hfacts x hx
        rw [hrt]
        refine ⟨hAbt, ?_⟩
        intro v'' hv''
        obtain rfl : v = v'' := by injection hv''
        exact ⟨tw, hbti, htwu⟩
    | .app f a, h =>
      obtain ⟨tf, n', ty', body', mPi, ta, htf, hwh, hta, hde, rfl⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
      simp only [AnnotOk] at ha
      obtain ⟨haf, haa, -⟩ := ha
      have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
      have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
      -- infer f, reduce its type to a Π
      obtain ⟨⟨vf, vtf, hfi, htfi, hmemf⟩, hAtf⟩ :=
        inferTypeCore_sound m fuel htf hw.1 hb.1 hLbf hokf haf
      have hwtf := inferTypeCore_WScoped m.wf fuel htf hw.1
      have hbtf := inferTypeCore_looseBVars m.wf fuel htf hw.1 hb.1 hLbf
      obtain ⟨hiw, haPi⟩ := whnf_facts m whnfFuel hwh hwtf hbtf hAtf
      have hwPi := whnf_WScoped m.wf whnfFuel hwh hwtf
      have hbPi := whnf_looseBVars m.wf whnfFuel hwh hbtf
      simp only [WScoped] at hwPi
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      -- interpret the Π
      have hPii : interpExpr V m.val env φ d ρ (.forallE n' ty' body' mPi) = some vtf := by
        rw [hiw]; exact htfi
      rw [interpExpr] at hPii
      cases hcPi : mPi.cod with
      | none => rw [hcPi] at hPii; exact nomatch hPii
      | some vPi =>
      rw [hcPi] at hPii
      dsimp only at hPii
      cases htyPi : interpExpr V m.val env φ d ρ ty' with
      | none => rw [htyPi] at hPii; exact nomatch hPii
      | some A' =>
      rw [htyPi] at hPii
      simp only [Option.some.injEq] at hPii
      -- infer a; its type is defeq to the domain
      obtain ⟨⟨va, vta, hai, htai, hmema⟩, hAta⟩ :=
        inferTypeCore_sound m fuel hta hw.2 hb.2 hLba hoka haa
      simp only [AnnotOk] at haPi
      obtain ⟨haty', -, hcond'⟩ := haPi
      have hAeq : vta = A' :=
        isDefEqCore_sound m defEqFuel hde
          (inferTypeCore_WScoped m.wf fuel hta hw.2) hwPi.1
          (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba) hbPi.1
          hAta haty' htai htyPi
      have hva : va ∈ˢ A' := hAeq ▸ hmema
      obtain ⟨hAopened, hwfact'⟩ := hcond' va A' htyPi hva
      obtain ⟨w', hwi', hmem'⟩ := hwfact' vPi hcPi
      have hfb' : fvarsBelow d body' := hwPi.2.fvarsBelow
      have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
        (n := n') (ty := ty') hfb' hw.2 hb.2 hai 0
      refine ⟨⟨SetTheory.app vf va, w', ?_, ?_, ?_⟩, ?_⟩
      · simp only [interpExpr]
        rw [hfi, hai]
      · rw [hbeta_eq]
        exact hwi'
      · have hpiM : vf ∈ˢ pi (vPi.eval φ) A'
            (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
              (body'.instantiate1 (.fvar d n' ty'))).getD SetTheory.empty) := by
          rw [hPii]; exact hmemf
        have hfib : ∀ x, x ∈ˢ A' →
            ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
              (body'.instantiate1 (.fvar d n' ty'))).getD SetTheory.empty) ∈ˢ
              univ (vPi.eval φ) := by
          intro x hx
          obtain ⟨-, hwf_x⟩ := hcond' x A' htyPi hx
          obtain ⟨w_x, hwi_x, hm_x⟩ := hwf_x vPi hcPi
          rw [hwi_x]
          simpa using hm_x
        have happ := app_mem hpiM hva hfib
        rw [hwi'] at happ
        simpa using happ
      · exact AnnotOk_beta hfb' hw.2 hb.2 hai haa 0 hAopened
    | .bvar i, h => simp [inferTypeCore] at h
    | .letE n' t' v' b', h => simp [inferTypeCore] at h
    | .lit l', h => simp [inferTypeCore] at h
    | .proj s' i' e', h => simp [inferTypeCore] at h

/-- `inferType` soundness (the fueled wrapper), bundled with syntactic
well-scopedness of the output. -/
theorem inferType_sound (m : EnvModel V env) {d : Nat} {e t : Expr} {ρ : Nat → V}
    (h : inferType env d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := inferTypeCore_sound m inferFuel h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf inferFuel h hw, this.2⟩

end Setlec
