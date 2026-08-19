import Setlec.Kernel.TypeChecker
import Setlec.Model.FvarsOkLemmas
import Setlec.Model.Subst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves

/-!
# Soundness of the type checker functions

All statements are relative to a model `m : EnvModel V env` of the current
environment and interpret with `m.val`.  Reduction, definitional equality
and inference are mutually recursive on a shared fuel (the beta rule
certifies possibly-Prop redexes by inference + defeq), so their soundness
is one mutual fuel induction, `check_sound`:

* whnf claims: reduction preserves the interpretation and annotation
  truthfulness (delta via `m.defn_eq`; beta via the substitution lemma,
  `SetTheory.app_lam`, and — for the guarded path — the proof-point
  axioms; the certified path gets `⟦a⟧ ∈ ⟦ty⟧` from the runtime check).
* defeq claims: a positive verdict means the interpretations agree
  whenever both are defined.
* infer claims: a successful inference means expression and type are
  interpreted and `⟦e⟧ ∈ ⟦t⟧`, and the inferred type carries truthful
  annotations.

The `*_sound` wrappers at the end instantiate the fuel.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

private theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- `whnfCore` preserves the local-context assumptions (a leaf-subset
argument). -/
theorem whnf_FvarsOk {cval : ConstVal V} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr} {ρ : Nat → V}
    (h : whnfCore env fuel d e = .ok e')
    (hok : FvarsOk V cval env φ d ρ e) : FvarsOk V cval env φ d ρ e' :=
  FvarsOk.of_subset (whnf_fvarLeaves henv fuel h) hok

/-- The whnf part of the mutual soundness claims. -/
def WhnfClaims (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {ρ : Nat → V},
    whnfCore env fuel d e = .ok e' →
    WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
    FvarsOk V m.val env φ d ρ e → AnnotOk V m.val env φ d ρ e →
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e'

/-- The defeq part of the mutual soundness claims. -/
def DefEqClaims (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {ρ : Nat → V},
    isDefEqCore env fuel d a b = .ok true →
    WScoped d a → WScoped d b →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a → Expr.LeavesBounded b →
    FvarsOk V m.val env φ d ρ a → FvarsOk V m.val env φ d ρ b →
    AnnotOk V m.val env φ d ρ a → AnnotOk V m.val env φ d ρ b →
    ∀ {va vb : V}, interpExpr V m.val env φ d ρ a = some va →
      interpExpr V m.val env φ d ρ b = some vb → va = vb

/-- The inference part of the mutual soundness claims. -/
def InferClaims (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {ρ : Nat → V},
    inferTypeCore env fuel d e = .ok t →
    WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
    FvarsOk V m.val env φ d ρ e → AnnotOk V m.val env φ d ρ e →
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    AnnotOk V m.val env φ d ρ t

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- A whnf result of `.sort u` identifies the interpretation with a
universe (the inlined-`ensureSort` pattern of the inference rules). -/
private theorem sort_result (hwc : WhnfClaims m φ fuel) {d : Nat} {t : Expr} {u : Level}
    {ρ : Nat → V}
    (h : whnfCore env fuel d t = .ok (.sort u))
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  obtain ⟨hi, -⟩ := hwc h hw hb hLb hok ha
  rw [← hi]
  simp [interpExpr]

private theorem whnf_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel) :
    WhnfClaims m φ (fuel + 1) := by
  intro d e e' ρ h hw hb hLb hok ha
  match e, h with
  | .sort u, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .fvar idx n ty, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .forallE n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .lam n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .const n ws, h =>
    simp only [whnfCore] at h
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
          obtain ⟨hi, ha'⟩ := ihw h
            (WScoped.of_not_hasFvar hcl)
            (by rw [looseBVarsBounded_instantiateLevelParams]; exact hvb)
            (Expr.LeavesBounded.of_not_hasFvar hcl)
            (FvarsOk.of_not_hasFvar hcl)
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
      | indInfo cv => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | ctorInfo cv nP nF => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | recInfo cv nP nM nm ni rules => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
  | .app f a, h =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    simp only [AnnotOk] at ha
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hvA, hfib⟩ := ha
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨hif, haf'⟩ := ihw hwf hw.1 hb.1 hLbf hokf haf
    rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, hcert⟩ | rfl
    · -- beta (guarded or certified)
      have hwlam := whnf_WScoped m.wf fuel hwf hw.1
      have hblam := whnf_looseBVars m.wf fuel hwf hb.1
      have hLblam : Expr.LeavesBounded (Expr.lam n ty body mm) := fun l hl =>
        hLbf l (whnf_fvarLeaves m.wf fuel hwf l hl)
      have hoklam : FvarsOk V m.val env φ d ρ (.lam n ty body mm) :=
        whnf_FvarsOk m.wf fuel hwf hokf
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
      simp only [AnnotOk] at haf'
      obtain ⟨haty, -, hcond⟩ := haf'
      -- the argument is in the λ's domain
      have hdom : va ∈ˢ Aty := by
        rcases hcert with hnz | ⟨ta, hta, hde⟩
        · -- guarded: certainly non-Prop, so the graph determines its domain
          have hnz' : Level.eval φ v ≠ 0 := Level.isNonZero_sound hnz φ
          by_cases hvE : vE = 0
          · subst hvE
            exact absurd (hfi'.trans (mem_pi_zero hpi)) (lam_ne_pt hnz')
          · have hpil : SetTheory.lam (v.eval φ) Aty
                (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
                  (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ
                pi vE A B := by
              rw [hfi']; exact hpi
            exact lam_dom hpil hvE hnz' va hvA
        · -- certified: the runtime check hands the fact directly
          obtain ⟨⟨va₂, vta, hai₂, htai, hmema⟩, hAta⟩ :=
            ihi hta hw.2 hb.2 hLba hoka haa
          have hva₂ : va₂ = va := by
            rw [hai] at hai₂
            exact (Option.some.inj hai₂).symm
          subst hva₂
          have hLbta : Expr.LeavesBounded ta := fun l hl =>
            hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hw.2 l hl)
          have hLbty : Expr.LeavesBounded ty := fun l hl =>
            hLblam l (by simp [fvarLeaves, hl])
          have heqA : vta = Aty :=
            ihd hde
              (inferTypeCore_WScoped m.wf fuel hta hw.2) hwlam.1
              (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba) hblam.1
              hLbta hLbty
              (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hw.2) hoka)
              ((FvarsOk.of_lam hoklam).1)
              hAta haty htai hty
          exact heqA ▸ hmema
      obtain ⟨hbodyA, hwfact⟩ := hcond va Aty hty hdom
      obtain ⟨w, Bl, hwi, hwB, hBu⟩ := hwfact v hc
      have hfb : fvarsBelow d body := hwlam.2.fvarsBelow
      have hred_w : WScoped d (body.instantiate1 a) :=
        WScoped.instantiate1_gen hw.2 0 hwlam.2
      have hred_b : (body.instantiate1 a).looseBVarsBounded 0 = true :=
        looseBVarsBounded_instantiate1_gen hb.2 hblam.2
      have hred_Lb : Expr.LeavesBounded (body.instantiate1 a) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hLblam l (by simp [fvarLeaves, hl'])
        · exact hLba l hl'
      have hred_ok : FvarsOk V m.val env φ d ρ (body.instantiate1 a) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact (FvarsOk.of_lam hoklam).2 l hl'
        · exact hoka l hl'
      have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
        (n := n) (ty := ty) hfb hw.2 hb.2 hai 0
      have hred_A : AnnotOk V m.val env φ d ρ (body.instantiate1 a) :=
        AnnotOk_beta hfb hw.2 hb.2 hai haa 0 hbodyA
      obtain ⟨hi2, ha2⟩ := ihw hbeta hred_w hred_b hred_Lb hred_ok hred_A
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

private theorem defeq_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel) :
    DefEqClaims m φ (fuel + 1) := by
  intro d a b ρ h hwa hwb hba hbb hLba hLbb hoka hokb haa hab va vb hva hvb
  unfold isDefEqCore at h
  simp only [Bind.bind, Except.bind] at h
  cases hwha : whnfCore env fuel d a with
  | error e => rw [hwha] at h; exact nomatch h
  | ok a' =>
  rw [hwha] at h
  dsimp only at h
  cases hwhb : whnfCore env fuel d b with
  | error e => rw [hwhb] at h; exact nomatch h
  | ok b' =>
  rw [hwhb] at h
  dsimp only at h
  -- transfer facts through reduction
  obtain ⟨hia, haa'⟩ := ihw hwha hwa hba hLba hoka haa
  obtain ⟨hib, hab'⟩ := ihw hwhb hwb hbb hLbb hokb hab
  rw [← hia] at hva
  rw [← hib] at hvb
  have hwa' := whnf_WScoped m.wf fuel hwha hwa
  have hwb' := whnf_WScoped m.wf fuel hwhb hwb
  have hba' := whnf_looseBVars m.wf fuel hwha hba
  have hbb' := whnf_looseBVars m.wf fuel hwhb hbb
  have hLba' : Expr.LeavesBounded a' := fun l hl =>
    hLba l (whnf_fvarLeaves m.wf fuel hwha l hl)
  have hLbb' : Expr.LeavesBounded b' := fun l hl =>
    hLbb l (whnf_fvarLeaves m.wf fuel hwhb l hl)
  have hoka' := whnf_FvarsOk m.wf fuel hwha hoka
  have hokb' := whnf_FvarsOk m.wf fuel hwhb hokb
  clear hwha hwhb hwa hwb haa hab hia hib hba hbb hLba hLbb hoka hokb
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
    have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_forallE hoka'
    obtain ⟨hokty₂, hokbody₂⟩ := FvarsOk.of_forallE hokb'
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
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbty₁ hLbty₂ hokty₁ hokty₂
        haty₁ haty₂ hA1 hA2
    subst hAeq
    have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
    rw [← hveq]
    refine pi_congr fun x hx => ?_
    obtain ⟨habody₁, hwfact₁⟩ := hcond₁ x A₁ hA1 hx
    obtain ⟨habody₂, hwfact₂⟩ := hcond₂ x A₁ hA2 hx
    obtain ⟨w₁, hw₁, -⟩ := hwfact₁ v₁ hv₁
    obtain ⟨w₂, hw₂, -⟩ := hwfact₂ v₂ hv₂
    rw [hw₁, hw₂]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hba'.1
        · exact hLbty₁ l hl'
    have hLbo₂ : Expr.LeavesBounded (body₂.instantiate1 (.fvar d n₂ ty₂)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₂ 0 hl with hl' | hl'
      · exact hLbb' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbb'.1
        · exact hLbty₂ l hl'
    simpa using ihd hd2
      (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
      (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
      hLbo₁ hLbo₂
      (FvarsOk.instantiate1 hwa'.1 hokty₁ haty₁ hA1 hx body₁ 0 hwa'.2 hokbody₁)
      (FvarsOk.instantiate1 hwb'.1 hokty₂ haty₂ hA2 hx body₂ 0 hwb'.2 hokbody₂)
      habody₁ habody₂ hw₁ hw₂
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_lam hoka'
    obtain ⟨hokty₂, hokbody₂⟩ := FvarsOk.of_lam hokb'
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
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbty₁ hLbty₂ hokty₁ hokty₂
        haty₁ haty₂ hA1 hA2
    subst hAeq
    have hveq : v₁.eval φ = v₂.eval φ := Level.isEquiv_sound hlev φ
    rw [← hveq]
    refine lam_congr fun x hx => ?_
    obtain ⟨habody₁, hwfact₁⟩ := hcond₁ x A₁ hA1 hx
    obtain ⟨habody₂, hwfact₂⟩ := hcond₂ x A₁ hA2 hx
    obtain ⟨w₁, B₁, hw₁, -, -⟩ := hwfact₁ v₁ hv₁
    obtain ⟨w₂, B₂, hw₂, -, -⟩ := hwfact₂ v₂ hv₂
    rw [hw₁, hw₂]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hba'.1
        · exact hLbty₁ l hl'
    have hLbo₂ : Expr.LeavesBounded (body₂.instantiate1 (.fvar d n₂ ty₂)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₂ 0 hl with hl' | hl'
      · exact hLbb' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbb'.1
        · exact hLbty₂ l hl'
    simpa using ihd hd2
      (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
      (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
      hLbo₁ hLbo₂
      (FvarsOk.instantiate1 hwa'.1 hokty₁ haty₁ hA1 hx body₁ 0 hwa'.2 hokbody₁)
      (FvarsOk.instantiate1 hwb'.1 hokty₂ haty₂ hA2 hx body₂ 0 hwb'.2 hokbody₂)
      habody₁ habody₂ hw₁ hw₂
  | Expr.app f₁ a₁, Expr.app f₂ a₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbf₁ : Expr.LeavesBounded f₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbf₂ : Expr.LeavesBounded f₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    have hLba₁ : Expr.LeavesBounded a₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLba₂ : Expr.LeavesBounded a₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokf₁, hoka₁⟩ := FvarsOk.of_app hoka'
    obtain ⟨hokf₂, hoka₂⟩ := FvarsOk.of_app hokb'
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
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbf₁ hLbf₂ hokf₁ hokf₂ haf₁ haf₂ hf1 hf2
    have hae : va₁ = va₂ :=
      ihd h hwa'.2 hwb'.2 hba'.2 hbb'.2 hLba₁ hLba₂ hoka₁ hoka₂ haa₁ haa₂ ha1 ha2
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

private theorem infer_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel) :
    InferClaims m φ (fuel + 1) := by
  intro d e t ρ h hw hb hLb hok ha
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
    obtain ⟨tty, u, hty, hwt, rfl⟩ := inferTypeCore_forall_inv hv₀ h
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨⟨A, tA, hA, htA, hmemA⟩, hAtA⟩ :=
      ihi hty hw.1 hb.1 hLbty hokty haty
    have hwtty := inferTypeCore_WScoped m.wf fuel hty hw.1
    have hbtty := inferTypeCore_looseBVars m.wf fuel hty hw.1 hb.1 hLbty
    have hLbtty : Expr.LeavesBounded tty := fun l hl =>
      hLbty l (inferTypeCore_fvarLeaves m.wf fuel hty hw.1 l hl)
    have hoktty : FvarsOk V m.val env φ d ρ tty :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hty hw.1) hokty
    rw [sort_result ihw hwt hwtty hbtty hLbtty hoktty hAtA] at htA
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
    obtain ⟨v, tty, u, bt, tbt, v', hc, htyi, hu, hbt, htbt, hwv, heqv, rfl⟩ :=
      inferTypeCore_lam_inv h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_lam hok
    simp only [AnnotOk] at ha
    obtain ⟨haty, -, hcond⟩ := ha
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    -- the domain interprets (via its own inference)
    obtain ⟨⟨A, tA, hA, -, -⟩, -⟩ :=
      ihi htyi hw.1 hb.1 hLbty hokty haty
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
        · exact hLbty l hb'
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
        ihi hbt hwo hbo hLbo hoko hbodyA
      -- the re-check gives the fibre's universe
      have hokbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hbt hwo) hoko
      have hbbt : bt.looseBVarsBounded 0 = true :=
        inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo
      have hLbbt : Expr.LeavesBounded bt := fun l hl =>
        hLbo l (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl)
      obtain ⟨⟨vbt, tvbt, hbti2, htbti, hmem2⟩, hAtbt⟩ :=
        ihi htbt hwbt hbbt hLbbt hokbt hAbt
      have hwtbt := inferTypeCore_WScoped m.wf fuel htbt hwbt
      have hbtbt := inferTypeCore_looseBVars m.wf fuel htbt hwbt hbbt hLbbt
      have hLbtbt : Expr.LeavesBounded tbt := fun l hl =>
        hLbbt l (inferTypeCore_fvarLeaves m.wf fuel htbt hwbt l hl)
      have hoktbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) tbt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htbt hwbt) hokbt
      rw [sort_result ihw hwv hwtbt hbtbt hLbtbt hoktbt hAtbt] at htbti
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
      ihi htf hw.1 hb.1 hLbf hokf haf
    have hwtf := inferTypeCore_WScoped m.wf fuel htf hw.1
    have hbtf := inferTypeCore_looseBVars m.wf fuel htf hw.1 hb.1 hLbf
    have hLbtf : Expr.LeavesBounded tf := fun l hl =>
      hLbf l (inferTypeCore_fvarLeaves m.wf fuel htf hw.1 l hl)
    have hoktf : FvarsOk V m.val env φ d ρ tf :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htf hw.1) hokf
    obtain ⟨hiw, haPi⟩ := ihw hwh hwtf hbtf hLbtf hoktf hAtf
    have hwPi := whnf_WScoped m.wf fuel hwh hwtf
    have hbPi := whnf_looseBVars m.wf fuel hwh hbtf
    have hLbPi : Expr.LeavesBounded (Expr.forallE n' ty' body' mPi) := fun l hl =>
      hLbtf l (whnf_fvarLeaves m.wf fuel hwh l hl)
    have hokPi : FvarsOk V m.val env φ d ρ (.forallE n' ty' body' mPi) :=
      whnf_FvarsOk m.wf fuel hwh hoktf
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
      ihi hta hw.2 hb.2 hLba hoka haa
    simp only [AnnotOk] at haPi
    obtain ⟨haty', -, hcond'⟩ := haPi
    have hLbta : Expr.LeavesBounded ta := fun l hl =>
      hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hw.2 l hl)
    have hLbty' : Expr.LeavesBounded ty' := fun l hl =>
      hLbPi l (by simp [fvarLeaves, hl])
    have hAeq : vta = A' :=
      ihd hde
        (inferTypeCore_WScoped m.wf fuel hta hw.2) hwPi.1
        (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba) hbPi.1
        hLbta hLbty'
        (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hw.2) hoka)
        ((FvarsOk.of_forallE hokPi).1)
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

end Claims

/-- The mutual soundness induction; see the module docstring. -/
theorem check_sound (m : EnvModel V env) :
    ∀ (fuel : Nat), WhnfClaims m φ fuel ∧ DefEqClaims m φ fuel ∧ InferClaims m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro d e e' ρ h
      exact nomatch h
    · intro d a b ρ h
      exact nomatch h
    · intro d e t ρ h
      exact nomatch h
  | succ fuel ih =>
    obtain ⟨ihw, ihd, ihi⟩ := ih
    exact ⟨whnf_claims m ihw ihd ihi, defeq_claims m ihw ihd ihi,
      infer_claims m ihw ihd ihi⟩

/-! ## Fuel-instantiated wrappers -/

/-- Reduction preserves the interpretation and annotation truthfulness. -/
theorem whnf_facts (m : EnvModel V env) {d : Nat} {e e' : Expr} {ρ : Nat → V}
    (h : whnf env d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m checkFuel).1 h hw hb hLb hok ha

/-- A positive definitional-equality verdict means the interpretations
agree, whenever both are defined. -/
theorem isDefEq_sound (m : EnvModel V env) {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : isDefEq env d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  (check_sound m checkFuel).2.1 h hwa hwb hba hbb hLba hLbb hoka hokb haa hab hva hvb

/-- Successful inference is sound (bundled with syntactic
well-scopedness of the output). -/
theorem inferType_sound (m : EnvModel V env) {d : Nat} {e t : Expr} {ρ : Nat → V}
    (h : inferType env d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := (check_sound m checkFuel).2.2 h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf checkFuel h hw, this.2⟩

/-- A successful `ensureSort` identifies the interpretation of the type
with a universe. -/
theorem ensureSort_sound (m : EnvModel V env) {d : Nat} {t : Expr} {u : Level}
    (h : ensureSort env d t = .ok u) {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSort at h
  cases hwh : whnf env d t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnf_facts m hwh hw hb hLb hok ha
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure, interpExpr]

end Setlec
