import Setlec.Model.Core.Irrel

/-!
# Checker-core soundness: Eta

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- A successful eta certification identifies the λ's interpretation
with the stuck side's (`SetTheory.lam_eta`). -/
theorem etaCert_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {n₁ : Name} {ty₁ body₁ b : Expr} {m₁ : BinderMeta} {ρ : Nat → V}
    {va vb : V}
    (hec : etaCertP env fuel d n₁ ty₁ body₁ m₁ b = .ok true)
    (hwa : WScoped d (Expr.lam n₁ ty₁ body₁ m₁)) (hwb : WScoped d b)
    (hba : (Expr.lam n₁ ty₁ body₁ m₁).looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded (Expr.lam n₁ ty₁ body₁ m₁))
    (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁) = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  obtain ⟨tb, n₂, ty₂, fb, m₂, htb, hwtb, hdty, hdbody⟩ :=
    etaCert_inv hec
  -- λ-side components
  simp only [WScoped] at hwa
  obtain ⟨hwty₁, hwbody₁⟩ := hwa
  simp only [looseBVarsBounded, Bool.and_eq_true] at hba
  obtain ⟨hbty₁, hbbody₁⟩ := hba
  have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba l (by simp [fvarLeaves, hl])
  obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_lam hoka
  simp only [AnnotOk] at haa
  obtain ⟨haty₁, hconds⟩ := haa
  -- b's inferred type
  obtain ⟨-, ⟨vb', Tb, hvb', hTbi, hmemb⟩, hATb⟩ := ihi htb hwb hbb hLbb hokb
  have hvbeq : vb' = vb := by
    rw [hvb] at hvb'
    exact (Option.some.inj hvb').symm
  rw [hvbeq] at hmemb
  -- transport through whnf of the type
  have hwtbW := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb := inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLbb
  have hLbtb : Expr.LeavesBounded tb := fun l hl =>
    hLbb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  have hoktb : FvarsOk V m.val env φ d ρ tb :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hokb
  obtain ⟨hiwtb, hAwtb⟩ := ihw hwtb hwtbW hbtb hLbtb hoktb hATb
  have hwWS := whnf_WScoped m.wf fuel hwtb hwtbW
  have hwB := whnf_looseBVars m.wf fuel hwtb hbtb
  have hwLb : Expr.LeavesBounded (Expr.forallE n₂ ty₂ fb m₂) := fun l hl =>
    hLbtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hwOk : FvarsOk V m.val env φ d ρ (Expr.forallE n₂ ty₂ fb m₂) :=
    whnf_FvarsOk m.wf fuel hwtb hoktb
  simp only [WScoped] at hwWS
  obtain ⟨hwty₂, hwfb⟩ := hwWS
  simp only [looseBVarsBounded, Bool.and_eq_true] at hwB
  obtain ⟨hbty₂, hbfb⟩ := hwB
  have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hwLb l (by simp [fvarLeaves, hl])
  obtain ⟨hokty₂, hokfb⟩ := FvarsOk.of_forallE hwOk
  simp only [AnnotOk] at hAwtb
  obtain ⟨haty₂, hcondf⟩ := hAwtb
  -- the whnf'd type interprets to `Tb`
  have hTfi : interpExpr V m.val env φ d ρ (Expr.forallE n₂ ty₂ fb m₂) = some Tb := by
    rw [hiwtb, hTbi]
  simp only [interpExpr] at hTfi
  cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
  | none => rw [hA2] at hTfi; exact nomatch hTfi
  | some A₂ =>
  rw [hA2] at hTfi
  dsimp only at hTfi
  simp only [Option.some.injEq] at hTfi
  -- λ interp
  simp only [interpExpr] at hva
  cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
  | none => rw [hA1] at hva; exact nomatch hva
  | some A₁ =>
  rw [hA1] at hva
  dsimp only at hva
  simp only [Option.some.injEq] at hva
  -- domain agreement
  have hAeq : A₂ = A₁ :=
    ihd hdty hwty₂ hwty₁ hbty₂ hbty₁ hLbty₂ hLbty₁ hokty₂ hokty₁ haty₂ haty₁ hA2 hA1
  subst hAeq
  -- membership of `b`'s value in the pi over the λ's domain
  have hmem' : vb ∈ˢ piC A₂ (fun x =>
      (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (fb.instantiate1 (.fvar d n₂ ty₂))).getD SetTheory.empty) := by
    rw [hTfi]
    exact hmemb
  -- pointwise: the λ's body is `b` applied
  have hpoint : ∀ x, x ∈ˢ A₂ →
      ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body₁.instantiate1 (.fvar d n₁ ty₁))).getD SetTheory.empty) =
      SetTheory.app vb x := by
    intro x hx
    obtain ⟨habody₁, hwfact₁⟩ := hconds x A₂ hA1 hx
    obtain ⟨w₁, B₁, hw₁, -⟩ := hwfact₁
    have happI : interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (Expr.app b (.fvar d n₁ ty₁)) = some (SetTheory.app vb x) := by
      simp only [interpExpr]
      rw [interp_weaken_top hwb, hvb]
      simp [updV]
    have hwapp : WScoped (d + 1) (Expr.app b (.fvar d n₁ ty₁)) := by
      simp only [WScoped]
      exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwty₁⟩
    have hbapp : (Expr.app b (.fvar d n₁ ty₁)).looseBVarsBounded 0 = true := by
      simp [looseBVarsBounded, hbb, hbty₁]
    have hLbapp : Expr.LeavesBounded (Expr.app b (.fvar d n₁ ty₁)) := by
      intro l hl
      simp only [fvarLeaves, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | hl
      · exact hLbb l hl
      · exact hbty₁
      · exact hLbty₁ l hl
    have hokapp : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
        (Expr.app b (.fvar d n₁ ty₁)) := by
      have h0 : (Expr.app b (Expr.bvar 0)).instantiate1 (.fvar d n₁ ty₁) 0 =
          Expr.app b (.fvar d n₁ ty₁) := by
        simp [Expr.instantiate1, instantiate1_eq_self hbb]
      rw [← h0]
      exact FvarsOk.instantiate1 hwty₁ hokty₁ haty₁ hA1 hx
        (Expr.app b (Expr.bvar 0)) 0 (by simp only [WScoped]; exact ⟨hwb, trivial⟩)
        (fun l hl => hokb l (by simpa [fvarLeaves] using hl))
    have haapp : AnnotOk V m.val env φ (d + 1) (updV V ρ d x)
        (Expr.app b (.fvar d n₁ ty₁)) := by
      simp only [AnnotOk]
      refine ⟨AnnotOk.weaken_top hwb hab, trivial, vb, x,
        A₂,
        (fun y => (interpExpr V m.val env φ (d + 1) (updV V ρ d y)
          (fb.instantiate1 (.fvar d n₂ ty₂))).getD SetTheory.empty),
        ?_, ?_, hmem', hx⟩
      · rw [interp_weaken_top hwb]
        exact hvb
      · simp [interpExpr, updV]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbty₁
        · exact hLbty₁ l hl'
    have heq := ihd hdbody
      (hwty₁.instantiate1 0 hwbody₁) hwapp
      (looseBVarsBounded_instantiate1 body₁ 0 hbbody₁) hbapp
      hLbo₁ hLbapp
      (FvarsOk.instantiate1 hwty₁ hokty₁ haty₁ hA1 hx body₁ 0 hwbody₁ hokbody₁)
      hokapp habody₁ haapp hw₁ happI
    rw [hw₁]
    simpa using heq
  -- assemble via congruence and eta
  rw [← hva]
  have hstep : lamC A₂
      (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body₁.instantiate1 (.fvar d n₁ ty₁))).getD SetTheory.empty) =
      lamC A₂ (fun x => SetTheory.app vb x) :=
    lamC_congr (fun x hx => hpoint x hx)
  rw [hstep]
  exact lamC_eta hmem'

/-- Soundness of the one-sided-λ branch of `isDefEqCore` (λ on the
left): eta, else proof irrelevance. -/
theorem etaBranch_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {n₁ : Name} {ty₁ body₁ b : Expr} {m₁ : BinderMeta} {ρ : Nat → V}
    {va vb : V}
    (h : (do
      if ← etaCertP env fuel d n₁ ty₁ body₁ m₁ b then pure true
      else stuckIrrelP env fuel d (Expr.lam n₁ ty₁ body₁ m₁) b :
        CheckM Bool) = .ok true)
    (hwa : WScoped d (Expr.lam n₁ ty₁ body₁ m₁)) (hwb : WScoped d b)
    (hba : (Expr.lam n₁ ty₁ body₁ m₁).looseBVarsBounded 0 = true)
    (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded (Expr.lam n₁ ty₁ body₁ m₁))
    (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁))
    (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ (Expr.lam n₁ ty₁ body₁ m₁) = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  simp only [Bind.bind, Except.bind] at h
  cases hec : etaCertP env fuel d n₁ ty₁ body₁ m₁ b with
  | error e => rw [hec] at h; exact nomatch h
  | ok r =>
  rw [hec] at h
  dsimp only at h
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact stuckIrrel_sound ihw ihd ihi h hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | true =>
  exact etaCert_sound ihw ihd ihi hec hwa hwb hba hbb hLba hLbb
    hoka hokb haa hab hva hvb

/-- Soundness of the one-sided-λ branch of `isDefEqCore` (λ on the
right). -/
theorem etaBranch_sound' {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {n₂ : Name} {ty₂ body₂ a : Expr} {m₂ : BinderMeta} {ρ : Nat → V}
    {va vb : V}
    (h : (do
      if ← etaCertP env fuel d n₂ ty₂ body₂ m₂ a then pure true
      else stuckIrrelP env fuel d a (Expr.lam n₂ ty₂ body₂ m₂) :
        CheckM Bool) = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d (Expr.lam n₂ ty₂ body₂ m₂))
    (hba : a.looseBVarsBounded 0 = true)
    (hbb : (Expr.lam n₂ ty₂ body₂ m₂).looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a)
    (hLbb : Expr.LeavesBounded (Expr.lam n₂ ty₂ body₂ m₂))
    (hoka : FvarsOk V m.val env φ d ρ a)
    (hokb : FvarsOk V m.val env φ d ρ (Expr.lam n₂ ty₂ body₂ m₂))
    (haa : AnnotOk V m.val env φ d ρ a)
    (hab : AnnotOk V m.val env φ d ρ (Expr.lam n₂ ty₂ body₂ m₂))
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ (Expr.lam n₂ ty₂ body₂ m₂) = some vb) :
    va = vb := by
  simp only [Bind.bind, Except.bind] at h
  cases hec : etaCertP env fuel d n₂ ty₂ body₂ m₂ a with
  | error e => rw [hec] at h; exact nomatch h
  | ok r =>
  rw [hec] at h
  dsimp only at h
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact stuckIrrel_sound ihw ihd ihi h hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | true =>
  exact (etaCert_sound ihw ihd ihi hec hwb hwa hbb hba hLbb hLba
    hokb hoka hab haa hvb hva).symm

end Claims

end Setlec
