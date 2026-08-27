import Setlec.TTVerify.StuckStep

/-!
# The one-sided-λ obligation

`EtaCertStepTT`: `etaCert`'s verdict yields an equation.  The checker's
certificate is exactly the layer's `eta` rule read backwards:

```
tb ← infer b,  whnf tb = ∀ (_ : ty₂), _        b is a function
defeq ty₂ ty₁                                  at the λ's domain
defeq (body₁[x]) (b x)                         pointwise
```

and the layer supplies `eta` (`λ x. f x ≡ f`) plus `congrLam` to move
the pointwise equation under the binder.  **`funext` is not needed**:
the checker's third check is already stated at the *opened* variable,
which is the shape `eta`'s left-hand side has, so the two equations
compose without ever going through a Π-typed equation.

The one non-mechanical step is the domain.  `eta` fires at whatever
domain the function's Π-type has — `ty₂`'s denotation — while the λ
carries `ty₁`, and the checker certifies only that the two are
definitionally equal.  `congrPi` retypes `b` at the λ's own domain
first, and then both rules speak about the same `A₁`.
-/

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode; the seven gated checks
reduce definitionally at `.ttModel`. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- **`EtaCertStepTT`, discharged.** -/
theorem etaCert_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) : EtaCertStepTT m φ fuel := by
  intro d Δ n₁ ty₁ body₁ b mb h hwa hba hLa hwb hbb hLb hCa hCb va vb
    hva hvb
  obtain ⟨tb, n₂, ty₂, fb, mb₂, htb, hwtb, hdty, hdbody⟩ := etaCert_inv h
  -- the λ's parts
  simp only [Expr.WScoped] at hwa
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba
  have hLty₁ : Expr.LeavesBounded ty₁ := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hLbody₁ : Expr.LeavesBounded body₁ := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hCty₁ : CtxOk m.cval env φ d Δ ty₁ :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa
  have hCbody₁ : CtxOk m.cval env φ d Δ body₁ :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa
  rw [denote_lam] at hva
  cases hA₁ : denote m.cval env φ d ty₁ with
  | none => rw [hA₁] at hva; exact nomatch hva
  | some A₁ =>
  cases hB₁ : denote m.cval env φ (d + 1)
      (body₁.instantiate1 (.fvar d n₁ ty₁)) with
  | none => rw [hA₁, hB₁] at hva; exact nomatch hva
  | some B₁ =>
  rw [hA₁, hB₁] at hva
  obtain rfl : VExpr.lam A₁ B₁ = va := Option.some.inj hva
  -- `b` has a Π-type
  obtain ⟨vb', Tb, hvb', hTb, hbT⟩ := ihi htb hwb hbb hLb hCb
  obtain rfl : vb = vb' := by
    rw [hvb'] at hvb; exact (Option.some.inj hvb).symm
  have hCtb : CtxOk m.cval env φ d Δ tb :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hCb
  have hwtb' : Expr.WScoped d tb := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb : tb.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLb
  have hLtb : Expr.LeavesBounded tb := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  obtain ⟨P, hP, hDP⟩ := ihw hwtb hwtb' hbtb hLtb hCtb hTb
  -- the reduct's parts
  have hwr : Expr.WScoped d (.forallE n₂ ty₂ fb mb₂) :=
    whnf_WScoped m.wf fuel hwtb hwtb'
  have hbr : (Expr.forallE n₂ ty₂ fb mb₂).looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hwtb hbtb
  have hLr : Expr.LeavesBounded (.forallE n₂ ty₂ fb mb₂) := fun l hl =>
    hLtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCr : CtxOk m.cval env φ d Δ (.forallE n₂ ty₂ fb mb₂) :=
    CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hCtb
  simp only [Expr.WScoped] at hwr
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbr
  rw [denote_forallE] at hP
  cases hA₂ : denote m.cval env φ d ty₂ with
  | none => rw [hA₂] at hP; exact nomatch hP
  | some A₂ =>
  cases hB₂ : denote m.cval env φ (d + 1)
      (fb.instantiate1 (.fvar d n₂ ty₂)) with
  | none => rw [hA₂, hB₂] at hP; exact nomatch hP
  | some B₂ =>
  rw [hA₂, hB₂] at hP
  obtain rfl : VExpr.pi A₂ B₂ = P := Option.some.inj hP
  -- the certified domain equation, and `b` retyped at the λ's domain
  have hDA : Deq Δ A₂ A₁ :=
    ihd hdty hwr.1 hbr.1 (fun l hl => hLr l (by simp [Expr.fvarLeaves, hl]))
      hwa.1 hba.1 hLty₁
      (CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCr)
      hCty₁ hA₂ hA₁
  have hbPi : HasType Δ vb (.pi A₁ B₂) := by
    refine Deq.conv (Deq.conv hbT hDP) ⟨.sort 0, ?_⟩
    obtain ⟨T, hT⟩ := hDA
    obtain ⟨T', hT'⟩ := Deq.refl (Γ := A₂ :: Δ) (a := B₂)
    exact HasType.congrPi hT hT'
  -- the pointwise equation, at the opened variable
  have hfbΔ : Expr.fvarsBelow d b := hwb.fvarsBelow
  have hvbUp : denote m.cval env φ (d + 1) b = some (vb.liftN 1) := by
    rw [denote_weaken_top hcl hfbΔ, hvb]
    rfl
  have hCnew : CtxOk m.cval env φ (d + 1) (A₁ :: Δ) (.fvar d n₁ ty₁) := by
    have := CtxOk.openWith (cval := m.cval) (env := env) (φ := φ)
      (body := .bvar 0) (ty := ty₁) (n := n₁) (A := A₁) (B := A₁) hcl
      ⟨hCa.1, fun l hl => by simp [Expr.fvarLeaves] at hl⟩ hCty₁ hA₁
      hwa.1.fvarsBelow (HasType.bvar (by simp))
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOk m.cval env φ (d + 1) (A₁ :: Δ)
      (.app b (.fvar d n₁ ty₁)) :=
    CtxOk.app (CtxOk.weakenTop hcl hCb) hCnew
  have hDB : Deq (A₁ :: Δ) B₁ (.app (vb.liftN 1) (.bvar 0)) := by
    refine ihd hdbody (Expr.WScoped.instantiate1 hwa.1 0 hwa.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba.2)
      (fun l hl => by
        rcases Expr.fvarLeaves_instantiate1 body₁ 0 hl with h2 | h2
        · exact hLbody₁ l h2
        · rw [Expr.fvarLeaves] at h2
          rcases List.mem_cons.mp h2 with rfl | h3
          · exact hba.1
          · exact hLty₁ l h3)
      ?_ ?_ ?_
      (CtxOk.open hcl hCbody₁ hCty₁ hA₁ hwa.1.fvarsBelow) hCapp hB₁ ?_
    · simp only [Expr.WScoped]
      exact ⟨Expr.WScoped.mono (by omega) hwb,
        by omega, Expr.WScoped.mono (by omega) hwa.1⟩
    · simp [Expr.looseBVarsBounded, hbb]
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h2 | h2
      · exact hLb l h2
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hba.1
        · exact hLty₁ l h3
    · rw [denote_app, hvbUp, denote_fvar]
      simp
  -- `λ x. b x ≡ b`, and the λ agrees with it under the binder
  obtain ⟨T₁, hT₁⟩ := Deq.refl (Γ := Δ) (a := A₁)
  obtain ⟨T₂, hT₂⟩ := hDB
  exact Deq.trans ⟨.sort 0, HasType.congrLam hT₁ hT₂⟩
    ⟨.sort 0, HasType.eta hbPi⟩

end Setlec.TTVerify
