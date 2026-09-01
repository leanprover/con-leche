import Setlec.SetR.Bridge.StuckIrrel

/-!
# `etaCert`, bridged (task #148, T3, batch c/d — the one-sided λ)

D13 `eta` is the checker's `etaCert` (`Core.lean:1026-1039`) read
premise for premise:

```
tb ← infer b,  whnf tb = ∀ (_ : ty₂), _     →  Infer Δ b tb, DefEq Δ tb (.pi A₂ B)
defeq ty₂ ty₁                               →  DefEq Δ A₂ A₁
defeq (body₁[x]) (b x)                      →  DefEq (A₁::Δ) b₁ (.app b.lift (.bvar 0))
```

so the clause is four bridge moves and one constructor.  Compare the TT
lane's `etaCert_stepTT`, which additionally has to *retype* `b` at the
λ's domain (`congrPi`) before `HasType.eta` fires, and then compose with
`congrLam`: none of that is needed here, because the rule already names
the domain mismatch as its own premise.  That is premise-exactness doing
the retyping once, in the rule, instead of once per use.

The only real work is the third premise's right-hand side: the checker
states it as `.app b (.fvar d n₁ ty₁)` at depth `d + 1`, whose
denotation is `.app (⟦b⟧.liftN 1) (.bvar 0)` — the lift by
`denote_weaken_top` (`b` is scoped below `d`), the variable by the
`fvar` clause's index arithmetic.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- `etaCert`'s verdict yields an equation (D13). -/
def EtaCertStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {n₁ : Name} {ty₁ body₁ b : Expr}
    {mb : BinderMeta},
    etaCertP mode env fuel d n₁ ty₁ body₁ mb b = .ok true →
    Expr.WScoped d (.lam n₁ ty₁ body₁ mb) →
    (Expr.lam n₁ ty₁ body₁ mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n₁ ty₁ body₁ mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ (.lam n₁ ty₁ body₁ mb) →
    CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr},
      denote m.cval env φ d (.lam n₁ ty₁ body₁ mb) = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- **`EtaCertStepR`, proved.** -/
theorem etaCert_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) : EtaCertStepR (mode := mode) m φ fuel := by
  intro d Δ n₁ ty₁ body₁ b mb h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨tb, n₂, ty₂, fb, mb₂, htb, hwtb, hdty, hdbody, -⟩ :=
    etaCert_inv h
  simp only [Expr.WScoped] at hwa
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba
  have hLty₁ : Expr.LeavesBounded ty₁ := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hLbody₁ : Expr.LeavesBounded body₁ := fun l hl =>
    hLa l (by simp [Expr.fvarLeaves, hl])
  have hCty₁ : CtxOkR mode m.cval env φ d Δ ty₁ :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa
  have hCbody₁ : CtxOkR mode m.cval env φ d Δ body₁ :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa
  -- the λ's denotation, split
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
  -- `b` has a Π-type (premises one and two)
  obtain ⟨vb₀, P, hvb₀, hP, TB, hbI, hbD⟩ :=
    inferShapeR m φ ihw ihi htb hwtb hwb hbb hLb hCb
  have hveq : vb₀ = vb := by rw [hvb₀] at hvb; exact Option.some.inj hvb
  rw [hveq] at hbI
  -- the reduct's frame conditions, for the domain certificate
  obtain ⟨htbw, htbb, htbL, htbC⟩ := frame_inferR m.wf htb hwb hbb hLb hCb
  have hwr : Expr.WScoped d (.forallE n₂ ty₂ fb mb₂) :=
    whnf_WScoped m.wf fuel hwtb htbw
  have hbr : (Expr.forallE n₂ ty₂ fb mb₂).looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hwtb htbb
  have hLr : Expr.LeavesBounded (.forallE n₂ ty₂ fb mb₂) := fun l hl =>
    htbL l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCr : CtxOkR mode m.cval env φ d Δ (.forallE n₂ ty₂ fb mb₂) :=
    CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwtb) htbC
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
  -- premise three: the certified domain equation
  have hDA : DefEq mode env m.cval φ Δ A₂ A₁ :=
    ihd hdty hwr.1 hbr.1 (fun l hl => hLr l (by simp [Expr.fvarLeaves, hl]))
      hwa.1 hba.1 hLty₁
      (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCr)
      hCty₁ hA₂ hA₁
  -- premise four: the pointwise equation, at the opened variable
  have hvbUp : denote m.cval env φ (d + 1) b = some (vb.liftN 1) := by
    rw [denote_weaken_top hcl hwb.fvarsBelow, hvb]
    rfl
  have hCnew : CtxOkR mode m.cval env φ (d + 1) (A₁ :: Δ) (.fvar d n₁ ty₁) := by
    have := CtxOkR.openWith (cval := m.cval) (env := env) (φ := φ)
      (μ := mode) (body := .bvar 0) (ty := ty₁) (n := n₁) (A := A₁)
      (B := A₁) hcl
      ⟨hCa.1, fun l hl => by simp [Expr.fvarLeaves] at hl⟩ hCty₁ hA₁
      hwa.1.fvarsBelow ⟨A₁.liftN 1, Infer.bvar rfl, DefEq.refl⟩
    simpa [Expr.instantiate1] using this
  have hCapp : CtxOkR mode m.cval env φ (d + 1) (A₁ :: Δ)
      (.app b (.fvar d n₁ ty₁)) :=
    CtxOkR.app (CtxOkR.weakenTop hcl hCb) hCnew
  have hDB : DefEq mode env m.cval φ (A₁ :: Δ) B₁
      (.app (vb.liftN 1) (.bvar 0)) := by
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
      (CtxOkR.open hcl hCbody₁ hCty₁ hA₁ hwa.1.fvarsBelow) hCapp hB₁ ?_
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
  exact DefEq.eta hbI hbD hDA (by simpa [VExpr.lift] using hDB)

end Setlec.SetR
