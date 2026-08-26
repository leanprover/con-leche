import Setlec.TTVerify.PairEtaStep
import Setlec.TTVerify.IotaStep

/-!
# The two literal chain links

`litMajorToCtor` and `projLitToCtor` are the same function up to the
non-literal fallback: a `String` literal is expanded to its constructor
form and reduced, a `Nat` literal is expanded to `Nat.zero` /
`Nat.succ k` (major position only), everything else passes through.

Both links are one lemma each once the two *expansion* denotations are
in hand — `denote_strLitToConstructor` (proved with the string-literal
inference clause) and `denote_natLitToConstructor` below.  Note what
that means: the expansions are `denote`-transparent, so these two links
are §2's identity again, not a `Deq` — the equation the chain
accumulates does not grow across them, and only the `whnf` that follows
the string expansion contributes anything.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- **A `Nat` literal's constructor form denotes to the literal.**
The `Nat` twin of `denote_strLitToConstructor`, and shorter for the
same reason `natLitT` is shorter than `strLitT`: the guard pins
`Nat.zero` and `Nat.succ` at empty level-parameter lists, so both
clauses are `denote_const_nolevels`. -/
theorem denote_natLitToConstructor {env : Env} (m : EnvTT env)
    (φ : Name → Nat) (hg : natLitSupported env = true) (d : Nat) (n : Nat) :
    denote m.cval env φ d (natLitToConstructor n)
      = denote m.cval env φ d (.lit (.natVal n)) := by
  rw [denote_natLit_numeral m φ hg d n]
  cases n with
  | zero =>
    rw [natLitToConstructor, denote_natZeroT m φ hg d]
    rfl
  | succ k =>
    rw [natLitToConstructor,
      denote_natSuccT m φ hg (denote_natLit_numeral m φ hg d k)]
    rfl

/-- The frame conditions of a `Nat` literal's constructor form. -/
theorem natLitToConstructor_frames {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {d : Nat} {Δ : List VExpr} (hlen : Δ.length = d)
    (n : Nat) :
    Expr.WScoped d (natLitToConstructor n) ∧
      (natLitToConstructor n).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (natLitToConstructor n) ∧
      CtxOk cval env φ d Δ (natLitToConstructor n) := by
  refine ⟨?_, natLitToConstructor_looseBVars n, ?_, hlen, ?_⟩
  · cases n <;> simp [natLitToConstructor, Expr.WScoped]
  · intro l hl
    rw [natLitToConstructor_fvarLeaves n] at hl
    exact nomatch hl
  · intro l hl
    rw [natLitToConstructor_fvarLeaves n] at hl
    exact nomatch hl

/-- **`LitMajorToCtorStepTT`, discharged.** -/
theorem litMajorToCtor_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (ihw : WhnfClaimsTT m φ fuel) :
    LitMajorToCtorStepTT m φ fuel := by
  intro d Δ e e' v h hws hb hLb hC hv
  match e, h with
  | .lit (.strVal s), h =>
    dsimp only [litMajorToCtorP, litMajorToCtor] at h
    split at h
    · next hg =>
      rw [whnf_def] at h
      refine whnf_reductOk m φ ihw h ?_ ?_ ?_ ?_ ?_
      · exact Expr.WScoped.of_not_hasFvar (strLitToConstructor_hasFvar s)
      · exact strLitToConstructor_looseBVars s 0
      · exact Expr.LeavesBounded.of_not_hasFvar
          (strLitToConstructor_hasFvar s)
      · refine ⟨hC.1, fun l hl => ?_⟩
        rw [strLitToConstructor_fvarLeaves s] at hl
        exact nomatch hl
      · rw [denote_strLitToConstructor m φ hg d]; exact hv
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨v, hv, Deq.refl, hws, hb, hLb, hC⟩
  | .lit (.natVal n), h =>
    dsimp only [litMajorToCtorP, litMajorToCtor, litToCtorIfNat] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split
    · next hg =>
      obtain ⟨hw2, hb2, hL2, hC2⟩ := natLitToConstructor_frames
        (cval := m.cval) (env := env) (φ := φ) hC.1 n
      exact ⟨v, by rw [denote_natLitToConstructor m φ hg d]; exact hv,
        Deq.refl, hw2, hb2, hL2, hC2⟩
    · exact ⟨v, hv, Deq.refl, hws, hb, hLb, hC⟩
  | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h
  | .app _ _, h | .lam _ _ _ _, h | .forallE _ _ _ _, h
  | .letE _ _ _ _, h | .proj _ _ _, h =>
    dsimp only [litMajorToCtorP, litMajorToCtor, litToCtorIfNat] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨v, hv, Deq.refl, hws, hb, hLb, hC⟩

/-- **`ProjLitToCtorStepTT`, discharged.**  The same function without
the `Nat` fallback. -/
theorem projLitToCtor_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (ihw : WhnfClaimsTT m φ fuel) :
    ProjLitToCtorStepTT m φ fuel := by
  intro d Δ e e' v h hws hb hLb hC hv
  match e, h with
  | .lit (.strVal s), h =>
    dsimp only [projLitToCtorP, projLitToCtor] at h
    split at h
    · next hg =>
      rw [whnf_def] at h
      refine whnf_reductOk m φ ihw h ?_ ?_ ?_ ?_ ?_
      · exact Expr.WScoped.of_not_hasFvar (strLitToConstructor_hasFvar s)
      · exact strLitToConstructor_looseBVars s 0
      · exact Expr.LeavesBounded.of_not_hasFvar
          (strLitToConstructor_hasFvar s)
      · refine ⟨hC.1, fun l hl => ?_⟩
        rw [strLitToConstructor_fvarLeaves s] at hl
        exact nomatch hl
      · rw [denote_strLitToConstructor m φ hg d]; exact hv
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨v, hv, Deq.refl, hws, hb, hLb, hC⟩
  | .lit (.natVal _), h | .bvar _, h | .fvar _ _ _, h | .sort _, h
  | .const _ _, h | .app _ _, h | .lam _ _ _ _, h
  | .forallE _ _ _ _, h | .letE _ _ _ _, h | .proj _ _ _, h =>
    dsimp only [projLitToCtorP, projLitToCtor] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨v, hv, Deq.refl, hws, hb, hLb, hC⟩

end Setlec.TTVerify
