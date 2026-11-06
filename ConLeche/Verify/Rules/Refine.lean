module

public import ConLeche.Rules.Refine
public import ConLeche.Kernel.CoreIO
import ConLeche.Verify.Rules.Bridge
public import ConLeche.Kernel.Inductives.Positivity

public section

/-!
# An accepting run at a refinement is a derivation at the refined environment (task #469)

The bridge (`Verify/Rules/Bridge.lean`) turns an accepting run into a derivation at the run's
environment; `Rules/Refine.lean` carries a derivation from a refinement to the environment it
refines.  Composed: a run that succeeds at an environment holding some definitions only as their
statements is a derivation at the environment holding them with their values, so it is sound in
every model of that one.  A run's RESULT is not the refined environment's run's
(`tests/ConLecheTests/RefineTests.lean`); its derivation is.

For a former read at its telescope (`reducedFormer`, `familyTelescope`): its reduct at a
refinement is a telescope of reductions at the refined environment (`reducedFormer_refine`).
-/

namespace ConLeche.Rules

open ConLeche

variable {env₁ env₂ : Env}

theorem whnf_refine (h : EnvRefines env₁ env₂) {fuel d : Nat} {e e' : Expr}
    (hr : whnf .verified false env₁ fuel d e = .ok e') : Red env₂ d e e' :=
  Red.refine h (whnf_bridge hr)

theorem isDefEqCore_refine (h : EnvRefines env₁ env₂) {fuel d : Nat} {a b : Expr}
    (hr : isDefEqCore .verified false env₁ fuel d a b = .ok true) : DefEq env₂ d a b :=
  DefEq.refine h (isDefEqCore_bridge hr)

theorem inferTypeCore_refine (h : EnvRefines env₁ env₂) {fuel d : Nat} {e t : Expr}
    (hr : inferTypeCore .verified false env₁ fuel d e = .ok t) : Infer env₂ .full d e t :=
  Infer.refine h (inferTypeCore_bridge hr)

theorem inferTypeCoreIO_refine (h : EnvRefines env₁ env₂) {fuel d : Nat} {e t : Expr}
    (hr : inferTypeCoreIO .verified false env₁ fuel d e = .ok t) : Infer env₂ .io d e t :=
  Infer.refine h (inferTypeCoreIO_bridge hr)

/-- **A telescope of reductions**: `e` at depth `i` reduces to a Π over the first domain, whose
body opened at `i` is again such a telescope, `n` times, and then to the sort `s`. -/
def TeleRed (env : Env) : Nat → Nat → Expr → List Expr → Level → Prop
  | i, 0, e, [], s => Red env i e (.sort s)
  | i, n + 1, e, dom :: bs, s =>
    ∃ body, Red env i e (.forallE dom body) ∧
      TeleRed env (i + 1) n (body.instantiate1 (.fvar i dom)) bs s
  | _, _, _, _, _ => False

theorem TeleRed.refine (h : EnvRefines env₁ env₂) :
    ∀ (i n : Nat) (e : Expr) (bs : List Expr) (s : Level), TeleRed env₁ i n e bs s →
      TeleRed env₂ i n e bs s
  | i, 0, e, [], s, ht => Red.refine h ht
  | i, n + 1, e, dom :: bs, s, ht => by
    obtain ⟨body, hr, hrest⟩ := ht
    exact ⟨body, Red.refine h hr, TeleRed.refine h (i + 1) n _ bs s hrest⟩
  | _, 0, _, _ :: _, _, ht => nomatch ht
  | _, _ + 1, _, [], _, ht => nomatch ht

/-- **The telescope walk's run is a telescope of reductions.** -/
theorem whnfTelescope_teleRed {env : Env} {F : Nat} :
    ∀ (i n : Nat) (e : Expr) (bs : List Expr) (s : Level),
      whnfTelescope (fueledOps .verified F) env i n e = .ok (bs, s) → TeleRed env i n e bs s
  | i, 0, e, bs, s, hr => by
    unfold whnfTelescope at hr
    cases hw : (fueledOps .verified F).whnf env i e with
    | error _ => rw [hw] at hr; exact nomatch hr
    | ok w =>
      rw [hw] at hr
      cases w with
      | sort u =>
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact whnf_bridge hw
      | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
  | i, n + 1, e, bs, s, hr => by
    unfold whnfTelescope at hr
    cases hw : (fueledOps .verified F).whnf env i e with
    | error _ => rw [hw] at hr; exact nomatch hr
    | ok w =>
      rw [hw] at hr
      cases w with
      | forallE dom body =>
        simp only [bind, Except.bind] at hr
        cases hrest : whnfTelescope (fueledOps .verified F) env (i + 1) n
            (body.instantiate1 (.fvar i dom)) with
        | error _ => rw [hrest] at hr; exact nomatch hr
        | ok p =>
          rw [hrest] at hr
          obtain ⟨bs', s'⟩ := p
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨body, whnf_bridge hw, whnfTelescope_teleRed (i + 1) n _ bs' s' hrest⟩
      | _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr

/-- **A former's reduct at a refinement is a telescope of reductions at the refined
environment**: its closed telescope's domains and sort are reached from its type by reduction
there. -/
theorem reducedFormer_refine (h : EnvRefines env₁ env₂) {F n : Nat} {cv f : ConstantVal}
    (hr : reducedFormer (fueledOps .verified F) env₁ cv n = .ok f) :
    ∃ bs s, f = { cv with type := closeTelescope bs 0 (.sort s) } ∧
      TeleRed env₂ 0 n cv.type bs s := by
  unfold reducedFormer at hr
  cases ht : whnfTelescope (fueledOps .verified F) env₁ 0 n cv.type with
  | error _ => rw [ht] at hr; exact nomatch hr
  | ok p =>
    rw [ht] at hr
    obtain ⟨bs, s⟩ := p
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hr
    exact ⟨bs, s, hr.symm, TeleRed.refine h 0 n _ bs s (whnfTelescope_teleRed 0 n _ bs s ht)⟩

end ConLeche.Rules
