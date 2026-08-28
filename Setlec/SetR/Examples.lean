import Setlec.SetR.CtxOkR

/-!
# Sanity derivations (task #148, T2)

Small closed derivations proving the constructors compose as intended —
the task's tests, compiled by the build.  Each is written against
*arbitrary* `(μ, env, cval, φ)`: the rules exercised here (sorts,
binders, beta, telescopes, weakening) are the environment-free core, so
the derivations are parametric — which is itself a check that no rule
sneaks in an unintended side condition.
-/

namespace Setlec.SetR.Examples

open Setlec.TT Setlec.TTVerify Setlec.SetR

variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- A beta step on a closed term:
`(fun (x : Sort 1) => x) Prop ⇝ Prop`, with the per-redex argument
certificate discharged by `Infer.sort` + `DefEq.refl`. -/
example : Red μ env cval φ []
    (.app (.lam (.sort 1) (.bvar 0)) (.sort 0)) (.sort 0) := by
  have h : Red μ env cval φ []
      (.app (.lam (.sort 1) (.bvar 0)) (.sort 0))
      ((VExpr.bvar 0).inst (.sort 0)) :=
    Red.beta Infer.sort DefEq.refl
  simpa [VExpr.inst] using h

/-- An `Infer` derivation through an application: the function part is
a λ over `Sort 1`, its type reduces (by `refl`) to a `pi`, and the
argument re-check is `Infer.sort` + `DefEq.refl`.  The conclusion type
is the instantiated codomain. -/
example : Infer μ env cval φ []
    (.app (.lam (.sort 1) (.bvar 0)) (.sort 0)) (.sort 1) := by
  have hf : Infer μ env cval φ [] (.lam (.sort 1) (.bvar 0))
      (.pi (.sort 1) (.sort 1)) := by
    have hb : Infer μ env cval φ [(.sort 1)] (.bvar 0)
        ((VExpr.sort 1).liftN 1) := Infer.bvar rfl
    exact Infer.lam Infer.sort DefEq.refl (by simpa using hb)
  have h : Infer μ env cval φ []
      (.app (.lam (.sort 1) (.bvar 0)) (.sort 0))
      ((VExpr.sort 1).inst (.sort 0)) :=
    Infer.app hf DefEq.refl Infer.sort DefEq.refl
  simpa [VExpr.inst] using h

/-- A `Tele` chain: walking the telescope `Sort 1 → Sort 1` at the
spine `[Prop]` lands on the residual `Sort 1` — `iotaCerts`'s walk in
miniature. -/
example : Tele μ env cval φ [] (.pi (.sort 1) (.sort 1))
    [(.sort 0)] (.sort 1) := by
  refine Tele.cons Infer.sort DefEq.refl ?_
  show Tele μ env cval φ [] ((VExpr.sort 1).inst (.sort 0)) [] (.sort 1)
  simpa [VExpr.inst] using
    (Tele.nil : Tele μ env cval φ [] (.sort 1) [] (.sort 1))

/-- M1 in action: the beta derivation above weakens into a one-entry
context, subjects lifted (here: unchanged, they are closed). -/
example (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) (B : VExpr) :
    Red μ env cval φ [B]
      (.app (.lam (.sort 1) (.bvar 0)) (.sort 0)) (.sort 0) := by
  have h : Red μ env cval φ []
      (.app (.lam (.sort 1) (.bvar 0)) (.sort 0)) (.sort 0) := by
    have h : Red μ env cval φ []
        (.app (.lam (.sort 1) (.bvar 0)) (.sort 0))
        ((VExpr.bvar 0).inst (.sort 0)) :=
      Red.beta Infer.sort DefEq.refl
    simpa [VExpr.inst] using h
  simpa [VExpr.lift, VExpr.liftN] using h.weakenHead hcl B

end Setlec.SetR.Examples
