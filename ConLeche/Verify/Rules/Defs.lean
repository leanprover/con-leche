module

public import ConLeche.Rules.Rel
import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.CoreIO
import ConLeche.Verify.Knot

public section

/-!
# The bridge's statements: run ⇒ derivation (task #305)

One predicate per fueled entry point of a pure knot at a mode `μ`: an
accepting run at `fuel` yields a derivation in the rules tier
(`ConLeche/Rules/Rel.lean`).  The relation has no mode index — it
describes the verified checker, and the eager flag (task #353) changes
which sound steps are taken, not which steps are sound — so one
relation serves `.verified`, on and off the eager tower; the
step theorems are stated at `.verified` where a certificate is read
(the others stay general in `μ`), and the recomposition (`Model/Rules/Recompose.lean`) uses
them at `.verified`.

The five are closed by one mutual fuel induction (`Verify/Rules/Bridge.lean`),
over both flags at once,
whose step is the four `*_bridge_succ` theorems of the lane files
(`RedBridge`, `DefEqBridge`, `InferBridge`) over the shared certificate
bridges (`Certs`).  The zero cases are the checker's own zero-fuel
throws, proved here.

**Mechanical by construction** (ruling 2): every clause of every step
theorem inverts the run with the `Verify/*` inversion lemma of its
site and lands on one rule of `ConLeche/Rules/*` whose premises are
exactly the sub-runs the inversion hands back, each sub-run being at
`fuel` and bridged by an induction hypothesis.
-/

namespace ConLeche.Rules

variable {μ : CheckMode} {eager : Bool} {env : Env}

/-- `whnfCore` at `fuel` is bridged. -/
@[expose] def WhnfCoreBridge (μ : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Prop :=
  ∀ {c : Bool} {d : Nat} {e e' : Expr},
    whnfCore μ eager env fuel d e c = .ok e' → Red env d e e'

/-- `whnf` at `fuel` is bridged. -/
@[expose] def WhnfBridge (μ : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr},
    whnf μ eager env fuel d e = .ok e' → Red env d e e'

/-- `isDefEqCore` at `fuel` is bridged. -/
@[expose] def DefEqBridge (μ : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr},
    isDefEqCore μ eager env fuel d a b = .ok true → DefEq env d a b

/-- `inferTypeCore` at `fuel` is bridged, at the full grade. -/
@[expose] def InferBridge (μ : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr},
    inferTypeCore μ eager env fuel d e = .ok t → Infer env .full d e t

/-- `inferTypeCoreIO` (the io leaf lane, the `InferClaimIO` subject) at
`fuel` is bridged, at the io grade. -/
@[expose] def InferIOBridge (μ : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr},
    inferTypeCoreIO μ eager env fuel d e = .ok t → Infer env .io d e t

/-- The knot's io SLOT (`inferTypeIO`, what every internal inference
call site runs) is the io lane at its mode (`inferTypeIO_on`), so
its bridge is the lane's. -/
theorem inferTypeIO_bridge {fuel : Nat} (hio : InferIOBridge μ eager env fuel)
    {d : Nat} {e t : Expr}
    (h : inferTypeIO μ eager env fuel d e = .ok t) : Infer env .io d e t :=
  hio (by rwa [inferTypeIO_on] at h)

/-! ## The zero cases: every entry point throws at fuel `0` -/

theorem whnfCore_bridge_zero : WhnfCoreBridge μ eager env 0 := by
  intro c d e e' h
  rw [whnfCore_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem whnf_bridge_zero : WhnfBridge μ eager env 0 := by
  intro d e e' h
  rw [whnf_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem defeq_bridge_zero : DefEqBridge μ eager env 0 := by
  intro d a b h
  rw [isDefEqCore_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem infer_bridge_zero : InferBridge μ eager env 0 := by
  intro d e t h
  rw [inferTypeCore_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem inferIO_bridge_zero : InferIOBridge μ eager env 0 := by
  intro d e t h
  rw [inferTypeCoreIO_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

end ConLeche.Rules
