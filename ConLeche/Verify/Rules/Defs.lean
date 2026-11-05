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

/-- A successful run of a projection guard's rows is the relation's
walk. -/
theorem checkGuardRows_bridge {inf wh : Nat → Expr → CheckM Expr} {bound : Level}
    (hinf : ∀ d e t, inf d e = .ok t → Infer env .io d e t)
    (hwh : ∀ d e t, wh d e = .ok t → Red env d e t) :
    ∀ rows, checkGuardRows inf wh bound rows = .ok () → GuardRows env bound rows
  | [], _ => .nil
  | (d, dom) :: rest, h => by
    unfold checkGuardRows at h
    simp only [Bind.bind, Except.bind] at h
    cases hi : inf d dom with
    | error err => rw [hi] at h; exact nomatch h
    | ok t =>
    rw [hi] at h
    dsimp only at h
    cases hw : wh d t with
    | error err => rw [hw] at h; exact nomatch h
    | ok w =>
    rw [hw] at h
    dsimp only at h
    cases w with
    | sort u =>
      dsimp only at h
      split at h
      next hz =>
        exact .row (hinf _ _ _ hi) (hwh _ _ _ hw) (by simpa using hz)
          (checkGuardRows_bridge hinf hwh rest h)
      next => exact nomatch h
    | _ => exact nomatch h

/-- The walk to a family's sort is `FormerSort`. -/
theorem formerSortLoop_bridgeW {wh : Nat → Expr → CheckM Expr}
    (hwh : ∀ d e t, wh d e = .ok t → Red env d e t) :
    ∀ {n d : Nat} {e : Expr} {s : Level},
      formerSortLoop wh d n e = .ok (some s) → FormerSort env d n e s
  | 0, d, e, s, h => by
    unfold formerSortLoop at h
    cases hr : wh d e with
    | error err => rw [hr] at h; exact nomatch h
    | ok w =>
      rw [hr] at h
      cases w with
      | sort s' =>
        cases Option.some.inj (Except.ok.inj h)
        exact .sort (hwh _ _ _ hr)
      | _ => exact nomatch h
  | n + 1, d, e, s, h => by
    unfold formerSortLoop at h
    cases hr : wh d e with
    | error err => rw [hr] at h; exact nomatch h
    | ok w =>
      rw [hr] at h
      cases w with
      | forallE dom b => exact .pi (hwh _ _ _ hr) (formerSortLoop_bridgeW hwh h)
      | _ => exact nomatch h

/-- A successful run of a projection's guard is `ProjGuard`. -/
theorem checkProjGuard_bridge {inf wh : Nat → Expr → CheckM Expr}
    (hinf : ∀ d e t, inf d e = .ok t → Infer env .io d e t)
    (hwh : ∀ d e t, wh d e = .ok t → Red env d e t)
    {entry : ProjEntry} {us : List Level}
    (h : checkProjGuard inf wh env entry us = .ok ()) : ProjGuard env entry us := by
  unfold checkProjGuard at h
  split at h
  case h_2 => exact nomatch h
  rename_i cvT caps hfT
  cases hb : projRowBound wh cvT caps us with
  | error err => rw [hb] at h; exact nomatch h
  | ok o =>
  rw [hb] at h
  unfold projRowBound at hb
  split at hb
  · next s hs =>
    cases hz : s.isAlwaysZero with
    | false =>
      simp only [hz, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hb
      exact .notProp hfT hs hz
    | true =>
      simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hb
      subst hb
      split at h
      · next rows hr => exact .prop hfT hs hz hr (checkGuardRows_bridge hinf hwh rows h)
      · exact nomatch h
  · next hs =>
    simp only [Bind.bind, Except.bind] at hb
    cases hl : formerSortLoop wh 0 (caps.nparams + caps.nIdx)
        (cvT.type.instantiateLevelParams cvT.levelParams us) with
    | error err => rw [hl] at hb; exact nomatch hb
    | ok o' =>
    rw [hl] at hb
    cases o' with
    | none => exact nomatch hb
    | some s =>
    have hfs := formerSortLoop_bridgeW hwh hl
    cases hnv : (Level.zeronessOf s).isNever with
    | true => exact .never hfT hs hfs hnv
    | false =>
      simp only [hnv, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hb
      subst hb
      split at h
      · next rows hr => exact .under hfT hs hfs hnv hr (checkGuardRows_bridge hinf hwh rows h)
      · exact nomatch h

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
