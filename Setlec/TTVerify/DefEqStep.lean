import Setlec.TTVerify.ProjStep

/-!
# The `isDefEq` step of `CheckStepTT`

`DefEqClaimsTT` at `fuel + 1`: a positive definitional-equality verdict
yields a derivable equation.  Transpose of `defeq_claims`
(`Setlec/Model/Core/DefEq.lean`).

**Contract (3), proved in its strongest form** (§12.3): the conclusion
is an unconditional `Deq`, with no typing hypotheses on either side.
Contracts (1) and (2) are refuted — (1) by the checker's own
post-#100 de-gating, (2) by F1 — and the equation carries no typing
because `eqE`'s type slot is inert, so the strongest form is also the
cheapest.

## The shape

`defeqBody` is `defeqLoop` at its own budget, and `defeqLoop` iterates
`defeqStep` with the continuation abstracted — the checker's own
design decision, and the bridge inherits its benefit: **every lemma
about the body is proved once, with a hypothesis about the
continuation, and the loop lemma is one induction on the budget**
(`Setlec/Kernel/Core.lean`).  That is the same factoring `whnfLoop`
got, and for the same reason.

`defeqStep`'s moves, in order, with what discharges each:

| move | discharged by |
|---|---|
| syntactic `a == b` | `Deq.refl` |
| `whnfCore` both sides | `WhnfCoreClaimsTT`, twice |
| hoisted proof irrelevance | `proof_irrel_step` |
| literal acceleration | `reduceNat_stepTT` |
| lazy delta | `denote_delta_step` — an **identity** (§2) |
| the stuck block's leaves and congruences | proved inline |
| `stuckIrrel`'s five rescues | `StuckIrrelStepTT` (named) |
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- The continuation's contract, which is `DefEqClaimsTT`'s own shape
at the loop's remaining budget.

**The depth is fixed**, not quantified: `defeqLoop` hands `defeqStep` a
continuation already applied to the ambient depth, and every use of it
inside the body is at that depth.  The clauses that *do* go deeper —
the `∀` and `λ` congruences — recurse through `r.defeq` instead, which
is the claim at `fuel`, not the continuation. -/
def DefEqContTT {env : Env} (m : EnvTT env) (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {Δ : List VExpr} {a b : Expr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- **`stuckIrrel`'s verdict**: the five rescues the checker tries when
neither side reduces — pair eta (both ways), structure eta (both ways),
unit-likeness, and proof irrelevance.

Named at `stuckIrrel` rather than at the whole stuck block because
that is where the checker itself draws the line: the block's other
cases are leaf comparisons and congruences, which the bridge proves.
Of the five rescues only the last is proved (`proof_irrel_step`); the
eta and unit ones consume `CapsOkTT`'s laws, which exist. -/
def StuckIrrelStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    stuckIrrel (pureFns env fuel) env d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- **One iteration of the lazy-delta loop.**  The body's contract,
with the continuation abstracted exactly as the checker abstracts
it. -/
def DefEqStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool}, DefEqContTT m φ d k →
    ∀ {Δ : List VExpr} {a b : Expr},
      defeqStep (pureFns env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb → Deq Δ va vb

/-! ## The budget induction

One induction, exactly as for `whnfLoop` — and for the same reason:
the checker abstracts the continuation, so the body's lemma is proved
once with a hypothesis about it and the loop is a trivial induction.
The bridge inherits the factoring rather than rediscovering it. -/

/-- The lazy-delta loop preserves the claim at every budget. -/
theorem defeqLoop_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hstep : DefEqStepTT m φ fuel) :
    ∀ (budget : Nat) {d : Nat} {Δ : List VExpr} {a b : Expr},
      defeqLoop (pureFns env fuel) env d budget a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb → Deq Δ va vb := by
  intro budget
  induction budget with
  | zero =>
    intro d Δ a b h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δ a b h
    rw [defeqLoop] at h
    refine hstep ?_ h
    intro Δ' a' b' hkk
    exact ih hkk

/-- **`DefEqClaimsTT` at `fuel + 1`.**  The third quarter of
`CheckStepTT`, modulo the step. -/
theorem defeq_claimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hstep : DefEqStepTT m φ fuel) :
    DefEqClaimsTT m φ (fuel + 1) := by
  intro d a b Δ h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  rw [isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_claim m φ hstep defeqLoopFuel h hwa hba hLa hwb hbb hLb
    hCa hCb hva hvb

end Setlec.TTVerify
