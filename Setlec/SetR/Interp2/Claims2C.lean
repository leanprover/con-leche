import Setlec.SetR.Interp2.Claims2B

/-!
# `Claims2`, generation four — the grading hoisted above `ρ`

Lineage: `Claims2` → `Claims2A` → `Claims2B` → this file.  The first
two were **refuted**; `Claims2B` is **not**.  It is merely too weak to
supply `CtxOk2.openCong`, and that distinction matters — this is the
first generation change in the arc that fixes an insufficiency rather
than a falsehood.

## The change, and why it is forced

`CtxOk2.openCong` (`Step2/Dispatch.lean`) is the gate for the
context-currency move: five `∀`/`λ` congruence sites need it.  It
needs `AnnotOk2` of both domains at **every** satisfying valuation,
because `CtxOk2` is a `∀ ρ` statement about the *extended* context.
`Claims2B` supplies them **under** its own `∀ ρ`, so a site that has
introduced `ρ` holds them at one valuation only.

That gap is not an artifact of any proof: `not_openCongLocal`
refutes the ρ-local congruence lemma **premise-free**, even with the
left domain fully certified.  *The problem is the quantifier, not the
grading.*

So every `AnnotOk2` that a claim either **takes** or **gives** moves
above the `∀ ρ`.  The `interp2` equalities and the membership stay
where they are — they are genuinely per-valuation facts.

## Blast radius, audited before this file was written

Hoisting `DefEqClaims2B` alone does not close: `infer_app_claim2A`
draws one of its two `AnnotOk2` from the *reduction* claims' graded
output at a single `ρ`, and `betaCert2P_of_claims` draws one from
`BetaCert2P`'s own ρ-local premise.  So the change is **all four
claims plus `BetaCert2P`** — the fourth time in this arc that a repair
scoped to one claim of the family had to be widened, and the instance
that turned family-wide from the fallback into the **starting
assumption**.

## Why the shape is believed right

`AnnotOk2.hoist_pi`/`hoist_lam` show the repair **self-propagates** at
the congruences: the hoisted node fact splits into the domain's
hoisted form *and* the codomain's hoisted form in the extended context
`A :: Δa`, which is exactly the pair the recursive call needs.  A
repair that reproduces its own premise across the recursion is the
sign that the quantifier now sits where the induction wants it.

## What is deliberately *not* in this generation

Seal 11's decision to carry `CtxOk2` rather than `CtxOkR` in all four
claims.  It is decided and specified, but it is a second, independent
change, and this campaign's own rule is that a mid-flight statement
change costs one silent integration break per consumer.  One change
per generation; the context move is generation five.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Head normalisation, hoisted. -/
def WhnfCoreClaims2C (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- The reduction loop, hoisted. -/
def WhnfClaims2C (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- Definitional equality, hoisted.  The two `AnnotOk2` remain
premises and never become conclusions, so nothing crosses an equality
and `deqStep2_symm`/`deqStep2_trans` stay one-liners. -/
def DefEqClaims2C (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ ba

/-- Inference, hoisted — **and extended**.  The returned type's
`AnnotOk2` is now delivered alongside the subject's, which is seal 8's
open question answered from two independent sites (`infer_app_claim2A`
and `betaCert2P_of_claims`) and which retires the inference quarter's
`TypeOk2` residue.  The membership stays per-valuation. -/
def InferClaims2C (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2 m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      ∃ F' ta, F ≤ F' ∧
        denote2 μ m.acval env φ F' d t = some ta ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The hoisted step. -/
def CheckStep2C (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2C μ m φ fuel → WhnfClaims2C μ m φ fuel →
    DefEqClaims2C μ m φ fuel → InferClaims2C μ m φ fuel →
    WhnfCoreClaims2C μ m φ (fuel + 1) ∧ WhnfClaims2C μ m φ (fuel + 1) ∧
      DefEqClaims2C μ m φ (fuel + 1) ∧ InferClaims2C μ m φ (fuel + 1)

/-- The hoisted induction. -/
theorem checkSound2C {μ : CheckMode} {env : Env}
    (hstep : CheckStep2C μ V) (m : EnvS2UM V μ env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2C μ m φ fuel ∧ WhnfClaims2C μ m φ fuel ∧
        DefEqClaims2C μ m φ fuel ∧ InferClaims2C μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δa h
      rw [Setlec.whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δa h
      rw [Setlec.whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δa h
      rw [Setlec.isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δa h
      rw [Setlec.inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

/-! ## The routed quarters, hoisted -/

/-- The inference quarter. -/
def InferStep2C (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2C μ m φ fuel → WhnfClaims2C μ m φ fuel →
    DefEqClaims2C μ m φ fuel → InferClaims2C μ m φ fuel →
    InferClaims2C μ m φ (fuel + 1)

/-- The head-normalisation quarter. -/
def WhnfCoreStep2C (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2C μ m φ fuel → WhnfClaims2C μ m φ fuel →
    DefEqClaims2C μ m φ fuel → InferClaims2C μ m φ fuel →
    WhnfCoreClaims2C μ m φ (fuel + 1)

/-- The reduction loop. -/
def WhnfStep2C (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2C μ m φ fuel → WhnfClaims2C μ m φ fuel →
    DefEqClaims2C μ m φ fuel → InferClaims2C μ m φ fuel →
    WhnfClaims2C μ m φ (fuel + 1)

/-- The definitional-equality quarter. -/
def DefEqStep2C (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2C μ m φ fuel → WhnfClaims2C μ m φ fuel →
    DefEqClaims2C μ m φ fuel → InferClaims2C μ m φ fuel →
    DefEqClaims2C μ m φ (fuel + 1)

/-- **The hoisted assembly.** -/
theorem checkStep2C_of {μ : CheckMode} {V : Type w} [SetTheory V]
    (hwc : WhnfCoreStep2C μ V) (hw : WhnfStep2C μ V)
    (hd : DefEqStep2C μ V) (hi : InferStep2C μ V) :
    CheckStep2C μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact ⟨hwc env m φ fuel h1 h2 h3 h4, hw env m φ fuel h1 h2 h3 h4,
    hd env m φ fuel h1 h2 h3 h4, hi env m φ fuel h1 h2 h3 h4⟩

/-! ## Direction of the change, recorded

Each claim's `AnnotOk2` **premises** became stronger hypotheses
(ρ-uniform rather than ρ-local), so each claim is **weaker**: producers
have less to prove and consumers have less to use.  The two claims that
also *deliver* an `AnnotOk2` (`Whnf*` and `Infer`) deliver it in the
ρ-uniform form, which is stronger on the output side.

Net: the reduction and inference quarters owe *more* at their
conclusions and are owed *more* at their hypotheses; the defeq quarter
is purely relieved.  That asymmetry is the whole point — it is what
lets a congruence site hand `CtxOk2.openCong` the ρ-uniform pair it
provably cannot get any other way.
-/

end Setlec.SetR.Interp2
