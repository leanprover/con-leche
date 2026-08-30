import Setlec.SetR.Interp2.EnvS2Refute

/-!
# `Claims2`, corrected — R1 and R3 unified (migration step 3, seal 7)

Lineage, so the reader can see what happened rather than only where it
landed:

* `Interp2/Claims2.lean` — the original seal.  **Refuted**
  (`inferClaims2_one_refuted`).
* `Interp2/Claims2A.lean` — seal 6's amendment, four repairs.  Its
  inference claim was right; its two *reduction* claims were still
  wrong.  **Refuted** (`whnfClaims2A_delta_refuted`).
* `Interp2/EnvS2Refute.lean` — both witnesses, plus the three that
  kill `EnvS2` itself.
* this file — the reduction claims in R3's shape, which is the shape
  the whole family should have had from the start.

## The one change from `Claims2A`

`WhnfCoreClaims2B`/`WhnfClaims2B` produce the reduct's annotation at a
fuel `F' ≥ F` of the *prover's* choosing, exactly as `InferClaims2A`
produces the inferred type's.  Seal 6 freed the annotation fuel from
the run's fuel (R1) but then pinned the reduct to the subject's fuel,
and reduction can produce a term that needs more fuel to annotate than
the subject did — the delta exit turns a `.const` leaf, which
annotates at fuel `1`, into a `λ` body, which does not.

Everything else stands: the grading by `AnnotOk2` of the subject (R2),
the `μ.verified = true` quantifier (R4), `InferClaims2A` unchanged,
and `DefEqClaims2A` unchanged and *ungraded* — it produces no reduct,
so it needs no slack, and `DeqS`'s grading is load-bearing for
`symm`/`trans`.

## Why the slack composes

Left to right: a chain `e ⟶ e' ⟶ e''` feeds the first link's `(F', ea')`
straight into the second, which returns `F'' ≥ F'`.  Where two
annotations must be held at one fuel — both sides of a `defeq`, or a
subject alongside its inferred type — `denote2_fuelMono`
(`Step2/Fuel.lean`, a theorem) lifts each to `max`, unchanged.  The
slack only ever points *up*, which is why `F ≤ F'` and not an
unconstrained fuel: an unconstrained one would not compose, and a
fixed one is false.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name whnf whnfCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Head normalisation, corrected: the reduct annotates at some
`F' ≥ F`. -/
def WhnfCoreClaims2B (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    μ.verified = true →
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- The reduction loop, corrected. -/
def WhnfClaims2B (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    μ.verified = true →
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- The corrected step. `DefEqClaims2A` and `InferClaims2A` are reused
verbatim — neither was refuted. -/
def CheckStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfCoreClaims2B μ m φ (fuel + 1) ∧ WhnfClaims2B μ m φ (fuel + 1) ∧
      DefEqClaims2A μ m φ (fuel + 1) ∧ InferClaims2A μ m φ (fuel + 1)

/-- The corrected induction. -/
theorem checkSound2B {μ : CheckMode} {env : Env}
    (hstep : CheckStep2B μ V) (m : EnvS2 V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2B μ m φ fuel ∧ WhnfClaims2B μ m φ fuel ∧
        DefEqClaims2A μ m φ fuel ∧ InferClaims2A μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δa _ h
      rw [Setlec.whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δa _ h
      rw [Setlec.whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δa _ h
      rw [Setlec.isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δa _ h
      rw [Setlec.inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

/-! ## The routed quarters, corrected -/

/-- The inference quarter. -/
def InferStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    InferClaims2A μ m φ (fuel + 1)

/-- The head-normalisation quarter. -/
def WhnfCoreStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfCoreClaims2B μ m φ (fuel + 1)

/-- The reduction loop. -/
def WhnfStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfClaims2B μ m φ (fuel + 1)

/-- The definitional-equality quarter. -/
def DefEqStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ (fuel + 1)

/-- **The corrected assembly.** -/
theorem checkStep2B_of {μ : CheckMode} {V : Type w} [SetTheory V]
    (hwc : WhnfCoreStep2B μ V) (hw : WhnfStep2B μ V)
    (hd : DefEqStep2B μ V) (hi : InferStep2B μ V) :
    CheckStep2B μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact ⟨hwc env m φ fuel h1 h2 h3 h4, hw env m φ fuel h1 h2 h3 h4,
    hd env m φ fuel h1 h2 h3 h4, hi env m φ fuel h1 h2 h3 h4⟩

/-! ## The acceptance test, this time with a hunt for a second witness

Seal 6 shipped with one acceptance test — the witness the amendment
was built from — and the statement was still false.  So this seal
records **both** known witnesses as tests, and the rule that produced
the second one.

1. `inferClaims2_one_refuted`'s construction: dead against
   `InferClaims2A` since seal 6 (checked, recorded there).
2. `whnfClaims2A_delta_refuted`'s construction: it demands the reduct
   at the subject's own fuel, and `WhnfCoreClaims2B`/`WhnfClaims2B`
   no longer offer that — the reduct's fuel is existential.

The generative rule behind both: **a claim that quantifies a fuel is
false at the smallest fuel unless every term it asserts a `denote2`
success for is a leaf.**  Seal 6's reduction claims asserted success
for the *reduct*, which is not a leaf.  `EnvS2.acval_defn` asserted it
for a definition's *body*, which is not a leaf either — same rule,
same fuel `1`, found by applying it deliberately rather than by
stumbling on it.
-/

end Setlec.SetR.Interp2
