import Setlec.SetR.Interp2.Claims2A

/-
`Claims2A`, not `EnvS2Refute`: the refutation file imports
`Step2.Whnf`, and the head-normalisation quarter must be able to *name*
`WhnfCoreStep2B`/`WhnfClaims2B` from inside the file that proves them.
`EnvS2Refute` is referenced below only in prose.  (Found by the whnf
quarter, which was blocked by the cycle; the file is otherwise
unchanged.)
-/

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
`InferClaims2A` unchanged,
and `DefEqClaims2A` **superseded by `DefEqClaims2B`** — see STOP 3 at its
definition below.  Its exemption from R2 was reasoned from what defeq
*produces*; the defeq quarter showed the cost is in what it
*consumes*.

## Why the slack composes

Left to right: a chain `e ⟶ e' ⟶ e''` feeds the first link's `(F', ea')`
straight into the second, which returns `F'' ≥ F'`.  Where two
annotations must be held at one fuel — both sides of a `defeq`, or a
subject alongside its inferred type — `denote2_fuelMono`
(`Step2/Fuel.lean`, a theorem) lifts each to `max`, unchanged.  The
slack only ever points *up*, which is why `F ≤ F'` and not an
unconstrained fuel: an unconstrained one would not compose, and a
fixed one is false.

## The R4 spike (this branch only)

R4's `μ.verified = true` has been deleted from all four claims (and
from `DefEqClaims2AP`/`DefEqStepAt2A`/`DefEqStuck2A`, which carried it
in sympathy).  It was pure threading — see the withdrawal note in
`Claims2A.lean`.  The four claims, `CheckStep2B`, `checkSound2B` and
the capstone are therefore mode-generic again, and instantiate at
`.noModel`.
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

/-- **Definitional equality, graded.**  STOP 3: `DefEqClaims2A` was
exempted from R2 on the grounds that defeq *produces* no reduct, so it
needs neither slack nor grading.  That is right about production and
wrong about consumption — `defeqStep`'s **first move** is to `whnfCore`
both sides, which consumes the now-graded reduction claims, and at
those two sites the quarter holds no `AnnotOk2` for either subject and
cannot manufacture one (`denote2` performs no membership check at an
`app` node; the scoping predicates are all syntactic).

The two `AnnotOk2` are **premises**, never conclusions.  So none of
them crosses an equality, and `deqStep2_symm`/`deqStep2_trans`
(`Step2/DefEq.lean`) stay one-liners — which is what the original
exemption was protecting and what it turns out not to have needed. -/
def DefEqClaims2B (μ : CheckMode) {env : Env} (m : EnvS2 V env)
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
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ aa → AnnotOk2 V ρ ba →
        interp2 V ρ aa = interp2 V ρ ba

/-- The corrected step.  `InferClaims2A` is reused verbatim — it was
never refuted and R3 was already its shape.  The defeq slot carries
`DefEqClaims2B` (STOP 3): the induction cannot close with an ungraded
hypothesis and a graded conclusion, so all four claims are uniform. -/
def CheckStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2B μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfCoreClaims2B μ m φ (fuel + 1) ∧ WhnfClaims2B μ m φ (fuel + 1) ∧
      DefEqClaims2B μ m φ (fuel + 1) ∧ InferClaims2A μ m φ (fuel + 1)

/-- The corrected induction. -/
theorem checkSound2B {μ : CheckMode} {env : Env}
    (hstep : CheckStep2B μ V) (m : EnvS2 V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2B μ m φ fuel ∧ WhnfClaims2B μ m φ fuel ∧
        DefEqClaims2B μ m φ fuel ∧ InferClaims2A μ m φ fuel := by
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

/-! ## The routed quarters, corrected -/

/-- The inference quarter. -/
def InferStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2B μ m φ fuel → InferClaims2A μ m φ fuel →
    InferClaims2A μ m φ (fuel + 1)

/-- The head-normalisation quarter. -/
def WhnfCoreStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2B μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfCoreClaims2B μ m φ (fuel + 1)

/-- The reduction loop. -/
def WhnfStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2B μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfClaims2B μ m φ (fuel + 1)

/-- The definitional-equality quarter. -/
def DefEqStep2B (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2B μ m φ fuel → WhnfClaims2B μ m φ fuel →
    DefEqClaims2B μ m φ fuel → InferClaims2A μ m φ fuel →
    DefEqClaims2B μ m φ (fuel + 1)

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
