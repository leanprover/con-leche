import Setlec.SetR.Interp2.Step2.Fuel
import Setlec.SetR.Interp2.Step2.Dispatch

/-!
# `Claims2`, amended — the four repairs (migration step 3, seal 6)

The sealed `Claims2` (`Interp2/Claims2.lean`) is **refuted**: four
independent discharges found four defects in it, one of them
mechanically (`inferClaims2_one_refuted`, and `CheckStep2` false with
it).  This file is the amendment.  The refuted originals stay where
they are as the tombstone — a shape nobody should re-seal — and this
file carries the shapes the quarters actually proved.

## The four repairs

**R1 — the annotation's fuel is quantified independently.**  The
sealed claims read the subject through `denote2 … fuel …`, the *same*
numeral indexing the checker call; the knot decrements it, so a
recursing clause had to move a `denote2` fact down, which
`denote2_fuelDown_false` proves impossible.  Here `F` is its own
binder.  Harmless downstream because **`denote2_fuelMono` is a
theorem** (`Step2/Fuel.lean`, from the landed `knotFuelMono`) — any
consumer needing two annotations at one fuel takes the max.  This also
retires `Step2Inputs.infer_fuel_det`'s purpose.

**R2 — the equality is graded**, i.e. inside the `AnnotOk2` premise,
for the two *reduction* claims.  That is what this campaign's own
architecture note said (§"the second soundness — architecture",
*Graded conclusions*) and what the suppliers were built to
(`AnnotOk2_zeta`, `AnnotOk2_beta_pos`, `AnnotOk2_beta_zero` all
conclude `eq ∧ AnnotOk2 ea'` **from** `AnnotOk2 ea`).  β at kind `0` is
where the ungraded form is actually false: off-domain `app` is the
canonical junk `∅`.

`DefEqClaims2A` is left **ungraded**, because that is the shape the
defeq quarter proved (`defeqStep_claim2`, all seven blocks) and because
it is `DeqS`'s grading, which is load-bearing for `symm`/`trans`.
*Evidence over symmetry.*

**R3 — the inference claim's returned type is produced at a larger
fuel.**  `.const` and `.fvar` neither recurse (which would pay for the
returned type's annotation with a run) nor return a run-free shape:
they return a type `inferBody` merely *reads*, whose `denote2` is a
knot computation.  So the claim takes the subject's annotation at any
`F` and produces the type's at some `F' ≥ F`; `denote2_fuelMono` lifts
the subject to `F'`, so both are available together.

**R4 — WITHDRAWN on this branch (the R4 spike).**  Seal 6 added
`μ.verified = true` to all four claims to fix an apparent granularity
mismatch: `denote2`'s λ clause calls `lamSortE` per λ *node* while
`inferBody` runs the #152 codomain check once per λ *chain* and only
at `mode.verified`.  R1/R3 dissolved that mismatch — the λ node's
`lamSortE` is a hypothesis, and `lamSortE_runs` reads its own
`inferTypeCore`/`sortOfE` runs back out of it, so *the annotation
pass never consults the checker's #152 check at all*.  The premise
was thereafter consumed only to pass to the induction hypothesis,
which needed it only because the claims carried it.  Deleting it from
all four claims here costs nothing: every occurrence in the four
quarters was a binder or an argument, no tactic changed, and the
claims — hence `checkSound2B_of_quarters` — are now mode-generic
again, so the `.noModel` lane is back.

## The acceptance test (run, recorded)

The amendment's acceptance criterion was that the mechanized `False`
witness must no longer be derivable.  Checked explicitly: the
refutation `inferClaims2_one_refuted` was transplanted verbatim onto
`InferClaims2A`, with its two now-hypothetical inputs (the context and
the subject's annotation, both at `F = 1`) supplied as hypotheses so
that the *only* question left is whether its final step still closes.
It does not:

```
error: Tactic `rewrite` failed: Did not find an occurrence of
  denote2 ?μ ?acval ?env ?φ 1 ?d (Expr.forallE ?n ?ty ?body ?mb)
in the target expression
  denote2 μ m.acval env φ F' 0 (Expr.forallE n' ty' body' mb') = some ta
```

That is R3 doing exactly its job and nothing more: the returned type's
annotation is now produced at a fuel the *prover* chooses, so
`denote2_one_forallE` — which speaks only at fuel `1` — no longer
applies.  The refuter cannot force `F' = 1`.  And the repair is not
merely evasive: `denote2_two_forallE` shows the missing annotation does
exist one fuel up, which is why `F' > F` is the right slack and not a
loophole.

## The context hypothesis, deliberately not uniform

`InferClaims2A` takes `CtxOk2` (`Step2/Dispatch.lean`) — the annotated
currency — because the `.fvar` clause **reads** the context and needs
both definedness and the leaf-to-entry link, neither of which
`CtxOkR`-on-erasures gives (seal 3).  The other three keep
`CtxOkR`-on-erasures, because that is what their discharges used and
they only *thread* the context.  Making it uniform would be invention;
the asymmetry is the evidence.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name inferTypeCore whnf whnfCore
  isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Head normalisation: fuel-free annotation, graded conclusion. -/
def WhnfCoreClaims2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- The reduction loop, ditto. -/
def WhnfClaims2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {F : Nat} {ea : AVExpr},
      denote2 μ m.acval env φ F d e = some ea →
      ∃ ea', denote2 μ m.acval env φ F d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea →
          interp2 V ρ ea = interp2 V ρ ea' ∧ AnnotOk2 V ρ ea'

/-- Definitional equality: fuel-free annotation, **ungraded** — the
shape the quarter proved and `DeqS`'s grading. -/
def DefEqClaims2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {F : Nat} {aa ba : AVExpr},
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- Inference: `CtxOk2` for the context, subject's annotation at any
`F`, the returned type's at some `F' ≥ F`. -/
def InferClaims2A (μ : CheckMode) {env : Env} (m : EnvS2U V env)
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
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The amended step. -/
def CheckStep2A (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2A μ m φ fuel → WhnfClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfCoreClaims2A μ m φ (fuel + 1) ∧ WhnfClaims2A μ m φ (fuel + 1) ∧
      DefEqClaims2A μ m φ (fuel + 1) ∧ InferClaims2A μ m φ (fuel + 1)

/-- The amended induction; `zero` closes as before. -/
theorem checkSound2A {μ : CheckMode} {env : Env}
    (hstep : CheckStep2A μ V) (m : EnvS2U V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2A μ m φ fuel ∧ WhnfClaims2A μ m φ fuel ∧
        DefEqClaims2A μ m φ fuel ∧ InferClaims2A μ m φ fuel := by
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

/-! ## The routed quarters, amended

`Routed.lean`'s four Props, re-pointed.  The quarters' discharges
migrate onto these; the sealed `*Step2` stay until the last one has
moved, and go with `Claims2.lean`.
-/

/-- The inference quarter, amended. -/
def InferStep2A (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2A μ m φ fuel → WhnfClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    InferClaims2A μ m φ (fuel + 1)

/-- The head-normalisation quarter, amended. -/
def WhnfCoreStep2A (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2A μ m φ fuel → WhnfClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfCoreClaims2A μ m φ (fuel + 1)

/-- The reduction loop, amended. -/
def WhnfStep2A (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2A μ m φ fuel → WhnfClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    WhnfClaims2A μ m φ (fuel + 1)

/-- The definitional-equality quarter, amended. -/
def DefEqStep2A (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2A μ m φ fuel → WhnfClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ fuel → InferClaims2A μ m φ fuel →
    DefEqClaims2A μ m φ (fuel + 1)

/-- **The amended assembly.** -/
theorem checkStep2A_of {μ : CheckMode} {V : Type w} [SetTheory V]
    (hwc : WhnfCoreStep2A μ V) (hw : WhnfStep2A μ V)
    (hd : DefEqStep2A μ V) (hi : InferStep2A μ V) :
    CheckStep2A μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact ⟨hwc env m φ fuel h1 h2 h3 h4, hw env m φ fuel h1 h2 h3 h4,
    hd env m φ fuel h1 h2 h3 h4, hi env m φ fuel h1 h2 h3 h4⟩

end Setlec.SetR.Interp2
