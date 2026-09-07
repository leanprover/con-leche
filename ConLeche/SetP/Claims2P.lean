import Lech.Verify.InferLeaves
import Lech.Semantics.Skeleton
import Lech.SetP.Annot.ValidV
import Lech.SetP.Annot.EnvS2Core

/-!
# The P-generation claims: the ladder over `denoteP` (task #161, P3.3)

The generation-six claims (`Claims2E.lean`) state the soundness ladder
over `denote2` — the canonical reading, whose binder numerals are
checker runs.  This file states the same ladder over **`denoteP`**,
the validated-annotation reading.  The deltas, uniformly:

* `denote2 μ m.acval env φ F d e` becomes `denoteP m.acval env φ d e`
  — the annotation fuels `F`/`F'` vanish (there is no run to pay
  for), taking with them the whole fuel-mediation surface
  (`denote2_fuelMono`, the `∃ F' ≥ F` slack, `CtxOk2`'s fuel
  parameter);
* the truthfulness currency is `AnnotOkP := AnnotOk2 ∧ AnnotValidV`:
  the hereditary invariant plus bit validity — the claims *establish*
  the regime bits they dispatch on, clause by clause, from the run
  inversions (never from a validity metatheorem — the refuted
  `ValidInfer` shape stays off the table);
* the context discipline is `CtxOkP`, `CtxOk2D`'s package with the
  historical `CtxOk2`/`CtxOk2Ann` split merged (fresh file, no
  compatibility constraint) and the leaf truthfulness upgraded to
  `AnnotOkP`.

The **dual-success** shape is kept verbatim: every `denoteP` sits in
a premise, never a conclusion, so the smallest-fuel refutation rule
has nothing to bite on — same structural reasoning as the E-tier's
frozen-text check.  (`denoteP` is *more* total than `denote2` — no
sort runs can fail — so success premises may later be dischargeable
outright; that is an upgrade path, not a statement change.)

`checkSound2P` closes the induction generically, exactly as
`checkSound2E`: the zero case is the checker's own zero-fuel throw,
untouched by the currency swap.

**Residue transformation (the P3.3 ledger, to be paid clause by
clause in the step proof):** where the E-tier step assembly consumes
sort-run residues, the P-tier consumes the P2 validation sites'
run-inversion conjuncts instead —

| E-tier residue | P-tier replacement |
|---|---|
| `BinderSortAgree2` (residue 9) | the `(defeq-forall)`/`(defeq-lam)` arm inversions: `==` ⇒ equal data ⇒ equal bits, and bits are canonical in `{0,1}` |
| `LamCodSort2` | the λ front door: leaf case delivered by `inferTypeCore_lam_inv`'s conjunct + `pwBit_zero_mem_univZero`; chain case by `piR_zero_mem_univZero` (impredicativity, no run) |
| `SortOfEInstLevels`/`LamSortEInstLevels` | `denotePInstLevels` — proved, unconditional, exact |
| `SortAgree` (env crossing) | dropped: `denoteP_envExtend` needs `FindPreserved`/`LitGuardsAgree` only |
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.Verify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- The P-tier truthfulness currency: hereditary truthfulness plus
bit validity. -/
def AnnotOkP (V : Type w) [SetTheory V] (ρ : Nat → V) (e : AVExpr) :
    Prop :=
  AnnotOk2 V ρ e ∧ AnnotValidV V ρ e

/-- The P-tier context discipline: `CtxOk2D`'s package over `denoteP`
— scope bound, leaf types annotate, their interpretations read the
telescope, and they are `AnnotOkP` under every satisfying valuation.
No fuel parameter. -/
def CtxOkP {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (d : Nat) (Δa : List AVExpr) (e : Expr) : Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2 ∧
    ∃ tya Aa,
      denoteP m.acval env φ d l.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ tya)

/-- Head normalisation, dual success, P currency. -/
def WhnfCoreClaims2P (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      denoteP m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- The reduction loop, dual success, P currency. -/
def WhnfClaims2P (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      denoteP m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- Definitional equality, P currency. -/
def DefEqClaims2P (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Lech.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a →
      CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ ba

/-- Inference, dual success, P currency: the subject's and the
type's truthfulness — bit validity included — are *conclusions*. -/
def InferClaims2P (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      denoteP m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The P-generation step. -/
def CheckStep2P (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2Core V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2P μ m φ fuel → WhnfClaims2P μ m φ fuel →
    DefEqClaims2P μ m φ fuel → InferClaims2P μ m φ fuel →
    WhnfCoreClaims2P μ m φ (fuel + 1) ∧ WhnfClaims2P μ m φ (fuel + 1) ∧
      DefEqClaims2P μ m φ (fuel + 1) ∧ InferClaims2P μ m φ (fuel + 1)

/-- The P-generation induction: generic in the step, zero case from
the checker's own zero-fuel throws (currency-independent). -/
theorem checkSound2P {μ : CheckMode} {env : Env}
    (hstep : CheckStep2P μ V) (m : EnvS2Core V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2P μ m φ fuel ∧ WhnfClaims2P μ m φ fuel ∧
        DefEqClaims2P μ m φ fuel ∧ InferClaims2P μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δa h
      rw [Lech.whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δa h
      rw [Lech.whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δa h
      rw [Lech.isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δa h
      rw [Lech.inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

end Lech.SetP
