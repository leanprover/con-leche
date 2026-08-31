import Setlec.SetR.Annot.EnvS2U
import Setlec.SetR.Interp2.Skeleton
import Setlec.SetR.Annot.SimSubst
import Setlec.SetR.Bridge.Claims
import Setlec.SetR.Annot.SortCoh

/-!
# `Claims2` — the run-level claims over `interp2` (migration step 3)

The statement seal.  `Bridge/Claims.lean`'s four claims restated in the
**annotated** currency: `denote2` instead of `denote`, `AnnotOk2`
instead of nothing, `interp2` conclusions instead of relation
derivations.

## Why these are claims about *runs*, not about the relation

Step 3's map settled this and it is worth having at the top of the
file that depends on it.  One might expect step 3 to restate
`Sound/*`'s five motives with `interp → interp2`.  **That cannot be
written.**  The motives quantify `VExpr` (`RedS (Δ : List VExpr)
(v w : VExpr)`), the relations of `Rel.lean` quantify `VExpr`, and so
the mutual recursor's motives must; but `interp2` is over `AVExpr`.
Bridging needs a `VExpr → AVExpr` map and there is none **by design**:
`Annotates` is a relation (a term has many annotations — WALL 3), and
`denote2` is a function but from `Expr`.  A bare `VExpr` has no
canonical annotation.

So the annotations follow the *run*, exactly as the architecture record
ruled: each claim takes the checker's own run, produces the annotated
twin `denote2` computes for it, and concludes in `interp2`.  The
per-former rows of `Interp2/Skeleton.lean` are what a discharge
composes; `Sound/*` is never translated and stays serving the collapse
lane.

## Two simplifications the annotated currency buys

* **No `∃ T'` slack.**  `InferClaimsR` concludes "some `T'` with
  `Infer … T'` and `DefEq … T' tv`", because an on-the-nose inference
  claim cannot serve a binder congruence.  Here the conclusion is
  *semantic* — a membership — and `DefEq` slack is absorbed by
  `DefEqClaims2`'s own equality, so the claim concludes directly at the
  inferred type's annotation.
* **The context correspondence is reused, not re-invented.**  The
  hypothesis side stays `CtxOkR` at the *erasures* (`Δa.map erase`),
  which is a function of the annotated context — no new relation, and
  no appeal to `Annotates`, whose many-annotations problem is what R1
  removed.  `denote2_erase` is what makes the two sides line up.

## Pre-build supplier check

Every field of every claim, and every input a discharge will consume,
with its supplier.  Nothing here is a wish.

| ingredient | supplier | status |
|---|---|---|
| `denote2`, `denote2_erase` | `Annot/Canon.lean` | landed |
| `AnnotOk2` + clauses + subst pair | `Annot/Ok2.lean` | landed |
| the ten per-former rows | `Interp2/Skeleton.lean` | landed |
| β / ζ / redex-fits steps | `Ok2.lean`, `Spine2.lean` | landed |
| `bval2_mem_type` | `Interp2/BasisOk.lean` | landed |
| `acval` + its three fields | `Annot/EnvS2.lean` | landed |
| `Sat2`, `Sat2_cons` | `Annot/EnvS2.lean` | landed |
| `CtxOkR` and its plumbing | `SetR/CtxOkR.lean` | landed |
| the fuel-zero throws | `Verify/Knot.lean` | landed |
| `SortSubstStable` (v3 β) | `Annot/SimSubst.lean` | **frozen**, here |
| the two zip obligations | `SortCoh/Discharge` | **frozen, Θ** |
| `denote2` fuel-invariance | `knotFuelMono` | **scheduled** |
| the fired iota law over `interp2` | — | **named slot** |

**The `EnvS` seam is closed by containment.**  `SortSubstStable` takes
`mS : EnvS V env` — the collapse-lane invariant, which the earlier
ledger flagged as needing re-signing.  It does not: `EnvS2` holds an
`EnvS` in its `base` field, so `m.base` supplies it verbatim.  The
ledger entry is discharged by the scaffolding that was already there.

**The named slot is `RecRulesV2`, and it is deliberately not stated
here.**  `declStepS` installs inductives, so the spine passes through
iota, so a discharge needs the fired law over `interp2`.  By the T5
rule that premise belongs to its *supplier* — the iota bottoms, when
they migrate — and writing it consumer-side first is the near-miss the
campaign has ruled against.  `Step2Inputs` therefore carries it as an
opaque `Prop` parameter, exactly as `Skeleton.sound_const` carried its
absence until `BConst.type2` and `bval2_mem_type` existed.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name inferTypeCore whnf whnfCore
  isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The four claims -/

/-- Head normalization (no delta) preserves the annotated
interpretation and transports truthfulness forward.  `WhnfCoreClaimsR`
in the annotated currency. -/
def WhnfCoreClaims2 (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {ea : AVExpr},
      denote2 μ m.acval env φ fuel d e = some ea →
      ∃ ea', denote2 μ m.acval env φ fuel d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea' ∧
          (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea')

/-- The reduction loop, ditto. -/
def WhnfClaims2 (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∀ {ea : AVExpr},
      denote2 μ m.acval env φ fuel d e = some ea →
      ∃ ea', denote2 μ m.acval env φ fuel d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea' ∧
          (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea')

/-- A positive definitional-equality verdict is an `interp2` equality.
Unconditional in truthfulness, exactly as `DeqS` is — the grading that
lets `symm`/`trans` and the binder congruences stay one-liners. -/
def DefEqClaims2 (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) a →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) b →
    ∀ {aa ba : AVExpr},
      denote2 μ m.acval env φ fuel d a = some aa →
      denote2 μ m.acval env φ fuel d b = some ba →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- Successful inference: the subject's annotated twin is truthful and
inhabits its type's annotated interpretation.  **No `∃ T'` slack** —
see the module docstring. -/
def InferClaims2 (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e →
    ∃ ea ta,
      denote2 μ m.acval env φ fuel d e = some ea ∧
      denote2 μ m.acval env φ fuel d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-! ## The induction -/

/-- The step of the mutual fuel induction: the four claims at
`fuel + 1` from the four at `fuel`.  `CheckStepR`'s analogue, and
hypothesis-first for the same reason — the `succ` case is the
clause-by-clause work of the batches. -/
def CheckStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    WhnfCoreClaims2 μ m φ (fuel + 1) ∧ WhnfClaims2 μ m φ (fuel + 1) ∧
      DefEqClaims2 μ m φ (fuel + 1) ∧ InferClaims2 μ m φ (fuel + 1)

/-- **The mutual induction.**  Transpose of `checkSoundR`; only the
step is outstanding, and its `zero` case is closed here because every
fuel-zero spelling throws. -/
theorem checkSound2 {μ : CheckMode} {env : Env}
    (hstep : CheckStep2 μ V) (m : EnvS2UM V μ env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2 μ m φ fuel ∧ WhnfClaims2 μ m φ fuel ∧
        DefEqClaims2 μ m φ fuel ∧ InferClaims2 μ m φ fuel := by
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

/-! ## The discharge's named inputs

What a proof of `CheckStep2` will consume beyond the landed
machinery — stated as a bundle so the ledger is mechanical rather than
prose.  Three kinds, and the kind is the point:

* **frozen on the Θ lane** — the two zip obligations.  Named here as
  themselves, *not* as the fifteen-hypothesis shells: the discharge
  tier already reduces both public claims to one obligation each
  (`ensureSortAgreeRQ_of_zip`, `sortOfAgreeRQ_of_zip`), so naming the
  shells would over-state what the consumer needs;
* **frozen with its consumer here** — `SortSubstStable`, whose `EnvS`
  parameter `EnvS2.base` supplies;
* **the named slot** — `recRules2`, an opaque `Prop`, because the fired
  modeled-iota law over `interp2` must be stated by the iota bottoms
  when they migrate (the T5 rule), never guessed at the consumer. -/
structure Step2Inputs (V : Type w) [SetTheory V] (μ : CheckMode)
    (env : Env) (φ : Name → Nat) (recRules2 : Prop) : Prop where
  /-- the v3 β premise's stability metatheorem (`Annot/SimSubst.lean`);
  its `EnvS` argument is `EnvS2.base` -/
  subst_stable : SortSubstStable V
  /-- the Θ lane's whnf-side summit obligation, at any pair slot -/
  zip_whnf : ∀ Q, ZipWhnfSortAgree μ env φ Q
  /-- the Θ lane's type-side summit obligation, at any pair slot -/
  zip_sortOf : ∀ Q, ZipSortOfAgree μ env φ Q
  /-- cross-fuel determinism of the knot, which `denote2`'s
  fuel-invariance rides (supplier landed: `knotFuelMono`) -/
  infer_fuel_det : InferFuelDet μ env
  /-- **the named slot**: the fired modeled-iota law over `interp2`,
  to be stated by the migrating iota bottoms -/
  rec_rules2 : recRules2

end Setlec.SetR.Interp2
