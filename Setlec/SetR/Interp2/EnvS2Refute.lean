import Setlec.SetR.Interp2.Claims2A
import Setlec.SetR.Interp2.Step2.Whnf

/-!
# STOP — `EnvS2` is unsatisfiable at every realistic environment

`EnvS2.acval_defn` and `EnvS2.acval_thm` are **equations demanding
success, universally quantified over the annotation fuel**:

```
acval_defn : ∀ μ φ fuel cv value hint,
  .defnInfo cv value hint ∈ env.consts →
  denote2 μ acval env φ fuel 0 value = some (acval cv.name φ)
```

`fuel = 1` is admitted, and `denote2` at fuel `1` returns `none` on
every `λ` and every `∀` (`denote2_one_lam`, `denote2_one_forallE`:
the binder clauses call `lamSortE`/`sortOfE`, which need a `whnf` run
and so cannot return at fuel `1`).  So the field is false as soon as
the environment stores **one definition whose body is a `λ`** — that
is, essentially every environment past `Env.empty`.

`EnvS2.empty` is not evidence against this: its `env.consts = []`
makes both fields vacuous.  This is the same masking that hid the
`InferClaims2` defect — *the one witness in the landed set had no
constants in it.*

## Consequence

The migration item "swap the fourteen's conclusion from
`Nonempty (EnvS V env')` to `Nonempty (EnvS2 V env')`" is **not
merely unproved, it is unprovable** while these two fields keep this
shape.  No amount of work in the install layer can produce an `EnvS2`
for an environment with a λ-bodied definition in it.

## The repair, and why it is a weakening that costs nothing

`Loop.lean`'s `whnfStep2_delta`/`whnfStep2_delta_thm` are the only
consumers, and what the delta exit actually needs is *uniqueness*, not
*existence at every fuel*: given that the unfolded body annotates at
all, that annotation must be the constant's own leaf.  Stated as an
implication the field is satisfiable — vacuous at the low fuels where
`denote2` cannot return, contentful where it can:

```
acval_defn : ... → ∀ {ea}, denote2 μ acval env φ fuel 0 value = some ea
  → ea = acval cv.name φ
```

Existence is then supplied where it is genuinely available, at a fuel
the *prover* picks — which is exactly repair R3's shape in
`Claims2A.lean`, arrived at independently here.

## A second, matching defect in `Claims2A` itself

The same argument refutes `WhnfClaims2A` (and `WhnfCoreClaims2A`):
repair R1 freed the annotation fuel `F` but still demands the
**reduct's** annotation at that same `F`, and reduction can produce a
term needing more fuel than the subject did — the delta exit turns a
`.const` leaf (annotates at fuel `1`) into a `λ` body (does not).
`whnfClaims2A_delta_refuted` below is the conditional witness.

So the reduction claims need R3's treatment too: the reduct's
annotation at some `F' ≥ F`, with `denote2_fuelMono` carrying the
subject's own annotation up to `F'` unchanged so composition still
works.  *R1 and R3 are one repair, and applying it to three of the
four claims and not the fourth was the mistake.*
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name Level BinderMeta ConstantInfo
  ConstantVal ReducibilityHint whnf)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {φ : Name → Nat}

/-- **`EnvS2` has no λ-bodied definitions.**  Unconditional: no run,
no annotation hypothesis, no choice of `V`. -/
theorem envS2_defn_lam_refuted {env : Env} (m : EnvS2 V env)
    (μ : CheckMode) (φ : Name → Nat)
    {cv : ConstantVal} {n : Name} {ty body : Expr} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv (.lam n ty body mb) hint
      ∈ env.consts) : False := by
  have h := m.acval_defn μ φ 1 cv (.lam n ty body mb) hint hc
  rw [denote2_one_lam] at h
  exact nomatch h

/-- Ditto for `∀`-bodied definitions (a type abbreviation). -/
theorem envS2_defn_pi_refuted {env : Env} (m : EnvS2 V env)
    (μ : CheckMode) (φ : Name → Nat)
    {cv : ConstantVal} {n : Name} {ty body : Expr} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv (.forallE n ty body mb) hint
      ∈ env.consts) : False := by
  have h := m.acval_defn μ φ 1 cv (.forallE n ty body mb) hint hc
  rw [denote2_one_forallE] at h
  exact nomatch h

/-- Ditto for a theorem whose proof term is a `λ` — i.e. the proof of
any implication or any universally quantified statement. -/
theorem envS2_thm_lam_refuted {env : Env} (m : EnvS2 V env)
    (μ : CheckMode) (φ : Name → Nat)
    {cv : ConstantVal} {n : Name} {ty body : Expr} {mb : BinderMeta}
    (hc : ConstantInfo.thmInfo cv (.lam n ty body mb)
      ∈ env.consts) : False := by
  have h := m.acval_thm μ φ 1 cv (.lam n ty body mb) hc
  rw [denote2_one_lam] at h
  exact nomatch h

/-- **The matching defect in the amended reduction claim.**  Whenever
`whnf` takes its delta exit from a constant to a `λ`-shaped body, and
the constant annotates at fuel `1` (leaves do), `WhnfClaims2A` demands
the reduct's annotation at fuel `1` too — which `denote2_one_lam`
denies.  Conditional only on the run and the subject's annotation,
both of which any real environment supplies. -/
theorem whnfClaims2A_delta_refuted {env : Env} (m : EnvS2 V env)
    {fuel d : Nat} {e : Expr} {Δa : List AVExpr} {ea : AVExpr}
    {n : Name} {ty body : Expr} {mb : BinderMeta}
    (hv : μ.verified = true)
    (hrun : whnf μ env fuel d e = .ok (.lam n ty body mb))
    (hsc : Expr.WScoped d e) (hlb : e.looseBVarsBounded 0 = true)
    (hlv : Expr.LeavesBounded e)
    (hctx : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e)
    (hea : denote2 μ m.acval env φ 1 d e = some ea) :
    ¬ WhnfClaims2A μ m φ fuel := by
  intro hclaim
  obtain ⟨ea', hea', -⟩ :=
    hclaim hv hrun hsc hlb hlv hctx hea
  rw [denote2_one_lam] at hea'
  exact nomatch hea'

end Setlec.SetR.Interp2
