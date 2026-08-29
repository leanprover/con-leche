import Setlec.SetR.Annot.Canon
import Setlec.SetR.Annot.Kinding
import Setlec.SetR.Annot.EnvS2
import Setlec.SetR.CtxOkR
import Setlec.Verify.InferLeaves

/-!
# The run-level substitution simulation — the STATEMENT (task #151 tier C)

Per the arc's first constraint: the statement alone, sealed before any
case work, stated against its actual consumer and trap-tested first.

## The consumer

`Claims2`'s β-thread needs: at a satisfying valuation, the
interpretation of the *canonical* annotation of the substituted body
agrees with the interpretation of the *descended* annotation
(`ba.inst aa`).  The two agree iff their λ/Π numerals do, so the
consumer-exact statement is **numeral agreement of the checker's sort
computations across its own β-substitution** — and the consumer is
semantic, so the agreement needs to hold **only under a satisfying
valuation**.

## The traps, tested against the quantifier pattern

* **Fuel** — the substituted run might need different fuel.  Defused
  by the hypothesis pattern: both computations' *successes at one
  fuel* are hypotheses; nothing is claimed where either fails, and no
  fuel monotonicity is consumed.
* **Branch divergence** — `whnf` on the substituted type may reduce
  where the opened one was stuck on the fvar (e.g. the substituend is
  a λ and a β fires).  So the conclusion cannot be a
  `substFvar`-image equation between outputs; it is numeral equality,
  reached through the relation's `DefEq` join of the two reduction
  paths.
* **Unsatisfiable contexts** — the relation can conceivably relate
  distinct sorts at an inconsistent context (no confluence theorem
  exists, deliberately), so *unconditional* numeral equality is not
  the right statement.  Defused by the consumer: `Claims2`'s
  conclusions are `Sat`-conditioned, so the statement concludes under
  `Sat V Δ ρ` — where `sort_rigid` closes the sort leg.
* **The open proof risk, named for the case work** (not a statement
  issue): linking a *synthetic* substituted derivation (M2's output)
  to the substituted *run*'s own derivation compares two independent
  `Infer` trees, which is uniqueness-of-inference ground.  The case
  work must keep both sides run-backed (the simulation invariant
  relates runs to runs, with the relation's `DefEq` only as the
  join), or the hostile ground resurfaces — the arc's STOP condition.
* **Supplier circularity, and the currency ladder** (two refutation
  seals — DESIGN, "REFUTATION"/"SECOND REFUTATION"): the β premise as
  first sealed was the site's *run cert* — supplier-committed, since
  rank 2 removes those walks.  Two successive semantic weakenings both
  fell to one countermodel family (sort-blind carriers: unit-likes at
  `Prop` and `Type 1` sharing `{pt}`): *membership* pins the element,
  not the type; *type-level interp equality* pins the carrier, not
  the sort.  The *relational* form dies at `DefEq.trans`'s runless
  middle.  The surviving currency is **v3**: existence of a
  certifying defeq *run* — run-shaped yet supplier-swappable (phase
  one: the site's cert via `betaCert_discharge` + `InferFuelDet`;
  phase two: the primary typing walk's app-site verdict, which is
  typing itself and never removed).  The countermodel is excluded
  because the checker *rejects* its pair: equal shadows, no
  certifying run.

## Determinism, stated early

The run-level route's free lemma: the checker is a function, so two
facts about one run are facts about one output.  Trivial and
load-bearing — every place the relation-level route needed uniqueness
of inference, the run-level route rewrites with these.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR
open Setlec (CheckMode Env Expr Name inferTypeCore whnf)

/-! ## Determinism -/

theorem inferTypeCore_det {mode : CheckMode} {env : Env}
    {fuel d : Nat} {e t t' : Expr}
    (h : inferTypeCore mode env fuel d e = .ok t)
    (h' : inferTypeCore mode env fuel d e = .ok t') : t = t' := by
  rw [h] at h'
  exact Except.ok.inj h'

theorem whnf_det {mode : CheckMode} {env : Env} {fuel d : Nat}
    {e t t' : Expr}
    (h : whnf mode env fuel d e = .ok t)
    (h' : whnf mode env fuel d e = .ok t') : t = t' := by
  rw [h] at h'
  exact Except.ok.inj h'

theorem sortOfE_det {mode : CheckMode} {env : Env} {φ : Name → Nat}
    {fuel d : Nat} {e : Expr} {v v' : Nat}
    (h : sortOfE mode env φ fuel d e = some v)
    (h' : sortOfE mode env φ fuel d e = some v') : v = v' := by
  rw [h] at h'
  exact Option.some.inj h'

theorem lamSortE_det {mode : CheckMode} {env : Env} {φ : Name → Nat}
    {fuel d : Nat} {e : Expr} {v v' : Nat}
    (h : lamSortE mode env φ fuel d e = some v)
    (h' : lamSortE mode env φ fuel d e = some v') : v = v' := by
  rw [h] at h'
  exact Option.some.inj h'

/-! ## The statement -/

/-- **The substitution-stability statement** (the arc's target,
consumer-exact).  Over an environment carrying the invariant, at the
verified mode: if the checker's β-argument check accepted `a` against
the opener's annotation (`hcert` — the run fact every β site has), and
the sort computation succeeded on the opened body *and* on the
substituted one, then the two sorts agree **at every satisfying
valuation of the (denoted) context**.

`Δv` is the denoted context the runs were bridged at; the syntactic
guards are the bridge-standard set.  The conclusion's `Sat`
conditioning is the trap-tested quantifier decision (module
docstring): the consumer is semantic, and unconditional agreement is
not claimed at inconsistent contexts. -/
def SortSubstStable (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {env : Env} (mS : EnvS V env) (φ : Name → Nat)
    {fuel d : Nat} {n : Name} {ty body a : Expr} {Δv : List VExpr}
    {v v' : Nat},
    μ.verified = true →
    -- the two sort computations, both successful at one fuel
    lamSortE μ env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some v →
    lamSortE μ env φ fuel d (body.instantiate1 a) = some v' →
    -- the bridge-standard syntactic guards on the participants
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) →
    (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) →
    -- the context correspondence at the site
    CtxOkR μ mS.cval env φ d Δv a →
    CtxOkR μ mS.cval env φ d Δv ty →
    ∀ {tyv : VExpr}, denote mS.cval env φ d ty = some tyv →
    ∀ {av : VExpr}, denote mS.cval env φ d a = some av →
    -- **the β premise, v3** (the surviving rung of the currency
    -- ladder — DESIGN, "SECOND REFUTATION"): every inferred type of
    -- the argument is run-certified convertible to the domain.
    -- Run-shaped yet supplier-swappable: phase one supplies the β
    -- site's own cert (`betaCert_discharge` below, via
    -- fuel-determinism); phase two supplies the primary typing
    -- walk's app-site verdict — typing itself, never removed.  The
    -- semantic rungs below this one (membership, type-level interp
    -- equality) are refuted by the sort-blind-carrier countermodel;
    -- the relational rung dies at `DefEq.trans`'s runless middle.
    (∀ (fuel' : Nat) {ta : Expr},
      inferTypeCore μ env fuel' d a = .ok ta →
        ∃ fuelc, Setlec.isDefEqCore μ env fuelc d ta ty = .ok true) →
    -- the conclusion: numeral agreement at satisfying valuations
    ∀ ρ : Nat → V, Sat V Δv ρ → v = v'

/-- **Cross-fuel determinism of inference**, named as the explicit
hypothesis the phase-one discharge carries until the knot's
fuel-monotonicity induction lands (carried-obligations ledger; the
`CheckStepR` precedent — hypothesize the step, prove it in batches).
The banked `inferTypeCore_det` above is *same-fuel only*; this is new
work, clean because `Setlec/Kernel/Core.lean` contains no
tryCatch/orElse — the bodies never backtrack through errors. -/
def InferFuelDet (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f₁ f₂ d : Nat} {e t₁ t₂ : Expr},
    inferTypeCore μ env f₁ d e = .ok t₁ →
    inferTypeCore μ env f₂ d e = .ok t₂ → t₁ = t₂

/-- **The current checker's discharge of the v3 β premise**: the run
cert every β site has today — the argument's inference and the domain
`defeq` at the site's own fuel — supplies "every inferred type of the
argument is run-certified convertible to the domain", with
`InferFuelDet` linking the site's `ta` to the arbitrary-fuel one.
Purely syntactic: the semantic machinery of the earlier (refuted)
discharge chains is gone with the rungs it served.  This is the
phase-one supplier; the phase-two supplier is the primary typing
walk's app-site verdict — rank 2 retires this lemma's use at gated
sites, never the premise. -/
theorem betaCert_discharge {μ : CheckMode} {env : Env}
    {fuel d : Nat} {ty a ta : Expr}
    (hdet : InferFuelDet μ env)
    (hinf : inferTypeCore μ env fuel d a = .ok ta)
    (hdefeq : Setlec.isDefEqCore μ env fuel d ta ty = .ok true) :
    ∀ (fuel' : Nat) {ta' : Expr},
      inferTypeCore μ env fuel' d a = .ok ta' →
        ∃ fuelc, Setlec.isDefEqCore μ env fuelc d ta' ty = .ok true := by
  intro fuel' ta' hinf'
  obtain rfl : ta' = ta := hdet hinf' hinf
  exact ⟨fuel, hdefeq⟩

end Setlec.SetR.Interp2
