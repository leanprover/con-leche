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
    -- the β site's own run facts
    ∀ {ta : Expr},
    inferTypeCore μ env fuel d a = .ok ta →
    Setlec.isDefEqCore μ env fuel d ta ty = .ok true →
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
    -- the conclusion: numeral agreement at satisfying valuations
    ∀ ρ : Nat → V, Sat V Δv ρ → v = v'

end Setlec.SetR.Interp2
