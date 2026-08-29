import Setlec.SetR.Annot.Canon
import Setlec.SetR.Annot.Kinding
import Setlec.SetR.Annot.EnvS2
import Setlec.SetR.CtxOkR
import Setlec.SetR.Bridge.Claims
import Setlec.SetR.Sound.Main
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
* **Supplier circularity** (the refinement, post-seal review): the β
  premise as first sealed was the *run cert* — the argument's
  inference plus the domain `defeq` — which is exactly the pair of
  walks rank 2 removes.  Not circular (two-phase structure: migration
  proves the current checker, removal re-proves gated cases), but
  phase two would have needed a variant theorem.  Refined to the
  **semantic form**: the argument's interpretation is a member of the
  domain's interpretation at satisfying valuations.  Today's supplier
  is the run cert, discharged by `betaCert_discharge` below
  (claims-bridge → soundness → membership); the post-removal supplier
  is the invariant's slot package (`AnnotOk2_redex_fits`).  One
  theorem, both phases; the supplier swaps under it.

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
open SetTheory

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
    -- **the β premise, semantic form** (supplier-neutral): the
    -- argument inhabits the opener's domain at satisfying valuations.
    -- Today's supplier is the run cert (`betaCert_discharge` below);
    -- the post-removal supplier is the invariant's slot package
    -- (`AnnotOk2_redex_fits`/`graded_beta_pos`).  One theorem, both
    -- phases; the supplier swaps under it.
    (∀ ρ : Nat → V, Sat V Δv ρ → interp V ρ av ∈ˢ interp V ρ tyv) →
    -- the conclusion: numeral agreement at satisfying valuations
    ∀ ρ : Nat → V, Sat V Δv ρ → v = v'

/-- **The current checker's discharge of the semantic β premise**: the
run cert every β site has today — the argument's inference and the
domain `defeq` — bridged and sounded, yields the membership.  This is
the phase-one supplier; rank 2's removal retires this lemma's use at
gated sites, never the premise. -/
theorem betaCert_discharge {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvR env)
    (φ : Name → Nat) {fuel : Nat}
    (henv : EnvSHyp V env m.cval φ)
    (ihd : DefEqClaimsR μ m φ fuel) (ihi : InferClaimsR μ m φ fuel)
    {d : Nat} {ty a ta : Expr} {Δv : List VExpr}
    (hinf : inferTypeCore μ env fuel d a = .ok ta)
    (hdefeq : Setlec.isDefEqCore μ env fuel d ta ty = .ok true)
    (hwsa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwst : Expr.WScoped d ty) (hbt : ty.looseBVarsBounded 0 = true)
    (hLt : Expr.LeavesBounded ty)
    (hCa : CtxOkR μ m.cval env φ d Δv a)
    (hCt : CtxOkR μ m.cval env φ d Δv ty)
    {tyv : VExpr} (hty : denote m.cval env φ d ty = some tyv)
    {av : VExpr} (hav : denote m.cval env φ d a = some av) :
    ∀ ρ : Nat → V, Sat V Δv ρ → interp V ρ av ∈ˢ interp V ρ tyv := by
  intro ρ hρ
  -- bridge the inference run
  obtain ⟨av', tav, hav', htav, T', hIT', hDT'⟩ :=
    ihi hinf hwsa hba hLa hCa
  obtain rfl : av = av' := by
    rw [hav] at hav'
    exact Option.some.inj hav'
  -- the inferred type's own guards, for the defeq run
  have hwsta : Expr.WScoped d ta :=
    Setlec.inferTypeCore_WScoped m.wf fuel hinf hwsa
  have hbta : ta.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars m.wf fuel hinf hwsa hba hLa
  have hLta : Expr.LeavesBounded ta := fun l hl =>
    hLa l (Setlec.inferTypeCore_fvarLeaves m.wf fuel hinf hwsa l hl)
  have hCta : CtxOkR μ m.cval env φ d Δv ta :=
    CtxOkR.of_subset
      (fun l hl => Setlec.inferTypeCore_fvarLeaves m.wf fuel hinf hwsa l hl)
      hCa
  -- bridge the defeq run
  have hD := ihd hdefeq hwsta hbta hLta hwst hbt hLt hCta hCt htav hty
  -- sound both: the membership transports along the equality chain
  have hmem := (Infer.sound henv hIT' ρ hρ).2
  have h1 := DefEq.sound henv hDT' ρ hρ
  have h2 := DefEq.sound henv hD ρ hρ
  rw [h1, h2] at hmem
  exact hmem

end Setlec.SetR.Interp2
