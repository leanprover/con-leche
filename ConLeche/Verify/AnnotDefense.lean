import Lech.Kernel.TypeChecker

/-!
# The defensive validation sites, as a named statement (task #161, P3)

The P2 seal recorded a finding: the three *defensive* sort-annotation
sites — `(defeq-forall)`, `(defeq-lam)`, `(eta)` — appear unreachable
through the spec knot, because every path to `defeqStep`'s structural
binder arms and to `etaCert`'s comparison first infers both compared
expressions (`proofIrrel` runs before them, with no monadic
short-circuit), the front door validates every binder an infer walks,
and two annotations valid for level-equivalent codomain sorts are
equal (`PropWhen.eq_iff_holds`: the datum is canonical).

The coordinator's ruling promotes the finding to a **theorem
candidate** with a decide-by-proof mandate: *every expr reaching
defeq's binder arms has front-door-validated metas — prove it or keep
the defense forever; either outcome is fine, but decide by proof, not
assumption.*  `DefensiveSitesQuiet` below is that statement, in the
observable shape the finding was tested in (P2's countermodel
attempts): on inputs whose inference succeeds, `isDefEqCore` never
declines at a defensive site.

Status: **statement only** — no proof and no refutation is claimed
here.  Whichever way it resolves, the checks stay in the kernel: the
checker never trusts (the invariants-over-runtime-gates ruling is
about proof *hypotheses*, not about dropping validation).
-/

namespace Lech

/-- The decline messages of the three defensive sites, exactly as
`defeqStep`'s binder arms and `etaCert` throw them (`Kernel/Core.lean`,
task #161 P2).  A drift between these strings and the kernel's would
make `DefensiveSitesQuiet` vacuously easier, and the proof attempt is
what would catch it. -/
def defensiveSiteMsgs : List String :=
  ["sort-annotation mismatch (defeq-forall)",
   "sort-annotation mismatch (defeq-lam)",
   "sort-annotation mismatch (eta)"]

/-- **The defensive-sites invariant** (see the module docstring): on
inputs whose inference succeeds — the front door has validated every
binder either side carries — a definitional-equality run never
declines at a defensive sort-annotation site. -/
def DefensiveSitesQuiet (μ : CheckMode) (env : Env) : Prop :=
  ∀ (fuelI fuelD d : Nat) (a b ta tb : Expr),
    inferTypeCore μ env fuelI d a = .ok ta →
    inferTypeCore μ env fuelI d b = .ok tb →
    ∀ msg ∈ defensiveSiteMsgs,
      isDefEqCore μ env fuelD d a b ≠ .error (.notImplemented msg)

end Lech
