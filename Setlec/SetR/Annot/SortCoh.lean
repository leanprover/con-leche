import Setlec.SetR.Annot.Canon
import Setlec.Verify.InferLeaves

/-!
# Run-level sort coherence — the defeq-branch claim family (task #151 tier C)

The load-bearing branch of the substitution-simulation arc: **"a true
defeq verdict plus sort-computation runs on both arguments forces
numeral agreement."**  Stated alone before any case work, per the
arc's discipline; the DESIGN "defeq-branch" record carries the case
map of `defeqStep` these claims were trap-tested against.

## The centerpiece: valuation-freedom

Unlike every semantic statement of this lane, the claims below never
mention `V`, `interp`, `Sat` or a valuation.  The `Sat`-conditioning
of `SortSubstStable` was forced by *relation*-level pathologies (the
family has no confluence theorem, so derivations may relate distinct
sorts at inconsistent contexts).  The *runs* have no such freedom: the
checker never certifies `.sort u ≡ .sort v` except through the ground
level comparison, and every other certifying path reduces to it
structurally or is vacuous (a subject whose `sortOfE` succeeds has a
type that whnfs to a literal sort, which no proof, element, function
or literal has).  Run-level sort coherence is pure syntax and
arithmetic — which is also what lets the whole file live `V`-free.

## The traps, tested against the quantifier pattern

* **Two independent fuel scales** — the certifying run's fuel and the
  sort runs' fuels are unrelated, and the sort runs' *own* sub-facts
  live at decremented fuels (a `sortOfE` at `f` contains infer/whnf
  sub-runs at `f - k`).  So every run is quantified at its own fuel,
  and all same-syntax links go through `KnotFuelDet` — the ledger's
  cross-fuel determinism obligation, knot-wide form.  (This also
  retires the "identical fuels" discipline: nothing here requires the
  consumer to align fuels.)
* **The `fvar` annotation divergence** — the congruence cases open
  binders with *each side's own* domain (`.fvar depth n₁ ty₁` vs
  `.fvar depth n₂ ty₂`), so inside a paired descent the two sides'
  annotations at an index agree only *up to the domain sub-cert*.
  The statement-level guard is the ambient discipline
  (`PairedLeaves`: one annotation per index across both sides — the
  consumer has it syntactically, since a walk opens each index once);
  the induction's internal motive generalizes it to a paired zone
  carrying, per opened index, the annotation pair, its certifying
  sub-run, and the induction-grade agreement fact — extended at every
  congruence descent from the domain IH (DESIGN, "the Θ motive").
* **The mutual knot is real** — `(C)`'s β case is
  `SortSubstStable`-shaped (redex type vs substituted-body type) and
  `SortSubstStable`'s leaf is `(B)`-shaped (the certified
  `ta`/`ty` pair), exactly the granted three-branch decomposition:
  one mutual induction, sealed at knot-natural boundaries.
* **Vacuity is load-bearing, not free** — proof-irrelevance, K,
  unit-like, eta and literal paths certify only subjects whose
  `sortOfE` *fails* (their types do not whnf to sorts), but proving
  each vacuity crosses the two fuel scales, i.e. consumes
  `KnotFuelDet`.

## STOP condition (the arc's, instantiated)

If any certifying path of `defeqStep` genuinely equates subjects
whose sort runs disagree — a defeq rule certifying across a sort
boundary — that is the finding of the whole arc; seal it with the
case.  The expectation from the same-carrier backbone is that none
does, and proving that is what this branch *is*.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

/-! ## The cross-fuel determinism obligation, knot-wide -/

/-- **Cross-fuel determinism of the knot** (the carried-obligations
ledger entry, knot-wide form; `InferFuelDet` is its first
projection).  Success at any two fuels is the same success — clean
because the core bodies never catch errors, mechanical by
oracle-extension induction over `coreKnot`; its own seal.  Until that
lands, every consumer here carries it as this named hypothesis (the
`CheckStepR` precedent).  `annotate` is deliberately omitted: no sort
computation consults it. -/
def KnotFuelDet (μ : CheckMode) (env : Env) : Prop :=
  (∀ {f₁ f₂ d : Nat} {e t₁ t₂ : Expr},
    inferTypeCore μ env f₁ d e = .ok t₁ →
    inferTypeCore μ env f₂ d e = .ok t₂ → t₁ = t₂) ∧
  (∀ {f₁ f₂ d : Nat} {e t₁ t₂ : Expr},
    whnf μ env f₁ d e = .ok t₁ →
    whnf μ env f₂ d e = .ok t₂ → t₁ = t₂) ∧
  (∀ {f₁ f₂ d : Nat} {e t₁ t₂ : Expr},
    whnfCore μ env f₁ d e = .ok t₁ →
    whnfCore μ env f₂ d e = .ok t₂ → t₁ = t₂) ∧
  (∀ {f₁ f₂ d : Nat} {a b : Expr} {v₁ v₂ : Bool},
    isDefEqCore μ env f₁ d a b = .ok v₁ →
    isDefEqCore μ env f₂ d a b = .ok v₂ → v₁ = v₂)

/-! ## The ambient leaf discipline -/

/-- **One annotation per index, across both sides.**  The syntactic
form of a walk's opening discipline: every `fvar` leaf with a given
index carries the same type annotation, on either side.  The consumer
has this because a walk opens each index exactly once
(`Expr.LeafCond`'s shape, paired); the congruence descent inside the
induction weakens it to the Θ motive — see the module docstring. -/
def PairedLeaves (a b : Expr) : Prop :=
  ∀ l ∈ a.fvarLeaves ++ b.fvarLeaves,
    ∀ l' ∈ a.fvarLeaves ++ b.fvarLeaves,
      l.1 = l'.1 → l.2.2 = l'.2.2

/-! ## The claim family

All claims take the bridge-standard syntactic guards on their
subjects; `μ` and `φ` are arbitrary (the sort computations are
mode-blind in their outputs — the verified-mode extra walks gate
success, never shape it — and levels are ground so `φ` only
evaluates). -/

/-- **(A) `ensureSort` agreement**: a certified pair whose members
both whnf to literal sorts has equal numerals.  The `fvar` leaf's
workhorse (annotations are compared through their whnf-sorts), and
the base the sort-sort case of the run bottoms out in. -/
def EnsureSortAgreeR (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {ℓ₁ ℓ₂ : Level},
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    whnf μ env f₁ d a = .ok (.sort ℓ₁) →
    whnf μ env f₂ d b = .ok (.sort ℓ₂) →
    ℓ₁.eval φ = ℓ₂.eval φ

/-- **(B) `sortOfE` agreement** — the branch's target, stated against
its actual consumer (`SortSubstStable`'s leaf: the certified
`ta`/`ty` pair): a certified pair on which both sort computations
succeed has equal numerals.  Unconditional — no valuation (module
docstring). -/
def SortOfAgreeR (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {u v : Nat},
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    sortOfE μ env φ f₁ d a = some u →
    sortOfE μ env φ f₂ d b = some v →
    u = v

/-- **(C) whnfCore-step stability**: the sort of the type survives a
head-normalization step.  One-sided (no pairing) — the supplier for
every rewrite-and-reenter path of `defeqStep` (and the whnfCore
branch of the granted decomposition; its β case is where
`SortSubstStable`'s machinery re-enters the knot). -/
def SortOfWhnfCoreStableR (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {f d : Nat} {e e' : Expr} {f₁ f₂ : Nat} {u v : Nat},
    whnfCore μ env f d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    PairedLeaves e e →
    sortOfE μ env φ f₁ d e = some u →
    sortOfE μ env φ f₂ d e' = some v →
    u = v

/-- **(C-δ) delta-step stability**: the sort of the type survives one
definition unfolding — the lazy-delta paths' supplier, threaded from
the *install-time* cert (the definition's value was checked against
its declared type when it entered the env; DESIGN names this the
install-threading unknown). -/
def SortOfDeltaStableR (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {f₁ f₂ : Nat} {u v : Nat},
    unfoldDefinition env e = some e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    PairedLeaves e e →
    sortOfE μ env φ f₁ d e = some u →
    sortOfE μ env φ f₂ d e' = some v →
    u = v

end Setlec.SetR.Interp2
