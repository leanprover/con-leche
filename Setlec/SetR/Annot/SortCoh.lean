import Setlec.SetR.Annot.Canon
import Setlec.Verify.InferLeaves
import Setlec.Verify.BinderLoop

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

/-! ## The ceilinged family — the induction's actual subject

The claims reference each other at **unrelated fuels** (a `(B)` case
about a cert at fuel 3 may consume `(C*)` facts about sort runs at
fuel 10⁶), so no single run's fuel can carry the induction.  The
measure is the **ceiling** `N` — an upper bound on *every* quantified
run fuel — under strong induction: every cross-claim consumption is
about sub-runs at strictly smaller fuels (the knot decrements per
level), so it drops the ceiling; a lazy-delta or whnf *loop* re-entry
keeps every run fuel and decreases only the loop budget, handled by
the loop-internal motive (designed with the first congruence case).
The public claims are the `∀ N` closures (`*_of_at` below). -/

/-- `(A)` at ceiling `N`. -/
def EnsureSortAgreeAt (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (N : Nat) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {ℓ₁ ℓ₂ : Level},
    fc ≤ N → f₁ ≤ N → f₂ ≤ N →
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    whnf μ env f₁ d a = .ok (.sort ℓ₁) →
    whnf μ env f₂ d b = .ok (.sort ℓ₂) →
    ℓ₁.eval φ = ℓ₂.eval φ

/-- `(B)` at ceiling `N`. -/
def SortOfAgreeAt (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (N : Nat) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {u v : Nat},
    fc ≤ N → f₁ ≤ N → f₂ ≤ N →
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    sortOfE μ env φ f₁ d a = some u →
    sortOfE μ env φ f₂ d b = some v →
    u = v

/-- `(C)` at ceiling `N`. -/
def SortOfWhnfCoreStableAt (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (N : Nat) : Prop :=
  ∀ {f d : Nat} {e e' : Expr} {f₁ f₂ : Nat} {u v : Nat},
    f ≤ N → f₁ ≤ N → f₂ ≤ N →
    whnfCore μ env f d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    PairedLeaves e e →
    sortOfE μ env φ f₁ d e = some u →
    sortOfE μ env φ f₂ d e' = some v →
    u = v

/-- `(C-δ)` at ceiling `N` (the unfolding itself is fuel-free; the
sort runs carry the ceiling). -/
def SortOfDeltaStableAt (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (N : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {f₁ f₂ : Nat} {u v : Nat},
    f₁ ≤ N → f₂ ≤ N →
    unfoldDefinition env e = some e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    PairedLeaves e e →
    sortOfE μ env φ f₁ d e = some u →
    sortOfE μ env φ f₂ d e' = some v →
    u = v

/-- `(C*)` at ceiling `N` — the whole-`whnf`-chain composition of
`(C)`/`(C-δ)`, promoted to a first-class family member: the
`proofIrrel` Prop-branch's vacuity consumes exactly this (a subject
whose type both whnfs to a literal sort *and* is `Prop`-sorted would
contradict its own chain — DESIGN, defeq-branch corrections). -/
def SortOfWhnfStableAt (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (N : Nat) : Prop :=
  ∀ {f d : Nat} {e e' : Expr} {f₁ f₂ : Nat} {u v : Nat},
    f ≤ N → f₁ ≤ N → f₂ ≤ N →
    whnf μ env f d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    PairedLeaves e e →
    sortOfE μ env φ f₁ d e = some u →
    sortOfE μ env φ f₂ d e' = some v →
    u = v

/-- The bundle the strong induction proves at each ceiling. -/
structure SortCohAt (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (N : Nat) : Prop where
  ensure : EnsureSortAgreeAt μ env φ N
  sortOf : SortOfAgreeAt μ env φ N
  whnfCoreStable : SortOfWhnfCoreStableAt μ env φ N
  deltaStable : SortOfDeltaStableAt μ env φ N
  whnfStable : SortOfWhnfStableAt μ env φ N

/-! The `∀ N` closures give back the public claims (instantiate the
ceiling at the maximum of the run fuels in play). -/

theorem EnsureSortAgreeR_of_at {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (h : ∀ N, SortCohAt μ env φ N) :
    EnsureSortAgreeR μ env φ :=
  fun {fc _ _ _ f₁ f₂ _ _} hc hwa hba hLa hwb hbb hLb hp h₁ h₂ =>
    (h (max fc (max f₁ f₂))).ensure
      (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      hc hwa hba hLa hwb hbb hLb hp h₁ h₂

theorem SortOfAgreeR_of_at {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (h : ∀ N, SortCohAt μ env φ N) :
    SortOfAgreeR μ env φ :=
  fun {fc _ _ _ f₁ f₂ _ _} hc hwa hba hLa hwb hbb hLb hp h₁ h₂ =>
    (h (max fc (max f₁ f₂))).sortOf
      (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      hc hwa hba hLa hwb hbb hLb hp h₁ h₂

theorem SortOfWhnfCoreStableR_of_at {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (h : ∀ N, SortCohAt μ env φ N) :
    SortOfWhnfCoreStableR μ env φ :=
  fun {f _ _ _ f₁ f₂ _ _} hr hw hb hL hp h₁ h₂ =>
    (h (max f (max f₁ f₂))).whnfCoreStable
      (Nat.le_max_left _ _)
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      hr hw hb hL hp h₁ h₂

theorem SortOfDeltaStableR_of_at {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (h : ∀ N, SortCohAt μ env φ N) :
    SortOfDeltaStableR μ env φ :=
  fun {_ _ _ f₁ f₂ _ _} hr hw hb hL hp h₁ h₂ =>
    (h (max f₁ f₂)).deltaStable
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      hr hw hb hL hp h₁ h₂

/-! ## Standalone case ingredients

Everything below is `KnotFuelDet`-powered and independent of the
induction — the base and vacuity material the step consumes. -/

/-- `sortOfE` is cross-fuel deterministic (given the knot is). -/
theorem sortOfE_fuelDet {μ : CheckMode} {env : Env} {φ : Name → Nat}
    (hdet : KnotFuelDet μ env) {f₁ f₂ d : Nat} {e : Expr} {u v : Nat}
    (h₁ : sortOfE μ env φ f₁ d e = some u)
    (h₂ : sortOfE μ env φ f₂ d e = some v) : u = v := by
  unfold sortOfE at h₁ h₂
  cases hi₁ : inferTypeCore μ env f₁ d e with
  | error => rw [hi₁] at h₁; exact nomatch h₁
  | ok t₁ =>
    cases hi₂ : inferTypeCore μ env f₂ d e with
    | error => rw [hi₂] at h₂; exact nomatch h₂
    | ok t₂ =>
      obtain rfl : t₁ = t₂ := hdet.1 hi₁ hi₂
      rw [hi₁] at h₁; rw [hi₂] at h₂
      simp only [Except.toOption] at h₁ h₂
      cases hw₁ : whnf μ env f₁ d t₁ with
      | error => rw [hw₁] at h₁; exact nomatch h₁
      | ok w₁ =>
        cases hw₂ : whnf μ env f₂ d t₁ with
        | error => rw [hw₂] at h₂; exact nomatch h₂
        | ok w₂ =>
          obtain rfl : w₁ = w₂ := hdet.2.1 hw₁ hw₂
          rw [hw₁] at h₁; rw [hw₂] at h₂
          cases w₁ <;> simp_all

/-- An inference on a literal sort can only return its successor
sort (the clause is fuel-free). -/
theorem inferTypeCore_sort_out {μ : CheckMode} {env : Env}
    {f d : Nat} {ℓ : Level} {t : Expr}
    (h : inferTypeCore μ env f d (.sort ℓ) = .ok t) :
    t = .sort (.succ ℓ) := by
  cases f with
  | zero => exact nomatch h
  | succ f =>
    rw [Setlec.inferTypeCore_succ] at h
    simp only [Setlec.inferBody, Setlec.viewM, Setlec.Expr.view,
      Bind.bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at h
    exact h.symm

/-- A `whnf` run on a literal sort returns it (via `whnf_sort` +
cross-fuel determinism). -/
theorem whnf_sort_out {μ : CheckMode} {env : Env}
    (hdet : KnotFuelDet μ env) {f d : Nat} {ℓ : Level} {t : Expr}
    (h : whnf μ env f d (.sort ℓ) = .ok t) : t = .sort ℓ :=
  hdet.2.1 h (Setlec.whnf_sort (mode := μ) env 0 d ℓ)

/-- A successful `sortOfE` on a literal sort computes the successor
numeral — the sort-sort base's arithmetic half. -/
theorem sortOfE_sort_out {μ : CheckMode} {env : Env} {φ : Name → Nat}
    (hdet : KnotFuelDet μ env) {f d : Nat} {ℓ : Level} {u : Nat}
    (h : sortOfE μ env φ f d (.sort ℓ) = some u) :
    u = ℓ.eval φ + 1 := by
  unfold sortOfE at h
  cases hi : inferTypeCore μ env f d (.sort ℓ) with
  | error => rw [hi] at h; exact nomatch h
  | ok t =>
    obtain rfl := inferTypeCore_sort_out hi
    rw [hi] at h
    simp only [Except.toOption] at h
    cases hw : whnf μ env f d (.sort (.succ ℓ)) with
    | error => rw [hw] at h; exact nomatch h
    | ok w =>
      obtain rfl := whnf_sort_out hdet hw
      rw [hw] at h
      simpa [Except.toOption, Level.eval] using h.symm

/-! ## ∃-fuel run facts and the (F) transport species (R3 ruling)

The ceiling measure died on manufactured runs (DESIGN, "STOP: the
ceiling measure fails").  The repair: state side facts **fuel-free**
(`∃ f, run f = …` — functional by `KnotFuelDet`), so they never enter
a measure, and add the missing claim species **(F): forward
transport** — a reduction step plus a successful sort computation on
the redex yields a successful sort computation on the reduct *with
the same numeral*.  (F) is the sort-level fragment of subject
reduction this arc has been circling — the campaign's original
prognosis ("a narrow, level-data-only fragment of SR") given its
precise formal identity.  The stratified measure audit that makes the
family well-founded is the DESIGN "audit under R3" record. -/

/-- A successful sort computation at some fuel — fuel-free
(functional by `KnotFuelDet`, `SortOfEE_det`). -/
def SortOfEE (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (d : Nat) (e : Expr) (u : Nat) : Prop :=
  ∃ f, sortOfE μ env φ f d e = some u

/-- A certified conversion at some fuel — the v3 premise's shape. -/
def DefEqE (μ : CheckMode) (env : Env) (d : Nat) (a b : Expr) : Prop :=
  ∃ f, isDefEqCore μ env f d a b = .ok true

theorem SortOfEE_det {μ : CheckMode} {env : Env} {φ : Name → Nat}
    (hdet : KnotFuelDet μ env) {d : Nat} {e : Expr} {u v : Nat}
    (h₁ : SortOfEE μ env φ d e u) (h₂ : SortOfEE μ env φ d e v) :
    u = v := by
  obtain ⟨f₁, h₁⟩ := h₁
  obtain ⟨f₂, h₂⟩ := h₂
  exact sortOfE_fuelDet hdet h₁ h₂

/-- **(F-core)**: one head-normalization step transports the sort
computation forward, numeral intact.  The β case is the substitution
pairing in constructive form (the walk on the substituted body is
*built* from the opened walk plus the site's own cert pieces — the
correspondence travels as cert runs, never as sort agreements). -/
def SortTransportWhnfCoreF (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {f d : Nat} {e e' : Expr} {u : Nat},
    whnfCore μ env f d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → PairedLeaves e e →
    SortOfEE μ env φ d e u → SortOfEE μ env φ d e' u

/-- **(F-δ)**: one definition unfolding transports the sort
computation forward — threading the *install-time* cert (the value
was checked against the declared type when the definition entered the
env). -/
def SortTransportDeltaF (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {u : Nat},
    unfoldDefinition env e = some e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → PairedLeaves e e →
    SortOfEE μ env φ d e u → SortOfEE μ env φ d e' u

/-- **(F-nat)**: one literal-acceleration step — expected vacuous
(the subjects are `Nat` elements, whose type never whnfs to a sort),
but stated as transport so the loop assembly is uniform. -/
def SortTransportNatF (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {f d : Nat} {e e' : Expr} {u : Nat},
    Setlec.reduceNat (Setlec.pureFns μ env f) env d e = .ok (some e') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → PairedLeaves e e →
    SortOfEE μ env φ d e u → SortOfEE μ env φ d e' u

/-- **(C\*-E)**: the whole-`whnf`-chain transport, ∃-fuel spelling —
assembled from the three step species by `whnf`-loop induction
(stratum S2); supersedes `SortOfWhnfStableAt`'s role, which stays as
a dual-success corollary (compose with `SortOfEE_det`). -/
def SortTransportWhnfF (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {f d : Nat} {e e' : Expr} {u : Nat},
    whnf μ env f d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e → PairedLeaves e e →
    SortOfEE μ env φ d e u → SortOfEE μ env φ d e' u

/-! ## Repair δ: the chain-link correspondence and the (A-T) primitive

The pairing's correspondence invariant carries **chain-links** — a
conditional, ∃-fuel convergence fact — instead of cert runs, and the
site certs are consumed *at the leaves* through the transport form of
(A).  Dual-success (A) becomes a corollary (`EnsureSortAgreeR_of_link`
below); the internal fueled forms and the joint measure
(lexicographic on (Σ knot fuels, Σ loop budgets) of fueled
hypotheses) are the DESIGN "J0" record. -/

/-- **The chain-link**: if the left type whnf-converges to a literal
sort, the right one does too, with the same numeral.  The ∃-fuel
*output* form the correspondence carries (repair δ: outputs are
fuel-free, so links never enter a measure). -/
def SortLinkE (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (d : Nat) (t t' : Expr) : Prop :=
  ∀ {f : Nat} {ℓ : Level}, whnf μ env f d t = .ok (.sort ℓ) →
    ∃ f' ℓ', whnf μ env f' d t' = .ok (.sort ℓ') ∧
      ℓ'.eval φ = ℓ.eval φ

/-- **(A-T), the family's true primitive**: a certified conversion
*transports* whnf-to-sort success across itself, numeral intact.
Consumed at the pairing's leaves (site cert + the opened side's
chain) and by the `proofIrrel`/eta vacuities (det-collision of the
constructed run with the probe's own run). -/
def SortLinkAcrossCertE (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {fc d : Nat} {a b : Expr},
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    SortLinkE μ env φ d a b

/-- Dual-success (A) is a corollary of the transport primitive: link
the left run across the cert, then collide with the given right run
(`KnotFuelDet`).  The statement-level consistency check that (A-T)
is stated strong enough. -/
theorem EnsureSortAgreeR_of_link {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (hdet : KnotFuelDet μ env)
    (hAT : SortLinkAcrossCertE μ env φ) :
    EnsureSortAgreeR μ env φ := by
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwa hba hLa hwb hbb hLb hp h₁ h₂
  obtain ⟨f', ℓ', hw', hev⟩ :=
    hAT hc hwa hba hLa hwb hbb hLb hp h₁
  have hs : Expr.sort ℓ' = Expr.sort ℓ₂ := hdet.2.1 hw' h₂
  obtain rfl : ℓ' = ℓ₂ := Setlec.Expr.sort.inj hs
  exact hev.symm

/-- **The unit-like vacuity pattern**: a subject cannot both have a
unit-like type (the `proofIrrel`/rescue branch's certifying run) and
a sort-successful run (whose type whnfs to a literal sort) — the two
whnf outputs are one output, and a `.sort` is not const-headed. -/
theorem unitBranch_absurd {μ : CheckMode} {env : Env}
    (hdet : KnotFuelDet μ env) {d fa fw fa' fw' : Nat}
    {a ta ta' tw : Expr} {ℓ : Level}
    (h1 : inferTypeCore μ env fa d a = .ok ta)
    (h2 : whnf μ env fw d ta = .ok tw)
    (hu : Setlec.isUnitLikeTy env tw = true)
    (h3 : inferTypeCore μ env fa' d a = .ok ta')
    (h4 : whnf μ env fw' d ta' = .ok (.sort ℓ)) : False := by
  obtain rfl : ta = ta' := hdet.1 h1 h3
  obtain rfl : tw = .sort ℓ := hdet.2.1 h2 h4
  exact nomatch hu

end Setlec.SetR.Interp2
