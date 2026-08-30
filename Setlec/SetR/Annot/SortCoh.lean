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

/-! ## The run algebra — loop decomposition and assembly

The (A-T) induction's first ingredient batch.  Decomposition reads a
given `whnf` run apart at its first step (aligning it with the cert
loop's own `whnfCore` by determinism); assembly builds `whnf` runs
from pieces (the probe/eta vacuities construct the colliding run).
Assembly is why the ledger obligation must be **monotonicity**, not
determinism: pieces from different runs live at different knot
fuels, and gluing them into one loop needs every sub-call at one
`r` — lift all pieces to the maximum.  Determinism is monotonicity's
corollary (`KnotFuelDet_of_mono`). -/

/-- **Cross-fuel monotonicity of the knot** — the carried-obligations
ledger entry, corrected shape (supersedes carrying `KnotFuelDet`
directly; determinism follows).  Success at a fuel is success at
every larger fuel, same output.  `reduceNat` is included because the
assembly lemmas glue its runs across knot levels too. -/
def KnotFuelMono (μ : CheckMode) (env : Env) : Prop :=
  (∀ {f f' d : Nat} {e t : Expr}, f ≤ f' →
    inferTypeCore μ env f d e = .ok t →
    inferTypeCore μ env f' d e = .ok t) ∧
  (∀ {f f' d : Nat} {e t : Expr}, f ≤ f' →
    whnf μ env f d e = .ok t → whnf μ env f' d e = .ok t) ∧
  (∀ {f f' d : Nat} {e t : Expr}, f ≤ f' →
    whnfCore μ env f d e = .ok t → whnfCore μ env f' d e = .ok t) ∧
  (∀ {f f' d : Nat} {a b : Expr} {v : Bool}, f ≤ f' →
    isDefEqCore μ env f d a b = .ok v →
    isDefEqCore μ env f' d a b = .ok v) ∧
  (∀ {f f' d : Nat} {e : Expr} {o : Option Expr}, f ≤ f' →
    Setlec.reduceNat (Setlec.pureFns μ env f) env d e = .ok o →
    Setlec.reduceNat (Setlec.pureFns μ env f') env d e = .ok o)

/-- Determinism is monotonicity's corollary: lift both runs to the
maximum fuel and read them off each other. -/
theorem KnotFuelDet_of_mono {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) : KnotFuelDet μ env := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f₁ f₂ d e t₁ t₂ h₁ h₂
    have g₁ := hm.1 (Nat.le_max_left f₁ f₂) h₁
    have g₂ := hm.1 (Nat.le_max_right f₁ f₂) h₂
    rw [g₁] at g₂; exact Except.ok.inj g₂
  · intro f₁ f₂ d e t₁ t₂ h₁ h₂
    have g₁ := hm.2.1 (Nat.le_max_left f₁ f₂) h₁
    have g₂ := hm.2.1 (Nat.le_max_right f₁ f₂) h₂
    rw [g₁] at g₂; exact Except.ok.inj g₂
  · intro f₁ f₂ d e t₁ t₂ h₁ h₂
    have g₁ := hm.2.2.1 (Nat.le_max_left f₁ f₂) h₁
    have g₂ := hm.2.2.1 (Nat.le_max_right f₁ f₂) h₂
    rw [g₁] at g₂; exact Except.ok.inj g₂
  · intro f₁ f₂ d a b v₁ v₂ h₁ h₂
    have g₁ := hm.2.2.2.1 (Nat.le_max_left f₁ f₂) h₁
    have g₂ := hm.2.2.2.1 (Nat.le_max_right f₁ f₂) h₂
    rw [g₁] at g₂; exact Except.ok.inj g₂

/-- Decompose one reduction-loop step of a successful run. -/
theorem whnfStep_decompose {env : Env} {r : Setlec.CoreFns Setlec.CheckM}
    {d : Nat} {k : Expr → Setlec.CheckM Expr} {e s : Expr}
    (h : Setlec.whnfStep r env d k e = .ok s) :
    ∃ e₁, r.whnfCore d e = .ok e₁ ∧
      ((∃ e₂, Setlec.reduceNat r env d e₁ = .ok (some e₂) ∧
          k e₂ = .ok s) ∨
       (Setlec.reduceNat r env d e₁ = .ok none ∧
         ∃ e₂, Setlec.unfoldDefinition env e₁ = some e₂ ∧
           k e₂ = .ok s) ∨
       (Setlec.reduceNat r env d e₁ = .ok none ∧
         Setlec.unfoldDefinition env e₁ = none ∧ s = e₁)) := by
  unfold Setlec.whnfStep at h
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · next e₁ hwc =>
    split at h
    · exact nomatch h
    · next o hrn =>
      match o, h with
      | some e₂, h => exact ⟨e₁, hwc, .inl ⟨e₂, hrn, h⟩⟩
      | none, h =>
        cases hud : Setlec.unfoldDefinition env e₁ with
        | some e₂ =>
          rw [hud] at h
          exact ⟨e₁, hwc, .inr (.inl ⟨hrn, e₂, hud, h⟩)⟩
        | none =>
          rw [hud] at h
          exact ⟨e₁, hwc, .inr (.inr ⟨hrn, hud,
            (Except.ok.inj h).symm⟩)⟩

/-- Assemble a step from a literal-acceleration continuation. -/
theorem whnfStep_assemble_nat {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat}
    {k : Expr → Setlec.CheckM Expr} {e e₁ e₂ s : Expr}
    (hwc : r.whnfCore d e = .ok e₁)
    (hrn : Setlec.reduceNat r env d e₁ = .ok (some e₂))
    (hk : k e₂ = .ok s) :
    Setlec.whnfStep r env d k e = .ok s := by
  unfold Setlec.whnfStep
  simp only [Bind.bind, Except.bind, hwc, hrn]
  exact hk

/-- Assemble a step from an unfolding continuation. -/
theorem whnfStep_assemble_delta {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat}
    {k : Expr → Setlec.CheckM Expr} {e e₁ e₂ s : Expr}
    (hwc : r.whnfCore d e = .ok e₁)
    (hrn : Setlec.reduceNat r env d e₁ = .ok none)
    (hud : Setlec.unfoldDefinition env e₁ = some e₂)
    (hk : k e₂ = .ok s) :
    Setlec.whnfStep r env d k e = .ok s := by
  unfold Setlec.whnfStep
  simp only [Bind.bind, Except.bind, hwc, hrn, hud]
  exact hk

/-- Assemble a terminal (stuck) step. -/
theorem whnfStep_assemble_stuck {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat}
    {k : Expr → Setlec.CheckM Expr} {e e₁ : Expr}
    (hwc : r.whnfCore d e = .ok e₁)
    (hrn : Setlec.reduceNat r env d e₁ = .ok none)
    (hud : Setlec.unfoldDefinition env e₁ = none) :
    Setlec.whnfStep r env d k e = .ok e₁ := by
  unfold Setlec.whnfStep
  simp only [Bind.bind, Except.bind, hwc, hrn, hud]
  rfl

/-- The loop unfolds one step (definitional). -/
theorem whnfLoop_succ {env : Env} {r : Setlec.CoreFns Setlec.CheckM}
    {d l : Nat} {e : Expr} :
    Setlec.whnfLoop r env d (l + 1) e =
      Setlec.whnfStep r env d (Setlec.whnfLoop r env d l) e := rfl

/-- The defeq loop unfolds one step (definitional). -/
theorem defeqLoop_succ {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d l : Nat} {a b : Expr} :
    Setlec.defeqLoop μ r env d (l + 1) a b =
      Setlec.defeqStep μ r env d (Setlec.defeqLoop μ r env d l) a b := rfl

/-- **Loop-budget monotonicity** — provable without any obligation:
the continuation sits in tail position, so a shorter successful loop
replays inside a longer one. -/
theorem whnfLoop_budget_mono {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} :
    ∀ {l l' : Nat} {e s : Expr}, l ≤ l' →
      Setlec.whnfLoop r env d l e = .ok s →
      Setlec.whnfLoop r env d l' e = .ok s := by
  intro l
  induction l with
  | zero => intro l' e s _ h; exact nomatch h
  | succ l ih =>
    intro l' e s hle h
    obtain ⟨l'', rfl⟩ : ∃ l'', l' = l'' + 1 := ⟨l' - 1, by omega⟩
    rw [whnfLoop_succ] at h
    rw [whnfLoop_succ]
    obtain ⟨e₁, hwc, hrest⟩ := whnfStep_decompose h
    rcases hrest with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact whnfStep_assemble_nat hwc hrn (ih (by omega) hk)
    · exact whnfStep_assemble_delta hwc hrn hud (ih (by omega) hk)
    · exact whnfStep_assemble_stuck hwc hrn hud

/-- Peel a `whnf` run to its loop form (the internal shape the (A-T)
induction speaks). -/
theorem whnf_to_loop {μ : CheckMode} {env : Env} {f d : Nat}
    {e s : Expr} (h : whnf μ env (f + 1) d e = .ok s) :
    Setlec.whnfLoop (Setlec.pureFns μ env f) env d
      Setlec.whnfLoopFuel e = .ok s := h

/-- Wrap a loop run back into a `whnf` run (budget monotonicity into
the loop's own budget). -/
theorem whnf_of_loop {μ : CheckMode} {env : Env} {f d l : Nat}
    {e s : Expr} (hl : l ≤ Setlec.whnfLoopFuel)
    (h : Setlec.whnfLoop (Setlec.pureFns μ env f) env d l e = .ok s) :
    whnf μ env (f + 1) d e = .ok s :=
  whnfLoop_budget_mono hl h

/-! ## The cert-loop decomposition — `defeqStep`'s certifying paths

The machine-checked form of the case map: one constructor per
certifying path of `defeqStep`, on the *post-whnfCore* pair (the
whnfCore facts are stated once, in `defeqStep_decompose`).  The
`rescue` constructor absorbs every `stuckIrrel` fallback site — the
body always passes the case's own scrutinees, i.e. the post-whnfCore
pair verbatim.  Hint/guard data that no consumer reads
(`unfoldableHead`, `headHint`, the string-support guard) is dropped:
constructors are deliberately *weaker* than their branches, which is
sound for a decomposition. -/

inductive PostCoreCert (μ : CheckMode) (env : Env)
    (r : Setlec.CoreFns Setlec.CheckM)
    (k : Expr → Expr → Setlec.CheckM Bool) (d : Nat) :
    Expr → Expr → Prop
  | syn (e : Expr) : PostCoreCert μ env r k d e e
  | irrel (a b : Expr) :
      Setlec.proofIrrel r env d a b = .ok true →
      PostCoreCert μ env r k d a b
  | natL (a b a₂ : Expr) :
      Setlec.reduceNat r env d a = .ok (some a₂) →
      k a₂ b = .ok true → PostCoreCert μ env r k d a b
  | natR (a b b₂ : Expr) :
      Setlec.reduceNat r env d a = .ok none →
      Setlec.reduceNat r env d b = .ok (some b₂) →
      k a b₂ = .ok true → PostCoreCert μ env r k d a b
  | deltaL (a b a₂ : Expr) :
      Setlec.unfoldDefinition env a = some a₂ →
      k a₂ b = .ok true → PostCoreCert μ env r k d a b
  | deltaR (a b b₂ : Expr) :
      Setlec.unfoldDefinition env b = some b₂ →
      k a b₂ = .ok true → PostCoreCert μ env r k d a b
  | deltaB (a b a₂ b₂ : Expr) :
      Setlec.unfoldDefinition env a = some a₂ →
      Setlec.unfoldDefinition env b = some b₂ →
      k a₂ b₂ = .ok true → PostCoreCert μ env r k d a b
  | spine (a b : Expr) :
      Setlec.defeqSpine r env d a b = .ok true →
      PostCoreCert μ env r k d a b
  | sorts (u v : Level) : Level.isEquiv u v = some true →
      PostCoreCert μ env r k d (.sort u) (.sort v)
  | lits (l : Setlec.Literal) :
      PostCoreCert μ env r k d (.lit l) (.lit l)
  | natZeroL : PostCoreCert μ env r k d
      (.lit (.natVal 0)) (.const Setlec.natZeroName [])
  | natZeroR :
      Setlec.unfoldableHead env (.const Setlec.natZeroName []) = false →
      PostCoreCert μ env r k d
        (.const Setlec.natZeroName []) (.lit (.natVal 0))
  | natSuccL (n : Nat) (x : Expr) :
      r.defeq d (.lit (.natVal n)) x = .ok true →
      PostCoreCert μ env r k d (.lit (.natVal (n + 1)))
        (.app (.const Setlec.natSuccName []) x)
  | natSuccR (n : Nat) (x : Expr) :
      Setlec.unfoldableHead env
        (.app (.const Setlec.natSuccName []) x) = false →
      r.defeq d x (.lit (.natVal n)) = .ok true →
      PostCoreCert μ env r k d
        (.app (.const Setlec.natSuccName []) x)
        (.lit (.natVal (n + 1)))
  | strL (st : String) (cO : Name) (usO : List Level) (x : Expr) :
      r.defeq d (Setlec.strLitToConstructor st)
        (.app (.const cO usO) x) = .ok true →
      PostCoreCert μ env r k d (.lit (.strVal st))
        (.app (.const cO usO) x)
  | strR (st : String) (cO : Name) (usO : List Level) (x : Expr) :
      Setlec.unfoldableHead env (.app (.const cO usO) x) = false →
      r.defeq d (.app (.const cO usO) x)
        (Setlec.strLitToConstructor st) = .ok true →
      PostCoreCert μ env r k d (.app (.const cO usO) x)
        (.lit (.strVal st))
  | fvars (i : Nat) (n₁ n₂ : Name) (ty₁ ty₂ : Expr) :
      PostCoreCert μ env r k d (.fvar i n₁ ty₁) (.fvar i n₂ ty₂)
  | consts (n : Name) (us us' : List Level) :
      Setlec.unfoldableHead env (.const n us) = false →
      Level.isEquivList us us' = some true →
      PostCoreCert μ env r k d (.const n us) (.const n us')
  | piCong (n₁ n₂ : Name) (ty₁ ty₂ body₁ body₂ : Expr)
      (m₁ m₂ : Setlec.BinderMeta) :
      r.defeq d ty₁ ty₂ = .ok true →
      r.defeq (d + 1) (body₁.instantiate1 (.fvar d n₁ ty₁))
        (body₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true →
      PostCoreCert μ env r k d (.forallE n₁ ty₁ body₁ m₁)
        (.forallE n₂ ty₂ body₂ m₂)
  | lamCong (n₁ n₂ : Name) (ty₁ ty₂ body₁ body₂ : Expr)
      (m₁ m₂ : Setlec.BinderMeta) :
      r.defeq d ty₁ ty₂ = .ok true →
      r.defeq (d + 1) (body₁.instantiate1 (.fvar d n₁ ty₁))
        (body₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true →
      PostCoreCert μ env r k d (.lam n₁ ty₁ body₁ m₁)
        (.lam n₂ ty₂ body₂ m₂)
  | appCong (f₁ a₁ f₂ a₂ : Expr) :
      Setlec.unfoldableHead env (.app f₁ a₁) = false →
      (Expr.app f₁ a₁).getAppArgs.length =
        (Expr.app f₂ a₂).getAppArgs.length →
      r.defeq d (Expr.app f₁ a₁).getAppFn
        (Expr.app f₂ a₂).getAppFn = .ok true →
      Setlec.defEqList r env d (Expr.app f₁ a₁).getAppArgs
        (Expr.app f₂ a₂).getAppArgs = .ok true →
      PostCoreCert μ env r k d (.app f₁ a₁) (.app f₂ a₂)
  | projCong (s₁ s₂ : Name) (i : Nat) (e₁ e₂ : Expr) :
      r.defeq d e₁ e₂ = .ok true →
      PostCoreCert μ env r k d (.proj s₁ i e₁) (.proj s₂ i e₂)
  | etaL (n₁ : Name) (ty₁ body₁ : Expr) (m₁ : Setlec.BinderMeta)
      (b : Expr) :
      Setlec.etaCert r env d n₁ ty₁ body₁ m₁ b = .ok true →
      PostCoreCert μ env r k d (.lam n₁ ty₁ body₁ m₁) b
  | etaR (a : Expr) (n₂ : Name) (ty₂ body₂ : Expr)
      (m₂ : Setlec.BinderMeta) :
      Setlec.etaCert r env d n₂ ty₂ body₂ m₂ a = .ok true →
      PostCoreCert μ env r k d a (.lam n₂ ty₂ body₂ m₂)
  | rescue (a b : Expr) :
      Setlec.stuckIrrel μ r env d a b = .ok true →
      PostCoreCert μ env r k d a b

/-- **Decompose a certifying `defeqStep`**: either the syntactic fast
path fired, or the post-whnfCore pair certifies by one of the
`PostCoreCert` paths. -/
theorem defeqStep_decompose {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM}
    {k : Expr → Expr → Setlec.CheckM Bool} {d : Nat} {a b : Expr}
    (h : Setlec.defeqStep μ r env d k a b = .ok true) :
    a = b ∨ ∃ a' b',
      r.whnfCore d a = .ok a' ∧ r.whnfCore d b = .ok b' ∧
        PostCoreCert μ env r k d a' b' := by
  unfold Setlec.defeqStep at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · next hab => exact .inl (eq_of_beq hab)
  next hab =>
  split at h
  · exact nomatch h
  next a' hwa =>
  split at h
  · exact nomatch h
  next b' hwb =>
  refine .inr ⟨a', b', hwa, hwb, ?_⟩
  split at h
  · next hab' => obtain rfl := eq_of_beq hab'; exact .syn a'
  next hab' =>
  split at h
  · exact nomatch h
  next c hpi =>
  split at h
  · next hc => exact .irrel a' b' (hc ▸ hpi)
  next hc =>
  split at h
  · exact nomatch h
  next oa hra =>
  split at h
  case _ a₂ =>
    -- literal acceleration, left: the guard must have been live
    split at hra
    · exact .natL a' b' a₂ hra h
    · exact nomatch hra
  split at h
  · exact nomatch h
  next ob hrb =>
  split at h
  case _ b₂ =>
    split at hrb
    · next hg =>
      rw [if_pos hg] at hra
      exact .natR a' b' b₂ hra hrb h
    · exact nomatch hrb
  clear hra hrb
  split at h
  -- (true, false): unfold left
  case _ hua hub =>
    split at h
    · next a₂ hu => exact .deltaL a' b' a₂ hu h
    · exact nomatch h
  -- (false, true): unfold right
  case _ hua hub =>
    split at h
    · next b₂ hu => exact .deltaR a' b' b₂ hu h
    · exact nomatch h
  -- (true, true): hints, spine, both-sided unfolds
  case _ hua hub =>
    split at h
    · split at h
      · next a₂ hu => exact .deltaL a' b' a₂ hu h
      · exact nomatch h
    split at h
    · split at h
      · next b₂ hu => exact .deltaR a' b' b₂ hu h
      · exact nomatch h
    split at h
    · split at h
      · exact nomatch h
      next c' hs =>
      split at h
      · next hc' => exact .spine a' b' (hc' ▸ hs)
      next hc' =>
      split at h
      · next a₂ b₂ hu₁ hu₂ => exact .deltaB a' b' a₂ b₂ hu₁ hu₂ h
      · exact nomatch h
    · split at h
      · next a₂ b₂ hu₁ hu₂ => exact .deltaB a' b' a₂ b₂ hu₁ hu₂ h
      · exact nomatch h
  -- (false, false): the structural endgame
  case _ hua hub =>
    split at h
    case _ u v => -- sorts
      rw [Setlec.liftFueled.eq_def] at h
      split at h
      · next c'' hiseq =>
        cases c'' with
        | true => exact .sorts u v hiseq
        | false => exact nomatch h
      · exact nomatch h
    case _ l₁ l₂ => -- lits
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl := eq_of_beq h
      exact .lits l₁
    case _ n c us => -- natLit vs const
      split at h
      · next hc'' =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain rfl : n = 0 := by simpa using eq_of_beq h
        obtain ⟨rfl, rfl⟩ := hc''
        exact .natZeroL
      · exact .rescue _ _ h
    case _ c us n => -- const vs natLit
      split at h
      · next hc'' =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain rfl : n = 0 := by simpa using eq_of_beq h
        obtain ⟨rfl, rfl⟩ := hc''
        exact .natZeroR hua
      · exact .rescue _ _ h
    case _ nn f x => -- natLit vs app
      split at h
      · next m c'' =>
        split at h
        · next hc'' => subst hc''; exact .natSuccL m x h
        · exact .rescue _ _ h
      · exact .rescue _ _ h
    case _ f x nn => -- app vs natLit
      split at h
      · next m c'' =>
        split at h
        · next hc'' => subst hc''; exact .natSuccR m x hua h
        · exact .rescue _ _ h
      · exact .rescue _ _ h
    case _ st cO usO x => -- strLit vs app
      split at h
      · exact .strL st cO usO x h
      · exact .rescue _ _ h
    case _ cO usO x st => -- app vs strLit
      split at h
      · exact .strR st cO usO x hua h
      · exact .rescue _ _ h
    case _ i n₁ ty₁ j n₂ ty₂ => -- fvars
      split at h
      · next hij => obtain rfl := eq_of_beq hij
                    exact .fvars i n₁ n₂ ty₁ ty₂
      · exact .rescue _ _ h
    case _ n us n' us' => -- consts
      split at h
      · next hn =>
        subst hn
        split at h
        · exact nomatch h
        next c'' hlift =>
        rw [Setlec.liftFueled.eq_def] at hlift
        split at hlift
        · next aa hiseq =>
          obtain rfl : aa = c'' := Except.ok.inj hlift
          split at h
          · next hc'' => exact .consts n us us' hua (hc'' ▸ hiseq)
          · exact .rescue _ _ h
        · exact nomatch hlift
      · exact .rescue _ _ h
    case _ n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ => -- pi congruence
      split at h
      · exact nomatch h
      next c'' hd =>
      split at h
      · next hc'' =>
        exact .piCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ (hc'' ▸ hd) h
      · exact nomatch h
    case _ n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ => -- lam congruence
      split at h
      · exact nomatch h
      next c'' hd =>
      split at h
      · next hc'' =>
        exact .lamCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ (hc'' ▸ hd) h
      · exact nomatch h
    case _ f₁ a₁ f₂ a₂ => -- app congruence
      split at h
      · next hlen =>
        split at h
        · exact nomatch h
        next c'' hdf =>
        split at h
        · next hc'' =>
          split at h
          · exact nomatch h
          next c₃ hdl =>
          split at h
          · next hc₃ =>
            exact .appCong f₁ a₁ f₂ a₂ hua hlen (hc'' ▸ hdf) (hc₃ ▸ hdl)
          · exact .rescue _ _ h
        · exact .rescue _ _ h
      · exact .rescue _ _ h
    case _ s₁ i₁ e₁ s₂ i₂ e₂ => -- proj congruence
      split at h
      · next hi =>
        obtain rfl := eq_of_beq hi
        split at h
        · exact nomatch h
        next c'' hd =>
        split at h
        · next hc'' => exact .projCong s₁ s₂ i₁ e₁ e₂ (hc'' ▸ hd)
        · exact .rescue _ _ h
      · exact .rescue _ _ h
    next => -- one-sided lam, left
      split at h
      · exact nomatch h
      next c'' he =>
      split at h
      · next hc'' => exact .etaL _ _ _ _ _ (hc'' ▸ he)
      · exact .rescue _ _ h
    next => -- one-sided lam, right
      split at h
      · exact nomatch h
      next c'' he =>
      split at h
      · next hc'' => exact .etaR _ _ _ _ _ (hc'' ▸ he)
      · exact .rescue _ _ h
    case _ => exact .rescue _ _ h

/-- Loop-level `whnf` runs are monotone in the knot fuel (given the
obligation): lift every piece and reassemble at the same budget. -/
theorem whnfLoop_r_mono {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g g' d : Nat} (hg : g ≤ g') :
    ∀ {l : Nat} {e s : Expr},
      Setlec.whnfLoop (Setlec.pureFns μ env g) env d l e = .ok s →
      Setlec.whnfLoop (Setlec.pureFns μ env g') env d l e = .ok s := by
  intro l
  induction l with
  | zero => intro e s h; exact nomatch h
  | succ l ih =>
    intro e s h
    rw [whnfLoop_succ] at h
    rw [whnfLoop_succ]
    obtain ⟨e₁, hwc, hrest⟩ := whnfStep_decompose h
    have hwc' : (Setlec.pureFns μ env g').whnfCore d e = .ok e₁ :=
      hm.2.2.1 hg (hwc : whnfCore μ env g d e = .ok e₁)
    rcases hrest with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact whnfStep_assemble_nat hwc' (hm.2.2.2.2 hg hrn) (ih hk)
    · exact whnfStep_assemble_delta hwc' (hm.2.2.2.2 hg hrn) hud (ih hk)
    · exact whnfStep_assemble_stuck hwc' (hm.2.2.2.2 hg hrn) hud

/-- Two loop-level runs on one subject agree (lift to common fuel and
budget, then read off). -/
theorem whnfLoop_det {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g₁ g₂ l₁ l₂ d : Nat} {e s₁ s₂ : Expr}
    (h₁ : Setlec.whnfLoop (Setlec.pureFns μ env g₁) env d l₁ e = .ok s₁)
    (h₂ : Setlec.whnfLoop (Setlec.pureFns μ env g₂) env d l₂ e = .ok s₂) :
    s₁ = s₂ := by
  have k₁ := whnfLoop_budget_mono (Nat.le_max_left l₁ l₂)
    (whnfLoop_r_mono hm (Nat.le_max_left g₁ g₂) h₁)
  have k₂ := whnfLoop_budget_mono (Nat.le_max_right l₁ l₂)
    (whnfLoop_r_mono hm (Nat.le_max_right g₁ g₂) h₂)
  rw [k₁] at k₂
  exact Except.ok.inj k₂

/-- Peel a whole `whnf` run to the loop (the given-run direction;
fuel `0` runs cannot succeed). -/
theorem whnf_peel {μ : CheckMode} {env : Env} {f d : Nat}
    {e s : Expr} (h : whnf μ env f d e = .ok s) :
    ∃ g l, l ≤ Setlec.whnfLoopFuel ∧
      Setlec.whnfLoop (Setlec.pureFns μ env g) env d l e = .ok s := by
  cases f with
  | zero => exact nomatch h
  | succ f => exact ⟨f, Setlec.whnfLoopFuel, Nat.le_refl _, h⟩

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
family well-founded is the DESIGN "audit under R3" record.  (The
spine seal later generalized the transported fact from sort numerals
to arbitrary `w` — see "The transport spine" below; the numeral forms
here remain as the spine's sort instances.) -/

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

/-- The loop-level sort computation — the internal form constructed
runs take (the budget-edge finding: whole-`whnf` conclusions are
false at the fixed budget's edge, so constructed sort computations
carry their own loop budget). -/
def SortOfLE (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (d : Nat) (e : Expr) (u : Nat) : Prop :=
  ∃ ft t, inferTypeCore μ env ft d e = .ok t ∧
    ∃ g l ℓ, Setlec.whnfLoop (Setlec.pureFns μ env g) env d l t
        = .ok (.sort ℓ) ∧
      ℓ.eval φ = u

/-- A given (whole-`whnf`) sort computation peels to the loop form. -/
theorem SortOfLE_of_run {μ : CheckMode} {env : Env} {φ : Name → Nat}
    {f d : Nat} {e : Expr} {u : Nat}
    (h : sortOfE μ env φ f d e = some u) : SortOfLE μ env φ d e u := by
  unfold sortOfE at h
  cases hi : inferTypeCore μ env f d e with
  | error => rw [hi] at h; exact nomatch h
  | ok t =>
    rw [hi] at h
    simp only [Except.toOption] at h
    cases hw : whnf μ env f d t with
    | error => rw [hw] at h; exact nomatch h
    | ok w =>
      rw [hw] at h
      split at h
      · next ℓ heq =>
        obtain rfl : w = .sort ℓ := by
          simpa [Except.toOption] using heq
        obtain ⟨g, l, -, hl⟩ := whnf_peel hw
        exact ⟨f, t, hi, g, l, ℓ, hl, Option.some.inj h⟩
      · exact nomatch h

/-- Loop-level sort computations on one subject agree. -/
theorem SortOfLE_det {μ : CheckMode} {env : Env} {φ : Name → Nat}
    (hm : KnotFuelMono μ env) {d : Nat} {e : Expr} {u v : Nat}
    (h₁ : SortOfLE μ env φ d e u) (h₂ : SortOfLE μ env φ d e v) :
    u = v := by
  obtain ⟨ft₁, t₁, hi₁, g₁, l₁, ℓ₁, hl₁, hev₁⟩ := h₁
  obtain ⟨ft₂, t₂, hi₂, g₂, l₂, ℓ₂, hl₂, hev₂⟩ := h₂
  obtain rfl : t₁ = t₂ := (KnotFuelDet_of_mono hm).1 hi₁ hi₂
  have hs : Expr.sort ℓ₁ = Expr.sort ℓ₂ := whnfLoop_det hm hl₁ hl₂
  obtain rfl : ℓ₁ = ℓ₂ := Setlec.Expr.sort.inj hs
  rw [← hev₁, ← hev₂]

/-! ### The transport spine (the trio + (F) currency, `_gen`-first)

**Ruling — the transported fact is `w`-general.**  Reading the trio's
cert bodies fixed the collision shapes: the rescue/eta collisions are
*shape* collisions — a struct-const- or `∀`-headed `w` against the
chain end's `.sort`-shaped one, by determinism — and the probe's sort
branch applies the spine a *second* time, along the type's own whnf
chain, at a sort whose level is not the subject's.  A sort-numeral
spine serves neither; both consumers (the trio and the (F) run-mirror
constructions) want the same `w`-uniform statement, so it is stated
once.  `SortOfLE` is its sort instance (`sortOfLE_iff_typeWhnfLE`).
The sort-numeral species `SortTransport*F` this block replaces were
unconsumed; DESIGN records the supersession and the trio's discharge
map against the spine. -/

/-- The spine's transported fact: the subject's inferred type
whnf-converges to `w` — loop-level (budget-edge discipline), fuel-free
(functional by `KnotFuelMono`, `TypeWhnfLE_det`), valuation-free (`w`
is carried syntactically). -/
def TypeWhnfLE (μ : CheckMode) (env : Env) (d : Nat) (e w : Expr) :
    Prop :=
  ∃ ft t, inferTypeCore μ env ft d e = .ok t ∧
    ∃ g l, Setlec.whnfLoop (Setlec.pureFns μ env g) env d l t = .ok w

/-- Spine facts on one subject agree. -/
theorem TypeWhnfLE_det {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {d : Nat} {e w₁ w₂ : Expr}
    (h₁ : TypeWhnfLE μ env d e w₁) (h₂ : TypeWhnfLE μ env d e w₂) :
    w₁ = w₂ := by
  obtain ⟨ft₁, t₁, hi₁, g₁, l₁, hl₁⟩ := h₁
  obtain ⟨ft₂, t₂, hi₂, g₂, l₂, hl₂⟩ := h₂
  obtain rfl : t₁ = t₂ := (KnotFuelDet_of_mono hm).1 hi₁ hi₂
  exact whnfLoop_det hm hl₁ hl₂

/-- The constructible chain-end fact: a literal sort's type
whnf-converges to the successor sort.  Every trio collision bottoms
out against this through `TypeWhnfLE_det`. -/
theorem typeWhnfLE_sort {μ : CheckMode} {env : Env} {d : Nat}
    {ℓ : Level} :
    TypeWhnfLE μ env d (.sort ℓ) (.sort (.succ ℓ)) := by
  have hi : inferTypeCore μ env (0 + 1) d (.sort ℓ)
      = .ok (.sort (.succ ℓ)) := by
    rw [Setlec.inferTypeCore_succ]; rfl
  obtain ⟨g, l, -, hl⟩ :=
    whnf_peel (Setlec.whnf_sort (mode := μ) env 0 d (.succ ℓ))
  exact ⟨0 + 1, _, hi, g, l, hl⟩

/-- `SortOfLE` is the spine's sort instance. -/
theorem sortOfLE_iff_typeWhnfLE {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {d : Nat} {e : Expr} {u : Nat} :
    SortOfLE μ env φ d e u ↔
      ∃ ℓ, TypeWhnfLE μ env d e (.sort ℓ) ∧ ℓ.eval φ = u := by
  constructor
  · rintro ⟨ft, t, hi, g, l, ℓ, hl, hev⟩
    exact ⟨ℓ, ⟨ft, t, hi, g, l, hl⟩, hev⟩
  · rintro ⟨ℓ, ⟨ft, t, hi, g, l, hl⟩, hev⟩
    exact ⟨ft, t, hi, g, l, ℓ, hl, hev⟩

/-- The subject-invariant package the spine threads: the
bridge-standard syntactic guards plus *self*-pairing.  It travels as
a premise by necessity: `infer`'s `fvar` leaf reads its own
annotation only — no cross-leaf check — so no run ever certifies
pairing (refutation by reading; DESIGN).  Supplied at the shell's
entry from `EnsureSortAgreeR`'s own guards (`SubjInv.of_pair`),
preserved along head steps by the `InvPreserve*F` species. -/
def SubjInv (d : Nat) (e : Expr) : Prop :=
  Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded e ∧ PairedLeaves e e

/-- Self-pairing restricts from any pairing: the package for one side
of a certified pair. -/
theorem SubjInv.of_pair {d : Nat} {a b : Expr}
    (h₁ : Expr.WScoped d a) (h₂ : a.looseBVarsBounded 0 = true)
    (h₃ : Expr.LeavesBounded a) (hp : PairedLeaves a b) :
    SubjInv d a :=
  ⟨h₁, h₂, h₃, fun l hl l' hl' heq =>
    hp l (List.mem_append_left _ ((List.mem_append.1 hl).elim id id))
      l' (List.mem_append_left _ ((List.mem_append.1 hl').elim id id))
      heq⟩

/-- The right-side restriction. -/
theorem SubjInv.of_pair_right {d : Nat} {a b : Expr}
    (h₁ : Expr.WScoped d b) (h₂ : b.looseBVarsBounded 0 = true)
    (h₃ : Expr.LeavesBounded b) (hp : PairedLeaves a b) :
    SubjInv d b :=
  ⟨h₁, h₂, h₃, fun l hl l' hl' heq =>
    hp l (List.mem_append_right _ ((List.mem_append.1 hl).elim id id))
      l' (List.mem_append_right _ ((List.mem_append.1 hl').elim id id))
      heq⟩

/-! ### The abstract pair slot (the joint motive ruling)

The shell is parametric in a **binary** invariant
`Q : Nat → Expr → Expr → Prop` on the compared pair, threaded along
head steps.  One binary slot serves both ruled consumers at once —
the denote frame is `Q d a b := P d a ∧ P d b` (the spine core's
model-tier discharge instantiates `P` at "denotes and `CtxOkR` in my
frame"; suppliers `WhnfCoreClaimsR`, `denote_delta_step`, the
literal/`Bool` denotes) and the cross-pairing (B)'s `fvars` case
needs is `Q d a b := PairedLeaves a b` — while the `Q := True`
instance recovers the slot-free claim with *trivial* preservers (no
hypothesis regression).  Steps touch one side at a time, so the slot
takes **left**-step preservers plus symmetry; V-freedom is preserved
by parametricity (the induction never inspects `Q`). -/

/-- `Q` survives a left-side head-normalization step. -/
def QPreserveCoreF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {f d : Nat} {e e' c : Expr},
    whnfCore μ env f d e = .ok e' → Q d e c → Q d e' c

/-- `Q` survives a left-side unfolding. -/
def QPreserveDeltaF (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d : Nat} {e e' c : Expr},
    Setlec.unfoldDefinition env e = some e' → Q d e c → Q d e' c

/-- `Q` survives a left-side literal-acceleration step. -/
def QPreserveNatF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {f d : Nat} {e e' c : Expr},
    Setlec.reduceNat (Setlec.pureFns μ env f) env d e = .ok (some e') →
    Q d e c → Q d e' c

/-- Cross-pairing is symmetric (the pairing instance's `Q`-symmetry
supplier). -/
theorem PairedLeaves.symm {a b : Expr} (h : PairedLeaves a b) :
    PairedLeaves b a := fun l hl l' hl' heq =>
  h l (List.mem_append.2 ((List.mem_append.1 hl).symm))
    l' (List.mem_append.2 ((List.mem_append.1 hl').symm)) heq

/-- Cross-pairing survives a left-side head-normalization step —
the pairing instance's core preserver ((B)'s `fvars` supplier;
discharged at its own seal alongside the `InvPreserve*F` suppliers,
whose self-pairing legs prove the same leaf-shrinking). -/
def PairedPreserveCoreF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e e' c : Expr},
    whnfCore μ env f d e = .ok e' →
    PairedLeaves e c → PairedLeaves e' c

/-- Cross-pairing survives a left-side unfolding (stored values are
closed — the same env-tier fact `InvPreserveDeltaF` threads). -/
def PairedPreserveDeltaF (env : Env) : Prop :=
  ∀ {e e' c : Expr},
    Setlec.unfoldDefinition env e = some e' →
    PairedLeaves e c → PairedLeaves e' c

/-- Cross-pairing survives a left-side literal-acceleration step. -/
def PairedPreserveNatF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e e' c : Expr},
    Setlec.reduceNat (Setlec.pureFns μ env f) env d e = .ok (some e') →
    PairedLeaves e c → PairedLeaves e' c

/-- **(F-core)**: one head-normalization step transports the spine
fact forward, `w` intact.  The β case is the substitution pairing in
constructive form (the walk on the substituted body is *built* from
the opened walk plus the site's own cert pieces — the correspondence
travels as cert runs, never as sort agreements). -/
def TypeTransportCoreF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e e' w : Expr},
    whnfCore μ env f d e = .ok e' → SubjInv d e →
    TypeWhnfLE μ env d e w → TypeWhnfLE μ env d e' w

/-- **(F-δ)**: one definition unfolding transports the spine fact
forward — threading the *install-time* cert (the value was checked
against the declared type when the definition entered the env);
`DeltaSortLinked`'s territory. -/
def TypeTransportDeltaF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {d : Nat} {e e' w : Expr},
    Setlec.unfoldDefinition env e = some e' → SubjInv d e →
    TypeWhnfLE μ env d e w → TypeWhnfLE μ env d e' w

/-- **(F-nat)**: one literal-acceleration step — expected vacuous on
sort-bound chains (the subjects are `Nat`/`Bool` elements), but
stated as transport so the loop assembly is uniform. -/
def TypeTransportNatF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e e' w : Expr},
    Setlec.reduceNat (Setlec.pureFns μ env f) env d e = .ok (some e') →
    SubjInv d e →
    TypeWhnfLE μ env d e w → TypeWhnfLE μ env d e' w

/-- Invariant preservation along a head-normalization step — the
spine's supply chain (with the δ/nat/infer siblings below). -/
def InvPreserveCoreF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e e' : Expr},
    whnfCore μ env f d e = .ok e' → SubjInv d e → SubjInv d e'

/-- Invariant preservation along one unfolding (stored values are
closed — the env-tier fact this species will thread). -/
def InvPreserveDeltaF (env : Env) : Prop :=
  ∀ {d : Nat} {e e' : Expr},
    Setlec.unfoldDefinition env e = some e' → SubjInv d e → SubjInv d e'

/-- Invariant preservation along one literal-acceleration step. -/
def InvPreserveNatF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e e' : Expr},
    Setlec.reduceNat (Setlec.pureFns μ env f) env d e = .ok (some e') →
    SubjInv d e → SubjInv d e'

/-- Invariant transfer to an inferred type — the probe discharge's
entry to the *type's* whnf chain (its second spine application). -/
def InvPreserveInferF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {f d : Nat} {e t : Expr},
    inferTypeCore μ env f d e = .ok t → SubjInv d e → SubjInv d t

/-- **(C\*-L)**: the whole-chain transport at loop level — assembled
from the three step species plus the `InvPreserve*` supply chain by
one loop induction (supersedes the whole-`whnf` (C\*-E) spelling;
that form returns as a corollary through `whnf_peel` when a consumer
holds a whole-`whnf` run).  Its conclusion sits at the loop's
*output*, which is where every trio collision reads it. -/
def TypeTransportLoopF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g l d : Nat} {e s w : Expr},
    Setlec.whnfLoop (Setlec.pureFns μ env g) env d l e = .ok s →
    SubjInv d e →
    TypeWhnfLE μ env d e w → TypeWhnfLE μ env d s w

/-! ## Repair δ: the chain-link correspondence and the (A-T) primitive

The pairing's correspondence invariant carries **chain-links** — a
conditional, ∃-fuel convergence fact — instead of cert runs, and the
site certs are consumed *at the leaves* through the transport form of
(A).  Dual-success (A) becomes a corollary (`EnsureSortAgreeR_of_link`
below); the internal fueled forms and the joint measure
(lexicographic on (Σ knot fuels, Σ loop budgets) of fueled
hypotheses) are the DESIGN "J0" record. -/

/-- **The chain-link**: if the left type whnf-converges to a literal
sort, the right one does too, with the same numeral.  The ∃-run
*output* form the correspondence carries (repair δ: outputs are
fuel-free, so links never enter a measure).

**Loop-level, by necessity** (the budget-edge finding): `whnf`'s
internal step budget is a *fixed constant*, so a constructed run one
step longer than a maximal given run cannot be wrapped back into
`whnf` — a whole-`whnf` conclusion is false at the edge.  Constructed
runs therefore live at the loop, with the knot fuel *and* the budget
existential; consumers collide them with given `whnf` runs through
`whnfLoop_det` below. -/
def SortLinkE (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (d : Nat) (t t' : Expr) : Prop :=
  ∀ {f : Nat} {ℓ : Level}, whnf μ env f d t = .ok (.sort ℓ) →
    ∃ g l ℓ', Setlec.whnfLoop (Setlec.pureFns μ env g) env d l t'
        = .ok (.sort ℓ') ∧
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
    {φ : Name → Nat} (hm : KnotFuelMono μ env)
    (hAT : SortLinkAcrossCertE μ env φ) :
    EnsureSortAgreeR μ env φ := by
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwa hba hLa hwb hbb hLb hp h₁ h₂
  obtain ⟨g, l, ℓ', hw', hev⟩ :=
    hAT hc hwa hba hLa hwb hbb hLb hp h₁
  obtain ⟨g₂, l₂', -, h₂'⟩ := whnf_peel h₂
  have hs : Expr.sort ℓ' = Expr.sort ℓ₂ := whnfLoop_det hm hw' h₂'
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

/-! ## Shape facts for the vacuity chases

`reduceNat` rewrites only the two nat-op application shapes and
`unfoldDefinition` only const-headed terms, so on every other shape
both are `none` by computation — the det-vacuity chases read the
given run's own step against these. -/

section Shapes
variable {μ : CheckMode} {env : Env}
variable {r : Setlec.CoreFns Setlec.CheckM} {d : Nat}

theorem reduceNat_sort {ℓ : Level} :
    Setlec.reduceNat r env d (.sort ℓ) = .ok none := rfl
theorem reduceNat_const {n : Name} {us : List Level} :
    Setlec.reduceNat r env d (.const n us) = .ok none := rfl
theorem reduceNat_forallE {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    Setlec.reduceNat r env d (.forallE n ty b m) = .ok none := rfl
theorem reduceNat_lam {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    Setlec.reduceNat r env d (.lam n ty b m) = .ok none := rfl
theorem reduceNat_fvar {i : Nat} {n : Name} {ty : Expr} :
    Setlec.reduceNat r env d (.fvar i n ty) = .ok none := rfl
theorem reduceNat_proj {s : Name} {i : Nat} {e : Expr} :
    Setlec.reduceNat r env d (.proj s i e) = .ok none := rfl
theorem reduceNat_lit {l : Setlec.Literal} :
    Setlec.reduceNat r env d (.lit l) = .ok none := rfl

theorem unfoldDefinition_sort {ℓ : Level} :
    Setlec.unfoldDefinition env (.sort ℓ) = none := rfl
theorem unfoldDefinition_forallE {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    Setlec.unfoldDefinition env (.forallE n ty b m) = none := rfl
theorem unfoldDefinition_lam {n : Name} {ty b : Expr}
    {m : Setlec.BinderMeta} :
    Setlec.unfoldDefinition env (.lam n ty b m) = none := rfl
theorem unfoldDefinition_fvar {i : Nat} {n : Name} {ty : Expr} :
    Setlec.unfoldDefinition env (.fvar i n ty) = none := rfl
theorem unfoldDefinition_proj {s : Name} {i : Nat} {e : Expr} :
    Setlec.unfoldDefinition env (.proj s i e) = none := rfl
theorem unfoldDefinition_lit {l : Setlec.Literal} :
    Setlec.unfoldDefinition env (.lit l) = none := rfl

end Shapes

/-! ## The (A-T) case tier — the vacuity workhorse and the replay

`loop_stuck_out` closes every det-vacuous structural case in one
move: the given run's own first step is read against the shape facts,
so a subject whose whnfCore output is inert *is* the run's output —
colliding with the given literal-sort output.  `loop_align` is the
syn-splice: two subjects with one whnfCore output share every
continuation, so the given run replays on the other subject. -/

/-- If the subject's whnfCore output is inert (no nat step, no
unfolding), the loop run ends there. -/
theorem loop_stuck_out {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g l d f : Nat} {a s a' : Expr}
    (h : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l a = .ok s)
    (hwc : whnfCore μ env f d a = .ok a')
    (hrn : ∀ g' : Nat,
      Setlec.reduceNat (Setlec.pureFns μ env g') env d a' = .ok none)
    (hud : Setlec.unfoldDefinition env a' = none) : s = a' := by
  cases l with
  | zero => exact nomatch h
  | succ l =>
    rw [whnfLoop_succ] at h
    obtain ⟨e₁, hwc', hrest⟩ := whnfStep_decompose h
    obtain rfl : e₁ = a' :=
      (KnotFuelDet_of_mono hm).2.2.1
        (hwc' : whnfCore μ env g d a = .ok e₁) hwc
    rcases hrest with ⟨e₂, hrn', _⟩ | ⟨_, e₂, hud', _⟩ | ⟨_, _, rfl⟩
    · rw [hrn g] at hrn'; exact nomatch (Except.ok.inj hrn')
    · rw [hud] at hud'; exact nomatch hud'
    · rfl

/-- **The replay**: if `b` whnfCores to the same head-normal form as
`a`, the given loop run on `a` reproduces on `b` (at a lifted knot
fuel, same budget). -/
theorem loop_align {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g l d f₁ f₂ : Nat} {a b s a₁ : Expr}
    (h : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l a = .ok s)
    (hwa : whnfCore μ env f₁ d a = .ok a₁)
    (hwb : whnfCore μ env f₂ d b = .ok a₁) :
    Setlec.whnfLoop (Setlec.pureFns μ env (max g f₂)) env d l b
      = .ok s := by
  cases l with
  | zero => exact nomatch h
  | succ l =>
    rw [whnfLoop_succ] at h
    rw [whnfLoop_succ]
    obtain ⟨e₁, hwc', hrest⟩ := whnfStep_decompose h
    obtain rfl : a₁ = e₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwc' : whnfCore μ env g d a = .ok e₁) hwa).symm
    have hwb' : (Setlec.pureFns μ env (max g f₂)).whnfCore d b
        = .ok a₁ :=
      hm.2.2.1 (Nat.le_max_right g f₂) hwb
    rcases hrest with ⟨e₂, hrn, hk⟩ | ⟨hrn, e₂, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact whnfStep_assemble_nat hwb'
        (hm.2.2.2.2 (Nat.le_max_left g f₂) hrn)
        (whnfLoop_r_mono hm (Nat.le_max_left g f₂) hk)
    · exact whnfStep_assemble_delta hwb'
        (hm.2.2.2.2 (Nat.le_max_left g f₂) hrn) hud
        (whnfLoop_r_mono hm (Nat.le_max_left g f₂) hk)
    · exact whnfStep_assemble_stuck hwb'
        (hm.2.2.2.2 (Nat.le_max_left g f₂) hrn) hud

/-- A non-unfoldable head yields no unfolding (the `isSome` relation
the body comment states, in the direction the vacuities read). -/
theorem unfoldDefinition_none_of_not_unfoldable {env : Env} {e : Expr}
    (h : Setlec.unfoldableHead env e = false) :
    Setlec.unfoldDefinition env e = none := by
  unfold Setlec.unfoldableHead at h
  unfold Setlec.unfoldDefinition
  split at h
  · next n us heq =>
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      rw [hf] at h
      cases ci with
      | defnInfo cv value hint =>
        exact if_neg (by simpa using h)
      | thmInfo cv value =>
        exact if_neg (by simpa using h)
      | axiomInfo cv => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv a b => rfl
      | recInfo cv a b c => rfl
      | projInfo entry => rfl
  · rfl

/-! ## The shell's named hypotheses (the ledger's routing points)

`WhnfCoreIdem` and the four vacuity routings — each discharged at its
own seal (idempotence: body-level induction; probe/rescue/eta: the
chain-transport / PSS seal; nat: the `natOpResult` shape-chase
seal).  All are consumed by `sortLinkAcrossCertE_of` (the shell,
next seal). -/

/- `WhnfCoreIdem` was DELETED (R-a ruling): refuted at the strLit
corner — `projLitToCtor` routes through the stored `String.ofList`,
a program the stream author controls, so whnfCore outputs are not
normal forms with respect to whnfCore in any fuel form.  Its
consumers use `whnfCore_reidem_const` (run-threaded, shape-
conditioned) and `whnfCore_sort_run` instead. -/

/-- PSS routing: a `proofIrrel`-certified subject cannot
whnf-converge to a literal sort. -/
def ProbeSortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g g' l f d : Nat} {a a' b' : Expr} {ℓ : Level},
    SubjInv d a → Q d a' b' →
    whnfCore μ env f d a = .ok a' →
    Setlec.proofIrrel (Setlec.pureFns μ env g) env d a' b' = .ok true →
    Setlec.whnfLoop (Setlec.pureFns μ env g') env d l a
      = .ok (.sort ℓ) →
    False

/-- PSS routing: a rescue-certified subject (pair-eta, struct-eta,
unit, or the irrelevance fallback) cannot whnf-converge to a literal
sort. -/
def RescueSortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g g' l f d : Nat} {a a' b' : Expr} {ℓ : Level},
    SubjInv d a → Q d a' b' →
    whnfCore μ env f d a = .ok a' →
    Setlec.stuckIrrel μ (Setlec.pureFns μ env g) env d a' b'
      = .ok true →
    Setlec.whnfLoop (Setlec.pureFns μ env g') env d l a
      = .ok (.sort ℓ) →
    False

/-- PSS routing: an eta-certified (function-typed) subject cannot
whnf-converge to a literal sort. -/
def EtaSortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g g' l f d : Nat} {a a' : Expr} {n : Name} {ty body : Expr}
    {m : Setlec.BinderMeta} {ℓ : Level},
    SubjInv d a → Q d a' (.lam n ty body m) →
    whnfCore μ env f d a = .ok a' →
    Setlec.etaCert (Setlec.pureFns μ env g) env d n ty body m a'
      = .ok true →
    Setlec.whnfLoop (Setlec.pureFns μ env g') env d l a
      = .ok (.sort ℓ) →
    False

/-- Nat-chase routing, one-sided (the right disjunct of the earlier
form dissolved: the dual shell holds the *given run of each side*, so
the hypothesis applies per side with that side's own run — the
run-mirror principle; no cert-loop induction needed): a subject whose
head-normal form nat-steps cannot whnf-converge to a literal sort. -/
def NatStepNoSort (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g g' l f d : Nat} {e e' x : Expr} {ℓ : Level},
    whnfCore μ env f d e = .ok e' →
    Setlec.reduceNat (Setlec.pureFns μ env g) env d e' = .ok (some x) →
    Setlec.whnfLoop (Setlec.pureFns μ env g') env d l e
      = .ok (.sort ℓ) →
    False
/-! ## Run positivity and terminal extraction -/

/-- Successful runs consume fuel: the zero-fuel knot throws. -/
theorem whnfCore_pos {μ : CheckMode} {env : Env} {f d : Nat}
    {e e' : Expr} (h : whnfCore μ env f d e = .ok e') : 1 ≤ f := by
  cases f with
  | zero => exact nomatch h
  | succ f => exact Nat.le_add_left 1 f

/-- **Terminal-step extraction**: a successful reduction loop ends
with a stuck step — its output is a `whnfCore` output at the loop's
own knot, with the literal no-step facts.  (The whnf-idem half of the
discharge reruns exactly these.) -/
theorem whnfLoop_final {env : Env} {r : Setlec.CoreFns Setlec.CheckM}
    {d : Nat} : ∀ {l : Nat} {e s : Expr},
    Setlec.whnfLoop r env d l e = .ok s →
    ∃ x, r.whnfCore d x = .ok s ∧
      Setlec.reduceNat r env d s = .ok none ∧
      Setlec.unfoldDefinition env s = none := by
  intro l
  induction l with
  | zero => intro e s h; exact nomatch h
  | succ l ih =>
    intro e s h
    rw [whnfLoop_succ] at h
    obtain ⟨e₁, hwc, hrest⟩ := whnfStep_decompose h
    rcases hrest with ⟨e₂, _, hk⟩ | ⟨_, e₂, _, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact ih hk
    · exact ih hk
    · exact ⟨e, hwc, hrn, hud⟩


/-! ## R-a: run-threaded partial re-idem (the `WhnfCoreIdem` deletion)

The obligation is gone (refuted at the strLit corner — DESIGN).  What
the shell's sites actually need: a whnfCore output the *surrounding
facts show const-headed* re-cores to itself (the proj-strLit path is
excluded by the shape, so no stored program is ever re-run), plus the
sort-value case directly.  The shape is derivable at every site from
the leg's own facts (`reduceNat`-some and `unfoldDefinition`-some
force const heads). -/

/-- A step target of `unfoldDefinition` is const-headed. -/
theorem unfoldDefinition_some_head {env : Env} {e x : Expr}
    (h : Setlec.unfoldDefinition env e = some x) :
    ∃ n us, e.getAppFn = Setlec.Expr.const n us := by
  unfold Setlec.unfoldDefinition at h
  split at h
  · next n us heq => exact ⟨n, us, heq⟩
  · exact nomatch h

/-- A subject `reduceNat` rewrites is const-headed. -/
theorem reduceNat_some_head {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e x : Expr}
    (h : Setlec.reduceNat r env d e = .ok (some x)) :
    ∃ n us, e.getAppFn = Setlec.Expr.const n us := by
  unfold Setlec.reduceNat at h
  split at h
  · next c a => exact ⟨c, [], rfl⟩
  · next c a b => exact ⟨c, [], rfl⟩
  · exact nomatch h

/-- Sorts re-core to themselves (value branch). -/
theorem whnfCore_sort_run {μ : CheckMode} {env : Env} {f d : Nat}
    {ℓ : Level} (hf : 1 ≤ f) :
    whnfCore μ env f d (.sort ℓ) = .ok (.sort ℓ) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- **Run-threaded partial re-idem**: a whnfCore output that is
const-headed re-cores to itself at the same fuel — by induction on
the producing run, re-firing the run's own `iotaRec`/cert facts.  The
proj branches are excluded by the shape, so the strLit corner (the
refutation) is never entered. -/
theorem whnfCore_reidem_const {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) :
    ∀ {f d : Nat} {e e' : Expr} {n : Name} {us : List Level},
      whnfCore μ env f d e = .ok e' →
      e'.getAppFn = Setlec.Expr.const n us →
      whnfCore μ env f d e' = .ok e' := by
  intro f
  induction f with
  | zero => intro d e e' n us h _; exact nomatch h
  | succ f ih =>
    intro d e e' n us h hshape
    rw [Setlec.whnfCore_succ] at h
    unfold Setlec.whnfCoreBody at h
    split at h
    · -- sort
      obtain rfl : Expr.sort _ = e' := Except.ok.inj h
      exact nomatch hshape
    · -- fvar
      obtain rfl : Expr.fvar _ _ _ = e' := Except.ok.inj h
      exact nomatch hshape
    · -- forallE
      obtain rfl : Expr.forallE _ _ _ _ = e' := Except.ok.inj h
      exact nomatch hshape
    · -- lam
      obtain rfl : Expr.lam _ _ _ _ = e' := Except.ok.inj h
      exact nomatch hshape
    · -- const
      next n' us' =>
      obtain rfl : Expr.const n' us' = e' := Except.ok.inj h
      rw [Setlec.whnfCore_succ]
      rfl
    · -- lit
      obtain rfl : Expr.lit _ = e' := Except.ok.inj h
      exact nomatch hshape
    · -- app
      next f₀ a₀ =>
      cases hwf : (Setlec.pureFns μ env f).whnfCore d f₀ with
      | error err => rw [hwf] at h; exact nomatch h
      | ok fw =>
      rw [hwf] at h
      simp only [Bind.bind, Except.bind] at h
      split at h
      · -- beta path (fw is a λ)
        next n₁ ty₁ body₁ mb₁ =>
        cases hinf : (Setlec.pureFns μ env f).infer d a₀ with
        | error err => rw [hinf] at h; exact nomatch h
        | ok ta =>
        rw [hinf] at h
        simp only [] at h
        cases hdq : (Setlec.pureFns μ env f).defeq d ta ty₁ with
        | error err => rw [hdq] at h; exact nomatch h
        | ok c =>
        rw [hdq] at h
        simp only [] at h
        cases c with
        | true =>
          simp only [if_true] at h
          exact hm.2.2.1 (Nat.le_succ f) (ih h hshape)
        | false =>
          simp only [Bool.false_eq_true, if_false] at h
          obtain rfl : Expr.app (.lam n₁ ty₁ body₁ mb₁) a₀ = e' :=
            Except.ok.inj h
          exact nomatch hshape
      · -- iota path (fw not a λ)
        rename_i hnelam
        cases hio : Setlec.iotaRec μ (Setlec.pureFns μ env f) env d
            (.app fw a₀) with
        | error err => rw [hio] at h; exact nomatch h
        | ok o =>
        rw [hio] at h
        simp only [] at h
        cases o with
        | some e₂ =>
          exact hm.2.2.1 (Nat.le_succ f) (ih h hshape)
        | none =>
          obtain rfl : Expr.app fw a₀ = e' := Except.ok.inj h
          have hfwshape : fw.getAppFn = Setlec.Expr.const n us := hshape
          have hfw' := ih hwf hfwshape
          rw [Setlec.whnfCore_succ]
          simp only [Setlec.whnfCoreBody, Bind.bind, Except.bind]
          rw [show (Setlec.pureFns μ env f).whnfCore d fw
              = .ok fw from hfw']
          split
          · next heq => exact nomatch heq
          · next v heq =>
            obtain rfl : fw = v := Except.ok.inj heq
            split
            · next => exact (hnelam _ _ _ _ rfl).elim
            · rw [hio]
              rfl
    · -- proj
      next sn i pe =>
      cases hw1 : (Setlec.pureFns μ env f).whnf d pe with
      | error err => rw [hw1] at h; exact nomatch h
      | ok w =>
      rw [hw1] at h
      simp only [Bind.bind, Except.bind] at h
      cases hplc : Setlec.projLitToCtor (Setlec.pureFns μ env f) env
          d w with
      | error err => rw [hplc] at h; exact nomatch h
      | ok w₂ =>
      rw [hplc] at h
      simp only [] at h
      split at h
      · next entry hfind =>
        split at h
        · next c us₂ hfn =>
          split at h
          · next hguard =>
            cases hpc : Setlec.projCert (Setlec.pureFns μ env f) env d
                w₂ i _ _ entry.numParams with
            | error err => rw [hpc] at h; exact nomatch h
            | ok pc =>
            rw [hpc] at h
            cases pc with
            | true =>
              simp only [if_true] at h
              cases htc : (if μ.ttChecks then Setlec.projTeleCert
                  (Setlec.pureFns μ env f) env d c us₂
                  w₂.getAppArgs else pure true) with
              | error err => rw [htc] at h; exact nomatch h
              | ok tc =>
              rw [htc] at h
              cases tc with
              | true =>
                simp only [if_true] at h
                exact hm.2.2.1 (Nat.le_succ f) (ih h hshape)
              | false =>
                simp only [Bool.false_eq_true, if_false] at h
                obtain rfl : Expr.proj sn i w₂ = e' := Except.ok.inj h
                exact nomatch hshape
            | false =>
              simp only [Bool.false_eq_true, if_false] at h
              obtain rfl : Expr.proj sn i w₂ = e' := Except.ok.inj h
              exact nomatch hshape
          · obtain rfl : Expr.proj sn i w₂ = e' := Except.ok.inj h
            exact nomatch hshape
        · obtain rfl : Expr.proj sn i w₂ = e' := Except.ok.inj h
          exact nomatch hshape
      · obtain rfl : Expr.proj sn i w₂ = e' := Except.ok.inj h
        exact nomatch hshape
    · -- letE
      exact hm.2.2.1 (Nat.le_succ f) (ih h hshape)
    · -- bvar
      exact nomatch h

/-! ## The dual shell

The primitive after the liveness revert: dual-success (A), by
budget-only cert-loop induction.  Six named hypotheses route what
later seals discharge; every other case reads both GIVEN runs — no
case constructs a run reality has not exhibited.  Ruled and recorded:
**dominance checks certify direction, not provability.** -/

/-- Spine routing, dual form (graded unknown #1): a same-head
level-and-spine congruence with both subjects' sort convergences
given forces numeral agreement.  Carries the abstract pair slot `Q`
at the pre-core subjects (the joint motive ruling). -/
def SpineSortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc l d ga la gb lb f₁ f₂ : Nat} {a b a' b' : Expr}
    {ℓa ℓb : Level},
    SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
    Setlec.defeqLoop μ (Setlec.pureFns μ env fc) env d l a b
      = .ok true →
    whnfCore μ env f₁ d a = .ok a' →
    whnfCore μ env f₂ d b = .ok b' →
    Setlec.defeqSpine (Setlec.pureFns μ env fc) env d a' b'
      = .ok true →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- The `Q`-enriched (A) claim (the joint motive ruling): the
slot-free `EnsureSortAgreeR` is its `Q := True` instance
(`ensureSortAgreeR_of`); the consumer instantiates `Q` at its
denote/`CtxOkR` frame or at cross-pairing. -/
def EnsureSortAgreeRQ (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {ℓ₁ ℓ₂ : Level},
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    Q d a b →
    whnf μ env f₁ d a = .ok (.sort ℓ₁) →
    whnf μ env f₂ d b = .ok (.sort ℓ₂) →
    ℓ₁.eval φ = ℓ₂.eval φ

/-- **The dual-(A) shell**: `EnsureSortAgreeRQ` from the obligations
and the routed hypotheses.  The `SubjInv` package enters from the
claim's own guards (`SubjInv.of_pair`/`.of_pair_right`) and travels
along the loop's head steps by the `InvPreserve*F` supply chain;
the abstract pair slot `Q` enters from the claim's `Q`-premise and
travels by the `QPreserve*F` chain plus symmetry — subjects here
evolve by head steps only (congruence routes wholesale to
`SpineSortAgree`), so no descent preservation is needed. -/
theorem ensureSortAgreeRQ_of {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) (hN : NatStepNoSort μ env)
    (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q := by
  have hdet := KnotFuelDet_of_mono hm
  have main : ∀ (fc L : Nat) {d : Nat} {a b : Expr},
      Setlec.defeqLoop μ (Setlec.pureFns μ env fc) env d L a b
        = .ok true →
      SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
      ∀ {ga la gb lb : Nat} {ℓa ℓb : Level},
        Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a
          = .ok (.sort ℓa) →
        Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b
          = .ok (.sort ℓb) →
        ℓa.eval φ = ℓb.eval φ := by
    intro fc L
    induction L with
    | zero => intro d a b hc; exact nomatch hc
    | succ l ih =>
      intro d a b hc hIa hIb hPab hQab ga la gb lb ℓa ℓb ha hb
      have hc0 := hc
      rw [defeqLoop_succ] at hc
      rcases defeqStep_decompose hc with rfl | ⟨a', b', hwa, hwb, hcert⟩
      · rw [Setlec.Expr.sort.inj (whnfLoop_det hm ha hb)]
      cases la with
      | zero => exact nomatch ha
      | succ la' =>
      cases lb with
      | zero => exact nomatch hb
      | succ lb' =>
      have haD := ha
      rw [whnfLoop_succ] at haD
      obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
      obtain rfl : a' = a₁ :=
        (hdet.2.2.1 (hwca : whnfCore μ env ga d a = .ok a₁)
          (hwa : whnfCore μ env fc d a = .ok a')).symm
      have hbD := hb
      rw [whnfLoop_succ] at hbD
      obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
      obtain rfl : b' = b₁ :=
        (hdet.2.2.1 (hwcb : whnfCore μ env gb d b = .ok b₁)
          (hwb : whnfCore μ env fc d b = .ok b')).symm
      cases hcert with
      | syn =>
        rw [Setlec.Expr.sort.inj
          (whnfLoop_det hm ha (loop_align hm hb hwb hwa))]
      | irrel _ _ hpi =>
        exact (hP hIa (hQs (hQC hwb (hQs (hQC hwa hQab)))) hwa hpi
          ha).elim
      | natL _ _ a₂ hrn hk =>
        exact (hN hwa hrn ha).elim
      | natR _ _ b₂ hrnA hrnB hk =>
        have hb₂ : Setlec.whnfLoop (Setlec.pureFns μ env gb) env d
            lb' b₂ = .ok (.sort ℓb) := by
          rcases htriB with ⟨y, hry, hkyb⟩ | ⟨hry, y, huy, hkyb⟩ |
            ⟨hry, hudy, hstop⟩
          · have h1 := hm.2.2.2.2 (Nat.le_max_left gb fc) hry
            have h2 := hm.2.2.2.2 (Nat.le_max_right gb fc) hrnB
            rw [h1] at h2
            obtain rfl : b₂ = y :=
              (Option.some.inj (Except.ok.inj h2)).symm
            exact hkyb
          · have h1 := hm.2.2.2.2 (Nat.le_max_left gb fc) hry
            have h2 := hm.2.2.2.2 (Nat.le_max_right gb fc) hrnB
            rw [h1] at h2; exact nomatch h2
          · have h1 := hm.2.2.2.2 (Nat.le_max_left gb fc) hry
            have h2 := hm.2.2.2.2 (Nat.le_max_right gb fc) hrnB
            rw [h1] at h2; exact nomatch h2
        rcases htriA with ⟨x, hrx, hkx⟩ | ⟨hrga, x, hux, hkx⟩ |
          ⟨hrga, huda, hstop⟩
        · have h1 := hm.2.2.2.2 (Nat.le_max_left ga fc) hrx
          have h2 := hm.2.2.2.2 (Nat.le_max_right ga fc) hrnA
          rw [h1] at h2; exact nomatch h2
        · have hA : Setlec.whnfLoop (Setlec.pureFns μ env (max fc ga))
              env d (la' + 1) a' = .ok (.sort ℓa) := by
            rw [whnfLoop_succ]
            obtain ⟨nh, ush, hhd⟩ := unfoldDefinition_some_head hux
            exact whnfStep_assemble_delta
              (hm.2.2.1 (Nat.le_max_left fc ga)
                (whnfCore_reidem_const hm hwa hhd))
              (hm.2.2.2.2 (Nat.le_max_right fc ga) hrga) hux
              (whnfLoop_r_mono hm (Nat.le_max_right fc ga) hkx)
          exact ih hk (hIC hwa hIa) (hIN hrnB (hIC hwb hIb))
            ((hLN hrnB (hLC hwb ((hLC hwa hPab).symm))).symm)
            (hQs (hQN hrnB (hQC hwb (hQs (hQC hwa hQab))))) hA hb₂
        · obtain rfl := hstop
          have hA : Setlec.whnfLoop (Setlec.pureFns μ env fc) env d
              1 (.sort ℓa) = .ok (.sort ℓa) := by
            rw [whnfLoop_succ]
            exact whnfStep_assemble_stuck
              (whnfCore_sort_run (whnfCore_pos hwa)) reduceNat_sort
              unfoldDefinition_sort
          exact ih hk (hIC hwa hIa) (hIN hrnB (hIC hwb hIb))
            ((hLN hrnB (hLC hwb ((hLC hwa hPab).symm))).symm)
            (hQs (hQN hrnB (hQC hwb (hQs (hQC hwa hQab))))) hA hb₂
      | deltaL _ _ a₂ hu hk =>
        have hbcore : whnfCore μ env fc d b' = .ok b' := by
          rcases htriB with ⟨y, hry, -⟩ | ⟨-, y, huy, -⟩ | ⟨-, -, hstopB⟩
          · obtain ⟨nh, ush, hhd⟩ := reduceNat_some_head hry
            exact whnfCore_reidem_const hm hwb hhd
          · obtain ⟨nh, ush, hhd⟩ := unfoldDefinition_some_head huy
            exact whnfCore_reidem_const hm hwb hhd
          · obtain rfl := hstopB
            exact whnfCore_sort_run (whnfCore_pos hwb)
        have hb' := loop_align hm hb hwb hbcore
        rcases htriA with ⟨x, hrx, hkx⟩ | ⟨hrga, x, hux, hkx⟩ |
          ⟨hrga, huda, hstop⟩
        · exact (hN hwa hrx ha).elim
        · rw [hu] at hux
          obtain rfl : a₂ = x := Option.some.inj hux
          exact ih hk (hID hu (hIC hwa hIa)) (hIC hwb hIb)
            ((hLC hwb ((hLD hu (hLC hwa hPab)).symm)).symm)
            (hQs (hQC hwb (hQs (hQD hu (hQC hwa hQab))))) hkx hb'
        · rw [hu] at huda; exact nomatch huda
      | deltaR _ _ b₂ hu hk =>
        rcases htriB with ⟨y, hry, hkyb⟩ | ⟨hrgb, y, huy, hkyb⟩ |
          ⟨hrgb, hudb, hstop⟩
        · exact (hN hwb hry hb).elim
        · rw [hu] at huy
          obtain rfl : b₂ = y := Option.some.inj huy
          rcases htriA with ⟨x, hrx, hkx⟩ | ⟨hrga, x, hux, hkx⟩ |
            ⟨hrga, huda, hstop⟩
          · exact (hN hwa hrx ha).elim
          · have hA : Setlec.whnfLoop (Setlec.pureFns μ env (max fc ga))
                env d (la' + 1) a' = .ok (.sort ℓa) := by
              rw [whnfLoop_succ]
              obtain ⟨nh, ush, hhd⟩ := unfoldDefinition_some_head hux
              exact whnfStep_assemble_delta
                (hm.2.2.1 (Nat.le_max_left fc ga)
                  (whnfCore_reidem_const hm hwa hhd))
                (hm.2.2.2.2 (Nat.le_max_right fc ga) hrga) hux
                (whnfLoop_r_mono hm (Nat.le_max_right fc ga) hkx)
            exact ih hk (hIC hwa hIa) (hID hu (hIC hwb hIb))
              ((hLD hu (hLC hwb ((hLC hwa hPab).symm))).symm)
              (hQs (hQD hu (hQC hwb (hQs (hQC hwa hQab))))) hA hkyb
          · obtain rfl := hstop
            have hA : Setlec.whnfLoop (Setlec.pureFns μ env fc) env d
                1 (.sort ℓa) = .ok (.sort ℓa) := by
              rw [whnfLoop_succ]
              exact whnfStep_assemble_stuck
                (whnfCore_sort_run (whnfCore_pos hwa)) reduceNat_sort
                unfoldDefinition_sort
            exact ih hk (hIC hwa hIa) (hID hu (hIC hwb hIb))
              ((hLD hu (hLC hwb ((hLC hwa hPab).symm))).symm)
              (hQs (hQD hu (hQC hwb (hQs (hQC hwa hQab))))) hA hkyb
        · rw [hu] at hudb; exact nomatch hudb
      | deltaB _ _ a₂ b₂ hua hub hk =>
        rcases htriA with ⟨x, hrx, hkx⟩ | ⟨hrga, x, hux, hkx⟩ |
          ⟨hrga, huda, hstop⟩
        · exact (hN hwa hrx ha).elim
        · rw [hua] at hux
          obtain rfl : a₂ = x := Option.some.inj hux
          rcases htriB with ⟨y, hry, hkyb⟩ | ⟨hrgb, y, huy, hkyb⟩ |
            ⟨hrgb, hudb, hstop⟩
          · exact (hN hwb hry hb).elim
          · rw [hub] at huy
            obtain rfl : b₂ = y := Option.some.inj huy
            exact ih hk (hID hua (hIC hwa hIa)) (hID hub (hIC hwb hIb))
              ((hLD hub (hLC hwb ((hLD hua (hLC hwa hPab)).symm))).symm)
              (hQs (hQD hub (hQC hwb (hQs (hQD hua (hQC hwa hQab))))))
              hkx hkyb
          · rw [hub] at hudb; exact nomatch hudb
        · rw [hua] at huda; exact nomatch huda
      | spine _ _ hs =>
        exact hS hIa hIb hPab hQab hc0 hwa hwb hs ha hb
      | sorts u v hiseq =>
        have h1 := loop_stuck_out hm ha hwa
          (fun _ => reduceNat_sort) unfoldDefinition_sort
        have h2 := loop_stuck_out hm hb hwb
          (fun _ => reduceNat_sort) unfoldDefinition_sort
        obtain rfl := Setlec.Expr.sort.inj h1
        obtain rfl := Setlec.Expr.sort.inj h2
        exact Level.isEquiv_sound hiseq φ
      | lits lt =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_lit) unfoldDefinition_lit)
      | natZeroL =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_lit) unfoldDefinition_lit)
      | natZeroR hua =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_const)
          (unfoldDefinition_none_of_not_unfoldable hua))
      | natSuccL n x hd =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_lit) unfoldDefinition_lit)
      | natSuccR n x hua hd =>
        rcases htriA with ⟨x', hrx, hkx⟩ | ⟨hrga, x', hux, hkx⟩ |
          ⟨hrga, huda, hstop⟩
        · exact (hN hwa hrx ha).elim
        · rw [unfoldDefinition_none_of_not_unfoldable hua] at hux
          exact nomatch hux
        · exact nomatch hstop
      | strL st cO usO x hd =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_lit) unfoldDefinition_lit)
      | strR st cO usO x hua hd =>
        rcases htriA with ⟨x', hrx, hkx⟩ | ⟨hrga, x', hux, hkx⟩ |
          ⟨hrga, huda, hstop⟩
        · exact (hN hwa hrx ha).elim
        · rw [unfoldDefinition_none_of_not_unfoldable hua] at hux
          exact nomatch hux
        · exact nomatch hstop
      | fvars i n₁ n₂ ty₁ ty₂ =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_fvar) unfoldDefinition_fvar)
      | consts n us us' hua hiseq =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_const)
          (unfoldDefinition_none_of_not_unfoldable hua))
      | piCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ hd hbody =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_forallE) unfoldDefinition_forallE)
      | lamCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ hd hbody =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_lam) unfoldDefinition_lam)
      | appCong f₁ a₁ f₂ a₂ hua hlen hdf hdl =>
        rcases htriA with ⟨x', hrx, hkx⟩ | ⟨hrga, x', hux, hkx⟩ |
          ⟨hrga, huda, hstop⟩
        · exact (hN hwa hrx ha).elim
        · rw [unfoldDefinition_none_of_not_unfoldable hua] at hux
          exact nomatch hux
        · exact nomatch hstop
      | projCong s₁ s₂ i e₁ e₂ hd =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_proj) unfoldDefinition_proj)
      | etaL n₁ ty₁ body₁ m₁ b₂ he =>
        exact nomatch (loop_stuck_out hm ha hwa
          (fun _ => reduceNat_lam) unfoldDefinition_lam)
      | etaR _ _ _ _ _ he =>
        exact (hE hIa (hQs (hQC hwb (hQs (hQC hwa hQab)))) hwa he
          ha).elim
      | rescue _ _ hsi =>
        exact (hR hIa (hQs (hQC hwb (hQs (hQC hwa hQab)))) hwa hsi
          ha).elim
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwsa hba hLa hwsb hbb hLb hp hQ h₁ h₂
  cases fc with
  | zero => exact nomatch hc
  | succ fc =>
    rw [Setlec.isDefEqCore_succ] at hc
    obtain ⟨ga, la, -, hla⟩ := whnf_peel h₁
    obtain ⟨gb, lb, -, hlb⟩ := whnf_peel h₂
    exact main fc Setlec.defeqLoopFuel hc
      (SubjInv.of_pair hwsa hba hLa hp)
      (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ hla hlb

/-- The slot-free shell: `EnsureSortAgreeR` as the `Q := True`
instance — trivial slot preservers, no hypothesis regression. -/
theorem ensureSortAgreeR_of {μ : CheckMode} {env : Env}
    {φ : Name → Nat}
    (hm : KnotFuelMono μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hP : ProbeSortVacuity μ env fun _ _ _ => True)
    (hR : RescueSortVacuity μ env fun _ _ _ => True)
    (hE : EtaSortVacuity μ env fun _ _ _ => True)
    (hN : NatStepNoSort μ env)
    (hS : SpineSortAgree μ env φ fun _ _ _ => True) :
    EnsureSortAgreeR μ env φ := by
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwsa hba hLa hwsb hbb hLb hp h₁ h₂
  exact ensureSortAgreeRQ_of (Q := fun _ _ _ => True) hm hIC hID hIN
    hLC hLD hLN
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun h => h)
    hP hR hE hN hS hc hwsa hba hLa hwsb hbb hLb hp trivial h₁ h₂


/-! ## `KnotFuelMono` discharge, batch 1: the oracle order and the helper tier

The obligation discharges by oracle-extension induction over
`coreKnot`: define success-extension between oracles, show every
body and helper respects it, chain up the knot.  Batch 1: the order
and the helpers below the bodies.  (`annotate` is in the order — the
bodies reach it through `isPropType` — even though the public
obligation omits it.) -/

/-- Success-extension: every successful call of `r₁` is reproduced
verbatim by `r₂`, on all five fields. -/
def CoreSub (r₁ r₂ : Setlec.CoreFns Setlec.CheckM) : Prop :=
  (∀ {d : Nat} {e x : Expr},
    r₁.whnfCore d e = .ok x → r₂.whnfCore d e = .ok x) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.whnf d e = .ok x → r₂.whnf d e = .ok x) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.infer d e = .ok x → r₂.infer d e = .ok x) ∧
  (∀ {d : Nat} {a b : Expr} {v : Bool},
    r₁.defeq d a b = .ok v → r₂.defeq d a b = .ok v) ∧
  (∀ {d : Nat} {e x : Expr},
    r₁.annotate d e = .ok x → r₂.annotate d e = .ok x)

section MonoHelpers
variable {env : Env} {r₁ r₂ : Setlec.CoreFns Setlec.CheckM}

/-- `ensureSort` respects the order. -/
theorem ensureSort_mono (hs : CoreSub r₁ r₂) {d : Nat} {e : Expr}
    {u : Level} (h : Setlec.ensureSort r₁ env d e = .ok u) :
    Setlec.ensureSort r₂ env d e = .ok u := by
  unfold Setlec.ensureSort at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hw : r₁.whnf d e with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
    rw [hw] at h
    rw [hs.2.1 hw]
    exact h

/-- `defEqList` respects the order. -/
theorem defEqList_mono (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {as bs : List Expr} {v : Bool},
      Setlec.defEqList r₁ env d as bs = .ok v →
      Setlec.defEqList r₂ env d as bs = .ok v := by
  intro as
  induction as with
  | nil => intro bs v h; cases bs <;> exact h
  | cons a as ih =>
    intro bs v h
    cases bs with
    | nil => exact h
    | cons b bs =>
      unfold Setlec.defEqList at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hd : r₁.defeq d a b with
      | error err => rw [hd] at h; exact nomatch h
      | ok c =>
        rw [hd] at h
        rw [hs.2.2.2.1 hd]
        cases c with
        | true => simpa using ih (by simpa using h)
        | false => exact h

/-- `reduceNat` respects the order (its only oracle use is whnf on
the arguments). -/
theorem reduceNat_mono (hs : CoreSub r₁ r₂) {d : Nat} {e : Expr}
    {o : Option Expr}
    (h : Setlec.reduceNat r₁ env d e = .ok o) :
    Setlec.reduceNat r₂ env d e = .ok o := by
  unfold Setlec.reduceNat at h ⊢
  split at h
  · -- unary shape `.app (.const c []) a`
    next c a =>
    by_cases h1 : c = Setlec.natSuccName ∧ Setlec.natLitSupported env
    · rw [if_pos h1] at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hw : r₁.whnf d a with
      | error err => rw [hw] at h; exact nomatch h
      | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : c = Setlec.natPredName ∧
          Setlec.natOpGuard env c = true
      · rw [if_pos h2] at h ⊢
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hw : r₁.whnf d a with
        | error err => rw [hw] at h; exact nomatch h
        | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
      · rw [if_neg h2] at h ⊢
        by_cases h3 : c = Setlec.natLog2Name ∧
            Setlec.natOpGuard env c = true
        · rw [if_pos h3] at h ⊢
          simp only [Bind.bind, Except.bind] at h ⊢
          cases hw : r₁.whnf d a with
          | error err => rw [hw] at h; exact nomatch h
          | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
        · rw [if_neg h3] at h ⊢
          by_cases h4 : c = Setlec.natLog2Name ∧
              Setlec.natLitSupported env
          · rw [if_pos h4] at h ⊢
            simp only [Bind.bind, Except.bind] at h ⊢
            cases hw : r₁.whnf d a with
            | error err => rw [hw] at h; exact nomatch h
            | ok w => rw [hw] at h; rw [hs.2.1 hw]; exact h
          · rw [if_neg h4] at h ⊢
            exact h
  · -- binary shape `.app (.app (.const c []) a) b`
    next c a b =>
    by_cases h1 : (c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
        c = Setlec.natMulName ∨ c = Setlec.natPowName ∨
        c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName) ∧
        Setlec.natOpGuard env c = true
    · rw [if_pos h1] at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hwa : r₁.whnf d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok wa =>
        rw [hwa] at h
        rw [hs.2.1 hwa]
        cases hwb : r₁.whnf d b with
        | error err => rw [hwb] at h; exact nomatch h
        | ok wb => rw [hwb] at h; rw [hs.2.1 hwb]; exact h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : Setlec.natOpWfNames.contains c ∧
          Setlec.natLitSupported env
      · rw [if_pos h2] at h ⊢
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hwa : r₁.whnf d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok wa =>
          rw [hwa] at h
          rw [hs.2.1 hwa]
          cases hwb : r₁.whnf d b with
          | error err => rw [hwb] at h; exact nomatch h
          | ok wb => rw [hwb] at h; rw [hs.2.1 hwb]; exact h
      · rw [if_neg h2] at h ⊢
        exact h
  · -- inert shapes
    exact h

/-- `whnfStep` respects the order (decompose, lift, reassemble). -/
theorem whnfStep_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {k₁ k₂ : Expr → Setlec.CheckM Expr}
    (hk : ∀ {e s : Expr}, k₁ e = .ok s → k₂ e = .ok s)
    {e s : Expr} (h : Setlec.whnfStep r₁ env d k₁ e = .ok s) :
    Setlec.whnfStep r₂ env d k₂ e = .ok s := by
  obtain ⟨e₁, hwc, hrest⟩ := whnfStep_decompose h
  rcases hrest with ⟨e₂, hrn, hkk⟩ | ⟨hrn, e₂, hud, hkk⟩ | ⟨hrn, hud, rfl⟩
  · exact whnfStep_assemble_nat (hs.1 hwc) (reduceNat_mono hs hrn)
      (hk hkk)
  · exact whnfStep_assemble_delta (hs.1 hwc) (reduceNat_mono hs hrn)
      hud (hk hkk)
  · exact whnfStep_assemble_stuck (hs.1 hwc) (reduceNat_mono hs hrn)
      hud

/-- `whnfLoop` respects the order at every budget. -/
theorem whnfLoop_mono (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {l : Nat} {e s : Expr},
      Setlec.whnfLoop r₁ env d l e = .ok s →
      Setlec.whnfLoop r₂ env d l e = .ok s := by
  intro l
  induction l with
  | zero => intro e s h; exact nomatch h
  | succ l ih =>
    intro e s h
    rw [whnfLoop_succ] at h
    rw [whnfLoop_succ]
    exact whnfStep_mono hs (fun hk => ih hk) h

end MonoHelpers

/-! ## Batch 2a: the cert-helper tier -/

section MonoHelpers2
variable {env : Env} {r₁ r₂ : Setlec.CoreFns Setlec.CheckM}

/-- `iotaCerts` respects the order. -/
theorem iotaCerts_mono (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {v : Bool},
      Setlec.iotaCerts r₁ env d ty args = .ok v →
      Setlec.iotaCerts r₂ env d ty args = .ok v := by
  intro args
  induction args with
  | nil => intro ty v h; exact h
  | cons a rest ih =>
    intro ty v h
    cases ty with
    | forallE n dom body bi =>
      unfold Setlec.iotaCerts at h ⊢
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hi : r₁.infer d a with
      | error err => rw [hi] at h; exact nomatch h
      | ok ta =>
        rw [hi] at h
        rw [hs.2.2.1 hi]
        simp only [] at h ⊢
        cases hd : r₁.defeq d ta dom with
        | error err => rw [hd] at h; exact nomatch h
        | ok c =>
          rw [hd] at h
          rw [hs.2.2.2.1 hd]
          simp only [] at h ⊢
          cases c with
          | true => simpa using ih (by simpa using h)
          | false => exact h
    | sort u => exact h
    | fvar i n ty => exact h
    | app f a' => exact h
    | lam n ty b m => exact h
    | letE n ty v' b => exact h
    | proj s i e => exact h
    | lit l => exact h
    | const n us => exact h
    | bvar i => exact h

/-- `defeqSpine` respects the order. -/
theorem defeqSpine_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {a b : Expr} {v : Bool}
    (h : Setlec.defeqSpine r₁ env d a b = .ok v) :
    Setlec.defeqSpine r₂ env d a b = .ok v := by
  unfold Setlec.defeqSpine at h ⊢
  cases hga : a.getAppFn with
  | const n us =>
    rw [hga] at h
    cases hgb : b.getAppFn with
    | const n' us' =>
      rw [hgb] at h
      simp only [] at h ⊢
      by_cases hcond : n = n' ∧
          a.getAppArgs.length = b.getAppArgs.length
      · rw [if_pos hcond] at h ⊢
        cases hle : Level.isEquivList us us' with
        | some c =>
          rw [hle] at h
          cases c with
          | true => exact defEqList_mono hs (by simpa using h)
          | false => exact h
        | none => rw [hle] at h; exact h
      · rw [if_neg hcond] at h ⊢; exact h
    | sort u => rw [hgb] at h; exact h
    | fvar i nm ty => rw [hgb] at h; exact h
    | forallE nm ty bd bi => rw [hgb] at h; exact h
    | lam nm ty bd m => rw [hgb] at h; exact h
    | letE nm ty vl bd => rw [hgb] at h; exact h
    | app f x => rw [hgb] at h; exact h
    | proj s i e => rw [hgb] at h; exact h
    | lit l => rw [hgb] at h; exact h
    | bvar i => rw [hgb] at h; exact h
  | sort u => rw [hga] at h; exact h
  | fvar i nm ty => rw [hga] at h; exact h
  | forallE nm ty bd bi => rw [hga] at h; exact h
  | lam nm ty bd m => rw [hga] at h; exact h
  | letE nm ty vl bd => rw [hga] at h; exact h
  | app f x => rw [hga] at h; exact h
  | proj s i e => rw [hga] at h; exact h
  | lit l => rw [hga] at h; exact h
  | bvar i => rw [hga] at h; exact h

/-- `projTeleCert` respects the order. -/
theorem projTeleCert_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {c : Name} {us : List Level} {args : List Expr} {v : Bool}
    (h : Setlec.projTeleCert r₁ env d c us args = .ok v) :
    Setlec.projTeleCert r₂ env d c us args = .ok v := by
  unfold Setlec.projTeleCert at h ⊢
  cases hf : env.find? c with
  | none => rw [hf] at h; exact h
  | some ci =>
    rw [hf] at h
    cases ci with
    | ctorInfo cvj na nb => exact iotaCerts_mono hs h
    | axiomInfo cv => exact h
    | defnInfo cv vl hint => exact h
    | thmInfo cv vl => exact h
    | indInfo cv caps => exact h
    | recInfo cv mi rp rules => exact h
    | projInfo entry => exact h

/-- `projLitToCtor` respects the order. -/
theorem projLitToCtor_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {e x : Expr}
    (h : Setlec.projLitToCtor r₁ env d e = .ok x) :
    Setlec.projLitToCtor r₂ env d e = .ok x := by
  cases e with
  | lit l =>
    cases l with
    | strVal s =>
      unfold Setlec.projLitToCtor at h ⊢
      simp only [] at h ⊢
      by_cases hsup : Setlec.strLitSupported env = true
      · rw [if_pos hsup] at h
        rw [if_pos hsup]
        exact hs.2.1 h
      · rw [if_neg hsup] at h
        rw [if_neg hsup]
        exact h
    | natVal n => exact h
  | sort u => exact h
  | fvar i n ty => exact h
  | app f a => exact h
  | lam n ty b m => exact h
  | letE n ty v' b => exact h
  | proj s i e' => exact h
  | const n us => exact h
  | forallE n ty b bi => exact h
  | bvar i => exact h

/-- `isPropType` respects the order (the `annotate` field's one
consumer). -/
theorem isPropType_mono (hs : CoreSub r₁ r₂) {d : Nat} {ty : Expr}
    {v : Bool} (h : Setlec.isPropType r₁ env d ty = .ok v) :
    Setlec.isPropType r₂ env d ty = .ok v := by
  unfold Setlec.isPropType at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases han : r₁.annotate d ty with
  | error err => rw [han] at h; exact nomatch h
  | ok ty' =>
    rw [han] at h
    rw [hs.2.2.2.2 han]
    simp only [] at h ⊢
    cases hi : r₁.infer d ty' with
    | error err => rw [hi] at h; exact nomatch h
    | ok t =>
      rw [hi] at h
      rw [hs.2.2.1 hi]
      simp only [] at h ⊢
      cases hes : Setlec.ensureSort r₁ env d t with
      | error err => rw [hes] at h; exact nomatch h
      | ok s =>
        rw [hes] at h
        rw [ensureSort_mono hs hes]
        simp only [] at h ⊢
        exact h


/-- `projCert` respects the order. -/
theorem projCert_mono (hs : CoreSub r₁ r₂) {d : Nat} {e₂ : Expr}
    {i : Nat} {fl sl : Level} {nP : Nat} {v : Bool}
    (h : Setlec.projCert r₁ env d e₂ i fl sl nP = .ok v) :
    Setlec.projCert r₂ env d e₂ i fl sl nP = .ok v := by
  unfold Setlec.projCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.infer d (e₂.getAppArgs.getD (nP + i) (.bvar 0)) with
  | error err => rw [h1] at h; exact nomatch h
  | ok ta =>
  rw [h1] at h; rw [hs.2.2.1 h1]
  simp only [] at h ⊢
  cases h2 : r₁.infer d ta with
  | error err => rw [h2] at h; exact nomatch h
  | ok tta =>
  rw [h2] at h; rw [hs.2.2.1 h2]
  simp only [] at h ⊢
  cases h3 : r₁.whnf d tta with
  | error err => rw [h3] at h; exact nomatch h
  | ok w =>
  rw [h3] at h; rw [hs.2.1 h3]
  simp only [] at h ⊢
  cases w with
  | sort uT =>
    simp only [] at h ⊢
    cases h4 : Setlec.liftFueled "level comparison"
        (Level.isEquiv uT fl) (m := Setlec.CheckM) with
    | error err => rw [h4] at h; exact nomatch h
    | ok okT =>
    rw [h4] at h
    simp only [] at h ⊢
    cases h5 : r₁.infer d e₂ with
    | error err => rw [h5] at h; exact nomatch h
    | ok te =>
    rw [h5] at h; rw [hs.2.2.1 h5]
    simp only [] at h ⊢
    cases h6 : r₁.infer d te with
    | error err => rw [h6] at h; exact nomatch h
    | ok tte =>
    rw [h6] at h; rw [hs.2.2.1 h6]
    simp only [] at h ⊢
    cases h7 : r₁.whnf d tte with
    | error err => rw [h7] at h; exact nomatch h
    | ok w₂ =>
    rw [h7] at h; rw [hs.2.1 h7]
    simp only [] at h ⊢
    exact h
  | fvar i' n ty => exact h
  | app f a => exact h
  | lam n ty b m => exact h
  | letE n ty v' b => exact h
  | proj s i' e => exact h
  | lit l => exact h
  | const n us => exact h
  | forallE n ty b bi => exact h
  | bvar i' => exact h


/-- `proofIrrel` respects the order. -/
theorem proofIrrel_mono (hs : CoreSub r₁ r₂) {d : Nat} {a b : Expr}
    {v : Bool} (h : Setlec.proofIrrel r₁ env d a b = .ok v) :
    Setlec.proofIrrel r₂ env d a b = .ok v := by
  unfold Setlec.proofIrrel at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.infer d a with
  | error err => rw [h1] at h; exact nomatch h
  | ok ta =>
  rw [h1] at h; rw [hs.2.2.1 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d ta with
  | error err => rw [h2] at h; exact nomatch h
  | ok wa =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  by_cases hu : Setlec.isUnitLikeTy env wa = true
  · rw [if_pos hu] at h ⊢
    cases h3 : r₁.infer d b with
    | error err => rw [h3] at h; exact nomatch h
    | ok tb =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    cases h4 : r₁.whnf d tb with
    | error err => rw [h4] at h; exact nomatch h
    | ok wb =>
    rw [h4] at h; rw [hs.2.1 h4]
    simp only [] at h ⊢
    exact h
  · rw [if_neg hu] at h ⊢
    cases h3 : r₁.infer d ta with
    | error err => rw [h3] at h; exact nomatch h
    | ok tta =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    cases h4 : r₁.whnf d tta with
    | error err => rw [h4] at h; exact nomatch h
    | ok w =>
    rw [h4] at h; rw [hs.2.1 h4]
    simp only [] at h ⊢
    cases w with
    | sort uT =>
      simp only [] at h ⊢
      cases h5 : Setlec.liftFueled "level comparison"
          (Level.isEquiv uT Level.zero) (m := Setlec.CheckM) with
      | error err => rw [h5] at h; exact nomatch h
      | ok okA =>
      rw [h5] at h
      simp only [] at h ⊢
      cases h6 : r₁.infer d b with
      | error err => rw [h6] at h; exact nomatch h
      | ok tb =>
      rw [h6] at h; rw [hs.2.2.1 h6]
      simp only [] at h ⊢
      cases h7 : r₁.infer d tb with
      | error err => rw [h7] at h; exact nomatch h
      | ok ttb =>
      rw [h7] at h; rw [hs.2.2.1 h7]
      simp only [] at h ⊢
      cases h8 : r₁.whnf d ttb with
      | error err => rw [h8] at h; exact nomatch h
      | ok w₂ =>
      rw [h8] at h; rw [hs.2.1 h8]
      simp only [] at h ⊢
      exact h
    | fvar i' n ty => exact h
    | app f a' => exact h
    | lam n ty b' m => exact h
    | letE n ty v' b' => exact h
    | proj s i' e => exact h
    | lit l => exact h
    | const n us => exact h
    | forallE n ty b' bi => exact h
    | bvar i' => exact h

/-- `etaCert` respects the order. -/
theorem etaCert_mono (hs : CoreSub r₁ r₂) {d : Nat} {n₁ : Name}
    {ty₁ body₁ : Expr} {m₁ : Setlec.BinderMeta} {b : Expr} {v : Bool}
    (h : Setlec.etaCert r₁ env d n₁ ty₁ body₁ m₁ b = .ok v) :
    Setlec.etaCert r₂ env d n₁ ty₁ body₁ m₁ b = .ok v := by
  unfold Setlec.etaCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.infer d b with
  | error err => rw [h1] at h; exact nomatch h
  | ok tb =>
  rw [h1] at h; rw [hs.2.2.1 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d tb with
  | error err => rw [h2] at h; exact nomatch h
  | ok w =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  cases w with
  | forallE n₂ ty₂ bd₂ m₂ =>
    simp only [] at h ⊢
    cases h3 : r₁.defeq d ty₂ ty₁ with
    | error err => rw [h3] at h; exact nomatch h
    | ok c =>
    rw [h3] at h; rw [hs.2.2.2.1 h3]
    simp only [] at h ⊢
    cases c with
    | true => exact hs.2.2.2.1 h
    | false => exact h
  | sort u => exact h
  | fvar i' n ty => exact h
  | app f a' => exact h
  | lam n ty b' m => exact h
  | letE n ty v' b' => exact h
  | proj s i' e => exact h
  | lit l => exact h
  | const n us => exact h
  | bvar i' => exact h

/-- `projParamCert` respects the order (an `iotaCerts` wrapper). -/
theorem projParamCert_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {entry : Setlec.ProjEntry} {us : List Level} {ps : List Expr}
    {v : Bool}
    (h : Setlec.projParamCert r₁ env d entry us ps = .ok v) :
    Setlec.projParamCert r₂ env d entry us ps = .ok v :=
  iotaCerts_mono hs h

/-- `structEtaProjCerts` respects the order. -/
theorem structEtaProjCerts_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
    {lpsT : List Name} :
    ∀ {idxs : List Nat} {v : Bool},
      Setlec.structEtaProjCerts r₁ env d T us' targs b lpsT idxs
        = .ok v →
      Setlec.structEtaProjCerts r₂ env d T us' targs b lpsT idxs
        = .ok v := by
  intro idxs
  induction idxs with
  | nil => intro v h; exact h
  | cons i rest ih =>
    intro v h
    unfold Setlec.structEtaProjCerts at h ⊢
    cases hf : env.find? (Setlec.projFnName T i) with
    | none => rw [hf] at h; exact h
    | some ci =>
      rw [hf] at h
      cases ci with
      | recInfo cvp mi rp rules =>
        simp only [] at h ⊢
        by_cases hg : cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (targs.length + 1)).isSome = true
        · rw [if_pos hg] at h ⊢
          simp only [Bind.bind, Except.bind] at h ⊢
          cases hic : Setlec.iotaCerts r₁ env d
              (cvp.type.instantiateLevelParams cvp.levelParams us')
              (targs ++ [b]) with
          | error err => rw [hic] at h; exact nomatch h
          | ok c =>
          rw [hic] at h; rw [iotaCerts_mono hs hic]
          simp only [] at h ⊢
          cases c with
          | true => exact ih h
          | false => exact h
        · rw [if_neg hg] at h ⊢; exact h
      | axiomInfo cv => exact h
      | defnInfo cv vl hint => exact h
      | thmInfo cv vl => exact h
      | indInfo cv caps => exact h
      | ctorInfo cv na nb => exact h
      | projInfo entry => exact h

/-- `pairEtaCert` respects the order (the split-both-sides recipe:
`split at h` handles compound patterns natively; the goal's matches
split into equation branches that unify with `h`'s or contradict). -/
theorem pairEtaCert_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b : Expr} {v : Bool}
    (h : Setlec.pairEtaCert μ r₁ env d a b = .ok v) :
    Setlec.pairEtaCert μ r₂ env d a b = .ok v := by
  unfold Setlec.pairEtaCert at h ⊢
  split at h
  · next c us pα pβ s₁ s₂ =>
    split at h
    · next cvm heq =>
      simp only [Bind.bind, Except.bind] at h ⊢
      cases h1 : r₁.infer d b with
      | error err => rw [h1] at h; exact nomatch h
      | ok tb =>
      rw [h1] at h; rw [hs.2.2.1 h1]
      simp only [] at h ⊢
      cases h2 : r₁.whnf d tb with
      | error err => rw [h2] at h; exact nomatch h
      | ok w =>
      rw [h2] at h; rw [hs.2.1 h2]
      simp only [] at h ⊢
      split at h
      · next c' us' A B =>
        split at h
        · next heq2 =>
          split at h
          · next cvr mI rP rr heq3 =>
            split at h
            · next hg =>
              rw [if_pos hg]
              cases h3 : Setlec.liftFueled "level comparison"
                  (Level.isEquivList us us') (m := Setlec.CheckM) with
              | error err => rw [h3] at h; exact nomatch h
              | ok c₃ =>
              rw [h3] at h
              simp only [] at h ⊢
              split at h
              · next hc₃ =>
                rw [if_pos hc₃]
                cases h4 : r₁.defeq d pα A with
                | error err => rw [h4] at h; exact nomatch h
                | ok c₄ =>
                rw [h4] at h; rw [hs.2.2.2.1 h4]
                simp only [] at h ⊢
                split at h
                · next hc₄ =>
                  rw [if_pos hc₄]
                  cases h5 : r₁.defeq d pβ B with
                  | error err => rw [h5] at h; exact nomatch h
                  | ok c₅ =>
                  rw [h5] at h; rw [hs.2.2.2.1 h5]
                  simp only [] at h ⊢
                  split at h
                  · next hc₅ =>
                    rw [if_pos hc₅]
                    cases h6 : r₁.defeq d s₁ (.proj c' 0 b) with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [hs.2.2.2.1 h6]
                    simp only [] at h ⊢
                    split at h
                    · next hc₆ =>
                      rw [if_pos hc₆]
                      cases h7 : r₁.defeq d s₂ (.proj c' 1 b) with
                      | error err => rw [h7] at h; exact nomatch h
                      | ok c₇ =>
                      rw [h7] at h; rw [hs.2.2.2.1 h7]
                      simp only [] at h ⊢
                      split at h
                      · next hc₇ =>
                        rw [if_pos hc₇]
                        split at h
                        · next htt =>
                          rw [if_pos htt]
                          split at h
                          · next entry heq4 =>
                            exact projParamCert_mono hs h
                          · exact h
                        · next htt =>
                          rw [if_neg htt]
                          exact h
                      · next hc₇ => rw [if_neg hc₇]; exact h
                    · next hc₆ => rw [if_neg hc₆]; exact h
                  · next hc₅ => rw [if_neg hc₅]; exact h
                · next hc₄ => rw [if_neg hc₄]; exact h
              · next hc₃ => rw [if_neg hc₃]; exact h
            · next hg => rw [if_neg hg]; exact h
          · next =>
            exact h
        · next =>
          exact h
      · next => exact h
    · next =>
      exact h
  · next => exact h

/-- `structUnitCert` respects the order. -/
theorem structUnitCert_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {a b : Expr} {v : Bool}
    (h : Setlec.structUnitCert r₁ env d a b = .ok v) :
    Setlec.structUnitCert r₂ env d a b = .ok v := by
  unfold Setlec.structUnitCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.infer d a with
  | error err => rw [h1] at h; exact nomatch h
  | ok ta =>
  rw [h1] at h; rw [hs.2.2.1 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d ta with
  | error err => rw [h2] at h; exact nomatch h
  | ok wta =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  split at h
  · next T us' =>
    split at h
    · next cvT caps heq =>
      split at h
      · next hg =>
        rw [if_pos hg]
        cases h3 : r₁.infer d b with
        | error err => rw [h3] at h; exact nomatch h
        | ok tb =>
        rw [h3] at h; rw [hs.2.2.1 h3]
        simp only [] at h ⊢
        cases h4 : r₁.whnf d tb with
        | error err => rw [h4] at h; exact nomatch h
        | ok wtb =>
        rw [h4] at h; rw [hs.2.1 h4]
        simp only [] at h ⊢
        cases h5 : r₁.defeq d wta wtb with
        | error err => rw [h5] at h; exact nomatch h
        | ok c₅ =>
        rw [h5] at h; rw [hs.2.2.2.1 h5]
        simp only [] at h ⊢
        cases c₅ with
        | true => exact iotaCerts_mono hs h
        | false => exact h
      · next hg => rw [if_neg hg]; exact h
    · next => exact h
  · next => exact h

/-- `structEtaCertWith` respects the order. -/
theorem structEtaCertWith_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b wtb : Expr} {v : Bool}
    (h : Setlec.structEtaCertWith μ r₁ env d a b wtb = .ok v) :
    Setlec.structEtaCertWith μ r₂ env d a b wtb = .ok v := by
  unfold Setlec.structEtaCertWith at h ⊢
  split at h
  · next c us hga =>
    split at h
    · next cvc cnP cnF heq =>
      split at h
      · next hlen =>
        rw [if_pos hlen]
        split at h
        · next T us' hgb =>
          split at h
          · next cvT caps heq2 =>
            split at h
            · next hg =>
              rw [if_pos hg]
              simp only [Bind.bind, Except.bind] at h ⊢
              cases h3 : Setlec.liftFueled "level comparison"
                  (Level.isEquivList us us') (m := Setlec.CheckM) with
              | error err => rw [h3] at h; exact nomatch h
              | ok c₃ =>
              rw [h3] at h
              simp only [] at h ⊢
              split at h
              · next hc₃ =>
                rw [if_pos hc₃]
                cases h4 : Setlec.iotaCerts r₁ env d
                    (cvT.type.instantiateLevelParams cvT.levelParams
                      us') wtb.getAppArgs with
                | error err => rw [h4] at h; exact nomatch h
                | ok c₄ =>
                rw [h4] at h; rw [iotaCerts_mono hs h4]
                simp only [] at h ⊢
                split at h
                · next hc₄ =>
                  rw [if_pos hc₄]
                  cases h5 : Setlec.structEtaProjCerts r₁ env d T us'
                      wtb.getAppArgs b cvT.levelParams
                      (List.range cnF) with
                  | error err => rw [h5] at h; exact nomatch h
                  | ok c₅ =>
                  rw [h5] at h; rw [structEtaProjCerts_mono hs h5]
                  simp only [] at h ⊢
                  split at h
                  · next hc₅ =>
                    rw [if_pos hc₅]
                    cases h6 : Setlec.defEqList r₁ env d
                        (a.getAppArgs.take cnP) wtb.getAppArgs with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [defEqList_mono hs h6]
                    simp only [] at h ⊢
                    split at h
                    · next hc₆ =>
                      rw [if_pos hc₆]
                      by_cases htt : μ.ttChecks = true
                      · rw [if_pos htt] at h ⊢
                        cases h7 : Setlec.iotaCerts r₁ env d
                            (cvc.type.instantiateLevelParams
                              cvc.levelParams us)
                            (wtb.getAppArgs ++
                              (List.range cnF).map fun i =>
                                Expr.mkAppN
                                  (.const (Setlec.projFnName T i) us')
                                  (wtb.getAppArgs ++ [b])) with
                        | error err => rw [h7] at h; exact nomatch h
                        | ok c₇ =>
                        rw [h7] at h; rw [iotaCerts_mono hs h7]
                        simp only [] at h ⊢
                        cases c₇ with
                        | true => exact defEqList_mono hs h
                        | false => exact h
                      · rw [if_neg htt] at h ⊢
                        exact defEqList_mono hs
                          (by simpa [pure, Except.pure] using h)
                    · next hc₆ => rw [if_neg hc₆]; exact h
                  · next hc₅ => rw [if_neg hc₅]; exact h
                · next hc₄ => rw [if_neg hc₄]; exact h
              · next hc₃ => rw [if_neg hc₃]; exact h
            · next hg => rw [if_neg hg]; exact h
          · next => exact h
        · next => exact h
      · next hlen => rw [if_neg hlen]; exact h
    · next => exact h
  · next => exact h

/-- `structEtaCert` respects the order. -/
theorem structEtaCert_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b : Expr} {v : Bool}
    (h : Setlec.structEtaCert μ r₁ env d a b = .ok v) :
    Setlec.structEtaCert μ r₂ env d a b = .ok v := by
  unfold Setlec.structEtaCert at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : r₁.infer d b with
  | error err => rw [h1] at h; exact nomatch h
  | ok tb =>
  rw [h1] at h; rw [hs.2.2.1 h1]
  simp only [] at h ⊢
  cases h2 : r₁.whnf d tb with
  | error err => rw [h2] at h; exact nomatch h
  | ok wtb =>
  rw [h2] at h; rw [hs.2.1 h2]
  simp only [] at h ⊢
  exact structEtaCertWith_mono hs h

/-- `stuckIrrel` respects the order. -/
theorem stuckIrrel_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {a b : Expr} {v : Bool}
    (h : Setlec.stuckIrrel μ r₁ env d a b = .ok v) :
    Setlec.stuckIrrel μ r₂ env d a b = .ok v := by
  unfold Setlec.stuckIrrel at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases h1 : Setlec.pairEtaCert μ r₁ env d a b with
  | error err => rw [h1] at h; exact nomatch h
  | ok c₁ =>
  rw [h1] at h; rw [pairEtaCert_mono hs h1]
  simp only [] at h ⊢
  cases c₁ with
  | true => exact h
  | false =>
  cases h2 : Setlec.pairEtaCert μ r₁ env d b a with
  | error err => rw [h2] at h; exact nomatch h
  | ok c₂ =>
  rw [h2] at h; rw [pairEtaCert_mono hs h2]
  simp only [] at h ⊢
  cases c₂ with
  | true => exact h
  | false =>
  cases h3 : Setlec.structEtaCert μ r₁ env d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok c₃ =>
  rw [h3] at h; rw [structEtaCert_mono hs h3]
  simp only [] at h ⊢
  cases c₃ with
  | true => exact h
  | false =>
  cases h4 : Setlec.structEtaCert μ r₁ env d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok c₄ =>
  rw [h4] at h; rw [structEtaCert_mono hs h4]
  simp only [] at h ⊢
  cases c₄ with
  | true => exact h
  | false =>
  cases h5 : Setlec.structUnitCert r₁ env d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok c₅ =>
  rw [h5] at h; rw [structUnitCert_mono hs h5]
  simp only [] at h ⊢
  cases c₅ with
  | true => exact h
  | false => exact proofIrrel_mono hs h

/-- `litMajorToCtor` respects the order. -/
theorem litMajorToCtor_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {e x : Expr}
    (h : Setlec.litMajorToCtor r₁ env d e = .ok x) :
    Setlec.litMajorToCtor r₂ env d e = .ok x := by
  cases e with
  | lit l =>
    cases l with
    | strVal s =>
      unfold Setlec.litMajorToCtor at h ⊢
      simp only [] at h ⊢
      by_cases hsup : Setlec.strLitSupported env = true
      · rw [if_pos hsup] at h
        rw [if_pos hsup]
        exact hs.2.1 h
      · rw [if_neg hsup] at h
        rw [if_neg hsup]
        exact h
    | natVal n => exact h
  | sort u => exact h
  | fvar i n ty => exact h
  | app f a => exact h
  | lam n ty b m => exact h
  | letE n ty v' b => exact h
  | proj s i e' => exact h
  | const n us => exact h
  | forallE n ty b bi => exact h
  | bvar i => exact h

/-- `majorToCtor` respects the order. -/
theorem majorToCtor_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {recName : Name} {rules : List Setlec.RecRule}
    {major x : Expr}
    (h : Setlec.majorToCtor μ r₁ env d recName rules major = .ok x) :
    Setlec.majorToCtor μ r₂ env d recName rules major = .ok x := by
  unfold Setlec.majorToCtor at h ⊢
  by_cases hca : Setlec.isCtorApp env major = true
  · rw [if_pos hca] at h ⊢; exact h
  rw [if_neg hca] at h ⊢
  split at h
  · next rl =>
    split at h
    · next cvj cnP cnF heq =>
      split at h
      · next T tus heq2 =>
        split at h
        · next cvT caps heq3 =>
          by_cases hK : caps.ruleK = true ∧ cnF = 0
          · rw [if_pos hK] at h ⊢
            simp only [Bind.bind, Except.bind] at h ⊢
            cases h1 : r₁.infer d major with
            | error err => rw [h1] at h; exact nomatch h
            | ok tm =>
            rw [h1] at h; rw [hs.2.2.1 h1]
            simp only [] at h ⊢
            cases h2 : r₁.whnf d tm with
            | error err => rw [h2] at h; exact nomatch h
            | ok tmaj =>
            rw [h2] at h; rw [hs.2.1 h2]
            simp only [] at h ⊢
            split at h
            · next T' ust heq4 =>
              split at h
              · next hg1 =>
                rw [if_pos hg1]
                split at h
                · next hg2 =>
                  rw [if_pos hg2]
                  split at h
                  · next hg3 =>
                    rw [if_pos hg3]
                    cases h3 : Setlec.iotaCerts r₁ env d
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (tmaj.getAppArgs.take cnP) with
                    | error err => rw [h3] at h; exact nomatch h
                    | ok c₃ =>
                    rw [h3] at h; rw [iotaCerts_mono hs h3]
                    simp only [] at h ⊢
                    cases c₃ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h4 : r₁.infer d (Expr.mkAppN
                        (.const rl.ctor ust)
                        (tmaj.getAppArgs.take cnP)) with
                    | error err => rw [h4] at h; exact nomatch h
                    | ok tf =>
                    rw [h4] at h; rw [hs.2.2.1 h4]
                    simp only [] at h ⊢
                    cases h5 : r₁.defeq d tmaj tf with
                    | error err => rw [h5] at h; exact nomatch h
                    | ok c₅ =>
                    rw [h5] at h; rw [hs.2.2.2.1 h5]
                    simp only [] at h ⊢
                    cases c₅ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h6 : Setlec.proofIrrel r₁ env d
                        (Expr.mkAppN (.const rl.ctor ust)
                          (tmaj.getAppArgs.take cnP)) major with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [proofIrrel_mono hs h6]
                    simp only [] at h ⊢
                    exact h
                  · next hg3 => rw [if_neg hg3]; exact h
                · next hg2 => rw [if_neg hg2]; exact h
              · next hg1 => rw [if_neg hg1]; exact h
            · next => exact h
          · rw [if_neg hK] at h ⊢
            by_cases hE : caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
                Setlec.Name.isProjFnShape recName = false
            · rw [if_pos hE] at h ⊢
              simp only [Bind.bind, Except.bind] at h ⊢
              cases h1 : r₁.infer d major with
              | error err => rw [h1] at h; exact nomatch h
              | ok tm =>
              rw [h1] at h; rw [hs.2.2.1 h1]
              simp only [] at h ⊢
              cases h2 : r₁.whnf d tm with
              | error err => rw [h2] at h; exact nomatch h
              | ok tmaj =>
              rw [h2] at h; rw [hs.2.1 h2]
              simp only [] at h ⊢
              split at h
              · next T' ust heq4 =>
                split at h
                · next hg1 =>
                  rw [if_pos hg1]
                  split at h
                  · next hg2 =>
                    rw [if_pos hg2]
                    split at h
                    · next hg3 =>
                      rw [if_pos hg3]
                      cases h3 : Setlec.iotaCerts r₁ env d
                          (cvj.type.instantiateLevelParams
                            cvj.levelParams ust)
                          (Setlec.etaFabArgs T ust tmaj.getAppArgs
                            major caps.etaFields) with
                      | error err => rw [h3] at h; exact nomatch h
                      | ok c₃ =>
                      rw [h3] at h; rw [iotaCerts_mono hs h3]
                      simp only [] at h ⊢
                      cases c₃ with
                      | false => exact h
                      | true =>
                      simp only [if_true] at h ⊢
                      cases h4 : Setlec.structEtaCertWith μ r₁ env d
                          (Expr.mkAppN (.const caps.etaCtor ust)
                            (Setlec.etaFabArgs T ust tmaj.getAppArgs
                              major caps.etaFields)) major tmaj with
                      | error err => rw [h4] at h; exact nomatch h
                      | ok c₄ =>
                      rw [h4] at h; rw [structEtaCertWith_mono hs h4]
                      simp only [] at h ⊢
                      cases c₄ with
                      | true => exact h
                      | false =>
                      simp only [Bool.false_eq_true, if_false] at h ⊢
                      split at h
                      · next hg4 =>
                        rw [if_pos hg4]
                        cases h5 : Setlec.proofIrrel r₁ env d
                            (Expr.mkAppN (.const caps.etaCtor ust)
                              (Setlec.etaFabArgs T ust
                                tmaj.getAppArgs major
                                caps.etaFields)) major with
                        | error err => rw [h5] at h; exact nomatch h
                        | ok c₅ =>
                        rw [h5] at h; rw [proofIrrel_mono hs h5]
                        simp only [] at h ⊢
                        exact h
                      · next hg4 => rw [if_neg hg4]; exact h
                    · next hg3 => rw [if_neg hg3]; exact h
                  · next hg2 => rw [if_neg hg2]; exact h
                · next hg1 => rw [if_neg hg1]; exact h
              · next => exact h
            · rw [if_neg hE] at h ⊢
              exact h
        · next => exact h
      · next => exact h
    · next => exact h
  · next => exact h

/-- `iotaRec` respects the order — the last helper. -/
theorem iotaRec_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {e : Expr} {o : Option Expr}
    (h : Setlec.iotaRec μ r₁ env d e = .ok o) :
    Setlec.iotaRec μ r₂ env d e = .ok o := by
  unfold Setlec.iotaRec at h ⊢
  split at h
  · next c us hga =>
    split at h
    · next cv mI rP rules heq =>
      dsimp only [] at h ⊢
      split at h
      · next hlen =>
        rw [if_pos hlen]
        simp only [Bind.bind, Except.bind] at h ⊢
        cases h1 : r₁.whnf d (e.getAppArgs.getD mI (.bvar 0)) with
        | error err => rw [h1] at h; exact nomatch h
        | ok major₀ =>
        rw [h1] at h; rw [hs.2.1 h1]
        simp only [] at h ⊢
        cases h2 : Setlec.litMajorToCtor r₁ env d major₀ with
        | error err => rw [h2] at h; exact nomatch h
        | ok major₁ =>
        rw [h2] at h; rw [litMajorToCtor_mono hs h2]
        simp only [] at h ⊢
        cases h3 : Setlec.majorToCtor μ r₁ env d c rules major₁ with
        | error err => rw [h3] at h; exact nomatch h
        | ok major =>
        rw [h3] at h; rw [majorToCtor_mono hs h3]
        simp only [] at h ⊢
        split at h
        · next cj usj hgm =>
          split at h
          · next cvj na nb heq2 =>
            split at h
            · next rl heq3 =>
              split at h
              · next hlen2 =>
                rw [if_pos hlen2]
                split at h
                · next hinert => exact nomatch h
                · next hinert =>
                  rw [if_neg hinert]
                  split at h
                  · next hg2 =>
                    rw [if_pos hg2]
                    cases h4 : Setlec.liftFueled "level comparison"
                        (Level.isEquivList usj
                          (Setlec.recFireComparands rl cv.levelParams
                            us cvj.levelParams e.getAppArgs rP).1)
                        (m := Setlec.CheckM) with
                    | error err => rw [h4] at h; exact nomatch h
                    | ok c₄ =>
                    rw [h4] at h
                    simp only [] at h ⊢
                    cases c₄ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h5 : Setlec.defEqList r₁ env d
                        (major.getAppArgs.take rl.ctorParams)
                        (Setlec.recFireComparands rl cv.levelParams
                          us cvj.levelParams e.getAppArgs rP).2 with
                    | error err => rw [h5] at h; exact nomatch h
                    | ok c₅ =>
                    rw [h5] at h; rw [defEqList_mono hs h5]
                    simp only [] at h ⊢
                    cases c₅ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h6 : Setlec.iotaCerts r₁ env d
                        (cv.type.instantiateLevelParams cv.levelParams
                          us)
                        (e.getAppArgs.take mI ++ [major]) with
                    | error err => rw [h6] at h; exact nomatch h
                    | ok c₆ =>
                    rw [h6] at h; rw [iotaCerts_mono hs h6]
                    simp only [] at h ⊢
                    cases c₆ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    cases h7 : Setlec.iotaCerts r₁ env d
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams usj)
                        major.getAppArgs with
                    | error err => rw [h7] at h; exact nomatch h
                    | ok c₇ =>
                    rw [h7] at h; rw [iotaCerts_mono hs h7]
                    simp only [] at h ⊢
                    cases c₇ with
                    | false => exact h
                    | true =>
                    simp only [if_true] at h ⊢
                    split at h
                    · next cbody residual heq4 heq5 =>
                      split at h
                      · next hcb =>
                        cases h8 : Setlec.defEqList r₁ env d
                            (residual.getAppArgs.drop rl.ctorParams)
                            ((e.getAppArgs.take mI).drop rP) with
                        | error err => rw [h8] at h; exact nomatch h
                        | ok c₈ =>
                        rw [h8] at h; rw [defEqList_mono hs h8]
                        simp only [] at h ⊢
                        exact h
                      · next => exact h
                    · next => exact h
                  · next hg2 => rw [if_neg hg2]; exact h
              · next hlen2 => rw [if_neg hlen2]; exact h
            · next => exact h
          · next => exact h
        · next => exact h
      · next hlen => rw [if_neg hlen]; exact h
    · next => exact h
  · next => exact h

/-- `projFieldDom` respects the order. -/
theorem projFieldDom_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {sp : Bool} {sn : Name} {e' : Expr} :
    ∀ {k j : Nat} {tel x : Expr},
      Setlec.projFieldDom r₁ env d sp sn e' j k tel = .ok x →
      Setlec.projFieldDom r₂ env d sp sn e' j k tel = .ok x := by
  intro k
  induction k with
  | zero => intro j tel x h; cases tel <;> exact h
  | succ k ih =>
    intro j tel x h
    cases tel with
    | forallE nm dom rest bi =>
      unfold Setlec.projFieldDom at h ⊢
      by_cases hb : rest.looseBVarsBounded 0 = true
      · rw [if_pos hb] at h ⊢
        exact ih h
      · rw [if_neg hb] at h ⊢
        by_cases hsp : sp = true
        · rw [if_pos hsp] at h ⊢
          simp only [Bind.bind, Except.bind] at h ⊢
          cases h1 : Setlec.isPropType r₁ env d dom with
          | error err => rw [h1] at h; exact nomatch h
          | ok b =>
          rw [h1] at h; rw [isPropType_mono hs h1]
          simp only [] at h ⊢
          cases b with
          | true => exact ih (by simpa using h)
          | false => exact h
        · rw [if_neg hsp] at h ⊢
          exact ih (by simpa [Bind.bind, Except.bind] using h)
    | sort u => exact h
    | fvar i n ty => exact h
    | app f a => exact h
    | lam n ty b m => exact h
    | letE n ty v b => exact h
    | proj s i e => exact h
    | lit l => exact h
    | const n us => exact h
    | bvar i => exact h

/-- `annotateProjRec` respects the order. -/
theorem annotateProjRec_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {entry : Setlec.ProjEntry} {i : Nat} {te e' : Expr}
    {us : List Level} {x : Expr}
    (h : Setlec.annotateProjRec r₁ env d entry i te e' us = .ok x) :
    Setlec.annotateProjRec r₂ env d entry i te e' us = .ok x := by
  unfold Setlec.annotateProjRec at h ⊢
  dsimp only [] at h ⊢
  split at h
  · next cvC nc cnF heq =>
    split at h
    · next hlen =>
      rw [if_pos hlen]
      split at h
      · next tel heq2 =>
        cases h1 : Setlec.isPropType r₁ env d te with
        | error err => rw [h1] at h; exact nomatch h
        | ok sp =>
        rw [h1] at h; rw [isPropType_mono hs h1]
        simp only [Bind.bind, Except.bind] at h ⊢
        cases h2 : Setlec.projFieldDom r₁ env d sp entry.structName e'
            0 i tel with
        | error err => rw [h2] at h; exact nomatch h
        | ok fi =>
        rw [h2] at h; rw [projFieldDom_mono hs h2]
        simp only [] at h ⊢
        split at h
        · next minor heq3 =>
          cases h3 : r₁.annotate d fi with
          | error err => rw [h3] at h; exact nomatch h
          | ok fi' =>
          rw [h3] at h; rw [hs.2.2.2.2 h3]
          simp only [] at h ⊢
          cases h4 : r₁.infer d fi' with
          | error err => rw [h4] at h; exact nomatch h
          | ok tfi =>
          rw [h4] at h; rw [hs.2.2.1 h4]
          simp only [] at h ⊢
          cases h5 : Setlec.ensureSort r₁ env d tfi with
          | error err => rw [h5] at h; exact nomatch h
          | ok sfi =>
          rw [h5] at h; rw [ensureSort_mono hs h5]
          simp only [] at h ⊢
          by_cases hsp : sp = true
          · rw [if_pos hsp] at h ⊢
            cases h6 : Setlec.liftFueled "level comparison"
                (Level.isEquiv sfi Level.zero)
                (m := Setlec.CheckM) with
            | error err => rw [h6] at h; exact nomatch h
            | ok c₆ =>
            rw [h6] at h
            simp only [] at h ⊢
            cases c₆ with
            | false => exact h
            | true =>
            simp only [if_true] at h ⊢
            split at h
            · next hre =>
              rw [if_pos hre]
              split at h
              · next hg => rw [if_pos hg]; exact hs.2.2.2.2 h
              · next hg => rw [if_neg hg]; exact h
            · next hre =>
              rw [if_neg hre]
              split at h
              · next hg => rw [if_pos hg]; exact hs.2.2.2.2 h
              · next hg => rw [if_neg hg]; exact h
          · rw [if_neg hsp] at h ⊢
            split at h
            · next hre =>
              rw [if_pos hre]
              split at h
              · next hg =>
                rw [if_pos hg]
                exact hs.2.2.2.2 (by simpa using h)
              · next hg => rw [if_neg hg]; exact h
            · next hre =>
              rw [if_neg hre]
              split at h
              · next hg =>
                rw [if_pos hg]
                exact hs.2.2.2.2 (by simpa using h)
              · next hg => rw [if_neg hg]; exact h
        · next => exact h
      · next => exact h
    · next hlen => rw [if_neg hlen]; exact h
  · next => exact h

/-- `annotateProjElim` respects the order. -/
theorem annotateProjElim_mono (hs : CoreSub r₁ r₂) {d : Nat}
    {sn : Name} {i : Nat} {te e' x : Expr}
    (h : Setlec.annotateProjElim r₁ env d sn i te e' = .ok x) :
    Setlec.annotateProjElim r₂ env d sn i te e' = .ok x := by
  unfold Setlec.annotateProjElim at h ⊢
  split at h
  · next T us hga =>
    by_cases hT : T = sn
    · rw [if_pos hT] at h ⊢
      split at h
      · next cvp mi rp rules heq =>
        split at h
        · next hlen =>
          rw [if_pos hlen]
          dsimp only [] at h ⊢
          split at h
          · next hg =>
            rw [if_pos hg]
            exact hs.2.2.2.2 h
          · next hg => rw [if_neg hg]; exact h
        · next hlen => rw [if_neg hlen]; exact h
      · next entry heq =>
        split at h
        · next hnat => exact nomatch h
        · next hnat =>
          rw [if_neg hnat]
          exact annotateProjRec_mono hs h
      · next => exact h
    · rw [if_neg hT] at h ⊢
      exact h
  · next => exact h

/-- `annotateBody` respects the order. -/
theorem annotateBody_mono (hs : CoreSub r₁ r₂) {d : Nat} {e x : Expr}
    (h : Setlec.annotateBody r₁ env d e = .ok x) :
    Setlec.annotateBody r₂ env d e = .ok x := by
  unfold Setlec.annotateBody at h ⊢
  cases e with
  | bvar i => exact h
  | fvar idx n ty => exact h
  | sort u => exact h
  | const n us => exact h
  | lit l => cases l <;> exact h
  | app f a =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok f' =>
    rw [h1] at h; rw [hs.2.2.2.2 h1]
    simp only [] at h ⊢
    cases h2 : r₁.annotate d a with
    | error err => rw [h2] at h; exact nomatch h
    | ok a' =>
    rw [h2] at h; rw [hs.2.2.2.2 h2]
    simp only [] at h ⊢
    exact h
  | forallE n ty body mb =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok ty' =>
    rw [h1] at h; rw [hs.2.2.2.2 h1]
    simp only [] at h ⊢
    cases h2 : r₁.annotate (d + 1)
        (body.instantiate1 (.fvar d n ty')) with
    | error err => rw [h2] at h; exact nomatch h
    | ok body' =>
    rw [h2] at h; rw [hs.2.2.2.2 h2]
    simp only [] at h ⊢
    exact h
  | lam n ty body mb =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok ty' =>
    rw [h1] at h; rw [hs.2.2.2.2 h1]
    simp only [] at h ⊢
    cases h2 : r₁.annotate (d + 1)
        (body.instantiate1 (.fvar d n ty')) with
    | error err => rw [h2] at h; exact nomatch h
    | ok body' =>
    rw [h2] at h; rw [hs.2.2.2.2 h2]
    simp only [] at h ⊢
    exact h
  | letE nm ty v b =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok ty' =>
    rw [h1] at h; rw [hs.2.2.2.2 h1]
    simp only [] at h ⊢
    cases h2 : r₁.infer d ty' with
    | error err => rw [h2] at h; exact nomatch h
    | ok tty =>
    rw [h2] at h; rw [hs.2.2.1 h2]
    simp only [] at h ⊢
    cases h3 : Setlec.ensureSort r₁ env d tty with
    | error err => rw [h3] at h; exact nomatch h
    | ok s =>
    rw [h3] at h; rw [ensureSort_mono hs h3]
    simp only [] at h ⊢
    cases h4 : r₁.annotate d v with
    | error err => rw [h4] at h; exact nomatch h
    | ok v' =>
    rw [h4] at h; rw [hs.2.2.2.2 h4]
    simp only [] at h ⊢
    cases h5 : r₁.infer d v' with
    | error err => rw [h5] at h; exact nomatch h
    | ok tv =>
    rw [h5] at h; rw [hs.2.2.1 h5]
    simp only [] at h ⊢
    cases h6 : r₁.defeq d tv ty' with
    | error err => rw [h6] at h; exact nomatch h
    | ok c₆ =>
    rw [h6] at h; rw [hs.2.2.2.1 h6]
    simp only [] at h ⊢
    cases c₆ with
    | false => exact h
    | true => exact hs.2.2.2.2 (by simpa using h)
  | proj sn i pe =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.annotate d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok e' =>
    rw [h1] at h; rw [hs.2.2.2.2 h1]
    simp only [] at h ⊢
    cases h2 : r₁.infer d e' with
    | error err => rw [h2] at h; exact nomatch h
    | ok te₀ =>
    rw [h2] at h; rw [hs.2.2.1 h2]
    simp only [] at h ⊢
    cases h3 : r₁.whnf d te₀ with
    | error err => rw [h3] at h; exact nomatch h
    | ok te =>
    rw [h3] at h; rw [hs.2.1 h3]
    simp only [] at h ⊢
    split at h
    · next T tus hga =>
      split at h
      · next entry heq =>
        split at h
        · next hnat =>
          rw [if_pos hnat]
          split at h
          · next hlen =>
            rw [if_pos hlen]
            exact h
          · next hlen => rw [if_neg hlen]; exact nomatch h
        · next hnat =>
          rw [if_neg hnat]
          exact annotateProjElim_mono hs h
      · next heq => exact annotateProjElim_mono hs h
    · next => exact annotateProjElim_mono hs h

/-- `whnfCoreBody` respects the order. -/
theorem whnfCoreBody_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {e x : Expr}
    (h : Setlec.whnfCoreBody μ r₁ env d e = .ok x) :
    Setlec.whnfCoreBody μ r₂ env d e = .ok x := by
  unfold Setlec.whnfCoreBody at h ⊢
  cases e with
  | sort u => exact h
  | fvar idx n ty => exact h
  | forallE n ty body bi => exact h
  | lam n ty body mb => exact h
  | const n us => exact h
  | lit l => exact h
  | bvar i => exact h
  | app f a =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.whnfCore d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok fw =>
    rw [h1] at h; rw [hs.1 h1]
    simp only [] at h ⊢
    split at h
    · next n₁ ty₁ body₁ mb₁ =>
      cases h2 : r₁.infer d a with
      | error err => rw [h2] at h; exact nomatch h
      | ok ta =>
      rw [h2] at h; rw [hs.2.2.1 h2]
      simp only [] at h ⊢
      cases h3 : r₁.defeq d ta ty₁ with
      | error err => rw [h3] at h; exact nomatch h
      | ok c₃ =>
      rw [h3] at h; rw [hs.2.2.2.1 h3]
      simp only [] at h ⊢
      cases c₃ with
      | true => exact hs.1 (by simpa using h)
      | false => exact h
    · next =>
      cases h2 : Setlec.iotaRec μ r₁ env d (.app fw a) with
      | error err => rw [h2] at h; exact nomatch h
      | ok o =>
      rw [h2] at h; rw [iotaRec_mono hs h2]
      simp only [] at h ⊢
      cases o with
      | some e₂ => exact hs.1 h
      | none => exact h
  | letE nm ty v b =>
    exact hs.1 h
  | proj sn i pe =>
    simp only [Bind.bind, Except.bind] at h ⊢
    cases h1 : r₁.whnf d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok w =>
    rw [h1] at h; rw [hs.2.1 h1]
    simp only [] at h ⊢
    cases h2 : Setlec.projLitToCtor r₁ env d w with
    | error err => rw [h2] at h; exact nomatch h
    | ok w₂ =>
    rw [h2] at h; rw [projLitToCtor_mono hs h2]
    simp only [] at h ⊢
    split at h
    · next entry heq =>
      split at h
      · next c us hga =>
        split at h
        · next hg =>
          rw [if_pos hg]
          cases h3 : Setlec.projCert r₁ env d w₂ i
              (Level.subst entry.levelParams us entry.fieldSort)
              (Level.subst entry.levelParams us entry.structSort)
              entry.numParams with
          | error err => rw [h3] at h; exact nomatch h
          | ok c₃ =>
          rw [h3] at h; rw [projCert_mono hs h3]
          simp only [] at h ⊢
          cases c₃ with
          | false => exact h
          | true =>
          simp only [if_true] at h ⊢
          by_cases htt : μ.ttChecks = true
          · rw [if_pos htt] at h ⊢
            cases h4 : Setlec.projTeleCert r₁ env d c us
                w₂.getAppArgs with
            | error err => rw [h4] at h; exact nomatch h
            | ok c₄ =>
            rw [h4] at h; rw [projTeleCert_mono hs h4]
            simp only [] at h ⊢
            cases c₄ with
            | true => exact hs.1 h
            | false => exact h
          · rw [if_neg htt] at h ⊢
            exact hs.1 (by simpa [pure, Except.pure] using h)
        · next hg => rw [if_neg hg]; exact h
      · next => exact h
    · next => exact h

/-- `inferBody` respects the order. -/
theorem inferBody_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {e x : Expr}
    (h : Setlec.inferBody μ r₁ env d e = .ok x) :
    Setlec.inferBody μ r₂ env d e = .ok x := by
  unfold Setlec.inferBody at h ⊢
  simp only [Setlec.viewM, Setlec.Expr.view, Bind.bind, Except.bind,
    pure, Except.pure] at h ⊢
  cases e with
  | sort u => exact h
  | fvar idx n ty => exact h
  | const n us => exact h
  | lit l => cases l <;> exact h
  | bvar i => exact h
  | forallE n ty body mb =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next u =>
      cases h3 : r₁.infer (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | error err => rw [h3] at h; exact nomatch h
      | ok tb =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      cases h4 : Setlec.ensureSort r₁ env (d + 1) tb with
      | error err => rw [h4] at h; exact nomatch h
      | ok v' =>
      rw [h4] at h; rw [ensureSort_mono hs h4]
      simp only [] at h ⊢
      exact h
    · next => exact h
  | lam n ty body mb =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next u =>
      cases h3 : r₁.infer (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | error err => rw [h3] at h; exact nomatch h
      | ok bt =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      by_cases hv : (μ.verified && !body.isLam) = true
      · rw [if_pos hv] at h ⊢
        cases h4 : r₁.infer (d + 1) bt with
        | error err => rw [h4] at h; exact nomatch h
        | ok btt =>
        rw [h4] at h; rw [hs.2.2.1 h4]
        simp only [] at h ⊢
        cases h5 : Setlec.ensureSort r₁ env (d + 1) btt with
        | error err => rw [h5] at h; exact nomatch h
        | ok s5 =>
        rw [h5] at h; rw [ensureSort_mono hs h5]
        simp only [] at h ⊢
        exact h
      · rw [if_neg hv] at h ⊢
        exact h
    · next => exact h
  | app f a =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d f with
    | error err => rw [h1] at h; exact nomatch h
    | ok tf =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tf with
    | error err => rw [h2] at h; exact nomatch h
    | ok w =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next n₁ ty₁ body₁ mt =>
      cases h3 : r₁.infer d a with
      | error err => rw [h3] at h; exact nomatch h
      | ok ta =>
      rw [h3] at h; rw [hs.2.2.1 h3]
      simp only [] at h ⊢
      cases h4 : r₁.defeq d ta ty₁ with
      | error err => rw [h4] at h; exact nomatch h
      | ok c₄ =>
      rw [h4] at h; rw [hs.2.2.2.1 h4]
      simp only [] at h ⊢
      cases c₄ with
      | true => simpa using h
      | false => exact h
    · next => exact h
  | proj sn i pe =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d pe with
    | error err => rw [h1] at h; exact nomatch h
    | ok tpe =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : r₁.whnf d tpe with
    | error err => rw [h2] at h; exact nomatch h
    | ok te =>
    rw [h2] at h; rw [hs.2.1 h2]
    simp only [] at h ⊢
    split at h
    · next T us hga =>
      split at h
      · next entry heq =>
        split at h
        · next hg =>
          rw [if_pos hg]
          by_cases htt : μ.ttChecks = true
          · rw [if_pos htt] at h ⊢
            cases h3 : Setlec.projParamCert r₁ env d entry us
                te.getAppArgs with
            | error err => rw [h3] at h; exact nomatch h
            | ok c₃ =>
            rw [h3] at h; rw [projParamCert_mono hs h3]
            simp only [] at h ⊢
            exact h
          · rw [if_neg htt] at h ⊢
            exact h
        · next hg => rw [if_neg hg]; exact h
      · next => exact h
    · next => exact h
  | letE nm ty v b =>
    simp only [] at h ⊢
    cases h1 : r₁.infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h; rw [hs.2.2.1 h1]
    simp only [] at h ⊢
    cases h2 : Setlec.ensureSort r₁ env d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok s2 =>
    rw [h2] at h; rw [ensureSort_mono hs h2]
    simp only [] at h ⊢
    cases h3 : r₁.infer d v with
    | error err => rw [h3] at h; exact nomatch h
    | ok tv =>
    rw [h3] at h; rw [hs.2.2.1 h3]
    simp only [] at h ⊢
    cases h4 : r₁.defeq d tv ty with
    | error err => rw [h4] at h; exact nomatch h
    | ok c₄ =>
    rw [h4] at h; rw [hs.2.2.2.1 h4]
    simp only [] at h ⊢
    cases c₄ with
    | true => exact hs.2.2.1 (by simpa using h)
    | false => exact h

/-- `defeqStep` respects the order — the last cascade. -/
theorem defeqStep_mono {μ : CheckMode} (hs : CoreSub r₁ r₂)
    {d : Nat} {k₁ k₂ : Expr → Expr → Setlec.CheckM Bool}
    (hk : ∀ {a b : Expr} {v : Bool},
      k₁ a b = .ok v → k₂ a b = .ok v)
    {a b : Expr} {v : Bool}
    (h : Setlec.defeqStep μ r₁ env d k₁ a b = .ok v) :
    Setlec.defeqStep μ r₂ env d k₂ a b = .ok v := by
  unfold Setlec.defeqStep at h ⊢
  by_cases hab : (a == b) = true
  · rw [if_pos hab] at h ⊢; exact h
  rw [if_neg hab] at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hwa : r₁.whnfCore d a with
  | error err => rw [hwa] at h; exact nomatch h
  | ok a' =>
  rw [hwa] at h; rw [hs.1 hwa]
  simp only [] at h ⊢
  cases hwb : r₁.whnfCore d b with
  | error err => rw [hwb] at h; exact nomatch h
  | ok b' =>
  rw [hwb] at h; rw [hs.1 hwb]
  simp only [] at h ⊢
  by_cases hab' : (a' == b') = true
  · rw [if_pos hab'] at h ⊢; exact h
  rw [if_neg hab'] at h ⊢
  cases hpi : Setlec.proofIrrel r₁ env d a' b' with
  | error err => rw [hpi] at h; exact nomatch h
  | ok cpi =>
  rw [hpi] at h; rw [proofIrrel_mono hs hpi]
  simp only [] at h ⊢
  cases cpi with
  | true => exact h
  | false =>
  simp only [Bool.false_eq_true, if_false] at h ⊢
  by_cases hg : (!a'.hasFvar && !b'.hasFvar) = true
  · rw [if_pos hg] at h ⊢
    cases hra : Setlec.reduceNat r₁ env d a' with
    | error err => rw [hra] at h; exact nomatch h
    | ok oa =>
    rw [hra] at h; rw [reduceNat_mono hs hra]
    simp only [] at h ⊢
    cases oa with
    | some a₂ => exact hk h
    | none =>
    rw [if_pos hg] at h ⊢
    cases hrb : Setlec.reduceNat r₁ env d b' with
    | error err => rw [hrb] at h; exact nomatch h
    | ok ob =>
    rw [hrb] at h; rw [reduceNat_mono hs hrb]
    simp only [] at h ⊢
    cases ob with
    | some b₂ => exact hk h
    | none =>
      cases hua : Setlec.unfoldableHead env a' <;>
        cases hub : Setlec.unfoldableHead env b' <;>
        rw [hua, hub] at h <;> simp only [] at h ⊢
      case true.false =>
        cases hud : Setlec.unfoldDefinition env a' with
        | some a₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      case false.true =>
        cases hud : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      case true.true =>
        by_cases hlt1 : (Setlec.headHint env b').lt
            (Setlec.headHint env a') = true
        · rw [if_pos hlt1] at h ⊢
          cases hud : Setlec.unfoldDefinition env a' with
          | some a₂ => rw [hud] at h; exact hk h
          | none => rw [hud] at h; exact h
        rw [if_neg hlt1] at h ⊢
        by_cases hlt2 : (Setlec.headHint env a').lt
            (Setlec.headHint env b') = true
        · rw [if_pos hlt2] at h ⊢
          cases hud : Setlec.unfoldDefinition env b' with
          | some b₂ => rw [hud] at h; exact hk h
          | none => rw [hud] at h; exact h
        rw [if_neg hlt2] at h ⊢
        by_cases hsr : ((Setlec.headHint env a').sameRegular
            (Setlec.headHint env b') && Setlec.sameConstHeads a' b') = true
        · rw [if_pos hsr] at h ⊢
          cases hsp : Setlec.defeqSpine r₁ env d a' b' with
          | error err => rw [hsp] at h; exact nomatch h
          | ok csp =>
          rw [hsp] at h; rw [defeqSpine_mono hs hsp]
          simp only [] at h ⊢
          cases csp with
          | true => exact h
          | false =>
          simp only [Bool.false_eq_true, if_false] at h ⊢
          cases hud1 : Setlec.unfoldDefinition env a' with
          | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
          | some a₂ =>
          rw [hud1] at h
          cases hud2 : Setlec.unfoldDefinition env b' with
          | some b₂ => rw [hud2] at h; exact hk h
          | none => rw [hud2] at h; exact h
        · rw [if_neg hsr] at h ⊢
          cases hud1 : Setlec.unfoldDefinition env a' with
          | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
          | some a₂ =>
          rw [hud1] at h
          cases hud2 : Setlec.unfoldDefinition env b' with
          | some b₂ => rw [hud2] at h; exact hk h
          | none => rw [hud2] at h; exact h
      case false.false =>
        split at h
        · next u v' => exact h
        · next l₁ l₂ => exact h
        · next n c us =>
          by_cases hc : (c = Setlec.natZeroName ∧ us = [])
          · rw [if_pos hc] at h ⊢; exact h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next c us n =>
          by_cases hc : (c = Setlec.natZeroName ∧ us = [])
          · rw [if_pos hc] at h ⊢; exact h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next nn f x =>
          split at h
          · next m c =>
            by_cases hc : c = Setlec.natSuccName
            · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
            · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
          · next => exact stuckIrrel_mono hs h
        · next f x nn =>
          split at h
          · next m c =>
            by_cases hc : c = Setlec.natSuccName
            · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
            · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
          · next => exact stuckIrrel_mono hs h
        · next st cO usO x =>
          by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
              Setlec.strLitSupported env)
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next cO usO x st =>
          by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
              Setlec.strLitSupported env)
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next i n₁ ty₁ j n₂ ty₂ =>
          by_cases hij : (i == j) = true
          · rw [if_pos hij] at h ⊢; exact h
          · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
        · next n us n' us' =>
          by_cases hn : n = n'
          · rw [if_pos hn] at h ⊢
            cases hle : Setlec.liftFueled "level comparison"
                (Level.isEquivList us us') (m := Setlec.CheckM) with
            | error err => rw [hle] at h; exact nomatch h
            | ok cle =>
            rw [hle] at h
            simp only [] at h ⊢
            cases cle with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
          · rw [if_neg hn] at h ⊢; exact stuckIrrel_mono hs h
        · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
          cases hd1 : r₁.defeq d ty₁ ty₂ with
          | error err => rw [hd1] at h; exact nomatch h
          | ok c₁ =>
          rw [hd1] at h; rw [hs.2.2.2.1 hd1]
          simp only [] at h ⊢
          cases c₁ with
          | false => exact h
          | true => exact hs.2.2.2.1 (by simpa using h)
        · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
          cases hd1 : r₁.defeq d ty₁ ty₂ with
          | error err => rw [hd1] at h; exact nomatch h
          | ok c₁ =>
          rw [hd1] at h; rw [hs.2.2.2.1 hd1]
          simp only [] at h ⊢
          cases c₁ with
          | false => exact h
          | true => exact hs.2.2.2.1 (by simpa using h)
        · next f₁ a₁ f₂ a₂ =>
          by_cases hlen : (Expr.app f₁ a₁).getAppArgs.length =
              (Expr.app f₂ a₂).getAppArgs.length
          · rw [if_pos hlen] at h ⊢
            cases hdf : r₁.defeq d (Expr.app f₁ a₁).getAppFn
                (Expr.app f₂ a₂).getAppFn with
            | error err => rw [hdf] at h; exact nomatch h
            | ok cdf =>
            rw [hdf] at h; rw [hs.2.2.2.1 hdf]
            simp only [] at h ⊢
            cases cdf with
            | false =>
              simp only [Bool.false_eq_true, if_false] at h ⊢
              exact stuckIrrel_mono hs h
            | true =>
            simp only [if_true] at h ⊢
            cases hdl : Setlec.defEqList r₁ env d
                (Expr.app f₁ a₁).getAppArgs
                (Expr.app f₂ a₂).getAppArgs with
            | error err => rw [hdl] at h; exact nomatch h
            | ok cdl =>
            rw [hdl] at h; rw [defEqList_mono hs hdl]
            simp only [] at h ⊢
            cases cdl with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
          · rw [if_neg hlen] at h ⊢; exact stuckIrrel_mono hs h
        · next s₁ i₁ e₁ s₂ i₂ e₂ =>
          by_cases hij : (i₁ == i₂) = true
          · rw [if_pos hij] at h ⊢
            cases hd1 : r₁.defeq d e₁ e₂ with
            | error err => rw [hd1] at h; exact nomatch h
            | ok c₁ =>
            rw [hd1] at h; rw [hs.2.2.2.1 hd1]
            simp only [] at h ⊢
            cases c₁ with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
          · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
        · next =>
          split at h
          · exact nomatch h
          · next ce he =>
            rw [etaCert_mono hs he]
            cases ce with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
        · next =>
          split at h
          · exact nomatch h
          · next ce he =>
            rw [etaCert_mono hs he]
            cases ce with
            | true => exact h
            | false => exact stuckIrrel_mono hs h
        · next => exact stuckIrrel_mono hs h
  · rw [if_neg hg] at h ⊢
    rw [if_neg hg] at h ⊢
    simp only [pure, Except.pure] at h ⊢
    cases hua : Setlec.unfoldableHead env a' <;>
      cases hub : Setlec.unfoldableHead env b' <;>
      rw [hua, hub] at h <;> simp only [] at h ⊢
    case true.false =>
      cases hud : Setlec.unfoldDefinition env a' with
      | some a₂ => rw [hud] at h; exact hk h
      | none => rw [hud] at h; exact h
    case false.true =>
      cases hud : Setlec.unfoldDefinition env b' with
      | some b₂ => rw [hud] at h; exact hk h
      | none => rw [hud] at h; exact h
    case true.true =>
      by_cases hlt1 : (Setlec.headHint env b').lt
          (Setlec.headHint env a') = true
      · rw [if_pos hlt1] at h ⊢
        cases hud : Setlec.unfoldDefinition env a' with
        | some a₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      rw [if_neg hlt1] at h ⊢
      by_cases hlt2 : (Setlec.headHint env a').lt
          (Setlec.headHint env b') = true
      · rw [if_pos hlt2] at h ⊢
        cases hud : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud] at h; exact hk h
        | none => rw [hud] at h; exact h
      rw [if_neg hlt2] at h ⊢
      by_cases hsr : ((Setlec.headHint env a').sameRegular
          (Setlec.headHint env b') && Setlec.sameConstHeads a' b') = true
      · rw [if_pos hsr] at h ⊢
        cases hsp : Setlec.defeqSpine r₁ env d a' b' with
        | error err => rw [hsp] at h; exact nomatch h
        | ok csp =>
        rw [hsp] at h; rw [defeqSpine_mono hs hsp]
        simp only [] at h ⊢
        cases csp with
        | true => exact h
        | false =>
        simp only [Bool.false_eq_true, if_false] at h ⊢
        cases hud1 : Setlec.unfoldDefinition env a' with
        | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
        | some a₂ =>
        rw [hud1] at h
        cases hud2 : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud2] at h; exact hk h
        | none => rw [hud2] at h; exact h
      · rw [if_neg hsr] at h ⊢
        cases hud1 : Setlec.unfoldDefinition env a' with
        | none => rw [hud1] at h; cases hud2 : Setlec.unfoldDefinition env b' <;> rw [hud2] at h <;> exact h
        | some a₂ =>
        rw [hud1] at h
        cases hud2 : Setlec.unfoldDefinition env b' with
        | some b₂ => rw [hud2] at h; exact hk h
        | none => rw [hud2] at h; exact h
    case false.false =>
      split at h
      · next u v' => exact h
      · next l₁ l₂ => exact h
      · next n c us =>
        by_cases hc : (c = Setlec.natZeroName ∧ us = [])
        · rw [if_pos hc] at h ⊢; exact h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next c us n =>
        by_cases hc : (c = Setlec.natZeroName ∧ us = [])
        · rw [if_pos hc] at h ⊢; exact h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next nn f x =>
        split at h
        · next m c =>
          by_cases hc : c = Setlec.natSuccName
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next => exact stuckIrrel_mono hs h
      · next f x nn =>
        split at h
        · next m c =>
          by_cases hc : c = Setlec.natSuccName
          · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
          · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
        · next => exact stuckIrrel_mono hs h
      · next st cO usO x =>
        by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
            Setlec.strLitSupported env)
        · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next cO usO x st =>
        by_cases hc : (cO = Setlec.stringOfListName ∧ usO = [] ∧
            Setlec.strLitSupported env)
        · rw [if_pos hc] at h ⊢; exact hs.2.2.2.1 h
        · rw [if_neg hc] at h ⊢; exact stuckIrrel_mono hs h
      · next i n₁ ty₁ j n₂ ty₂ =>
        by_cases hij : (i == j) = true
        · rw [if_pos hij] at h ⊢; exact h
        · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
      · next n us n' us' =>
        by_cases hn : n = n'
        · rw [if_pos hn] at h ⊢
          cases hle : Setlec.liftFueled "level comparison"
              (Level.isEquivList us us') (m := Setlec.CheckM) with
          | error err => rw [hle] at h; exact nomatch h
          | ok cle =>
          rw [hle] at h
          simp only [] at h ⊢
          cases cle with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
        · rw [if_neg hn] at h ⊢; exact stuckIrrel_mono hs h
      · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
        cases hd1 : r₁.defeq d ty₁ ty₂ with
        | error err => rw [hd1] at h; exact nomatch h
        | ok c₁ =>
        rw [hd1] at h; rw [hs.2.2.2.1 hd1]
        simp only [] at h ⊢
        cases c₁ with
        | false => exact h
        | true => exact hs.2.2.2.1 (by simpa using h)
      · next n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ =>
        cases hd1 : r₁.defeq d ty₁ ty₂ with
        | error err => rw [hd1] at h; exact nomatch h
        | ok c₁ =>
        rw [hd1] at h; rw [hs.2.2.2.1 hd1]
        simp only [] at h ⊢
        cases c₁ with
        | false => exact h
        | true => exact hs.2.2.2.1 (by simpa using h)
      · next f₁ a₁ f₂ a₂ =>
        by_cases hlen : (Expr.app f₁ a₁).getAppArgs.length =
            (Expr.app f₂ a₂).getAppArgs.length
        · rw [if_pos hlen] at h ⊢
          cases hdf : r₁.defeq d (Expr.app f₁ a₁).getAppFn
              (Expr.app f₂ a₂).getAppFn with
          | error err => rw [hdf] at h; exact nomatch h
          | ok cdf =>
          rw [hdf] at h; rw [hs.2.2.2.1 hdf]
          simp only [] at h ⊢
          cases cdf with
          | false =>
            simp only [Bool.false_eq_true, if_false] at h ⊢
            exact stuckIrrel_mono hs h
          | true =>
          simp only [if_true] at h ⊢
          cases hdl : Setlec.defEqList r₁ env d
              (Expr.app f₁ a₁).getAppArgs
              (Expr.app f₂ a₂).getAppArgs with
          | error err => rw [hdl] at h; exact nomatch h
          | ok cdl =>
          rw [hdl] at h; rw [defEqList_mono hs hdl]
          simp only [] at h ⊢
          cases cdl with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
        · rw [if_neg hlen] at h ⊢; exact stuckIrrel_mono hs h
      · next s₁ i₁ e₁ s₂ i₂ e₂ =>
        by_cases hij : (i₁ == i₂) = true
        · rw [if_pos hij] at h ⊢
          cases hd1 : r₁.defeq d e₁ e₂ with
          | error err => rw [hd1] at h; exact nomatch h
          | ok c₁ =>
          rw [hd1] at h; rw [hs.2.2.2.1 hd1]
          simp only [] at h ⊢
          cases c₁ with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
        · rw [if_neg hij] at h ⊢; exact stuckIrrel_mono hs h
      · next =>
        split at h
        · exact nomatch h
        · next ce he =>
          rw [etaCert_mono hs he]
          cases ce with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
      · next =>
        split at h
        · exact nomatch h
        · next ce he =>
          rw [etaCert_mono hs he]
          cases ce with
          | true => exact h
          | false => exact stuckIrrel_mono hs h
      · next => exact stuckIrrel_mono hs h

/-- `defeqLoop` respects the order at every budget. -/
theorem defeqLoop_mono {μ : CheckMode} (hs : CoreSub r₁ r₂) {d : Nat} :
    ∀ {l : Nat} {a b : Expr} {v : Bool},
      Setlec.defeqLoop μ r₁ env d l a b = .ok v →
      Setlec.defeqLoop μ r₂ env d l a b = .ok v := by
  intro l
  induction l with
  | zero => intro a b v h; exact nomatch h
  | succ l ih =>
    intro a b v h
    rw [defeqLoop_succ] at h
    rw [defeqLoop_succ]
    exact defeqStep_mono hs (fun hk => ih hk) h

end MonoHelpers2

/-! ## The knot chain and the public projection -/

/-- `CoreSub` is transitive. -/
theorem CoreSub.trans {r₁ r₂ r₃ : Setlec.CoreFns Setlec.CheckM}
    (h₁ : CoreSub r₁ r₂) (h₂ : CoreSub r₂ r₃) : CoreSub r₁ r₃ :=
  ⟨fun h => h₂.1 (h₁.1 h),
   fun h => h₂.2.1 (h₁.2.1 h),
   fun h => h₂.2.2.1 (h₁.2.2.1 h),
   fun h => h₂.2.2.2.1 (h₁.2.2.2.1 h),
   fun h => h₂.2.2.2.2 (h₁.2.2.2.2 h)⟩

/-- One knot level: the oracle at fuel `f` extends into fuel `f+1`. -/
theorem coreSub_succ (μ : CheckMode) (env : Env) :
    ∀ f : Nat, CoreSub (Setlec.pureFns μ env f)
      (Setlec.pureFns μ env (f + 1)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e x h; exact nomatch h
    · intro d e x h; exact nomatch h
    · intro d e x h; exact nomatch h
    · intro d a b v h; exact nomatch h
    · intro d e x h; exact nomatch h
  | succ f ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e x h
      exact whnfCoreBody_mono ih h
    · intro d e x h
      exact whnfLoop_mono ih h
    · intro d e x h
      exact inferBody_mono ih h
    · intro d a b v h
      exact defeqLoop_mono ih h
    · intro d e x h
      exact annotateBody_mono ih h

/-- The chain: fuel-gap induction. -/
theorem coreSub_le (μ : CheckMode) (env : Env) :
    ∀ {f f' : Nat}, f ≤ f' →
      CoreSub (Setlec.pureFns μ env f) (Setlec.pureFns μ env f') := by
  intro f f' hle
  induction f' with
  | zero =>
    obtain rfl : f = 0 := Nat.le_zero.mp hle
    exact ⟨fun h => h, fun h => h, fun h => h, fun h => h, fun h => h⟩
  | succ f' ih =>
    rcases Nat.lt_or_ge f (f' + 1) with hlt | hge
    · exact CoreSub.trans (ih (Nat.lt_succ_iff.mp hlt))
        (coreSub_succ μ env f')
    · obtain rfl : f = f' + 1 := Nat.le_antisymm hle hge
      exact ⟨fun h => h, fun h => h, fun h => h, fun h => h, fun h => h⟩

/-- **`KnotFuelMono` LANDS**: the carried obligation is a theorem.
Every lemma that hypothesized it — the dual shell
(`ensureSortAgreeR_of`), the run-threaded re-idem
(`whnfCore_reidem_const`), the loop algebra (`whnfLoop_r_mono`,
`whnfLoop_det`, `loop_stuck_out`, `loop_align`), the cross-fuel sort
determinism (`sortOfE_fuelDet` via `KnotFuelDet_of_mono`) — now
closes with this theorem in the slot. -/
theorem knotFuelMono (μ : CheckMode) (env : Env) : KnotFuelMono μ env := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f f' d e t hle h
    exact (coreSub_le μ env hle).2.2.1 h
  · intro f f' d e t hle h
    exact (coreSub_le μ env hle).2.1 h
  · intro f f' d e t hle h
    exact (coreSub_le μ env hle).1 h
  · intro f f' d a b v hle h
    exact (coreSub_le μ env hle).2.2.2.1 h
  · intro f f' d e o hle h
    exact reduceNat_mono (coreSub_le μ env hle) h

/-- The determinism corollary, now unconditional. -/
theorem knotFuelDet (μ : CheckMode) (env : Env) : KnotFuelDet μ env :=
  KnotFuelDet_of_mono (knotFuelMono μ env)

/-- **The payoff**: the dual shell conditioned on the five routings
alone — the wide obligation's slot is filled by the theorem.  (The
same instantiation closes `whnfCore_reidem_const`, `whnfLoop_r_mono`,
`whnfLoop_det`, `loop_stuck_out`, `loop_align`, `whnf_sort_out`,
`sortOfE_sort_out`, `sortOfE_fuelDet`, `unitBranch_absurd`,
`SortOfLE_det`, and `EnsureSortAgreeR_of_link` at their `hm`/`hdet`
slots.) -/
theorem ensureSortAgreeR_of_vacuities {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) (hN : NatStepNoSort μ env)
    (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  ensureSortAgreeRQ_of (Q := Q) (knotFuelMono μ env) hIC hID hIN
    hLC hLD hLN hQC hQD hQN hQs hP hR hE hN hS

/-! ## The nat-chase discharge -/

/-- The env-side fact the chase needs (ledger; install-tier supplier):
the comparison ops' output constants are delta-inert. -/
def BoolCtorsInert (env : Env) : Prop :=
  Setlec.unfoldDefinition env (.const Setlec.boolTrueName []) = none ∧
  Setlec.unfoldDefinition env (.const Setlec.boolFalseName []) = none

/-- Literals re-core to themselves (value branch). -/
theorem whnfCore_lit_run {μ : CheckMode} {env : Env} {f d : Nat}
    {l : Setlec.Literal} (hf : 1 ≤ f) :
    whnfCore μ env f d (.lit l) = .ok (.lit l) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- Constants re-core to themselves (value branch). -/
theorem whnfCore_const_run {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {us : List Level} (hf : 1 ≤ f) :
    whnfCore μ env f d (.const n us) = .ok (.const n us) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- `natOpResult` outputs are literals or the two `Bool` constants. -/
theorem natOpResult_shape {c : Name} {a b : Nat} {e : Expr}
    (h : Setlec.natOpResult c a b = some e) :
    (∃ n, e = .lit (.natVal n)) ∨
      e = .const Setlec.boolTrueName [] ∨
      e = .const Setlec.boolFalseName [] := by
  rw [Setlec.natOpResult.eq_def] at h
  by_cases h1 : c = Setlec.natPredName
  · rw [if_pos h1] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h1] at h
  by_cases h2 : c = Setlec.natAddName
  · rw [if_pos h2] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h2] at h
  by_cases h3 : c = Setlec.natSubName
  · rw [if_pos h3] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h3] at h
  by_cases h4 : c = Setlec.natMulName
  · rw [if_pos h4] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h4] at h
  by_cases h5 : c = Setlec.natPowName
  · rw [if_pos h5] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h5] at h
  by_cases h6 : c = Setlec.natDivName
  · rw [if_pos h6] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h6] at h
  by_cases h7 : c = Setlec.natModName
  · rw [if_pos h7] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h7] at h
  by_cases h8 : c = Setlec.natGcdName
  · rw [if_pos h8] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h8] at h
  by_cases h9 : c = Setlec.natLandName
  · rw [if_pos h9] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h9] at h
  by_cases h10 : c = Setlec.natLorName
  · rw [if_pos h10] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h10] at h
  by_cases h11 : c = Setlec.natXorName
  · rw [if_pos h11] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h11] at h
  by_cases h12 : c = Setlec.natShiftLeftName
  · rw [if_pos h12] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h12] at h
  by_cases h13 : c = Setlec.natShiftRightName
  · rw [if_pos h13] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h13] at h
  by_cases h14 : c = Setlec.natLog2Name
  · rw [if_pos h14] at h
    exact .inl ⟨_, (Option.some.inj h).symm⟩
  rw [if_neg h14] at h
  by_cases hbeq : c = Setlec.natBeqName
  · rw [if_pos hbeq] at h
    by_cases hab : a = b
    · rw [if_pos hab] at h
      exact .inr (.inl (Option.some.inj h).symm)
    · rw [if_neg hab] at h
      exact .inr (.inr (Option.some.inj h).symm)
  rw [if_neg hbeq] at h
  by_cases hble : c = Setlec.natBleName
  · rw [if_pos hble] at h
    by_cases hab : a ≤ b
    · rw [if_pos hab] at h
      exact .inr (.inl (Option.some.inj h).symm)
    · rw [if_neg hab] at h
      exact .inr (.inr (Option.some.inj h).symm)
  rw [if_neg hble] at h
  exact nomatch h

/-- `reduceNat`'s rewrites are literals or the two `Bool`
constants. -/
theorem reduceNat_some_shape {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e x : Expr}
    (h : Setlec.reduceNat r env d e = .ok (some x)) :
    (∃ n, x = .lit (.natVal n)) ∨
      x = .const Setlec.boolTrueName [] ∨
      x = .const Setlec.boolFalseName [] := by
  unfold Setlec.reduceNat at h
  split at h
  · next c a =>
    by_cases h1 : c = Setlec.natSuccName ∧ Setlec.natLitSupported env
    · rw [if_pos h1] at h
      simp only [Bind.bind, Except.bind] at h
      cases hw : r.whnf d a with
      | error err => rw [hw] at h; exact nomatch h
      | ok w =>
        rw [hw] at h
        simp only [] at h
        split at h
        · next n heq =>
          obtain rfl := (Option.some.inj (Except.ok.inj h)).symm
          exact .inl ⟨_, rfl⟩
        · exact nomatch h
    · rw [if_neg h1] at h
      by_cases h2 : c = Setlec.natPredName ∧
          Setlec.natOpGuard env c = true
      · rw [if_pos h2] at h
        simp only [Bind.bind, Except.bind] at h
        cases hw : r.whnf d a with
        | error err => rw [hw] at h; exact nomatch h
        | ok w =>
          rw [hw] at h
          simp only [] at h
          split at h
          · next n heq => exact natOpResult_shape (Except.ok.inj h)
          · exact nomatch h
      · rw [if_neg h2] at h
        by_cases h3 : c = Setlec.natLog2Name ∧
            Setlec.natOpGuard env c = true
        · rw [if_pos h3] at h
          simp only [Bind.bind, Except.bind] at h
          cases hw : r.whnf d a with
          | error err => rw [hw] at h; exact nomatch h
          | ok w =>
            rw [hw] at h
            simp only [] at h
            split at h
            · next n heq => exact natOpResult_shape (Except.ok.inj h)
            · exact nomatch h
        · rw [if_neg h3] at h
          by_cases h4 : c = Setlec.natLog2Name ∧
              Setlec.natLitSupported env
          · rw [if_pos h4] at h
            simp only [Bind.bind, Except.bind] at h
            cases hw : r.whnf d a with
            | error err => rw [hw] at h; exact nomatch h
            | ok w =>
              rw [hw] at h
              simp only [] at h
              split at h
              · next n heq => exact nomatch h
              · exact nomatch h
          · rw [if_neg h4] at h
            exact nomatch h
  · next c a b =>
    by_cases h1 : (c = Setlec.natAddName ∨ c = Setlec.natSubName ∨
        c = Setlec.natMulName ∨ c = Setlec.natPowName ∨
        c = Setlec.natBeqName ∨ c = Setlec.natBleName ∨
        c = Setlec.natDivName ∨ c = Setlec.natModName ∨
        c = Setlec.natGcdName ∨ c = Setlec.natLandName ∨
        c = Setlec.natLorName ∨ c = Setlec.natXorName ∨
        c = Setlec.natShiftLeftName ∨ c = Setlec.natShiftRightName) ∧
        Setlec.natOpGuard env c = true
    · rw [if_pos h1] at h
      simp only [Bind.bind, Except.bind] at h
      cases hwa : r.whnf d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok wa =>
        rw [hwa] at h
        simp only [] at h
        cases hwb : r.whnf d b with
        | error err => rw [hwb] at h; exact nomatch h
        | ok wb =>
          rw [hwb] at h
          simp only [] at h
          split at h
          · next n₁ n₂ heq₁ heq₂ =>
            exact natOpResult_shape (Except.ok.inj h)
          all_goals exact nomatch h
    · rw [if_neg h1] at h
      by_cases h2 : Setlec.natOpWfNames.contains c ∧
          Setlec.natLitSupported env
      · rw [if_pos h2] at h
        simp only [Bind.bind, Except.bind] at h
        cases hwa : r.whnf d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok wa =>
          rw [hwa] at h
          simp only [] at h
          cases hwb : r.whnf d b with
          | error err => rw [hwb] at h; exact nomatch h
          | ok wb =>
            rw [hwb] at h
            simp only [] at h
            split at h
            all_goals exact nomatch h
      · rw [if_neg h2] at h
        exact nomatch h
  · exact nomatch h

/-- **The `NatStepNoSort` discharge** (with the env fact
hypothesized): the nat step's target is a literal or `Bool` constant,
all of which are whnf-inert — colliding with the given
literal-sort convergence. -/
theorem natStepNoSort_of {μ : CheckMode} {env : Env}
    (hB : BoolCtorsInert env) : NatStepNoSort μ env := by
  intro g g' l f d e e' x ℓ hwc hrn hrun
  have hdet := knotFuelDet μ env
  have hm := knotFuelMono μ env
  cases l with
  | zero => exact nomatch hrun
  | succ l =>
  rw [whnfLoop_succ] at hrun
  obtain ⟨e₁, hwc', htri⟩ := whnfStep_decompose hrun
  obtain rfl : e' = e₁ :=
    (hdet.2.2.1 (hwc' : whnfCore μ env g' d e = .ok e₁) hwc).symm
  rcases htri with ⟨y, hry, hk⟩ | ⟨hry, y, huy, hk⟩ | ⟨hry, huy, hstop⟩
  · have h1 := hm.2.2.2.2 (Nat.le_max_left g' g) hry
    have h2 := hm.2.2.2.2 (Nat.le_max_right g' g) hrn
    rw [h1] at h2
    obtain rfl : y = x := Option.some.inj (Except.ok.inj h2)
    rcases reduceNat_some_shape hry with ⟨n, rfl⟩ | rfl | rfl
    · exact nomatch (loop_stuck_out hm hk
        (whnfCore_lit_run (Nat.le_refl 1))
        (fun _ => reduceNat_lit) unfoldDefinition_lit)
    · exact nomatch (loop_stuck_out hm hk
        (whnfCore_const_run (Nat.le_refl 1))
        (fun _ => reduceNat_const) hB.1)
    · exact nomatch (loop_stuck_out hm hk
        (whnfCore_const_run (Nat.le_refl 1))
        (fun _ => reduceNat_const) hB.2)
  · have h1 := hm.2.2.2.2 (Nat.le_max_left g' g) hry
    have h2 := hm.2.2.2.2 (Nat.le_max_right g' g) hrn
    rw [h1] at h2; exact nomatch h2
  · have h1 := hm.2.2.2.2 (Nat.le_max_left g' g) hry
    have h2 := hm.2.2.2.2 (Nat.le_max_right g' g) hrn
    rw [h1] at h2; exact nomatch h2

/-- The shell, nat routing discharged: conditioned on the three PSS
routings, the spine unknown, the env fact, and the `InvPreserve*F`
supply chain (obligations with named suppliers — their own discharge
seals). -/
theorem ensureSortAgreeR_of_pss {μ : CheckMode} {env : Env}
    {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  ensureSortAgreeR_of_vacuities (Q := Q) hIC hID hIN hLC hLD hLN
    hQC hQD hQN hQs hP hR hE (natStepNoSort_of hB) hS

/-! ## The trio discharge tier

The recorded recipe, mechanized: the loop assembly
(`typeTransportLoopF_of`), the collision engine
(`typeWhnfLE_collide` — spine fact at the head-normal form of a
sort-converging subject is pinned to the successor sort), and the
ctor-headed route (`ctorHead_no_sort` — no spine: nat continuation is
`NatStepNoSort` verbatim, δ is refuted by the ctor head, stuck
collides an app head with `.sort`). -/

section Discharge
variable {μ : CheckMode} {env : Env}

/-- The loop assembly: chain transport from the step species plus the
invariant supply chain, by one budget induction. -/
theorem typeTransportLoopF_of
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) :
    TypeTransportLoopF μ env := by
  intro g l
  induction l with
  | zero => intro d e s w h; exact nomatch h
  | succ l ih =>
    intro d e s w h hI hT
    rw [whnfLoop_succ] at h
    obtain ⟨e₁, hwcg, htri⟩ := whnfStep_decompose h
    have hwc : whnfCore μ env g d e = .ok e₁ := hwcg
    have hI₁ := hIC hwc hI
    have hT₁ := hTC hwc hI hT
    rcases htri with ⟨x, hrn, hk⟩ | ⟨hrn, x, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact ih hk (hIN hrn hI₁) (hTN hrn hI₁ hT₁)
    · exact ih hk (hID hud hI₁) (hTD hud hI₁ hT₁)
    · exact hT₁

/-- The collision engine. -/
theorem typeWhnfLE_collide (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    {g l f d : Nat} {a a' w : Expr} {ℓ : Level}
    (hI : SubjInv d a)
    (hwc : whnfCore μ env f d a = .ok a')
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l a
      = .ok (.sort ℓ))
    (hW : TypeWhnfLE μ env d a' w) : w = .sort (.succ ℓ) := by
  cases l with
  | zero => exact nomatch hloop
  | succ l =>
    rw [whnfLoop_succ] at hloop
    obtain ⟨a₁, hwcg, htri⟩ := whnfStep_decompose hloop
    obtain rfl : a' = a₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwcg : whnfCore μ env g d a = .ok a₁) hwc).symm
    have hI₁ : SubjInv d a' := hIC hwc hI
    rcases htri with ⟨x, hrn, hk⟩ | ⟨hrn, x, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact TypeWhnfLE_det hm
        (hT hk (hIN hrn hI₁) (hTN hrn hI₁ hW)) typeWhnfLE_sort
    · exact TypeWhnfLE_det hm
        (hT hk (hID hud hI₁) (hTD hud hI₁ hW)) typeWhnfLE_sort
    · exact TypeWhnfLE_det hm hW typeWhnfLE_sort

/-- Constructor heads never unfold. -/
theorem unfoldDefinition_ctor_none {c : Name} {us : List Level}
    {e : Expr} {cv : Setlec.ConstantVal} {nP nF : Nat}
    (hhd : e.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cv nP nF)) :
    Setlec.unfoldDefinition env e = none := by
  simp only [Setlec.unfoldDefinition, hhd, hf]

/-- The ctor-headed route: a head-normal form with a stored-inert
constant head never continues to a sort. -/
theorem ctorHead_no_sort (hm : KnotFuelMono μ env)
    (hN : NatStepNoSort μ env)
    {g l f d : Nat} {a a' : Expr} {c : Name} {us : List Level}
    {ℓ : Level}
    (hwc : whnfCore μ env f d a = .ok a')
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l a
      = .ok (.sort ℓ))
    (hhd : a'.getAppFn = .const c us)
    (hud : Setlec.unfoldDefinition env a' = none) : False := by
  have h0 := hloop
  cases l with
  | zero => exact nomatch hloop
  | succ l =>
    rw [whnfLoop_succ] at hloop
    obtain ⟨a₁, hwcg, htri⟩ := whnfStep_decompose hloop
    obtain rfl : a' = a₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwcg : whnfCore μ env g d a = .ok a₁) hwc).symm
    rcases htri with ⟨x, hrn, hk⟩ | ⟨hrn, x, hud', hk⟩ | ⟨hrn, hud', rfl⟩
    · exact hN hwc hrn h0
    · rw [hud] at hud'; exact nomatch hud'
    · simp [Setlec.Expr.getAppFn] at hhd

/-- Literal sorts are never unit-like (computation leaf). -/
theorem isUnitLikeTy_sort {ℓ : Level} :
    Setlec.isUnitLikeTy env (.sort ℓ) = false := rfl

/-- **Eta routing discharged** (against the spine): `etaCert`'s own
`whnf (infer a')` run lands at a `∀`, which the collision engine pins
to the successor sort — shape clash. -/
theorem etaSortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) {Q : Nat → Expr → Expr → Prop} :
    EtaSortVacuity μ env Q := by
  intro g g' l f d a a' n ty body m ℓ hI _hQv hwc hcert hloop
  unfold Setlec.etaCert at hcert
  simp only [Bind.bind, Except.bind] at hcert
  cases hinf : (Setlec.pureFns μ env g).infer d a' with
  | error err => rw [hinf] at hcert; exact nomatch hcert
  | ok tb =>
  rw [hinf] at hcert
  simp only [] at hcert
  cases hw : (Setlec.pureFns μ env g).whnf d tb with
  | error err => rw [hw] at hcert; exact nomatch hcert
  | ok wtb =>
  rw [hw] at hcert
  simp only [] at hcert
  split at hcert
  · next n₂ ty₂ body₂ m₂ =>
    obtain ⟨gw, lw, -, hlw⟩ :=
      whnf_peel (hw : whnf μ env g d tb = .ok (.forallE n₂ ty₂ body₂ m₂))
    have hW : TypeWhnfLE μ env d a' (.forallE n₂ ty₂ body₂ m₂) :=
      ⟨g, tb, hinf, gw, lw, hlw⟩
    exact nomatch (typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
      hI hwc hloop hW)
  · exact nomatch hcert

/-- **Probe routing discharged** (the double spine): the unit check's
own `whnf ta` run collides to the successor sort, killing the unit
branch by computation (`isUnitLikeTy_sort`); the sort branch's
level-2 fact `TypeWhnfLE ta (.sort uT)` transports along `ta`'s own
whnf chain (entered through `InvPreserveInferF`) onto the successor
sort, pinning `uT` to a double successor — refuting the cert's
`isEquiv uT 0` through `Level.isEquiv_sound`. -/
theorem proofIrrel_no_sort (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    {g g' l f d : Nat} {a a' b' : Expr} {ℓ : Level}
    (hI : SubjInv d a)
    (hwc : whnfCore μ env f d a = .ok a')
    (hpi : Setlec.proofIrrel (Setlec.pureFns μ env g) env d a' b'
      = .ok true)
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env g') env d l a
      = .ok (.sort ℓ)) : False := by
  unfold Setlec.proofIrrel at hpi
  simp only [Bind.bind, Except.bind] at hpi
  cases hinfa : (Setlec.pureFns μ env g).infer d a' with
  | error err => rw [hinfa] at hpi; exact nomatch hpi
  | ok ta =>
  rw [hinfa] at hpi
  simp only [] at hpi
  cases hwta : (Setlec.pureFns μ env g).whnf d ta with
  | error err => rw [hwta] at hpi; exact nomatch hpi
  | ok wta =>
  rw [hwta] at hpi
  simp only [] at hpi
  have hW1 : TypeWhnfLE μ env d a' wta := by
    obtain ⟨gw, lw, -, hlw⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok wta)
    exact ⟨g, ta, hinfa, gw, lw, hlw⟩
  obtain rfl : wta = .sort (.succ ℓ) :=
    typeWhnfLE_collide hm hT hTD hTN hIC hID hIN hI hwc hloop hW1
  rw [isUnitLikeTy_sort, if_neg Bool.false_ne_true] at hpi
  cases hinfta : (Setlec.pureFns μ env g).infer d ta with
  | error err => rw [hinfta] at hpi; exact nomatch hpi
  | ok sa =>
  rw [hinfta] at hpi
  simp only [] at hpi
  cases hwsa : (Setlec.pureFns μ env g).whnf d sa with
  | error err => rw [hwsa] at hpi; exact nomatch hpi
  | ok wsa =>
  rw [hwsa] at hpi
  simp only [] at hpi
  split at hpi
  · next uT =>
    -- the second spine application, along `ta`'s own whnf chain
    have hIta : SubjInv d ta := hInf hinfa (hIC hwc hI)
    have hW2 : TypeWhnfLE μ env d ta (.sort uT) := by
      obtain ⟨gs, ls, -, hls⟩ :=
        whnf_peel (hwsa : whnf μ env g d sa = .ok (.sort uT))
      exact ⟨g, sa, hinfta, gs, ls, hls⟩
    obtain ⟨gt, lt, -, hlt⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok (.sort (.succ ℓ)))
    have hW3 : TypeWhnfLE μ env d (.sort (.succ ℓ)) (.sort uT) :=
      hT hlt hIta hW2
    obtain rfl : uT = .succ (.succ ℓ) :=
      Setlec.Expr.sort.inj (TypeWhnfLE_det hm hW3 typeWhnfLE_sort)
    cases hlift : Setlec.liftFueled "level comparison"
        (Level.isEquiv (.succ (.succ ℓ)) .zero)
        (m := Setlec.CheckM) with
    | error err => rw [hlift] at hpi; exact nomatch hpi
    | ok okA =>
    rw [hlift] at hpi
    simp only [] at hpi
    rw [Setlec.liftFueled.eq_def] at hlift
    split at hlift
    · next okA' hEq =>
      obtain rfl : okA' = okA := by
        simpa [pure, Except.pure] using hlift
      cases okA' with
      | true =>
        have hev := Level.isEquiv_sound hEq (fun _ => 0)
        simp only [Setlec.Level.eval] at hev
        omega
      | false =>
        -- the b-side walk: every terminal returns `false` or throws
        cases hinfb : (Setlec.pureFns μ env g).infer d b' with
        | error err => rw [hinfb] at hpi; exact nomatch hpi
        | ok tb =>
        rw [hinfb] at hpi
        simp only [] at hpi
        cases hinftb : (Setlec.pureFns μ env g).infer d tb with
        | error err => rw [hinftb] at hpi; exact nomatch hpi
        | ok sb =>
        rw [hinftb] at hpi
        simp only [] at hpi
        cases hwsb : (Setlec.pureFns μ env g).whnf d sb with
        | error err => rw [hwsb] at hpi; exact nomatch hpi
        | ok wsb =>
        rw [hwsb] at hpi
        simp only [] at hpi
        split at hpi
        · next vT =>
          cases hliftB : Setlec.liftFueled "level comparison"
              (Level.isEquiv vT .zero) (m := Setlec.CheckM) with
          | error err => rw [hliftB] at hpi; exact nomatch hpi
          | ok okB => rw [hliftB] at hpi; exact nomatch hpi
        · exact nomatch hpi
    · exact nomatch hlift
  · exact nomatch hpi

/-- **Rescue routing discharged**: the five-way read of `stuckIrrel`.
The a-directed pair/struct-eta branches need no spine (the subject is
ctor-headed — `ctorHead_no_sort`); the b-directed branches and the
unit cert collide a const-app-headed `w` with the successor sort; the
fallback is the probe (`proofIrrel_no_sort`). -/
theorem rescueSortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hN : NatStepNoSort μ env) {Q : Nat → Expr → Expr → Prop} :
    RescueSortVacuity μ env Q := by
  intro g g' l f d a a' b' ℓ hI _hQv hwc hsi hloop
  unfold Setlec.stuckIrrel at hsi
  simp only [Bind.bind, Except.bind] at hsi
  -- branch 1: pairEtaCert a' b' (a-directed; ctor-headed route)
  cases h1 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d a' b' with
  | error err => rw [h1] at hsi; exact nomatch hsi
  | ok c1 =>
  rw [h1] at hsi
  simp only [] at hsi
  cases c1 with
  | true =>
    unfold Setlec.pairEtaCert at h1
    split at h1
    · next c us pα pβ s₁ s₂ =>
      split at h1
      · next _cvm hfind =>
        exact ctorHead_no_sort hm hN hwc hloop
          (show Setlec.Expr.getAppFn _ = .const c us from rfl)
          (unfoldDefinition_ctor_none rfl hfind)
      · exact nomatch h1
    · exact nomatch h1
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 2: pairEtaCert b' a' (b-directed; spine)
  cases h2 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d b' a' with
  | error err => rw [h2] at hsi; exact nomatch hsi
  | ok c2 =>
  rw [h2] at hsi
  simp only [] at hsi
  cases c2 with
  | true =>
    unfold Setlec.pairEtaCert at h2
    simp only [Bind.bind, Except.bind] at h2
    split at h2
    · next cB usB pαB pβB s₁B s₂B =>
      split at h2
      · next _cvmB hfindB =>
        cases hinf2 : (Setlec.pureFns μ env g).infer d a' with
        | error err => rw [hinf2] at h2; exact nomatch h2
        | ok tb =>
        rw [hinf2] at h2
        simp only [] at h2
        cases hw2 : (Setlec.pureFns μ env g).whnf d tb with
        | error err => rw [hw2] at h2; exact nomatch h2
        | ok wtb =>
        rw [hw2] at h2
        simp only [] at h2
        split at h2
        · next c' us' A B =>
          obtain ⟨gw, lw, -, hlw⟩ :=
            whnf_peel (hw2 : whnf μ env g d tb = .ok _)
          exact nomatch (typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
            hI hwc hloop (⟨g, tb, hinf2, gw, lw, hlw⟩ :
              TypeWhnfLE μ env d a' _))
        · exact nomatch h2
      · exact nomatch h2
    · exact nomatch h2
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 3: structEtaCert a' b' (a-directed; ctor-headed route)
  cases h3 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d a' b' with
  | error err => rw [h3] at hsi; exact nomatch hsi
  | ok c3 =>
  rw [h3] at hsi
  simp only [] at hsi
  cases c3 with
  | true =>
    unfold Setlec.structEtaCert at h3
    simp only [Bind.bind, Except.bind] at h3
    cases hinf3 : (Setlec.pureFns μ env g).infer d b' with
    | error err => rw [hinf3] at h3; exact nomatch h3
    | ok tb =>
    rw [hinf3] at h3
    simp only [] at h3
    cases hw3 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw3] at h3; exact nomatch h3
    | ok wtb =>
    rw [hw3] at h3
    simp only [] at h3
    unfold Setlec.structEtaCertWith at h3
    split at h3
    · next c us heqa =>
      split at h3
      · next cvc cnP cnF hfinda =>
        exact ctorHead_no_sort hm hN hwc hloop heqa
          (unfoldDefinition_ctor_none heqa hfinda)
      · exact nomatch h3
    · exact nomatch h3
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 4: structEtaCert b' a' (b-directed; spine)
  cases h4 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d b' a' with
  | error err => rw [h4] at hsi; exact nomatch hsi
  | ok c4 =>
  rw [h4] at hsi
  simp only [] at hsi
  cases c4 with
  | true =>
    unfold Setlec.structEtaCert at h4
    simp only [Bind.bind, Except.bind] at h4
    cases hinf4 : (Setlec.pureFns μ env g).infer d a' with
    | error err => rw [hinf4] at h4; exact nomatch h4
    | ok tb =>
    rw [hinf4] at h4
    simp only [] at h4
    cases hw4 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw4] at h4; exact nomatch h4
    | ok wtb =>
    rw [hw4] at h4
    simp only [] at h4
    obtain rfl : wtb = .sort (.succ ℓ) := by
      obtain ⟨gw, lw, -, hlw⟩ :=
        whnf_peel (hw4 : whnf μ env g d tb = .ok wtb)
      exact typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
        hI hwc hloop ⟨g, tb, hinf4, gw, lw, hlw⟩
    unfold Setlec.structEtaCertWith at h4
    split at h4
    · next cB usB heqb =>
      split at h4
      · next cvcB cnPB cnFB hfindb =>
        split at h4
        · split at h4
          · next T us' heqw => exact nomatch heqw
          · exact nomatch h4
        · exact nomatch h4
      · exact nomatch h4
    · exact nomatch h4
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 5: structUnitCert (spine at the unit type's const head)
  cases h5 : Setlec.structUnitCert (Setlec.pureFns μ env g) env d a' b' with
  | error err => rw [h5] at hsi; exact nomatch hsi
  | ok c5 =>
  rw [h5] at hsi
  simp only [] at hsi
  cases c5 with
  | true =>
    unfold Setlec.structUnitCert at h5
    simp only [Bind.bind, Except.bind] at h5
    cases hinf5 : (Setlec.pureFns μ env g).infer d a' with
    | error err => rw [hinf5] at h5; exact nomatch h5
    | ok ta =>
    rw [hinf5] at h5
    simp only [] at h5
    cases hw5 : (Setlec.pureFns μ env g).whnf d ta with
    | error err => rw [hw5] at h5; exact nomatch h5
    | ok wta =>
    rw [hw5] at h5
    simp only [] at h5
    obtain rfl : wta = .sort (.succ ℓ) := by
      obtain ⟨gw, lw, -, hlw⟩ :=
        whnf_peel (hw5 : whnf μ env g d ta = .ok wta)
      exact typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
        hI hwc hloop ⟨g, ta, hinf5, gw, lw, hlw⟩
    split at h5
    · next T us' heqw => exact nomatch heqw
    · exact nomatch h5
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 6: the proofIrrel fallback = the probe
  exact proofIrrel_no_sort hm hT hTD hTN hIC hID hIN hInf
    hI hwc hsi hloop

/-- The probe routing, packaged. -/
theorem probeSortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    {Q : Nat → Expr → Expr → Prop} :
    ProbeSortVacuity μ env Q := by
  intro g g' l f d a a' b' ℓ hI _hQv hwc hpi hloop
  exact proofIrrel_no_sort hm hT hTD hTN hIC hID hIN hInf
    hI hwc hpi hloop

/-! ### The spine routing, reduced to its both-δ core

The `defeqSpine` scoping map (graded-unknown discipline): a `true`
verdict pins both subjects const-headed with the *same* head `n`,
equal arg counts, `isEquivList`-equivalent levels, and pointwise
`defEqList`-certified args.  On a sort-converging subject the loop's
stuck leg clashes with the const head and the nat leg is
`NatStepNoSort` verbatim — so both sides take δ steps, unfolding the
*same stored value* at equivalent levels with certified args.  That
both-δ residue is the routing's irreducible core, named below; the
reduction `spineSortAgree_of` is proved here, the core's supplier is
graded (DESIGN — it embeds certified-pair convergence at argument
positions, not level bookkeeping). -/

/-- **The both-δ core** (graded unknown #1, reduced form, restated
dual-success per the unhold's Gap 2): a same-head
`defeqSpine`-certified pair whose members' own chains reach literal
sorts has equal numerals.  The sort runs are stated ON `a'`/`b'` (the
(A-T) liveness pattern — the consumer assembles them from its
decomposition; the discharge reads the δ steps off the runs), and
the no-cumulativity finding fixes the discharge route: both sides'
type-sorts are ONE level expression in `us`/`us'` (Gap 1 =
`DeltaSortLinked` at two-instantiation strength), transported along
each run by `TypeTransportLoopF`, pinned by `typeWhnfLE_sort` + det,
and equated by `isEquivList` soundness. -/
def DeltaSpineSortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {a' b' : Expr} {ℓa ℓb : Level},
    SubjInv d a' → SubjInv d b' → PairedLeaves a' b' → Q d a' b' →
    Setlec.defeqSpine (Setlec.pureFns μ env fc) env d a' b'
      = .ok true →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a'
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b'
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The spine routing reduced**: `SpineSortAgree` from the both-δ
core — the stuck legs clash with `defeqSpine`'s const heads, the nat
legs are `NatStepNoSort`, the δ-δ leg is the core with `SubjInv`
carried across the whnfCore step. -/
theorem spineSortAgree_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop} (hm : KnotFuelMono μ env)
    (hB : BoolCtorsInert env) (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hD : DeltaSpineSortAgree μ env φ Q) :
    SpineSortAgree μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc l d ga la gb lb f₁ f₂ a b a' b' ℓa ℓb hIa hIb hPab hQab
    hc hwa hwb hs ha hb
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
  obtain rfl : a' = a₁ :=
    ((KnotFuelDet_of_mono hm).2.2.1
      (hwca : whnfCore μ env ga d a = .ok a₁) hwa).symm
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
  obtain rfl : b' = b₁ :=
    ((KnotFuelDet_of_mono hm).2.2.1
      (hwcb : whnfCore μ env gb d b = .ok b₁) hwb).symm
  rcases htriA with ⟨x, hrx, -⟩ | ⟨hrga, xa, hux, hkx⟩ |
    ⟨-, -, hstopA⟩
  · exact (hN hwa hrx ha).elim
  · rcases htriB with ⟨y, hry, -⟩ | ⟨hrgb, xb, huy, hky⟩ |
      ⟨-, -, hstopB⟩
    · exact (hN hwb hry hb).elim
    · -- both-δ: assemble the dual-success runs on `a'`/`b'` (the
      -- spine cert's const heads make whnfCore re-idem) and hand
      -- the core its inputs.
      obtain ⟨na, usa, heqa⟩ : ∃ n us, a'.getAppFn = .const n us := by
        have hs' := hs
        unfold Setlec.defeqSpine at hs'
        split at hs'
        · next n us heq => exact ⟨n, us, heq⟩
        · exact nomatch hs'
      obtain ⟨nb, usb, heqb⟩ : ∃ n us, b'.getAppFn = .const n us := by
        have hs' := hs
        unfold Setlec.defeqSpine at hs'
        split at hs'
        · next n us heq =>
          split at hs'
          · next n' us' heq' => exact ⟨n', us', heq'⟩
          · exact nomatch hs'
        · exact nomatch hs'
      have ha' : Setlec.whnfLoop (Setlec.pureFns μ env (max f₁ ga))
          env d (la' + 1) a' = .ok (.sort ℓa) := by
        rw [whnfLoop_succ]
        exact whnfStep_assemble_delta
          (hm.2.2.1 (Nat.le_max_left f₁ ga)
            (whnfCore_reidem_const hm hwa heqa))
          (hm.2.2.2.2 (Nat.le_max_right f₁ ga) hrga) hux
          (whnfLoop_r_mono hm (Nat.le_max_right f₁ ga) hkx)
      have hb' : Setlec.whnfLoop (Setlec.pureFns μ env (max f₂ gb))
          env d (lb' + 1) b' = .ok (.sort ℓb) := by
        rw [whnfLoop_succ]
        exact whnfStep_assemble_delta
          (hm.2.2.1 (Nat.le_max_left f₂ gb)
            (whnfCore_reidem_const hm hwb heqb))
          (hm.2.2.2.2 (Nat.le_max_right f₂ gb) hrgb) huy
          (whnfLoop_r_mono hm (Nat.le_max_right f₂ gb) hky)
      exact hD (hIC hwa hIa) (hIC hwb hIb)
        ((hLC hwb ((hLC hwa hPab).symm)).symm)
        (hQs (hQC hwb (hQs (hQC hwa hQab)))) hs ha' hb'
    · obtain rfl := hstopB
      unfold Setlec.defeqSpine at hs
      split at hs
      · exact nomatch hs
      · exact nomatch hs
  · obtain rfl := hstopA
    unfold Setlec.defeqSpine at hs
    exact nomatch hs

/-- **The shell against the species tier**: `EnsureSortAgreeR` from
the env fact, the invariant supply chain, the three transport step
species, and the spine routing.  The PSS trio is discharged — the
branch's remaining unknowns are (F)-species-shaped plus
`SpineSortAgree`. -/
theorem ensureSortAgreeR_of_species {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  have hm : KnotFuelMono μ env := knotFuelMono μ env
  have hT : TypeTransportLoopF μ env :=
    typeTransportLoopF_of hTC hTD hTN hIC hID hIN
  ensureSortAgreeR_of_pss (Q := Q) hB hIC hID hIN hLC hLD hLN
    hQC hQD hQN hQs
    (probeSortVacuity_of hm hT hTD hTN hIC hID hIN hInf)
    (rescueSortVacuity_of hm hT hTD hTN hIC hID hIN hInf
      (natStepNoSort_of hB))
    (etaSortVacuity_of hm hT hTD hTN hIC hID hIN) hS

/-- **The branch primitive at its irreducibles**: `EnsureSortAgreeR`
from the env fact, the three transport step species, the four
invariant preservers, and the both-δ spine core.  Everything else on
the defeq branch is discharged. -/
theorem ensureSortAgreeR_of_core {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hD : DeltaSpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  ensureSortAgreeR_of_species (Q := Q) hB hTC hTD hTN hIC hID hIN
    hInf hLC hLD hLN hQC hQD hQN hQs
    (spineSortAgree_of (Q := Q) (knotFuelMono μ env) hB hIC hLC hQC
      hQs hD)

/-! ## (B)'s dual shell — `sortOfE` agreement on the same decomposition

The type-level dual of the (A) shell, on the settled motive shape
(`SubjInv` per side + concrete cross-`PairedLeaves` + the abstract
`Q`-slot).  Bases and re-entries are proved here (determinism,
arithmetic, and the transport species); the congruence tier and the
type-level vacuities are the named routings below, each at its own
seal.  Three map corrections landed with the build: `etaL`/`etaR`/
`lamCong` all die on `LamTySortVacuity` (a λ's inferred type is a
`∀`, never a sort — the eta cert is not even consumed), and
`natL`/`natR` are plain re-entries through the nat transport species,
not vacuities. -/

/-- `SortOfLE` transports across a head-normalization step (the
(F-core) sort instance). -/
theorem sortOfLE_step_core {φ : Name → Nat}
    (hTC : TypeTransportCoreF μ env) {f d : Nat} {e e' : Expr}
    {u : Nat} (hwc : whnfCore μ env f d e = .ok e') (hI : SubjInv d e)
    (h : SortOfLE μ env φ d e u) : SortOfLE μ env φ d e' u := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  exact sortOfLE_iff_typeWhnfLE.2 ⟨ℓ, hTC hwc hI hW, hev⟩

/-- `SortOfLE` transports across one unfolding ((F-δ) sort
instance). -/
theorem sortOfLE_step_delta {φ : Name → Nat}
    (hTD : TypeTransportDeltaF μ env) {d : Nat} {e e' : Expr}
    {u : Nat} (hud : Setlec.unfoldDefinition env e = some e')
    (hI : SubjInv d e)
    (h : SortOfLE μ env φ d e u) : SortOfLE μ env φ d e' u := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  exact sortOfLE_iff_typeWhnfLE.2 ⟨ℓ, hTD hud hI hW, hev⟩

/-- `SortOfLE` transports across one literal-acceleration step
((F-nat) sort instance). -/
theorem sortOfLE_step_nat {φ : Name → Nat}
    (hTN : TypeTransportNatF μ env) {f d : Nat} {e e' : Expr}
    {u : Nat}
    (hrn : Setlec.reduceNat (Setlec.pureFns μ env f) env d e
      = .ok (some e'))
    (hI : SubjInv d e)
    (h : SortOfLE μ env φ d e u) : SortOfLE μ env φ d e' u := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  exact sortOfLE_iff_typeWhnfLE.2 ⟨ℓ, hTN hrn hI hW, hev⟩

/-- A successful loop-level sort computation on a literal sort is
the successor numeral. -/
theorem sortOfLE_sort_out {φ : Name → Nat} (hm : KnotFuelMono μ env)
    {d : Nat} {w : Level} {u : Nat}
    (h : SortOfLE μ env φ d (.sort w) u) : u = w.eval φ + 1 := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  obtain rfl : ℓ = .succ w :=
    Setlec.Expr.sort.inj (TypeWhnfLE_det hm hW typeWhnfLE_sort)
  exact hev.symm

/-! ### (B)'s routed hypotheses (each at its own seal) -/

/-- Type-level probe vacuity: a `proofIrrel`-certified subject's
type never whnf-converges to a literal sort. -/
def ProbeTySortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {a' b' : Expr} {ℓ : Level},
    SubjInv d a' → Q d a' b' →
    Setlec.proofIrrel (Setlec.pureFns μ env g) env d a' b' = .ok true →
    TypeWhnfLE μ env d a' (.sort ℓ) → False

/-- Type-level rescue vacuity, five-way as before. -/
def RescueTySortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {a' b' : Expr} {ℓ : Level},
    SubjInv d a' → Q d a' b' →
    Setlec.stuckIrrel μ (Setlec.pureFns μ env g) env d a' b'
      = .ok true →
    TypeWhnfLE μ env d a' (.sort ℓ) → False

/-- A λ's inferred type is a `∀`, never a sort — kills `etaL`,
`etaR` and `lamCong` without reading their certs. -/
def LamTySortVacuity (μ : CheckMode) (env : Env) : Prop :=
  ∀ {d : Nat} {n : Name} {ty body : Expr} {m : Setlec.BinderMeta}
    {ℓ : Level},
    TypeWhnfLE μ env d (.lam n ty body m) (.sort ℓ) → False

/-- Mixed terminal: the `Nat` literal against the stored zero. -/
def NatZeroTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d u v : Nat},
    SortOfLE μ env φ d (.lit (.natVal 0)) u →
    SortOfLE μ env φ d (.const Setlec.natZeroName []) v → u = v

/-- Mixed terminal: successor packing, literal side left. -/
def NatSuccLTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v n : Nat} {x : Expr},
    (Setlec.pureFns μ env g).defeq d (.lit (.natVal n)) x = .ok true →
    SortOfLE μ env φ d (.lit (.natVal (n + 1))) u →
    SortOfLE μ env φ d (.app (.const Setlec.natSuccName []) x) v →
    u = v

/-- Mixed terminal: successor packing, literal side right. -/
def NatSuccRTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v n : Nat} {x : Expr},
    Setlec.unfoldableHead env
      (.app (.const Setlec.natSuccName []) x) = false →
    (Setlec.pureFns μ env g).defeq d x (.lit (.natVal n)) = .ok true →
    SortOfLE μ env φ d (.app (.const Setlec.natSuccName []) x) u →
    SortOfLE μ env φ d (.lit (.natVal (n + 1))) v → u = v

/-- Mixed terminal: the string literal against a stuck app. -/
def StrLTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v : Nat} {st : String} {cO : Name} {usO : List Level}
    {x : Expr},
    (Setlec.pureFns μ env g).defeq d (Setlec.strLitToConstructor st)
      (.app (.const cO usO) x) = .ok true →
    SortOfLE μ env φ d (.lit (.strVal st)) u →
    SortOfLE μ env φ d (.app (.const cO usO) x) v → u = v

/-- Mixed terminal: the stuck app against the string literal. -/
def StrRTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v : Nat} {st : String} {cO : Name} {usO : List Level}
    {x : Expr},
    Setlec.unfoldableHead env (.app (.const cO usO) x) = false →
    (Setlec.pureFns μ env g).defeq d (.app (.const cO usO) x)
      (Setlec.strLitToConstructor st) = .ok true →
    SortOfLE μ env φ d (.app (.const cO usO) x) u →
    SortOfLE μ env φ d (.lit (.strVal st)) v → u = v

/-- The `fvars` leaf: same index, own annotations — cross-pairing
pins the annotations equal, and `infer` is name-blind. -/
def FvarTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d u v i : Nat} {n₁ n₂ : Name} {ty₁ ty₂ : Expr},
    SubjInv d (.fvar i n₁ ty₁) → SubjInv d (.fvar i n₂ ty₂) →
    PairedLeaves (.fvar i n₁ ty₁) (.fvar i n₂ ty₂) →
    SortOfLE μ env φ d (.fvar i n₁ ty₁) u →
    SortOfLE μ env φ d (.fvar i n₂ ty₂) v → u = v

/-- The `consts` leaf: one stored type at two equivalent level
instantiations — the spine core's argless sibling. -/
def ConstTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d u v : Nat} {n : Name} {us us' : List Level},
    Setlec.unfoldableHead env (.const n us) = false →
    Level.isEquivList us us' = some true →
    SortOfLE μ env φ d (.const n us) u →
    SortOfLE μ env φ d (.const n us') v → u = v

/-- The spine's type-level agreement (`Q`-carrying, like its (A)
sibling). -/
def SpineTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v : Nat} {a' b' : Expr},
    SubjInv d a' → SubjInv d b' → Q d a' b' →
    Setlec.defeqSpine (Setlec.pureFns μ env g) env d a' b'
      = .ok true →
    SortOfLE μ env φ d a' u → SortOfLE μ env φ d b' v → u = v

/-- The `∀`-congruence tier (the Θ-motive proper; `Q`-carrying). -/
def PiCongTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v : Nat} {n₁ n₂ : Name} {ty₁ ty₂ body₁ body₂ : Expr}
    {m₁ m₂ : Setlec.BinderMeta},
    SubjInv d (.forallE n₁ ty₁ body₁ m₁) →
    SubjInv d (.forallE n₂ ty₂ body₂ m₂) →
    PairedLeaves (.forallE n₁ ty₁ body₁ m₁)
      (.forallE n₂ ty₂ body₂ m₂) →
    Q d (.forallE n₁ ty₁ body₁ m₁) (.forallE n₂ ty₂ body₂ m₂) →
    (Setlec.pureFns μ env g).defeq d ty₁ ty₂ = .ok true →
    (Setlec.pureFns μ env g).defeq (d + 1)
      (body₁.instantiate1 (.fvar d n₁ ty₁))
      (body₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true →
    SortOfLE μ env φ d (.forallE n₁ ty₁ body₁ m₁) u →
    SortOfLE μ env φ d (.forallE n₂ ty₂ body₂ m₂) v → u = v

/-- The application-congruence tier (`Q`-carrying). -/
def AppCongTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v : Nat} {f₁ a₁ f₂ a₂ : Expr},
    SubjInv d (.app f₁ a₁) → SubjInv d (.app f₂ a₂) →
    PairedLeaves (.app f₁ a₁) (.app f₂ a₂) →
    Q d (.app f₁ a₁) (.app f₂ a₂) →
    Setlec.unfoldableHead env (.app f₁ a₁) = false →
    (Expr.app f₁ a₁).getAppArgs.length =
      (Expr.app f₂ a₂).getAppArgs.length →
    (Setlec.pureFns μ env g).defeq d (Expr.app f₁ a₁).getAppFn
      (Expr.app f₂ a₂).getAppFn = .ok true →
    Setlec.defEqList (Setlec.pureFns μ env g) env d
      (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs
      = .ok true →
    SortOfLE μ env φ d (.app f₁ a₁) u →
    SortOfLE μ env φ d (.app f₂ a₂) v → u = v

/-- The projection-congruence tier (`Q`-carrying). -/
def ProjCongTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v i : Nat} {s₁ s₂ : Name} {e₁ e₂ : Expr},
    SubjInv d (.proj s₁ i e₁) → SubjInv d (.proj s₂ i e₂) →
    PairedLeaves (.proj s₁ i e₁) (.proj s₂ i e₂) →
    Q d (.proj s₁ i e₁) (.proj s₂ i e₂) →
    (Setlec.pureFns μ env g).defeq d e₁ e₂ = .ok true →
    SortOfLE μ env φ d (.proj s₁ i e₁) u →
    SortOfLE μ env φ d (.proj s₂ i e₂) v → u = v

/-- The `Q`-enriched (B) claim; `SortOfAgreeR` is its `Q := True`
instance. -/
def SortOfAgreeRQ (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {u v : Nat},
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    Q d a b →
    sortOfE μ env φ f₁ d a = some u →
    sortOfE μ env φ f₂ d b = some v →
    u = v

/-- **(B)'s dual shell**: `SortOfAgreeRQ` from the transport species,
the three supply chains, and the routed hypotheses — the same
budget-only cert-loop induction as (A), at the type level. -/
theorem sortOfAgreeRQ_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeTySortVacuity μ env Q)
    (hR : RescueTySortVacuity μ env Q)
    (hLam : LamTySortVacuity μ env)
    (hZ : NatZeroTySortAgree μ env φ)
    (hSL : NatSuccLTySortAgree μ env φ)
    (hSR : NatSuccRTySortAgree μ env φ)
    (hStL : StrLTySortAgree μ env φ) (hStR : StrRTySortAgree μ env φ)
    (hF : FvarTySortAgree μ env φ) (hK : ConstTySortAgree μ env φ)
    (hSp : SpineTySortAgree μ env φ Q)
    (hPi : PiCongTySortAgree μ env φ Q)
    (hAp : AppCongTySortAgree μ env φ Q)
    (hPj : ProjCongTySortAgree μ env φ Q) :
    SortOfAgreeRQ μ env φ Q := by
  have main : ∀ (fc L : Nat) {d : Nat} {a b : Expr},
      Setlec.defeqLoop μ (Setlec.pureFns μ env fc) env d L a b
        = .ok true →
      SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
      ∀ {u v : Nat}, SortOfLE μ env φ d a u →
        SortOfLE μ env φ d b v → u = v := by
    intro fc L
    induction L with
    | zero => intro d a b hc; exact nomatch hc
    | succ l ih =>
      intro d a b hc hIa hIb hPab hQab u v hu hv
      rw [defeqLoop_succ] at hc
      rcases defeqStep_decompose hc with rfl | ⟨a', b', hwa, hwb, hcert⟩
      · exact SortOfLE_det hm hu hv
      have hIa' := hIC hwa hIa
      have hIb' := hIC hwb hIb
      have hu' := sortOfLE_step_core hTC hwa hIa hu
      have hv' := sortOfLE_step_core hTC hwb hIb hv
      have hPab' : PairedLeaves a' b' :=
        ((hLC hwb ((hLC hwa hPab).symm)).symm)
      have hQab' : Q d a' b' := hQs (hQC hwb (hQs (hQC hwa hQab)))
      cases hcert with
      | syn => exact SortOfLE_det hm hu' hv'
      | irrel _ _ hpi =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hP hIa' hQab' hpi hW).elim
      | natL _ _ a₂ hrn hk =>
        exact ih hk (hIN hrn hIa') hIb' (hLN hrn hPab')
          (hQN hrn hQab') (sortOfLE_step_nat hTN hrn hIa' hu') hv'
      | natR _ _ b₂ hrnA hrnB hk =>
        exact ih hk hIa' (hIN hrnB hIb')
          ((hLN hrnB hPab'.symm).symm)
          (hQs (hQN hrnB (hQs hQab'))) hu'
          (sortOfLE_step_nat hTN hrnB hIb' hv')
      | deltaL _ _ a₂ hud hk =>
        exact ih hk (hID hud hIa') hIb' (hLD hud hPab')
          (hQD hud hQab') (sortOfLE_step_delta hTD hud hIa' hu') hv'
      | deltaR _ _ b₂ hud hk =>
        exact ih hk hIa' (hID hud hIb')
          ((hLD hud hPab'.symm).symm)
          (hQs (hQD hud (hQs hQab'))) hu'
          (sortOfLE_step_delta hTD hud hIb' hv')
      | deltaB _ _ a₂ b₂ hua hub hk =>
        exact ih hk (hID hua hIa') (hID hub hIb')
          ((hLD hub ((hLD hua hPab').symm)).symm)
          (hQs (hQD hub (hQs (hQD hua hQab'))))
          (sortOfLE_step_delta hTD hua hIa' hu')
          (sortOfLE_step_delta hTD hub hIb' hv')
      | spine _ _ hs => exact hSp hIa' hIb' hQab' hs hu' hv'
      | sorts u' v' hiseq =>
        rw [sortOfLE_sort_out hm hu', sortOfLE_sort_out hm hv',
          Level.isEquiv_sound hiseq φ]
      | lits _ => exact SortOfLE_det hm hu' hv'
      | natZeroL => exact hZ hu' hv'
      | natZeroR _ => exact (hZ hv' hu').symm
      | natSuccL n x hd => exact hSL hd hu' hv'
      | natSuccR n x hua hd => exact hSR hua hd hu' hv'
      | strL st cO usO x hd => exact hStL hd hu' hv'
      | strR st cO usO x hua hd => exact hStR hua hd hu' hv'
      | fvars i n₁ n₂ ty₁ ty₂ => exact hF hIa' hIb' hPab' hu' hv'
      | consts n us us' hua hiseq => exact hK hua hiseq hu' hv'
      | piCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ hd hbody =>
        exact hPi hIa' hIb' hPab' hQab' hd hbody hu' hv'
      | lamCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ hd hbody =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hLam hW).elim
      | appCong f₁ a₁ f₂ a₂ hua hlen hdf hdl =>
        exact hAp hIa' hIb' hPab' hQab' hua hlen hdf hdl hu' hv'
      | projCong s₁ s₂ i e₁ e₂ hd =>
        exact hPj hIa' hIb' hPab' hQab' hd hu' hv'
      | etaL n₁ ty₁ body₁ m₁ b₂ he =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hLam hW).elim
      | etaR _ n₂ ty₂ body₂ m₂ he =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hv'
        exact (hLam hW).elim
      | rescue _ _ hsi =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hR hIa' hQab' hsi hW).elim
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp hQ h₁ h₂
  cases fc with
  | zero => exact nomatch hc
  | succ fc =>
    rw [Setlec.isDefEqCore_succ] at hc
    exact main fc Setlec.defeqLoopFuel hc
      (SubjInv.of_pair hwsa hba hLa hp)
      (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ
      (SortOfLE_of_run h₁) (SortOfLE_of_run h₂)

/-! ### (B)'s mechanizable discharges: λ, fvar, probe -/

/-- `whnfCore` is the identity on `∀`s (value branch). -/
theorem whnfCore_forallE_run {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {ty body : Expr} {m : Setlec.BinderMeta} (hf : 1 ≤ f) :
    whnfCore μ env f d (.forallE n ty body m)
      = .ok (.forallE n ty body m) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- Inference on a `λ` only ever returns a `∀` with the λ's own
domain and meta (the clause's every success path). -/
theorem inferTypeCore_lam_out {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {ty body : Expr} {m : Setlec.BinderMeta} {t : Expr}
    (h : inferTypeCore μ env f d (.lam n ty body m) = .ok t) :
    ∃ bt, t = .forallE n ty bt m := by
  cases f with
  | zero => exact nomatch h
  | succ f =>
    rw [Setlec.inferTypeCore_succ] at h
    unfold Setlec.inferBody at h
    simp only [Setlec.viewM, Setlec.Expr.view, Bind.bind, Except.bind,
      pure, Except.pure] at h
    cases h1 : (Setlec.pureFns μ env f).infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h
    simp only [] at h
    cases h2 : (Setlec.pureFns μ env f).whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok wty =>
    rw [h2] at h
    simp only [] at h
    split at h
    · cases h3 : (Setlec.pureFns μ env f).infer (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | error err => rw [h3] at h; exact nomatch h
      | ok bt =>
      rw [h3] at h
      simp only [] at h
      split at h
      · cases h4 : (Setlec.pureFns μ env f).infer (d + 1) bt with
        | error err => rw [h4] at h; exact nomatch h
        | ok btt =>
        rw [h4] at h
        simp only [] at h
        cases h5 : Setlec.ensureSort (Setlec.pureFns μ env f) env
            (d + 1) btt with
        | error err => rw [h5] at h; exact nomatch h
        | ok s =>
        rw [h5] at h
        exact ⟨bt.abstract1 d, (Except.ok.inj h).symm⟩
      · exact ⟨bt.abstract1 d, (Except.ok.inj h).symm⟩
    · exact nomatch h

/-- Inference on an `fvar` leaf is name-blind: it returns the stored
annotation. -/
theorem inferTypeCore_fvar_out {μ : CheckMode} {env : Env} {f d : Nat}
    {i : Nat} {n : Name} {ty t : Expr}
    (h : inferTypeCore μ env f d (.fvar i n ty) = .ok t) : t = ty := by
  cases f with
  | zero => exact nomatch h
  | succ f =>
    rw [Setlec.inferTypeCore_succ] at h
    unfold Setlec.inferBody at h
    simp only [Setlec.viewM, Setlec.Expr.view, Bind.bind, Except.bind,
      pure, Except.pure] at h
    split at h
    · exact (Except.ok.inj h).symm
    · exact nomatch h

/-- **λ vacuity discharged**: a λ infers to a `∀`, and `∀`s are
whnf-inert — never a sort. -/
theorem lamTySortVacuity_of (hm : KnotFuelMono μ env) :
    LamTySortVacuity μ env := by
  intro d n ty body m ℓ hW
  obtain ⟨ft, t, hi, g, l, hl⟩ := hW
  obtain ⟨bt, rfl⟩ := inferTypeCore_lam_out hi
  exact nomatch (loop_stuck_out hm hl
    (whnfCore_forallE_run (μ := μ) (env := env) (d := d)
      (Nat.le_refl 1))
    (fun _ => reduceNat_forallE) unfoldDefinition_forallE)

/-- **The fvar leaf discharged**: cross-pairing pins the two
annotations equal, and `infer` reads the annotation name-blind, so
both sort computations run on one type. -/
theorem fvarTySortAgree_of (hm : KnotFuelMono μ env)
    {φ : Name → Nat} : FvarTySortAgree μ env φ := by
  intro d u v i n₁ n₂ ty₁ ty₂ _ _ hp hu hv
  have hty : ty₁ = ty₂ :=
    hp (i, n₁, ty₁)
      (List.mem_append_left _ (by simp [Setlec.Expr.fvarLeaves]))
      (i, n₂, ty₂)
      (List.mem_append_right _ (by simp [Setlec.Expr.fvarLeaves]))
      rfl
  obtain ⟨f₁, t₁, hi₁, g₁, l₁, ℓ₁, hl₁, hev₁⟩ := hu
  obtain ⟨f₂, t₂, hi₂, g₂, l₂, ℓ₂, hl₂, hev₂⟩ := hv
  obtain rfl : t₁ = ty₁ := inferTypeCore_fvar_out hi₁
  obtain rfl : t₂ = ty₂ := inferTypeCore_fvar_out hi₂
  subst hty
  obtain rfl : ℓ₁ = ℓ₂ :=
    Setlec.Expr.sort.inj (whnfLoop_det hm hl₁ hl₂)
  rw [← hev₁, ← hev₂]

/-- **The type-level probe vacuity discharged** — the (A) double
spine with determinism in place of the loop collide: the cert's own
unit-check run det-collides with the given type-sort fact, the sort
branch pins `uT` to the single successor through the second
transport, and `Level.isEquiv_sound` refutes at the zero
valuation. -/
theorem probeTySortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env) (hInf : InvPreserveInferF μ env)
    {Q : Nat → Expr → Expr → Prop} :
    ProbeTySortVacuity μ env Q := by
  intro g d a' b' ℓ hIa' _hQv hpi hW
  unfold Setlec.proofIrrel at hpi
  simp only [Bind.bind, Except.bind] at hpi
  cases hinfa : (Setlec.pureFns μ env g).infer d a' with
  | error err => rw [hinfa] at hpi; exact nomatch hpi
  | ok ta =>
  rw [hinfa] at hpi
  simp only [] at hpi
  cases hwta : (Setlec.pureFns μ env g).whnf d ta with
  | error err => rw [hwta] at hpi; exact nomatch hpi
  | ok wta =>
  rw [hwta] at hpi
  simp only [] at hpi
  have hW1 : TypeWhnfLE μ env d a' wta := by
    obtain ⟨gw, lw, -, hlw⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok wta)
    exact ⟨g, ta, hinfa, gw, lw, hlw⟩
  obtain rfl : wta = .sort ℓ := TypeWhnfLE_det hm hW1 hW
  rw [isUnitLikeTy_sort, if_neg Bool.false_ne_true] at hpi
  cases hinfta : (Setlec.pureFns μ env g).infer d ta with
  | error err => rw [hinfta] at hpi; exact nomatch hpi
  | ok sa =>
  rw [hinfta] at hpi
  simp only [] at hpi
  cases hwsa : (Setlec.pureFns μ env g).whnf d sa with
  | error err => rw [hwsa] at hpi; exact nomatch hpi
  | ok wsa =>
  rw [hwsa] at hpi
  simp only [] at hpi
  split at hpi
  · next uT =>
    have hIta : SubjInv d ta := hInf hinfa hIa'
    have hW2 : TypeWhnfLE μ env d ta (.sort uT) := by
      obtain ⟨gs, ls, -, hls⟩ :=
        whnf_peel (hwsa : whnf μ env g d sa = .ok (.sort uT))
      exact ⟨g, sa, hinfta, gs, ls, hls⟩
    obtain ⟨gt, lt, -, hlt⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok (.sort ℓ))
    have hW3 : TypeWhnfLE μ env d (.sort ℓ) (.sort uT) :=
      hT hlt hIta hW2
    obtain rfl : uT = .succ ℓ :=
      Setlec.Expr.sort.inj (TypeWhnfLE_det hm hW3 typeWhnfLE_sort)
    cases hlift : Setlec.liftFueled "level comparison"
        (Level.isEquiv (.succ ℓ) .zero)
        (m := Setlec.CheckM) with
    | error err => rw [hlift] at hpi; exact nomatch hpi
    | ok okA =>
    rw [hlift] at hpi
    simp only [] at hpi
    rw [Setlec.liftFueled.eq_def] at hlift
    split at hlift
    · next okA' hEq =>
      obtain rfl : okA' = okA := by
        simpa [pure, Except.pure] using hlift
      cases okA' with
      | true =>
        have hev := Level.isEquiv_sound hEq (fun _ => 0)
        simp only [Setlec.Level.eval] at hev
        omega
      | false =>
        cases hinfb : (Setlec.pureFns μ env g).infer d b' with
        | error err => rw [hinfb] at hpi; exact nomatch hpi
        | ok tb =>
        rw [hinfb] at hpi
        simp only [] at hpi
        cases hinftb : (Setlec.pureFns μ env g).infer d tb with
        | error err => rw [hinftb] at hpi; exact nomatch hpi
        | ok sb =>
        rw [hinftb] at hpi
        simp only [] at hpi
        cases hwsb : (Setlec.pureFns μ env g).whnf d sb with
        | error err => rw [hwsb] at hpi; exact nomatch hpi
        | ok wsb =>
        rw [hwsb] at hpi
        simp only [] at hpi
        split at hpi
        · next vT =>
          cases hliftB : Setlec.liftFueled "level comparison"
              (Level.isEquiv vT .zero) (m := Setlec.CheckM) with
          | error err => rw [hliftB] at hpi; exact nomatch hpi
          | ok okB => rw [hliftB] at hpi; exact nomatch hpi
        · exact nomatch hpi
    · exact nomatch hlift
  · exact nomatch hpi

/-! ## The summit statement: the certified-pair eval-sort simulation

**Lineage** (the arc closing its own loop): the module docstring's
trap list said from the start "(C)'s β case is
`SortSubstStable`-shaped and `SortSubstStable`'s leaf is (B)-shaped
— one mutual induction".  After the w-general species' refutation,
every surviving agreement consumer (the spine core, (B)'s
re-entries, the congruence routings) converges on exactly that one
induction; `CertZip` and the two claims below are its statement.

**The relation**: lockstep pairs — one template at two
`isEquiv`-linked level instantiations, with `defEqList`-certified
leaves.  The `cert` leaf carries a GIVEN `isDefEqCore` run at knot
fuel `fc` — the relation's index and the mutual induction's primary
measure component (a leaf cert always sits at strictly smaller knot
fuel than the claim run that exposed it: `isDefEqCore (fc+1)` opens
to `defeqLoop` over `pureFns fc`, whose cert fields run at `fc`).

**The claims are dual-success eval currency throughout**: both runs
GIVEN, conclusions are `eval`-equalities — no liveness, no
constructed runs, no syntactic level identity (the refutation's
seeds are absorbed: isEquiv slack by eval, proofIrrel stuck slack by
never claiming output identity).

**Audit records (statement-tier, before any case work — DESIGN
carries the full versions)**:
* the zip tier is `Q`-FREE — the syntactic route displaced the model
  tier for agreements, so leaf recursion consumes the (A)/(B) claims
  at `Q := True` (no descent obligation); `Q`'s surviving consumer
  is the semantic trio alone;
* leaf recursion needs the (A)-claim's cross-`PairedLeaves` at the
  leaf pair, so the claims carry `PairedLeaves s t` (and the (A)
  motive gains the concrete pairing thread at the collapse seal —
  (B)'s motive is the proved pattern);
* the measure is lexicographic
  [env declaration index, cert knot fuel `fc`, run budgets]:
  δ-template linking recurses through INSTALL certs, which live at
  the env prefix — the outer layer needs env-indexed claims and
  prefix transport (`Extend/Transport` is the named supplier);
* β-closure of the zip is shape-restricted and sufficient: whnf
  β-reduces only at the head, where a zip head-λ is a template pair
  (contractum = template body with the arg zip substituted at
  substituAND positions — leaves are never substituted INTO) or a
  `cert` leaf (decomposed by the (A)-machinery at smaller `fc`);
  asymmetric stages (one side's redex cert fails) are disciplined by
  the GIVEN runs (a stuck non-sort output contradicts the run). -/

/-- The lockstep relation.  Generated minimally for the audited
consumers: syntactic identity, certified leaves (at knot fuel `fc`),
level slack at exactly the two level-carrying nodes, and structural
congruence (what `instantiateLevelParams` crosses) — the
"one template, two instantiations, certified leaves" pairs are
derivable, not primitive. -/
inductive CertZip (μ : CheckMode) (env : Env) (fc d : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : CertZip μ env fc d e e
  | cert (a b : Expr) :
      a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
      isDefEqCore μ env fc d a b = .ok true →
      CertZip μ env fc d a b
  | sortSlack (u v : Level) :
      (∀ φ' : Name → Nat, u.eval φ' = v.eval φ') →
      CertZip μ env fc d (.sort u) (.sort v)
  | constSlack (n : Name) (us us' : List Level) :
      (∀ φ' : Name → Nat,
        us.map (Level.eval φ') = us'.map (Level.eval φ')) →
      CertZip μ env fc d (.const n us) (.const n us')
  | fvar (i : Nat) (n : Name) (ty₁ ty₂ : Expr) :
      CertZip μ env fc d ty₁ ty₂ →
      CertZip μ env fc d (.fvar i n ty₁) (.fvar i n ty₂)
  | app (f₁ a₁ f₂ a₂ : Expr) :
      CertZip μ env fc d f₁ f₂ → CertZip μ env fc d a₁ a₂ →
      CertZip μ env fc d (.app f₁ a₁) (.app f₂ a₂)
  | lam (n : Name) (ty₁ ty₂ body₁ body₂ : Expr)
      (m : Setlec.BinderMeta) :
      CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d body₁ body₂ →
      CertZip μ env fc d (.lam n ty₁ body₁ m) (.lam n ty₂ body₂ m)
  | forallE (n : Name) (ty₁ ty₂ body₁ body₂ : Expr)
      (m : Setlec.BinderMeta) :
      CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d body₁ body₂ →
      CertZip μ env fc d (.forallE n ty₁ body₁ m)
        (.forallE n ty₂ body₂ m)
  | letE (n : Name) (ty₁ ty₂ v₁ v₂ body₁ body₂ : Expr) :
      CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
      CertZip μ env fc d body₁ body₂ →
      CertZip μ env fc d (.letE n ty₁ v₁ body₁)
        (.letE n ty₂ v₂ body₂)
  | proj (s : Name) (i : Nat) (e₁ e₂ : Expr) :
      CertZip μ env fc d e₁ e₂ →
      CertZip μ env fc d (.proj s i e₁) (.proj s i e₂)

/-! ### (E): env-extension run stability — the third install-tier fact

The env-layer ruling: the zip claims stay single-env; the δ-link's
install cert (which ran at the env PREFIX of its declaration) is
transported FORWARD by (E).  Stated with the pre-build check
(DESIGN): success-lifting survives every env-consulting clause —
`find?` agrees on prefix names (`FindPreserved`; supplier:
duplicate-name installs are rejected, no shadowing), presence guards
(`natLitSupported`/`strLitSupported`/`natOpGuard`) are
`find?`-monotone and env₀-success pins them `true`, and the run's
reachable name set stays inside env₀ given the subject premise
(`ConstsBound`) plus stored-material closure (env₀'s stored exprs
are themselves bound — install-tier, fixed in clause form at the
discharge seal).  `ConstsBound`'s supplier for BOTH declared types
and values is the one install traversal: install typechecks every
declaration, inference visits every const leaf, and unknown
constants throw; recursor-rule right-hand sides ride the RecRulesOk
fold facts.  Discharge = the `CoreSub`-pattern oracle-extension
induction (the `KnotFuelMono` precedent), with the internal motive
strengthened by output-boundness. -/

/-- Every constant the expression mentions is bound in `env₀`
(hereditarily through annotations, like the leaf machinery). -/
def ConstsBound (env₀ : Env) : Expr → Prop
  | .const n _ => (env₀.find? n).isSome = true
  | .app f a => ConstsBound env₀ f ∧ ConstsBound env₀ a
  | .lam _ ty b _ => ConstsBound env₀ ty ∧ ConstsBound env₀ b
  | .forallE _ ty b _ => ConstsBound env₀ ty ∧ ConstsBound env₀ b
  | .letE _ t v b =>
      ConstsBound env₀ t ∧ ConstsBound env₀ v ∧ ConstsBound env₀ b
  | .proj _ _ e => ConstsBound env₀ e
  | .fvar _ _ ty => ConstsBound env₀ ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Setlec.Expr.sizeF]; omega)
  | simp [Setlec.Expr.sizeF]

/-- The extension is conservative on the prefix: every stored lookup
survives verbatim (no shadowing — duplicate installs are
rejected). -/
def FindPreserved (env₀ env : Env) : Prop :=
  ∀ {n : Name} {ci : Setlec.ConstantInfo},
    env₀.find? n = some ci → env.find? n = some ci

/-- **(E)**: successful runs on prefix-bound subjects are reproduced
verbatim at the extended env, knot-wide (the `CoreSub` field set). -/
def EnvExtendStable (μ : CheckMode) (env₀ env : Env) : Prop :=
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnfCore μ env₀ f d e = .ok x → whnfCore μ env f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnf μ env₀ f d e = .ok x → whnf μ env f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    inferTypeCore μ env₀ f d e = .ok x →
    inferTypeCore μ env f d e = .ok x) ∧
  (∀ {f d : Nat} {a b : Expr} {v : Bool},
    ConstsBound env₀ a → ConstsBound env₀ b →
    isDefEqCore μ env₀ f d a b = .ok v →
    isDefEqCore μ env f d a b = .ok v) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    Setlec.annotateCore μ env₀ f d e = .ok x →
    Setlec.annotateCore μ env f d e = .ok x)

/-- Pointwise eval-equal substitutions induce the same assignment
(the level side of the instantiation zip). -/
theorem substFn_eval_congr {φ : Name → Nat} :
    ∀ {lps : List Name} {us us' : List Level},
      us.map (Level.eval φ) = us'.map (Level.eval φ) →
      Setlec.Level.substFn φ lps us = Setlec.Level.substFn φ lps us'
  | [], _, _, _ => by funext n; rfl
  | k :: ks, [], [], _ => rfl
  | k :: ks, [], v' :: vs', h => nomatch h
  | k :: ks, v :: vs, [], h => nomatch h
  | k :: ks, v :: vs, v' :: vs', h => by
    injection h with h1 h2
    funext n
    simp only [Setlec.Level.substFn]
    rw [h1, substFn_eval_congr (lps := ks) h2]

/-- **One template, two instantiations, zipped**: level-instantiating
a single expression at pointwise eval-equal level lists lands in
`CertZip` — the δ-case's bridge from the spine's `isEquivList`
verdict (via `isEquivList` soundness) to the lockstep relation. -/
theorem certZip_instantiate {μ : CheckMode} {env : Env} {fc d : Nat}
    {lps : List Name} {us us' : List Level}
    (hev : ∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) :
    ∀ v : Expr, CertZip μ env fc d
      (v.instantiateLevelParams lps us)
      (v.instantiateLevelParams lps us') := by
  intro v
  induction v with
  | bvar i => exact .refl _
  | fvar i n ty ih => exact .fvar _ _ _ _ ih
  | sort u =>
    exact .sortSlack _ _ fun φ' => by
      rw [show (Setlec.Level.subst lps us u).eval φ'
          = Setlec.Level.eval (Setlec.Level.substFn φ' lps us) u from
        Setlec.Level.eval_subst φ' lps us u,
        show (Setlec.Level.subst lps us' u).eval φ'
          = Setlec.Level.eval (Setlec.Level.substFn φ' lps us') u from
        Setlec.Level.eval_subst φ' lps us' u,
        substFn_eval_congr (hev φ')]
  | const n vs =>
    exact .constSlack _ _ _ fun φ' => by
      simp only [List.map_map]
      congr 1
      funext l
      show (Setlec.Level.subst lps us l).eval φ'
        = (Setlec.Level.subst lps us' l).eval φ'
      rw [Setlec.Level.eval_subst φ' lps us l,
        Setlec.Level.eval_subst φ' lps us' l,
        substFn_eval_congr (hev φ')]
  | app f a ihf iha => exact .app _ _ _ _ ihf iha
  | lam n ty body m iht ihb => exact .lam _ _ _ _ _ _ iht ihb
  | forallE n ty body m iht ihb => exact .forallE _ _ _ _ _ _ iht ihb
  | letE n ty val body iht ihv ihb =>
    exact .letE _ _ _ _ _ _ _ iht ihv ihb
  | lit l => exact .refl _
  | proj s i e ih => exact .proj _ _ _ _ ih

/-- Per-argument extraction from a spine certificate: a `true`
`defEqList` verdict yields the pairwise `defeq` runs (and the length
equation). -/
theorem defEqList_extract {r : Setlec.CoreFns Setlec.CheckM}
    {env : Env} {d : Nat} :
    ∀ {as bs : List Expr},
      Setlec.defEqList r env d as bs = .ok true →
      as.length = bs.length ∧
      ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        r.defeq d as[i] bs[i] = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil =>
      exact ⟨rfl, fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)⟩
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      unfold Setlec.defEqList at h
      simp only [Bind.bind, Except.bind] at h
      cases hd : r.defeq d a b with
      | error err => rw [hd] at h; exact nomatch h
      | ok c =>
        rw [hd] at h
        simp only [] at h
        cases c with
        | false => exact nomatch h
        | true =>
          rw [if_pos rfl] at h
          obtain ⟨hlen, hall⟩ := ih h
          refine ⟨by simp [hlen], ?_⟩
          intro i h₁ h₂
          cases i with
          | zero => simpa using hd
          | succ i =>
            simpa using hall i (by simpa using h₁) (by simpa using h₂)

/-- `EvalEqList` as a map equality (the bridge from `isEquivList`
soundness to `constSlack`'s premise). -/
theorem evalEqList_map {φ : Name → Nat} :
    ∀ {us vs : List Level}, Setlec.Level.EvalEqList φ us vs →
      us.map (Level.eval φ) = vs.map (Level.eval φ)
  | [], [], _ => rfl
  | u :: us, v :: vs, h => by
    obtain ⟨h1, h2⟩ := h
    simp only [List.map]
    rw [h1, evalEqList_map h2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Zip a spine fold: a zipped head applied to pointwise-certified
argument lists stays zipped. -/
theorem certZip_mkAppN {μ : CheckMode} {env : Env} {fc d : Nat} :
    ∀ {as bs : List Expr} {f₁ f₂ : Expr},
      CertZip μ env fc d f₁ f₂ →
      as.length = bs.length →
      (∀ x ∈ as, x.looseBVarsBounded 0 = true) →
      (∀ x ∈ bs, x.looseBVarsBounded 0 = true) →
      (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        isDefEqCore μ env fc d as[i] bs[i] = .ok true) →
      CertZip μ env fc d (Setlec.Expr.mkAppN f₁ as)
        (Setlec.Expr.mkAppN f₂ bs) := by
  intro as
  induction as with
  | nil =>
    intro bs f₁ f₂ hz hlen hba hbb hcert
    cases bs with
    | nil => exact hz
    | cons b bs => exact nomatch hlen
  | cons a as ih =>
    intro bs f₁ f₂ hz hlen hba hbb hcert
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      simp only [Setlec.Expr.mkAppN]
      exact ih
        (.app _ _ _ _ hz
          (.cert _ _ (hba a (List.mem_cons_self ..))
            (hbb b (List.mem_cons_self ..))
            (hcert 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))))
        (by simpa using hlen)
        (fun x hx => hba x (List.mem_cons_of_mem _ hx))
        (fun x hx => hbb x (List.mem_cons_of_mem _ hx))
        (fun i h₁ h₂ =>
          hcert (i + 1)
            (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega))

/-- Substitution leaves bounded expressions verbatim (all loose
bvars below `j ≤ k` — the closed-cert-leaf case's engine). -/
theorem instantiate1_bounded : ∀ {x v : Expr} {j k : Nat},
    x.looseBVarsBounded j = true → j ≤ k →
    x.instantiate1 v k = x := by
  intro x
  induction x with
  | bvar i =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at h
    simp only [Setlec.Expr.instantiate1]
    rw [if_neg (by omega), if_neg (by omega)]
  | fvar idx n ty ih => intro v j k h hjk; rfl
  | sort u => intro v j k h hjk; rfl
  | const n us => intro v j k h hjk; rfl
  | app f a ihf iha =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, ihf h.1 hjk, iha h.2 hjk]
  | lam n ty body m iht ihb =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, iht h.1 hjk,
      ihb h.2 (Nat.succ_le_succ hjk)]
  | forallE n ty body m iht ihb =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, iht h.1 hjk,
      ihb h.2 (Nat.succ_le_succ hjk)]
  | letE n ty val body iht ihv ihb =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, iht h.1.1 hjk,
      ihv h.1.2 hjk, ihb h.2 (Nat.succ_le_succ hjk)]
  | lit l => intro v j k h hjk; rfl
  | proj s i e ih =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded] at h
    simp only [Setlec.Expr.instantiate1, ih h hjk]

/-- **Substitution lemma (i)**: one template, two zipped args — the
`refl`-leaf replacement (a `refl` body does not survive
substitution; this is what it becomes). -/
theorem certZip_instantiate1 {μ : CheckMode} {env : Env} {fc d : Nat}
    {a₁ a₂ : Expr} (hz : CertZip μ env fc d a₁ a₂) :
    ∀ (e : Expr) (k : Nat),
      CertZip μ env fc d (e.instantiate1 a₁ k)
        (e.instantiate1 a₂ k) := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    by_cases h : i = k
    · rw [if_pos h, if_pos h]; exact hz
    · rw [if_neg h, if_neg h]
      by_cases h2 : i > k <;> exact .refl _
  | fvar idx n ty ih => intro k; exact .refl _
  | sort u => intro k; exact .refl _
  | const n us => intro k; exact .refl _
  | app f a ihf iha =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .app _ _ _ _ (ihf k) (iha k)
  | lam n ty body m iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .lam _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | forallE n ty body m iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .forallE _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | letE n ty val body iht ihv ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .letE _ _ _ _ _ _ _ (iht k) (ihv k) (ihb (k + 1))
  | lit l => intro k; exact .refl _
  | proj s i e ih =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .proj _ _ _ _ (ih k)

/-- **Substitution lemma (ii)**: zipped bodies at zipped args stay
zipped — `refl` leaves by (i), `cert` leaves verbatim by closedness
(the summit map's Finding 1), congruence structurally.  The β case's
engine. -/
theorem certZip_subst {μ : CheckMode} {env : Env} {fc d : Nat}
    {a₁ a₂ : Expr} (ha : CertZip μ env fc d a₁ a₂) :
    ∀ {body₁ body₂ : Expr}, CertZip μ env fc d body₁ body₂ →
    ∀ k : Nat,
      CertZip μ env fc d (body₁.instantiate1 a₁ k)
        (body₂.instantiate1 a₂ k) := by
  intro body₁ body₂ hb
  induction hb with
  | refl e => intro k; exact certZip_instantiate1 ha e k
  | cert x y hbx hby hc =>
    intro k
    rw [instantiate1_bounded hbx (Nat.zero_le k),
      instantiate1_bounded hby (Nat.zero_le k)]
    exact .cert _ _ hbx hby hc
  | sortSlack u v hev => intro k; exact .sortSlack _ _ hev
  | constSlack n us us' hev => intro k; exact .constSlack _ _ _ hev
  | fvar i n ty₁ ty₂ hty ih => intro k; exact .fvar _ _ _ _ hty
  | app f₁ x₁ f₂ x₂ hf hx ihf ihx =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .app _ _ _ _ (ihf k) (ihx k)
  | lam n ty₁ ty₂ b₁ b₂ m hty hbody iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .lam _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | forallE n ty₁ ty₂ b₁ b₂ m hty hbody iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .forallE _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody iht ihv ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .letE _ _ _ _ _ _ _ (iht k) (ihv k) (ihb (k + 1))
  | proj s i e₁ e₂ he ih =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .proj _ _ _ _ (ih k)

/-- `proofIrrel` never certifies two literal sorts: the subject's
type-chain pins `uT` to a double successor, refuting the `Prop`
check by eval arithmetic (the probe walk, at literal subjects). -/
theorem proofIrrel_sorts_absurd {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g d : Nat} {u v : Level}
    (hpi : Setlec.proofIrrel (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) = .ok true) : False := by
  have hdet := KnotFuelDet_of_mono hm
  unfold Setlec.proofIrrel at hpi
  simp only [Bind.bind, Except.bind] at hpi
  cases hinfa : (Setlec.pureFns μ env g).infer d (.sort u) with
  | error err => rw [hinfa] at hpi; exact nomatch hpi
  | ok ta =>
  rw [hinfa] at hpi
  simp only [] at hpi
  obtain rfl : ta = .sort (.succ u) := inferTypeCore_sort_out hinfa
  cases hwta : (Setlec.pureFns μ env g).whnf d (.sort (.succ u)) with
  | error err => rw [hwta] at hpi; exact nomatch hpi
  | ok wta =>
  rw [hwta] at hpi
  simp only [] at hpi
  obtain rfl : wta = .sort (.succ u) := whnf_sort_out hdet hwta
  rw [isUnitLikeTy_sort, if_neg Bool.false_ne_true] at hpi
  cases hinfta : (Setlec.pureFns μ env g).infer d (.sort (.succ u)) with
  | error err => rw [hinfta] at hpi; exact nomatch hpi
  | ok sa =>
  rw [hinfta] at hpi
  simp only [] at hpi
  obtain rfl : sa = .sort (.succ (.succ u)) :=
    inferTypeCore_sort_out hinfta
  cases hwsa : (Setlec.pureFns μ env g).whnf d
      (.sort (.succ (.succ u))) with
  | error err => rw [hwsa] at hpi; exact nomatch hpi
  | ok wsa =>
  rw [hwsa] at hpi
  simp only [] at hpi
  obtain rfl : wsa = .sort (.succ (.succ u)) := whnf_sort_out hdet hwsa
  simp only [] at hpi
  cases hlift : Setlec.liftFueled "level comparison"
      (Level.isEquiv (.succ (.succ u)) .zero)
      (m := Setlec.CheckM) with
  | error err => rw [hlift] at hpi; exact nomatch hpi
  | ok okA =>
  rw [hlift] at hpi
  simp only [] at hpi
  rw [Setlec.liftFueled.eq_def] at hlift
  split at hlift
  · next okA' hEq =>
    obtain rfl : okA' = okA := by
      simpa [pure, Except.pure] using hlift
    cases okA' with
    | true =>
      have hev := Level.isEquiv_sound hEq (fun _ => 0)
      simp only [Setlec.Level.eval] at hev
      omega
    | false =>
      cases hinfb : (Setlec.pureFns μ env g).infer d (.sort v) with
      | error err => rw [hinfb] at hpi; exact nomatch hpi
      | ok tb =>
      rw [hinfb] at hpi
      simp only [] at hpi
      cases hinftb : (Setlec.pureFns μ env g).infer d tb with
      | error err => rw [hinftb] at hpi; exact nomatch hpi
      | ok sb =>
      rw [hinftb] at hpi
      simp only [] at hpi
      cases hwsb : (Setlec.pureFns μ env g).whnf d sb with
      | error err => rw [hwsb] at hpi; exact nomatch hpi
      | ok wsb =>
      rw [hwsb] at hpi
      simp only [] at hpi
      split at hpi
      · next vT =>
        cases hliftB : Setlec.liftFueled "level comparison"
            (Level.isEquiv vT .zero) (m := Setlec.CheckM) with
        | error err => rw [hliftB] at hpi; exact nomatch hpi
        | ok okB => rw [hliftB] at hpi; exact nomatch hpi
      · exact nomatch hpi
  · exact nomatch hlift

/-- `stuckIrrel` never certifies two literal sorts (the five-way
walk at literal subjects; the fallback is
`proofIrrel_sorts_absurd`). -/
theorem stuckIrrel_sorts_absurd {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g d : Nat} {u v : Level}
    (hsi : Setlec.stuckIrrel μ (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) = .ok true) : False := by
  have hdet := KnotFuelDet_of_mono hm
  unfold Setlec.stuckIrrel at hsi
  simp only [Bind.bind, Except.bind] at hsi
  cases h1 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) with
  | error err => rw [h1] at hsi; exact nomatch hsi
  | ok c1 =>
  rw [h1] at hsi
  simp only [] at hsi
  cases c1 with
  | true => unfold Setlec.pairEtaCert at h1; exact nomatch h1
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h2 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort v) (.sort u) with
  | error err => rw [h2] at hsi; exact nomatch hsi
  | ok c2 =>
  rw [h2] at hsi
  simp only [] at hsi
  cases c2 with
  | true => unfold Setlec.pairEtaCert at h2; exact nomatch h2
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h3 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) with
  | error err => rw [h3] at hsi; exact nomatch hsi
  | ok c3 =>
  rw [h3] at hsi
  simp only [] at hsi
  cases c3 with
  | true =>
    unfold Setlec.structEtaCert at h3
    simp only [Bind.bind, Except.bind] at h3
    cases hinf3 : (Setlec.pureFns μ env g).infer d (.sort v) with
    | error err => rw [hinf3] at h3; exact nomatch h3
    | ok tb =>
    rw [hinf3] at h3
    simp only [] at h3
    cases hw3 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw3] at h3; exact nomatch h3
    | ok wtb =>
    rw [hw3] at h3
    simp only [] at h3
    unfold Setlec.structEtaCertWith at h3
    exact nomatch h3
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h4 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort v) (.sort u) with
  | error err => rw [h4] at hsi; exact nomatch hsi
  | ok c4 =>
  rw [h4] at hsi
  simp only [] at hsi
  cases c4 with
  | true =>
    unfold Setlec.structEtaCert at h4
    simp only [Bind.bind, Except.bind] at h4
    cases hinf4 : (Setlec.pureFns μ env g).infer d (.sort u) with
    | error err => rw [hinf4] at h4; exact nomatch h4
    | ok tb =>
    rw [hinf4] at h4
    simp only [] at h4
    cases hw4 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw4] at h4; exact nomatch h4
    | ok wtb =>
    rw [hw4] at h4
    simp only [] at h4
    unfold Setlec.structEtaCertWith at h4
    exact nomatch h4
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h5 : Setlec.structUnitCert (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) with
  | error err => rw [h5] at hsi; exact nomatch hsi
  | ok c5 =>
  rw [h5] at hsi
  simp only [] at hsi
  cases c5 with
  | true =>
    unfold Setlec.structUnitCert at h5
    simp only [Bind.bind, Except.bind] at h5
    cases hinf5 : (Setlec.pureFns μ env g).infer d (.sort u) with
    | error err => rw [hinf5] at h5; exact nomatch h5
    | ok ta =>
    rw [hinf5] at h5
    simp only [] at h5
    obtain rfl : ta = .sort (.succ u) := inferTypeCore_sort_out hinf5
    cases hw5 : (Setlec.pureFns μ env g).whnf d (.sort (.succ u)) with
    | error err => rw [hw5] at h5; exact nomatch h5
    | ok wta =>
    rw [hw5] at h5
    simp only [] at h5
    obtain rfl : wta = .sort (.succ u) := whnf_sort_out hdet hw5
    exact nomatch h5
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  exact proofIrrel_sorts_absurd hm hsi

/-- **The sort-sort cert inversion** (the summit's stuck-stuck
terminal and the cert case's base): a certified pair of literal
sorts has eval-equal levels. -/
theorem isDefEqCore_sorts_eval {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (hm : KnotFuelMono μ env)
    {fc d : Nat} {u v : Level}
    (h : isDefEqCore μ env fc d (.sort u) (.sort v) = .ok true) :
    u.eval φ = v.eval φ := by
  have hdet := KnotFuelDet_of_mono hm
  cases fc with
  | zero => exact nomatch h
  | succ fc =>
  rw [Setlec.isDefEqCore_succ] at h
  obtain ⟨L, hL⟩ := Setlec.defeqLoopFuel_succ
  unfold Setlec.defeqBody at h
  rw [hL, defeqLoop_succ] at h
  rcases defeqStep_decompose h with heq | ⟨a', b', hwa, hwb, hcert⟩
  · rw [Setlec.Expr.sort.inj heq]
  · obtain rfl : a' = .sort u :=
      hdet.2.2.1 hwa (whnfCore_sort_run (whnfCore_pos hwa))
    obtain rfl : b' = .sort v :=
      hdet.2.2.1 hwb (whnfCore_sort_run (whnfCore_pos hwb))
    cases hcert with
    | syn => rfl
    | irrel _ _ hpi => exact (proofIrrel_sorts_absurd hm hpi).elim
    | natL _ _ a₂ hrn hk => exact nomatch hrn
    | natR _ _ b₂ hrnA hrnB hk => exact nomatch hrnB
    | deltaL _ _ a₂ hu hk => exact nomatch hu
    | deltaR _ _ b₂ hu hk => exact nomatch hu
    | deltaB _ _ a₂ b₂ hua hub hk => exact nomatch hua
    | spine _ _ hs =>
      unfold Setlec.defeqSpine at hs
      exact nomatch hs
    | sorts _ _ hiseq => exact Level.isEquiv_sound hiseq φ
    | rescue _ _ hsi => exact (stuckIrrel_sorts_absurd hm hsi).elim

/-- Spine arguments of a bvar-closed expression are bvar-closed. -/
theorem getAppArgs_bounded : ∀ {e : Expr},
    e.looseBVarsBounded 0 = true →
    ∀ x ∈ e.getAppArgs, x.looseBVarsBounded 0 = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h x hx
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.getAppArgs] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ihf h.1 x hx
    · simp only [List.mem_singleton] at hx
      exact hx ▸ h.2
  | bvar i => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | fvar i n ty ih => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | sort u => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | const n us => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | lam n ty body m iht ihb =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | forallE n ty body m iht ihb =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | letE n ty val body iht ihv ihb =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | lit l => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | proj sn i pe ih =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx

/-- **Summit claim, subject form**: zipped pairs whose members'
whnf chains both reach literal sorts have eval-equal levels.  The
spine core and (A)'s remaining routings collapse onto this. -/
def ZipWhnfSortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    CertZip μ env fc d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Summit claim, type form**: zipped pairs on which both sort
computations succeed have equal numerals.  (B)'s re-entries and the
congruence routings collapse onto this. -/
def ZipSortOfAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {fc d : Nat} {s t : Expr} {u v : Nat},
    CertZip μ env fc d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t →
    SortOfLE μ env φ d s u → SortOfLE μ env φ d t v → u = v

/-! ### The summit skeleton (build order, step 2)

The one induction, on the audited lexicographic measure — outer
strong induction on the cert fuel `fc`, inner on the loop-budget sum
— with `ZipBelow` as the continuation contract handed to the routed
cases (the house pattern: the recursion travels as a premise, cases
seal separately).  Inline here: `refl` (determinism), `sortSlack`
(stuck + eval), and the four stuck-shape vacuities (`fvar`, `lam`,
`forallE`; `lit` rides `refl`).  Routed: the cert case (the shells'
template — build step 3), the constSlack both-δ case (needs the
`StoredWF` supply kit), and the three sim roots (`app`, `letE`,
`proj` — the knot-fuel tier, iota getting its full treatment when
reached). -/

/-- The summit claim strictly below the measure `(fc, r)` —
lexicographically: smaller cert fuel, or equal fuel and smaller
loop-budget sum. -/
def ZipBelow (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (fc r : Nat) : Prop :=
  ∀ {fc' d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    (fc' < fc ∨ (fc' = fc ∧ la + lb < r)) →
    CertZip μ env fc' d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- Stored definition/theorem values are fvar-free, bvar-closed and
leaf-bounded — the install-tier fact the constSlack case's
continuations consume (the ledgered value-closedness family, in the
form the summit reads). -/
def StoredWF (env : Env) : Prop :=
  ∀ {n : Name} {cv : Setlec.ConstantVal} {value : Expr},
    ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
      env.find? n = some (.thmInfo cv value)) →
    value.fvarLeaves = [] ∧ value.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded value

/-- **Routed: the cert case** (the shells' template — a certified
pair with both sort convergences, the recursion available strictly
below). -/
def ZipCertCase (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {a b : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ fc (la + lb) →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    isDefEqCore μ env fc d a b = .ok true →
    SubjInv d a → SubjInv d b → PairedLeaves a b →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the constSlack both-δ case** (same head at eval-equal
levels; the continuations are `certZip_instantiate` zips of one
stored value, `StoredWF` supplying their invariants). -/
def ZipConstCase (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {us us' : List Level}
    {ℓa ℓb : Level},
    ZipBelow μ env φ fc (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la (.const n us)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb (.const n us')
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the app sim root** (the knot-fuel tier; the cert-headed
sub-case is the mutual knot with binder opening — full pre-build
treatment at its seal). -/
def ZipAppCase (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {f₁ x₁ f₂ x₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ fc (la + lb) →
    CertZip μ env fc d f₁ f₂ → CertZip μ env fc d x₁ x₂ →
    SubjInv d (.app f₁ x₁) → SubjInv d (.app f₂ x₂) →
    PairedLeaves (.app f₁ x₁) (.app f₂ x₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la (.app f₁ x₁)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb (.app f₂ x₂)
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the letE sim root** (lockstep zeta through
`certZip_subst`, inside the knot-fuel tier). -/
def ZipLetECase (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name}
    {ty₁ ty₂ v₁ v₂ b₁ b₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ fc (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
    CertZip μ env fc d b₁ b₂ →
    SubjInv d (.letE n ty₁ v₁ b₁) → SubjInv d (.letE n ty₂ v₂ b₂) →
    PairedLeaves (.letE n ty₁ v₁ b₁) (.letE n ty₂ v₂ b₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (.letE n ty₁ v₁ b₁) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (.letE n ty₂ v₂ b₂) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the proj sim root** (whnf-of-scrutinee lockstep +
`projLitToCtor` + the structural rule; its seal carries the
struct-name-slack audit flagged at the map). -/
def ZipProjCase (μ : CheckMode) (env : Env) (φ : Name → Nat) : Prop :=
  ∀ {fc d ga la gb lb i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {ℓa ℓb : Level},
    ZipBelow μ env φ fc (la + lb) →
    CertZip μ env fc d e₁ e₂ →
    SubjInv d (.proj sn i e₁) → SubjInv d (.proj sn i e₂) →
    PairedLeaves (.proj sn i e₁) (.proj sn i e₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (.proj sn i e₁) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (.proj sn i e₂) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- Fvar leaves re-core to themselves (value branch). -/
theorem whnfCore_fvar_run {μ : CheckMode} {env : Env} {f d : Nat}
    {i : Nat} {n : Name} {ty : Expr} (hf : 1 ≤ f) :
    whnfCore μ env f d (.fvar i n ty) = .ok (.fvar i n ty) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- Lams re-core to themselves (value branch). -/
theorem whnfCore_lam_run {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {ty body : Expr} {m : Setlec.BinderMeta} (hf : 1 ≤ f) :
    whnfCore μ env f d (.lam n ty body m) = .ok (.lam n ty body m) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- **The summit skeleton**: `ZipWhnfSortAgree` from the five routed
cases, by the one lexicographic induction; the determinism, stuck
and slack cases are inline. -/
theorem zipWhnfSortAgree_of {φ : Name → Nat}
    (hm : KnotFuelMono μ env)
    (hCert : ZipCertCase μ env φ) (hConst : ZipConstCase μ env φ)
    (hApp : ZipAppCase μ env φ) (hLet : ZipLetECase μ env φ)
    (hProj : ZipProjCase μ env φ) :
    ZipWhnfSortAgree μ env φ := by
  have main : ∀ fc r {d ga la gb lb : Nat} {s t : Expr}
      {ℓa ℓb : Level}, la + lb ≤ r →
      CertZip μ env fc d s t →
      SubjInv d s → SubjInv d t → PairedLeaves s t →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
        = .ok (.sort ℓa) →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
        = .ok (.sort ℓb) →
      ℓa.eval φ = ℓb.eval φ := by
    intro fc
    induction fc using Nat.strongRecOn with
    | ind fc ihfc =>
    intro r
    induction r with
    | zero =>
      intro d ga la gb lb s t ℓa ℓb hle hz hIs hIt hp ha hb
      obtain rfl : la = 0 := by omega
      exact nomatch ha
    | succ r ihr =>
      intro d ga la gb lb s t ℓa ℓb hle hz hIs hIt hp ha hb
      have below : ZipBelow μ env φ fc (la + lb) := by
        intro fc' d' ga' la' gb' lb' s' t' ℓa' ℓb' hlt hz' hIs' hIt'
          hp' ha' hb'
        rcases hlt with hlt | ⟨rfl, hlt⟩
        · exact ihfc fc' hlt (la' + lb') (Nat.le_refl _) hz' hIs'
            hIt' hp' ha' hb'
        · exact ihr (by omega) hz' hIs' hIt' hp' ha' hb'
      cases hz with
      | refl e =>
        rw [Setlec.Expr.sort.inj (whnfLoop_det hm ha hb)]
      | cert a b hba hbb hc =>
        exact hCert below hba hbb hc hIs hIt hp ha hb
      | sortSlack u v hev =>
        have h1 : Expr.sort ℓa = Expr.sort u :=
          loop_stuck_out hm ha (whnfCore_sort_run (Nat.le_refl 1))
            (fun _ => reduceNat_sort) unfoldDefinition_sort
        have h2 : Expr.sort ℓb = Expr.sort v :=
          loop_stuck_out hm hb (whnfCore_sort_run (Nat.le_refl 1))
            (fun _ => reduceNat_sort) unfoldDefinition_sort
        rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
        exact hev φ
      | constSlack n us us' hev => exact hConst below hev ha hb
      | fvar i nm ty₁ ty₂ hty =>
        exact nomatch (loop_stuck_out hm ha
          (whnfCore_fvar_run (Nat.le_refl 1))
          (fun _ => reduceNat_fvar) unfoldDefinition_fvar)
      | lam n ty₁ ty₂ b₁ b₂ m hty hbody =>
        exact nomatch (loop_stuck_out hm ha
          (whnfCore_lam_run (Nat.le_refl 1))
          (fun _ => reduceNat_lam) unfoldDefinition_lam)
      | forallE n ty₁ ty₂ b₁ b₂ m hty hbody =>
        exact nomatch (loop_stuck_out hm ha
          (whnfCore_forallE_run (Nat.le_refl 1))
          (fun _ => reduceNat_forallE) unfoldDefinition_forallE)
      | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody =>
        exact hLet below hty hval hbody hIs hIt hp ha hb
      | app f₁ x₁ f₂ x₂ hf hx =>
        exact hApp below hf hx hIs hIt hp ha hb
      | proj sn i e₁ e₂ he =>
        exact hProj below he hIs hIt hp ha hb
  intro fc d ga la gb lb s t ℓa ℓb hz hIs hIt hp ha hb
  exact main fc (la + lb) (Nat.le_refl _) hz hIs hIt hp ha hb

/-- **The both-δ core COLLAPSED onto the summit**: the spine facts
zip the pair (head by `constSlack` through `isEquivList` soundness,
args as `.cert` leaves through `defEqList_extract`), and
`ZipWhnfSortAgree` concludes. -/
theorem deltaSpineSortAgree_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipWhnfSortAgree μ env φ) :
    DeltaSpineSortAgree μ env φ Q := by
  intro fc d ga la gb lb a' b' ℓa ℓb hIa hIb hPab _hQ hs hla hlb
  unfold Setlec.defeqSpine at hs
  split at hs
  · next n us heqa =>
    split at hs
    · next n' us' heqb =>
      split at hs
      · next hcond =>
        obtain ⟨rfl, hlen⟩ := hcond
        split at hs
        · next heql =>
          obtain ⟨hlen', hcerts⟩ := defEqList_extract hs
          have hzip : CertZip μ env fc d a' b' := by
            rw [← Setlec.Expr.mkAppN_getApp a',
              ← Setlec.Expr.mkAppN_getApp b', heqa, heqb]
            exact certZip_mkAppN
              (.constSlack n us us' fun φ' =>
                evalEqList_map (Setlec.Level.isEquivList_sound heql φ'))
              hlen' (getAppArgs_bounded hIa.2.1)
              (getAppArgs_bounded hIb.2.1) hcerts
          exact hZ hzip hIa hIb hPab hla hlb
        · exact nomatch hs
      · exact nomatch hs
    · exact nomatch hs
  · exact nomatch hs

/-- **The branch primitive at the summit**: `EnsureSortAgreeRQ` with
the spine core discharged onto `ZipWhnfSortAgree`.  (The trio legs
still route through the refuted transport species pending the
semantic discharge — this composite tracks the live frontier.) -/
theorem ensureSortAgreeR_of_summit {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hZ : ZipWhnfSortAgree μ env φ) :
    EnsureSortAgreeRQ μ env φ Q :=
  have hD : DeltaSpineSortAgree μ env φ Q :=
    deltaSpineSortAgree_of (φ := φ) (Q := Q) hZ
  ensureSortAgreeR_of_core (Q := Q) hB hTC hTD hTN hIC hID hIN hInf
    hLC hLD hLN hQC hQD hQN hQs hD

/-! ### The public claims collapse onto the summit

The `.cert` leaf absorbs the entire top level: a certified pair IS a
zipped pair, so both public claims are one-line corollaries of the
summit claims.  The landed 25-case shells are thereby superseded as
DISCHARGE routes — but not deleted: their case work is the summit
induction's `.cert`-case template (the mutual knot's design: the
summit's cert case decomposes the cert run exactly as the shells do,
with leaf certs at strictly smaller knot fuel feeding the ih). -/

/-- **(A) collapses onto the summit**: `EnsureSortAgreeRQ` from
`ZipWhnfSortAgree` alone, via the `.cert` leaf. -/
theorem ensureSortAgreeRQ_of_zip {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipWhnfSortAgree μ env φ) :
    EnsureSortAgreeRQ μ env φ Q := by
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwsa hba hLa hwsb hbb hLb hp _hQ
    h₁ h₂
  obtain ⟨ga, la, -, hla⟩ := whnf_peel h₁
  obtain ⟨gb, lb, -, hlb⟩ := whnf_peel h₂
  exact hZ (.cert a b hba hbb hc) (SubjInv.of_pair hwsa hba hLa hp)
    (SubjInv.of_pair_right hwsb hbb hLb hp) hp hla hlb

/-- **(B) collapses onto the summit**: `SortOfAgreeRQ` from
`ZipSortOfAgree` alone, via the `.cert` leaf. -/
theorem sortOfAgreeRQ_of_zip {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipSortOfAgree μ env φ) :
    SortOfAgreeRQ μ env φ Q := by
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp _hQ h₁ h₂
  exact hZ (.cert a b hba hbb hc) (SubjInv.of_pair hwsa hba hLa hp)
    (SubjInv.of_pair_right hwsb hbb hLb hp) hp
    (SortOfLE_of_run h₁) (SortOfLE_of_run h₂)

/-- The slot-free (B) shell: `SortOfAgreeR` as the `Q := True`
instance. -/
theorem sortOfAgreeR_of {φ : Name → Nat}
    (hm : KnotFuelMono μ env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hP : ProbeTySortVacuity μ env fun _ _ _ => True)
    (hR : RescueTySortVacuity μ env fun _ _ _ => True)
    (hLam : LamTySortVacuity μ env)
    (hZ : NatZeroTySortAgree μ env φ)
    (hSL : NatSuccLTySortAgree μ env φ)
    (hSR : NatSuccRTySortAgree μ env φ)
    (hStL : StrLTySortAgree μ env φ) (hStR : StrRTySortAgree μ env φ)
    (hF : FvarTySortAgree μ env φ) (hK : ConstTySortAgree μ env φ)
    (hSp : SpineTySortAgree μ env φ fun _ _ _ => True)
    (hPi : PiCongTySortAgree μ env φ fun _ _ _ => True)
    (hAp : AppCongTySortAgree μ env φ fun _ _ _ => True)
    (hPj : ProjCongTySortAgree μ env φ fun _ _ _ => True) :
    SortOfAgreeR μ env φ := by
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp h₁ h₂
  exact sortOfAgreeRQ_of (Q := fun _ _ _ => True) hm hTC hTD hTN
    hIC hID hIN hLC hLD hLN
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun h => h)
    hP hR hLam hZ hSL hSR hStL hStR hF hK hSp hPi hAp hPj
    hc hwsa hba hLa hwsb hbb hLb hp trivial h₁ h₂

end Discharge

end Setlec.SetR.Interp2
