import Setlec.SetR.Annot.Canon
import Setlec.Verify.InferLeaves
import Setlec.Verify.LeavesPres
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

/-- The spine handler at a fixed knot fuel — the one seam between
the cert-loop template and its two consumers (the (A)-shell's
`SpineSortAgree` instance; the summit's zip-and-recurse). -/
def SpineHandler (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) (fc : Nat) : Prop :=
  ∀ {l d ga la gb lb f₁ f₂ : Nat} {a b a' b' : Expr} {ℓa ℓb : Level},
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

/-- **The dual-(A) shell**: `EnsureSortAgreeRQ` from the obligations
and the routed hypotheses.  The `SubjInv` package enters from the
claim's own guards (`SubjInv.of_pair`/`.of_pair_right`) and travels
along the loop's head steps by the `InvPreserve*F` supply chain;
the abstract pair slot `Q` enters from the claim's `Q`-premise and
travels by the `QPreserve*F` chain plus symmetry — subjects here
evolve by head steps only (congruence routes wholesale to
the spine handler), so no descent preservation is needed.

**The cert-loop template, extracted** (fixed knot fuel `fc`; the
spine handler is a per-`fc` hypothesis, so both the (A)-shell and the
summit's cert case consume ONE proof — the shell instantiates it with
`SpineSortAgree`, the summit with the zip construction feeding
`ZipBelow` at the decreased cert fuel). -/
theorem certLoop_sortAgree {μ : CheckMode} {env : Env}
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
    (fc : Nat) (hSp : SpineHandler μ env φ Q fc) :
    ∀ (L : Nat) {d : Nat} {a b : Expr},
      Setlec.defeqLoop μ (Setlec.pureFns μ env fc) env d L a b
        = .ok true →
      SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
      ∀ {ga la gb lb : Nat} {ℓa ℓb : Level},
        Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a
          = .ok (.sort ℓa) →
        Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b
          = .ok (.sort ℓb) →
        ℓa.eval φ = ℓb.eval φ := by
  have hdet := KnotFuelDet_of_mono hm
  intro L
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
        exact hSp hIa hIb hPab hQab hc0 hwa hwb hs ha hb
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
/-- **The dual-(A) shell** on the extracted template. -/
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
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwsa hba hLa hwsb hbb hLb hp hQ h₁ h₂
  cases fc with
  | zero => exact nomatch hc
  | succ fc =>
    rw [Setlec.isDefEqCore_succ] at hc
    obtain ⟨ga, la, -, hla⟩ := whnf_peel h₁
    obtain ⟨gb, lb, -, hlb⟩ := whnf_peel h₂
    have hSp : SpineHandler μ env φ Q fc := by
      intro l d ga la gb lb f₁ f₂ a b a' b' ℓa ℓb
        hIa hIb hPab hQab hc0 hwa hwb hs ha hb
      exact hS hIa hIb hPab hQab hc0 hwa hwb hs ha hb
    exact certLoop_sortAgree (φ := φ) (Q := Q) hm hIC hID hIN
      hLC hLD hLN hQC hQD hQN
      hQs hP hR hE hN fc hSp Setlec.defeqLoopFuel hc
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
    (φ : Name → Nat) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    CertZip μ env fc d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Summit claim, type form**: zipped pairs on which both sort
computations succeed have equal numerals.  (B)'s re-entries and the
congruence routings collapse onto this. -/
def ZipSortOfAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d : Nat} {s t : Expr} {u v : Nat},
    CertZip μ env fc d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
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
    (Q : Nat → Expr → Expr → Prop) (fc g r : Nat) : Prop :=
  ∀ {fc' d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    (fc' < fc ∨ (fc' = fc ∧
      (ga + gb < g ∨ (ga + gb = g ∧ la + lb < r)))) →
    CertZip μ env fc' d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
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

/-- The fc-only recursion contract (what the cert case actually
consumes — its spine feeds strictly smaller cert fuel, nothing
else; consumers can therefore supply it from ANY measure
position). -/
def ZipBelowFc (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) (fc : Nat) : Prop :=
  ∀ {fc' d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    fc' < fc →
    CertZip μ env fc' d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the cert case** (the shells' template — a certified
pair with both sort convergences, the recursion available at
strictly smaller cert fuel). -/
def ZipCertCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {a b : Expr} {ℓa ℓb : Level},
    ZipBelowFc μ env φ Q fc →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    isDefEqCore μ env fc d a b = .ok true →
    SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the constSlack both-δ case** (same head at eval-equal
levels; the continuations are `certZip_instantiate` zips of one
stored value, `StoredWF` supplying their invariants). -/
def ZipConstCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {us us' : List Level}
    {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    Q d (.const n us) (.const n us') →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la (.const n us)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb (.const n us')
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the app sim root** (the knot-fuel tier; the cert-headed
sub-case is the mutual knot with binder opening — full pre-build
treatment at its seal). -/
def ZipAppCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {f₁ x₁ f₂ x₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d f₁ f₂ → CertZip μ env fc d x₁ x₂ →
    SubjInv d (.app f₁ x₁) → SubjInv d (.app f₂ x₂) →
    PairedLeaves (.app f₁ x₁) (.app f₂ x₂) →
    Q d (.app f₁ x₁) (.app f₂ x₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la (.app f₁ x₁)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb (.app f₂ x₂)
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the letE sim root** (lockstep zeta through
`certZip_subst`, inside the knot-fuel tier). -/
def ZipLetECase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name}
    {ty₁ ty₂ v₁ v₂ b₁ b₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
    CertZip μ env fc d b₁ b₂ →
    SubjInv d (.letE n ty₁ v₁ b₁) → SubjInv d (.letE n ty₂ v₂ b₂) →
    PairedLeaves (.letE n ty₁ v₁ b₁) (.letE n ty₂ v₂ b₂) →
    Q d (.letE n ty₁ v₁ b₁) (.letE n ty₂ v₂ b₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (.letE n ty₁ v₁ b₁) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (.letE n ty₂ v₂ b₂) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the proj sim root** (whnf-of-scrutinee lockstep +
`projLitToCtor` + the structural rule; its seal carries the
struct-name-slack audit flagged at the map). -/
def ZipProjCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d e₁ e₂ →
    SubjInv d (.proj sn i e₁) → SubjInv d (.proj sn i e₂) →
    PairedLeaves (.proj sn i e₁) (.proj sn i e₂) →
    Q d (.proj sn i e₁) (.proj sn i e₂) →
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
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hCert : ZipCertCase μ env φ Q) (hConst : ZipConstCase μ env φ Q)
    (hApp : ZipAppCase μ env φ Q) (hLet : ZipLetECase μ env φ Q)
    (hProj : ZipProjCase μ env φ Q) :
    ZipWhnfSortAgree μ env φ Q := by
  have main : ∀ fc g r {d ga la gb lb : Nat} {s t : Expr}
      {ℓa ℓb : Level}, ga + gb ≤ g → la + lb ≤ r →
      CertZip μ env fc d s t →
      SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
        = .ok (.sort ℓa) →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
        = .ok (.sort ℓb) →
      ℓa.eval φ = ℓb.eval φ := by
    intro fc
    induction fc using Nat.strongRecOn with
    | ind fc ihfc =>
    intro g
    induction g using Nat.strongRecOn with
    | ind g ihg =>
    intro r
    induction r with
    | zero =>
      intro d ga la gb lb s t ℓa ℓb hgle hle hz hIs hIt hp hQ ha hb
      obtain rfl : la = 0 := by omega
      exact nomatch ha
    | succ r ihr =>
      intro d ga la gb lb s t ℓa ℓb hgle hle hz hIs hIt hp hQ ha hb
      have below : ZipBelow μ env φ Q fc (ga + gb) (la + lb) := by
        intro fc' d' ga' la' gb' lb' s' t' ℓa' ℓb' hlt hz' hIs' hIt'
          hp' hQ' ha' hb'
        rcases hlt with hlt | ⟨rfl, hlt | ⟨hge, hlt⟩⟩
        · exact ihfc fc' hlt (ga' + gb') (la' + lb') (Nat.le_refl _)
            (Nat.le_refl _) hz' hIs' hIt' hp' hQ' ha' hb'
        · exact ihg (ga' + gb') (Nat.lt_of_lt_of_le hlt hgle)
            (la' + lb') (Nat.le_refl _) (Nat.le_refl _) hz' hIs'
            hIt' hp' hQ' ha' hb'
        · exact ihr (hge ▸ hgle) (by omega) hz' hIs' hIt' hp' hQ'
            ha' hb'
      cases hz with
      | refl e =>
        rw [Setlec.Expr.sort.inj (whnfLoop_det hm ha hb)]
      | cert a b hba hbb hc =>
        exact hCert
          (fun hlt hz' hIs' hIt' hp' hQ' ha' hb' =>
            below (Or.inl hlt) hz' hIs' hIt' hp' hQ' ha' hb')
          hba hbb hc hIs hIt hp hQ ha hb
      | sortSlack u v hev =>
        have h1 : Expr.sort ℓa = Expr.sort u :=
          loop_stuck_out hm ha (whnfCore_sort_run (Nat.le_refl 1))
            (fun _ => reduceNat_sort) unfoldDefinition_sort
        have h2 : Expr.sort ℓb = Expr.sort v :=
          loop_stuck_out hm hb (whnfCore_sort_run (Nat.le_refl 1))
            (fun _ => reduceNat_sort) unfoldDefinition_sort
        rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
        exact hev φ
      | constSlack n us us' hev => exact hConst below hev hQ ha hb
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
        exact hLet below hty hval hbody hIs hIt hp hQ ha hb
      | app f₁ x₁ f₂ x₂ hf hx =>
        exact hApp below hf hx hIs hIt hp hQ ha hb
      | proj sn i e₁ e₂ he =>
        exact hProj below he hIs hIt hp hQ ha hb
  intro fc d ga la gb lb s t ℓa ℓb hz hIs hIt hp hQ ha hb
  exact main fc (ga + gb) (la + lb) (Nat.le_refl _) (Nat.le_refl _)
    hz hIs hIt hp hQ ha hb

/-- **The cert case DISCHARGED** (build step 3): the extracted
cert-loop template, with the spine handler zipping the post-core
pair (`constSlack` head through `isEquivList` soundness, `.cert`
leaves through `defEqList_extract`, dual-success runs assembled from
the spine's const heads) and feeding `ZipBelow` at the strictly
smaller cert fuel. -/
theorem zipCertCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) :
    ZipCertCase μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb a b ℓa ℓb below hba hbb hc hIa hIb hp hQ ha hb
  cases fc with
  | zero => exact nomatch hc
  | succ fc =>
  rw [Setlec.isDefEqCore_succ] at hc
  have hSp : SpineHandler μ env φ Q fc := by
    intro l d' ga' la' gb' lb' f₁ f₂ a0 b0 a' b' ℓa' ℓb'
      hIa' hIb' hPab' hQab' hc0 hwa hwb hs ha' hb'
    cases la' with
    | zero => exact nomatch ha'
    | succ la'' =>
    cases lb' with
    | zero => exact nomatch hb'
    | succ lb'' =>
    have haD := ha'
    rw [whnfLoop_succ] at haD
    obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
    obtain rfl : a' = a₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwca : whnfCore μ env ga' d' a0 = .ok a₁) hwa).symm
    have hbD := hb'
    rw [whnfLoop_succ] at hbD
    obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
    obtain rfl : b' = b₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwcb : whnfCore μ env gb' d' b0 = .ok b₁) hwb).symm
    rcases htriA with ⟨x, hrx, -⟩ | ⟨hrga, xa, hux, hkx⟩ |
      ⟨-, -, hstopA⟩
    · exact (hN hwa hrx ha').elim
    · rcases htriB with ⟨y, hry, -⟩ | ⟨hrgb, xb, huy, hky⟩ |
        ⟨-, -, hstopB⟩
      · exact (hN hwb hry hb').elim
      · obtain ⟨na, usa, heqa⟩ : ∃ n us,
            a'.getAppFn = .const n us := by
          have hs' := hs
          unfold Setlec.defeqSpine at hs'
          split at hs'
          · next n us heq => exact ⟨n, us, heq⟩
          · exact nomatch hs'
        obtain ⟨nb, usb, heqb⟩ : ∃ n us,
            b'.getAppFn = .const n us := by
          have hs' := hs
          unfold Setlec.defeqSpine at hs'
          split at hs'
          · next n us heq =>
            split at hs'
            · next n' us' heq' => exact ⟨n', us', heq'⟩
            · exact nomatch hs'
          · exact nomatch hs'
        have hA : Setlec.whnfLoop (Setlec.pureFns μ env (max f₁ ga'))
            env d' (la'' + 1) a' = .ok (.sort ℓa') := by
          rw [whnfLoop_succ]
          exact whnfStep_assemble_delta
            (hm.2.2.1 (Nat.le_max_left f₁ ga')
              (whnfCore_reidem_const hm hwa heqa))
            (hm.2.2.2.2 (Nat.le_max_right f₁ ga') hrga) hux
            (whnfLoop_r_mono hm (Nat.le_max_right f₁ ga') hkx)
        have hB2 : Setlec.whnfLoop (Setlec.pureFns μ env (max f₂ gb'))
            env d' (lb'' + 1) b' = .ok (.sort ℓb') := by
          rw [whnfLoop_succ]
          exact whnfStep_assemble_delta
            (hm.2.2.1 (Nat.le_max_left f₂ gb')
              (whnfCore_reidem_const hm hwb heqb))
            (hm.2.2.2.2 (Nat.le_max_right f₂ gb') hrgb) huy
            (whnfLoop_r_mono hm (Nat.le_max_right f₂ gb') hky)
        have hIa2 := hIC hwa hIa'
        have hIb2 := hIC hwb hIb'
        unfold Setlec.defeqSpine at hs
        split at hs
        · next n us heqa2 =>
          split at hs
          · next n' us' heqb2 =>
            split at hs
            · next hcond =>
              obtain ⟨rfl, hlen⟩ := hcond
              split at hs
              · next heql =>
                obtain ⟨hlen', hcerts⟩ := defEqList_extract hs
                have hzip : CertZip μ env fc d' a' b' := by
                  rw [← Setlec.Expr.mkAppN_getApp a',
                    ← Setlec.Expr.mkAppN_getApp b', heqa2, heqb2]
                  exact certZip_mkAppN
                    (.constSlack n us us' fun φ' =>
                      evalEqList_map
                        (Setlec.Level.isEquivList_sound heql φ'))
                    hlen' (getAppArgs_bounded hIa2.2.1)
                    (getAppArgs_bounded hIb2.2.1) hcerts
                exact below (Nat.lt_succ_self fc) hzip
                  hIa2 hIb2
                  ((hLC hwb ((hLC hwa hPab').symm)).symm)
                  (hQs (hQC hwb (hQs (hQC hwa hQab')))) hA hB2
              · exact nomatch hs
            · exact nomatch hs
          · exact nomatch hs
        · exact nomatch hs
      · obtain rfl := hstopB
        unfold Setlec.defeqSpine at hs
        split at hs
        · exact nomatch hs
        · exact nomatch hs
    · obtain rfl := hstopA
      unfold Setlec.defeqSpine at hs
      exact nomatch hs
  exact certLoop_sortAgree (φ := φ) (Q := Q) hm hIC hID hIN
    hLC hLD hLN hQC hQD hQN hQs hP hR hE hN fc hSp
    Setlec.defeqLoopFuel hc hIa hIb hp hQ ha hb

/-! ### The StoredWF supply kit (instantiation preservation) -/

/-- Level instantiation creates no fvar leaves. -/
theorem instL_fvarLeaves_nil {lps : List Name} {us : List Level} :
    ∀ {e : Expr}, e.fvarLeaves = [] →
      (e.instantiateLevelParams lps us).fvarLeaves = [] := by
  intro e
  induction e with
  | bvar i =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | fvar idx n ty ih =>
    intro h
    simp [Setlec.Expr.fvarLeaves] at h
  | sort u =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | const n vs =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | app f a ihf iha =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, ihf h.1, iha h.2, List.append_nil]
  | lam n ty body m iht ihb =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, iht h.1, ihb h.2, List.append_nil]
  | forallE n ty body m iht ihb =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, iht h.1, ihb h.2, List.append_nil]
  | letE n ty val body iht ihv ihb =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, iht h1, ihv h2, ihb h3,
      List.append_nil]
  | lit l =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | proj sn i e ih =>
    intro h
    simp only [Setlec.Expr.fvarLeaves] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, ih h]

/-- Level instantiation touches no bvars. -/
theorem instL_looseBVarsBounded {lps : List Name} {us : List Level} :
    ∀ {e : Expr} {k : Nat}, e.looseBVarsBounded k = true →
      (e.instantiateLevelParams lps us).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simpa [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded] using h
  | fvar idx n ty ih =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | sort u =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | const n vs =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | app f a ihf iha =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, ihf h.1, iha h.2,
      Bool.and_self]
  | lam n ty body m iht ihb =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, iht h.1, ihb h.2,
      Bool.and_self]
  | forallE n ty body m iht ihb =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, iht h.1, ihb h.2,
      Bool.and_self]
  | letE n ty val body iht ihv ihb =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, iht h1, ihv h2, ihb h3,
      Bool.and_self]
  | lit l =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | proj sn i e ih =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, ih h]

/-- Fvar-leaf-free expressions are well-scoped at any depth. -/
theorem wScoped_of_fvarLeaves_nil :
    ∀ {e : Expr} {d : Nat}, e.fvarLeaves = [] → Expr.WScoped d e := by
  intro e
  induction e with
  | bvar i => intro d h; simp [Setlec.Expr.WScoped]
  | fvar idx n ty ih =>
    intro d h
    simp [Setlec.Expr.fvarLeaves] at h
  | sort u => intro d h; simp [Setlec.Expr.WScoped]
  | const n vs => intro d h; simp [Setlec.Expr.WScoped]
  | app f a ihf iha =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.WScoped]
    exact ⟨ihf h.1, iha h.2⟩
  | lam n ty body m iht ihb =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE n ty body m iht ihb =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | letE n ty val body iht ihv ihb =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Setlec.Expr.WScoped]
    exact ⟨iht h1, ihv h2, ihb h3⟩
  | lit l => intro d h; simp [Setlec.Expr.WScoped]
  | proj sn i e ih =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves] at h
    simp only [Setlec.Expr.WScoped]
    exact ih h

/-- The `SubjInv` package for an fvar-leaf-free, bvar-closed
expression. -/
theorem subjInv_of_nil {e : Expr} {d : Nat}
    (h1 : e.fvarLeaves = []) (h2 : e.looseBVarsBounded 0 = true) :
    SubjInv d e :=
  ⟨wScoped_of_fvarLeaves_nil h1, h2,
    fun l hl => absurd hl (by rw [h1]; exact List.not_mem_nil),
    fun l hl => absurd hl (by
      rw [List.mem_append, h1] at hl
      exact absurd (hl.elim id id) List.not_mem_nil)⟩

/-- Pairing is vacuous on fvar-leaf-free pairs. -/
theorem pairedLeaves_of_nil {a b : Expr}
    (h1 : a.fvarLeaves = []) (h2 : b.fvarLeaves = []) :
    PairedLeaves a b := by
  intro l hl
  rw [h1, h2] at hl
  exact absurd hl List.not_mem_nil

/-- Both instantiations of a same-head δ unfold together (the guard
reads only the length). -/
theorem unfoldDefinition_const_both {env : Env} {n : Name}
    {us us' : List Level} {xa : Expr}
    (hlen : us.length = us'.length)
    (hux : Setlec.unfoldDefinition env (.const n us) = some xa) :
    ∃ cv value, xa
        = Setlec.Expr.instantiateLevelParams cv.levelParams us value ∧
      Setlec.unfoldDefinition env (.const n us')
        = some (Setlec.Expr.instantiateLevelParams
            cv.levelParams us' value) ∧
      ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
        env.find? n = some (.thmInfo cv value)) := by
  unfold Setlec.unfoldDefinition at hux
  simp only [Setlec.Expr.getAppFn] at hux
  cases hf : env.find? n with
  | none => rw [hf] at hux; exact nomatch hux
  | some ci =>
    rw [hf] at hux
    cases ci with
    | defnInfo cv value hint =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inl ⟨hint, rfl⟩⟩
        · have h2 := Option.some.inj hux
          simp only [Setlec.Expr.getAppArgs,
            Setlec.Expr.mkAppN] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition, Setlec.Expr.getAppFn,
            hf]
          rw [if_pos (hlen ▸ hl)]
          simp [Setlec.Expr.getAppArgs, Setlec.Expr.mkAppN]
      · rw [if_neg hl] at hux; exact nomatch hux
    | thmInfo cv value =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inr rfl⟩
        · have h2 := Option.some.inj hux
          simp only [Setlec.Expr.getAppArgs,
            Setlec.Expr.mkAppN] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition, Setlec.Expr.getAppFn,
            hf]
          rw [if_pos (hlen ▸ hl)]
          simp [Setlec.Expr.getAppArgs, Setlec.Expr.mkAppN]
      · rw [if_neg hl] at hux; exact nomatch hux
    | axiomInfo cv => exact nomatch hux
    | indInfo cv caps => exact nomatch hux
    | ctorInfo cv a b => exact nomatch hux
    | recInfo cv a b c => exact nomatch hux
    | projInfo entry => exact nomatch hux

/-- **The constSlack case DISCHARGED** (both-δ of one stored value):
the two sides unfold together, the continuations are
`certZip_instantiate` zips with the `StoredWF` package, and the
recursion runs at the same cert fuel with a smaller loop-budget
sum. -/
theorem zipConstCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hSW : StoredWF env)
    (hQD : QPreserveDeltaF env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a) :
    ZipConstCase μ env φ Q := by
  intro fc d ga la gb lb n us us' ℓa ℓb below hev hQ ha hb
  have hlen : us.length = us'.length := by
    have := congrArg List.length (hev fun _ => 0)
    simpa using this
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
  obtain rfl : a₁ = .const n us :=
    (KnotFuelDet_of_mono hm).2.2.1
      (hwca : whnfCore μ env ga d (.const n us) = .ok a₁)
      (whnfCore_const_run (Nat.le_refl 1))
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
  obtain rfl : b₁ = .const n us' :=
    (KnotFuelDet_of_mono hm).2.2.1
      (hwcb : whnfCore μ env gb d (.const n us') = .ok b₁)
      (whnfCore_const_run (Nat.le_refl 1))
  rcases htriA with ⟨x, hrx, -⟩ | ⟨-, xa, hux, hkx⟩ | ⟨-, -, hstopA⟩
  · exact nomatch hrx
  · obtain ⟨cv, value, rfl, huy', hstore⟩ :=
      unfoldDefinition_const_both hlen hux
    obtain ⟨hnil, hbnd, -⟩ := hSW hstore
    rcases htriB with ⟨y, hry, -⟩ | ⟨-, xb, huy, hky⟩ | ⟨-, hudb, -⟩
    · exact nomatch hry
    · rw [huy'] at huy
      obtain rfl := (Option.some.inj huy).symm
      exact below (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
        (certZip_instantiate hev value)
        (subjInv_of_nil (instL_fvarLeaves_nil hnil)
          (instL_looseBVarsBounded hbnd))
        (subjInv_of_nil (instL_fvarLeaves_nil hnil)
          (instL_looseBVarsBounded hbnd))
        (pairedLeaves_of_nil (instL_fvarLeaves_nil hnil)
          (instL_fvarLeaves_nil hnil))
        (hQs (hQD huy' (hQs (hQD hux hQ)))) hkx hky
    · rw [huy'] at hudb; exact nomatch hudb
  · exact nomatch hstopA

/-- **Zip inversion at two literal sorts** (the sim tier's terminal):
only `refl`, `sortSlack` and `cert` can relate two sorts, and each
forces eval-equal levels (`cert` through the landed
`isDefEqCore_sorts_eval`). -/
theorem certZip_sorts_eval {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (hm : KnotFuelMono μ env)
    {fc d : Nat} {u v : Level}
    (hz : CertZip μ env fc d (.sort u) (.sort v)) :
    u.eval φ = v.eval φ := by
  cases hz with
  | refl _ => rfl
  | sortSlack _ _ hev => exact hev φ
  | cert _ _ _ _ hc => exact isDefEqCore_sorts_eval hm hc

/-- **The Θ seam, frozen** (the one routed hard case of the sim
tier): a cert-related head pair under pointwise-zipped spines, both
sort convergences given, the recursion available strictly below.
Subsumes β-under-cert-head, the exposed-argument mutual knot, and
the eta-rescue-on-cert-major seam (`as = []` is `ZipCertCase`'s
content, already discharged — this Prop's obligation is the
nonempty-spine tier).  Its discharge is the binder-opening
machinery: the head cert's `lamCong` decomposition relates OPENED
bodies at `d+1`, and connecting the substituted-with-args forms is
the Θ-motive apparatus the module docstring promised. -/
def ZipCertSpineCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {f₁ f₂ : Expr} {as bs : List Expr}
    {ℓa ℓb : Level},
    ZipBelowFc μ env φ Q fc →
    f₁.looseBVarsBounded 0 = true → f₂.looseBVarsBounded 0 = true →
    isDefEqCore μ env fc d f₁ f₂ = .ok true →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN f₁ as) →
    SubjInv d (Setlec.Expr.mkAppN f₂ bs) →
    PairedLeaves (Setlec.Expr.mkAppN f₁ as)
      (Setlec.Expr.mkAppN f₂ bs) →
    Q d (Setlec.Expr.mkAppN f₁ as) (Setlec.Expr.mkAppN f₂ bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN f₁ as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN f₂ bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The whnfCore-app internal decomposition** (the discharge
campaign's first brick): every success on an application splits into
the head's core run at knot `g` plus exactly one of the four
continuations — fired β (with the argument cert), stuck β (cert
false), fired iota, or stuck iota. -/
theorem whnfCore_app_decompose {μ : CheckMode} {env : Env}
    {g d : Nat} {f x s : Expr}
    (h : whnfCore μ env (g + 1) d (.app f x) = .ok s) :
    ∃ f', whnfCore μ env g d f = .ok f' ∧
      ((∃ n ty body m ta,
          f' = .lam n ty body m ∧
          inferTypeCore μ env g d x = .ok ta ∧
          isDefEqCore μ env g d ta ty = .ok true ∧
          whnfCore μ env g d (body.instantiate1 x) = .ok s) ∨
       (∃ n ty body m ta,
          f' = .lam n ty body m ∧
          inferTypeCore μ env g d x = .ok ta ∧
          isDefEqCore μ env g d ta ty = .ok false ∧
          s = .app f' x) ∨
       ((∀ n ty body mb, f' ≠ .lam n ty body mb) ∧
        ((∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
            (.app f' x) = .ok (some e'') ∧
          whnfCore μ env g d e'' = .ok s) ∨
         (Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
            (.app f' x) = .ok none ∧ s = .app f' x)))) := by
  rw [Setlec.whnfCore_succ] at h
  unfold Setlec.whnfCoreBody at h
  simp only [Bind.bind, Except.bind] at h
  cases hwf : (Setlec.pureFns μ env g).whnfCore d f with
  | error err => rw [hwf] at h; exact nomatch h
  | ok f' =>
  rw [hwf] at h
  simp only [] at h
  refine ⟨f', hwf, ?_⟩
  split at h
  · next n ty body mb =>
    cases hinf : (Setlec.pureFns μ env g).infer d x with
    | error err => rw [hinf] at h; exact nomatch h
    | ok ta =>
    rw [hinf] at h
    simp only [] at h
    cases hdq : (Setlec.pureFns μ env g).defeq d ta ty with
    | error err => rw [hdq] at h; exact nomatch h
    | ok c =>
    rw [hdq] at h
    simp only [] at h
    cases c with
    | true =>
      rw [if_pos rfl] at h
      exact .inl ⟨n, ty, body, mb, ta, rfl, hinf, hdq, h⟩
    | false =>
      rw [if_neg Bool.false_ne_true] at h
      exact .inr (.inl ⟨n, ty, body, mb, ta, rfl, hinf, hdq,
        (Except.ok.inj h).symm⟩)
  · next hne =>
    cases hio : Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
        (.app f' x) with
    | error err => rw [hio] at h; exact nomatch h
    | ok o =>
    rw [hio] at h
    simp only [] at h
    cases o with
    | some e'' =>
      exact .inr (.inr ⟨fun n ty body mb heq => hne n ty body mb heq,
        .inl ⟨e'', rfl, h⟩⟩)
    | none =>
      exact .inr (.inr ⟨fun n ty body mb heq => hne n ty body mb heq,
        .inr ⟨rfl, (Except.ok.inj h).symm⟩⟩)

/-- **The app-layer assemble** (the decompose's inverse): a head run
plus a leg package build the layer's core run at joined fuel.  The
connecting runs of re-based seams are assembled with this — the
seam's own head run replaces the original's, the original legs are
reused verbatim. -/
theorem whnfCore_app_assemble {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g gl d : Nat} {P y h' s : Expr}
    (hh : whnfCore μ env g d P = .ok h')
    (hlegs :
      (∃ n ty body mb ta,
          h' = .lam n ty body mb ∧
          inferTypeCore μ env gl d y = .ok ta ∧
          isDefEqCore μ env gl d ta ty = .ok true ∧
          whnfCore μ env gl d (body.instantiate1 y) = .ok s) ∨
      (∃ n ty body mb ta,
          h' = .lam n ty body mb ∧
          inferTypeCore μ env gl d y = .ok ta ∧
          isDefEqCore μ env gl d ta ty = .ok false ∧
          s = .app h' y) ∨
      ((∀ n ty body mb, h' ≠ .lam n ty body mb) ∧
       ((∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env gl) env d
            (.app h' y) = .ok (some e'') ∧
          whnfCore μ env gl d e'' = .ok s) ∨
        (Setlec.iotaRec μ (Setlec.pureFns μ env gl) env d
            (.app h' y) = .ok none ∧ s = .app h' y)))) :
    whnfCore μ env (max g gl + 1) d (.app P y) = .ok s := by
  have hh' : (Setlec.pureFns μ env (max g gl)).whnfCore d P
      = .ok h' :=
    hm.2.2.1 (Nat.le_max_left g gl) hh
  rw [show whnfCore μ env (max g gl + 1) d (.app P y)
      = Setlec.whnfCoreBody μ (Setlec.pureFns μ env (max g gl)) env d
        (.app P y) from Setlec.whnfCore_succ ..]
  unfold Setlec.whnfCoreBody
  simp only [Bind.bind, Except.bind]
  rw [hh']
  simp only []
  rcases hlegs with ⟨n, ty, body, mb, ta, rfl, hinf, hdq, hrun⟩ |
    ⟨n, ty, body, mb, ta, rfl, hinf, hdq, rfl⟩ | ⟨hnl, hio⟩
  · simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).infer d y = .ok ta
      from hm.1 (Nat.le_max_right g gl) hinf]
    simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).defeq d ta ty
        = .ok true
      from hm.2.2.2.1 (Nat.le_max_right g gl) hdq]
    simp only []
    rw [if_pos trivial]
    exact hm.2.2.1 (Nat.le_max_right g gl) hrun
  · simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).infer d y = .ok ta
      from hm.1 (Nat.le_max_right g gl) hinf]
    simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).defeq d ta ty
        = .ok false
      from hm.2.2.2.1 (Nat.le_max_right g gl) hdq]
    simp only []
    rw [if_neg Bool.false_ne_true]
    rfl
  · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
    · have hioG := iotaRec_mono
        (coreSub_le μ env (Nat.le_max_right g gl)) hio
      have hrunG : (Setlec.pureFns μ env (max g gl)).whnfCore d e''
          = .ok s :=
        hm.2.2.1 (Nat.le_max_right g gl) hrun
      cases h' with
      | lam n2 ty2 b2 m2 => exact absurd rfl (hnl n2 ty2 b2 m2)
      | bvar i =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | fvar i n2 ty2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | sort u0 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | const n2 us2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | app p q =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | forallE n2 ty2 b2 m2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | letE n2 ty2 v2 b2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | lit l =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | proj sn i e0 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
    · have hioG := iotaRec_mono
        (coreSub_le μ env (Nat.le_max_right g gl)) hio
      cases h' with
      | lam n2 ty2 b2 m2 => exact absurd rfl (hnl n2 ty2 b2 m2)
      | bvar i =>
        simp only []; rw [hioG]; rfl
      | fvar i n2 ty2 =>
        simp only []; rw [hioG]; rfl
      | sort u0 =>
        simp only []; rw [hioG]; rfl
      | const n2 us2 =>
        simp only []; rw [hioG]; rfl
      | app p q =>
        simp only []; rw [hioG]; rfl
      | forallE n2 ty2 b2 m2 =>
        simp only []; rw [hioG]; rfl
      | letE n2 ty2 v2 b2 =>
        simp only []; rw [hioG]; rfl
      | lit l =>
        simp only []; rw [hioG]; rfl
      | proj sn i e0 =>
        simp only []; rw [hioG]; rfl

/-- Zeta is one knot level down (the letE analog of the app
decomposition). -/
theorem whnfCore_letE_step {μ : CheckMode} {env : Env}
    {g d : Nat} {n : Name} {ty v b s : Expr} :
    whnfCore μ env (g + 1) d (.letE n ty v b) = .ok s ↔
    whnfCore μ env g d (b.instantiate1 v) = .ok s := by
  rw [Setlec.whnfCore_succ]
  exact Iff.rfl

/-- `getAppFn` outputs are never applications. -/
theorem getAppFn_not_app : ∀ {e p q : Expr},
    e.getAppFn ≠ .app p q := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro p q h
    rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl] at h
    exact ihf h
  | bvar i => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | fvar idx n ty ih => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | sort u => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | const n us => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | lam n ty body m iht ihb =>
    intro p q h; simp [Setlec.Expr.getAppFn] at h
  | forallE n ty body m iht ihb =>
    intro p q h; simp [Setlec.Expr.getAppFn] at h
  | letE n ty val body iht ihv ihb =>
    intro p q h; simp [Setlec.Expr.getAppFn] at h
  | lit l => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | proj sn i e ih => intro p q h; simp [Setlec.Expr.getAppFn] at h

/-- One-step spine extension of the fold. -/
theorem mkAppN_append_one {f a : Expr} : ∀ {as : List Expr},
    Setlec.Expr.mkAppN f (as ++ [a])
      = .app (Setlec.Expr.mkAppN f as) a := by
  intro as
  induction as generalizing f with
  | nil => rfl
  | cons b bs ih =>
    show Setlec.Expr.mkAppN (.app f b) (bs ++ [a]) = _
    rw [ih]
    rfl

/-- Left-part indexing of an appended singleton (self-contained; the
core lemma names shift across toolchains). -/
theorem getElem_append_left' {α : Type _} :
    ∀ (l₁ l₂ : List α) (i : Nat) (h : i < l₁.length)
      {h' : i < (l₁ ++ l₂).length},
      (l₁ ++ l₂)[i]'h' = l₁[i]'h
  | _ :: _, _, 0, _, _ => rfl
  | _ :: xs, l₂, i + 1, h, _ =>
    getElem_append_left' xs l₂ i (Nat.lt_of_succ_lt_succ h)
  | [], _, i, h, _ => absurd h (Nat.not_lt_zero i)

/-- The appended element sits at the old length. -/
theorem getElem_append_last {α : Type _} :
    ∀ (l : List α) (a : α) {h : l.length < (l ++ [a]).length},
      (l ++ [a])[l.length]'h = a
  | [], _, _ => rfl
  | _ :: xs, a, _ => getElem_append_last xs a

/-- **The spine view**: every zip flattens to a head zip over
pointwise-zipped argument lists, where the head is either a
certified pair (possibly app-shaped — the Θ seam's territory) or a
non-application zip node (the case analysis' terminating heads). -/
theorem certZip_app_view {μ : CheckMode} {env : Env} {fc d : Nat} :
    ∀ {u v : Expr}, CertZip μ env fc d u v →
    ∃ (F₁ F₂ : Expr) (as bs : List Expr),
      u = Setlec.Expr.mkAppN F₁ as ∧ v = Setlec.Expr.mkAppN F₂ bs ∧
      as.length = bs.length ∧
      (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) ∧
      ((F₁.looseBVarsBounded 0 = true ∧ F₂.looseBVarsBounded 0 = true ∧
        isDefEqCore μ env fc d F₁ F₂ = .ok true) ∨
       ((∀ p q, F₁ ≠ .app p q) ∧ (∀ p q, F₂ ≠ .app p q) ∧
        CertZip μ env fc d F₁ F₂)) := by
  intro u v hz
  induction hz with
  | app h₁ y₁ h₂ y₂ hh hy ihh ihy =>
    obtain ⟨F₁, F₂, as, bs, rfl, rfl, hlen, hargs, hhead⟩ := ihh
    refine ⟨F₁, F₂, as ++ [y₁], bs ++ [y₂], ?_, ?_, ?_, ?_, hhead⟩
    · rw [mkAppN_append_one]
    · rw [mkAppN_append_one]
    · simp [hlen]
    · intro i hi₁ hi₂
      by_cases hlt : i < as.length
      · have hlt₂ : i < bs.length := hlen ▸ hlt
        rw [getElem_append_left' as [y₁] i hlt,
          getElem_append_left' bs [y₂] i hlt₂]
        exact hargs i hlt hlt₂
      · have hi : i = as.length := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hi₁
          omega
        subst hi
        rw [getElem_append_last as y₁]
        simp only [hlen]
        rw [getElem_append_last bs y₂]
        exact hy
  | cert a b hba hbb hc =>
    exact ⟨a, b, [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inl ⟨hba, hbb, hc⟩⟩
  | refl e =>
    exact ⟨e.getAppFn, e.getAppFn, e.getAppArgs, e.getAppArgs,
      (Setlec.Expr.mkAppN_getApp e).symm,
      (Setlec.Expr.mkAppN_getApp e).symm, rfl,
      (fun i h₁ h₂ => CertZip.refl _),
      Or.inr ⟨(fun p q => getAppFn_not_app),
        (fun p q => getAppFn_not_app), CertZip.refl _⟩⟩
  | sortSlack w x hev =>
    exact ⟨.sort w, .sort x, [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.sortSlack _ _ hev⟩⟩
  | constSlack n us us' hev =>
    exact ⟨.const n us, .const n us', [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.constSlack _ _ _ hev⟩⟩
  | fvar i n ty₁ ty₂ hty ihty =>
    exact ⟨.fvar i n ty₁, .fvar i n ty₂, [], [], rfl, rfl, rfl,
      (fun j h₁ _ => absurd h₁ (Nat.not_lt_zero j)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.fvar _ _ _ _ hty⟩⟩
  | lam n ty₁ ty₂ b₁ b₂ m hty hbody ihty ihbody =>
    exact ⟨.lam n ty₁ b₁ m, .lam n ty₂ b₂ m, [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.lam _ _ _ _ _ _ hty hbody⟩⟩
  | forallE n ty₁ ty₂ b₁ b₂ m hty hbody ihty ihbody =>
    exact ⟨.forallE n ty₁ b₁ m, .forallE n ty₂ b₂ m, [], [], rfl,
      rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.forallE _ _ _ _ _ _ hty hbody⟩⟩
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody ihty ihval ihbody =>
    exact ⟨.letE n ty₁ v₁ b₁, .letE n ty₂ v₂ b₂, [], [], rfl, rfl,
      rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.letE _ _ _ _ _ _ _ hty hval hbody⟩⟩
  | proj sn i e₁ e₂ he ihe =>
    exact ⟨.proj sn i e₁, .proj sn i e₂, [], [], rfl, rfl, rfl,
      (fun j h₁ _ => absurd h₁ (Nat.not_lt_zero j)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.proj _ _ _ _ he⟩⟩

/-- **The flat-spine leg** (the campaign's one remaining sim
routing): a NON-application head zip over pointwise-zipped spines,
both sort convergences given.  Every non-cert-headed shape funnels
here through the view — including empty-spine letE/proj/congruence
pairs — and its discharge is the F-driven analysis (refl heads
det-synchronized, lam-congruence β through `certZip_subst`,
constSlack through the iota/δ lockstep, shape-stuck vacuities). -/
def ZipSpineFlatCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {F₁ F₂ : Expr} {as bs : List Expr}
    {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ p q, F₁ ≠ .app p q) → (∀ p q, F₂ ≠ .app p q) →
    CertZip μ env fc d F₁ F₂ →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN F₁ as) →
    SubjInv d (Setlec.Expr.mkAppN F₂ bs) →
    PairedLeaves (Setlec.Expr.mkAppN F₁ as)
      (Setlec.Expr.mkAppN F₂ bs) →
    Q d (Setlec.Expr.mkAppN F₁ as) (Setlec.Expr.mkAppN F₂ bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN F₁ as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN F₂ bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The app wrapper DISCHARGED**: view, then dispatch — cert heads
to the Θ seam, everything else to the flat-spine leg. -/
theorem zipAppCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipAppCase μ env φ Q := by
  intro fc d ga la gb lb f₁ x₁ f₂ x₂ ℓa ℓb below hf hx hIs hIt hp
    hQ ha hb
  obtain ⟨F₁, F₂, as, bs, hu, hv, hlen, hargs, hhead⟩ :=
    certZip_app_view (CertZip.app f₁ x₁ f₂ x₂ hf hx)
  rw [hu] at hIs ha
  rw [hv] at hIt hb
  rw [hu, hv] at hp hQ
  rcases hhead with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hFz⟩
  · exact hΘ
      (fun hlt hz' hIs' hIt' hp' hQ' ha' hb' =>
        below (Or.inl hlt) hz' hIs' hIt' hp' hQ' ha' hb')
      hba hbb hc hlen hargs hIs hIt hp hQ ha hb
  · exact hSpine below hne₁ hne₂ hFz hlen hargs hIs hIt hp hQ ha hb

/-- **The letE wrapper DISCHARGED**: a letE pair is a non-app head
with an empty spine — straight to the flat-spine leg. -/
theorem zipLetECase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipLetECase μ env φ Q := by
  intro fc d ga la gb lb n ty₁ ty₂ v₁ v₂ b₁ b₂ ℓa ℓb below hty hval
    hbody hIs hIt hp hQ ha hb
  exact hSpine (F₁ := .letE n ty₁ v₁ b₁) (F₂ := .letE n ty₂ v₂ b₂)
    (as := []) (bs := []) below
    (fun p q h => nomatch h) (fun p q h => nomatch h)
    (CertZip.letE _ _ _ _ _ _ _ hty hval hbody) rfl
    (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i))
    hIs hIt hp hQ ha hb

/-- **The proj wrapper DISCHARGED**: likewise a bare non-app head. -/
theorem zipProjCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipProjCase μ env φ Q := by
  intro fc d ga la gb lb i sn e₁ e₂ ℓa ℓb below he hIs hIt hp hQ
    ha hb
  exact hSpine (F₁ := .proj sn i e₁) (F₂ := .proj sn i e₂)
    (as := []) (bs := []) below
    (fun p q h => nomatch h) (fun p q h => nomatch h)
    (CertZip.proj _ _ _ _ he) rfl
    (fun j h₁ _ => absurd h₁ (Nat.not_lt_zero j))
    hIs hIt hp hQ ha hb

/-- **The summit at its two sim obligations**: `ZipWhnfSortAgree`
from the Θ seam and the flat-spine leg (plus the trio's Q-frame
vacuities and the env facts).  Every structural case is
discharged. -/
theorem zipWhnfSortAgree_of_two {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hSW : StoredWF env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipWhnfSortAgree μ env φ Q :=
  zipWhnfSortAgree_of (φ := φ) (Q := Q) hm
    (zipCertCase_of (φ := φ) (Q := Q) hm hB hIC hID hIN hLC hLD hLN
      hQC hQD hQN hQs hP hR hE)
    (zipConstCase_of (φ := φ) (Q := Q) hm hSW hQD hQs)
    (zipAppCase_of (φ := φ) (Q := Q) hΘ hSpine)
    (zipLetECase_of (φ := φ) (Q := Q) hSpine)
    (zipProjCase_of (φ := φ) (Q := Q) hSpine)

/-! ### The flat-spine bases kit -/

/-- Pure congruence fold: a zipped head under pointwise-zipped
arguments stays zipped (no cert leaves manufactured). -/
theorem certZip_mkAppN_zips {μ : CheckMode} {env : Env} {fc d : Nat} :
    ∀ {as bs : List Expr} {F₁ F₂ : Expr},
      CertZip μ env fc d F₁ F₂ →
      as.length = bs.length →
      (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) →
      CertZip μ env fc d (Setlec.Expr.mkAppN F₁ as)
        (Setlec.Expr.mkAppN F₂ bs) := by
  intro as
  induction as with
  | nil =>
    intro bs F₁ F₂ hz hlen hargs
    cases bs with
    | nil => exact hz
    | cons b bs => exact nomatch hlen
  | cons a as ih =>
    intro bs F₁ F₂ hz hlen hargs
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      simp only [Setlec.Expr.mkAppN]
      exact ih
        (.app _ _ _ _ hz
          (hargs 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)))
        (by simpa using hlen)
        (fun i h₁ h₂ =>
          hargs (i + 1)
            (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega))

/-- A non-const-headed subject never iota-fires. -/
theorem iotaRec_none_of_fn_not_const {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) :
    Setlec.iotaRec μ r env d e = .ok none := by
  unfold Setlec.iotaRec
  split
  · next n us heq => exact absurd heq (h n us)
  · rfl

/-- A non-const-headed subject never δ-unfolds. -/
theorem unfoldDefinition_none_of_fn_not_const {env : Env} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) :
    Setlec.unfoldDefinition env e = none := by
  unfold Setlec.unfoldDefinition
  split
  · next n us heq => exact absurd heq (h n us)
  · rfl

/-- A non-const-headed subject never nat-steps. -/
theorem reduceNat_none_of_fn_not_const {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) :
    Setlec.reduceNat r env d e = .ok none := by
  unfold Setlec.reduceNat
  split
  · next c a =>
    exact absurd (show (Expr.app (.const c []) a).getAppFn
        = .const c [] from rfl) (h c [])
  · next c a b =>
    exact absurd (show (Expr.app (.app (.const c []) a) b).getAppFn
        = .const c [] from rfl) (h c [])
  · rfl

/-- **Spine inertness**: a stuck, non-λ, non-const-headed head keeps
its whole spine stuck (fuel grows one per spine layer). -/
theorem whnfCore_mkAppN_inert {μ : CheckMode} {env : Env} {d : Nat} :
    ∀ (as : List Expr) {F : Expr} {hd : Nat},
      (∀ g, hd ≤ g → whnfCore μ env g d F = .ok F) →
      (∀ n ty body m, F ≠ .lam n ty body m) →
      (∀ n us, F.getAppFn ≠ .const n us) →
      ∀ {g : Nat}, hd + as.length ≤ g →
        whnfCore μ env g d (Setlec.Expr.mkAppN F as)
          = .ok (Setlec.Expr.mkAppN F as) := by
  intro as
  induction as with
  | nil =>
    intro F hd hF _ _ g hg
    exact hF g (by simpa using hg)
  | cons a as ih =>
    intro F hd hF hnl hnc g hg
    show whnfCore μ env g d (Setlec.Expr.mkAppN (.app F a) as) = _
    refine ih (F := .app F a) (hd := hd + 1) ?_ ?_ ?_ ?_
    · intro g' hg'
      cases g' with
      | zero => exact absurd hg' (by omega)
      | succ g'' =>
        rw [show whnfCore μ env (g'' + 1) d (.app F a)
            = Setlec.whnfCoreBody μ (Setlec.pureFns μ env g'') env d
              (.app F a) from Setlec.whnfCore_succ ..]
        have hiota : Setlec.iotaRec μ (Setlec.pureFns μ env g'') env d
            (.app F a) = .ok none :=
          iotaRec_none_of_fn_not_const
            (by intro n us hh
                exact hnc n us
                  ((show (Expr.app F a).getAppFn = F.getAppFn
                    from rfl) ▸ hh))
        have hFrun : (Setlec.pureFns μ env g'').whnfCore d F
            = .ok F := hF g'' (by omega)
        cases F with
        | lam n ty body m => exact absurd rfl (hnl n ty body m)
        | const n us =>
          exact absurd (show (Expr.const n us).getAppFn
            = .const n us from rfl) (hnc n us)
        | bvar i =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | fvar i n ty =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | sort u =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | forallE n ty body m =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | letE n ty v b =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | lit l =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | proj sn i e =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | app p q =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
    · intro n ty body m hh; exact nomatch hh
    · intro n us hh
      exact hnc n us
        ((show (Expr.app F a).getAppFn = F.getAppFn from rfl) ▸ hh)
    · simp only [List.length_cons] at hg ⊢
      omega

/-- Nonempty spines are application-shaped. -/
theorem mkAppN_cons_app {F a : Expr} : ∀ {as : List Expr},
    ∃ p q, Setlec.Expr.mkAppN F (a :: as) = .app p q := by
  intro as
  induction as generalizing F a with
  | nil => exact ⟨F, a, rfl⟩
  | cons b bs ih => exact ih (F := .app F a) (a := b)

/-- The spine head inherits the bvar bound. -/
theorem mkAppN_bounded_head {k : Nat} : ∀ {as : List Expr} {F : Expr},
    (Setlec.Expr.mkAppN F as).looseBVarsBounded k = true →
    F.looseBVarsBounded k = true := by
  intro as
  induction as with
  | nil => intro F h; exact h
  | cons a as ih =>
    intro F h
    have := ih (F := .app F a) h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at this
    exact this.1

/-- **The inert-spine loop terminal**: an inert head pins the loop
output to the spine itself. -/
theorem spine_inert_out {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {d ga la : Nat} {F : Expr}
    {as : List Expr} {ℓ : Level}
    (hF : ∀ g, 1 ≤ g → whnfCore μ env g d F = .ok F)
    (hnl : ∀ n ty body m, F ≠ .lam n ty body m)
    (hnc : ∀ n us, F.getAppFn ≠ .const n us)
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN F as) = .ok (.sort ℓ)) :
    Expr.sort ℓ = Setlec.Expr.mkAppN F as := by
  have hncS : ∀ n us,
      (Setlec.Expr.mkAppN F as).getAppFn ≠ .const n us := by
    intro n us h
    exact hnc n us (Setlec.Expr.getAppFn_mkAppN as F ▸ h)
  exact loop_stuck_out hm hloop
    (whnfCore_mkAppN_inert as (hd := 1) hF hnl hnc (Nat.le_refl _))
    (fun _ => reduceNat_none_of_fn_not_const hncS)
    (unfoldDefinition_none_of_fn_not_const hncS)

/-! ### The routed head cases of the flat-spine leg -/

/-- Const-headed spines at eval-linked levels (δ, iota — the iota
lockstep's home — and the nat-op vacuities). -/
def ZipConstHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {us us' : List Level}
    {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) as) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Q d (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.const n us) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- λ-headed spines (the β-chain: reassociation + spine-length
induction). -/
def ZipLamHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {ty₁ ty₂ b₁ b₂ : Expr}
    {m : Setlec.BinderMeta} {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d b₁ b₂ →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m) as) →
    SubjInv d (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m) as)
      (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m) bs) →
    Q d (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m) as)
      (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- letE-headed spines (zeta under application, knot-paid). -/
def ZipLetEHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name}
    {ty₁ ty₂ v₁ v₂ b₁ b₂ : Expr} {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
    CertZip μ env fc d b₁ b₂ →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as)
      (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) →
    Q d (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as)
      (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- proj-headed spines (the proj clause's walk; the struct-name
slack audit lives at its seal). -/
def ZipProjHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d e₁ e₂ →
    as.length = bs.length →
    (∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
      CertZip μ env fc d as[j] bs[j]) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Q d (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The flat-spine leg DISCHARGED to its four head cases**: the
stuck-shape and terminal legs inline (the bases kit), cert heads to
Θ, const/λ/letE/proj heads routed. -/
theorem zipSpineFlatCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hLam : ZipLamHeadCase μ env φ Q)
    (hLetE : ZipLetEHeadCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipSpineFlatCase μ env φ Q := by
  intro fc d ga la gb lb F₁ F₂ as bs ℓa ℓb below hne₁ hne₂ hFz hlen
    hargs hIs hIt hp hQ ha hb
  cases hFz with
  | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
  | cert a b hba hbb hc =>
    exact hΘ
      (fun hlt hz' hIs' hIt' hp' hQ' ha' hb' =>
        below (Or.inl hlt) hz' hIs' hIt' hp' hQ' ha' hb')
      hba hbb hc hlen hargs hIs hIt hp hQ ha hb
  | constSlack n us us' hev =>
    exact hConst below hev hlen hargs hIs hIt hp hQ ha hb
  | lam n ty₁ ty₂ b₁ b₂ m hty hbody =>
    exact hLam below hty hbody hlen hargs hIs hIt hp hQ ha hb
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody =>
    exact hLetE below hty hval hbody hlen hargs hIs hIt hp hQ ha hb
  | proj sn i e₁ e₂ he =>
    exact hProj below he hlen hargs hIs hIt hp hQ ha hb
  | sortSlack u v hev =>
    have h1 := spine_inert_out hm (F := .sort u) (as := as)
      (fun g hg => whnfCore_sort_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.sort u).getAppFn = Expr.sort u from rfl) ▸ h)) ha
    have h2 := spine_inert_out hm (F := .sort v) (as := bs)
      (fun g hg => whnfCore_sort_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.sort v).getAppFn = Expr.sort v from rfl) ▸ h)) hb
    cases as with
    | nil =>
      cases bs with
      | cons b bs => exact nomatch hlen
      | nil =>
        rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
        exact hev φ
    | cons a as' =>
      obtain ⟨p, q, hpq⟩ :=
        mkAppN_cons_app (F := Expr.sort u) (a := a) (as := as')
      rw [hpq] at h1
      exact nomatch h1
  | fvar i n ty₁ ty₂ hty =>
    have h1 := spine_inert_out hm (F := .fvar i n ty₁) (as := as)
      (fun g hg => whnfCore_fvar_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.fvar i n ty₁).getAppFn = Expr.fvar i n ty₁
          from rfl) ▸ h)) ha
    cases as with
    | nil => exact nomatch h1
    | cons a as' =>
      obtain ⟨p, q, hpq⟩ :=
        mkAppN_cons_app (F := Expr.fvar i n ty₁) (a := a) (as := as')
      rw [hpq] at h1
      exact nomatch h1
  | forallE n ty₁ ty₂ b₁ b₂ m hty hbody =>
    have h1 := spine_inert_out hm (F := .forallE n ty₁ b₁ m)
      (as := as)
      (fun g hg => whnfCore_forallE_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.forallE n ty₁ b₁ m).getAppFn
          = Expr.forallE n ty₁ b₁ m from rfl) ▸ h)) ha
    cases as with
    | nil => exact nomatch h1
    | cons a as' =>
      obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
        (F := Expr.forallE n ty₁ b₁ m) (a := a) (as := as')
      rw [hpq] at h1
      exact nomatch h1
  | refl _ =>
    cases F₁ with
    | app p q => exact absurd rfl (hne₁ p q)
    | bvar i =>
      have hbd := mkAppN_bounded_head (k := 0) hIs.2.1
      simp [Setlec.Expr.looseBVarsBounded] at hbd
    | const n us =>
      exact hConst below (fun _ => rfl) hlen hargs hIs hIt hp hQ
        ha hb
    | lam n ty b m =>
      exact hLam below (CertZip.refl ty) (CertZip.refl b) hlen hargs
        hIs hIt hp hQ ha hb
    | letE n ty v b =>
      exact hLetE below (CertZip.refl ty) (CertZip.refl v)
        (CertZip.refl b) hlen hargs hIs hIt hp hQ ha hb
    | proj sn i e =>
      exact hProj below (CertZip.refl e) hlen hargs hIs hIt hp hQ
        ha hb
    | sort u =>
      have h1 := spine_inert_out hm (F := .sort u) (as := as)
        (fun g hg => whnfCore_sort_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.sort u).getAppFn = Expr.sort u from rfl) ▸ h)) ha
      have h2 := spine_inert_out hm (F := .sort u) (as := bs)
        (fun g hg => whnfCore_sort_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.sort u).getAppFn = Expr.sort u from rfl) ▸ h)) hb
      cases as with
      | nil =>
        cases bs with
        | cons b bs => exact nomatch hlen
        | nil =>
          rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ :=
          mkAppN_cons_app (F := Expr.sort u) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1
    | fvar i n ty =>
      have h1 := spine_inert_out hm (F := .fvar i n ty) (as := as)
        (fun g hg => whnfCore_fvar_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.fvar i n ty).getAppFn = Expr.fvar i n ty
            from rfl) ▸ h)) ha
      cases as with
      | nil => exact nomatch h1
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ :=
          mkAppN_cons_app (F := Expr.fvar i n ty) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1
    | lit l =>
      have h1 := spine_inert_out hm (F := .lit l) (as := as)
        (fun g hg => whnfCore_lit_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.lit l).getAppFn = Expr.lit l from rfl) ▸ h)) ha
      cases as with
      | nil => exact nomatch h1
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ :=
          mkAppN_cons_app (F := Expr.lit l) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1
    | forallE n ty b m =>
      have h1 := spine_inert_out hm (F := .forallE n ty b m)
        (as := as)
        (fun g hg => whnfCore_forallE_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.forallE n ty b m).getAppFn
            = Expr.forallE n ty b m from rfl) ▸ h)) ha
      cases as with
      | nil => exact nomatch h1
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
          (F := Expr.forallE n ty b m) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1

/-- **The summit at its head cases**: `ZipWhnfSortAgree` from the Θ
seam and the four head cases (const/λ/letE/proj), plus the trio's
Q-frame vacuities and the env facts.  The flat-spine leg is
dissolved. -/
theorem zipWhnfSortAgree_of_heads {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hSW : StoredWF env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hLam : ZipLamHeadCase μ env φ Q)
    (hLetE : ZipLetEHeadCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipWhnfSortAgree μ env φ Q :=
  zipWhnfSortAgree_of_two (φ := φ) (Q := Q) hm hB hSW hIC hID hIN
    hLC hLD hLN hQC hQD hQN hQs hP hR hE hΘ
    (zipSpineFlatCase_of (φ := φ) (Q := Q) hm hΘ hConst hLam hLetE
      hProj)

/-! ### The const head: δ and nat-op legs (iota routed) -/

/-- A non-recursor const head never iota-fires. -/
theorem iotaRec_none_of_not_rec {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e : Expr}
    {n : Name} {us : List Level}
    (hfn : e.getAppFn = .const n us)
    (hnr : ∀ cv mI rP rules,
      env.find? n ≠ some (.recInfo cv mI rP rules)) :
    Setlec.iotaRec μ r env d e = .ok none := by
  unfold Setlec.iotaRec
  split
  · next n' us' heq =>
    rw [hfn] at heq
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      cases heq; exact ⟨rfl, rfl⟩
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      cases ci with
      | recInfo cv mI rP rules => exact absurd hf (hnr cv mI rP rules)
      | axiomInfo cv => rfl
      | defnInfo cv value hint => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv a b => rfl
      | projInfo entry => rfl
  · rfl

/-- A non-recursor const head keeps its whole spine
whnfCore-stuck. -/
theorem whnfCore_mkAppN_const_inert {μ : CheckMode} {env : Env}
    {d : Nat} {n : Name} {us : List Level}
    (hnr : ∀ cv mI rP rules,
      env.find? n ≠ some (.recInfo cv mI rP rules)) :
    ∀ (as : List Expr) {g : Nat}, 1 + as.length ≤ g →
      whnfCore μ env g d (Setlec.Expr.mkAppN (.const n us) as)
        = .ok (Setlec.Expr.mkAppN (.const n us) as) := by
  have main : ∀ (as : List Expr) {F : Expr} {hd : Nat},
      F.getAppFn = .const n us →
      (∀ g, hd ≤ g → whnfCore μ env g d F = .ok F) →
      (∀ n' ty body m, F ≠ .lam n' ty body m) →
      ∀ {g : Nat}, hd + as.length ≤ g →
        whnfCore μ env g d (Setlec.Expr.mkAppN F as)
          = .ok (Setlec.Expr.mkAppN F as) := by
    intro as
    induction as with
    | nil =>
      intro F hd hfn hF _ g hg
      exact hF g (by simpa using hg)
    | cons a as ih =>
      intro F hd hfn hF hnl g hg
      show whnfCore μ env g d
        (Setlec.Expr.mkAppN (.app F a) as) = _
      refine ih (F := .app F a) (hd := hd + 1)
        ((show (Expr.app F a).getAppFn = F.getAppFn from rfl).trans
          hfn) ?_ ?_ ?_
      · intro g' hg'
        cases g' with
        | zero => exact absurd hg' (by omega)
        | succ g'' =>
          rw [show whnfCore μ env (g'' + 1) d (.app F a)
              = Setlec.whnfCoreBody μ (Setlec.pureFns μ env g'')
                env d (.app F a) from Setlec.whnfCore_succ ..]
          have hiota : Setlec.iotaRec μ (Setlec.pureFns μ env g'')
              env d (.app F a) = .ok none :=
            iotaRec_none_of_not_rec
              ((show (Expr.app F a).getAppFn = F.getAppFn
                from rfl).trans hfn) hnr
          have hFrun : (Setlec.pureFns μ env g'').whnfCore d F
              = .ok F := hF g'' (by omega)
          cases F with
          | lam n' ty body m => exact absurd rfl (hnl n' ty body m)
          | const n' us' =>
            unfold Setlec.whnfCoreBody
            simp only [Bind.bind, Except.bind]
            rw [hFrun]
            simp only []
            rw [hiota]
            rfl
          | app p q =>
            unfold Setlec.whnfCoreBody
            simp only [Bind.bind, Except.bind]
            rw [hFrun]
            simp only []
            rw [hiota]
            rfl
          | bvar i => exact nomatch hfn
          | fvar i n' ty => exact nomatch hfn
          | sort u => exact nomatch hfn
          | forallE n' ty body m => exact nomatch hfn
          | letE n' ty v b => exact nomatch hfn
          | lit l => exact nomatch hfn
          | proj sn i e => exact nomatch hfn
      · intro n' ty body m h; exact nomatch h
      · simp only [List.length_cons] at hg ⊢
        omega
  intro as g hg
  exact main as
    (show (Expr.const n us).getAppFn = Expr.const n us from rfl)
    (fun g' hg' => whnfCore_const_run hg')
    (fun _ _ _ _ h => nomatch h) hg

/-- Both instantiated spines of a same-head δ unfold together. -/
theorem unfoldDefinition_spine_both {env : Env} {n : Name}
    {us us' : List Level} {as bs : List Expr} {xa : Expr}
    (hlen : us.length = us'.length)
    (hux : Setlec.unfoldDefinition env
      (Setlec.Expr.mkAppN (.const n us) as) = some xa) :
    ∃ cv value,
      xa = Setlec.Expr.mkAppN
        (Setlec.Expr.instantiateLevelParams cv.levelParams us value)
        as ∧
      Setlec.unfoldDefinition env
        (Setlec.Expr.mkAppN (.const n us') bs)
        = some (Setlec.Expr.mkAppN
          (Setlec.Expr.instantiateLevelParams cv.levelParams us'
            value) bs) ∧
      ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
        env.find? n = some (.thmInfo cv value)) := by
  unfold Setlec.unfoldDefinition at hux
  rw [Setlec.Expr.getAppFn_mkAppN,
    show (Expr.const n us).getAppFn = Expr.const n us from rfl]
    at hux
  simp only [] at hux
  cases hf : env.find? n with
  | none => rw [hf] at hux; exact nomatch hux
  | some ci =>
    rw [hf] at hux
    cases ci with
    | defnInfo cv value hint =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inl ⟨hint, rfl⟩⟩
        · have h2 := Option.some.inj hux
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us).getAppArgs = ([] : List Expr)
              from rfl, List.nil_append] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition,
            Setlec.Expr.getAppFn_mkAppN]
          rw [show (Expr.const n us').getAppFn = Expr.const n us'
            from rfl]
          simp only [hf]
          rw [if_pos (hlen ▸ hl)]
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us').getAppArgs = ([] : List Expr)
              from rfl, List.nil_append]
      · rw [if_neg hl] at hux; exact nomatch hux
    | thmInfo cv value =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inr rfl⟩
        · have h2 := Option.some.inj hux
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us).getAppArgs = ([] : List Expr)
              from rfl, List.nil_append] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition,
            Setlec.Expr.getAppFn_mkAppN]
          rw [show (Expr.const n us').getAppFn = Expr.const n us'
            from rfl]
          simp only [hf]
          rw [if_pos (hlen ▸ hl)]
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us').getAppArgs = ([] : List Expr)
              from rfl, List.nil_append]
      · rw [if_neg hl] at hux; exact nomatch hux
    | axiomInfo cv => exact nomatch hux
    | indInfo cv caps => exact nomatch hux
    | ctorInfo cv a b => exact nomatch hux
    | recInfo cv a b c => exact nomatch hux
    | projInfo entry => exact nomatch hux

/-- **Routed: the iota case** (recursor-headed spines at eval-linked
levels — the standing full treatment at its seal). -/
def ZipIotaCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb mI rP : Nat} {n : Name} {us us' : List Level}
    {cv : Setlec.ConstantVal} {rules : List Setlec.RecRule}
    {as bs : List Expr} {ℓa ℓb : Level},
    env.find? n = some (.recInfo cv mI rP rules) →
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) as) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Q d (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.const n us) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The both-δ core COLLAPSED onto the summit**: the spine facts
zip the pair (head by `constSlack` through `isEquivList` soundness,
args as `.cert` leaves through `defEqList_extract`), and
`ZipWhnfSortAgree` concludes. -/
theorem deltaSpineSortAgree_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipWhnfSortAgree μ env φ Q) :
    DeltaSpineSortAgree μ env φ Q := by
  intro fc d ga la gb lb a' b' ℓa ℓb hIa hIb hPab hQ hs hla hlb
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
          exact hZ hzip hIa hIb hPab hQ hla hlb
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
    (hZ : ZipWhnfSortAgree μ env φ Q) :
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
    (hZ : ZipWhnfSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q := by
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwsa hba hLa hwsb hbb hLb hp hQ
    h₁ h₂
  obtain ⟨ga, la, -, hla⟩ := whnf_peel h₁
  obtain ⟨gb, lb, -, hlb⟩ := whnf_peel h₂
  exact hZ (.cert a b hba hbb hc) (SubjInv.of_pair hwsa hba hLa hp)
    (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ hla hlb

/-- **(B) collapses onto the summit**: `SortOfAgreeRQ` from
`ZipSortOfAgree` alone, via the `.cert` leaf. -/
theorem sortOfAgreeRQ_of_zip {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipSortOfAgree μ env φ Q) :
    SortOfAgreeRQ μ env φ Q := by
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp hQ h₁ h₂
  exact hZ (.cert a b hba hbb hc) (SubjInv.of_pair hwsa hba hLa hp)
    (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ
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

/-- **The const head DISCHARGED to iota**: non-recursor heads are
inert (nat steps die on `NatStepNoSort`, δ unfolds together into
zipped instantiations, stuck outputs clash with the sorts); recursor
heads route to `ZipIotaCase`. -/
theorem zipConstHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hID : InvPreserveDeltaF env) (hLD : PairedPreserveDeltaF env)
    (hQD : QPreserveDeltaF env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hIota : ZipIotaCase μ env φ Q) :
    ZipConstHeadCase μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb n us us' as bs ℓa ℓb below hev hlen hargs
    hIs hIt hp hQ ha hb
  by_cases hrec : ∃ cv mI rP rules,
      env.find? n = some (.recInfo cv mI rP rules)
  · obtain ⟨cv, mI, rP, rules, hf⟩ := hrec
    exact hIota hf below hev hlen hargs hIs hIt hp hQ ha hb
  · have hnr : ∀ cv mI rP rules,
        env.find? n ≠ some (.recInfo cv mI rP rules) :=
      fun cv mI rP rules hf => hrec ⟨cv, mI, rP, rules, hf⟩
    have hnr' : ∀ cv mI rP rules,
        env.find? n ≠ some (.recInfo cv mI rP rules) := hnr
    have hlen' : us.length = us'.length := by
      have := congrArg List.length (hev fun _ => 0)
      simpa using this
    have hstuckA := whnfCore_mkAppN_const_inert (μ := μ) (d := d)
      (us := us) hnr as (Nat.le_refl _)
    have hstuckB := whnfCore_mkAppN_const_inert (μ := μ) (d := d)
      (us := us') hnr bs (Nat.le_refl _)
    cases la with
    | zero => exact nomatch ha
    | succ la' =>
    cases lb with
    | zero => exact nomatch hb
    | succ lb' =>
    have haD := ha
    rw [whnfLoop_succ] at haD
    obtain ⟨e₁, hwca, htriA⟩ := whnfStep_decompose haD
    obtain rfl : e₁ = Setlec.Expr.mkAppN (.const n us) as :=
      (KnotFuelDet_of_mono hm).2.2.1
        (hwca : whnfCore μ env ga d _ = .ok e₁) hstuckA
    have hbD := hb
    rw [whnfLoop_succ] at hbD
    obtain ⟨e₂, hwcb, htriB⟩ := whnfStep_decompose hbD
    obtain rfl : e₂ = Setlec.Expr.mkAppN (.const n us') bs :=
      (KnotFuelDet_of_mono hm).2.2.1
        (hwcb : whnfCore μ env gb d _ = .ok e₂) hstuckB
    rcases htriA with ⟨x, hrx, -⟩ | ⟨hrga, xa, hux, hkx⟩ |
      ⟨-, -, hstopA⟩
    · exact (hN hstuckA hrx ha).elim
    · obtain ⟨cv, value, rfl, huy', hstore⟩ :=
        unfoldDefinition_spine_both (us' := us') (bs := bs)
          hlen' hux
      rcases htriB with ⟨y, hry, -⟩ | ⟨hrgb, xb, huy, hky⟩ |
        ⟨-, hudb, -⟩
      · exact (hN hstuckB hry hb).elim
      · rw [huy'] at huy
        obtain rfl := (Option.some.inj huy).symm
        exact below (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
          (certZip_mkAppN_zips (certZip_instantiate hev value)
            hlen hargs)
          (hID hux hIs) (hID huy' hIt)
          ((hLD huy' ((hLD hux hp).symm)).symm)
          (hQs (hQD huy' (hQs (hQD hux hQ)))) hkx hky
      · rw [huy'] at hudb; exact nomatch hudb
    · cases as with
      | nil =>
        simp only [Setlec.Expr.mkAppN] at hstopA
        exact nomatch hstopA
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
          (F := Expr.const n us) (a := a) (as := as')
        rw [hpq] at hstopA
        exact nomatch hstopA

/-! ### The substitution-transport kit (core lemmas) -/

/-- Loose-bvar bounds are monotone. -/
theorem looseBVarsBounded_mono : ∀ {e : Expr} {j k : Nat}, j ≤ k →
    e.looseBVarsBounded j = true → e.looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at h ⊢
    omega
  | fvar idx n ty ih => intro j k hjk h; rfl
  | sort u => intro j k hjk h; rfl
  | const n us => intro j k hjk h; rfl
  | app f a ihf iha =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    exact ⟨ihf hjk h.1, iha hjk h.2⟩
  | lam n ty body m iht ihb =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    exact ⟨iht hjk h.1, ihb (Nat.succ_le_succ hjk) h.2⟩
  | forallE n ty body m iht ihb =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    exact ⟨iht hjk h.1, ihb (Nat.succ_le_succ hjk) h.2⟩
  | letE n ty val body iht ihv ihb =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨⟨iht hjk h1, ihv hjk h2⟩, ihb (Nat.succ_le_succ hjk) h3⟩
  | lit l => intro j k hjk h; rfl
  | proj sn i e ih =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded] at h ⊢
    exact ih hjk h

/-- Substitution transports well-scopedness (fvars and their
annotations pass through untouched; the plugged argument brings its
own). -/
theorem wScoped_instantiate1 {d : Nat} {a : Expr}
    (ha : Expr.WScoped d a) :
    ∀ {b : Expr} {k : Nat}, Expr.WScoped d b →
      Expr.WScoped d (b.instantiate1 a k) := by
  intro b
  induction b with
  | bvar i =>
    intro k hb
    simp only [Setlec.Expr.instantiate1]
    by_cases h : i = k
    · rw [if_pos h]; exact ha
    · rw [if_neg h]
      by_cases h2 : i > k <;> simp [h2, Setlec.Expr.WScoped]
  | fvar idx n ty ih => intro k hb; exact hb
  | sort u => intro k hb; exact hb
  | const n us => intro k hb; exact hb
  | app f a' ihf iha' =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨ihf hb.1, iha' hb.2⟩
  | lam n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨iht hb.1, ihb hb.2⟩
  | forallE n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨iht hb.1, ihb hb.2⟩
  | letE n ty val body iht ihv ihb =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨iht hb.1, ihv hb.2.1, ihb hb.2.2⟩
  | lit l => intro k hb; exact hb
  | proj sn i e ih =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ih hb

/-- Substitution of a closed argument transports the bvar bound down
one binder. -/
theorem looseBVarsBounded_instantiate1 {a : Expr}
    (ha : a.looseBVarsBounded 0 = true) :
    ∀ {b : Expr} {k : Nat}, b.looseBVarsBounded (k + 1) = true →
      (b.instantiate1 a k).looseBVarsBounded k = true := by
  intro b
  induction b with
  | bvar i =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at hb
    simp only [Setlec.Expr.instantiate1]
    by_cases h : i = k
    · rw [if_pos h]
      exact looseBVarsBounded_mono (Nat.zero_le k) ha
    · rw [if_neg h]
      have h2 : ¬ i > k := by omega
      rw [if_neg h2]
      simp only [Setlec.Expr.looseBVarsBounded, decide_eq_true_eq]
      omega
  | fvar idx n ty ih => intro k hb; rfl
  | sort u => intro k hb; rfl
  | const n us => intro k hb; rfl
  | app f a' ihf iha' =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, ihf hb.1, iha' hb.2,
      Bool.and_self]
  | lam n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, iht hb.1, ihb hb.2,
      Bool.and_self]
  | forallE n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, iht hb.1, ihb hb.2,
      Bool.and_self]
  | letE n ty val body iht ihv ihb =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, iht h1, ihv h2, ihb h3,
      Bool.and_self]
  | lit l => intro k hb; rfl
  | proj sn i e ih =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, ih hb]

/-- Substitution introduces no fvar leaves beyond the body's and the
argument's. -/
theorem fvarLeaves_instantiate1_mem {a : Expr} :
    ∀ {b : Expr} {k : Nat},
      ∀ l ∈ (b.instantiate1 a k).fvarLeaves,
        l ∈ b.fvarLeaves ∨ l ∈ a.fvarLeaves := by
  intro b
  induction b with
  | bvar i =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1] at hl
    by_cases h : i = k
    · rw [if_pos h] at hl; exact .inr hl
    · rw [if_neg h] at hl
      by_cases h2 : i > k
      · rw [if_pos h2] at hl
        simp [Setlec.Expr.fvarLeaves] at hl
      · rw [if_neg h2] at hl
        simp [Setlec.Expr.fvarLeaves] at hl
  | fvar idx n ty ih => intro k l hl; exact .inl hl
  | sort u => intro k l hl; exact .inl hl
  | const n us => intro k l hl; exact .inl hl
  | app f a' ihf iha' =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases ihf _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inl h'))
      · exact .inr h'
    · rcases iha' _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | lam n ty body m iht ihb =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases iht _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inl h'))
      · exact .inr h'
    · rcases ihb _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | forallE n ty body m iht ihb =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases iht _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inl h'))
      · exact .inr h'
    · rcases ihb _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | letE n ty val body iht ihv ihb =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases List.mem_append.1 h with h2 | h2
      · rcases iht _ h2 with h' | h'
        · exact .inl (List.mem_append.2 (.inl
            (List.mem_append.2 (.inl h'))))
        · exact .inr h'
      · rcases ihv _ h2 with h' | h'
        · exact .inl (List.mem_append.2 (.inl
            (List.mem_append.2 (.inr h'))))
        · exact .inr h'
    · rcases ihb _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | lit l' => intro k l hl; exact .inl hl
  | proj sn i e ih =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    exact ih _ hl

/-- `Q` survives a left-side certified β-contraction (the contractum
is not a whnfCore output, so the three step preservers cannot serve;
at `FrameQ` this discharges through the claims' β `Red` step — the
cert premise is exactly the rule's — plus the substitution kit for
the guards). -/
def QPreserveBetaF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {n : Name} {ty b a ta c : Expr}
    {m : Setlec.BinderMeta} {as : List Expr},
    inferTypeCore μ env g d a = .ok ta →
    isDefEqCore μ env g d ta ty = .ok true →
    Q d (Setlec.Expr.mkAppN (.app (.lam n ty b m) a) as) c →
    Q d (Setlec.Expr.mkAppN (b.instantiate1 a) as) c

/-- `Q` survives a left-side zeta-contraction (`ZetaEq.interp_eq` is
the named `FrameQ`-side supplier). -/
def QPreserveZetaF (_env : Env) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d : Nat} {n : Name} {ty v b c : Expr} {as : List Expr},
    Q d (Setlec.Expr.mkAppN (.letE n ty v b) as) c →
    Q d (Setlec.Expr.mkAppN (b.instantiate1 v) as) c

/-- `Q` survives completing the head's whnfCore under a spine (the
carrier's head re-basing steps; at `FrameQ` this discharges through
the claims' core preservation — whnfCore preserves denotation —
spine-composed). -/
def QPreserveHeadF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {P F c : Expr} {as : List Expr},
    whnfCore μ env g d P = .ok F →
    Q d (Setlec.Expr.mkAppN P as) c →
    Q d (Setlec.Expr.mkAppN F as) c

/-- whnfCore introduces no fvar leaves (the supplier is a Verify-tier
mutual induction over the core family, `StoredWF`-backed: stored
rule/definition values are fvar-free, and every contraction
substitutes existing subterms). -/
def LeavesSubCoreF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g d : Nat} {e e' : Expr},
    whnfCore μ env g d e = .ok e' →
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves

/-- `LeavesSubCoreF`'s supplier: the Verify-tier mutual fuel
induction (`whnfPres_leaves`), under environment well-formedness. -/
theorem leavesSubCore_of (henv : Setlec.EnvWF env) :
    LeavesSubCoreF μ env :=
  fun h => Setlec.whnfCore_leaves henv _ h

/-- `Q` descends through an app-node pair (the peel's head
recursion; at `FrameQ` the frame is per-side structural — a
defined application has defined parts). -/
def QDescendAppF (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d : Nat} {P y R z : Expr},
    Q d (.app P y) (.app R z) → Q d P R

/- TOMBSTONE (do not restate): `CoreIdemF` — whnfCore idempotence on
outputs — briefly re-entered the ledger here as the head re-basing's
connecting-run supplier, and was caught at its supplier seal against
the STANDING refutation (`WhnfCoreIdem`, the strLit corner: an
accepted env's `String.ofList` body makes the proj-scrutinee literal
re-expansion a genuine second reduction step).  The consumers ride
the R-a family instead: iota fires and δ-steps force const heads
(`iotaRec_some_head` / `unfoldDefinition_some_head` →
`whnfCore_reidem_const`), β-side heads are λ-values
(`whnfCore_lam_run`), sort stops are values (`whnfCore_sort_run`),
and non-const stuck sides exit dead seams. -/

/-- An iota fire's subject is const-headed. -/
theorem iotaRec_some_head {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e x : Expr}
    (h : Setlec.iotaRec μ r env d e = .ok (some x)) :
    ∃ n us, e.getAppFn = Setlec.Expr.const n us := by
  by_cases hc : ∃ n us, e.getAppFn = Setlec.Expr.const n us
  · exact hc
  · rw [iotaRec_none_of_fn_not_const
        (fun n us hh => hc ⟨n, us, hh⟩)] at h
    exact nomatch h

/-! ### The seam datatype and its app-lift (the coreLock design) -/

/-- **The liftable seams**: the configurations the layer-peeling
lockstep cannot zip through, each convertible by the top-level
caller (which holds the loop runs) and each liftable through an
app-layer because view-heads propagate.  `deadL`/`deadR` carry a
self-sustaining stuck package (run + head-shape data) so the lift
is one derivation step. -/
inductive CoreSeam (μ : CheckMode) (env : Env) (fc d : Nat) :
    Expr → Expr → Prop
  | certHead (F₁ F₂ : Expr) (as bs : List Expr)
      (hba : F₁.looseBVarsBounded 0 = true)
      (hbb : F₂.looseBVarsBounded 0 = true)
      (hc : isDefEqCore μ env fc d F₁ F₂ = .ok true)
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) :
      CoreSeam μ env fc d (Setlec.Expr.mkAppN F₁ as)
        (Setlec.Expr.mkAppN F₂ bs)
  | recHead (n : Name) (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rules : List Setlec.RecRule) (us us' : List Level)
      (as bs : List Expr)
      (hf : env.find? n = some (.recInfo cv mI rP rules))
      (hev : ∀ φ' : Name → Nat,
        us.map (Level.eval φ') = us'.map (Level.eval φ'))
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) :
      CoreSeam μ env fc d (Setlec.Expr.mkAppN (.const n us) as)
        (Setlec.Expr.mkAppN (.const n us') bs)
  | projHead (sn : Name) (i : Nat) (e₁ e₂ : Expr) (as bs : List Expr)
      (he : CertZip μ env fc d e₁ e₂)
      (hlen : as.length = bs.length)
      (hargs : ∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
        CertZip μ env fc d as[j] bs[j]) :
      CoreSeam μ env fc d (Setlec.Expr.mkAppN (.proj sn i e₁) as)
        (Setlec.Expr.mkAppN (.proj sn i e₂) bs)
  | deadL (u v u' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d u = .ok u')
      (hnc : ∀ p q, u'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, u' ≠ .lam n ty body m)
      (hns : ∀ ℓ, u' ≠ .sort ℓ) :
      CoreSeam μ env fc d u v
  | deadR (u v v' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d v = .ok v')
      (hnc : ∀ p q, v'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, v' ≠ .lam n ty body m)
      (hns : ∀ ℓ, v' ≠ .sort ℓ) :
      CoreSeam μ env fc d u v

/-- One stuck derivation step for the dead seams' lift: an app over
a dead-stuck head is itself dead-stuck. -/
theorem dead_step {μ : CheckMode} {env : Env} {d : Nat}
    {u u' y : Expr} {b : Nat}
    (hrun : ∀ g, b ≤ g → whnfCore μ env g d u = .ok u')
    (hnc : ∀ p q, u'.getAppFn ≠ .const p q)
    (hnl : ∀ n ty body m, u' ≠ .lam n ty body m) :
    ∀ g, b + 1 ≤ g → whnfCore μ env g d (.app u y)
      = .ok (.app u' y) := by
  intro g hg
  cases g with
  | zero => exact absurd hg (by omega)
  | succ g' =>
  rw [show whnfCore μ env (g' + 1) d (.app u y)
      = Setlec.whnfCoreBody μ (Setlec.pureFns μ env g') env d
        (.app u y) from Setlec.whnfCore_succ ..]
  have hiota : Setlec.iotaRec μ (Setlec.pureFns μ env g') env d
      (.app u' y) = .ok none :=
    iotaRec_none_of_fn_not_const
      (by intro p q hh
          exact hnc p q
            ((show (Expr.app u' y).getAppFn = u'.getAppFn
              from rfl) ▸ hh))
  have hu : (Setlec.pureFns μ env g').whnfCore d u = .ok u' :=
    hrun g' (by omega)
  cases u' with
  | lam n ty body m => exact absurd rfl (hnl n ty body m)
  | const p q =>
    exact absurd (show (Expr.const p q).getAppFn = Expr.const p q
      from rfl) (hnc p q)
  | bvar i =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | fvar i n ty =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | sort u₀ =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | forallE n ty body m =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | letE n ty v b' =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | lit l =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | proj sn i e =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | app p q =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl

/-- **Seams lift through app-layers** (view-heads propagate; the
flatten seams append the argument zip, the dead seams take one
stuck derivation step). -/
theorem coreSeam_lift_app {μ : CheckMode} {env : Env} {fc d : Nat}
    {P₁ P₂ y₁ y₂ : Expr}
    (hz : CertZip μ env fc d y₁ y₂)
    (hs : CoreSeam μ env fc d P₁ P₂) :
    CoreSeam μ env fc d (.app P₁ y₁) (.app P₂ y₂) := by
  cases hs with
  | certHead F₁ F₂ as bs hba hbb hc hlen hargs =>
    rw [show Expr.app (Setlec.Expr.mkAppN F₁ as) y₁
        = Setlec.Expr.mkAppN F₁ (as ++ [y₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN F₂ bs) y₂
        = Setlec.Expr.mkAppN F₂ (bs ++ [y₂]) from
      mkAppN_append_one.symm]
    refine CoreSeam.certHead F₁ F₂ (as ++ [y₁]) (bs ++ [y₂])
      hba hbb hc (by simp [hlen]) ?_
    intro i hi₁ hi₂
    by_cases hlt : i < as.length
    · have hlt₂ : i < bs.length := hlen ▸ hlt
      rw [getElem_append_left' as [y₁] i hlt,
        getElem_append_left' bs [y₂] i hlt₂]
      exact hargs i hlt hlt₂
    · have hi : i = as.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hi₁
        omega
      subst hi
      rw [getElem_append_last as y₁]
      simp only [hlen]
      rw [getElem_append_last bs y₂]
      exact hz
  | recHead n cv mI rP rules us us' as bs hf hev hlen hargs =>
    rw [show Expr.app (Setlec.Expr.mkAppN (.const n us) as) y₁
        = Setlec.Expr.mkAppN (.const n us) (as ++ [y₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN (.const n us') bs) y₂
        = Setlec.Expr.mkAppN (.const n us') (bs ++ [y₂]) from
      mkAppN_append_one.symm]
    refine CoreSeam.recHead n cv mI rP rules us us'
      (as ++ [y₁]) (bs ++ [y₂]) hf hev (by simp [hlen]) ?_
    intro i hi₁ hi₂
    by_cases hlt : i < as.length
    · have hlt₂ : i < bs.length := hlen ▸ hlt
      rw [getElem_append_left' as [y₁] i hlt,
        getElem_append_left' bs [y₂] i hlt₂]
      exact hargs i hlt hlt₂
    · have hi : i = as.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hi₁
        omega
      subst hi
      rw [getElem_append_last as y₁]
      simp only [hlen]
      rw [getElem_append_last bs y₂]
      exact hz
  | projHead sn i e₁ e₂ as bs he hlen hargs =>
    rw [show Expr.app (Setlec.Expr.mkAppN (.proj sn i e₁) as) y₁
        = Setlec.Expr.mkAppN (.proj sn i e₁) (as ++ [y₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN (.proj sn i e₂) bs) y₂
        = Setlec.Expr.mkAppN (.proj sn i e₂) (bs ++ [y₂]) from
      mkAppN_append_one.symm]
    refine CoreSeam.projHead sn i e₁ e₂ (as ++ [y₁]) (bs ++ [y₂])
      he (by simp [hlen]) ?_
    intro j hj₁ hj₂
    by_cases hlt : j < as.length
    · have hlt₂ : j < bs.length := hlen ▸ hlt
      rw [getElem_append_left' as [y₁] j hlt,
        getElem_append_left' bs [y₂] j hlt₂]
      exact hargs j hlt hlt₂
    · have hj : j = as.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hj₁
        omega
      subst hj
      rw [getElem_append_last as y₁]
      simp only [hlen]
      rw [getElem_append_last bs y₂]
      exact hz
  | deadL u v u' b hrun hnc hnl hns =>
    refine CoreSeam.deadL _ _ (.app u' y₁) (b + 1)
      (dead_step hrun hnc hnl) ?_ ?_ ?_
    · intro p q h
      exact hnc p q
        ((show (Expr.app u' y₁).getAppFn = u'.getAppFn from rfl) ▸ h)
    · intro n ty body m h; exact nomatch h
    · intro ℓ h; exact nomatch h
  | deadR u v v' b hrun hnc hnl hns =>
    refine CoreSeam.deadR _ _ (.app v' y₂) (b + 1)
      (dead_step hrun hnc hnl) ?_ ?_ ?_
    · intro p q h
      exact hnc p q
        ((show (Expr.app v' y₂).getAppFn = v'.getAppFn from rfl) ▸ h)
    · intro n ty body m h; exact nomatch h
    · intro ℓ h; exact nomatch h

/-! ### Spine-fold invariant helpers (the trace-transport kit) -/

/-- Head leaves persist into the spine. -/
theorem mem_fvarLeaves_mkAppN_head {l : Nat × Name × Expr} :
    ∀ {as : List Expr} {F : Expr}, l ∈ F.fvarLeaves →
      l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves := by
  intro as
  induction as with
  | nil => intro F h; exact h
  | cons a as ih =>
    intro F h
    exact ih (F := .app F a)
      (by simp only [Setlec.Expr.fvarLeaves]
          exact List.mem_append.2 (.inl h))

/-- Argument leaves persist into the spine. -/
theorem mem_fvarLeaves_mkAppN_arg {l : Nat × Name × Expr} :
    ∀ {as : List Expr} {F a : Expr}, a ∈ as → l ∈ a.fvarLeaves →
      l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves := by
  intro as
  induction as with
  | nil => intro F a h; exact absurd h List.not_mem_nil
  | cons a' as ih =>
    intro F a h hl
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_fvarLeaves_mkAppN_head (F := .app F a)
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inr hl))
    · exact ih h hl

/-- Spine leaves come from the head or an argument. -/
theorem fvarLeaves_mkAppN_cases {l : Nat × Name × Expr} :
    ∀ {as : List Expr} {F : Expr},
      l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves →
      l ∈ F.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves := by
  intro as
  induction as with
  | nil => intro F h; exact .inl h
  | cons a as ih =>
    intro F h
    rcases ih (F := .app F a) h with h' | ⟨a', ha', hl'⟩
    · simp only [Setlec.Expr.fvarLeaves] at h'
      rcases List.mem_append.1 h' with h'' | h''
      · exact .inl h''
      · exact .inr ⟨a, List.mem_cons_self .., h''⟩
    · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hl'⟩

/-- Build well-scopedness of a spine from its parts. -/
theorem wScoped_mkAppN_build {d : Nat} :
    ∀ {as : List Expr} {F : Expr}, Expr.WScoped d F →
      (∀ a ∈ as, Expr.WScoped d a) →
      Expr.WScoped d (Setlec.Expr.mkAppN F as) := by
  intro as
  induction as with
  | nil => intro F hF _; exact hF
  | cons a as ih =>
    intro F hF hargs
    exact ih (F := .app F a)
      (by simp only [Setlec.Expr.WScoped]
          exact ⟨hF, hargs a (List.mem_cons_self ..)⟩)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-- Decompose well-scopedness of a spine into its parts. -/
theorem wScoped_mkAppN_parts {d : Nat} :
    ∀ {as : List Expr} {F : Expr},
      Expr.WScoped d (Setlec.Expr.mkAppN F as) →
      Expr.WScoped d F ∧ ∀ a ∈ as, Expr.WScoped d a := by
  intro as
  induction as with
  | nil => intro F h; exact ⟨h, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a as ih =>
    intro F h
    obtain ⟨happ, hargs⟩ := ih (F := .app F a) h
    simp only [Setlec.Expr.WScoped] at happ
    refine ⟨happ.1, ?_⟩
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact happ.2
    · exact hargs a' ha'

/-- Build the bvar bound of a spine from its parts. -/
theorem looseBVarsBounded_mkAppN_build {k : Nat} :
    ∀ {as : List Expr} {F : Expr}, F.looseBVarsBounded k = true →
      (∀ a ∈ as, a.looseBVarsBounded k = true) →
      (Setlec.Expr.mkAppN F as).looseBVarsBounded k = true := by
  intro as
  induction as with
  | nil => intro F hF _; exact hF
  | cons a as ih =>
    intro F hF hargs
    exact ih (F := .app F a)
      (by simp only [Setlec.Expr.looseBVarsBounded,
            Bool.and_eq_true]
          exact ⟨hF, hargs a (List.mem_cons_self ..)⟩)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-- Decompose the bvar bound of a spine into its parts. -/
theorem looseBVarsBounded_mkAppN_parts {k : Nat} :
    ∀ {as : List Expr} {F : Expr},
      (Setlec.Expr.mkAppN F as).looseBVarsBounded k = true →
      F.looseBVarsBounded k = true ∧
        ∀ a ∈ as, a.looseBVarsBounded k = true := by
  intro as
  induction as with
  | nil => intro F h; exact ⟨h, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a as ih =>
    intro F h
    obtain ⟨happ, hargs⟩ := ih (F := .app F a) h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at happ
    refine ⟨happ.1, ?_⟩
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact happ.2
    · exact hargs a' ha'

/-- A head's leaf subset spreads over the spine. -/
theorem head_leaves_sub {P F : Expr} {as : List Expr}
    (hsub : ∀ l ∈ F.fvarLeaves, l ∈ P.fvarLeaves) :
    ∀ l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN P as).fvarLeaves := by
  intro l hl
  rcases fvarLeaves_mkAppN_cases hl with h | ⟨a', ha', hl'⟩
  · exact mem_fvarLeaves_mkAppN_head (hsub l h)
  · exact mem_fvarLeaves_mkAppN_arg ha' hl'

/-- One β-step's leaf subset (spine form). -/
theorem beta_leaves_sub {n : Name} {ty b a : Expr}
    {m : Setlec.BinderMeta} {as : List Expr} :
    ∀ l ∈ (Setlec.Expr.mkAppN (b.instantiate1 a) as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN (.app (.lam n ty b m) a) as).fvarLeaves
    := by
  intro l hl
  rcases fvarLeaves_mkAppN_cases hl with h | ⟨a', ha', hl'⟩
  · rcases fvarLeaves_instantiate1_mem _ h with h' | h'
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inl (List.mem_append.2
              (.inr h'))))
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inr h'))
  · exact mem_fvarLeaves_mkAppN_arg ha' hl'

/-- One zeta-step's leaf subset (spine form). -/
theorem zeta_leaves_sub {n : Name} {ty v b : Expr} {as : List Expr} :
    ∀ l ∈ (Setlec.Expr.mkAppN (b.instantiate1 v) as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN (.letE n ty v b) as).fvarLeaves := by
  intro l hl
  rcases fvarLeaves_mkAppN_cases hl with h | ⟨a', ha', hl'⟩
  · rcases fvarLeaves_instantiate1_mem _ h with h' | h'
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inr h'))
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inl (List.mem_append.2
              (.inr h'))))
  · exact mem_fvarLeaves_mkAppN_arg ha' hl'

/-- **The reduction trace**: spine-positioned β/zeta chains plus
head-whnf re-basing steps (transitive by construction; the
contraction constructors match the two contraction species' shapes
exactly, the head constructor matches `QPreserveHeadF`'s).  The
head steps are what the peel's ZipPack outcome erases — a refl
bottom swallows arbitrary whnfCore history — so seam subjects
reached past such a bottom need them. -/
inductive Contracts (μ : CheckMode) (env : Env) (d : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : Contracts μ env d e e
  | beta (n : Name) (ty b a ta : Expr) (m : Setlec.BinderMeta)
      (as : List Expr) (g : Nat) {w : Expr}
      (hinf : inferTypeCore μ env g d a = .ok ta)
      (hdq : isDefEqCore μ env g d ta ty = .ok true)
      (hrest : Contracts μ env d
        (Setlec.Expr.mkAppN (b.instantiate1 a) as) w) :
      Contracts μ env d
        (Setlec.Expr.mkAppN (.app (.lam n ty b m) a) as) w
  | zeta (n : Name) (ty v b : Expr) (as : List Expr) {w : Expr}
      (hrest : Contracts μ env d
        (Setlec.Expr.mkAppN (b.instantiate1 v) as) w) :
      Contracts μ env d
        (Setlec.Expr.mkAppN (.letE n ty v b) as) w
  | head (P F : Expr) (as : List Expr) (g : Nat) {w : Expr}
      (hr : whnfCore μ env g d P = .ok F)
      (hrest : Contracts μ env d (Setlec.Expr.mkAppN F as) w) :
      Contracts μ env d (Setlec.Expr.mkAppN P as) w

/-- Q rides the trace. -/
theorem Contracts.q_transport {μ : CheckMode} {env : Env} {d : Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    {u w c : Expr} (h : Contracts μ env d u w) :
    Q d u c → Q d w c := by
  induction h with
  | refl e => exact id
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    exact fun hq => ih (hQB hinf hdq hq)
  | zeta n ty v b as hrest ih =>
    exact fun hq => ih (hQZ hq)
  | head P F as g hr hrest ih =>
    exact fun hq => ih (hQH hr hq)

/-- The trace only shrinks the leaf set. -/
theorem Contracts.leaves_sub {μ : CheckMode} {env : Env} {d : Nat}
    (hLS : LeavesSubCoreF μ env)
    {u w : Expr} (h : Contracts μ env d u w) :
    ∀ l ∈ w.fvarLeaves, l ∈ u.fvarLeaves := by
  induction h with
  | refl e => exact fun l hl => hl
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    exact fun l hl => beta_leaves_sub l (ih l hl)
  | zeta n ty v b as hrest ih =>
    exact fun l hl => zeta_leaves_sub l (ih l hl)
  | head P F as g hr hrest ih =>
    exact fun l hl => head_leaves_sub (hLS hr) l (ih l hl)

/-- `SubjInv` rides the trace (the substitution kit at each step;
self-pairing restricts through the leaf subset). -/
theorem Contracts.subjInv {μ : CheckMode} {env : Env} {d : Nat}
    (hIC : InvPreserveCoreF μ env) (hLS : LeavesSubCoreF μ env)
    {u w : Expr} (h : Contracts μ env d u w)
    (hI : SubjInv d u) : SubjInv d w := by
  induction h with
  | refl e => exact hI
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    refine ih ?_
    obtain ⟨hw, hb, hL, hp⟩ := hI
    obtain ⟨hwapp, hwargs⟩ := wScoped_mkAppN_parts hw
    obtain ⟨hbapp, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
    simp only [Setlec.Expr.WScoped] at hwapp
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hbapp
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wScoped_mkAppN_build
        (wScoped_instantiate1 hwapp.2 hwapp.1.2) hwargs
    · exact looseBVarsBounded_mkAppN_build
        (looseBVarsBounded_instantiate1 hbapp.2 hbapp.1.2) hbargs
    · exact fun l hl => hL l (beta_leaves_sub l hl)
    · intro l hl l' hl' heq
      rw [List.mem_append] at hl hl'
      exact hp l
        (List.mem_append.2 (.inl (beta_leaves_sub l
          (hl.elim id id))))
        l' (List.mem_append.2 (.inl (beta_leaves_sub l'
          (hl'.elim id id)))) heq
  | zeta n ty v b as hrest ih =>
    refine ih ?_
    obtain ⟨hw, hb, hL, hp⟩ := hI
    obtain ⟨hwlet, hwargs⟩ := wScoped_mkAppN_parts hw
    obtain ⟨hblet, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
    simp only [Setlec.Expr.WScoped] at hwlet
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hblet
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wScoped_mkAppN_build
        (wScoped_instantiate1 hwlet.2.1 hwlet.2.2) hwargs
    · exact looseBVarsBounded_mkAppN_build
        (looseBVarsBounded_instantiate1 hblet.1.2 hblet.2) hbargs
    · exact fun l hl => hL l (zeta_leaves_sub l hl)
    · intro l hl l' hl' heq
      rw [List.mem_append] at hl hl'
      exact hp l
        (List.mem_append.2 (.inl (zeta_leaves_sub l
          (hl.elim id id))))
        l' (List.mem_append.2 (.inl (zeta_leaves_sub l'
          (hl'.elim id id)))) heq
  | head P F as g hr hrest ih =>
    refine ih ?_
    obtain ⟨hw, hb, hL, hp⟩ := hI
    obtain ⟨hwP, hwargs⟩ := wScoped_mkAppN_parts hw
    obtain ⟨hbP, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
    have hIP : SubjInv d P :=
      ⟨hwP, hbP,
        fun l hl => hL l (mem_fvarLeaves_mkAppN_head hl),
        fun l hl l' hl' heq => hp l
          (List.mem_append.2 (.inl (mem_fvarLeaves_mkAppN_head
            ((List.mem_append.1 hl).elim id id))))
          l' (List.mem_append.2 (.inl (mem_fvarLeaves_mkAppN_head
            ((List.mem_append.1 hl').elim id id)))) heq⟩
    have hIF : SubjInv d F := hIC hr hIP
    have hsub : ∀ l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves,
        l ∈ (Setlec.Expr.mkAppN P as).fvarLeaves :=
      head_leaves_sub (hLS hr)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wScoped_mkAppN_build hIF.1 hwargs
    · exact looseBVarsBounded_mkAppN_build hIF.2.1 hbargs
    · exact fun l hl => hL l (hsub l hl)
    · intro l hl l' hl' heq
      rw [List.mem_append] at hl hl'
      exact hp l
        (List.mem_append.2 (.inl (hsub l (hl.elim id id))))
        l' (List.mem_append.2 (.inl (hsub l' (hl'.elim id id)))) heq

/-- Cross-pairing rides two traces (through the leaf subsets). -/
theorem Contracts.pairing {μ : CheckMode} {env : Env} {d : Nat}
    (hLS : LeavesSubCoreF μ env) {u v w₁ w₂ : Expr}
    (h₁ : Contracts μ env d u w₁) (h₂ : Contracts μ env d v w₂)
    (hp : PairedLeaves u v) : PairedLeaves w₁ w₂ := by
  intro l hl l' hl' heq
  rw [List.mem_append] at hl hl'
  refine hp l ?_ l' ?_ heq
  · exact List.mem_append.2
      (hl.elim (fun h => .inl (h₁.leaves_sub hLS l h))
        (fun h => .inr (h₂.leaves_sub hLS l h)))
  · exact List.mem_append.2
      (hl'.elim (fun h => .inl (h₁.leaves_sub hLS l' h))
        (fun h => .inr (h₂.leaves_sub hLS l' h)))

/-- Traces lift through app-layers (the contraction site keeps its
spine position under one more argument). -/
theorem Contracts.app_lift {μ : CheckMode} {env : Env} {d : Nat}
    {u w y : Expr} (h : Contracts μ env d u w) :
    Contracts μ env d (.app u y) (.app w y) := by
  induction h with
  | refl e => exact .refl _
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    rw [show Expr.app (Setlec.Expr.mkAppN
        (.app (.lam n ty b m) a) as) y
      = Setlec.Expr.mkAppN (.app (.lam n ty b m) a) (as ++ [y])
      from mkAppN_append_one.symm]
    refine Contracts.beta n ty b a ta m (as ++ [y]) g hinf hdq ?_
    rw [show Setlec.Expr.mkAppN (b.instantiate1 a) (as ++ [y])
      = Expr.app (Setlec.Expr.mkAppN (b.instantiate1 a) as) y
      from mkAppN_append_one]
    exact ih
  | zeta n ty v b as hrest ih =>
    rw [show Expr.app (Setlec.Expr.mkAppN (.letE n ty v b) as) y
      = Setlec.Expr.mkAppN (.letE n ty v b) (as ++ [y])
      from mkAppN_append_one.symm]
    refine Contracts.zeta n ty v b (as ++ [y]) ?_
    rw [show Setlec.Expr.mkAppN (b.instantiate1 v) (as ++ [y])
      = Expr.app (Setlec.Expr.mkAppN (b.instantiate1 v) as) y
      from mkAppN_append_one]
    exact ih
  | head P F as g hr hrest ih =>
    rw [show Expr.app (Setlec.Expr.mkAppN P as) y
      = Setlec.Expr.mkAppN P (as ++ [y]) from mkAppN_append_one.symm]
    refine Contracts.head P F (as ++ [y]) g hr ?_
    rw [show Setlec.Expr.mkAppN F (as ++ [y])
      = Expr.app (Setlec.Expr.mkAppN F as) y from mkAppN_append_one]
    exact ih

/-! ### The coreLock helper tier -/

/-- whnfCore is the identity on non-redex shapes. -/
theorem whnfCore_inert {μ : CheckMode} {env : Env} {g d : Nat}
    {e e' : Expr}
    (hna : ∀ f a, e ≠ .app f a)
    (hnl : ∀ n ty v b, e ≠ .letE n ty v b)
    (hnp : ∀ sn i s, e ≠ .proj sn i s)
    (h : whnfCore μ env g d e = .ok e') : e' = e := by
  cases g with
  | zero => rw [Setlec.whnfCore_zero] at h; exact nomatch h
  | succ g' =>
    rw [Setlec.whnfCore_succ] at h
    unfold Setlec.whnfCoreBody at h
    cases e with
    | app f a => exact absurd rfl (hna f a)
    | letE n ty v b => exact absurd rfl (hnl n ty v b)
    | proj sn i s => exact absurd rfl (hnp sn i s)
    | bvar i => simp only [] at h; exact nomatch h
    | fvar i n ty => simp only [] at h; exact (Except.ok.inj h).symm
    | sort u0 => simp only [] at h; exact (Except.ok.inj h).symm
    | const n us => simp only [] at h; exact (Except.ok.inj h).symm
    | lam n ty b m => simp only [] at h; exact (Except.ok.inj h).symm
    | forallE n ty b m =>
      simp only [] at h; exact (Except.ok.inj h).symm
    | lit l => simp only [] at h; exact (Except.ok.inj h).symm

/-- Pairing restricts along leaf subsets on both slots. -/
theorem pairedLeaves_mono {a b a' b' : Expr}
    (hsa : ∀ l ∈ a'.fvarLeaves, l ∈ a.fvarLeaves)
    (hsb : ∀ l ∈ b'.fvarLeaves, l ∈ b.fvarLeaves)
    (hp : PairedLeaves a b) : PairedLeaves a' b' := by
  intro l hl l' hl' heq
  rw [List.mem_append] at hl hl'
  exact hp l (List.mem_append.2 (hl.imp (hsa l) (hsb l)))
    l' (List.mem_append.2 (hl'.imp (hsa l') (hsb l'))) heq

/-- A function-position leaf is an app leaf. -/
theorem mem_fvarLeaves_app_left {f a : Expr} :
    ∀ l ∈ f.fvarLeaves, l ∈ (Expr.app f a).fvarLeaves := by
  intro l hl
  simp only [Setlec.Expr.fvarLeaves]
  exact List.mem_append.2 (.inl hl)

/-- An argument-position leaf is an app leaf. -/
theorem mem_fvarLeaves_app_right {f a : Expr} :
    ∀ l ∈ a.fvarLeaves, l ∈ (Expr.app f a).fvarLeaves := by
  intro l hl
  simp only [Setlec.Expr.fvarLeaves]
  exact List.mem_append.2 (.inr hl)

/-- The subject package descends through an app node. -/
theorem subjInv_app {d : Nat} {f a : Expr}
    (h : SubjInv d (.app f a)) : SubjInv d f ∧ SubjInv d a := by
  obtain ⟨hw, hb, hL, hp⟩ := h
  simp only [Setlec.Expr.WScoped] at hw
  simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (mem_fvarLeaves_app_left l hl),
      pairedLeaves_mono mem_fvarLeaves_app_left
        mem_fvarLeaves_app_left hp⟩,
    ⟨hw.2, hb.2, fun l hl => hL l (mem_fvarLeaves_app_right l hl),
      pairedLeaves_mono mem_fvarLeaves_app_right
        mem_fvarLeaves_app_right hp⟩⟩

/-- Pairwise argument zips extend by one (the flatten seams' append
step, extracted). -/
theorem zip_args_append {μ : CheckMode} {env : Env} {fc d : Nat}
    {as bs : List Expr} {y₁ y₂ : Expr}
    (hlen : as.length = bs.length)
    (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i])
    (hy : CertZip μ env fc d y₁ y₂) :
    ∀ i (h₁ : i < (as ++ [y₁]).length) (h₂ : i < (bs ++ [y₂]).length),
      CertZip μ env fc d (as ++ [y₁])[i] (bs ++ [y₂])[i] := by
  intro i hi₁ hi₂
  by_cases hlt : i < as.length
  · have hlt₂ : i < bs.length := hlen ▸ hlt
    rw [getElem_append_left' as [y₁] i hlt,
      getElem_append_left' bs [y₂] i hlt₂]
    exact hargs i hlt hlt₂
  · have hi : i = as.length := by
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hi₁
      omega
    subst hi
    rw [getElem_append_last as y₁]
    simp only [hlen]
    rw [getElem_append_last bs y₂]
    exact hy

/-- A non-app expression is its own spine head. -/
theorem getAppFn_of_not_app {e : Expr}
    (h : ∀ p q, e ≠ .app p q) : e.getAppFn = e := by
  cases e with
  | app p q => exact absurd rfl (h p q)
  | bvar i => rfl
  | fvar i n ty => rfl
  | sort u0 => rfl
  | const n us => rfl
  | lam n ty b m => rfl
  | forallE n ty b m => rfl
  | letE n ty v b => rfl
  | lit l => rfl
  | proj sn i s => rfl

/-- A recorded iota fire under a non-recursor const head is
absurd. -/
theorem absurd_rec_fire {μ : CheckMode} {env : Env}
    {d g₁' g₂' : Nat} {S₁ S₂ : Expr} {n : Name}
    {us us' : List Level} {C : Prop}
    (hfn₁ : S₁.getAppFn = .const n us)
    (hfn₂ : S₂.getAppFn = .const n us')
    (hsome :
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₁') env d S₁
        = .ok (some e'')) ∨
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₂') env d S₂
        = .ok (some e'')))
    (hnr : ∀ cv mI rP rules,
      env.find? n ≠ some (.recInfo cv mI rP rules)) : C := by
  exfalso
  rcases hsome with ⟨e'', hio⟩ | ⟨e'', hio⟩
  · rw [iotaRec_none_of_not_rec hfn₁ hnr] at hio
    exact nomatch hio
  · rw [iotaRec_none_of_not_rec hfn₂ hnr] at hio
    exact nomatch hio

/-- **The stuck-spine exit**: a zipped app-pair on which some side's
iota fires exits as a flatten seam — the spine view walks to the
first cert layer (`certHead`) or a shared-name const head
(`recHead` under `recInfo`), and every other head shape refutes
the fire.  Fire-agnostic on the other side (mixed fire is the
top's `ZipIotaCase` business). -/
theorem zip_stuck_spine_exit {μ : CheckMode} {env : Env}
    {fc d g₁' g₂' : Nat} {F₁ F₂ a₁ a₂ : Expr}
    (hzF : CertZip μ env fc d F₁ F₂)
    (hza : CertZip μ env fc d a₁ a₂)
    (hsome :
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₁') env d
        (.app F₁ a₁) = .ok (some e'')) ∨
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₂') env d
        (.app F₂ a₂) = .ok (some e''))) :
    CoreSeam μ env fc d (.app F₁ a₁) (.app F₂ a₂) := by
  obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlen, hargs, hhead⟩ :=
    certZip_app_view hzF
  rcases hhead with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
  · rw [show Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁
        = Setlec.Expr.mkAppN H₁ (cs ++ [a₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂
        = Setlec.Expr.mkAppN H₂ (ds ++ [a₂]) from
      mkAppN_append_one.symm]
    exact CoreSeam.certHead H₁ H₂ (cs ++ [a₁]) (ds ++ [a₂])
      hba hbb hc (by simp [hlen]) (zip_args_append hlen hargs hza)
  · have hfn₁ : (Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁).getAppFn
        = H₁ := by
      rw [show (Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁).getAppFn
          = (Setlec.Expr.mkAppN H₁ cs).getAppFn from rfl,
        Setlec.Expr.getAppFn_mkAppN cs H₁,
        getAppFn_of_not_app hne₁]
    have hfn₂ : (Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂).getAppFn
        = H₂ := by
      rw [show (Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂).getAppFn
          = (Setlec.Expr.mkAppN H₂ ds).getAppFn from rfl,
        Setlec.Expr.getAppFn_mkAppN ds H₂,
        getAppFn_of_not_app hne₂]
    have hcontra : (∀ p q, H₁ ≠ Expr.const p q) →
        (∀ p q, H₂ ≠ Expr.const p q) → False := by
      intro hnc₁ hnc₂
      rcases hsome with ⟨e'', hio⟩ | ⟨e'', hio⟩
      · rw [iotaRec_none_of_fn_not_const
            (fun n us h => hnc₁ n us (hfn₁.symm.trans h))] at hio
        exact nomatch hio
      · rw [iotaRec_none_of_fn_not_const
            (fun n us h => hnc₂ n us (hfn₂.symm.trans h))] at hio
        exact nomatch hio
    have recExit : ∀ {n : Name} {us us' : List Level},
        H₁ = .const n us → H₂ = .const n us' →
        (∀ φ' : Name → Nat,
          us.map (Level.eval φ') = us'.map (Level.eval φ')) →
        CoreSeam μ env fc d
          (.app (Setlec.Expr.mkAppN H₁ cs) a₁)
          (.app (Setlec.Expr.mkAppN H₂ ds) a₂) := by
      intro n us us' he₁ he₂ hev
      subst he₁; subst he₂
      cases hf : env.find? n with
      | some ci =>
        cases ci with
        | recInfo cv mI rP rules =>
          rw [show Expr.app
                (Setlec.Expr.mkAppN (Expr.const n us) cs) a₁
              = Setlec.Expr.mkAppN (Expr.const n us) (cs ++ [a₁])
              from mkAppN_append_one.symm,
            show Expr.app
                (Setlec.Expr.mkAppN (Expr.const n us') ds) a₂
              = Setlec.Expr.mkAppN (Expr.const n us') (ds ++ [a₂])
              from mkAppN_append_one.symm]
          exact CoreSeam.recHead n cv mI rP rules us us'
            (cs ++ [a₁]) (ds ++ [a₂]) hf hev (by simp [hlen])
            (zip_args_append hlen hargs hza)
        | defnInfo cv val hints =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | thmInfo cv val =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | axiomInfo cv =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | indInfo cv caps =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | ctorInfo cv x y =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | projInfo entry =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
      | none =>
        exact absurd_rec_fire hfn₁ hfn₂ hsome
          (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
    cases hzH with
    | refl _ =>
      cases H₁ with
      | const n us => exact recExit rfl rfl (fun φ' => rfl)
      | app p q => exact absurd rfl (hne₁ p q)
      | bvar i =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | fvar i n ty =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | sort u0 =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | lam n ty b m =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | forallE n ty b m =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | letE n ty v b =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | lit l =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | proj sn i s =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
    | cert _ _ hba hbb hc =>
      rw [show Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁
          = Setlec.Expr.mkAppN H₁ (cs ++ [a₁]) from
        mkAppN_append_one.symm,
        show Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂
          = Setlec.Expr.mkAppN H₂ (ds ++ [a₂]) from
        mkAppN_append_one.symm]
      exact CoreSeam.certHead H₁ H₂ (cs ++ [a₁]) (ds ++ [a₂])
        hba hbb hc (by simp [hlen]) (zip_args_append hlen hargs hza)
    | constSlack n us us' hev => exact recExit rfl rfl hev
    | sortSlack u0 v0 hev =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | fvar i n ty₁ ty₂ hty =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | app p₁ q₁ p₂ q₂ hp hq => exact absurd rfl (hne₁ p₁ q₁)
    | lam n ty₁ ty₂ b₁ b₂ m hty hb =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | forallE n ty₁ ty₂ b₁ b₂ m hty hb =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hv hb =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | proj s i e₁ e₂ he =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim

/-- **The layer-peeling lockstep** (the ratified carrier): a zipped
pair's whnfCore runs either land zipped — the invariants free from
the landed preservers, since outputs are whnfCore outputs — or
exit at a liftable seam re-based by connecting runs and reduction
traces, so the top-level caller can loop-align.  Strong induction
on the pair's core-run fuel sum; subjects peeled one app-layer at
a time, never reassociated. -/
theorem coreLock {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q) :
    ∀ (N : Nat) {g₁ g₂ fc d : Nat} {u v u' v' : Expr},
      g₁ + g₂ ≤ N →
      CertZip μ env fc d u v →
      SubjInv d u → SubjInv d v →
      PairedLeaves u v → Q d u v →
      whnfCore μ env g₁ d u = .ok u' →
      whnfCore μ env g₂ d v = .ok v' →
      (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧ SubjInv d v' ∧
        PairedLeaves u' v' ∧ Q d u' v') ∨
      (∃ w₁ w₂ c₁ c₂, c₁ ≤ g₁ ∧ c₂ ≤ g₂ ∧
        whnfCore μ env c₁ d w₁ = .ok u' ∧
        whnfCore μ env c₂ d w₂ = .ok v' ∧
        Contracts μ env d u w₁ ∧ Contracts μ env d v w₂ ∧
        CoreSeam μ env fc d w₁ w₂) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IH =>
  intro g₁ g₂ fc d u v u' v' hN hz hIu hIv hP hQ h₁ h₂
  have hIu' : SubjInv d u' := hIC h₁ hIu
  have hIv' : SubjInv d v' := hIC h₂ hIv
  have hP' : PairedLeaves u' v' := ((hLC h₂ (hLC h₁ hP).symm)).symm
  have hQ' : Q d u' v' := hQs (hQC h₂ (hQs (hQC h₁ hQ)))
  cases hz with
  | refl _ =>
    have hdet : u' = v' := by
      have ha := hm.2.2.1 (Nat.le_max_left g₁ g₂) h₁
      have hb := hm.2.2.1 (Nat.le_max_right g₁ g₂) h₂
      rw [ha] at hb
      exact Except.ok.inj hb
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hdet]
    exact .refl v'
  | cert _ _ hba hbb hc =>
    exact .inr ⟨u, v, g₁, g₂, Nat.le_refl _, Nat.le_refl _,
      h₁, h₂, .refl u, .refl v,
      CoreSeam.certHead u v [] [] hba hbb hc rfl
        (fun i hi _ => absurd hi (Nat.not_lt_zero i))⟩
  | sortSlack u₀ v₀ hev =>
    have hu : u' = .sort u₀ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .sort v₀ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .sortSlack u₀ v₀ hev
  | constSlack n us us' hev =>
    have hu : u' = .const n us := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .const n us' := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .constSlack n us us' hev
  | fvar i n ty₁ ty₂ hty =>
    have hu : u' = .fvar i n ty₁ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .fvar i n ty₂ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .fvar i n ty₁ ty₂ hty
  | lam n ty₁ ty₂ b₁ b₂ m hty hbody =>
    have hu : u' = .lam n ty₁ b₁ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .lam n ty₂ b₂ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .lam n ty₁ ty₂ b₁ b₂ m hty hbody
  | forallE n ty₁ ty₂ b₁ b₂ m hty hbody =>
    have hu : u' = .forallE n ty₁ b₁ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .forallE n ty₂ b₂ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .forallE n ty₁ ty₂ b₁ b₂ m hty hbody
  | proj s i e₁ e₂ he =>
    exact .inr ⟨.proj s i e₁, .proj s i e₂, g₁, g₂,
      Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
      CoreSeam.projHead s i e₁ e₂ [] [] he rfl
        (fun j hj _ => absurd hj (Nat.not_lt_zero j))⟩
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody =>
    cases g₁ with
    | zero => rw [Setlec.whnfCore_zero] at h₁; exact nomatch h₁
    | succ gp =>
    cases g₂ with
    | zero => rw [Setlec.whnfCore_zero] at h₂; exact nomatch h₂
    | succ gr =>
    rw [whnfCore_letE_step] at h₁ h₂
    have tr₁ : Contracts μ env d (.letE n ty₁ v₁ b₁)
        (b₁.instantiate1 v₁) :=
      Contracts.zeta n ty₁ v₁ b₁ [] (.refl _)
    have tr₂ : Contracts μ env d (.letE n ty₂ v₂ b₂)
        (b₂.instantiate1 v₂) :=
      Contracts.zeta n ty₂ v₂ b₂ [] (.refl _)
    have hzc : CertZip μ env fc d (b₁.instantiate1 v₁)
        (b₂.instantiate1 v₂) := certZip_subst hval hbody 0
    have hIc₁ : SubjInv d (b₁.instantiate1 v₁) :=
      tr₁.subjInv hIC hLS hIu
    have hIc₂ : SubjInv d (b₂.instantiate1 v₂) :=
      tr₂.subjInv hIC hLS hIv
    have hPc : PairedLeaves (b₁.instantiate1 v₁)
        (b₂.instantiate1 v₂) := Contracts.pairing hLS tr₁ tr₂ hP
    have hQc : Q d (b₁.instantiate1 v₁) (b₂.instantiate1 v₂) :=
      hQs (tr₂.q_transport hQB hQZ hQH
        (hQs (tr₁.q_transport hQB hQZ hQH hQ)))
    rcases IH (gp + gr) (by omega) (Nat.le_refl _) hzc hIc₁ hIc₂
        hPc hQc h₁ h₂ with hpack |
      ⟨w₁, w₂, c₁, c₂, hb₁, hb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
    · exact .inl ⟨hpack.1, hIu', hIv', hP', hQ'⟩
    · exact .inr ⟨w₁, w₂, c₁, c₂, Nat.le_succ_of_le hb₁,
        Nat.le_succ_of_le hb₂, hr₁, hr₂,
        Contracts.zeta n ty₁ v₁ b₁ [] ht₁,
        Contracts.zeta n ty₂ v₂ b₂ [] ht₂, hsm⟩
  | app f₁ a₁ f₂ a₂ hzf hza =>
    cases g₁ with
    | zero => rw [Setlec.whnfCore_zero] at h₁; exact nomatch h₁
    | succ gp =>
    cases g₂ with
    | zero => rw [Setlec.whnfCore_zero] at h₂; exact nomatch h₂
    | succ gr =>
    obtain ⟨F₁, hh₁, legs₁⟩ := whnfCore_app_decompose h₁
    obtain ⟨F₂, hh₂, legs₂⟩ := whnfCore_app_decompose h₂
    obtain ⟨hIf₁, hIa₁⟩ := subjInv_app hIu
    obtain ⟨hIf₂, hIa₂⟩ := subjInv_app hIv
    have hPf : PairedLeaves f₁ f₂ := pairedLeaves_mono
      mem_fvarLeaves_app_left mem_fvarLeaves_app_left hP
    have hQf : Q d f₁ f₂ := hQA hQ
    rcases IH (gp + gr) (by omega) (Nat.le_refl _) hzf hIf₁ hIf₂
        hPf hQf hh₁ hh₂ with
      ⟨hzF, hIF₁, hIF₂, hPF, hQF⟩ |
      ⟨w₁h, w₂h, c₁, c₂, hb₁, hb₂, hw₁, hw₂, ht₁, ht₂, hsm⟩
    · -- pack: the legs matrix
      -- the uniform cert-head exit (any legs)
      have certExit : whnfCore μ env gp d F₁ = .ok F₁ →
          whnfCore μ env gr d F₂ = .ok F₂ →
          F₁.looseBVarsBounded 0 = true →
          F₂.looseBVarsBounded 0 = true →
          isDefEqCore μ env fc d F₁ F₂ = .ok true →
          (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧ SubjInv d v' ∧
            PairedLeaves u' v' ∧ Q d u' v') ∨
          (∃ w₁ w₂ c₁ c₂, c₁ ≤ gp + 1 ∧ c₂ ≤ gr + 1 ∧
            whnfCore μ env c₁ d w₁ = .ok u' ∧
            whnfCore μ env c₂ d w₂ = .ok v' ∧
            Contracts μ env d (.app f₁ a₁) w₁ ∧
            Contracts μ env d (.app f₂ a₂) w₂ ∧
            CoreSeam μ env fc d w₁ w₂) := by
        intro hS₁ hS₂ hba hbb hc
        exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
          max gp gp + 1, max gr gr + 1, (by omega), (by omega),
          whnfCore_app_assemble hm hS₁ legs₁,
          whnfCore_app_assemble hm hS₂ legs₂,
          Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
          Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
          CoreSeam.certHead F₁ F₂ [a₁] [a₂] hba hbb hc rfl
            (fun i hi₁ _ => by
              have h0 : i = 0 := by
                simp only [List.length_cons, List.length_nil] at hi₁
                omega
              subst h0
              exact hza)⟩
      rcases legs₁ with
        ⟨n₁, ty₁, b₁, m₁, ta₁, rfl, hinf₁, hdq₁, hrun₁⟩ |
        ⟨n₁, ty₁, b₁, m₁, ta₁, rfl, hinf₁, hdq₁, rfl⟩ |
        ⟨hnl₁, hio₁⟩
      · -- β fired on the left
        rcases legs₂ with
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, hrun₂⟩ |
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, rfl⟩ |
          ⟨hnl₂, hio₂⟩
        · -- both fired: recurse on the contracta
          have betaRec : CertZip μ env fc d b₁ b₂ →
              (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧
                SubjInv d v' ∧ PairedLeaves u' v' ∧ Q d u' v') ∨
              (∃ w₁ w₂ c₁ c₂, c₁ ≤ gp + 1 ∧ c₂ ≤ gr + 1 ∧
                whnfCore μ env c₁ d w₁ = .ok u' ∧
                whnfCore μ env c₂ d w₂ = .ok v' ∧
                Contracts μ env d (.app f₁ a₁) w₁ ∧
                Contracts μ env d (.app f₂ a₂) w₂ ∧
                CoreSeam μ env fc d w₁ w₂) := by
            intro hbody
            have hzc : CertZip μ env fc d (b₁.instantiate1 a₁)
                (b₂.instantiate1 a₂) := certZip_subst hza hbody 0
            have tr₁ : Contracts μ env d (.app f₁ a₁)
                (b₁.instantiate1 a₁) :=
              Contracts.head f₁ (.lam n₁ ty₁ b₁ m₁) [a₁] gp hh₁
                (Contracts.beta n₁ ty₁ b₁ a₁ ta₁ m₁ [] gp hinf₁
                  hdq₁ (.refl _))
            have tr₂ : Contracts μ env d (.app f₂ a₂)
                (b₂.instantiate1 a₂) :=
              Contracts.head f₂ (.lam n₂ ty₂ b₂ m₂) [a₂] gr hh₂
                (Contracts.beta n₂ ty₂ b₂ a₂ ta₂ m₂ [] gr hinf₂
                  hdq₂ (.refl _))
            have hIc₁ : SubjInv d (b₁.instantiate1 a₁) :=
              tr₁.subjInv hIC hLS hIu
            have hIc₂ : SubjInv d (b₂.instantiate1 a₂) :=
              tr₂.subjInv hIC hLS hIv
            have hPc : PairedLeaves (b₁.instantiate1 a₁)
                (b₂.instantiate1 a₂) :=
              Contracts.pairing hLS tr₁ tr₂ hP
            have hQc : Q d (b₁.instantiate1 a₁)
                (b₂.instantiate1 a₂) :=
              hQs (tr₂.q_transport hQB hQZ hQH
                (hQs (tr₁.q_transport hQB hQZ hQH hQ)))
            rcases IH (gp + gr) (by omega) (Nat.le_refl _) hzc
                hIc₁ hIc₂ hPc hQc hrun₁ hrun₂ with hpack |
              ⟨w₁, w₂, c₁, c₂, hb₁, hb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
            · exact .inl ⟨hpack.1, hIu', hIv', hP', hQ'⟩
            · exact .inr ⟨w₁, w₂, c₁, c₂, Nat.le_succ_of_le hb₁,
                Nat.le_succ_of_le hb₂, hr₁, hr₂,
                Contracts.head f₁ (.lam n₁ ty₁ b₁ m₁) [a₁] gp hh₁
                  (Contracts.beta n₁ ty₁ b₁ a₁ ta₁ m₁ [] gp hinf₁
                    hdq₁ ht₁),
                Contracts.head f₂ (.lam n₂ ty₂ b₂ m₂) [a₂] gr hh₂
                  (Contracts.beta n₂ ty₂ b₂ a₂ ta₂ m₂ [] gr hinf₂
                    hdq₂ ht₂),
                hsm⟩
          cases hzF with
          | refl _ => exact betaRec (.refl b₁)
          | cert _ _ hba hbb hc =>
            exact certExit (whnfCore_lam_run (whnfCore_pos hh₁))
              (whnfCore_lam_run (whnfCore_pos hh₂)) hba hbb hc
          | lam _ _ _ _ _ _ hty hbody => exact betaRec hbody
        · -- right side stuck at a failed β-cert: dead on the right
          exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
            Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
            CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
              (.app (.lam n₂ ty₂ b₂ m₂) a₂) (gr + 1)
              (fun g hg => hm.2.2.1 hg h₂)
              (fun p q h => nomatch h)
              (fun _ _ _ _ h => nomatch h)
              (fun _ h => nomatch h)⟩
        · -- left λ against a right iota package: cert node forced
          cases hzF with
          | refl _ => exact absurd rfl (hnl₂ n₁ ty₁ b₁ m₁)
          | cert _ _ hba hbb hc =>
            rcases hio₂ with ⟨e₂'', hio₂s, hrun₂'⟩ | ⟨hio₂n, rfl⟩
            · obtain ⟨n2, us2, hhd₂⟩ := iotaRec_some_head hio₂s
              exact certExit (whnfCore_lam_run (whnfCore_pos hh₁))
                (whnfCore_reidem_const hm hh₂ hhd₂) hba hbb hc
            · by_cases hc2 : ∃ n' us',
                  F₂.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n2, us2, hhd₂⟩ := hc2
                exact certExit (whnfCore_lam_run (whnfCore_pos hh₁))
                  (whnfCore_reidem_const hm hh₂ hhd₂) hba hbb hc
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₂ a₂) (gr + 1)
                    (fun g hg => hm.2.2.1 hg h₂)
                    (fun p q hh => hc2 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
          | lam _ _ ty₂' _ b₂' _ hty hbody =>
            exact absurd rfl (hnl₂ n₁ ty₂' b₂' m₁)
      · -- left side stuck at a failed β-cert: dead on the left
        exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
          Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
          CoreSeam.deadL (.app f₁ a₁) (.app f₂ a₂)
            (.app (.lam n₁ ty₁ b₁ m₁) a₁) (gp + 1)
            (fun g hg => hm.2.2.1 hg h₁)
            (fun p q h => nomatch h)
            (fun _ _ _ _ h => nomatch h)
            (fun _ h => nomatch h)⟩
      · -- left iota package
        rcases legs₂ with
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, hrun₂⟩ |
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, rfl⟩ |
          ⟨hnl₂, hio₂⟩
        · -- right λ against a left iota package: cert node forced
          cases hzF with
          | refl _ => exact absurd rfl (hnl₁ n₂ ty₂ b₂ m₂)
          | cert _ _ hba hbb hc =>
            rcases hio₁ with ⟨e₁'', hio₁s, hrun₁'⟩ | ⟨hio₁n, rfl⟩
            · obtain ⟨n1, us1, hhd₁⟩ := iotaRec_some_head hio₁s
              exact certExit (whnfCore_reidem_const hm hh₁ hhd₁)
                (whnfCore_lam_run (whnfCore_pos hh₂)) hba hbb hc
            · by_cases hc1 : ∃ n' us',
                  F₁.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n1, us1, hhd₁⟩ := hc1
                exact certExit (whnfCore_reidem_const hm hh₁ hhd₁)
                  (whnfCore_lam_run (whnfCore_pos hh₂)) hba hbb hc
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadL (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₁ a₁) (gp + 1)
                    (fun g hg => hm.2.2.1 hg h₁)
                    (fun p q hh => hc1 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
          | lam _ ty₁' _ b₁' _ _ hty hbody =>
            exact absurd rfl (hnl₁ n₂ ty₁' b₁' m₂)
        · -- right side stuck at a failed β-cert: dead on the right
          exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
            Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
            CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
              (.app (.lam n₂ ty₂ b₂ m₂) a₂) (gr + 1)
              (fun g hg => hm.2.2.1 hg h₂)
              (fun p q h => nomatch h)
              (fun _ _ _ _ h => nomatch h)
              (fun _ h => nomatch h)⟩
        · -- both iota packages
          rcases hio₁ with ⟨e₁'', hio₁s, hrun₁'⟩ | ⟨hio₁n, rfl⟩
          · obtain ⟨n1, us1, hhd₁⟩ := iotaRec_some_head hio₁s
            have hS₁ : whnfCore μ env gp d F₁ = .ok F₁ :=
              whnfCore_reidem_const hm hh₁ hhd₁
            rcases hio₂ with ⟨e₂'', hio₂s, hrun₂'⟩ | ⟨hio₂n, rfl⟩
            · obtain ⟨n2, us2, hhd₂⟩ := iotaRec_some_head hio₂s
              exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
                max gp gp + 1, max gr gr + 1,
                (by omega), (by omega),
                whnfCore_app_assemble hm hS₁
                  (.inr (.inr ⟨hnl₁, .inl ⟨e₁'', hio₁s, hrun₁'⟩⟩)),
                whnfCore_app_assemble hm
                  (whnfCore_reidem_const hm hh₂ hhd₂)
                  (.inr (.inr ⟨hnl₂, .inl ⟨e₂'', hio₂s, hrun₂'⟩⟩)),
                Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
                Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
                zip_stuck_spine_exit (g₁' := gp) (g₂' := gr)
                  hzF hza (.inl ⟨e₁'', hio₁s⟩)⟩
            · by_cases hc2 : ∃ n' us',
                  F₂.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n2, us2, hhd₂⟩ := hc2
                exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
                  max gp gp + 1, max gr gr + 1,
                  (by omega), (by omega),
                  whnfCore_app_assemble hm hS₁
                    (.inr (.inr ⟨hnl₁, .inl ⟨e₁'', hio₁s, hrun₁'⟩⟩)),
                  whnfCore_app_assemble hm
                    (whnfCore_reidem_const hm hh₂ hhd₂)
                    (.inr (.inr ⟨hnl₂, .inr ⟨hio₂n, rfl⟩⟩)),
                  Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
                  Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
                  zip_stuck_spine_exit (g₁' := gp) (g₂' := gr)
                    hzF hza (.inl ⟨e₁'', hio₁s⟩)⟩
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₂ a₂) (gr + 1)
                    (fun g hg => hm.2.2.1 hg h₂)
                    (fun p q hh => hc2 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
          · rcases hio₂ with ⟨e₂'', hio₂s, hrun₂'⟩ | ⟨hio₂n, rfl⟩
            · obtain ⟨n2, us2, hhd₂⟩ := iotaRec_some_head hio₂s
              by_cases hc1 : ∃ n' us',
                  F₁.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n1, us1, hhd₁⟩ := hc1
                exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
                  max gp gp + 1, max gr gr + 1,
                  (by omega), (by omega),
                  whnfCore_app_assemble hm
                    (whnfCore_reidem_const hm hh₁ hhd₁)
                    (.inr (.inr ⟨hnl₁, .inr ⟨hio₁n, rfl⟩⟩)),
                  whnfCore_app_assemble hm
                    (whnfCore_reidem_const hm hh₂ hhd₂)
                    (.inr (.inr ⟨hnl₂, .inl ⟨e₂'', hio₂s, hrun₂'⟩⟩)),
                  Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
                  Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
                  zip_stuck_spine_exit (g₁' := gp) (g₂' := gr)
                    hzF hza (.inr ⟨e₂'', hio₂s⟩)⟩
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadL (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₁ a₁) (gp + 1)
                    (fun g hg => hm.2.2.1 hg h₁)
                    (fun p q hh => hc1 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
            · -- both inert: the pair stays zipped
              exact .inl ⟨.app F₁ a₁ F₂ a₂ hzF hza,
                hIu', hIv', hP', hQ'⟩
    · -- seam from the heads: lift it through the layer
      exact .inr ⟨.app w₁h a₁, .app w₂h a₂,
        max c₁ gp + 1, max c₂ gr + 1, (by omega), (by omega),
        whnfCore_app_assemble hm hw₁ legs₁,
        whnfCore_app_assemble hm hw₂ legs₂,
        ht₁.app_lift, ht₂.app_lift,
        coreSeam_lift_app hza hsm⟩

/-! ### The loop-level dispatch riding coreLock -/

/-- A spine head's non-const fact spreads over the spine. -/
theorem mkAppN_fn_ne_const {H : Expr} {cs : List Expr}
    (h : ∀ p q, H.getAppFn ≠ .const p q) :
    ∀ p q, (Setlec.Expr.mkAppN H cs).getAppFn ≠ .const p q := by
  intro p q hh
  rw [Setlec.Expr.getAppFn_mkAppN] at hh
  exact h p q hh

/-- Shape disequalities give the head fact (non-app subjects are
their own spine heads). -/
theorem not_const_getAppFn_of_shape {e : Expr}
    (h : ∀ p q, e ≠ .app p q) (h2 : ∀ p q, e ≠ .const p q) :
    ∀ p q, e.getAppFn ≠ .const p q := by
  intro p q hh
  rw [getAppFn_of_not_app h] at hh
  exact h2 p q hh

/-- A non-empty spine is an application, never a sort. -/
theorem mkAppN_cons_ne_sort {H a : Expr} {as : List Expr} :
    ∀ ℓ, Setlec.Expr.mkAppN H (a :: as) ≠ .sort ℓ := by
  intro ℓ h
  obtain ⟨p, q, hpq⟩ := mkAppN_cons_app (F := H) (a := a) (as := as)
  rw [hpq] at h
  exact nomatch h

/-- A spine over a non-sort head is never a sort. -/
theorem mkAppN_ne_sort {H : Expr} (hH : ∀ ℓ, H ≠ .sort ℓ) :
    ∀ {cs : List Expr} (ℓ : Level),
      Setlec.Expr.mkAppN H cs ≠ .sort ℓ := by
  intro cs
  cases cs with
  | nil => exact hH
  | cons a as => exact fun ℓ => mkAppN_cons_ne_sort ℓ

/-- **The dead exit**: a non-const-headed, non-sort whnfCore output
refutes its own sort-loop — the nat leg by `NatStepNoSort`, the δ
leg by the head shape, the stop leg by the sort equation. -/
theorem loop_dead_exit {μ : CheckMode} {env : Env}
    (hN : NatStepNoSort μ env) {ga la d : Nat}
    {k : Expr → Setlec.CheckM Expr} {X e₁ : Expr} {ℓa : Level}
    {C : Prop}
    (hwca : whnfCore μ env ga d X = .ok e₁)
    (ha : Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la X
      = .ok (.sort ℓa))
    (tri :
      (∃ e₂, Setlec.reduceNat (Setlec.pureFns μ env ga) env d e₁
          = .ok (some e₂) ∧ k e₂ = .ok (.sort ℓa)) ∨
      (Setlec.reduceNat (Setlec.pureFns μ env ga) env d e₁
          = .ok none ∧
        ∃ e₂, Setlec.unfoldDefinition env e₁ = some e₂ ∧
          k e₂ = .ok (.sort ℓa)) ∨
      (Setlec.reduceNat (Setlec.pureFns μ env ga) env d e₁
          = .ok none ∧
        Setlec.unfoldDefinition env e₁ = none ∧
        Expr.sort ℓa = e₁))
    (hnc : ∀ p q, e₁.getAppFn ≠ .const p q)
    (hns : ∀ ℓ, e₁ ≠ .sort ℓ) : C := by
  exfalso
  rcases tri with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ | ⟨-, -, hstop⟩
  · exact hN hwca hrx ha
  · rw [unfoldDefinition_none_of_fn_not_const hnc] at hud
    exact nomatch hud
  · exact hns ℓa hstop.symm

/-- **The head dispatch**: a zipped pair with sort-loops agrees —
one loop step decomposed per side, `coreLock` on the core runs, the
pack classified by the spine view (Θ at the first cert layer, the
const-head case at const heads, dead exits elsewhere), the seams
converted by the routed loop-level cases with re-based loop runs
(assembled from the seam's connecting runs at the premise knot
fuels — the coreLock fuel bounds).  Both the λ- and letE-head
cases collapse onto this. -/
theorem zipHeadDispatch {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hIo : ZipIotaCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ∀ {fc d ga la gb lb : Nat} {X₁ X₂ : Expr} {ℓa ℓb : Level},
      ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
      CertZip μ env fc d X₁ X₂ →
      SubjInv d X₁ → SubjInv d X₂ →
      PairedLeaves X₁ X₂ → Q d X₁ X₂ →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la X₁
        = .ok (.sort ℓa) →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb X₂
        = .ok (.sort ℓb) →
      ℓa.eval φ = ℓb.eval φ := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb X₁ X₂ ℓa ℓb below hz hI₁ hI₂ hp hQ ha hb
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨e₁, hwca, triA⟩ := whnfStep_decompose haD
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨e₂, hwcb, triB⟩ := whnfStep_decompose hbD
  have hwca' : whnfCore μ env ga d X₁ = .ok e₁ := hwca
  have hwcb' : whnfCore μ env gb d X₂ = .ok e₂ := hwcb
  have stepA : ∀ {W : Expr},
      whnfCore μ env ga d W = .ok e₁ →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d (la' + 1) W
        = .ok (.sort ℓa) := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triA with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  have stepB : ∀ {W : Expr},
      whnfCore μ env gb d W = .ok e₂ →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d (lb' + 1) W
        = .ok (.sort ℓb) := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triB with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  have belowFc : ZipBelowFc μ env φ Q fc :=
    fun hlt hz' hIs hIt hp' hq' hla hlb =>
      below (Or.inl hlt) hz' hIs hIt hp' hq' hla hlb
  rcases @coreLock μ env Q hm hIC hLC hQC hQB hQZ hQH hLS
      (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
      (ga + gb) ga gb fc d X₁ X₂ e₁ e₂
      (Nat.le_refl _) hz hI₁ hI₂ hp hQ hwca' hwcb' with
    ⟨hzE, hIe₁, hIe₂, hpE, hQE⟩ |
    ⟨w₁, w₂, c₁, c₂, hcb₁, hcb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
  · -- the pack: classify the zipped outputs by the spine view
    have hcoreA : whnfCore μ env ga d e₁ = .ok e₁ := by
      rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ | ⟨-, -, hstop⟩
      · exact (hN hwca' hrx ha).elim
      · obtain ⟨n0, us0, hhd⟩ := unfoldDefinition_some_head hud
        exact whnfCore_reidem_const hm hwca' hhd
      · rw [← hstop]
        exact whnfCore_sort_run (whnfCore_pos hwca')
    have hcoreB : whnfCore μ env gb d e₂ = .ok e₂ := by
      rcases triB with ⟨y, hry, -⟩ | ⟨-, y, hud, -⟩ | ⟨-, -, hstop⟩
      · exact (hN hwcb' hry hb).elim
      · obtain ⟨n0, us0, hhd⟩ := unfoldDefinition_some_head hud
        exact whnfCore_reidem_const hm hwcb' hhd
      · rw [← hstop]
        exact whnfCore_sort_run (whnfCore_pos hwcb')
    have ha' := stepA hcoreA
    have hb' := stepB hcoreB
    obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
      certZip_app_view hzE
    rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
    · exact hΘ belowFc hba hbb hc hlenv hargsv hIe₁ hIe₂ hpE hQE
        ha' hb'
    · cases hzH with
      | refl _ =>
        cases H₁ with
        | const n us =>
          exact hConst below (fun φ' => rfl) hlenv hargsv
            hIe₁ hIe₂ hpE hQE ha' hb'
        | sort u₀ =>
          cases cs with
          | cons ch ct =>
            exact loop_dead_exit hN hwca' ha triA
              (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
              (fun ℓ => mkAppN_cons_ne_sort ℓ)
          | nil =>
            cases ds with
            | cons dh dt => exact nomatch hlenv
            | nil =>
              rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ |
                ⟨-, -, hstopA⟩
              · exact (hN hwca' hrx ha).elim
              · have hnone : Setlec.unfoldDefinition env
                    (Setlec.Expr.mkAppN (Expr.sort u₀) []) = none :=
                  unfoldDefinition_none_of_fn_not_const
                    (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
                exact nomatch (hnone.symm.trans hud)
              · rcases triB with ⟨y, hry, -⟩ | ⟨-, y, hud', -⟩ |
                  ⟨-, -, hstopB⟩
                · exact (hN hwcb' hry hb).elim
                · have hnone : Setlec.unfoldDefinition env
                      (Setlec.Expr.mkAppN (Expr.sort u₀) []) = none :=
                    unfoldDefinition_none_of_fn_not_const
                      (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
                  exact nomatch (hnone.symm.trans hud')
                · have hA : ℓa = u₀ :=
                    Expr.sort.inj (show Expr.sort ℓa = Expr.sort u₀
                      from hstopA)
                  have hB : ℓb = u₀ :=
                    Expr.sort.inj (show Expr.sort ℓb = Expr.sort u₀
                      from hstopB)
                  rw [hA, hB]
        | app p q => exact absurd rfl (hne₁ p q)
        | bvar i =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.bvar i) (fun _ h2 => nomatch h2) ℓ0 hh)
        | fvar i n ty =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.fvar i n ty) (fun _ h2 => nomatch h2) ℓ0 hh)
        | lam n ty b m =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.lam n ty b m) (fun _ h2 => nomatch h2) ℓ0 hh)
        | forallE n ty b m =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.forallE n ty b m) (fun _ h2 => nomatch h2) ℓ0 hh)
        | letE n ty v b =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.letE n ty v b) (fun _ h2 => nomatch h2) ℓ0 hh)
        | lit l =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.lit l) (fun _ h2 => nomatch h2) ℓ0 hh)
        | proj sn i pe =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.proj sn i pe) (fun _ h2 => nomatch h2) ℓ0 hh)
      | cert _ _ hba hbb hc =>
        exact hΘ belowFc hba hbb hc hlenv hargsv hIe₁ hIe₂ hpE hQE
          ha' hb'
      | constSlack n us us' hev =>
        exact hConst below hev hlenv hargsv hIe₁ hIe₂ hpE hQE
          ha' hb'
      | sortSlack u₀ v₀ hev =>
        cases cs with
        | cons ch ct =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (fun ℓ => mkAppN_cons_ne_sort ℓ)
        | nil =>
          cases ds with
          | cons dh dt => exact nomatch hlenv
          | nil =>
            rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ |
              ⟨-, -, hstopA⟩
            · exact (hN hwca' hrx ha).elim
            · have hnone : Setlec.unfoldDefinition env
                  (Setlec.Expr.mkAppN (Expr.sort u₀) []) = none :=
                unfoldDefinition_none_of_fn_not_const
                  (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
              exact nomatch (hnone.symm.trans hud)
            · rcases triB with ⟨y, hry, -⟩ | ⟨-, y, hud', -⟩ |
                ⟨-, -, hstopB⟩
              · exact (hN hwcb' hry hb).elim
              · have hnone : Setlec.unfoldDefinition env
                    (Setlec.Expr.mkAppN (Expr.sort v₀) []) = none :=
                  unfoldDefinition_none_of_fn_not_const
                    (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
                exact nomatch (hnone.symm.trans hud')
              · have hA : ℓa = u₀ :=
                  Expr.sort.inj (show Expr.sort ℓa = Expr.sort u₀
                    from hstopA)
                have hB : ℓb = v₀ :=
                  Expr.sort.inj (show Expr.sort ℓb = Expr.sort v₀
                    from hstopB)
                rw [hA, hB]
                exact hev φ
      | fvar i n ty₁' ty₂' hty =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.fvar i n ty₁') (fun _ h2 => nomatch h2) ℓ0 hh)
      | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
      | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.lam n ty₁' b₁' m) (fun _ h2 => nomatch h2) ℓ0 hh)
      | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.forallE n ty₁' b₁' m) (fun _ h2 => nomatch h2) ℓ0 hh)
      | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.letE n ty₁' v₁' b₁') (fun _ h2 => nomatch h2) ℓ0 hh)
      | proj sn i pe₁ pe₂ he =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.proj sn i pe₁) (fun _ h2 => nomatch h2) ℓ0 hh)
  · -- the seam: transport, re-base the loops, convert
    have hIw₁ : SubjInv d w₁ := ht₁.subjInv hIC hLS hI₁
    have hIw₂ : SubjInv d w₂ := ht₂.subjInv hIC hLS hI₂
    have hpw : PairedLeaves w₁ w₂ :=
      Contracts.pairing hLS ht₁ ht₂ hp
    have hQw : Q d w₁ w₂ :=
      hQs (ht₂.q_transport hQB hQZ hQH
        (hQs (ht₁.q_transport hQB hQZ hQH hQ)))
    have hw₁ga : whnfCore μ env ga d w₁ = .ok e₁ :=
      hm.2.2.1 hcb₁ hr₁
    have hw₂gb : whnfCore μ env gb d w₂ = .ok e₂ :=
      hm.2.2.1 hcb₂ hr₂
    have haw := stepA hw₁ga
    have hbw := stepB hw₂gb
    cases hsm with
    | certHead F₁ F₂ as bs hba hbb hc hlen hargs =>
      exact hΘ belowFc hba hbb hc hlen hargs hIw₁ hIw₂ hpw hQw
        haw hbw
    | recHead n cv mI rP rules us us' as bs hf hev hlen hargs =>
      exact @hIo fc d ga (la' + 1) gb (lb' + 1) mI rP n us us'
        cv rules as bs ℓa ℓb hf
        (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
            hmes hz' hIs' hIt' hp' hq' hla hlb =>
          below hmes hz' hIs' hIt' hp' hq' hla hlb)
        hev hlen hargs hIw₁ hIw₂ hpw hQw haw hbw
    | projHead sn i pe₁ pe₂ as bs he hlen hargs =>
      exact @hProj fc d ga (la' + 1) gb (lb' + 1) i sn pe₁ pe₂
        as bs ℓa ℓb
        (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
            hmes hz' hIs' hIt' hp' hq' hla hlb =>
          below hmes hz' hIs' hIt' hp' hq' hla hlb)
        he hlen hargs hIw₁ hIw₂ hpw hQw haw hbw
    | deadL _ _ u'd bnd hrun hnc hnl hns =>
      have h1 : whnfCore μ env (max bnd ga) d w₁ = .ok u'd :=
        hrun (max bnd ga) (Nat.le_max_left _ _)
      have h2 : whnfCore μ env (max bnd ga) d w₁ = .ok e₁ :=
        hm.2.2.1 (Nat.le_max_right _ _) hw₁ga
      rw [h1] at h2
      obtain rfl := Except.ok.inj h2
      exact loop_dead_exit hN hwca' ha triA hnc hns
    | deadR _ _ v'd bnd hrun hnc hnl hns =>
      have h1 : whnfCore μ env (max bnd gb) d w₂ = .ok v'd :=
        hrun (max bnd gb) (Nat.le_max_left _ _)
      have h2 : whnfCore μ env (max bnd gb) d w₂ = .ok e₂ :=
        hm.2.2.1 (Nat.le_max_right _ _) hw₂gb
      rw [h1] at h2
      obtain rfl := Except.ok.inj h2
      exact loop_dead_exit hN hwcb' hb triB hnc hns

/-! ### The loop-level lockstep tier (loopLock's statement kit)

The whnf-loop lockstep the proj/iota discharges ride (the mapped
arc): the carrier `LoopReaches` (loop steps compose the nine landed
preservers — no new species), the out-shapes (`LoopLockOut`:
pack ∨ re-based seam ∨ nat split — the nat tier is wholesale
Θ-family, deferred as raw data with a PROGRESS MARKER so the
disjunct cannot be satisfied vacuously), the recursion bar
`LoopBelow` (knot-sum then loop-budget-sum; `fc` fixed — the loop
tier never descends cert fuel), and the two routed step Props
(`LoopIotaStep`/`LoopProjStep`, each discharged at its own seal —
coreLock's recHead/projHead seams are UNPACKED through them, since
no sort premise exists at scrutinee/major level). -/

/-- `Q` survives a projection fire (scrutinee whnf'd, field
extracted, spine kept; at `FrameQ` this is the model's projection
law on the whnf'd constructor form — the models-public-interface
theorems — composed with the claims' whnf preservation). -/
def QPreserveProjFireF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d i : Nat} {sn : Name} {e w e₃ h' c : Expr}
    {entry : Setlec.ProjEntry} {us : List Level} {as : List Expr},
    whnf μ env g d e = .ok w →
    Setlec.projLitToCtorP μ env g d w = .ok e₃ →
    e₃.getAppFn = .const entry.ctor us →
    env.findProj? sn i = some entry →
    entry.native = true →
    i < entry.numFields →
    e₃.getAppArgs.length = entry.numParams + entry.numFields →
    whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h' →
    Q d (Setlec.Expr.mkAppN (.proj sn i e) as) c →
    Q d (Setlec.Expr.mkAppN h' as) c

/-- The subject package survives a projection fire (supplier: the
whnf/core preservation family, `EnvWF`-backed, own seal). -/
def InvPreserveProjFireF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g d i : Nat} {sn : Name} {e w e₃ h' : Expr}
    {entry : Setlec.ProjEntry} {us : List Level} {as : List Expr},
    whnf μ env g d e = .ok w →
    Setlec.projLitToCtorP μ env g d w = .ok e₃ →
    e₃.getAppFn = .const entry.ctor us →
    env.findProj? sn i = some entry →
    entry.native = true →
    i < entry.numFields →
    e₃.getAppArgs.length = entry.numParams + entry.numFields →
    whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h' →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e) as) →
    SubjInv d (Setlec.Expr.mkAppN h' as)

/-- Cross-pairing survives a projection fire (left slot; supplier:
the whnf/core leaf-subset family). -/
def PairedPreserveProjFireF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g d i : Nat} {sn : Name} {e w e₃ h' c : Expr}
    {entry : Setlec.ProjEntry} {us : List Level} {as : List Expr},
    whnf μ env g d e = .ok w →
    Setlec.projLitToCtorP μ env g d w = .ok e₃ →
    e₃.getAppFn = .const entry.ctor us →
    env.findProj? sn i = some entry →
    entry.native = true →
    i < entry.numFields →
    e₃.getAppArgs.length = entry.numParams + entry.numFields →
    whnfCore μ env g d
      (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
      = .ok h' →
    PairedLeaves (Setlec.Expr.mkAppN (.proj sn i e) as) c →
    PairedLeaves (Setlec.Expr.mkAppN h' as) c

/-- **The loop-level carrier**: reachability by whole-subject loop
steps (full core runs, δ, nat) and embedded contraction traces. -/
inductive LoopReaches (μ : CheckMode) (env : Env) (d : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : LoopReaches μ env d e e
  | core (g : Nat) {s s' w : Expr}
      (h : whnfCore μ env g d s = .ok s')
      (rest : LoopReaches μ env d s' w) : LoopReaches μ env d s w
  | delta {s s' w : Expr}
      (h : Setlec.unfoldDefinition env s = some s')
      (rest : LoopReaches μ env d s' w) : LoopReaches μ env d s w
  | nat (g : Nat) {s s' w : Expr}
      (h : Setlec.reduceNat (Setlec.pureFns μ env g) env d s
        = .ok (some s'))
      (rest : LoopReaches μ env d s' w) : LoopReaches μ env d s w
  | contract {s t w : Expr} (h : Contracts μ env d s t)
      (rest : LoopReaches μ env d t w) : LoopReaches μ env d s w
  | projFire (sn : Name) (i g : Nat) (e w e₃ h' : Expr)
      (entry : Setlec.ProjEntry) (us : List Level)
      (as : List Expr) {t : Expr}
      (hw : whnf μ env g d e = .ok w)
      (hlit : Setlec.projLitToCtorP μ env g d w = .ok e₃)
      (hfn : e₃.getAppFn = .const entry.ctor us)
      (hf : env.findProj? sn i = some entry)
      (hnat : entry.native = true)
      (hi : i < entry.numFields)
      (hlen : e₃.getAppArgs.length
        = entry.numParams + entry.numFields)
      (hfield : whnfCore μ env g d
        (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
        = .ok h')
      (rest : LoopReaches μ env d (Setlec.Expr.mkAppN h' as) t) :
      LoopReaches μ env d
        (Setlec.Expr.mkAppN (.proj sn i e) as) t

/-- Reachability composes. -/
theorem LoopReaches.trans {μ : CheckMode} {env : Env} {d : Nat}
    {u w x : Expr} (h₁ : LoopReaches μ env d u w)
    (h₂ : LoopReaches μ env d w x) : LoopReaches μ env d u x := by
  induction h₁ with
  | refl e => exact h₂
  | core g h rest ih => exact .core g h (ih h₂)
  | delta h rest ih => exact .delta h (ih h₂)
  | nat g h rest ih => exact .nat g h (ih h₂)
  | contract h rest ih => exact .contract h (ih h₂)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact .projFire sn i g e w e₃ h' entry us as hw hlit hfn hf
      hnat hi hlen hfield (ih h₂)

/-- Q rides the loop carrier (the nine step preservers). -/
theorem LoopReaches.q_transport {μ : CheckMode} {env : Env} {d : Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hQP : QPreserveProjFireF μ env Q)
    {u w c : Expr} (h : LoopReaches μ env d u w) :
    Q d u c → Q d w c := by
  induction h with
  | refl e => exact id
  | core g h rest ih => exact fun hq => ih (hQC h hq)
  | delta h rest ih => exact fun hq => ih (hQD h hq)
  | nat g h rest ih => exact fun hq => ih (hQN h hq)
  | contract h rest ih =>
    exact fun hq => ih (h.q_transport hQB hQZ hQH hq)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact fun hq => ih (hQP hw hlit hfn hf hnat hi hlen hfield hq)

/-- `SubjInv` rides the loop carrier. -/
theorem LoopReaches.subjInv {μ : CheckMode} {env : Env} {d : Nat}
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hLS : LeavesSubCoreF μ env)
    (hIP : InvPreserveProjFireF μ env)
    {u w : Expr} (h : LoopReaches μ env d u w)
    (hI : SubjInv d u) : SubjInv d w := by
  induction h with
  | refl e => exact hI
  | core g h rest ih => exact ih (hIC h hI)
  | delta h rest ih => exact ih (hID h hI)
  | nat g h rest ih => exact ih (hIN h hI)
  | contract h rest ih => exact ih (h.subjInv hIC hLS hI)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact ih (hIP hw hlit hfn hf hnat hi hlen hfield hI)

/-- Cross-pairing rides the carrier one side at a time (left-slot
species; the embedded contraction uses a refl other-trace). -/
theorem LoopReaches.pairing_left {μ : CheckMode} {env : Env}
    {d : Nat}
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env) (hLS : LeavesSubCoreF μ env)
    (hLP : PairedPreserveProjFireF μ env)
    {u w c : Expr} (h : LoopReaches μ env d u w) :
    PairedLeaves u c → PairedLeaves w c := by
  induction h with
  | refl e => exact id
  | core g h rest ih => exact fun hp => ih (hLC h hp)
  | delta h rest ih => exact fun hp => ih (hLD h hp)
  | nat g h rest ih => exact fun hp => ih (hLN h hp)
  | contract h rest ih =>
    exact fun hp => ih (Contracts.pairing hLS h (.refl c) hp)
  | projFire sn i g e w e₃ h' entry us as hw hlit hfn hf hnat hi
      hlen hfield rest ih =>
    exact fun hp => ih (hLP hw hlit hfn hf hnat hi hlen hfield hp)

/-- **The loop seam pack**: a `CoreSeam` at loop-reachable
subjects, with connecting loop runs at bounded knot fuels. -/
def LoopSeamOut (μ : CheckMode) (env : Env) (fc d : Nat)
    (u v u' v' : Expr) (f₁ f₂ : Nat) : Prop :=
  ∃ w₁ w₂ c₁ c₂ l₁ l₂, c₁ ≤ f₁ ∧ c₂ ≤ f₂ ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d l₁ w₁
      = .ok u' ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d l₂ w₂
      = .ok v' ∧
    LoopReaches μ env d u w₁ ∧ LoopReaches μ env d v w₂ ∧
    CoreSeam μ env fc d w₁ w₂

/-- **The nat split** (the Θ-family deferral, PROGRESS-MARKED): a
last-synced zipped pair whose next core outputs carry at least one
`reduceNat` fire — value divergence between zipped sides traces to
buried certs, so the loop tier hands the raw data to the consumers
(sort-premised tops kill the fired side by `NatStepNoSort`;
scrutinee/major consumers route through their own cert's Θ-funnel).
The `isSome` marker is what keeps this disjunct from absorbing the
whole theorem vacuously. -/
def NatSplitOut (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc d : Nat)
    (u v u' v' : Expr) (f₁ f₂ : Nat) : Prop :=
  ∃ p₁ p₂ t₁ t₂ g₁ g₂ gn₁ gn₂ o₁ o₂ c₁ c₂ l₁ l₂,
    c₁ ≤ f₁ ∧ c₂ ≤ f₂ ∧
    LoopReaches μ env d u p₁ ∧ LoopReaches μ env d v p₂ ∧
    CertZip μ env fc d t₁ t₂ ∧ SubjInv d t₁ ∧ SubjInv d t₂ ∧
    PairedLeaves t₁ t₂ ∧ Q d t₁ t₂ ∧
    whnfCore μ env g₁ d p₁ = .ok t₁ ∧
    whnfCore μ env g₂ d p₂ = .ok t₂ ∧
    Setlec.reduceNat (Setlec.pureFns μ env gn₁) env d t₁
      = .ok o₁ ∧
    Setlec.reduceNat (Setlec.pureFns μ env gn₂) env d t₂
      = .ok o₂ ∧
    (o₁.isSome = true ∨ o₂.isSome = true) ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d l₁ p₁
      = .ok u' ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d l₂ p₂
      = .ok v'

/-- **The proj split** (the second Θ-deferral channel, ratified):
both projections fire — pinning both heads to the entry's
constructor — but the whnf'd-scrutinee pack's cert layer swallows
the field position, so the fields relate only through the cert.
Everything sits at the ORIGINAL subjects (premise-reachable,
premise runs — nothing rebased, honoring both bars), progress-
marked by the DUAL FIRE data.  The Θ-arc owns the conversion. -/
def ProjSplitOut (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc d : Nat)
    (u v u' v' : Expr) (f₁ f₂ : Nat) : Prop :=
  ∃ (sn : Name) (i : Nat) (e₁ e₂ w₁ w₂ e₃₁ e₃₂ : Expr)
    (as bs : List Expr) (g₁ g₂ c₁ c₂ l₁ l₂ : Nat),
    c₁ ≤ f₁ ∧ c₂ ≤ f₂ ∧ g₁ ≤ f₁ ∧ g₂ ≤ f₂ ∧
    LoopReaches μ env d u
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) ∧
    LoopReaches μ env d v
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) ∧
    CertZip μ env fc d e₁ e₂ ∧
    as.length = bs.length ∧
    (∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
      CertZip μ env fc d as[j] bs[j]) ∧
    whnf μ env g₁ d e₁ = .ok w₁ ∧ whnf μ env g₂ d e₂ = .ok w₂ ∧
    CertZip μ env fc d w₁ w₂ ∧ SubjInv d w₁ ∧ SubjInv d w₂ ∧
    PairedLeaves w₁ w₂ ∧ Q d w₁ w₂ ∧
    Setlec.projLitToCtorP μ env g₁ d w₁ = .ok e₃₁ ∧
    Setlec.projLitToCtorP μ env g₂ d w₂ = .ok e₃₂ ∧
    (∃ us₁ entry₁, e₃₁.getAppFn = .const entry₁.ctor us₁ ∧
      env.findProj? sn i = some entry₁ ∧ entry₁.native = true) ∧
    (∃ us₂ entry₂, e₃₂.getAppFn = .const entry₂.ctor us₂ ∧
      env.findProj? sn i = some entry₂ ∧ entry₂.native = true) ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₁) env d l₁
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok u' ∧
    Setlec.whnfLoop (Setlec.pureFns μ env c₂) env d l₂
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok v'

/-- **loopLock's conclusion**: outputs zipped with the invariants,
or a re-based seam, or one of the two Θ-deferral splits. -/
def LoopLockOut (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc d : Nat)
    (u v u' v' : Expr) (f₁ f₂ : Nat) : Prop :=
  (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧ SubjInv d v' ∧
    PairedLeaves u' v' ∧ Q d u' v') ∨
  LoopSeamOut μ env fc d u v u' v' f₁ f₂ ∨
  NatSplitOut μ env Q fc d u v u' v' f₁ f₂ ∨
  ProjSplitOut μ env Q fc d u v u' v' f₁ f₂

/-- **The loop recursion bar**: knot-fuel sum strictly below, or
equal with the loop-budget sum strictly below.  `fc` is fixed —
the loop tier never descends cert fuel (Θ-funnels exit as seams). -/
def LoopBelow (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) (fc N R : Nat) : Prop :=
  ∀ {f₁ f₂ l₁ l₂ d : Nat} {u v u' v' : Expr},
    (f₁ + f₂ < N ∨ (f₁ + f₂ = N ∧ l₁ + l₂ < R)) →
    CertZip μ env fc d u v → SubjInv d u → SubjInv d v →
    PairedLeaves u v → Q d u v →
    Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁ u
      = .ok u' →
    Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂ v
      = .ok v' →
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂

/-- **Routed: the loop-level iota step** (unpacking coreLock's
recHead seams — no sort premise exists at major level, so rec-spine
pairs must actually sync: zipped majors recurse through `LoopBelow`
at knot minus one, fires match by ctor-name determinism, the K/eta
rescue rows scope their infer-lockstep lemmas leg-locally at the
discharge; divergence exits Θ-seams or the nat split).  Premises:
the shaped pair with its core runs, reachability from the loop
subjects, and the suffix loop runs. -/
def LoopIotaStep (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc N R f₁ f₂ l₁ l₂ d mI rP : Nat} {n : Name}
    {cv : Setlec.ConstantVal} {rules : List Setlec.RecRule}
    {us us' : List Level} {as bs : List Expr}
    {u v u' v' : Expr},
    LoopBelow μ env Q fc N R →
    f₁ + f₂ ≤ N → l₁ + l₂ ≤ R →
    env.find? n = some (.recInfo cv mI rP rules) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) as) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Q d (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    LoopReaches μ env d u (Setlec.Expr.mkAppN (.const n us) as) →
    LoopReaches μ env d v (Setlec.Expr.mkAppN (.const n us') bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁
      (Setlec.Expr.mkAppN (.const n us) as) = .ok u' →
    Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok v' →
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂

/-- **Routed: the loop-level proj step** (unpacking coreLock's
projHead seams: the scrutinees' whnfs run at knot minus one —
`whnf_proj_inv` pins it — so the zipped scrutinees recurse through
`LoopBelow`; fire sync by table+ctor determinism, stuck sides
rebuild, divergence exits Θ-seams or the nat split). -/
def LoopProjStep (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc N R f₁ f₂ l₁ l₂ d i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {as bs : List Expr} {u v u' v' : Expr},
    LoopBelow μ env Q fc N R →
    f₁ + f₂ ≤ N → l₁ + l₂ ≤ R →
    CertZip μ env fc d e₁ e₂ →
    as.length = bs.length →
    (∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
      CertZip μ env fc d as[j] bs[j]) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Q d (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    LoopReaches μ env d u (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    LoopReaches μ env d v (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok u' →
    Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok v' →
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂

/-- `LoopLockOut` re-bases along reachability prefixes (the pack is
output-only; the seam and split compose their traces). -/
theorem LoopLockOut.prepend {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop} {fc d : Nat}
    {u v x₁ x₂ u' v' : Expr} {f₁ f₂ : Nat}
    (r₁ : LoopReaches μ env d u x₁) (r₂ : LoopReaches μ env d v x₂)
    (h : LoopLockOut μ env Q fc d x₁ x₂ u' v' f₁ f₂) :
    LoopLockOut μ env Q fc d u v u' v' f₁ f₂ := by
  rcases h with hpack | ⟨w₁, w₂, c₁, c₂, l₁, l₂, hb₁, hb₂, hr₁, hr₂,
      ht₁, ht₂, hsm⟩ |
    ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂, o₁, o₂, c₁, c₂, l₁, l₂,
      hb₁, hb₂, hp₁, hp₂, hrest⟩ |
    ⟨sn, i, e₁, e₂, w₁, w₂, e₃₁, e₃₂, as, bs, g₁, g₂, c₁, c₂,
      l₁, l₂, hb₁, hb₂, hg₁, hg₂, hp₁, hp₂, hrest⟩
  · exact .inl hpack
  · exact .inr (.inl ⟨w₁, w₂, c₁, c₂, l₁, l₂, hb₁, hb₂, hr₁, hr₂,
      r₁.trans ht₁, r₂.trans ht₂, hsm⟩)
  · exact .inr (.inr (.inl ⟨p₁, p₂, t₁, t₂, g₁, g₂, gn₁, gn₂,
      o₁, o₂, c₁, c₂, l₁, l₂, hb₁, hb₂, r₁.trans hp₁,
      r₂.trans hp₂, hrest⟩))
  · exact .inr (.inr (.inr ⟨sn, i, e₁, e₂, w₁, w₂, e₃₁, e₃₂,
      as, bs, g₁, g₂, c₁, c₂, l₁, l₂, hb₁, hb₂, hg₁, hg₂,
      r₁.trans hp₁, r₂.trans hp₂, hrest⟩))

/-- A whnfCore output either re-cores to itself at the producing
fuel, or is dead-stuck (non-const-headed, non-λ, non-sort) — the
R-a family packaged for the loop walk's stuck sides. -/
theorem whnfCore_self_or_dead {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {f d : Nat} {p t : Expr}
    (h : whnfCore μ env f d p = .ok t) :
    whnfCore μ env f d t = .ok t ∨
    ((∀ p' q', t.getAppFn ≠ .const p' q') ∧
      (∀ n ty b m, t ≠ .lam n ty b m) ∧ (∀ ℓ, t ≠ .sort ℓ)) := by
  by_cases hc : ∃ n us, t.getAppFn = Setlec.Expr.const n us
  · obtain ⟨n, us, hhd⟩ := hc
    exact .inl (whnfCore_reidem_const hm h hhd)
  · have hpos : 1 ≤ f := whnfCore_pos h
    cases t with
    | sort ℓ => exact .inl (whnfCore_sort_run hpos)
    | lam n ty b m => exact .inl (whnfCore_lam_run hpos)
    | fvar i n ty => exact .inl (whnfCore_fvar_run hpos)
    | forallE n ty b m => exact .inl (whnfCore_forallE_run hpos)
    | lit l => exact .inl (whnfCore_lit_run hpos)
    | const n us => exact absurd ⟨n, us, rfl⟩ hc
    | bvar i =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩
    | letE n ty v b =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩
    | proj sn i pe =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩
    | app pf pa =>
      exact .inr ⟨(fun p' q' hh => hc ⟨p', q', hh⟩),
        (fun _ _ _ _ hh => nomatch hh), (fun _ hh => nomatch hh)⟩

/-- An unfolding spine's non-app head is a constant (subject-first
argument order so the head resolves before the shape lambda). -/
theorem unfold_some_head_of_spine {env : Env} {H x : Expr}
    {cs : List Expr}
    (h : Setlec.unfoldDefinition env (Setlec.Expr.mkAppN H cs)
      = some x)
    (hne : ∀ p q, H ≠ .app p q) :
    ∃ n us, H = Setlec.Expr.const n us := by
  obtain ⟨n, us, hfn⟩ := unfoldDefinition_some_head h
  rw [Setlec.Expr.getAppFn_mkAppN, getAppFn_of_not_app hne] at hfn
  exact ⟨n, us, hfn⟩

set_option maxHeartbeats 1600000 in
/-- **The whnf-loop lockstep** (the frozen statement): a zipped
pair's loop runs land zipped, or exit at a re-based seam, or split
at the nat tier.  Double strong induction (knot-fuel sum, then
loop-budget sum); per step: decompose both sides, coreLock on the
core parts, recHead/projHead seams unpacked through the routed step
Props, δ synced by name-determinism or exited at cert layers, nat
to the progress-marked split. -/
theorem loopLock {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hIC : InvPreserveCoreF μ env) (hIDl : InvPreserveDeltaF env)
    (hLC : PairedPreserveCoreF μ env)
    (hLD : PairedPreserveDeltaF env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hIo : LoopIotaStep μ env Q) (hPr : LoopProjStep μ env Q) :
    ∀ (N R : Nat) {f₁ f₂ l₁ l₂ fc d : Nat} {u v u' v' : Expr},
      f₁ + f₂ ≤ N → l₁ + l₂ ≤ R →
      CertZip μ env fc d u v →
      SubjInv d u → SubjInv d v → PairedLeaves u v → Q d u v →
      Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d l₁ u
        = .ok u' →
      Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d l₂ v
        = .ok v' →
      LoopLockOut μ env Q fc d u v u' v' f₁ f₂ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IHN =>
  intro R
  induction R using Nat.strongRecOn with
  | ind R IHR =>
  intro f₁ f₂ l₁ l₂ fc d u v u' v' hN hR hz hIu hIv hP hQ h₁ h₂
  have below : LoopBelow μ env Q fc N R := by
    intro f₁' f₂' l₁' l₂' d' u₀ v₀ u₀' v₀' hrel hz' hI₁' hI₂'
      hp' hq' ha' hb'
    rcases hrel with hlt | ⟨heq, hlt⟩
    · exact IHN (f₁' + f₂') hlt (l₁' + l₂') (Nat.le_refl _)
        (Nat.le_refl _) hz' hI₁' hI₂' hp' hq' ha' hb'
    · exact IHR (l₁' + l₂') hlt (heq ▸ Nat.le_refl _)
        (Nat.le_refl _) hz' hI₁' hI₂' hp' hq' ha' hb'
  cases l₁ with
  | zero => exact nomatch h₁
  | succ l₁' =>
  cases l₂ with
  | zero => exact nomatch h₂
  | succ l₂' =>
  have haD := h₁
  rw [whnfLoop_succ] at haD
  obtain ⟨t₁, hwc₁, triA⟩ := whnfStep_decompose haD
  have hbD := h₂
  rw [whnfLoop_succ] at hbD
  obtain ⟨t₂, hwc₂, triB⟩ := whnfStep_decompose hbD
  have hwc₁' : whnfCore μ env f₁ d u = .ok t₁ := hwc₁
  have hwc₂' : whnfCore μ env f₂ d v = .ok t₂ := hwc₂
  have stepA : ∀ {W : Expr},
      whnfCore μ env f₁ d W = .ok t₁ →
      Setlec.whnfLoop (Setlec.pureFns μ env f₁) env d (l₁' + 1) W
        = .ok u' := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triA with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  have stepB : ∀ {W : Expr},
      whnfCore μ env f₂ d W = .ok t₂ →
      Setlec.whnfLoop (Setlec.pureFns μ env f₂) env d (l₂' + 1) W
        = .ok v' := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triB with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  rcases @coreLock μ env Q hm hIC hLC hQC hQB hQZ hQH hLS
      (fun {d'} {a b} h => hQs h)
      (fun {d'} {P} {y} {Rz} {z} h => hQA h)
      (f₁ + f₂) f₁ f₂ fc d u v t₁ t₂
      (Nat.le_refl _) hz hIu hIv hP hQ hwc₁' hwc₂' with
    ⟨hzT, hIt₁, hIt₂, hPt, hQt⟩ |
    ⟨w₁, w₂, c₁, c₂, hcb₁, hcb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
  · -- pack: the tri matrix
    have natOut : ∀ (o₁ o₂ : Option Expr),
        Setlec.reduceNat (Setlec.pureFns μ env f₁) env d t₁
          = .ok o₁ →
        Setlec.reduceNat (Setlec.pureFns μ env f₂) env d t₂
          = .ok o₂ →
        (o₁.isSome = true ∨ o₂.isSome = true) →
        LoopLockOut μ env Q fc d u v u' v' f₁ f₂ :=
      fun o₁ o₂ hn₁ hn₂ hmark =>
        .inr (.inr (.inl ⟨u, v, t₁, t₂, f₁, f₂, f₁, f₂, o₁, o₂,
          f₁, f₂, l₁' + 1, l₂' + 1, Nat.le_refl _, Nat.le_refl _,
          .refl _, .refl _, hzT, hIt₁, hIt₂, hPt, hQt,
          hwc₁', hwc₂', hn₁, hn₂, hmark, h₁, h₂⟩))
    rcases triA with ⟨x₁, hrn₁, hk₁⟩ | ⟨hrnn₁, x₁, hux₁, hk₁⟩ |
      ⟨hrnn₁, hud₁, hstop₁⟩
    · -- A nat fire
      rcases triB with ⟨x₂, hrn₂, hk₂⟩ | ⟨hrnn₂, -, -, -⟩ |
        ⟨hrnn₂, -, -⟩
      · exact natOut _ _ hrn₁ hrn₂ (.inl rfl)
      · exact natOut _ _ hrn₁ hrnn₂ (.inl rfl)
      · exact natOut _ _ hrn₁ hrnn₂ (.inl rfl)
    · -- A δ
      rcases triB with ⟨x₂, hrn₂, hk₂⟩ | ⟨hrnn₂, x₂, hux₂, hk₂⟩ |
        ⟨hrnn₂, hud₂, hstop₂⟩
      · exact natOut _ _ hrnn₁ hrn₂ (.inr rfl)
      · -- δδ: classify the zipped pair by the spine view
        obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
          certZip_app_view hzT
        have certSeam : H₁.looseBVarsBounded 0 = true →
            H₂.looseBVarsBounded 0 = true →
            isDefEqCore μ env fc d H₁ H₂ = .ok true →
            LoopLockOut μ env Q fc d u v u' v' f₁ f₂ := by
          intro hba hbb hc
          obtain ⟨n₁, us₁, hhd₁⟩ := unfoldDefinition_some_head hux₁
          obtain ⟨n₂', us₂', hhd₂⟩ := unfoldDefinition_some_head hux₂
          refine .inr (.inl ⟨Setlec.Expr.mkAppN H₁ cs,
            Setlec.Expr.mkAppN H₂ ds, f₁, f₂, l₁' + 1, l₂' + 1,
            Nat.le_refl _, Nat.le_refl _,
            stepA (whnfCore_reidem_const hm hwc₁' hhd₁),
            stepB (whnfCore_reidem_const hm hwc₂' hhd₂),
            .core f₁ hwc₁' (.refl _), .core f₂ hwc₂' (.refl _),
            CoreSeam.certHead H₁ H₂ cs ds hba hbb hc hlenv hargsv⟩)
        rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
        · exact certSeam hba hbb hc
        · have deltaConst : ∀ {n : Name} {us us' : List Level},
              H₁ = .const n us → H₂ = .const n us' →
              (∀ φ' : Name → Nat,
                us.map (Level.eval φ') = us'.map (Level.eval φ')) →
              LoopLockOut μ env Q fc d u v u' v' f₁ f₂ := by
            intro n us us' he₁ he₂ hev
            subst he₁; subst he₂
            have hlen' : us.length = us'.length := by
              have := congrArg List.length (hev fun _ => 0)
              simpa using this
            obtain ⟨cv, value, hxeq, huy', -⟩ :=
              unfoldDefinition_spine_both (us' := us') (bs := ds)
                hlen' hux₁
            subst hxeq
            have hx₂ := Option.some.inj (hux₂.symm.trans huy')
            subst hx₂
            have hzX : CertZip μ env fc d
                (Setlec.Expr.mkAppN
                  (Setlec.Expr.instantiateLevelParams
                    cv.levelParams us value) cs)
                (Setlec.Expr.mkAppN
                  (Setlec.Expr.instantiateLevelParams
                    cv.levelParams us' value) ds) :=
              certZip_mkAppN_zips (certZip_instantiate hev value)
                hlenv hargsv
            have hIx₁ := hIDl hux₁ hIt₁
            have hIx₂ := hIDl hux₂ hIt₂
            have hpX := (hLD hux₂ ((hLD hux₁ hPt).symm)).symm
            have hQX := hQs (hQD hux₂ (hQs (hQD hux₁ hQt)))
            have hout := below (by omega) hzX hIx₁ hIx₂ hpX hQX
              hk₁ hk₂
            exact LoopLockOut.prepend
              (.core f₁ hwc₁' (.delta hux₁ (.refl _)))
              (.core f₂ hwc₂' (.delta hux₂ (.refl _))) hout
          cases hzH with
          | refl _ =>
            cases H₁ with
            | const n us => exact deltaConst rfl rfl (fun φ' => rfl)
            | app p q => exact absurd rfl (hne₁ p q)
            | bvar i =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | fvar i n ty =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | sort ℓ0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lam n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | forallE n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | letE n ty vv b =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lit l0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | proj sn i pe =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
          | constSlack n us us' hev => exact deltaConst rfl rfl hev
          | cert _ _ hba hbb hc => exact certSeam hba hbb hc
          | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
          | sortSlack u₀ v₀ hev =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | fvar i n ty₁' ty₂' hty =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | proj sn i pe₁ pe₂ he =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
      · -- A δ, B stuck: dead or seam by B's re-core
        obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
          certZip_app_view hzT
        subst hstop₂
        have certSeam : H₁.looseBVarsBounded 0 = true →
            H₂.looseBVarsBounded 0 = true →
            isDefEqCore μ env fc d H₁ H₂ = .ok true →
            LoopLockOut μ env Q fc d u v u'
              (Setlec.Expr.mkAppN H₂ ds) f₁ f₂ := by
          intro hba hbb hc
          obtain ⟨n₁, us₁, hhd₁⟩ := unfoldDefinition_some_head hux₁
          rcases whnfCore_self_or_dead hm hwc₂' with hS₂ |
            ⟨hnc, hnl, hns⟩
          · exact .inr (.inl ⟨Setlec.Expr.mkAppN H₁ cs,
              Setlec.Expr.mkAppN H₂ ds, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _,
              stepA (whnfCore_reidem_const hm hwc₁' hhd₁),
              stepB hS₂,
              .core f₁ hwc₁' (.refl _), .core f₂ hwc₂' (.refl _),
              CoreSeam.certHead H₁ H₂ cs ds hba hbb hc hlenv
                hargsv⟩)
          · exact .inr (.inl ⟨u, v, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _, h₁, h₂,
              .refl _, .refl _,
              CoreSeam.deadR u v (Setlec.Expr.mkAppN H₂ ds) f₂
                (fun g hg => hm.2.2.1 hg hwc₂') hnc hnl hns⟩)
        rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
        · exact certSeam hba hbb hc
        · have deltaBoth : ∀ {n : Name} {us us' : List Level},
              H₁ = .const n us → H₂ = .const n us' →
              (∀ φ' : Name → Nat,
                us.map (Level.eval φ') = us'.map (Level.eval φ')) →
              LoopLockOut μ env Q fc d u v u'
                (Setlec.Expr.mkAppN H₂ ds) f₁ f₂ := by
            intro n us us' he₁ he₂ hev
            subst he₁; subst he₂
            have hlen' : us.length = us'.length := by
              have := congrArg List.length (hev fun _ => 0)
              simpa using this
            obtain ⟨cv, value, -, huy', -⟩ :=
              unfoldDefinition_spine_both (us' := us') (bs := ds)
                hlen' hux₁
            rw [huy'] at hud₂
            exact nomatch hud₂
          cases hzH with
          | refl _ =>
            cases H₁ with
            | const n us => exact deltaBoth rfl rfl (fun φ' => rfl)
            | app p q => exact absurd rfl (hne₁ p q)
            | bvar i =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | fvar i n ty =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | sort ℓ0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lam n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | forallE n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | letE n ty vv b =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lit l0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | proj sn i pe =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
          | constSlack n us us' hev => exact deltaBoth rfl rfl hev
          | cert _ _ hba hbb hc => exact certSeam hba hbb hc
          | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
          | sortSlack u₀ v₀ hev =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | fvar i n ty₁' ty₂' hty =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | proj sn i pe₁ pe₂ he =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₁
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
    · -- A stuck
      rcases triB with ⟨x₂, hrn₂, hk₂⟩ | ⟨hrnn₂, x₂, hux₂, hk₂⟩ |
        ⟨hrnn₂, hud₂, hstop₂⟩
      · exact natOut _ _ hrnn₁ hrn₂ (.inr rfl)
      · -- A stuck, B δ (mirror)
        obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
          certZip_app_view hzT
        subst hstop₁
        have certSeam : H₁.looseBVarsBounded 0 = true →
            H₂.looseBVarsBounded 0 = true →
            isDefEqCore μ env fc d H₁ H₂ = .ok true →
            LoopLockOut μ env Q fc d u v
              (Setlec.Expr.mkAppN H₁ cs) v' f₁ f₂ := by
          intro hba hbb hc
          obtain ⟨n₂', us₂', hhd₂⟩ := unfoldDefinition_some_head hux₂
          rcases whnfCore_self_or_dead hm hwc₁' with hS₁ |
            ⟨hnc, hnl, hns⟩
          · exact .inr (.inl ⟨Setlec.Expr.mkAppN H₁ cs,
              Setlec.Expr.mkAppN H₂ ds, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _,
              stepA hS₁,
              stepB (whnfCore_reidem_const hm hwc₂' hhd₂),
              .core f₁ hwc₁' (.refl _), .core f₂ hwc₂' (.refl _),
              CoreSeam.certHead H₁ H₂ cs ds hba hbb hc hlenv
                hargsv⟩)
          · exact .inr (.inl ⟨u, v, f₁, f₂, l₁' + 1, l₂' + 1,
              Nat.le_refl _, Nat.le_refl _, h₁, h₂,
              .refl _, .refl _,
              CoreSeam.deadL u v (Setlec.Expr.mkAppN H₁ cs) f₁
                (fun g hg => hm.2.2.1 hg hwc₁') hnc hnl hns⟩)
        rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
        · exact certSeam hba hbb hc
        · have deltaBoth : ∀ {n : Name} {us us' : List Level},
              H₁ = .const n us → H₂ = .const n us' →
              (∀ φ' : Name → Nat,
                us.map (Level.eval φ') = us'.map (Level.eval φ')) →
              LoopLockOut μ env Q fc d u v
                (Setlec.Expr.mkAppN H₁ cs) v' f₁ f₂ := by
            intro n us us' he₁ he₂ hev
            subst he₁; subst he₂
            have hlen' : us'.length = us.length := by
              have := congrArg List.length (hev fun _ => 0)
              simpa using this.symm
            obtain ⟨cv, value, -, huy', -⟩ :=
              unfoldDefinition_spine_both (us' := us) (bs := cs)
                hlen' hux₂
            rw [huy'] at hud₁
            exact nomatch hud₁
          cases hzH with
          | refl _ =>
            cases H₁ with
            | const n us => exact deltaBoth rfl rfl (fun φ' => rfl)
            | app p q => exact absurd rfl (hne₁ p q)
            | bvar i =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | fvar i n ty =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | sort ℓ0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lam n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | forallE n ty b m =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | letE n ty vv b =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | lit l0 =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
            | proj sn i pe =>
              obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
                (fun _ _ h2 => nomatch h2)
              exact nomatch hh0
          | constSlack n us us' hev => exact deltaBoth rfl rfl hev
          | cert _ _ hba hbb hc => exact certSeam hba hbb hc
          | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
          | sortSlack u₀ v₀ hev =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | fvar i n ty₁' ty₂' hty =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
          | proj sn i pe₁ pe₂ he =>
            obtain ⟨n0, us0, hh0⟩ := unfold_some_head_of_spine hux₂
              (fun _ _ h2 => nomatch h2)
            exact nomatch hh0
      · -- both stuck: pack out
        subst hstop₁
        subst hstop₂
        exact .inl ⟨hzT, hIt₁, hIt₂, hPt, hQt⟩
  · -- seam from the core step
    have hIw₁ : SubjInv d w₁ := ht₁.subjInv hIC hLS hIu
    have hIw₂ : SubjInv d w₂ := ht₂.subjInv hIC hLS hIv
    have hpw : PairedLeaves w₁ w₂ :=
      Contracts.pairing hLS ht₁ ht₂ hP
    have hQw : Q d w₁ w₂ :=
      hQs (ht₂.q_transport hQB hQZ hQH
        (hQs (ht₁.q_transport hQB hQZ hQH hQ)))
    have runA := stepA (hm.2.2.1 hcb₁ hr₁)
    have runB := stepB (hm.2.2.1 hcb₂ hr₂)
    cases hsm with
    | certHead F₁ F₂ as bs hba hbb hc hlen hargs =>
      exact .inr (.inl ⟨Setlec.Expr.mkAppN F₁ as,
        Setlec.Expr.mkAppN F₂ bs, f₁, f₂, l₁' + 1, l₂' + 1,
        Nat.le_refl _, Nat.le_refl _, runA, runB,
        .contract ht₁ (.refl _), .contract ht₂ (.refl _),
        CoreSeam.certHead F₁ F₂ as bs hba hbb hc hlen hargs⟩)
    | recHead n cv mI rP rules us us' as bs hf hev hlen hargs =>
      exact hIo below hN hR hf hev hlen hargs hIw₁ hIw₂ hpw hQw
        (.contract ht₁ (.refl _)) (.contract ht₂ (.refl _))
        runA runB
    | projHead sn i pe₁ pe₂ as bs he hlen hargs =>
      exact hPr below hN hR he hlen hargs hIw₁ hIw₂ hpw hQw
        (.contract ht₁ (.refl _)) (.contract ht₂ (.refl _))
        runA runB
    | deadL _ _ u'd bnd hrun hnc hnl hns =>
      exact .inr (.inl ⟨w₁, w₂, f₁, f₂, l₁' + 1, l₂' + 1,
        Nat.le_refl _, Nat.le_refl _, runA, runB,
        .contract ht₁ (.refl _), .contract ht₂ (.refl _),
        CoreSeam.deadL w₁ w₂ u'd bnd hrun hnc hnl hns⟩)
    | deadR _ _ v'd bnd hrun hnc hnl hns =>
      exact .inr (.inl ⟨w₁, w₂, f₁, f₂, l₁' + 1, l₂' + 1,
        Nat.le_refl _, Nat.le_refl _, runA, runB,
        .contract ht₁ (.refl _), .contract ht₂ (.refl _),
        CoreSeam.deadR w₁ w₂ v'd bnd hrun hnc hnl hns⟩)

/-- A spine over a non-λ head is never a λ. -/
theorem mkAppN_ne_lam {H : Expr}
    (hH : ∀ n ty b m, H ≠ .lam n ty b m) :
    ∀ {cs : List Expr} (n : Name) (ty b : Expr)
      (m : Setlec.BinderMeta),
      Setlec.Expr.mkAppN H cs ≠ .lam n ty b m := by
  intro cs
  cases cs with
  | nil => exact hH
  | cons a as =>
    intro n ty b m h
    obtain ⟨p, q, hpq⟩ := mkAppN_cons_app (F := H) (a := a) (as := as)
    rw [hpq] at h
    exact nomatch h

/-- `Q` descends through a proj-node pair (the descent family's
second member; at `FrameQ` the frame is per-side structural — a
defined projection has a defined scrutinee). -/
def QDescendProjF (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d i i' : Nat} {sn sn' : Name} {a b : Expr},
    Q d (.proj sn i a) (.proj sn' i' b) → Q d a b

/-- **The proj-spine inversion** (reverse-spine induction): a core
run on a projection-headed spine factors through the scrutinee's
whnf and the projection decision — stuck (the rebuilt spine), or
fired with the field's run and a residual that is a run, the empty
spine, or a dead shape (the nil/dead disjuncts dodge every
idempotence, per the map). -/
theorem whnfCore_proj_spine_inv {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) :
    ∀ {as : List Expr} {f d i : Nat} {sn : Name} {e t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.proj sn i e) as)
        = .ok t →
      ∃ g e₂ e₃, g + 1 ≤ f ∧
        whnf μ env g d e = .ok e₂ ∧
        Setlec.projLitToCtorP μ env g d e₂ = .ok e₃ ∧
        (t = Setlec.Expr.mkAppN (.proj sn i e₃) as ∨
         ∃ us entry h',
           e₃.getAppFn = Setlec.Expr.const entry.ctor us ∧
           env.findProj? sn i = some entry ∧
           entry.native = true ∧
           i < entry.numFields ∧
           e₃.getAppArgs.length
             = entry.numParams + entry.numFields ∧
           whnfCore μ env g d
             (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
             = .ok h' ∧
           ((as = [] ∧ t = h') ∨
            (∃ c, c ≤ f ∧
              whnfCore μ env c d (Setlec.Expr.mkAppN h' as)
                = .ok t) ∨
            ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
              (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
              (∀ ℓ, t ≠ .sort ℓ)))) := by
  suffices H : ∀ (n : Nat) (as : List Expr), as.length ≤ n →
      ∀ {f d i : Nat} {sn : Name} {e t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.proj sn i e) as)
        = .ok t →
      ∃ g e₂ e₃, g + 1 ≤ f ∧
        whnf μ env g d e = .ok e₂ ∧
        Setlec.projLitToCtorP μ env g d e₂ = .ok e₃ ∧
        (t = Setlec.Expr.mkAppN (.proj sn i e₃) as ∨
         ∃ us entry h',
           e₃.getAppFn = Setlec.Expr.const entry.ctor us ∧
           env.findProj? sn i = some entry ∧
           entry.native = true ∧
           i < entry.numFields ∧
           e₃.getAppArgs.length
             = entry.numParams + entry.numFields ∧
           whnfCore μ env g d
             (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
             = .ok h' ∧
           ((as = [] ∧ t = h') ∨
            (∃ c, c ≤ f ∧
              whnfCore μ env c d (Setlec.Expr.mkAppN h' as)
                = .ok t) ∨
            ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
              (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
              (∀ ℓ, t ≠ .sort ℓ)))) by
    exact fun {as} => H as.length as (Nat.le_refl _)
  have nilCase : ∀ {f d i : Nat} {sn : Name} {e t : Expr},
      whnfCore μ env f d (Setlec.Expr.mkAppN (.proj sn i e) [])
        = .ok t →
      ∃ g e₂ e₃, g + 1 ≤ f ∧
        whnf μ env g d e = .ok e₂ ∧
        Setlec.projLitToCtorP μ env g d e₂ = .ok e₃ ∧
        (t = Setlec.Expr.mkAppN (.proj sn i e₃) [] ∨
         ∃ us entry h',
           e₃.getAppFn = Setlec.Expr.const entry.ctor us ∧
           env.findProj? sn i = some entry ∧
           entry.native = true ∧
           i < entry.numFields ∧
           e₃.getAppArgs.length
             = entry.numParams + entry.numFields ∧
           whnfCore μ env g d
             (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
             = .ok h' ∧
           ((([] : List Expr) = [] ∧ t = h') ∨
            (∃ c, c ≤ f ∧
              whnfCore μ env c d (Setlec.Expr.mkAppN h' [])
                = .ok t) ∨
            ((∀ p' q', t.getAppFn ≠ Setlec.Expr.const p' q') ∧
              (∀ n' ty' b' m', t ≠ .lam n' ty' b' m') ∧
              (∀ ℓ, t ≠ .sort ℓ)))) := by
    intro f d i sn e t h
    cases f with
    | zero => exact nomatch h
    | succ f' =>
    obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
    refine ⟨f', e₂, e₃, Nat.le_refl _, he, hlit, ?_⟩
    rcases hcase with rfl |
      ⟨us, entry, hfn, hf, hnat, hi, hlen, hus, hred, -, -⟩
    · exact .inl rfl
    · exact .inr ⟨us, entry, t, hfn, hf, hnat, hi, hlen, hred,
        .inl ⟨rfl, rfl⟩⟩
  intro n
  induction n with
  | zero =>
    intro as hlen0 f d i sn e t h
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp hlen0)
    exact nilCase h
  | succ n ihn =>
    intro as hlenn f d i sn e t h
    rcases List.eq_nil_or_concat as with rfl | ⟨as₀, b, rfl⟩
    · exact nilCase h
    · rw [List.concat_eq_append] at h hlenn ⊢
      have hlen₀ : as₀.length ≤ n := by
        rw [List.length_append] at hlenn
        simpa using Nat.le_of_succ_le_succ hlenn
      have ih := fun {f d i sn e t} h => ihn as₀ hlen₀
        (f := f) (d := d) (i := i) (sn := sn) (e := e) (t := t) h
      rw [show Setlec.Expr.mkAppN (.proj sn i e) (as₀ ++ [b])
          = Expr.app (Setlec.Expr.mkAppN (.proj sn i e) as₀) b
        from mkAppN_append_one] at h
      cases f with
      | zero => exact nomatch h
      | succ f' =>
      obtain ⟨P', hhead, legs⟩ := whnfCore_app_decompose h
      obtain ⟨g, e₂, e₃, hg, he, hlit, hcase⟩ := ih hhead
      refine ⟨g, e₂, e₃, by omega, he, hlit, ?_⟩
      rcases hcase with rfl |
        ⟨us, entry, h', hfn, hf, hnat, hi, hlen, hred, hres⟩
      · -- head stuck: the layer must be iota-none
        rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
          ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
        · exact absurd hPlam
            (mkAppN_ne_lam (H := Expr.proj sn i e₃)
              (fun _ _ _ _ hh => nomatch hh) n' ty' b' m')
        · exact absurd hPlam
            (mkAppN_ne_lam (H := Expr.proj sn i e₃)
              (fun _ _ _ _ hh => nomatch hh) n' ty' b' m')
        · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
          · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio
            rw [show (Expr.app
                  (Setlec.Expr.mkAppN (.proj sn i e₃) as₀) b).getAppFn
                = (Setlec.Expr.mkAppN (.proj sn i e₃) as₀).getAppFn
              from rfl, Setlec.Expr.getAppFn_mkAppN] at hh
            exact nomatch hh
          · exact .inl mkAppN_append_one.symm
      · -- head fired: compose the residual through the layer
        refine .inr ⟨us, entry, h', hfn, hf, hnat, hi, hlen, hred, ?_⟩
        rcases hres with ⟨rfl, rfl⟩ | ⟨c, hc, hresrun⟩ |
          ⟨hnc, hnl2, hns⟩
        · -- empty head spine: the head output IS the field output
          rcases whnfCore_self_or_dead hm hred with hS |
            ⟨hnc, hnl2, hns⟩
          · refine .inr (.inl ⟨max f' f' + 1, by omega, ?_⟩)
            rw [show Setlec.Expr.mkAppN P' ([] ++ [b])
                = Expr.app (Setlec.Expr.mkAppN P' []) b
              from mkAppN_append_one]
            exact whnfCore_app_assemble (g := f') (gl := f') hm
              (hm.2.2.1 (by omega) hS) legs
          · rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
              ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
            · exact absurd hPlam (hnl2 n' ty' b' m')
            · exact absurd hPlam (hnl2 n' ty' b' m')
            · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
              · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio
                exact absurd hh (hnc nn uu)
              · refine .inr (.inr ⟨?_, ?_, ?_⟩)
                · exact fun p' q' hh => hnc p' q' hh
                · exact fun _ _ _ _ hh => nomatch hh
                · exact fun _ hh => nomatch hh
        · -- run residual: assemble one more layer
          refine .inr (.inl ⟨max f' f' + 1, by omega, ?_⟩)
          rw [show Setlec.Expr.mkAppN h' (as₀ ++ [b])
              = Expr.app (Setlec.Expr.mkAppN h' as₀) b
            from mkAppN_append_one]
          exact whnfCore_app_assemble (g := f') (gl := f') hm
            (hm.2.2.1 (Nat.le_trans hc (by omega)) hresrun) legs
        · -- dead residual: the layer stays dead
          rcases legs with ⟨n', ty', b', m', ta', hPlam, -, -, -⟩ |
            ⟨n', ty', b', m', ta', hPlam, -, -, rfl⟩ | ⟨hnl, hio⟩
          · exact absurd hPlam (hnl2 n' ty' b' m')
          · exact absurd hPlam (hnl2 n' ty' b' m')
          · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
            · obtain ⟨nn, uu, hh⟩ := iotaRec_some_head hio
              exact absurd hh (hnc nn uu)
            · refine .inr (.inr ⟨?_, ?_, ?_⟩)
              · exact fun p' q' hh => hnc p' q' hh
              · exact fun _ _ _ _ hh => nomatch hh
              · exact fun _ hh => nomatch hh

/-- **The λ-head case DISCHARGED**: build the spine zip from the
congruent λ components and dispatch. -/
theorem zipLamHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hIo : ZipIotaCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipLamHeadCase μ env φ Q := by
  intro fc d ga la gb lb n ty₁ ty₂ b₁ b₂ m as bs ℓa ℓb below hty
    hbody hlen hargs hIs hIt hp hQ ha hb
  exact zipHeadDispatch (φ := φ) (Q := Q) hm hB hIC hLC hQC hQB
    hQZ hQH hLS
    (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
    hΘ hConst hIo hProj
    (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
        hmes hz' hIs' hIt' hp' hq' hla hlb =>
      below hmes hz' hIs' hIt' hp' hq' hla hlb)
    (certZip_mkAppN_zips (.lam n ty₁ ty₂ b₁ b₂ m hty hbody)
      hlen hargs) hIs hIt hp hQ ha hb

/-- **The letE-head case DISCHARGED**: same dispatch, letE-node
head zip. -/
theorem zipLetEHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hIo : ZipIotaCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipLetEHeadCase μ env φ Q := by
  intro fc d ga la gb lb n ty₁ ty₂ v₁ v₂ b₁ b₂ as bs ℓa ℓb below
    hty hval hbody hlen hargs hIs hIt hp hQ ha hb
  exact zipHeadDispatch (φ := φ) (Q := Q) hm hB hIC hLC hQC hQB
    hQZ hQH hLS
    (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
    hΘ hConst hIo hProj
    (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
        hmes hz' hIs' hIt' hp' hq' hla hlb =>
      below hmes hz' hIs' hIt' hp' hq' hla hlb)
    (certZip_mkAppN_zips (.letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval
      hbody) hlen hargs) hIs hIt hp hQ ha hb

end Discharge

end Setlec.SetR.Interp2
