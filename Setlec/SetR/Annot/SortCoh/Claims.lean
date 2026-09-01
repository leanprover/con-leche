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
      Setlec.etaCert μ r env d n₁ ty₁ body₁ m₁ b = .ok true →
      PostCoreCert μ env r k d (.lam n₁ ty₁ body₁ m₁) b
  | etaR (a : Expr) (n₂ : Name) (ty₂ body₂ : Expr)
      (m₂ : Setlec.BinderMeta) :
      Setlec.etaCert μ r env d n₂ ty₂ body₂ m₂ a = .ok true →
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
        revert h
        cases hbd : r.defeq (d + 1)
            (body₁.instantiate1 (.fvar d n₁ ty₁))
            (body₂.instantiate1 (.fvar d n₂ ty₂)) with
        | error err => intro h; exact nomatch h
        | ok rb =>
          intro h
          dsimp only at h
          cases rb with
          | false => simp [pure, Except.pure] at h
          | true =>
            exact .piCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂
              (hc'' ▸ hd) hbd
      · exact nomatch h
    case _ n₁ ty₁ body₁ m₁ n₂ ty₂ body₂ m₂ => -- lam congruence
      split at h
      · exact nomatch h
      next c'' hd =>
      split at h
      · next hc'' =>
        revert h
        cases hbd : r.defeq (d + 1)
            (body₁.instantiate1 (.fvar d n₁ ty₁))
            (body₂.instantiate1 (.fvar d n₂ ty₂)) with
        | error err => intro h; exact nomatch h
        | ok rb =>
          intro h
          dsimp only at h
          cases rb with
          | false => simp [pure, Except.pure] at h
          | true =>
            exact .lamCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂
              (hc'' ▸ hd) hbd
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
    Setlec.etaCert μ (Setlec.pureFns μ env g) env d n ty body m a'
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


end Setlec.SetR.Interp2
