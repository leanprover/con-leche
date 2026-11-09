module

import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.CoreIO

public section

/-!
# Knot equations

The definitional bridges between the fueled entry-point spellings
(`whnfCore mode eager env fuel d e`, …) and the core bodies applied to the knot
one level down.  Inversion and claims lemmas are stated against the
bodies with an abstract record; instantiating the record with
`pureFns mode eager env fuel` and rewriting with these equations recovers the
fueled statements the higher layers consume.
-/

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

/-! ## Loop step budgets

The reduction and lazy-delta loops (task #106) run on their own step
budgets, kept `irreducible` so that the `rfl` knot equations above do
not try to evaluate them.  Proofs that need to peel one iteration use
these positivity witnesses instead. -/

theorem whnfLoopFuel_succ : ∃ n, whnfLoopFuel = n + 1 :=
  ⟨4611686018427387903, by unfold whnfLoopFuel; rfl⟩

/-- The binder node of a kind: a λ (`true`) or a ∀ (`false`), the
shapes `Expr.binderPair?` reads. -/
@[expose] def Expr.binderOf : Bool → Expr → Expr → Expr
  | true, t, b => .lam t b
  | false, t, b => .forallE t b

/-- `Expr.binderPair?`, read back: two binders of the kind. -/
theorem Expr.binderPair?_some {lam : Bool} {B₁ B₂ t₁ b₁ t₂ b₂ : Expr}
    (h : Expr.binderPair? lam B₁ B₂ = some (t₁, b₁, t₂, b₂)) :
    B₁ = Expr.binderOf lam t₁ b₁ ∧ B₂ = Expr.binderOf lam t₂ b₂ := by
  cases lam <;> cases B₁ <;> cases B₂ <;>
    simp only [Expr.binderPair?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    (obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)

theorem whnfCore_succ (env : Env) (f d : Nat) (e : Expr) {c : Bool} :
    whnfCore mode eager env (f + 1) d e c = whnfCoreBody mode (pureFns mode eager env f) env c d e
        := rfl

theorem whnf_succ (env : Env) (f d : Nat) (e : Expr) :
    whnf mode eager env (f + 1) d e = whnfBody (pureFns mode eager env f) env d e := rfl

theorem inferTypeCore_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCore mode eager env (f + 1) d e = inferBody (pureFns mode eager env f) env d e := rfl

theorem isDefEqCore_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCore mode eager env (f + 1) d a b = defeqBody mode eager (pureFns mode eager env f) env
        d a b := rfl

/-! ## The io lane (task #161 stage 2)

The io knot is a *leaf* lane: its reduction and definitional-equality
fields are the full knot's at the same fuel, so the equations below
fold them straight back to the full spellings and the io claims family
consumes the sealed four unchanged. -/

@[simp] theorem pureFnsIO_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode eager env f).whnf d e = whnf mode eager env f d e := by
  cases f <;> rfl

@[simp] theorem pureFnsIO_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsIO mode eager env f).defeq d a b = isDefEqCore mode eager env f d a b := by
  cases f <;> rfl

theorem ensureSortIO_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFnsIO mode eager env f) env d e = ensureSortCore mode eager env f d e := by
  cases f <;> rfl

theorem inferTypeCoreIO_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCoreIO mode eager env (f + 1) d e =
      inferBodyIO (pureFnsIO mode eager env f) env d e := rfl

theorem inferIO_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsIO mode eager env f).infer d e = inferTypeCoreIO mode eager env f d e := rfl

theorem inferTypeCoreIO_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCoreIO mode eager env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

/-! ## The io slot (task #172 B4)

The executable knot's `inferIO` slot **is** the leaf-lane
`inferTypeCoreIO` the io claims are stated at (`inferTypeIO_on`), at
every mode (task #346). -/

theorem inferTypeIO_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeIO mode eager env (f + 1) d e =
      inferBodyIO (CoreFns.ioView (pureFns mode eager env f)) env d e := rfl

theorem inferTypeIO_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode eager env f).inferIO d e = inferTypeIO mode eager env f d e := rfl

theorem inferTypeIO_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeIO mode eager env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

/-- `inferBodyIO` reads exactly three fields of its record (`whnf`,
`infer`, `defeq`); two records agreeing there run it identically. -/
theorem inferBodyIO_congr {r₁ r₂ : CoreFns CheckM} {env : Env}
    (hw : r₁.whnf = r₂.whnf) (hi : r₁.infer = r₂.infer)
    (hd : r₁.defeq = r₂.defeq) (d : Nat) (e : Expr) :
    inferBodyIO r₁ env d e = inferBodyIO r₂ env d e := by
  cases r₁; cases r₂
  dsimp only at hw hi hd
  subst hw; subst hi; subst hd
  rfl

/-- **The io identification**: the executable
io slot runs the leaf-lane `inferTypeCoreIO` — the io claims' stated
subject — level for level.  (The two ties differ only in which record
carries the io recursion: `CoreFns.ioView` of the knot versus the leaf
knot; `inferBodyIO_congr` plus this induction identifies them.) -/
theorem inferTypeIO_on (env : Env) :
    ∀ (f d : Nat) (e : Expr),
      inferTypeIO mode eager env f d e = inferTypeCoreIO mode eager env f d e
  | 0, _, _ => rfl
  | f + 1, d, e => by
    rw [inferTypeIO_succ, inferTypeCoreIO_succ]
    exact inferBodyIO_congr
      (r₁ := (pureFns mode eager env f).ioView) (r₂ := pureFnsIO mode eager env f)
      (funext fun d' => funext fun e' => (pureFnsIO_whnf env f d' e').symm)
      (funext fun d' => funext fun e' => by
        show inferTypeIO mode eager env f d' e' = (pureFnsIO mode eager env f).infer d' e'
        rw [inferTypeIO_on env f d' e']
        exact (inferIO_def (mode := mode) (eager := eager) env f d' e').symm)
      (funext fun d' => funext fun a => funext fun b =>
        (pureFnsIO_defeq env f d' a b).symm) d e

theorem whnfCore_def (env : Env) (f d : Nat) (e : Expr) {c : Bool} :
    (pureFns mode eager env f).whnfCore c d e = whnfCore mode eager env f d e c := rfl

theorem whnf_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode eager env f).whnf d e = whnf mode eager env f d e := rfl

theorem infer_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode eager env f).infer d e = inferTypeCore mode eager env f d e := rfl

theorem defeq_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode eager env f).defeq d a b = isDefEqCore mode eager env f d a b := rfl

/-- **The eager slot is the eager tower's `defeq`** (task #353): the
knot ties `defeqE` to the bodies at `eager := true`, which is what the
knot at `eager := true` ties its `defeq` to. -/
theorem defeqE_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode eager env f).defeqE d a b = isDefEqCore mode true env f d a b := by
  cases f <;> rfl

/-- The eager flag an application argument's type is compared at (task
#353): the eager tower for an `eagerReduce _ _` argument (`defeqArg`). -/
@[expose] def argEager (eager : Bool) (a : Expr) : Bool :=
  if a.isEagerReduce then true else eager

/-- The full-grade argument check, read as one comparison at the
argument's flag. -/
theorem defeqArg_def (env : Env) (f d : Nat) (a ta ty : Expr) :
    defeqArg (pureFns mode eager env f) d a ta ty =
      isDefEqCore mode (argEager eager a) env f d ta ty := by
  unfold defeqArg argEager
  split
  · exact defeqE_def env f d ta ty
  · rfl

/-- Fuel-zero spellings throw. -/
theorem whnfCore_zero (env : Env) (d : Nat) (e : Expr) {c : Bool} :
    whnfCore mode eager env 0 d e c = throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnf_zero (env : Env) (d : Nat) (e : Expr) :
    whnf mode eager env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCore_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCore mode eager env 0 d e = throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCore_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCore mode eager env 0 d a b = throw (.internal "fuel exhausted: defeq") := rfl

theorem ensureSort_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFns mode eager env f) env d e = ensureSortCore mode eager env f d e := rfl

/-! Fueled spellings for the record-parameterized helpers: the body one
level up calls them with `pureFns mode eager env fuel`, so their facts appear in
inversions at the same fuel as the entry-point facts. -/

abbrev iotaRecFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := iotaRec mode (pureFns mode eager env fuel) env

abbrev iotaCertsFullFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    List Expr → CheckM Bool := iotaCertsFull (pureFns mode eager env fuel) env

abbrev iotaIndexOkFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Nat →
    Nat → Nat →
    Expr → List Expr → List Expr → CheckM Bool := iotaIndexOk (pureFns mode eager env fuel) env

abbrev defEqListFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → List Expr
    →
    List Expr → CheckM Bool := defEqList (pureFns mode eager env fuel) env

abbrev proofIrrelFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM Bool := proofIrrel (pureFns mode eager env fuel)

abbrev propIrrelFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM Bool := propIrrel (pureFns mode eager env fuel) env

abbrev stuckIrrelFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM Bool := stuckIrrel (pureFns mode eager env fuel) env

abbrev structEtaCertFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr
    → Expr →
    CheckM Bool := structEtaCert (pureFns mode eager env fuel) env

abbrev structEtaCertWithFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat →
    Expr → Expr →
    Expr → CheckM Bool := structEtaCertWith (pureFns mode eager env fuel) env

abbrev structUnitCertFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr
    → Expr →
    CheckM Bool := structUnitCert (pureFns mode eager env fuel) env

abbrev etaCertFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) (d : Nat)
    (ty body : Expr) (b : Expr) : CheckM Bool :=
  etaCert mode (pureFns mode eager env fuel) env d ty body b

abbrev majorToCtorFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Name →
    Bool → List RecRule → Expr → CheckM Expr := majorToCtor mode (pureFns mode eager env fuel) env

abbrev litMajorToCtorFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr
    →
    CheckM Expr := litMajorToCtor (pureFns mode eager env fuel) env

abbrev prepareMajorFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Name →
    Bool → List RecRule → Expr → CheckM Expr := prepareMajor mode (pureFns mode eager env fuel) env

abbrev projLitToCtorFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := projLitToCtor (pureFns mode eager env fuel) env

abbrev reduceNatFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := reduceNat (pureFns mode eager env fuel) env

abbrev boolTrueShortcutFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat →
    Expr →
    CheckM Bool := boolTrueShortcut (pureFns mode eager env fuel)

abbrev defeqSpineFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM Bool := defeqSpine (pureFns mode eager env fuel) env

abbrev reduceProjCoreFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Name
    →
    Nat → Expr → CheckM (Option Expr) := reduceProjCore mode (pureFns mode eager env fuel) env

abbrev quickDefEqFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM (Option Bool) := quickDefEq mode (pureFns mode eager env fuel)

abbrev defeqBindersFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Bool →
    Nat → Nat → List Expr → Expr → Expr → Expr → Expr → CheckM Bool :=
  defeqBinders mode (pureFns mode eager env fuel)

abbrev defeqBindersInnerFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Bool →
    Nat → Expr → Expr → CheckM Bool := defeqBindersInner mode (pureFns mode eager env fuel)

abbrev defeqOffsetFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM (Option Bool) := defeqOffset (pureFns mode eager env fuel)

abbrev tryUnfoldProjAppFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat →
    Expr →
    CheckM (Option Expr) := tryUnfoldProjApp (pureFns mode eager env fuel)

abbrev deltaQuickFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM DeltaStep := deltaQuick mode (pureFns mode eager env fuel)

abbrev lazyDeltaStepFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr
    → Expr →
    CheckM DeltaStep := lazyDeltaStep mode (pureFns mode eager env fuel) env

abbrev lazyDeltaReductionFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat →
    Nat →
    Expr → Expr → CheckM LazyRes := lazyDeltaReduction mode eager (pureFns mode eager env fuel) env

abbrev lazyDeltaProjReductionFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) :
    Nat →
    Name → Nat → Nat → Expr → Expr → CheckM Bool :=
  lazyDeltaProjReduction mode (pureFns mode eager env fuel) env

abbrev defeqProjPairFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr
    → Expr →
    CheckM Bool := defeqProjPair mode (pureFns mode eager env fuel) env

abbrev defeqStuckFueled (mode : CheckMode) (eager : Bool) (env : Env) (fuel : Nat) : Nat → Expr →
    Expr →
    CheckM Bool := defeqStuck mode (pureFns mode eager env fuel) env

/-! Folding rewrites: record-applied helper spellings into their fueled
`P` names (used right after unfolding a body in an inversion proof). -/

theorem iotaRec_fold (env : Env) (fuel : Nat) :
    iotaRec mode (pureFns mode eager env fuel) env = iotaRecFueled mode eager env fuel := rfl
theorem iotaCertsFull_fold (env : Env) (fuel : Nat) :
    iotaCertsFull (pureFns mode eager env fuel) env = iotaCertsFullFueled mode eager env fuel := rfl
theorem iotaIndexOk_fold (env : Env) (fuel : Nat) :
    iotaIndexOk (pureFns mode eager env fuel) env = iotaIndexOkFueled mode eager env fuel := rfl
theorem defEqList_fold (env : Env) (fuel : Nat) :
    defEqList (pureFns mode eager env fuel) env = defEqListFueled mode eager env fuel := rfl
theorem proofIrrel_fold (env : Env) (fuel : Nat) :
    proofIrrel (pureFns mode eager env fuel) = proofIrrelFueled mode eager env fuel := rfl
theorem propIrrel_fold (env : Env) (fuel : Nat) :
    propIrrel (pureFns mode eager env fuel) env = propIrrelFueled mode eager env fuel := rfl
theorem stuckIrrel_fold (env : Env) (fuel : Nat) :
    stuckIrrel (pureFns mode eager env fuel) env = stuckIrrelFueled mode eager env fuel := rfl
theorem structEtaCert_fold (env : Env) (fuel : Nat) :
    structEtaCert (pureFns mode eager env fuel) env = structEtaCertFueled mode eager env fuel := rfl
theorem structEtaCertWith_fold (env : Env) (fuel : Nat) :
    structEtaCertWith (pureFns mode eager env fuel) env =
      structEtaCertWithFueled mode eager env fuel := rfl
theorem structUnitCert_fold (env : Env) (fuel : Nat) :
    structUnitCert (pureFns mode eager env fuel) env = structUnitCertFueled mode eager env fuel :=
        rfl
theorem etaCert_fold (env : Env) (fuel : Nat) :
    etaCert mode (pureFns mode eager env fuel) env = etaCertFueled mode eager env fuel := rfl
theorem majorToCtor_fold (env : Env) (fuel : Nat) :
    majorToCtor mode (pureFns mode eager env fuel) env = majorToCtorFueled mode eager env fuel :=
        rfl
theorem litMajorToCtor_fold (env : Env) (fuel : Nat) :
    litMajorToCtor (pureFns mode eager env fuel) env = litMajorToCtorFueled mode eager env fuel :=
        rfl
theorem prepareMajor_fold (env : Env) (fuel : Nat) :
    prepareMajor mode (pureFns mode eager env fuel) env = prepareMajorFueled mode eager env fuel :=
        rfl
theorem projLitToCtor_fold (env : Env) (fuel : Nat) :
    projLitToCtor (pureFns mode eager env fuel) env = projLitToCtorFueled mode eager env fuel := rfl
theorem reduceNat_fold (env : Env) (fuel : Nat) :
    reduceNat (pureFns mode eager env fuel) env = reduceNatFueled mode eager env fuel := rfl
theorem boolTrueShortcut_fold (env : Env) (fuel : Nat) :
    boolTrueShortcut (pureFns mode eager env fuel) = boolTrueShortcutFueled mode eager env fuel :=
        rfl
theorem defeqSpine_fold (env : Env) (fuel : Nat) :
    defeqSpine (pureFns mode eager env fuel) env = defeqSpineFueled mode eager env fuel := rfl
theorem reduceProjCore_fold (env : Env) (fuel : Nat) :
    reduceProjCore mode (pureFns mode eager env fuel) env = reduceProjCoreFueled mode eager env
        fuel := rfl
theorem quickDefEq_fold (env : Env) (fuel : Nat) :
    quickDefEq mode (pureFns mode eager env fuel) = quickDefEqFueled mode eager env fuel := rfl
theorem defeqOffset_fold (env : Env) (fuel : Nat) :
    defeqOffset (pureFns mode eager env fuel) = defeqOffsetFueled mode eager env fuel := rfl
theorem tryUnfoldProjApp_fold (env : Env) (fuel : Nat) :
    tryUnfoldProjApp (pureFns mode eager env fuel) = tryUnfoldProjAppFueled mode eager env fuel :=
        rfl
theorem deltaQuick_fold (env : Env) (fuel : Nat) :
    deltaQuick mode (pureFns mode eager env fuel) = deltaQuickFueled mode eager env fuel := rfl
theorem lazyDeltaStep_fold (env : Env) (fuel : Nat) :
    lazyDeltaStep mode (pureFns mode eager env fuel) env = lazyDeltaStepFueled mode eager env fuel
        := rfl
theorem lazyDeltaReduction_fold (env : Env) (fuel : Nat) :
    lazyDeltaReduction mode eager (pureFns mode eager env fuel) env =
      lazyDeltaReductionFueled mode eager env fuel := rfl
theorem lazyDeltaProjReduction_fold (env : Env) (fuel : Nat) :
    lazyDeltaProjReduction mode (pureFns mode eager env fuel) env =
      lazyDeltaProjReductionFueled mode eager env fuel := rfl
theorem defeqProjPair_fold (env : Env) (fuel : Nat) :
    defeqProjPair mode (pureFns mode eager env fuel) env = defeqProjPairFueled mode eager env fuel
        := rfl
theorem defeqStuck_fold (env : Env) (fuel : Nat) :
    defeqStuck mode (pureFns mode eager env fuel) env = defeqStuckFueled mode eager env fuel := rfl

end ConLeche
