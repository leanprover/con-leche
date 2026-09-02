import Setlec.Kernel.TypeChecker

/-!
# Knot equations

The definitional bridges between the fueled entry-point spellings
(`whnfCore mode env fuel d e`, …) and the core bodies applied to the knot
one level down.  Inversion and claims lemmas are stated against the
bodies with an abstract record; instantiating the record with
`pureFns mode env fuel` and rewriting with these equations recovers the
fueled statements the higher layers consume.
-/

namespace Setlec

variable {mode : CheckMode}

/-! ## Loop step budgets

The reduction and lazy-delta loops (task #106) run on their own step
budgets, kept `irreducible` so that the `rfl` knot equations above do
not try to evaluate them.  Proofs that need to peel one iteration use
these positivity witnesses instead. -/

theorem whnfCoreLoopFuel_succ : ∃ n, whnfCoreLoopFuel = n + 1 :=
  ⟨999999, by unfold whnfCoreLoopFuel; rfl⟩

theorem whnfLoopFuel_succ : ∃ n, whnfLoopFuel = n + 1 :=
  ⟨99999, by unfold whnfLoopFuel; rfl⟩

theorem defeqLoopFuel_succ : ∃ n, defeqLoopFuel = n + 1 :=
  ⟨99999, by unfold defeqLoopFuel; rfl⟩


@[simp] theorem pureFns_whnfCore (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).whnfCore d e =
      whnfCoreBody mode (pureFns mode env f) env d e := rfl

@[simp] theorem pureFns_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).whnf d e = whnfBody (pureFns mode env f) env d e := rfl

@[simp] theorem pureFns_infer (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).infer d e = inferBody mode (pureFns mode env f) env d e := rfl

@[simp] theorem pureFns_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode env (f + 1)).defeq d a b =
      defeqBody mode (pureFns mode env f) env d a b := rfl

@[simp] theorem pureFns_annotate (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env (f + 1)).annotate d e =
      annotateBody mode (pureFns mode env f) env d e := rfl

theorem whnfCore_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfCore mode env (f + 1) d e = whnfCoreBody mode (pureFns mode env f) env d e := rfl

theorem whnf_succ (env : Env) (f d : Nat) (e : Expr) :
    whnf mode env (f + 1) d e = whnfBody (pureFns mode env f) env d e := rfl

theorem inferTypeCore_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCore mode env (f + 1) d e = inferBody mode (pureFns mode env f) env d e := rfl

theorem isDefEqCore_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCore mode env (f + 1) d a b = defeqBody mode (pureFns mode env f) env d a b := rfl

theorem annotateCore_succ (env : Env) (f d : Nat) (e : Expr) :
    annotateCore mode env (f + 1) d e = annotateBody mode (pureFns mode env f) env d e := rfl

theorem whnfCore_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).whnfCore d e = whnfCore mode env f d e := rfl

theorem whnf_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).whnf d e = whnf mode env f d e := rfl

theorem infer_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).infer d e = inferTypeCore mode env f d e := rfl

theorem defeq_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns mode env f).defeq d a b = isDefEqCore mode env f d a b := rfl

theorem annotate_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns mode env f).annotate d e = annotateCore mode env f d e := rfl

/-- Fuel-zero spellings throw. -/
theorem whnfCore_zero (env : Env) (d : Nat) (e : Expr) :
    whnfCore mode env 0 d e = throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnf_zero (env : Env) (d : Nat) (e : Expr) :
    whnf mode env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCore_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCore mode env 0 d e = throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCore_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCore mode env 0 d a b = throw (.internal "fuel exhausted: defeq") := rfl

theorem annotateCore_zero (env : Env) (d : Nat) (e : Expr) :
    annotateCore mode env 0 d e =
      throw (.internal "fuel exhausted: annotate") := rfl

theorem ensureSort_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFns mode env f) env d e = ensureSortCore mode env f d e := rfl

/-! Fueled spellings for the record-parameterized helpers: the body one
level up calls them with `pureFns mode env fuel`, so their facts appear in
inversions at the same fuel as the entry-point facts. -/

abbrev iotaRecP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := iotaRec mode (pureFns mode env fuel) env

abbrev iotaCertsP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → List Expr →
    CheckM Bool := iotaCerts (pureFns mode env fuel) env

abbrev defEqListP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → List Expr →
    List Expr → CheckM Bool := defEqList (pureFns mode env fuel) env

abbrev proofIrrelP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := proofIrrel (pureFns mode env fuel) env

abbrev stuckIrrelP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := stuckIrrel mode (pureFns mode env fuel) env

abbrev pairEtaCertP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := pairEtaCert mode (pureFns mode env fuel) env

abbrev structEtaCertP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structEtaCert mode (pureFns mode env fuel) env

abbrev structEtaCertWithP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    Expr → CheckM Bool := structEtaCertWith mode (pureFns mode env fuel) env

abbrev structEtaProjCertsP (mode : CheckMode) (env : Env) (fuel : Nat) (d : Nat) (T : Name)
    (us' : List Level) (targs : List Expr) (b : Expr) (lpsT : List Name) :
    List Nat → CheckM Bool :=
  structEtaProjCerts (pureFns mode env fuel) env d T us' targs b lpsT

abbrev structUnitCertP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structUnitCert (pureFns mode env fuel) env

abbrev etaCertP (mode : CheckMode) (env : Env) (fuel : Nat) (d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) (b : Expr) : CheckM Bool :=
  etaCert mode (pureFns mode env fuel) env d n ty body mb b

abbrev majorToCtorP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name →
    List RecRule → Expr → CheckM Expr := majorToCtor mode (pureFns mode env fuel) env

abbrev litMajorToCtorP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := litMajorToCtor (pureFns mode env fuel) env

abbrev projLitToCtorP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM Expr := projLitToCtor (pureFns mode env fuel) env

abbrev projCertP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Nat →
    Nat → CheckM Bool := projCert (pureFns mode env fuel) env

abbrev isPropTypeP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → CheckM Bool :=
  isPropType (pureFns mode env fuel) env

abbrev projFieldDomP (mode : CheckMode) (env : Env) (fuel : Nat) (d : Nat) (structProp : Bool)
    (sn : Name) (e₂ : Expr) : Nat → Nat → Expr → CheckM Expr :=
  projFieldDom (pureFns mode env fuel) env d structProp sn e₂

abbrev annotateProjRecP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → ProjEntry →
    Nat → Expr → Expr → List Level → CheckM Expr :=
  annotateProjRec (pureFns mode env fuel) env

abbrev annotateProjElimP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Name → Nat →
    Expr → Expr → CheckM Expr := annotateProjElim (pureFns mode env fuel) env

abbrev reduceNatP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := reduceNat (pureFns mode env fuel) env

abbrev defeqSpineP (mode : CheckMode) (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := defeqSpine (pureFns mode env fuel) env

/-! Folding rewrites: record-applied helper spellings into their fueled
`P` names (used right after unfolding a body in an inversion proof). -/

theorem iotaRec_fold (env : Env) (fuel : Nat) :
    iotaRec mode (pureFns mode env fuel) env = iotaRecP mode env fuel := rfl
theorem iotaCerts_fold (env : Env) (fuel : Nat) :
    iotaCerts (pureFns mode env fuel) env = iotaCertsP mode env fuel := rfl
theorem defEqList_fold (env : Env) (fuel : Nat) :
    defEqList (pureFns mode env fuel) env = defEqListP mode env fuel := rfl
theorem proofIrrel_fold (env : Env) (fuel : Nat) :
    proofIrrel (pureFns mode env fuel) env = proofIrrelP mode env fuel := rfl
theorem stuckIrrel_fold (env : Env) (fuel : Nat) :
    stuckIrrel mode (pureFns mode env fuel) env = stuckIrrelP mode env fuel := rfl
theorem pairEtaCert_fold (env : Env) (fuel : Nat) :
    pairEtaCert mode (pureFns mode env fuel) env = pairEtaCertP mode env fuel := rfl
theorem structEtaCert_fold (env : Env) (fuel : Nat) :
    structEtaCert mode (pureFns mode env fuel) env = structEtaCertP mode env fuel := rfl
theorem structEtaCertWith_fold (env : Env) (fuel : Nat) :
    structEtaCertWith mode (pureFns mode env fuel) env =
      structEtaCertWithP mode env fuel := rfl
theorem structEtaProjCerts_fold (env : Env) (fuel : Nat) :
    structEtaProjCerts (pureFns mode env fuel) env =
      structEtaProjCertsP mode env fuel := rfl
theorem structUnitCert_fold (env : Env) (fuel : Nat) :
    structUnitCert (pureFns mode env fuel) env = structUnitCertP mode env fuel := rfl
theorem etaCert_fold (env : Env) (fuel : Nat) :
    etaCert mode (pureFns mode env fuel) env = etaCertP mode env fuel := rfl
theorem majorToCtor_fold (env : Env) (fuel : Nat) :
    majorToCtor mode (pureFns mode env fuel) env = majorToCtorP mode env fuel := rfl
theorem litMajorToCtor_fold (env : Env) (fuel : Nat) :
    litMajorToCtor (pureFns mode env fuel) env = litMajorToCtorP mode env fuel := rfl
theorem projLitToCtor_fold (env : Env) (fuel : Nat) :
    projLitToCtor (pureFns mode env fuel) env = projLitToCtorP mode env fuel := rfl
theorem projCert_fold (env : Env) (fuel : Nat) :
    projCert (pureFns mode env fuel) env = projCertP mode env fuel := rfl
theorem annotateProjElim_fold (env : Env) (fuel : Nat) :
    annotateProjElim (pureFns mode env fuel) env =
      annotateProjElimP mode env fuel := rfl
theorem reduceNat_fold (env : Env) (fuel : Nat) :
    reduceNat (pureFns mode env fuel) env = reduceNatP mode env fuel := rfl
theorem defeqSpine_fold (env : Env) (fuel : Nat) :
    defeqSpine (pureFns mode env fuel) env = defeqSpineP mode env fuel := rfl

end Setlec
