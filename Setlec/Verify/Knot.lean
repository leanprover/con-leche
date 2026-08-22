import Setlec.Kernel.TypeChecker

/-!
# Knot equations

The definitional bridges between the fueled entry-point spellings
(`whnfCore env fuel d e`, …) and the core bodies applied to the knot
one level down.  Inversion and claims lemmas are stated against the
bodies with an abstract record; instantiating the record with
`pureFns env fuel` and rewriting with these equations recovers the
fueled statements the higher layers consume.
-/

namespace Setlec

@[simp] theorem pureFns_whnfCore (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env (f + 1)).whnfCore d e =
      whnfCoreBody (pureFns env f) env d e := rfl

@[simp] theorem pureFns_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env (f + 1)).whnf d e = whnfBody (pureFns env f) env d e := rfl

@[simp] theorem pureFns_infer (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env (f + 1)).infer d e = inferBody (pureFns env f) env d e := rfl

@[simp] theorem pureFns_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns env (f + 1)).defeq d a b =
      defeqBody (pureFns env f) env d a b := rfl

@[simp] theorem pureFns_annotate (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env (f + 1)).annotate d e =
      annotateBody (pureFns env f) env d e := rfl

theorem whnfCore_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfCore env (f + 1) d e = whnfCoreBody (pureFns env f) env d e := rfl

theorem whnf_succ (env : Env) (f d : Nat) (e : Expr) :
    whnf env (f + 1) d e = whnfBody (pureFns env f) env d e := rfl

theorem inferTypeCore_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCore env (f + 1) d e = inferBody (pureFns env f) env d e := rfl

theorem isDefEqCore_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCore env (f + 1) d a b = defeqBody (pureFns env f) env d a b := rfl

theorem annotateCore_succ (env : Env) (f d : Nat) (e : Expr) :
    annotateCore env (f + 1) d e = annotateBody (pureFns env f) env d e := rfl

theorem whnfCore_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env f).whnfCore d e = whnfCore env f d e := rfl

theorem whnf_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env f).whnf d e = whnf env f d e := rfl

theorem infer_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env f).infer d e = inferTypeCore env f d e := rfl

theorem defeq_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFns env f).defeq d a b = isDefEqCore env f d a b := rfl

theorem annotate_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFns env f).annotate d e = annotateCore env f d e := rfl

/-- Fuel-zero spellings throw. -/
theorem whnfCore_zero (env : Env) (d : Nat) (e : Expr) :
    whnfCore env 0 d e = throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnf_zero (env : Env) (d : Nat) (e : Expr) :
    whnf env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCore_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCore env 0 d e = throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCore_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCore env 0 d a b = throw (.internal "fuel exhausted: defeq") := rfl

theorem annotateCore_zero (env : Env) (d : Nat) (e : Expr) :
    annotateCore env 0 d e =
      throw (.internal "fuel exhausted: annotate") := rfl

theorem ensureSort_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFns env f) env d e = ensureSortCore env f d e := rfl

/-! Fueled spellings for the record-parameterized helpers: the body one
level up calls them with `pureFns env fuel`, so their facts appear in
inversions at the same fuel as the entry-point facts. -/

abbrev iotaRecP (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := iotaRec (pureFns env fuel) env

abbrev iotaCertsP (env : Env) (fuel : Nat) : Nat → Expr → List Expr →
    CheckM Bool := iotaCerts (pureFns env fuel) env

abbrev defEqListP (env : Env) (fuel : Nat) : Nat → List Expr →
    List Expr → CheckM Bool := defEqList (pureFns env fuel) env

abbrev proofIrrelP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := proofIrrel (pureFns env fuel) env

abbrev stuckIrrelP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := stuckIrrel (pureFns env fuel) env

abbrev pairEtaCertP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := pairEtaCert (pureFns env fuel) env

abbrev structEtaCertP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structEtaCert (pureFns env fuel) env

abbrev structEtaCertWithP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    Expr → CheckM Bool := structEtaCertWith (pureFns env fuel) env

abbrev structEtaProjCertsP (env : Env) (fuel : Nat) (d : Nat) (T : Name)
    (us' : List Level) (targs : List Expr) (b : Expr) (lpsT : List Name) :
    List Nat → CheckM Bool :=
  structEtaProjCerts (pureFns env fuel) env d T us' targs b lpsT

abbrev structUnitCertP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := structUnitCert (pureFns env fuel) env

abbrev etaCertP (env : Env) (fuel : Nat) (d : Nat) (n : Name)
    (ty body : Expr) (mb : BinderMeta) (b : Expr) : CheckM Bool :=
  etaCert (pureFns env fuel) env d n ty body mb b

abbrev majorToCtorP (env : Env) (fuel : Nat) : Nat → Name →
    List RecRule → Expr → CheckM Expr := majorToCtor (pureFns env fuel) env

abbrev projCertP (env : Env) (fuel : Nat) : Nat → Expr → Nat →
    Level → Level → Nat → CheckM Bool := projCert (pureFns env fuel) env

abbrev isPropTypeP (env : Env) (fuel : Nat) : Nat → Expr → CheckM Bool :=
  isPropType (pureFns env fuel) env

abbrev projFieldDomP (env : Env) (fuel : Nat) (d : Nat) (structProp : Bool)
    (sn : Name) (e₂ : Expr) : Nat → Nat → Expr → CheckM Expr :=
  projFieldDom (pureFns env fuel) env d structProp sn e₂

abbrev annotateProjRecP (env : Env) (fuel : Nat) : Nat → ProjEntry →
    Nat → Expr → Expr → List Level → CheckM Expr :=
  annotateProjRec (pureFns env fuel) env

abbrev annotateProjElimP (env : Env) (fuel : Nat) : Nat → Name → Nat →
    Expr → Expr → CheckM Expr := annotateProjElim (pureFns env fuel) env

abbrev reduceNatP (env : Env) (fuel : Nat) : Nat → Expr →
    CheckM (Option Expr) := reduceNat (pureFns env fuel) env

abbrev defeqSpineP (env : Env) (fuel : Nat) : Nat → Expr → Expr →
    CheckM Bool := defeqSpine (pureFns env fuel) env

/-! Folding rewrites: record-applied helper spellings into their fueled
`P` names (used right after unfolding a body in an inversion proof). -/

theorem iotaRec_fold (env : Env) (fuel : Nat) :
    iotaRec (pureFns env fuel) env = iotaRecP env fuel := rfl
theorem iotaCerts_fold (env : Env) (fuel : Nat) :
    iotaCerts (pureFns env fuel) env = iotaCertsP env fuel := rfl
theorem defEqList_fold (env : Env) (fuel : Nat) :
    defEqList (pureFns env fuel) env = defEqListP env fuel := rfl
theorem proofIrrel_fold (env : Env) (fuel : Nat) :
    proofIrrel (pureFns env fuel) env = proofIrrelP env fuel := rfl
theorem stuckIrrel_fold (env : Env) (fuel : Nat) :
    stuckIrrel (pureFns env fuel) env = stuckIrrelP env fuel := rfl
theorem pairEtaCert_fold (env : Env) (fuel : Nat) :
    pairEtaCert (pureFns env fuel) env = pairEtaCertP env fuel := rfl
theorem structEtaCert_fold (env : Env) (fuel : Nat) :
    structEtaCert (pureFns env fuel) env = structEtaCertP env fuel := rfl
theorem structEtaCertWith_fold (env : Env) (fuel : Nat) :
    structEtaCertWith (pureFns env fuel) env =
      structEtaCertWithP env fuel := rfl
theorem structEtaProjCerts_fold (env : Env) (fuel : Nat) :
    structEtaProjCerts (pureFns env fuel) env =
      structEtaProjCertsP env fuel := rfl
theorem structUnitCert_fold (env : Env) (fuel : Nat) :
    structUnitCert (pureFns env fuel) env = structUnitCertP env fuel := rfl
theorem etaCert_fold (env : Env) (fuel : Nat) :
    etaCert (pureFns env fuel) env = etaCertP env fuel := rfl
theorem majorToCtor_fold (env : Env) (fuel : Nat) :
    majorToCtor (pureFns env fuel) env = majorToCtorP env fuel := rfl
theorem projCert_fold (env : Env) (fuel : Nat) :
    projCert (pureFns env fuel) env = projCertP env fuel := rfl
theorem annotateProjElim_fold (env : Env) (fuel : Nat) :
    annotateProjElim (pureFns env fuel) env =
      annotateProjElimP env fuel := rfl
theorem reduceNat_fold (env : Env) (fuel : Nat) :
    reduceNat (pureFns env fuel) env = reduceNatP env fuel := rfl
theorem defeqSpine_fold (env : Env) (fuel : Nat) :
    defeqSpine (pureFns env fuel) env = defeqSpineP env fuel := rfl

end Setlec
