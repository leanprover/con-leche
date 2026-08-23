import Setlec.Kernel.CheckerS
import Setlec.Kernel.CoreNC

/-!
# The cert-skipping shared-state driver (task #76, `SETLEC_NO_PROOF_CERTS`)

**Unverified measurement mode** — see `Setlec/Kernel/CoreNC.lean`.
Each definition here duplicates its `Setlec/Kernel/CheckerS.lean`
counterpart verbatim with `sharedOps` replaced by `sharedOpsNC` (the
core knot tied at the cert-skipping bodies).  Everything else is
identical: the phase structure, the flush discipline, every
declaration-level check — the flag removes only the proof-feeding
infer/defeq calls inside the core engine, never a declaration-level or
install-time check.  Main selects this driver only under
`SETLEC_NO_PROOF_CERTS=1`; the default path (`checkDeclsShared`) is
untouched and remains the subject of the consistency statements.
-/

namespace Setlec

/-- `opE` at the cert-skipping knot. -/
def opENC (fe : FEnv) (pick : CoreFnsI → Nat → EIdx → CheckIM EIdx)
    (d : Nat) (e : Expr) : CheckIM Expr := do
  let i ← internExprM e
  let j ← pick (coreKnotNC fe checkFuel) d i
  match ← withStore (fun st => st.readbackI j) with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- `opB` at the cert-skipping knot. -/
def opBNC (fe : FEnv) (d : Nat) (a b : Expr) : CheckIM Bool := do
  let i ← internExprM a
  let j ← internExprM b
  (coreKnotNC fe checkFuel).defeq d i j

/-- `opS` at the cert-skipping knot. -/
def opSNC (fe : FEnv) (d : Nat) (e : Expr) : CheckIM Level := do
  let i ← internExprM e
  let u ← ensureSortI (coreKnotNC fe checkFuel) d i
  readbackLevelM u

/-- `sharedOps` at the cert-skipping knot. -/
def sharedOpsNC (fe : FEnv) : CheckerOps CheckIM where
  annotate _ d e := opENC fe (·.annotate) d e
  inferType _ d e := opENC fe (·.infer) d e
  isDefEq _ d a b := opBNC fe d a b
  ensureSort _ d e := opSNC fe d e
  whnf _ d e := opENC fe (·.whnf) d e

/-- `checkIndMemberS` at the cert-skipping ops. -/
def checkIndMemberNC (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckIM FEnv := do
  flushS
  let cvA ← checkMemberValF (sharedOpsNC fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- `provisionRecsS` at the cert-skipping ops. -/
def provisionRecsNC (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckIM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushS
      let cvA ← checkMemberValF (sharedOpsNC feAcc) blockNames feAcc
        ci.toConstantVal
      let (feSelf, others) ← provisionRecsNC blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- `checkIndRecsS` at the cert-skipping ops. -/
def checkIndRecsNC (blockNames : List Name) (fe₂ : FEnv)
    (recs : List ConstantInfo) : CheckIM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsNC blockNames fe₂ recs
    flushS
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF (sharedOpsNC feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- `checkProjFnS` at the cert-skipping ops. -/
def checkProjFnNC (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckIM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckIM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckIM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOpsNC fe) fe pty cvj lps nP nF i
  checkProjIotaF (m := CheckIM) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- `installProjFnStepS` at the cert-skipping ops. -/
def installProjFnStepNC (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushS
    checkProjFnNC fe T ctorName lps nP nF i
  else pure fe

/-- `checkDirectStructS` at the cert-skipping ops (task #82).

The cert-skipping twin of `checkDirectStructS`.  Like every definition
in this module it duplicates its `Setlec/Kernel/CheckerS.lean`
counterpart verbatim with `sharedOps` replaced by `sharedOpsNC`; the
`...F` stages are the shared ones.  **Not yet reachable**: the direct
clause is parked, so neither `checkIndDeclSF` nor `checkIndDeclNC`
dispatches to it yet — this definition exists so that enabling the
clause is a one-line change in both drivers at once. -/
def checkDirectStructNC (fe : FEnv) (p : DirectParts) : CheckIM FEnv := do
  let (fe₁, cvTa) ← checkDirectIndF (sharedOpsNC fe) fe p
  let (fe₂, cvCa) ← checkDirectCtorF (sharedOpsNC fe₁) fe₁ p
  let cvRa ← checkConstantValF (sharedOpsNC fe₂) fe₂ p.cvR
  checkDirectRecTyF (sharedOpsNC fe₂) fe₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRuleF (sharedOpsNC fe₂) fe₂ p cvCa cvRa
  let fe₃ := fe₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP,
      if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
        .plain else .inert,
      rhsA⟩])
  unless (List.range p.nF).all
      (fun j => (fe₃.find? (projFnName p.cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  (List.range p.nF).foldlM
    (fun e j => checkDirectProjF (sharedOpsNC e) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF cvTa cvCa e j) fe₃

/-- `checkIndDeclSF` at the cert-skipping ops. -/
def checkIndDeclNC (fe : FEnv) (block : List ConstantInfo) :
    CheckIM FEnv := do
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  unless block = nonrecs ++ recs do
    throw (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps ← pure (indBlockCapsF fe cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberNC blockNames caps) fe
    let fe₃ ← checkIndRecsNC blockNames fe₂ recs
    unless (List.range nF).all
        (fun j => (fe₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    let fe₄ ← (List.range nF).foldlM
      (installProjFnStepNC cvT.name cvC.name cvT.levelParams nP nF) fe₃
    (List.range nF).foldlM
      (installProjTemplateStepS cvT.name cvC.name cvT.levelParams nP nF) fe₄
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberNC blockNames {}) fe
    checkIndRecsNC blockNames fe₂ recs

/-- `checkDeclSF` at the cert-skipping ops. -/
def checkDeclNC (fe : FEnv) (d : Declaration) : CheckIM FEnv :=
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantValF (sharedOpsNC fe) fe cv
    let fe2 ← checkDefnValF (sharedOpsNC fe) fe cv value hint
    if natOpNames.contains cv.name then
      unless natOpGuardF fe2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOkF fe2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match fe2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs (sharedOpsNC fe) fe.env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal
          s!"structural Nat operation not stored ({cv.name})")
    if natDivModNames.contains cv.name then
      checkDivModPinF (sharedOpsNC fe) fe fe2 cv.name
    pure fe2
  | .thmDecl cv value => do
    let cv ← checkConstantValF (sharedOpsNC fe) fe cv
    checkThmValF (sharedOpsNC fe) fe cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantValF (sharedOpsNC fe) fe cv
    checkOpaqueValF (sharedOpsNC fe) fe cv value
  | .axiomDecl cv => do
    let cvA ← checkConstantValF (sharedOpsNC fe) fe cv
    if stdAxiomOkF fe cvA then
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure fe
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    if kind = .quotK then
      unless fe.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDeclF fe
  | .indDecl block => checkIndDeclNC fe block

/-- `checkDeclSharedF` at the cert-skipping ops (what the binary runs
under `SETLEC_NO_PROOF_CERTS=1`). -/
def checkDeclSharedNC (fe : FEnv) (d : Declaration) : CheckM FEnv :=
  (checkDeclNC fe d).run' {}

/-- `checkDeclsShared` at the cert-skipping ops. -/
def checkDeclsSharedNC (ds : List Declaration) : CheckM Env := do
  let fe ← ds.foldlM checkDeclSharedNC (mkFEnv Env.empty)
  pure fe.env

end Setlec
