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
  checkProjIotaF (sharedOpsNC fe) fe T ctorName lps cvj nP nF i
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

/-- `checkDirectProjsS` at the cert-skipping ops. -/
def checkDirectProjsNC (T C : Name) (lps : List Name) (nP nF : Nat)
    (cvTa cvCa : ConstantVal) :
    (todo i : Nat) → Option Expr → FEnv → CheckIM FEnv
  | 0, _, _, fe => pure fe
  | todo + 1, i, rt?, fe => do
    flushS
    let fe' ← checkDirectProjF (sharedOpsNC fe) T C lps nP nF cvTa cvCa
      rt? fe i
    checkDirectProjsNC T C lps nP nF cvTa cvCa todo (i + 1)
      (rt?.bind (Expr.instPisAtLift [directProjArg T lps nP i])) fe'

/-- `checkDirectStructS` at the cert-skipping ops (task #82).

The cert-skipping twin of `checkDirectStructS`.  Like every definition
in this module it duplicates its `Setlec/Kernel/CheckerS.lean`
counterpart verbatim with `sharedOps` replaced by `sharedOpsNC`; the
`...F` stages are the shared ones.  **Not yet reachable**: the direct
clause is parked, so neither `checkIndDeclSF` nor `checkIndDeclNC`
dispatches to it yet — this definition exists so that enabling the
clause is a one-line change in both drivers at once. -/
def checkDirectStructNC (fe : FEnv) (p : DirectParts) : CheckIM FEnv := do
  flushS
  let (fe₁, cvTa) ← checkDirectIndF (sharedOpsNC fe) fe p
  flushS
  let (fe₂, cvCa) ← checkDirectCtorF (sharedOpsNC fe₁) fe fe₁ p cvTa
  flushS
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
  checkDirectProjsNC p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF
    cvTa cvCa p.nF 0
    (Expr.instPisAtLift (directProjPs p.nP) cvCa.type) fe₃

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
    -- Rare Nat-op branch decided before the value check, so the common
    -- path does not retain `fe` across it (see `checkDeclSP`).
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
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
    else
      checkDefnValF (sharedOpsNC fe) fe cv value hint
  | .thmDecl cv value => do
    let cv ← checkConstantValF (sharedOpsNC fe) fe cv
    checkThmValF (sharedOpsNC fe) fe cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantValF (sharedOpsNC fe) fe cv
    let fe2 ← checkOpaqueValF (sharedOpsNC fe) fe cv value
    if reduceOpNames.contains cv.name then
      checkReducePinF (sharedOpsNC fe) fe fe2 cv.name value
    pure fe2
  | .axiomDecl cv => do
    let cvA ← checkConstantValF (sharedOpsNC fe) fe cv
    if stdAxiomOkF fe cvA then
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
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
  | .indDecl block =>
    match directPartsF? fe block with
    | some p => checkDirectStructNC fe p
    | none => checkIndDeclNC fe block

/-- `checkDeclSharedF` at the cert-skipping ops (what the binary runs
under `SETLEC_NO_PROOF_CERTS=1`). -/
def checkDeclSharedNC (fe : FEnv) (d : Declaration) : CheckM FEnv :=
  (checkDeclNC fe d).run' {}

/-- `checkDeclsShared` at the cert-skipping ops. -/
def checkDeclsSharedNC (ds : List Declaration) : CheckM Env := do
  let fe ← ds.foldlM checkDeclSharedNC (mkFEnv Env.empty)
  pure fe.env

/-! ## Parsed-index drivers at the cert-skipping knot (task #78) -/

/-- `opSIx` at the cert-skipping knot. -/
def opSIxNC (fe : FEnv) (d : Nat) (i : EIdx) : CheckIM Level := do
  let u ← ensureSortI (coreKnotNC fe checkFuel) d i
  readbackLevelM u

/-- `checkConstantValP` at the cert-skipping knot. -/
def checkConstantValPNC (fe : FEnv) (cv : ConstantValP) :
    CheckIM (ConstantVal × EIdx) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 cv.type) do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if ← withStore (fun st => st.hasFvarI cv.type) then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotNC fe checkFuel).annotate 0 cv.type
  unless ← withStore (fun st => st.allLevelParamsDefinedI cv.levelParams jty) do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless ← withStore (fun st => constsResolveFI st fe jty) do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotNC fe checkFuel).infer 0 jty
  let _u ← opSIxNC fe 0 jsty
  let tyE ← readbackEM jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValP` at the cert-skipping knot (task #64 split: install
phase first — guards, annotate, record — then the check phase; see
`checkDefnValP`). -/
def checkDefnValPNC (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) (hint : ReducibilityHint) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotNC fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  recordIConst cvA.name cvA.type jty (some (vE, jv))
  -- CHECK PHASE ENTRY (task #64 split, see `checkDefnValP`)
  let jvt ← (coreKnotNC fe checkFuel).infer 0 jv
  unless ← (coreKnotNC fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  -- CHECK PHASE EXIT
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValP` at the cert-skipping knot (task #64 split). -/
def checkThmValPNC (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  let jsty ← (coreKnotNC fe checkFuel).infer 0 jty
  let ul ← opSIxNC fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotNC fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  recordIConst cvA.name cvA.type jty (some (vE, jv))
  -- CHECK PHASE ENTRY (task #64 split, see `checkDefnValP`)
  let jvt ← (coreKnotNC fe checkFuel).infer 0 jv
  unless ← (coreKnotNC fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  -- CHECK PHASE EXIT
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValP` at the cert-skipping knot (task #64 split). -/
def checkOpaqueValPNC (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotNC fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordIConst cvA.name cvA.type jty none
  -- CHECK PHASE ENTRY (task #64 split, see `checkDefnValP`)
  let jvt ← (coreKnotNC fe checkFuel).infer 0 jv
  unless ← (coreKnotNC fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  -- CHECK PHASE EXIT
  pure (fe.push (.axiomInfo cvA))

/-- `checkDeclSPPlain` at the cert-skipping knot (the unbracketed
path: install-only kinds and the rare pinned-cert branches). -/
def checkDeclSPNCPlain (fe : FEnv) (pd : DeclP) : CheckIM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValPNC fe cv
    -- Rare Nat-op branch decided before the value check, so the common
    -- path does not retain `fe` across it (see `checkDeclSP`).
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValPNC fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsNC fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsNC fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValPNC fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValPNC fe cv
    checkThmValPNC fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValPNC fe cv
    let fe2 ← checkOpaqueValPNC fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE ← readbackEM value
      checkReducePinF (sharedOpsNC fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValPNC fe cv
    if stdAxiomOkF fe cvA then do
      recordIConst cvA.name cvA.type jty none
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then do
        recordIConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then do
        recordIConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
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
  | .indDecl block =>
    match directPartsF? fe block with
    | some p => checkDirectStructNC fe p
    | none => checkIndDeclNC fe block

/-- `checkDefnValPNC` with the in-place annotate-snapshot bracket. -/
def checkDefnValPNCB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) (hint : ReducibilityHint) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  modify fun s =>
    let st := s.store
    let s := { s with store := EStore.empty }
    { s with store := st.enableTierTwo }
  let jv ← (coreKnotNC fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  let jvt ← (coreKnotNC fe checkFuel).infer 0 jv
  let ok ← (coreKnotNC fe checkFuel).defeq 0 jvt jty
  let jv' ← closeSnapshotM jv
  unless ok do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  recordIConst cvA.name cvA.type jty (some (vE, jv'))
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValPNC` with the in-place annotate-snapshot bracket. -/
def checkThmValPNCB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  let jsty ← (coreKnotNC fe checkFuel).infer 0 jty
  let ul ← opSIxNC fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  modify fun s =>
    let st := s.store
    let s := { s with store := EStore.empty }
    { s with store := st.enableTierTwo }
  let jv ← (coreKnotNC fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  let jvt ← (coreKnotNC fe checkFuel).infer 0 jv
  let ok ← (coreKnotNC fe checkFuel).defeq 0 jvt jty
  let jv' ← closeSnapshotM jv
  unless ok do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  recordIConst cvA.name cvA.type jty (some (vE, jv'))
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValPNC` with the in-place annotate-snapshot bracket
(nothing stored, nothing promoted). -/
def checkOpaqueValPNCB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  modify fun s =>
    let st := s.store
    let s := { s with store := EStore.empty }
    { s with store := st.enableTierTwo }
  let jv ← (coreKnotNC fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let jvt ← (coreKnotNC fe checkFuel).infer 0 jv
  let ok ← (coreKnotNC fe checkFuel).defeq 0 jvt jty
  modify fun s =>
    let st := s.store
    let s := { s with store := EStore.empty }
    let s := s.flushed
    { s with store := st.truncateTierTwo }
  unless ok do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  recordIConst cvA.name cvA.type jty none
  pure (fe.push (.axiomInfo cvA))

/-- `checkDeclSPNC` with the in-place annotate-snapshot bracket. -/
def checkDeclSPNC (fe : FEnv) (pd : DeclP) : CheckIM FEnv :=
  match pd with
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
      checkDeclSPNCPlain fe pd
    else do
      let (cvA, jty) ← checkConstantValPNC fe cv
      checkDefnValPNCB4 fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValPNC fe cv
    checkThmValPNCB4 fe cvA jty value
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then
      checkDeclSPNCPlain fe pd
    else do
      let (cvA, jty) ← checkConstantValPNC fe cv
      checkOpaqueValPNCB4 fe cvA jty value
  | _ => checkDeclSPNCPlain fe pd

/-- One step of the cert-skipping fold (the bracketed checker). -/
def checkDeclSPStepNC (n0 : Nat) (fe : FEnv) (pd : DeclP) :
    CheckIM FEnv := do
  unless pd.inRangeB n0 do
    throw (.internal "parsed declaration index out of range")
  flushS
  checkDeclSPNC fe pd

/-- The cert-skipping parsed-declaration checker (measurement knob;
UNVERIFIED). -/
def checkDeclsSPNC (st : WFStore) (pds : List DeclP) : CheckM Env := do
  let fe ← (pds.foldlM (checkDeclSPStepNC (st.raw.nodes.size + st.raw.nodes.size))
    (mkFEnv Env.empty)).run' { store := st.raw }
  pure fe.env

end Setlec
