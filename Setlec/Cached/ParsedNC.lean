import Setlec.Cached.ParsedC
import Setlec.Cached.CoreNC

/-!
# The `--no-model` cached parsed-declaration driver (the cached parity lane)

The cached counterpart of `Setlec/Kernel/CheckerNC.lean`: each
definition here duplicates its `Setlec/Cached/CheckerC.lean` /
`Setlec/Cached/ParsedC.lean` counterpart with `sharedOpsC` replaced by
`sharedOpsCNC` (install-time engine ops on the cert-skipping cached
knot) and the front-door knot references on `coreKnotFNC` — exactly
the substitution `CheckerNC` performs on `CheckerS`/the production
parsed driver.  The phase structure, the flush discipline and every
declaration-level check are identical to the certified cached driver;
`flushInferFC` runs back to back with `flushC` at every declaration
boundary, mirroring `checkDeclSPStepNM` (the snapshot-close
`flushInferFC` sites of the arena driver have no counterpart here —
the cached driver has no tier-two bracket, see `ParsedC.lean`).

Measurement-only and UNVERIFIED: reference-kernel parity is the claim,
stated as parity.  Main selects this driver only under
`--no-model --core=cached-parsed`.
-/

namespace Setlec.Cached

open Setlec

/-! ## The entry-point record over the cert-skipping cached core -/

/-- `opE` at the cert-skipping cached knot (twin of `CheckerC`'s
`opE`; port of `CheckerNC`'s `opENC`). -/
def opENC (fe : FEnv) (pick : CoreFnsI → Nat → ExprC → CheckCM ExprC)
    (d : Nat) (e : Expr) : CheckCM Expr := do
  pick (coreKnotNC fe checkFuel) d e

/-- `opB` at the cert-skipping cached knot. -/
def opBNC (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  (coreKnotNC fe checkFuel).defeq d a b

/-- `opS` at the cert-skipping cached knot. -/
def opSNC (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI (coreKnotNC fe checkFuel) d e

/-- `sharedOpsC` at the cert-skipping cached knot (the cached
`sharedOpsNC`). -/
def sharedOpsCNC (fe : FEnv) : CheckerOps CheckCM where
  annotate _ d e := opENC fe (·.annotate) d e
  inferType _ d e := opENC fe (·.infer) d e
  isDefEq _ d a b := opBNC fe d a b
  ensureSort _ d e := opSNC fe d e
  whnf _ d e := opENC fe (·.whnf) d e

/-! ## Inductive-block drivers at the cert-skipping ops
(the `CheckerC` S-family with `sharedOpsC mode` → `sharedOpsCNC` and
the mode-gated stages at `.noModel`, mirroring `CheckerNC`) -/

/-- `checkIndMemberS` at the cert-skipping ops. -/
def checkIndMemberNC (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckCM FEnv := do
  flushC
  let cvA ← checkMemberValF (sharedOpsCNC fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- `provisionRecsS` at the cert-skipping ops. -/
def provisionRecsNC (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckCM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushC
      let cvA ← checkMemberValF (sharedOpsCNC feAcc) blockNames feAcc
        ci.toConstantVal
      let (feSelf, others) ← provisionRecsNC blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- `checkIndRecsS` at the cert-skipping ops. -/
def checkIndRecsNC (blockNames : List Name) (fe₂ : FEnv)
    (recs : List ConstantInfo) : CheckCM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsNC blockNames fe₂ recs
    flushC
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF .noModel (sharedOpsCNC feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- `checkProjFnS` at the cert-skipping ops. -/
def checkProjFnNC (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckCM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckCM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckCM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckCM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOpsCNC fe) fe pty cvj lps nP nF i
  checkProjIotaF .noModel (sharedOpsCNC fe) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- `installProjFnStepS` at the cert-skipping ops. -/
def installProjFnStepNC (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckCM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushC
    checkProjFnNC fe T ctorName lps nP nF i
  else pure fe

/-- `checkDirectProjsS` at the cert-skipping ops. -/
def checkDirectProjsNC (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (cvTa cvCa : ConstantVal) :
    (todo i : Nat) → Option Expr → FEnv → CheckCM FEnv
  | 0, _, _, fe => pure fe
  | todo + 1, i, rt?, fe => do
    flushC
    let fe' ← checkDirectProjF (sharedOpsCNC fe) T C lps nP nF resSort cvTa
      cvCa rt? fe i
    checkDirectProjsNC T C lps nP nF resSort cvTa cvCa todo (i + 1)
      (rt?.bind (Expr.instPisAtLift [directProjArgP T i])) fe'

/-- `checkDirectStructS` at the cert-skipping ops. -/
def checkDirectStructNC (fe : FEnv) (p : DirectParts) : CheckCM FEnv := do
  flushC
  let (fe₁, cvTa) ← checkDirectIndF (sharedOpsCNC fe) fe p
  flushC
  let (fe₂, cvCa) ← checkDirectCtorF (sharedOpsCNC fe₁) fe fe₁ p cvTa
  flushC
  let cvRa ← checkConstantValF (sharedOpsCNC fe₂) fe₂ p.cvR
  checkDirectRecTyF (sharedOpsCNC fe₂) fe₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRuleF (sharedOpsCNC fe₂) fe₂ p cvCa cvRa
  let fe₃ := fe₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP,
      if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
        .plain else .inert,
      rhsA⟩])
  unless (List.range p.nF).all
      (fun j => (fe₃.find? (projFnName p.cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  checkDirectProjsNC p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF
    p.resSort cvTa cvCa p.nF 0
    (Expr.instPisAtLift (directProjPs p.nP) cvCa.type) fe₃

/-- `checkIndDeclSF` at the cert-skipping ops. -/
def checkIndDeclNC (fe : FEnv) (block : List ConstantInfo) :
    CheckCM FEnv := do
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
    let caps ← pure (indBlockCapsF .noModel fe cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberNC blockNames caps) fe
    let fe₃ ← checkIndRecsNC blockNames fe₂ recs
    unless ctorResidualOkF .noModel fe₃ cvT.name cvC.name cvT.levelParams
        nP nF
        caps.eta do
      throw (.notImplemented "modeled structure: eta constructor residual")
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

/-! ## The parsed-declaration driver: checking-mode front door
(`coreKnotFNC`), cert-skipping internals -/

/-- `opSIxC` at the cert-skipping front-door knot. -/
def opSIxNC (fe : FEnv) (d : Nat) (i : ExprC) : CheckCM Level :=
  ensureSortI (coreKnotFNC fe checkFuel) d i

/-- `checkConstantValC` at the cert-skipping knot (twin of
`CheckerNC`'s `checkConstantValPNC`). -/
def checkConstantValCNC (fe : FEnv) (cv : ConstantValC) :
    CheckCM (ConstantVal × ExprC) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless ExprC.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotFNC fe checkFuel).annotate 0 cv.type
  unless ExprC.allLevelParamsDefined cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotFNC fe checkFuel).infer 0 jty
  let _u ← opSIxNC fe 0 jsty
  let tyE := jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValC` at the cert-skipping knot. -/
def checkDefnValCNC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotFNC fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotFNC fe checkFuel).infer 0 jv
  unless ← (coreKnotFNC fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValC` at the cert-skipping knot. -/
def checkThmValCNC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotFNC fe checkFuel).infer 0 jty
  let ul ← opSIxNC fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotFNC fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotFNC fe checkFuel).infer 0 jv
  unless ← (coreKnotFNC fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValC` at the cert-skipping knot. -/
def checkOpaqueValCNC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotFNC fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotFNC fe checkFuel).infer 0 jv
  unless ← (coreKnotFNC fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (fe.push (.axiomInfo cvA))

/-- `checkDeclSPC` at the cert-skipping knot (mirrors
`checkDeclSPNCPlain` branch by branch). -/
def checkDeclSPCNC (fe : FEnv) (pd : DeclC) : CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValCNC fe cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValCNC fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsCNC fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsCNC fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValCNC fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValCNC fe cv
    checkThmValCNC fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValCNC fe cv
    let fe2 ← checkOpaqueValCNC fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE := value
      checkReducePinF (sharedOpsCNC fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValCNC fe cv
    if stdAxiomOkF fe cvA then do
      recordCConst cvA.name cvA.type jty none
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
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

/-- One step of the cert-skipping converted-declaration fold: flush
(entry-point memos and the checking-mode inference memo, back to
back, as in `checkDeclSPStepNM`), then check. -/
def checkDeclSPStepCNC (fe : FEnv) (pd : DeclC) : CheckCM FEnv := do
  flushC
  flushInferFC
  checkDeclSPCNC fe pd

/-- The `--no-model` direct-parse driver (UNVERIFIED — reference-kernel
parity is the claim, stated as parity; the certified counterpart is
`checkDeclsSPCachedD`).  The whole fold runs in one `CState` with the
environment-dependent caches flushed per declaration. -/
def checkDeclsSPCachedDNM (ds : List DeclC) : CheckM Env := do
  let fe ← (ds.foldlM checkDeclSPStepCNC (mkFEnv Env.empty)).run' {}
  pure fe.env

end Setlec.Cached
