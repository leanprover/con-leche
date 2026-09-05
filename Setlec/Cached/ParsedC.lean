import Setlec.Cached.CheckerC

/-!
# The parsed-declaration driver on the cached representation

The counterpart of the retired interned `checkDeclsSP`: one `CState`
for the whole stream, the environment-dependent caches flushed per
declaration, declarations consumed as `DeclC` records straight from
the direct parse (`Setlec/Frontend/ExportC.lean`, task #171 — no
arena, no conversion detour).

`checkDeclsSPCachedD` is what the binary runs at `--set-model[=r|=p]`;
its parity twin at `--no-model` is `checkDeclsSPCachedDNM`
(`Setlec/Cached/ParsedNC.lean`).  Acceptance is covered by
`no_proof_of_Empty_SPCD_{R,R2,R2M}` and `no_proof_of_Empty_SPCD_P`
(`Setlec/Verify/Cached/MainC.lean`).
-/

namespace Setlec.Cached

open Setlec

/-! ## Parsed declarations over `ExprC` -/

/-- `ConstantVal` with the type as an `ExprC`. -/
structure ConstantValC where
  name : Name
  levelParams : List Name
  type : ExprC

/-- A parsed declaration over `ExprC` (the counterpart of `DeclP`). -/
inductive DeclC where
  | axiomDecl (val : ConstantValC)
  | defnDecl (val : ConstantValC) (value : ExprC) (hint : ReducibilityHint)
  | thmDecl (val : ConstantValC) (value : ExprC)
  | opaqueDecl (val : ConstantValC) (value : ExprC)
  | basisDecl (kind : BasisKind)
  | indDecl (block : List ConstantInfo)

/-! ## The parsed-declaration checker -/

variable (mode : CheckMode)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : ExprC) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d i

/-- `checkConstantVal` on a converted declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `ExprC`
DAG and the operations on `ExprC` values. -/
def checkConstantValC (fe : FEnv) (cv : ConstantValC) :
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
  let jty ← (coreKnotI mode fe checkFuel).annotate 0 cv.type
  unless ExprC.allLevelParamsDefined cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let _u ← opSIxC mode fe 0 jsty
  let tyE := jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValP` over `ExprC`. -/
def checkDefnValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValP` over `ExprC`. -/
def checkThmValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValP` over `ExprC`. -/
def checkOpaqueValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (fe.push (.axiomInfo cvA))

/-- One converted declaration (mirrors `checkDeclSPPlain` branch by
branch; inductive and basis blocks reuse the `Expr`-level drivers). -/
def checkDeclSPC (fe : FEnv) (pd : DeclC) : CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValC mode fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsC mode fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsC mode fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValC mode fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    checkThmValC mode fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    let fe2 ← checkOpaqueValC mode fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE := value
      checkReducePinF (sharedOpsC mode fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValC mode fe cv
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
    | some p => checkDirectStructS mode fe p
    | none => checkIndDeclSF mode fe block

/-- One step of the converted-declaration fold: flush, then check. -/
def checkDeclSPStepC (fe : FEnv) (pd : DeclC) : CheckCM FEnv := do
  flushC
  checkDeclSPC mode fe pd

/-- Task #171: the direct-parse driver.  `DeclC` records come straight
from the frontend (`Setlec/Frontend/ExportC.lean`) — no arena and no
conversion pass.

Task #172 B3b: the argument was `List WDeclC`, the subtype of records
whose `ExprC` slots carried the field invariant `WFc`, because the
capstone's entry premise was the parser's `WFc`-by-construction
theorem.  Under `@[computed_field]` (B3a) `WFc` held of everything, so
the receipt carried no information; the subtype, its predicate
`DeclCWFc` and the fold's unwrapping step are gone, and the capstone
letters below this driver are restated over `List DeclC` — strictly
stronger, by the coordinator's ratification. -/
def checkDeclsSPCachedD (mode : CheckMode) (ds : List DeclC) : CheckM Env := do
  let fe ← (ds.foldlM (checkDeclSPStepC mode) (mkFEnv Env.empty)).run' {}
  pure fe.env

end Setlec.Cached
