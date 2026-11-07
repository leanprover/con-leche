module

public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The parsed-declaration driver on the cached representation

One `CState` for the whole stream, the environment-dependent caches
flushed per declaration, declarations consumed as `Declaration` records
straight from the direct parse (`ConLeche/Frontend/ExportC.lean`, task
#171 — no conversion detour).

`checkDeclStepC` is the check of one record, every kind: the fold `checkDecls`
(`ConLeche/Cached/Decls.lean`) runs it at each position, and the binary's driver
(`ConLeche/Driver/*`) runs it as a job at a view of the stream's index and returns the fold's
environment together with the proof that `checkDecls` returns it.  It runs at `.verified` and at
`.trusted` alike (the trusted mode is the same fold at the other mode, and nothing else):
acceptance at `.verified` is covered by the main corollary `no_False_declaration`
(`ConLeche/MainTheorem.lean`, through `no_False_theorem_accepted` in
`ConLeche/Verify/Cached/StreamThm.lean`), and two modes that both accept end in the same
environment (`checkDecls_agree`, `ConLeche/Verify/Cached/DeclPushes.lean`).

The driver's parameter is the `CheckMode` itself (task #185): the knot it
ties (`coreKnotI mode`) and the block's stages all take the same
mode.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The parsed-declaration checker -/

variable (mode : CheckMode)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode false fe checkFuel) d i

/-- `checkConstantVal` on a parsed declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `Expr`
DAG and the cached operations on its nodes. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorL (strLitStoredF fe) s!"type of {cv.name}" cv.type)
  let jsty ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let _u ← opSIxC mode fe 0 jsty

/-- `refuseBlock` (`ConLeche/Kernel/CheckDecl.lean`) through the index: a block `blockShape?`
cannot read has its type formers checked as constants, then is refused with the reason
(`blockDefect`).  It never returns an index. -/
def refuseBlockS (fe : FEnv) (nPd : Nat) (block : List ConstantInfo) : CheckCM FEnv := do
  block.foldlM (fun (_ : Unit) ci => match ci with
    | .indInfo cv _ => discard <| checkConstantValC mode fe cv
    | _ => pure ()) ()
  throw (blockDefect nPd block)

/-- Check a definition's value against its declared type, returning the
record to install, unpushed: the pinned `Nat`-operation arm of
`checkDeclC` certifies against an overlay before it pushes. -/
def checkDefnValCI (fe : FEnv) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : CheckCM ConstantInfo := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let jv := value
  unless Expr.allLevelParamsDefinedC cv.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsErrorL (strLitStoredF fe) s!"value of {cv.name}" jv)
  let jvt ← (coreKnotI mode false fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode false fe checkFuel).defeq 0 jvt cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure (.defnInfo cv jv hint)

/-- Check a theorem's value against its declared type, returning the
record to install, unpushed: its statement alone, a theorem being opaque
to reduction. -/
def checkThmValCI (fe : FEnv) (cv : ConstantVal) (value : Expr) : CheckCM ConstantInfo := do
  let jsty ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let u ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
    throw (.invalid s!"type of theorem {cv.name} is not a proposition")
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let jv := value
  unless Expr.allLevelParamsDefinedC cv.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsErrorL (strLitStoredF fe) s!"value of {cv.name}" jv)
  let jvt ← (coreKnotI mode false fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode false fe checkFuel).defeq 0 jvt cv.type do
    throw (.invalid s!"type mismatch in theorem {cv.name}")
  pure (.thmInfo cv)

/-- Check an opaque's value against its declared type, returning the
axiom record to install, unpushed (as `checkDefnValCI`). -/
def checkOpaqueValCI (fe : FEnv) (cv : ConstantVal)
    (value : Expr) : CheckCM ConstantInfo := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let jv := value
  unless Expr.allLevelParamsDefinedC cv.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsErrorL (strLitStoredF fe) s!"value of {cv.name}" jv)
  let jvt ← (coreKnotI mode false fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode false fe checkFuel).defeq 0 jvt cv.type do
    throw (.invalid s!"type mismatch in opaque {cv.name}")
  pure (.axiomInfo cv)

/-- `checkQuotRecord`'s cached twin. -/
def checkQuotRecordC (fe : FEnv) (k : QuotKind) (cv : ConstantVal) : CheckCM FEnv := do
  unless quotPinHit k cv do
    throw (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))
  unless quotPredsOk fe.find? k do
    throw (.notImplemented "quotient declaration before what it needs")
  installBasisDeclF fe (quotAt k cv)

/-- **An inductive block's install** (`checkDeclKind`'s `.indDecl` arm's
twin).

* Task #228: the stream's DECLARED parameter count, checked before the
  dispatch.
* ONE ROUTE (task #210), dispatched by the RECOGNISER alone (task
  #219): a recognised block is the installer's, nested ones and the
  pinned basis blocks included; any other is refused with the reason
  (`refuseBlockS`). -/
def checkIndDeclC (fe : FEnv) (block : List ConstantInfo) (nP : Nat) :
    CheckCM FEnv :=
  if indParamsOk nP block then
    match blockShape? nP block with
    | some p => checkBlockKS mode fe block p
    | none => refuseBlockS mode fe nP block
  else throw (.invalid "number of parameters mismatch")

/-- **A declaration's own checks** (`checkDeclKind`'s twin), every kind (inductive blocks reuse
the `Expr`-level drivers).  `pins` is the `Nat.div`/`Nat.mod` pin-variant list the gate tries
(task #304), threaded from the fold.

**The pinned arms push last.**  A pinned `Nat`-operation definition and
a `reduce*` opaque are certified against the environment before the
push (`fe`) AND after it.  Holding both alive across a push would copy
the whole index, so the value check returns the record unpushed
(`checkDefnValCI`, `checkOpaqueValCI`), the "after" environment is an
overlay sharing `fe`'s index (`FEnv.overlay`, read-only; it answers
`find?` as the push would, `find?_overlay_push`), and the push comes
last, onto an index nothing else holds. -/
def checkDeclKindC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    checkConstantValC mode fe cv true
    let ci ← checkDefnValCI mode fe cv value hint
    if natOpNames.contains cv.name then
      let fe2 := fe.overlay [ci]
      unless natOpGuardF fe2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOkF fe2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match fe2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs (sharedOpsC mode fe) fe.env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal
          s!"structural Nat operation not stored ({cv.name})")
    if natDivModNames.contains cv.name then
      checkDivModPinF (sharedOpsC mode fe) pins fe (fe.overlay [ci]) cv.name
    pure (fe.push ci)
  | .thmDecl cv value => do
    checkConstantValC mode fe cv
    let ci ← checkThmValCI mode fe cv value
    pure (fe.push ci)
  | .opaqueDecl cv value => do
    checkConstantValC mode fe cv
    let ci ← checkOpaqueValCI mode fe cv value
    if reduceOpNames.contains cv.name then
      checkReducePinF (sharedOpsC mode fe) fe (fe.overlay [ci]) cv.name value
    pure (fe.push ci)
  | .axiomDecl cv =>
    if cv.name = quotSoundName then
      checkQuotRecordC fe .sound cv
    else do
      checkConstantValC mode fe cv
      if stdAxiomOkF fe cv then
        pure (fe.push (.axiomInfo cv))
      else if cv.name = trustCompilerName then
        if trustCompilerOkF fe cv then
          pure (fe.push (.axiomInfo cv))
        else throw (.notImplemented
          s!"unsupported Lean.trustCompiler shape ({cv.name})")
      else if cv.name = ofReduceNatName ∨ cv.name = ofReduceBoolName then
        if ofReduceAxOkF fe cv then
          pure (fe.push (.axiomInfo cv))
        else throw (.notImplemented
          s!"unsupported compiler-trust axiom environment ({cv.name})")
      else if cv.name = propextName ∨ cv.name = choiceName then
        throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
      else if cv.name = sorryAxName then
        pure fe
      else
        throw (.notImplemented (nonStdAxiomMsg cv.name))
  | .indDecl block nP => checkIndDeclC mode fe block nP
  | .quotDecl k cv => checkQuotRecordC fe k cv

/-- **One declaration** (`checkDecl`'s twin): its own checks, then the reserved names'. -/
def checkDeclC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv := do
  let fe₂ ← checkDeclKindC mode pins fe pd
  unless basisNamesOk pd do
    throw (basisNamesError pd)
  pure fe₂

/-! ## Names and durations for the driver's messages -/

/-- Milliseconds as `s.d` seconds (`12345` ↦ `"12.3"`).  `Nat`
arithmetic — no `Float` formatting on a message path. -/
def msSecs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

/-- A parsed declaration's display label (`ConLeche.Driver.declCName`,
shared with the driver's progress callback so the two can never
drift). -/
def declCLabel : Declaration → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b _ => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .quotDecl _ cv => s!"quot {cv.name}"

/-- The check of one record: flush, then check. -/
def checkDeclStepC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv := do
  flushC
  checkDeclC mode pins fe pd

end ConLeche.Cached
