import Setlec.Kernel.CheckerS

/-!
# The split install/check driver (task #108)

**Unverified debug path.**  The verified drivers
(`Setlec/Kernel/CheckerS.lean`) interleave installation and checking:
each declaration is checked against the environment as it stood before
it and then pushed.  That is the only shape the consistency chain
(`Setlec/Model/ConsistencyP.lean`) covers, and it is what the binary
runs by default.

For *investigating* a large stream the interleaving is a nuisance: to
reach declaration 40 000 you must re-check the 39 999 before it.  This
file splits the two phases:

* **install** (`installDeclSPStep`) — the syntactic guards, the
  annotation, the recording of the annotated indices
  (`IState.ienv`) and the environment push; every `infer`/`defeq`/
  `ensureSort` call — the conformance checking — is skipped.  For
  inductive blocks, basis blocks and axioms, installation and checking
  are *not* separable (their pins and positivity conditions are
  validated as they are installed), so those kinds run the ordinary
  `checkDeclSP`.
* **check** (`recheckDeclSPStep`) — the conformance phase of one
  declaration, run against the *final* environment restricted to what
  had been installed before that declaration
  (`FEnv.restrictTo`).  This is where the counters earn their keep: a
  restricted `FEnv` answers exactly as the environment truncated to
  that prefix would (`Setlec/Verify/EnvBound.lean`,
  `mkFEnv_find?_visibleBelow`), so nothing installed later can justify
  an earlier declaration.

Every environment consultation the check phase performs goes through
`FEnv.find?` and is therefore bounded: the `Env` arguments threaded to
`CheckerOps` methods are inert under `sharedOps` (which always uses the
`fe` it was built with), and `IState.ienv` is only ever reached *after*
a successful `fe.find?` and is pointer-validated against the constant
that lookup returned.

Because a split run checks less than the whole stream, a successful run
is a **decline** (exit 2), never an acceptance — see `Main.lean`.
-/

namespace Setlec

variable (mode : CheckMode)

/-! ## Install phase -/

/-- Declarations carrying a pinned environment condition and a
certificate: the structural-`Nat` operations, the div/mod family and
the `reduce*` opaques (`checkDeclSPPlain`'s cert branches).  Both the
guards and the certificates are check phase here — they consult the
environment and run `annotate`/`inferType`/`isDefEq` — so they are
replayed by `recheckDeclSP`, at the *same two views* the interleaved
driver used: the declaration's prefix and that prefix plus the
declaration itself (`FEnv.restrictTo k` and `restrictTo (k+1)`; the
two coincide with the interleaved `fe`/`fe2` by
`restrictTo_push_find?`). -/
def pinnedDeclP : DeclP → Bool
  | .defnDecl cv _ _ =>
    natOpNames.contains cv.name || natDivModNames.contains cv.name
  | .opaqueDecl cv _ => reduceOpNames.contains cv.name
  | _ => false

/-- `checkConstantValP` without its check phase: the duplicate/reserved
name guards, the syntactic passes, the annotation and the post-annotate
guards.  The "the stated type is a type" test (`infer` + `ensureSort`)
is conformance checking and moves to `recheckDeclSP`. -/
def installConstantValP (fe : FEnv) (cv : ConstantValP) :
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
  let jty ← (coreKnotI mode fe checkFuel).annotate 0 cv.type
  unless ← withStore (fun st => st.allLevelParamsDefinedI cv.levelParams jty) do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless ← withStore (fun st => constsResolveFI st fe jty) do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let tyE ← readbackEM jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- The install phase of a declaration value: the syntactic guards, the
annotation under the per-declaration snapshot bracket and the readback
of the stored form.  No conformance check. -/
def installValueP (fe : FEnv) (cvA : ConstantVal) (value : EIdx) :
    CheckIM (Expr × EIdx) := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  openSnapshotM
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  let jv' ← closeSnapshotM jv
  pure (vE, jv')

/-- Install one parsed declaration without checking it.  The kinds
whose installation *is* their check (axioms with their pinned
environment conditions, inductive blocks, basis blocks) run the
ordinary driver. -/
def installDeclSP (fe : FEnv) (pd : DeclP) : CheckIM FEnv := do
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← installConstantValP mode fe cv
    let (vE, jv) ← installValueP mode fe cvA value
    recordIConst cvA.name cvA.type jty (some (vE, jv))
    pure (fe.push (.defnInfo cvA vE hint))
  | .thmDecl cv value => do
    let (cvA, jty) ← installConstantValP mode fe cv
    let (vE, jv) ← installValueP mode fe cvA value
    recordIConst cvA.name cvA.type jty (some (vE, jv))
    pure (fe.push (.thmInfo cvA vE))
  | .opaqueDecl cv value => do
    let (cvA, jty) ← installConstantValP mode fe cv
    let _ ← installValueP mode fe cvA value
    recordIConst cvA.name cvA.type jty none
    pure (fe.push (.axiomInfo cvA))
  | .axiomDecl _ | .indDecl _ | .basisDecl _ => checkDeclSP mode fe pd

/-- One install step: the parse-range validation and cache flush of
`checkDeclSPStep`, then the install. -/
def installDeclSPStep (n0 : Nat) (fe : FEnv) (pd : DeclP) : CheckIM FEnv := do
  unless pd.inRangeB n0 do
    throw (.internal "parsed declaration index out of range")
  flushS
  installDeclSP mode fe pd

/-! ## Check phase

The conformance calls of one declaration, replayed against the
restricted environment.  The annotated type and value indices are the
ones the install phase recorded (`IState.ienv`), so nothing is
re-annotated except an opaque's discarded realizability witness (which
is never stored). -/

/-- The interned-environment entry of an installed constant. -/
def ienvEntry? (n : Name) : CheckIM (Option IConstE) :=
  modifyGet fun s => (s.ienv[n]?, s)

/-- The "the stated type is a type" check, on the recorded annotated
type. -/
def recheckTypeP (fe : FEnv) (jty : EIdx) : CheckIM Level := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  opSIx mode fe 0 jsty

/-- Conformance of a recorded value against its recorded type. -/
def recheckValueP (fe : FEnv) (n : Name) (jty jv : EIdx) : CheckIM Unit := do
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in {n}")

/-- The pinned-name certificate branches of `checkDeclSPPlain`,
replayed at the declaration's two install-time views: `fe` is the
prefix before it, `fe2` the prefix including it. -/
def recheckPinsP (fe fe2 : FEnv) (pd : DeclP) : CheckIM Unit := do
  match pd with
  | .defnDecl cv _ _ => do
    if natOpNames.contains cv.name then
      unless natOpGuardF fe2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOkF fe2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match fe2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs (sharedOps mode fe) fe.env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal
          s!"structural Nat operation not stored ({cv.name})")
    if natDivModNames.contains cv.name then
      checkDivModPinF (sharedOps mode fe) fe fe2 cv.name
  | .opaqueDecl cv value => do
    if reduceOpNames.contains cv.name then do
      let vE ← readbackEM value
      checkReducePinF (sharedOps mode fe) fe fe2 cv.name vE
  | _ => pure ()

/-- The check phase of one declaration.  `fe` must already be restricted
to the declaration's install-time prefix `k`; the pinned-certificate
branches additionally need the view including the declaration itself,
which is the same index at the bound `k + 1`. -/
def recheckDeclSP (fe : FEnv) (k : Nat) (pd : DeclP) : CheckIM Unit := do
  match pd with
  | .defnDecl cv _ _ => do
    match ← ienvEntry? cv.name with
    | some ⟨_, jty, some (_, jv)⟩ => do
      let _u ← recheckTypeP mode fe jty
      recheckValueP mode fe cv.name jty jv
    | _ => throw (.internal s!"not installed: {cv.name}")
    if pinnedDeclP pd then recheckPinsP mode fe (fe.restrictTo (k + 1)) pd
  | .thmDecl cv _ => do
    match ← ienvEntry? cv.name with
    | some ⟨_, jty, some (_, jv)⟩ => do
      let ul ← recheckTypeP mode fe jty
      unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
        throw (.invalid s!"type of theorem {cv.name} is not a proposition")
      recheckValueP mode fe cv.name jty jv
    | _ => throw (.internal s!"not installed: {cv.name}")
  | .opaqueDecl cv value => do
    match ← ienvEntry? cv.name with
    | some ⟨_, jty, _⟩ => do
      let _u ← recheckTypeP mode fe jty
      -- an opaque's value is not stored, so it is re-annotated here
      openSnapshotM
      let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
      let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
      let ok ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty
      closeDiscardM
      unless ok do
        throw (.invalid s!"type mismatch in opaque {cv.name}")
    | none => throw (.internal s!"not installed: {cv.name}")
    if pinnedDeclP pd then recheckPinsP mode fe (fe.restrictTo (k + 1)) pd
  | .axiomDecl cv => do
    match ← ienvEntry? cv.name with
    | some ⟨_, jty, _⟩ => do
      let _u ← recheckTypeP mode fe jty
    -- a tolerated axiom is skipped at install, so there is nothing to
    -- re-check
    | none => pure ()
  | .indDecl _ | .basisDecl _ =>
    -- fully checked as they were installed
    pure ()

/-- One check step: flush the environment-dependent caches (the bound
changed, so every cached lookup is stale) and run the check phase at the
declaration's install-time prefix. -/
def recheckDeclSPStep (fe : FEnv) (k : Nat) (pd : DeclP) : CheckIM Unit := do
  flushS
  recheckDeclSP mode (fe.restrictTo k) k pd

end Setlec
