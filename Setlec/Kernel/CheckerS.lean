import Setlec.Kernel.Checker
import Setlec.Kernel.DeclCheck
import Setlec.Kernel.DeclI
import Setlec.Kernel.WFStore
import Setlec.Kernel.Promote

/-!
# The shared-state declaration checker (task #51)

One interned state (`IState`, `Setlec/Kernel/CoreI.lean`) per
*declaration*: all checker operations within one `checkDecl` — the
annotate/infer/defeq/whnf calls of every phase — run in a single
`CheckIM` state, so the arena and the memo caches are shared across
entry calls instead of being rebuilt per call (`cachedOps`).

The environment is not constant within an inductive block
(`checkIndDecl`'s provisional environments), and cache entries are only
valid for the environment they were created under.  The discipline is
**driver-directed**: the thin drivers below mirror `checkDecl`'s
phase structure and call `flushS` at every environment transition —
the memo and lazy-constant caches are dropped, the *arena* (which is
environment-independent: denotations mention no environment) and the
name index survive.  There is no runtime environment comparison; the
adequacy of the flush points is what the bridge proves
(`Setlec/Verify/SimS.lean`, `Setlec/Verify/BridgeS*.lean`,
`Setlec.SetR.checkDeclsS_sound_R`).

The environment *index* (`FEnv`) is built once per declaration and
maintained across the provisional environments by `FEnv.push` — the
index of a cons-extended environment is one `HashMap.insert`
(`mkFEnv_push`), so the per-entry-call `mkFEnv` fold disappears.  The
recursor group keeps the `env₂` snapshot of the index and rebuilds the
final environments from it by pushes (the ruled recursors are installed
on `env₂`, not on the provisional `envSelf`).

Everything here is additive: `Setlec/Kernel/Checker.lean` (the generic
checker and its `cachedOps` instantiation) is untouched, and the
single-environment pieces are the *generic* checker functions
instantiated at `sharedOps` — only the phase structure is mirrored.
-/

namespace Setlec


variable (mode : CheckMode)


/-- Drop the memo and lazy stored-constant caches (an environment
transition).  The environment-independent components survive: the
arena, the interned environment (`ienv`, self-certified by denotation
tags), the loose-bvar-bound cache and the level-operation caches —
none of their invariants mention the environment.

The bulk-instantiation memo `instC` (task #145) is environment-
independent too, but it is dropped all the same: it is keyed by arena
indices, and this is the point at which the tier bracket may truncate
the arena (`Setlec/Verify/BracketB4.lean`), so its keys are exactly
what the close must not survive.  Bounding its size is a welcome side
effect. -/
def IState.flushed (s : IState) : IState :=
  { s with
      constTyAt := {}, constValAt := {}, ruleRhsAt := {},
      whnfCoreC := {}, whnfC := {}, inferC := {}, inferIOC := {},
      defeqC := {}, annotC := {}, instC := {} }

def flushS : CheckIM Unit :=
  modify (·.flushed)

/-- Shared-state unary entry point: intern into the ambient arena, run
the interned knot, read back.  Unlike `runEntryE` the state is the
ambient per-declaration state, not a fresh one. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → EIdx → CheckIM EIdx)
    (d : Nat) (e : Expr) : CheckIM Expr := do
  let i ← internExprM e
  let j ← pick (coreKnotI mode fe checkFuel) d i
  match ← withStore (fun st => st.readbackI j) with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckIM Bool := do
  let i ← internExprM a
  let j ← internExprM b
  (coreKnotI mode fe checkFuel).defeq d i j

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckIM Level := do
  let i ← internExprM e
  let u ← ensureSortI (coreKnotI mode fe checkFuel) d i
  readbackLevelM u

/-- The per-declaration shared operations at a fixed environment index.
The methods ignore the per-call environment argument: the drivers
instantiate the record only at `fe.env`, which is what the bridge
walks relate (there is no runtime check — the flush discipline is
proven adequate, not tested). -/
def sharedOps (fe : FEnv) : CheckerOps CheckIM where
  annotate _ d e := opE mode fe (·.annotate) d e
  inferType _ d e := opE mode fe (·.infer) d e
  isDefEq _ d a b := opB mode fe d a b
  ensureSort _ d e := opS mode fe d e
  whnf _ d e := opE mode fe (·.whnf) d e



/-! ## Thin phase drivers (one interned state per declaration)

Each mirrors its `Setlec/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushS` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- One non-recursor member (mirrors `checkIndMember`). -/
def checkIndMemberS (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckIM FEnv := do
  flushS
  let cvA ← checkMemberValF (sharedOps mode fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group (mirrors `provisionRecs`). -/
def provisionRecsS (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckIM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushS
      let cvA ← checkMemberValF (sharedOps mode feAcc) blockNames feAcc
        ci.toConstantVal
      let (feSelf, others) ← provisionRecsS blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- The recursor group (mirrors `checkIndRecs`).  All iota-rule checks
run at `envSelf` — one flush entering the phase, none inside the fold
(the fold's accumulator environments are never passed to the
operations).  The ruled recursors are installed on the `env₂` snapshot
of the index. -/
def checkIndRecsS (blockNames : List Name) (fe₂ : FEnv)
    (recs : List ConstantInfo) : CheckIM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsS mode blockNames fe₂ recs
    flushS
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF mode (sharedOps mode feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- The public projection function for field `i` (mirrors
`checkProjFn`; the single-environment stages are the generic ones). -/
def checkProjFnS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckIM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckIM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckIM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOps mode fe) fe pty cvj lps nP nF i
  checkProjIotaF mode (sharedOps mode fe) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushS
    checkProjFnS mode fe T ctorName lps nP nF i
  else pure fe

/-- The Prop-fallback elimination-template entry (mirrors
`installProjTemplate`; operation-free, lookups through the index). -/
def installProjTemplateS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  match fe.find? (T.str "rec") with
  | some (.recInfo cvR mI rP [rule]) =>
    if (fe.find? (projFnName T i)).isNone ∧
        mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧ i < nF then
      pure (fe.push (.projInfo ⟨T, i, lps, nP, ctorName, nF, .sort .zero,
        .zero, .zero, false,
        cvR.levelParams.length = lps.length + 1⟩))
    else pure fe
  | _ => pure fe

/-- One elimination-template install step (mirrors
`installProjTemplateStep`). -/
def installProjTemplateStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv :=
  if (fe.find? (projFnName T i)).isNone then
    installProjTemplateS fe T ctorName lps nP nF i
  else pure fe

/-- The projection fold of the direct install, with the constructor
residual `directProjResid T lps nP cvCa.type i` threaded alongside the
index (`todo` counts the remaining fields, `i` the current one): each
step consumes the residual for `i` and extends it by a **single**
`instantiate1Lift` — the earlier projections' substitutions are never
redone, which is what keeps wide structures out of the cubic
regime. -/
def checkDirectProjsS (T C : Name) (lps : List Name) (nP nF : Nat)
    (cvTa cvCa : ConstantVal) :
    (todo i : Nat) → Option Expr → FEnv → CheckIM FEnv
  | 0, _, _, fe => pure fe
  | todo + 1, i, rt?, fe => do
    flushS
    let fe' ← checkDirectProjF (sharedOps mode fe) T C lps nP nF cvTa cvCa
      rt? fe i
    checkDirectProjsS T C lps nP nF cvTa cvCa todo (i + 1)
      (rt?.bind (Expr.instPisAtLift [directProjArg T lps nP i])) fe'

/-- `checkDirectStruct` through the index. -/
def checkDirectStructS (fe : FEnv) (p : DirectParts) : CheckIM FEnv := do
  -- one `flushS` per environment transition, as everywhere else in this
  -- file: the memo caches are only valid for the environment that
  -- created them, and this driver walks five of them (the block's
  -- provisional environments plus one per projection).
  flushS
  let (fe₁, cvTa) ← checkDirectIndF (sharedOps mode fe) fe p
  flushS
  let (fe₂, cvCa) ← checkDirectCtorF (sharedOps mode fe₁) fe fe₁ p cvTa
  flushS
  let cvRa ← checkConstantValF (sharedOps mode fe₂) fe₂ p.cvR
  checkDirectRecTyF (sharedOps mode fe₂) fe₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRuleF (sharedOps mode fe₂) fe₂ p cvCa cvRa
  let fe₃ := fe₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP,
      if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
        .plain else .inert,
      rhsA⟩])
  unless (List.range p.nF).all
      (fun j => (fe₃.find? (projFnName p.cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  checkDirectProjsS mode p.cvT.name p.cvC.name p.cvT.levelParams p.nP p.nF
    cvTa cvCa p.nF 0
    (Expr.instPisAtLift (directProjPs p.nP) cvCa.type) fe₃

/-- The modeled inductive block (mirrors `checkIndDecl`), returning
the extended index. -/
def checkIndDeclSF (fe : FEnv) (block : List ConstantInfo) :
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
    let caps ← pure (indBlockCapsF mode fe cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
    let fe₃ ← checkIndRecsS mode blockNames fe₂ recs
    unless ctorResidualOkF mode fe₃ cvT.name cvC.name cvT.levelParams nP nF
        caps.eta do
      throw (.notImplemented "modeled structure: eta constructor residual")
    unless (List.range nF).all
        (fun j => (fe₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    let fe₄ ← (List.range nF).foldlM
      (installProjFnStepS mode cvT.name cvC.name cvT.levelParams nP nF)
      fe₃
    (List.range nF).foldlM
      (installProjTemplateStepS cvT.name cvC.name cvT.levelParams nP nF) fe₄
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames {}) fe
    checkIndRecsS mode blockNames fe₂ recs

/-- One declaration in the shared state, index in and out (mirrors
`checkDecl` branch by branch; every lookup through the index). -/
def checkDeclSF (fe : FEnv) (d : Declaration) : CheckIM FEnv :=
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantValF (sharedOps mode fe) fe cv
    -- Rare Nat-op branch decided before the value check, so the common
    -- path does not retain `fe` across it (see `checkDeclSP`).
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
      let fe2 ← checkDefnValF (sharedOps mode fe) fe cv value hint
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
      pure fe2
    else
      checkDefnValF (sharedOps mode fe) fe cv value hint
  | .thmDecl cv value => do
    let cv ← checkConstantValF (sharedOps mode fe) fe cv
    checkThmValF (sharedOps mode fe) fe cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantValF (sharedOps mode fe) fe cv
    let fe2 ← checkOpaqueValF (sharedOps mode fe) fe cv value
    if reduceOpNames.contains cv.name then
      checkReducePinF (sharedOps mode fe) fe fe2 cv.name value
    pure fe2
  | .axiomDecl cv => do
    let cvA ← checkConstantValF (sharedOps mode fe) fe cv
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
    | some p => checkDirectStructS mode fe p
    | none => checkIndDeclSF mode fe block

/-- The shared-state checker step the binary runs: the index is
threaded *across* declarations (built once for the whole stream; each
accepted constant is one `FEnv.push`), the interned state lives for
exactly one declaration. -/
def checkDeclSharedF (fe : FEnv) (d : Declaration) : CheckM FEnv :=
  (checkDeclSF mode fe d).run' {}

/-- The declaration fold of the shared-state checker. -/
def checkDeclsShared (ds : List Declaration) : CheckM Env := do
  let fe ← ds.foldlM (checkDeclSharedF mode) (mkFEnv Env.empty)
  pure fe.env

/-! ## The parsed-index drivers (task #78)

The frontend parses expression-table entries directly into the arena
(`Setlec/Frontend/Export.lean`); declarations arrive as `DeclP` — arena
indices instead of `Expr` trees — over the parse store, which seeds the
run's single `IState`.  The drivers below mirror the non-inductive
branches of `checkDeclSF` clause by clause, with

* the raw syntactic checks (`looseBVarsBounded`/`hasFvar`) and the
  post-annotate checks (`allLevelParamsDefined`/`constsResolveF`) run
  DAG-memoized on the arena,
* the entry operations called on indices (no per-entry tree interning),
* the accepted constant's annotated type/value *indices* recorded in
  the interned environment (`IState.ienv`), so later delta-unfoldings
  instantiate on the arena instead of re-interning read-back trees.

Inductive and basis blocks reuse the `Expr`-level drivers verbatim
(their inputs are read back at parse under the tree-size budget).
The state persists across declarations: `checkDeclsSP` runs the whole
fold in one `IState` seeded from the parse store, flushing the
environment-dependent caches at each declaration boundary. -/

/-- Parsed-index `ensureSort`: the interned entry plus the level
readback (the `opS` tail without the per-call tree interning). -/
def opSIx (fe : FEnv) (d : Nat) (i : EIdx) : CheckIM Level := do
  let u ← ensureSortI (coreKnotI mode fe checkFuel) d i
  readbackLevelM u

/-- Read back an interned expression (internal error on a dangling
index — never on the bridge invariant). -/
def readbackEM (i : EIdx) : CheckIM Expr := do
  match ← withStore (fun st => st.readbackI i) with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Record an accepted constant's interned type/value in the interned
environment.  The tags (`tyE`, the value tag) must be the very objects
pushed into the environment, so the pointer validation in
`constTyAtM`/`constValAtM` succeeds. -/
def recordIConst (n : Name) (tyE : Expr) (ty : EIdx)
    (val : Option (Expr × EIdx)) : CheckIM Unit :=
  modify fun s =>
    let m := s.ienv
    let s := { s with ienv := {} }
    { s with ienv := m.insert n ⟨tyE, ty, val⟩ }

/-- `checkConstantVal` on a parsed index: the checks of
`checkConstantValF` with the syntactic passes memoized on the arena and
the operations on indices.  Returns the annotated `ConstantVal` (type
read back once, for the environment) and the annotated type's index. -/
def checkConstantValP (fe : FEnv) (cv : ConstantValP) :
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
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let _u ← opSIx mode fe 0 jsty
  let tyE ← readbackEM jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValF` on parsed indices, recording the interned entry
(the value sequence is inlined flat so the simulation walk mirrors it
clause by clause).

**Task #64 driver split**: the body is ordered install-phase first —
the syntactic guards, the annotation, the post-annotate guards, and
the recording of the annotated indices (`readbackEM`/`recordIConst`,
state-only steps, moved before the conformance check) — then the
check phase (infer + defeq), which consumes the annotated indices and
produces nothing.  The environment push comes last, with `fe`
consumed in tail position; the check phase therefore runs against the
pre-push environment (the prefix view: this declaration is not
visible to its own conformance check), exactly as the pre-split
order did. -/
def checkDefnValP (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) (hint : ReducibilityHint) : CheckIM FEnv := do
  -- install phase: guards, annotation, recording
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  recordIConst cvA.name cvA.type jty (some (vE, jv))
  -- CHECK PHASE ENTRY (task #64: the two-tier bracket hooks here —
  -- everything below produces no stored artifact)
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  -- CHECK PHASE EXIT (the driver-level cert branches that follow in
  -- `checkDeclSP` are check-phase too; the bracket closes after them)
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValF` on parsed indices (split as `checkDefnValP`; the
is-a-proposition test stays install-side, preserving the pre-split
error order). -/
def checkThmValP (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIx mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  recordIConst cvA.name cvA.type jty (some (vE, jv))
  -- CHECK PHASE ENTRY (task #64 split, see `checkDefnValP`)
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  -- CHECK PHASE EXIT
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValF` on parsed indices (stored as an `axiomInfo`,
exactly as the `Expr`-level driver does — the checked value is a
discarded realizability witness, so no value index is recorded; split
as `checkDefnValP`). -/
def checkOpaqueValP (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordIConst cvA.name cvA.type jty none
  -- CHECK PHASE ENTRY (task #64 split, see `checkDefnValP`)
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  -- CHECK PHASE EXIT (the reduce-pin cert branch in `checkDeclSP` is
  -- check-phase too)
  pure (fe.push (.axiomInfo cvA))

/-- One parsed declaration on the *unbracketed* path (mirrors
`checkDeclSF` branch by branch; inductive/basis blocks reuse the
`Expr`-level drivers).  The default driver `checkDeclSP` dispatches
here for the install-only kinds and the rare pinned-cert branches
(task #64: their per-declaration temporaries are bounded); the
def/thm/opaque value pipeline runs under the tier-two snapshot
bracket instead. -/
def checkDeclSPPlain (fe : FEnv) (pd : DeclP) : CheckIM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValP mode fe cv
    -- The Nat-op certification branch is decided *before* checking the
    -- value: the pinned certifications intentionally run against the
    -- pre-push `fe`, so the rare branch must retain `fe` across
    -- `checkDefnValP` — but on the common path that retention would
    -- force the final `fe.push` to copy the whole index bucket array
    -- (a hidden quadratic cost, one copy per definition).  The common
    -- path is therefore a tail call with `fe` consumed.
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValP mode fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOps mode fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOps mode fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValP mode fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValP mode fe cv
    checkThmValP mode fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValP mode fe cv
    let fe2 ← checkOpaqueValP mode fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE ← readbackEM value
      checkReducePinF (sharedOps mode fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValP mode fe cv
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
    | some p => checkDirectStructS mode fe p
    | none => checkIndDeclSF mode fe block

/-! ## The per-declaration tier-two snapshot bracket (task #64)

THE default value pipeline: each def/thm/opaque value is annotated,
guarded, read back and conformance-checked with tier two enabled on
the linearly-threaded state; at the close the tier-two node table is
harvested, tier two truncated in place, the index-carrying memos
flushed, and the stored output's sub-DAG promoted into the retained
tier-one store (`Setlec/Kernel/Promote.lean`, index-memoized).  Levels
and names intern single-tier throughout and simply persist, so
promotion remaps only tier-two expression nodes (the level/name bases
are the harvest-time table sizes — every reference is below them and
kept).  Opaques store no value, so nothing is promoted.  Verified:
`Setlec/Verify/BracketB4.lean` (the seam theory and the driver walks),
consumed by the consistency chain at `Setlec.SetR.checkDeclsSP_sound_R`.
-/

/-- Promote a snapshot index into the ambient (retained) store. -/
def promoteM (h : Harvest) (lbase nbase : Nat) (e : EIdx) :
    CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.promoteE h lbase nbase e
    (r, { s with store := store })

/-- Open the per-declaration snapshot: enable tier two on the
linearly-threaded state (detach-before-update). -/
def openSnapshotM : CheckIM Unit :=
  modify fun s =>
    let st := s.store
    let s := { s with store := EStore.empty }
    { s with store := st.enableTierTwo }

/-- Close a snapshot discarding everything: truncate tier two in
place and flush the index-carrying memos (detach-before-update; the
level caches and the interned environment survive). -/
def closeDiscardM : CheckIM Unit :=
  modify fun s =>
    let st := s.store
    let s := { s with store := EStore.empty }
    let s := s.flushed
    { s with store := st.truncateTierTwo }

/-- In-place close for the annotate snapshot: harvest the tier-two
node table, truncate, flush the index-carrying memos, promote the
stored output. -/
def closeSnapshotM (jv : EIdx) : CheckIM EIdx := do
  let (tno, lsz, nsz) ← withStore
    (fun st => (st.tnodes, st.lnodes.size, st.nnodes.size))
  closeDiscardM
  promoteM ⟨tno, #[], #[]⟩ lsz nsz jv

/-- The shared bracketed middle of the def/thm value pipeline: under
the snapshot, annotate the value, run the post-annotate guards, read
the stored form back, infer and compare against the stated type; at
the close promote the annotated value's sub-DAG.  Returns the
readback, the promoted (tier-one) index and the conformance verdict —
the throw on a failed conformance is the caller's (after the close,
so the snapshot is released on both verdicts). -/
def bracketValB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM (Expr × EIdx × Bool) := do
  openSnapshotM
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  let ok ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty
  let jv' ← closeSnapshotM jv
  pure (vE, jv', ok)

/-- `checkDefnValP` with the in-place annotate-snapshot bracket. -/
def checkDefnValPB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) (hint : ReducibilityHint) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let (vE, jv', ok) ← bracketValB4 mode fe cvA jty value
  unless ok do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  recordIConst cvA.name cvA.type jty (some (vE, jv'))
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValP` with the in-place annotate-snapshot bracket. -/
def checkThmValPB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIx mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let (vE, jv', ok) ← bracketValB4 mode fe cvA jty value
  unless ok do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  recordIConst cvA.name cvA.type jty (some (vE, jv'))
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValP` with the in-place annotate-snapshot bracket
(nothing stored, nothing promoted). -/
def checkOpaqueValPB4 (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
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
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  let ok ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty
  closeDiscardM
  unless ok do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  recordIConst cvA.name cvA.type jty none
  pure (fe.push (.axiomInfo cvA))

/-- One parsed declaration, THE default driver (task #64): the
def/thm/opaque value pipeline runs under the per-declaration tier-two
snapshot bracket; the rare pinned-cert branches and the install-only
kinds run the unbracketed path (bounded content). -/
def checkDeclSP (fe : FEnv) (pd : DeclP) : CheckIM FEnv :=
  match pd with
  | .defnDecl cv value hint =>
    -- the pinned-name conditions depend only on the header name
    -- (`checkConstantValP` preserves it), so the rare cert branches
    -- dispatch before the header check and the unbracketed path runs
    -- it exactly once
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
      checkDeclSPPlain mode fe pd
    else do
      let (cvA, jty) ← checkConstantValP mode fe cv
      checkDefnValPB4 mode fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValP mode fe cv
    checkThmValPB4 mode fe cvA jty value
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then
      checkDeclSPPlain mode fe pd
    else do
      let (cvA, jty) ← checkConstantValP mode fe cv
      checkOpaqueValPB4 mode fe cvA jty value
  | _ => checkDeclSPPlain mode fe pd

/-- One step of the parsed-declaration fold: validate the indices
against the parse store's range (`O(1)`; in-range indices denote under
the store invariant), flush the environment-dependent caches, check. -/
def checkDeclSPStep (n0 : Nat) (fe : FEnv) (pd : DeclP) : CheckIM FEnv := do
  unless pd.inRangeB n0 do
    throw (.internal "parsed declaration index out of range")
  flushS
  checkDeclSP mode fe pd

/-- The parsed-declaration checker the binary runs: the parse arena
arrives well-formed *by construction* (`WFStore`, task #103 — there is
nothing left to validate), seeds the run's single interned state, and
the whole fold shares it (the arena, the interned environment and the
environment-independent caches persist; the environment-dependent
caches are flushed per declaration). -/
def checkDeclsSP (st : WFStore) (pds : List DeclP) : CheckM Env := do
  -- SCOUT (task #64 low-bit): `EIdx` bound is the encoded one.
  let fe ← (pds.foldlM (checkDeclSPStep mode (st.raw.nodes.size + st.raw.nodes.size))
    (mkFEnv Env.empty)).run' { store := st.raw }
  pure fe.env

end Setlec
