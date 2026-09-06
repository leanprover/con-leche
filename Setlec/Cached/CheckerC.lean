import Setlec.Kernel.Direct.InstallF
import Setlec.Cached.CoreC

/-!
# The cached-clone declaration driver

The declaration checker *above* `CheckerOps` is shared verbatim with
the production checker: the pilot replaces the core, nothing else.
What is cloned here is exactly the thin `CheckIM`-pinned layer of
`Setlec/Kernel/CheckerS.lean` (the per-declaration shared-state phase
drivers) at the clone's monad, plus the entry-point record over the
cached core.

Task #172: the interned checker this was cloned from is gone, and with
it the `Expr`-typed shared fold (`checkDeclsShared`) that existed only
to make the two comparable.  What is left is the per-declaration phase
driver the parsed-declaration drivers
(`Setlec/Cached/Parsed{C,NC}.lean`) and their bridges consume.
-/

namespace Setlec.Cached

open Setlec

variable (mode : CheckMode)

/-! ## The entry-point record over the cached core

`opE`/`opB`/`opS` used to convert their `Expr` arguments in and their
results out, exactly as the interned `opE`/`opB`/`opS` intern and read
back at the same seam.  Since task #172 B3a there is one expression
type, so they pass their arguments through — measured at −3.5 % / −3.8 %
instructions on `init-prelude` / `app-lam`, which is where that batch's
win came from. -/

/-- Shared-state unary entry point: run the cached knot. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → ExprC → CheckCM ExprC)
    (d : Nat) (e : Expr) : CheckCM Expr := do
  pick (coreKnotI mode fe checkFuel) d e

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  (coreKnotI mode fe checkFuel).defeq d a b

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d e

/-- The per-declaration shared operations at a fixed environment
index (the clone's `sharedOps`). -/
def sharedOpsC (fe : FEnv) : CheckerOps CheckCM where
  annotate _ d e := opE mode fe (·.annotate) d e
  inferType _ d e := opE mode fe (·.infer) d e
  isDefEq _ d a b := opB mode fe d a b
  ensureSort _ d e := opS mode fe d e
  whnf _ d e := opE mode fe (·.whnf) d e


/-! ## Thin phase drivers (one interned state per declaration)

Each mirrors its `Setlec/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- One non-recursor member (mirrors `checkIndMember`). -/
def checkIndMemberS (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckCM FEnv := do
  flushC
  let cvA ← checkMemberValF (sharedOpsC mode fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group (mirrors `provisionRecs`). -/
def provisionRecsS (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckCM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushC
      let cvA ← checkMemberValF (sharedOpsC mode feAcc) blockNames feAcc
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
    (recs : List ConstantInfo) : CheckCM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsS mode blockNames fe₂ recs
    flushC
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- The public projection function for field `i` (mirrors
`checkProjFn`; the single-environment stages are the generic ones). -/
def checkProjFnS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckCM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckCM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckCM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckCM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOpsC mode fe) fe pty cvj lps nP nF i
  checkProjIotaF mode (sharedOpsC mode fe) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckCM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushC
    checkProjFnS mode fe T ctorName lps nP nF i
  else pure fe

/-- The Prop-fallback elimination-template table (mirrors
`installProjTemplate`; operation-free, lookups through the index). -/
def installProjTemplateS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) : CheckCM FEnv := do
  match fe.find? (T.str "rec") with
  | some (.recInfo _cvR mI rP [rule]) =>
    if (fe.find? (projTableName T)).isNone ∧
        mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧
        !(List.range nF).all (fun i => (fe.find? (projFnName T i)).isSome) then
      pure (fe.push (.projInfo ⟨T, lps, nP, ctorName, nF, .zero, Array.replicate nF (.sort .zero), [], false⟩))
    else pure fe
  | _ => pure fe

/-- `checkDirectStruct` through the index. -/
def checkDirectStructS (fe : FEnv) (p : DirectParts) : CheckCM FEnv := do
  -- one `flushC` per environment transition, as everywhere else in this
  -- file: the memo caches are only valid for the environment that
  -- created them, and this driver walks four of them (the block's
  -- provisional environments)
  flushC
  let (fe₁, cvTa) ← checkDirectIndF (sharedOpsC mode fe) fe p
  flushC
  let (fe₂, cvCa, sorts) ← checkDirectCtorF (sharedOpsC mode fe₁) fe fe₁ p cvTa
  flushC
  let cvRa ← checkConstantValF (sharedOpsC mode fe₂) fe₂ p.cvR
  checkDirectRecTyF (sharedOpsC mode fe₂) fe₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRuleF (sharedOpsC mode fe₂) fe₂ p cvCa cvRa
  let fe₃ := fe₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP,
      if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
        .plain else .inert,
      rhsA⟩])
  checkDirectProjTableF (m := CheckCM) p.cvT.name p.cvC.name p.cvT.levelParams
    p.nP p.nF p.resSort (directProjGuards cvCa.type p.nP p.nF sorts) cvCa fe₃

/-- The modeled inductive block (mirrors `checkIndDecl`), returning
the extended index. -/
def checkIndDeclSF (fe : FEnv) (block : List ConstantInfo) :
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
    installProjTemplateS fe₄ cvT.name cvC.name cvT.levelParams nP nF
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames {}) fe
    checkIndRecsS mode blockNames fe₂ recs

/-- One declaration in the shared state, index in and out (mirrors
`checkDecl` branch by branch; every lookup through the index). -/
def checkDeclSF (fe : FEnv) (d : Declaration) : CheckCM FEnv :=
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantValF (sharedOpsC mode fe) fe cv
    -- Rare Nat-op branch decided before the value check, so the common
    -- path does not retain `fe` across it (see `checkDeclSP`).
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
      let fe2 ← checkDefnValF (sharedOpsC mode fe) fe cv value hint
      if natOpNames.contains cv.name then
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
        checkDivModPinF (sharedOpsC mode fe) fe fe2 cv.name
      pure fe2
    else
      checkDefnValF (sharedOpsC mode fe) fe cv value hint
  | .thmDecl cv value => do
    let cv ← checkConstantValF (sharedOpsC mode fe) fe cv
    checkThmValF (sharedOpsC mode fe) fe cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantValF (sharedOpsC mode fe) fe cv
    let fe2 ← checkOpaqueValF (sharedOpsC mode fe) fe cv value
    if reduceOpNames.contains cv.name then
      checkReducePinF (sharedOpsC mode fe) fe fe2 cv.name value
    pure fe2
  | .axiomDecl cv => do
    let cvA ← checkConstantValF (sharedOpsC mode fe) fe cv
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

end Setlec.Cached
