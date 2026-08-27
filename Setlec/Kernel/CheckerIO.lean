import Setlec.Kernel.CheckerS
import Setlec.Kernel.CoreIO

/-!
# The infer-only declaration drivers (task #134, `SETLEC_INFER_ONLY`)

The parsed-index drivers of `Setlec/Kernel/CheckerS.lean` with the
core knot `coreKnotI` replaced by the checking-mode knot `coreKnotF`
(`Setlec/Kernel/CoreIO.lean`): the front door still infers in checking
mode — the per-argument application re-check runs on the declaration's
own type and value, and propagates down the term — while every
inference *reduction* and *definitional equality* perform internally
is infer-only.

**Scope.**  Only the def/thm/opaque value pipeline runs on this stack.
The install-only kinds (axioms, quotient/basis blocks, inductive
blocks) and the two rare pinned-certificate branches (the structural
Nat operations and the reduce pins) fall through to the *shared,
fully certified* `checkDeclSPPlain`: they are install-time, bounded,
and it is cheaper to keep them exactly as they are than to mirror
them.  A declaration therefore runs on exactly one of the two stacks,
and `checkDeclSPStepIO`'s per-declaration flush keeps the shared memos
from carrying a result of one mode into the other.

**Not verified.**  The consistency statements are about the default
drivers (`checkDeclsSP`); with the flag on the argument is
reference-kernel parity, see the header of `Setlec/Kernel/CoreIO.lean`.
-/

namespace Setlec

/-- `opSIx` at the checking-mode knot. -/
def opSIxIO (fe : FEnv) (d : Nat) (i : EIdx) : CheckIM Level := do
  let u ← ensureSortI (coreKnotF fe checkFuel) d i
  readbackLevelM u

/-- `checkConstantValP` at the checking-mode knot. -/
def checkConstantValPIO (fe : FEnv) (cv : ConstantValP) :
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
  let jty ← (coreKnotF fe checkFuel).annotate 0 cv.type
  unless ← withStore (fun st => st.allLevelParamsDefinedI cv.levelParams jty) do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless ← withStore (fun st => constsResolveFI st fe jty) do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotF fe checkFuel).infer 0 jty
  let _u ← opSIxIO fe 0 jsty
  let tyE ← readbackEM jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `closeDiscardM` for this stack: the checking-mode inference memo
carries arena indices too, so it goes with the others. -/
def closeDiscardMIO : CheckIM Unit := do
  flushInferFC
  closeDiscardM

/-- `closeSnapshotM` for this stack (as `closeDiscardMIO`). -/
def closeSnapshotMIO (jv : EIdx) : CheckIM EIdx := do
  flushInferFC
  closeSnapshotM jv

/-- `bracketValB4` at the checking-mode knot. -/
def bracketValB4IO (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM (Expr × EIdx × Bool) := do
  openSnapshotM
  let jv ← (coreKnotF fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE ← readbackEM jv
  let jvt ← (coreKnotF fe checkFuel).infer 0 jv
  let ok ← (coreKnotF fe checkFuel).defeq 0 jvt jty
  let jv' ← closeSnapshotMIO jv
  pure (vE, jv', ok)

/-- `checkDefnValPB4` at the checking-mode knot. -/
def checkDefnValPB4IO (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) (hint : ReducibilityHint) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let (vE, jv', ok) ← bracketValB4IO fe cvA jty value
  unless ok do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  recordIConst cvA.name cvA.type jty (some (vE, jv'))
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValPB4` at the checking-mode knot. -/
def checkThmValPB4IO (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  let jsty ← (coreKnotF fe checkFuel).infer 0 jty
  let ul ← opSIxIO fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let (vE, jv', ok) ← bracketValB4IO fe cvA jty value
  unless ok do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  recordIConst cvA.name cvA.type jty (some (vE, jv'))
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValPB4` at the checking-mode knot. -/
def checkOpaqueValPB4IO (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  openSnapshotM
  let jv ← (coreKnotF fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let jvt ← (coreKnotF fe checkFuel).infer 0 jv
  let ok ← (coreKnotF fe checkFuel).defeq 0 jvt jty
  closeDiscardMIO
  unless ok do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  recordIConst cvA.name cvA.type jty none
  pure (fe.push (.axiomInfo cvA))

/-- `checkDeclSP` on this stack: the def/thm/opaque value pipeline runs
infer-only; everything else falls through to the shared certified
driver (see the scope note in the header). -/
def checkDeclSPIO (fe : FEnv) (pd : DeclP) : CheckIM FEnv :=
  match pd with
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
      checkDeclSPPlain fe pd
    else do
      let (cvA, jty) ← checkConstantValPIO fe cv
      checkDefnValPB4IO fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValPIO fe cv
    checkThmValPB4IO fe cvA jty value
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then
      checkDeclSPPlain fe pd
    else do
      let (cvA, jty) ← checkConstantValPIO fe cv
      checkOpaqueValPB4IO fe cvA jty value
  | _ => checkDeclSPPlain fe pd

/-- `checkDeclSPStep` on this stack: the per-declaration flush drops
the checking-mode inference memo alongside the shared ones, so no
result of either mode survives an environment transition. -/
def checkDeclSPStepIO (n0 : Nat) (fe : FEnv) (pd : DeclP) : CheckIM FEnv := do
  unless pd.inRangeB n0 do
    throw (.internal "parsed declaration index out of range")
  flushS
  flushInferFC
  checkDeclSPIO fe pd

/-- `checkDeclsSP` on this stack. -/
def checkDeclsSPIO (st : WFStore) (pds : List DeclP) : CheckM Env := do
  let fe ← (pds.foldlM (checkDeclSPStepIO (st.raw.nodes.size + st.raw.nodes.size))
    (mkFEnv Env.empty)).run' { store := st.raw }
  pure fe.env

end Setlec
