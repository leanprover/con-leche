import Setlec.Kernel.Direct.InstallF
import Setlec.Kernel.Direct.SumInstall

/-!
# The direct sum install, through the index

`checkDirectSum`'s stages (`Setlec/Kernel/Direct/SumInstall.lean`)
over an `FEnv`, the mirrors the cached drivers run.
-/

namespace Setlec

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `directSumNonRec` through the index. -/
def directSumNonRecF (fe : FEnv) (p : DirectSumParts) : Bool :=
  p.ctors.all fun c =>
    match c.1.type.stripPis (p.nP + c.2) with
    | some (cbs, _) => cbs.all fun b => b.2.1.constsResolveF fe
    | none => false

/-- `directSumParts?` through the index. -/
def directSumPartsF? (fe : FEnv) (block : List ConstantInfo) :
    Option DirectSumParts :=
  match directSumPartsCore? block with
  | some p => if directSumNonRecF fe p then some p else none
  | none => none

/-- `checkDirectSumInd` through the index. -/
def checkDirectSumIndF (ops : CheckerOps m) (fe : FEnv) (p : DirectSumParts) :
    m (FEnv × ConstantVal) := do
  let cvTa ← checkConstantValF ops fe p.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (p.nP + p.nIdx))
    (.notImplemented "direct sum: type former telescope")
  unless tbody == Expr.sort p.resSort do
    throw (.notImplemented "direct sum: type former result sort")
  pure (fe.push (.indInfo cvTa (directSumCaps p)), cvTa)

/-- `checkDirectFieldSortsI` through the index. -/
def checkDirectFieldSortsIF (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkDirectFieldSortsIF ops fe isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- `checkDirectFieldSortsIF` over an array of field variables (the
callers convert once).  Equal to it at `List.toArray`:
`checkDirectFieldSortsIFA_eq`. -/
def checkDirectFieldSortsIFA (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : Array Expr) (idxArgs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkDirectFieldSortsIFA ops fe isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- `checkDirectSumCtor` through the index. -/
def checkDirectSumCtorF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m ConstantVal := do
  let cvCa ← checkConstantValF ops fe cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "direct sum: constructor telescope")
  unless directCtorResidOk T lps nP nF nIdx cbody do
    throw (.notImplemented "direct sum: constructor result")
  let cq ← unwrapOr (openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkDirectDomsAtFA ops fe 0 cq.1.toArray (tq.1.map Expr.fvarTypeD).toArray nP
  let xq ← unwrapOr (openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀ do
    throw (.notImplemented "direct sum: field domain after the block")
  unless (xq.2.getAppArgs.drop nP).all fun e => e.constsResolveF fe₀ do
    throw (.invalid "direct sum: index expression mentions the block")
  let _sorts ← checkDirectFieldSortsIFA ops fe isProp large resSort nP xq.1.toArray
    (xq.2.getAppArgs.drop nP) nF
  pure cvCa

/-- `checkDirectSumCtors` through the index. -/
def checkDirectSumCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) : List (ConstantVal × Nat) → m (List (ConstantVal × Nat))
  | [] => pure []
  | c :: cs => do
    let cvCa ← checkDirectSumCtorF ops fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    let rest ← checkDirectSumCtorsF ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest)

/-- `consSumCtors` through the index. -/
def consSumCtorsF (nP : Nat) : List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | c :: cs, fe => consSumCtorsF nP cs (fe.push (.ctorInfo c.1 nP c.2))

/-- `checkDirectSumRules` through the index. -/
def checkDirectSumRulesF (ops : CheckerOps m) (fe : FEnv) (rlps : List Name)
    (T : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat)
    (tty : Expr) (ctors : List (Name × Nat × Expr)) : Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (directRecRhsI T lps elim large nP nIdx tty ctors j)
      (.internal "direct sum: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolveF fe &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct sum: recursor rule scoping")
    let _rhsTy ← ops.inferType fe.env 0 rhs
    let rest ← checkDirectSumRulesF ops fe rlps T lps elim large nP nIdx tty ctors k (j + 1)
    pure (rhs :: rest)

/-- `checkDirectSumRec` through the index. -/
def checkDirectSumRecF (ops : CheckerOps m) (fe : FEnv) (p : DirectSumParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := ctorsA.map fun c => (c.1.name, c.2, c.1.type)
  let recTy ← unwrapOr (directRecTyI T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct sum: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolveF fe &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct sum: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    -- a recognised block's recursor is derived, so a different type is
    -- INVALID input (task #181), not an unsupported shape
    throw (.invalid "direct sum: recursor type is not the generated one")
  let rhss ← checkDirectSumRulesF ops fe p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors ctors.length 0
  pure (⟨p.cvR.name, p.cvR.levelParams, recTy⟩, rhss)

end Mirrors

end Setlec
