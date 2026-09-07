import ConLeche.Kernel.Direct.InstallF
import ConLeche.Kernel.Direct.SumInstall

/-!
# The direct sum install, through the index

`checkDirectSum`'s stages (`ConLeche/Kernel/Direct/SumInstall.lean`)
over an `FEnv`, the mirrors the cached drivers run.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkDirectSumTele` through the index (task #195): the whnf loop
runs at the index's environment through the shared operations, the
re-check of the closed telescope is `checkConstantValF`. -/
def checkDirectSumTeleF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal) (n : Nat)
    (cvTa₀ : ConstantVal) : m (ConstantVal × Level) :=
  match cvTa₀.type.stripPis n with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ => do
    let (bs, s) ← whnfTelescope ops fe.env 0 n cvTa₀.type
    let cvTa ← checkConstantValF ops fe { cv with type := closeTelescope bs 0 (.sort s) }
    pure (cvTa, s)

/-- `checkDirectSumInd` through the index. -/
def checkDirectSumIndF (ops : CheckerOps m) (fe : FEnv) (p : DirectSumParts)
    (capsOf : DirectSumParts → IndCaps) :
    m (FEnv × ConstantVal × DirectSumParts) := do
  let cvTa₀ ← checkConstantValF ops fe p.cvT
  let (cvTa, s) ← checkDirectSumTeleF ops fe p.cvT (p.nP + p.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (p.nP + p.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  let p' := p.withSort s
  pure (fe.push (.indInfo cvTa (capsOf p')), cvTa, p')

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
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level) := do
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
  let sorts ← checkDirectFieldSortsIFA ops fe isProp large resSort nP xq.1.toArray
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- `checkDirectSumCtors` through the index. -/
def checkDirectSumCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkDirectSumCtorF ops fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2
      cvTa
    let (rest, srest) ← checkDirectSumCtorsF ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-- `consSumCtors` through the index. -/
def consSumCtorsF (nP : Nat) : List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | c :: cs, fe => consSumCtorsF nP cs (fe.push (.ctorInfo c.1 nP c.2))

end Mirrors

end ConLeche
