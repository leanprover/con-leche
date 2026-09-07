import ConLeche.Kernel.DeclCheck

/-!
# The direct simple-structure install, through the index

`checkDirectStruct`'s stages (`ConLeche/Kernel/Direct/Install.lean`)
over an `FEnv`, the mirrors the cached drivers run.  Extracted verbatim
from the tail of `ConLeche/Kernel/DeclCheck.lean` (its `Mirrors`
section) on 2026-09-06 (cleanup pass A).
-/

namespace ConLeche

variable (mode : CheckMode)

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ### The direct simple-structure path, through the index -/

/-- `directNonRec` through the index. -/
def directNonRecF (fe : FEnv) (p : DirectParts) : Bool :=
  match p.cvC.type.stripPis (p.nP + p.nF) with
  | some (cbs, _) => cbs.all fun b => b.1.constsResolveF fe
  | none => false

/-- `directParts?` through the index (the priority gate, task #175
W4c). -/
def directPartsF? (fe : FEnv) (block : List ConstantInfo) :
    Option DirectParts :=
  match directPartsCore? block with
  | some p => if directNonRecF fe p then some p else none
  | none => none

/-- `checkDirectFieldSorts` through the index. -/
def checkDirectFieldSortsF (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct structure: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct structure: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true do
        throw (.notImplemented
          "direct structure: large eliminator with a non-propositional field")
    let rest ← checkDirectFieldSortsF ops fe isProp large s nP fvs j
    pure (rest ++ [u])

/-- `checkDirectFieldSortsF` over an array (positional list indexing is
linear per access; the callers convert once).  Equal to it at
`List.toArray`: `checkDirectFieldSortsFA_eq`. -/
def checkDirectFieldSortsFA (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : Array Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct structure: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct structure: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true do
        throw (.notImplemented
          "direct structure: large eliminator with a non-propositional field")
    let rest ← checkDirectFieldSortsFA ops fe isProp large s nP fvs j
    pure (rest ++ [u])

/-- `checkDirectDomsAt` through the index. -/
def checkDirectDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAtF ops fe off fvs doms j

/-- `checkDirectDomsAtF` over arrays (see `checkDirectFieldUnivFA`).
Equal to it at `List.toArray`: `checkDirectDomsAtFA_eq`. -/
def checkDirectDomsAtFA (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : Array Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAtFA ops fe off fvs doms j

/-- `checkDirectInd` through the index. -/
def checkDirectIndF (ops : CheckerOps m) (fe : FEnv) (p : DirectParts) :
    m (FEnv × ConstantVal) := do
  let cvTa ← checkConstantValF ops fe p.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis p.nP)
    (.notImplemented "direct structure: type former telescope")
  unless tbody == Expr.sort p.resSort do
    throw (.notImplemented "direct structure: type former result sort")
  pure (fe.push (.indInfo cvTa (directCaps p)), cvTa)

/-- `checkDirectCtor` through the index. -/
def checkDirectCtorF (ops : CheckerOps m) (fe₀ fe : FEnv) (p : DirectParts)
    (cvTa : ConstantVal) : m (FEnv × ConstantVal × List Level) := do
  let cvCa ← checkConstantValF ops fe p.cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (p.nP + p.nF))
    (.notImplemented "direct structure: constructor telescope")
  unless cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF do
    throw (.notImplemented "direct structure: constructor result")
  let cq ← unwrapOr (openPisAtFvarsF p.nP cvCa.type 0)
    (.notImplemented "direct structure: constructor telescope")
  let tq ← unwrapOr (openPisAtFvarsF p.nP cvTa.type 0)
    (.notImplemented "direct structure: type former telescope")
  checkDirectDomsAtFA ops fe 0 cq.1.toArray
    (tq.1.map Expr.fvarTypeD).toArray p.nP
  let xq ← unwrapOr (openPisAtFvarsF p.nF cq.2 p.nP)
    (.notImplemented "direct structure: constructor field telescope")
  unless xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1 do
    throw (.notImplemented "direct structure: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀ do
    throw (.notImplemented "direct structure: field domain after the block")
  let sorts ← checkDirectFieldSortsFA ops fe p.isProp p.large p.resSort p.nP
    xq.1.toArray p.nF
  pure (fe.push (.ctorInfo cvCa p.nP p.nF), cvCa, sorts)

/-- `checkDirectRec` through the index (task #175 S2). -/
def checkDirectRecF (ops : CheckerOps m) (fe : FEnv) (p : DirectParts)
    (cvTa cvCa : ConstantVal) : m (ConstantVal × Expr) := do
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := [(p.cvC.name, p.nF, cvCa.type)]
  let recTy ← unwrapOr (directRecTy T lps p.elim p.large p.nP cvTa.type ctors)
    (.internal "direct structure: recursor type")
  let rhs ← unwrapOr (directRecRhs T lps p.elim p.large p.nP cvTa.type ctors 0)
    (.internal "direct structure: recursor rule")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolveF fe &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct structure: recursor type scoping")
  unless rhs.allLevelParamsDefined p.cvR.levelParams && rhs.constsResolveF fe &&
      rhs.looseBVarsBounded 0 && !rhs.hasFvar do
    throw (.internal "direct structure: recursor rule scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    throw (.notImplemented "direct structure: recursor type")
  let _rhsTy ← ops.inferType fe.env 0 rhs
  pure (⟨p.cvR.name, p.cvR.levelParams, recTy⟩, rhs)


/-- `checkDirectProjTable` through the index (task #175 S1). -/
def checkDirectProjTableF (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) (fe : FEnv) :
    m FEnv := do
  let bodies ← unwrapOr (directProjBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined lps && b.constsResolveF fe &&
      b.looseBVarsBounded (nP + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the projection-function name family (the modeled route's, the key
  -- of its η-family predicate) must be free too: a direct family has
  -- no projection functions, and the model's η law for the block is
  -- discharged by the tower, never by `EtaFamilyStored`
  unless (List.range nF).all (fun j => (fe.find? (projFnName T j)).isNone) do
    throw (.invalid "projection name family taken")
  unless (fe.find? (projTableName T)).isNone do
    throw (.invalid "projection table taken")
  pure (fe.push (.projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards, off⟩))

end Mirrors
