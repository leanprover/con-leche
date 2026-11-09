module

public import InLean.Inductives.BlockShape
public import InLean.Push

/-!
# InLean's inductive check: the formers, the constructors, the tables

Twins of the executed stages of `ConLeche.Kernel.Inductives.SumInstall`,
`ConLeche.Kernel.Inductives.SumInstallF`, `ConLeche.Kernel.Inductives.StructParts`, `ConLeche.Kernel.Inductives.StructInstallF`,
`ConLeche.Kernel.Inductives.BlockInstall` and `ConLeche.Kernel.Inductives.BlockInstallF`, and of
`ConLeche.Kernel.DeclCheck`'s `checkConstantValF`.

An environment push records a Lean entry: a former as an `InductiveVal`
whose `all`, counts, constructors and `isRec` are the block's (what
`blockCapsAt` stores, read back by `FEnv.indView?`), a constructor as a
`ConstructorVal` with its counts, a rule-less recursor as a `RecursorVal`
whose counts encode `(mI, rP)` (`numParams := rP`, `numIndices := mI - rP`).
-/

@[expose] public section

namespace InLean

open Lean

/-- Twin of `checkConstantValF`; the name's freshness read off the environment
itself, as official's `check_name` (`FEnv.find?` hides constants a check does
not see). -/
def checkConstantValF (ops : CheckerOps) (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.env.find? cv.name).isSome then throw (alreadyDeclared cv.name)
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk cv.name cv.levelParams cv.type do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless namesNodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  checkTermWF fe s!"type of {cv.name}" cv.levelParams cv.type
  let stype ← ops.inferType fe 0 cv.type
  let _u ← ops.ensureSort fe 0 stype

/-! ## Structure parts (twin of `ConLeche.Kernel.Inductives.StructParts`) -/

/-- Twin of `structPsAt`. -/
def structPsAt (o nP : Nat) : List Expr :=
  (List.range nP).map fun k => mkBvar (o + nP - 1 - k)

/-- Twin of `structElimLevel`. -/
def structElimLevel (elim : Name) (large : Bool) : Level :=
  if large then .param elim else .zero

/-- Twin of `structCtorResidOk`. -/
def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFnT == .const T (lps.map .param) &&
  cbody.getAppNumArgsT == nP + nIdx &&
  (appArgs cbody).take nP == structPsAt o nP

/-- Twin of `Expr.mentionsConst` (`mentionsAnyConstC` at one name). -/
def mentionsConst (T : Name) (e : Expr) : CheckCM Bool := mentionsAnyConst [T] e

/-! ## Sums (twins of `ConLeche.Kernel.Inductives.SumInstall`, `ConLeche.Kernel.Inductives.SumInstallF`) -/

/-- Twin of `checkSumTele`. -/
def checkSumTele (n : Nat) (cvTa₀ : ConstantVal) : CheckCM (ConstantVal × Level) :=
  match (stripPis n cvTa₀.type).map (fun (p : List Expr × Expr) => EO.stripTop p.2) with
  | some (.sort s) => pure (cvTa₀, s)
  | _ => throw (.invalid "direct sum: type former does not reduce to a sort after its \
      parameters and indices")

/-- Twin of `checkStructFieldSortsIC`. -/
def checkStructFieldSortsIC (ops : CheckerOps) (fe : FEnv) (isProp large : Bool) (s : Level)
    (nP : Nat) (fvs idxArgs : List Expr) : Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe (nP + j) (← fvarTypeD fv)
    let u ← ops.ensureSort fe (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Lvl.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Lvl.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    checkStructFieldSortsIC ops fe isProp large s nP fvs idxArgs j

/-- Twin of `checkStructFieldSortsC`: `checkStructFieldSortsIC` over an array of field
variables. -/
def checkStructFieldSortsC (ops : CheckerOps) (fe : FEnv) (isProp large : Bool) (s : Level)
    (nP : Nat) (fvs : Array Expr) (idxArgs : List Expr) : Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe (nP + j) (← fvarTypeD fv)
    let u ← ops.ensureSort fe (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Lvl.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Lvl.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    checkStructFieldSortsC ops fe isProp large s nP fvs idxArgs j

/-- Twin of `checkStructDomsAtC`, over arrays. -/
def checkStructDomsAtF (ops : CheckerOps) (fe : FEnv) (off : Nat) (fvs doms : Array Expr) :
    Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe (off + j) (← fvarTypeD a) b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtF ops fe off fvs doms j

/-- Twin of `checkSumCtorC`. -/
def checkSumCtorC (ops : CheckerOps) (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    CheckCM Unit := do
  checkConstantValF ops fe cvC
  let (_, cbody) ← unwrapOr (stripPis (nP + nF) cvC.type)
    (.notImplemented "direct sum: constructor telescope")
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (← openPisAtFvars nP cvC.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvars nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAtF ops fe 0 cq.1.toArray (← tq.1.mapM fvarTypeD).toArray nP
  let xq ← unwrapOr (← openPisAtFvars nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  let args := appArgs xq.2
  unless xq.2.getAppFnT == Expr.const T (lps.map .param) &&
      args.take nP == cq.1 && args.length == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  let fieldsOk ← xq.1.allM fun x => do constsResolveF fe₀ (← fvarTypeD x)
  unless fieldsOk do
    throw (.notImplemented "direct sum: field domain after the block")
  unless ← (args.drop nP).allM (constsResolveF fe₀) do
    throw (.invalid "direct sum: index expression mentions the block")
  checkStructFieldSortsC ops fe isProp large resSort nP xq.1.toArray (args.drop nP) nF

/-- Twin of `checkSumCtorsC`. -/
def checkSumCtorsC (ops : CheckerOps) (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → CheckCM Unit
  | [] => pure ()
  | c :: cs => do
    checkSumCtorC ops fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    checkSumCtorsC ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs

/-- Twin of `consSumCtorsF`: each constructor pushed with its counts (its
family `T` and its position recorded as Lean's entry has them). -/
def consSumCtorsF (T : Name) (nP : Nat) : Nat → List (ConstantVal × Nat) → FEnv → FEnv
  | _, [], fe => fe
  | i, c :: cs, fe =>
    consSumCtorsF T nP (i + 1) cs
      (fe.push (.ctorInfo { toConstantVal := c.1, induct := T, cidx := i, numParams := nP,
                            numFields := c.2, isUnsafe := false }))

/-! ## Structures (twin of `ConLeche.Kernel.Inductives.StructInstallF`) -/

/-- Twin of `ProjTable`: a structure's projection table as the block's check
builds it.  InLean reads the tables off Lean's entries at use (`FEnv.findProj?`);
this one is built only to be checked. -/
structure ProjTable where
  structName : Name
  levelParams : List Name
  numParams : Nat
  ctor : Name
  numFields : Nat
  bodies : Array Expr
  deriving Inhabited

/-- Twin of `blockTablesC`: every structure member's table, its bodies by
`structProjBodies`. -/
def blockTables (p : BlockShape) : List MemberShape → Option (List ProjTable)
  | [] => some []
  | ms :: rest =>
    match ms.structCtor? with
    | some c =>
      (structProjBodies ms.declared.name p.nP c.2 c.1.type).bind fun bodies =>
        (blockTables p rest).map (⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩ :: ·)
    | none => blockTables p rest

/-- Twin of `checkStructProjTableC`.  A projection table is read off its
structure (`FEnv.findTable?`), so the "table taken" refusal has nothing to
find: the structure's name is fresh (`checkConstantValF`). -/
def checkStructProjTableC (t : ProjTable) (fe : FEnv) : CheckCM Unit := do
  unless t.bodies.size = t.numFields ∧ (← t.bodies.allM fun b => do
      pure (!b.hasFVar) <&&> allLevelParamsDefined t.levelParams b <&&> constsResolveF fe b <&&>
        pure (b.looseBVarRange ≤ t.numParams + 1)) do
    throw (.internal "direct structure: projection body scoping")
  unless (fe.find? t.structName).isSome do
    throw (.internal "direct structure: projection table before its structure")

/-- Twin of `checkBlockTablesC`. -/
def checkBlockTablesC (fe : FEnv) : List ProjTable → CheckCM Unit
  | [] => pure ()
  | t :: rest => do
    checkStructProjTableC t fe
    checkBlockTablesC fe rest

/-! ## The block (twins of `ConLeche.Kernel.Inductives.BlockInstall`, `ConLeche.Kernel.Inductives.BlockInstallF`) -/

/-- Twin of `Expr.piDomsMentionAny`. -/
def piDomsMentionAny (names : List Name) : Expr → Bool
  | .mdata _ e => piDomsMentionAny names e
  | .forallE _ ty b _ =>
    EO.any (fun | .const n _ => names.contains n | .proj s _ _ => names.contains s | _ => false) ty ||
      piDomsMentionAny names b
  | _ => false

/-- Twin of `blockIsRec`. -/
def blockIsRec (p : BlockShape) : Bool :=
  p.members.any fun ms => ms.ctors.any fun c => piDomsMentionAny p.memberNames c.1.type

/-- Twin of `checkBlockTeleC`. -/
def checkBlockTeleC (ops : CheckerOps) (fe : FEnv) (nP : Nat) (ms : MemberShape) :
    CheckCM (ConstantVal × Level) := do
  checkConstantValF ops fe ms.cvT
  let (cvTa, s) ← checkSumTele (nP + ms.nIdx) ms.cvT
  let (_, tbody) ← unwrapOr (stripPis (nP + ms.nIdx) cvTa.type)
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do throw (.internal "direct sum: type former result sort")
  pure (cvTa, s)

/-- Twin of `checkBlockTelesC`. -/
def checkBlockTelesC (ops : CheckerOps) (fe : FEnv) (nP : Nat) :
    List MemberShape → CheckCM (List (ConstantVal × Level))
  | [] => pure []
  | ms :: rest => do
    let r ← checkBlockTeleC ops fe nP ms
    let rs ← checkBlockTelesC ops fe nP rest
    pure (r :: rs)

/-- Twin of `checkBlockDomsAtC`. -/
def checkBlockDomsAtC (ops : CheckerOps) (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "block: domain index")
    let b ← unwrapOr doms[j]? (.internal "block: domain index")
    unless ← ops.isDefEq fe (off + j) (← fvarTypeD a) b do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtC ops fe off fvs doms j

/-- Twin of `checkBlockAgreeC`. -/
def checkBlockAgreeC (ops : CheckerOps) (fe : FEnv) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    List (ConstantVal × Level) → CheckCM Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq0 ← unwrapOr (← openPisAtFvars nP cvTa0.type 0) (.internal "block: type former telescope")
    let tq ← unwrapOr (← openPisAtFvars nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    unless tq.1.length == tq0.1.length do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtC ops fe 0 tq.1 (← tq0.1.mapM fvarTypeD) nP
    unless ← liftFueled "level comparison" (Lvl.isEquiv s s0) do
      throw (.invalid "mutually inductive types must live in the same universe")
    checkBlockAgreeC ops fe nP cvTa0 s0 rest

/-- Twin of `consBlockIndsF`: each former pushed as the entry `blockCapsAt`
reads back (`all`, counts, constructors, `isRec`). -/
def consBlockIndsF (p₁ : BlockShape) (isRec : Bool) : List ConstantVal → Nat → FEnv → FEnv
  | [], _, fe => fe
  | cvTa :: rest, i, fe =>
    let ms := p₁.members.getD i default
    let v : InductiveVal :=
      { toConstantVal := cvTa
        numParams := p₁.nP
        numIndices := ms.nIdx
        all := p₁.memberNames
        ctors := ms.ctors.map (·.1.name)
        numNested := 0
        isRec := isRec
        isUnsafe := false
        isReflexive := false }
    consBlockIndsF p₁ isRec rest (i + 1) (fe.push (.inductInfo v))

/-- The block's members as the job's environments mark them
(`FEnv.pending`): each pushed former's name. -/
def blockMarks (p : BlockShape) : List Name :=
  p.members.map (·.declared.name)

/-- Twin of `checkBlockIndsC`.  The formers are pushed onto `fe` marked with
the block (`blockMarks`): from here to the end of the job InLean reads the
members' capabilities and projection tables as master's staged
environments hold them. -/
def checkBlockIndsC (ops : CheckerOps) (fe : FEnv) (p : BlockShape) (isRec : Bool) :
    CheckCM (FEnv × BlockShape) :=
  match p.members with
  | [] => throw (.internal "block: no type former")
  | ms0 :: rest => do
    let (cvTa0, s0) ← checkBlockTeleC ops fe p.nP ms0
    let cvs ← checkBlockTelesC ops fe p.nP rest
    checkBlockAgreeC ops fe p.nP cvTa0 s0 cvs
    let p₁ := p.withSort s0
    pure (consBlockIndsF p₁ isRec (p.members.map (·.declared)) 0
      { fe with pending := blockMarks p₁ ++ fe.pending }, p₁)

/-- Twin of `checkBlockCtorsC`. -/
def checkBlockCtorsC (ops : CheckerOps) (fe₀ fe : FEnv) (p : BlockShape) :
    List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    checkSumCtorsC ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx p.resSort p.isProp p.large ms.cvT
      ms.ctors
    checkBlockCtorsC ops fe₀ fe p rest

/-- Twin of `checkBlockIdxSortsC`. -/
def checkBlockIdxSortsC (ops : CheckerOps) (fe₁ : FEnv) (p : BlockShape) :
    List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    let tq ← unwrapOr (← openPisAtFvars (p.nP + ms.nIdx) ms.cvT.type 0)
      (.internal "direct rec: type former telescope")
    checkStructFieldSortsIC ops fe₁ true false p.resSort p.nP (tq.1.drop p.nP) [] ms.nIdx
    checkBlockIdxSortsC ops fe₁ p rest

/-- Twin of `consBlockCtorsF`. -/
def consBlockCtorsF (p : BlockShape) : FEnv → FEnv :=
  fun fe => p.members.foldl (fun fe ms => consSumCtorsF ms.cvT.name p.nP 0 ms.ctors fe) fe

/-- A recursor entry at `(mI, rP)`, its rules and K flag. -/
def recEntry (p : BlockShape) (cv : ConstantVal) (mI rP : Nat) (isK : Bool)
    (rules : List RecursorRule) : ConstantInfo :=
  .recInfo { toConstantVal := cv, all := p.memberNames, numParams := rP, numIndices := mI - rP,
                     numMotives := 0, numMinors := 0, rules, k := isK, isUnsafe := false }

/-- Twin of `consBlockRecsBareF`. -/
def consBlockRecsBareF (p : BlockShape) : Nat → List (ConstantVal × Nat) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cvRa, _nIdx) :: rest, fe =>
    consBlockRecsBareF p (m + 1) rest
      (fe.push (recEntry p cvRa (p.majorIdxAt m) (p.rulePrefixAt m) false []))

end InLean
