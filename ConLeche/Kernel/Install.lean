module

public import ConLeche.Kernel.Inductives.BlockInstall

@[expose] public section

/-!
# What a declaration installs

A declaration's constants and projection tables are a direct consequence of the declaration: this
file reads them off it, with no environment, no inference and no reduction.  The fold's step pushes
exactly this once the declaration's checks pass, and the parallel install pushes it before them.

A block the checks reject may still read as something here (a recursor whose major is not a
container reads as firing `.plain`, a structure whose constructor is too short has no table): what
it reads as never reaches an accepted environment.
-/

namespace ConLeche

/-- The environment with a declaration's constants and tables pushed, each list oldest first. -/
def Env.pushDelta (env : Env) (L : List ConstantInfo) (Q : List ProjTable) : Env :=
  ⟨L.reverse ++ env.consts, Q.reverse ++ env.tables⟩

/-- The formers, in block order, as declared, with the capabilities their block gives them. -/
def blockFormers (p : BlockShape) (isRec : Bool) : List ConstantInfo :=
  (p.members.map (·.declared)).zipIdx.map fun (cv, i) => .indInfo cv (blockCapsAt p i isRec)

/-- The constructors of every member, as declared, in block order. -/
def blockCtors (p : BlockShape) : List ConstantInfo :=
  p.allCtors.map fun c => .ctorInfo c.1 p.nP c.2

/-- `n` variables below a term's own, which do not occur in it, dropped. -/
def Expr.dropVars : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.dropVars n (e.instantiate1 (.sort .zero))

/-- **How a recursor's rules fire**: `.plain` at a member major; at a major outside the block,
`.nested` at the levels and parameters of the major's container.  Those are read off the major's
domain, whose arguments end in the `mI - rP` index variables; the parameters are moved from under
the index binders to the rule prefix. -/
def recFire (p : BlockShape) (rc : RecShape) : RecRuleFire :=
  if rc.tgt < p.k then .plain
  else
    match rc.cvR.type.stripPis rc.mI with
    | some (_, .forallE dom _) =>
      match dom.getAppFn with
      | .const _ us =>
        let nI := rc.mI - rc.rP
        let args := dom.getAppArgs
        .nested us ((args.take (args.length - nI)).map (Expr.dropVars nI))
      | _ => .plain
    | _ => .plain

/-- The recursors, in block order: each record with its rules' firing mode. -/
def blockRecs (p : BlockShape) : List RecShape → List ConstantInfo
  | [] => []
  | rc :: rest =>
    .recInfo rc.cvR rc.mI rc.rP rc.isK (rc.rules.map ({ · with fire := recFire p rc })) ::
      blockRecs p rest

/-- The projection tables, in block order: one per structure-like member. -/
def blockTables (p : BlockShape) : List MemberShape → List ProjTable
  | [] => []
  | ms :: rest =>
    match ms.structCtor? with
    | some c =>
      match structProjBodies ms.declared.name p.nP c.2 c.1.type with
      | some bodies =>
        ⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩ :: blockTables p rest
      | none => blockTables p rest
    | none => blockTables p rest

/-- The block's constants, in push order: the formers, the constructors, the recursors. -/
def blockConstants (p : BlockParts) : List ConstantInfo :=
  blockFormers p.toBlockShape (blockRawRec p) ++ blockCtors p.toBlockShape ++
    blockRecs p.toBlockShape p.recs

/-- **The constants a declaration installs**, in push order.  A block with a pinned block's names
installs the pin at the names the record declares, a block the recogniser does not read nothing
(it declines), and `sorryAx` nothing (any use of it declines). -/
def declConstants : Declaration → List ConstantInfo
  | .defnDecl cv value hint => [.defnInfo cv value hint]
  | .thmDecl cv _ => [.thmInfo cv]
  | .opaqueDecl cv _ => [.axiomInfo cv]
  | .axiomDecl cv =>
    if cv.name = quotSoundName then [quotAt .sound cv]
    else if cv.name = sorryAxName then []
    else [.axiomInfo cv]
  | .quotDecl k cv => [quotAt k cv]
  | .indDecl block nP =>
    match basisNameHit block with
    | some kind => kind.atBlock block
    | none =>
      match blockParts? nP block with
      | some p => blockConstants p
      | none => []

/-- The names a declaration installs, in push order: what the parallel install reserves slots at
before any declaration is installed. -/
def predictSlots (pd : Declaration) : Array Name :=
  ((declConstants pd).map (·.name)).toArray

/-- **The projection tables a declaration installs**: those of a recognised inductive block. -/
def declTables : Declaration → List ProjTable
  | .indDecl block nP =>
    match basisNameHit block with
    | some _ => []
    | none =>
      match blockParts? nP block with
      | some p => blockTables p.toBlockShape p.members
      | none => []
  | _ => []

end ConLeche
