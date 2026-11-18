module

public import ConLeche.Driver.Worker
public import ConLeche.Driver.Compare
public import ConLeche.Driver.Graph

@[expose] public section

/-!
# The compare worker: a challenge as one more module of a modular run (task #608)

`con-leche --olean --module --compare --search-path=DIRS -- C S` is the worker of the challenge
`C` in a modular run over the closures of `C` and of its solution `S` (`--check-graph --compare`,
`--schedule --compare`).  The challenge is one more module of the run: its records are not
checked, its own names are read from the solution, and what it imports is read from the module
that declares it, as every worker reads it.

1. **The home** (`homeOf`): `C`'s private view loaded and its parts checked against each other,
   as the worker's; its records emitted (`ownRecords`).
2. **The reads** (`workerReads` with `import all S` added to `C`'s header,
   `NamePositions.withImports`): the header fixpoint of `C`'s imports and of the solution with
   everything it holds, the name index, Lean's clash rule over every loaded name.  `C`'s own
   names are no constants of this part: they are the solution's.
   A solution whose closure holds the challenge is refused (the graph check refuses it too: the
   added import closes a cycle).
3. **The context** (`reach`): from `C`'s own names, every one a name the loads hold (else the
   solution lacks it), and the names `C`'s records read that `C` imports; with no own name of
   its own, so that each of `C`'s names is read from the module of `S`'s closure that declares
   it.
4. **The homes** (`importedAt`): every name `C`'s records read that `C` imports is, in the
   context, the constant of the module `C`'s own view (the reads at `C`'s own header) loads it
   from first, or both are theorems of one statement (Lean's key for a proof).  So a name the
   challenge imports is its home's constant: a solution declaring one of them itself is refused
   here, or by the clash rule before.
5. **The comparison** (`cmpCtxRecord`), each record of `C` against the context's record of its
   key: a hole (`isHole`) by the statement up to the names of level parameters
   (`sameCvUpToLevels`), of any kind; a theorem by its statement (the context holds a theorem as
   its statement); an opaque constant by its statement and its value, read off its home's private
   part (`opaqueValue`); any other record as the record the context holds
   (`sameRecordUpToLevels`): a definition the context holds as its statement (its value hidden
   from `C`) is refused.  The declines of `--olean --compare` stay.

Exit 0 needs every phase; the accept prints the holes, each with the module and the kind of
what fills it.
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **A challenge record as the context holds it**: a hole, a theorem and an opaque constant as
its statement (`Modular.stmtOf`), any other record itself. -/
def cmpView (uses : Declaration → Array Name) (d : Declaration) : Declaration :=
  if isHole uses d then Modular.stmtOf d else
  match d with
  | .thmDecl .. | .opaqueDecl .. => Modular.stmtOf d
  | d => d

/-- A stored constant's kind, by its tag (`CKindF.tag`), for the messages. -/
def tagKind : Nat → String
  | 0 => "axiom"
  | 1 => "definition"
  | 2 => "theorem"
  | 3 => "opaque constant"
  | 4 => "quotient constant"
  | 5 => "inductive type"
  | 6 => "constructor"
  | 7 => "recursor"
  | _ => "constant"

/-- **A challenge record against the context's record of its key** (`dS`, of home `homeS`):
whether it is met and, for a hole, what fills it (`kindS`: the kind the home declares).  An
opaque constant's value is compared by the caller. -/
def cmpCtxRecord (uses : Declaration → Array Name) (dC dS : Declaration)
    (homeS : Name) (kindS : String) : Except String (Option Filled) :=
  let n := recKey dC
  if isHole uses dC then
    let label := match dC with
      | .axiomDecl _ => "axiom"
      | d => s!"{recKind d} := sorry"
    if n == quotSoundName || n == sorryAxName then
      .error s!"{declined}{n}: a hole at {if n == quotSoundName then "the quotient's axiom"
        else "the placeholder axiom"}, which installs no axiom of its own; con-leche cannot \
        fill it"
    else
    match dS with
    | .axiomDecl cv' | .defnDecl cv' _ _ =>
      if reduceOpNames.contains n && kindS != "axiom" && kindS != "opaque constant" then
        .error s!"{declined}{n}: the solution fills this hole at a compiler-trust name with a \
          {kindS}; con-leche can fill it only with an opaque constant or an axiom"
      else
      match recCv? dC with
      | some cv =>
        if sameCvUpToLevels cv cv' then .ok (some ⟨n, label, kindS, homeS⟩)
        else .error s!"{n}: the solution's {kindS} is not of the hole's type"
      | none => .error s!"{n}: the solution's {kindS} is not of the hole's type"
    | _ => .error s!"{declined}{n}: the solution fills this hole with an {kindS}; \
        con-leche can fill a hole only with a definition, a theorem, an opaque constant or an \
        axiom at the moment"
  else
    let differs := s!"{n}: the solution's {kindS} differs from the challenge's {recKind dC}"
    match dC, dS with
    | .thmDecl cv _, .axiomDecl cv' | .opaqueDecl cv _, .axiomDecl cv' =>
      if kindS == recKind dC && sameCvUpToLevels cv cv' then .ok none else .error differs
    | .defnDecl .., .axiomDecl _ =>
      .error s!"{n}: the solution's {kindS} is not visible to the challenge with its value \
        (declared by {homeS}, which the solution does not import with `import all`)"
    | dC, dS => if sameRecordUpToLevels dC dS then .ok none else .error differs

/-- **A constant of a module's private part, read whole**, and its position there. -/
def privEntry {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (h n : Name) :
    μ (Option (NamePosition × Option (CEntryF Name Expr))) := do
  match ← rd.names (h, .private) with
  | .error _ => pure none
  | .ok t =>
    match t.consts.find? (·.name == n) with
    | none => pure none
    | some q =>
      match ← rd.files h .private with
      | .error _ => pure (some (q, none))
      | .ok f =>
        match f.viewRegion .private with
        | none => pure (some (q, none))
        | some (r, _) => pure (some (q, (entryWith r {} q.loc).map (·.2)))

/-- **An opaque challenge record's value against the solution's**, read off its home's private
part: the same up to the names of level parameters. -/
def opaqueValue (cv : ConstantVal) (v : Expr) : Option (CEntryF Name Expr) → Bool
  | some { name, levelParams, type, kind := .opaq v' _ } =>
    sameUpToLevels (.defnInfo cv v .opaque)
      (.defnInfo { name, levelParams, type } v' .opaque)
  | _ => false

/-- **A name the challenge imports is its home's constant** (the merging rule's key): the
context's copy of `y` is of the module the challenge's own view loads it from first (`wrC`, the
reads at `C`'s own header), or both copies are theorems of one statement (Lean's key for a
proof).  `none` when it is; else why not. -/
def importedAt {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (wrC : WorkerReads) (r : Reach)
    (owner : Std.HashMap Name Nat) (y : Name) : μ (Option String) := do
  match wrC.index.first[y]? with
  | none => pure (some s!"{y}: the challenge's records read it, and no module the challenge \
      loads holds it")
  | some cp =>
    let hC := wrC.loads.nameAt cp.mod
    match owner[y]? with
    | none => pure (some s!"{y}: the challenge's records read it, and the context does not hold it")
    | some k =>
      let hS := r.homes.getD k .anonymous
      if hC == hS then return none
      let msg := s!"{y}: the challenge reads it from {hC}, the solution's is {hS}'s; a name the \
        challenge imports must be its home's constant"
      let cvOf (e : CEntryF Name Expr) : ConstantVal :=
        { name := e.name, levelParams := e.levelParams, type := e.type }
      match ← privEntry rd hS y, ← privEntry rd hC y with
      | some (qS, some eS), some (qC, some eC) =>
        if qS.tag == 2 && qC.tag == 2 && (cvOf eS).beqP (cvOf eC) then pure none
        else pure (some msg)
      | _, _ => pure (some msg)

/-- Every name of `ys` its home's constant (`importedAt`), or the first that is not. -/
def importedAll {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (wrC : WorkerReads) (r : Reach)
    (owner : Std.HashMap Name Nat) : List Name → μ (Option String)
  | [] => pure none
  | y :: ys => do
    match ← importedAt rd wrC r owner y with
    | some why => pure (some why)
    | none => importedAll rd wrC r owner ys

/-- **The comparison's verdict at one challenge record**: `cmpCtxRecord` against the context's
record storing its key, and an opaque constant's value. -/
def cmpAt {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ)
    (uses : Declaration → Array Name) (r : Reach) (owner : Std.HashMap Name Nat)
    (dC : Declaration) : μ (Except String (Option Filled)) := do
  let n := recKey dC
  match owner[n]? with
  | none => pure (.error s!"{n}: the solution has no constant of this name")
  | some k =>
    let dS := r.ctx.getD k default
    let h := r.homes.getD k .anonymous
    let pe ← privEntry rd h n
    let kindS := tagKind ((pe.map (·.1.tag)).getD 8)
    match cmpCtxRecord uses dC dS h kindS with
    | .error e => pure (.error e)
    | .ok f =>
      match dC with
      | .opaqueDecl cv v =>
        if isHole uses dC || opaqueValue cv v (pe.bind (·.2)) then pure (.ok f)
        else pure (.error s!"{n}: the solution's opaque constant differs from the challenge's \
          opaque constant")
      | _ => pure (.ok f)

/-- **What the compare worker has read and compared.** -/
structure CmpModuleRead where
  /-- the challenge's private view, loaded -/
  home : Loaded
  /-- its records -/
  emitted : Array Declaration
  /-- the header fixpoint of its header with the solution added, the name index, the clash
  rule's copies -/
  reads : WorkerReads
  /-- the same at its own header: its own view -/
  view : WorkerReads
  /-- the context -/
  reach : Reach
  /-- the holes filled -/
  filled : Array Filled

/-- Every challenge record compared, in order: the holes filled, or the first record not met. -/
def cmpAll {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ)
    (uses : Declaration → Array Name) (r : Reach) (owner : Std.HashMap Name Nat) :
    List Declaration → Array Filled → μ (Except String (Array Filled))
  | [], acc => pure (.ok acc)
  | d :: ds, acc => do
    match ← cmpAt rd uses r owner d with
    | .error e => pure (.error e)
    | .ok f => cmpAll rd uses r owner ds (match f with | some f => acc.push f | none => acc)

/-- **The compare worker's phases** (see the module docstring): the error and its exit code, or
what was read and compared. -/
def cmpModuleRead {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (C S : Name) (pace : Pace)
    (t0 jobs : Nat) : μ (Except (String × UInt8) CmpModuleRead) := do
  let fail (e : CheckError) : Except (String × UInt8) CmpModuleRead := .error (toString e, e.exitCode)
  match ← rd.files C .private with
  | .error e => pure (fail e)
  | .ok f =>
  match homeOf C f with
  | .error e => pure (fail e)
  | .ok (l, _) =>
  match ← workerReads rd C jobs #[Graph.solutionImport S] with
  | .error e => pure (fail e)
  | .ok wr =>
  if wr.loads.index.contains C then
    return .error (s!"{S} does not solve {C}: the solution's closure holds the challenge", 1)
  workerSay pace t0 s!"loads {wr.loads.order.size} modules, {wr.index.first.size} names"
  match ownRecords l with
  | .error (e, _) => pure (fail e)
  | .ok ds =>
  let uses := ownUses l
  let own := (l.constants.filter (!·.skipped)).map (·.name)
  match own.find? (!wr.index.first.contains ·) with
  | some n => pure (.error (s!"{S} does not solve {C}: {n}: the solution has no constant of \
      this name", 1))
  | none =>
  let ownSet := ownNames l
  -- what the challenge's records read of what it imports
  let imported := ds.foldl (fun acc d =>
    acc ++ (recordReads (cmpView uses d)).filter (!ownSet.contains ·)) #[]
  match ← reach rd C wr {} (own ++ imported) with
  | .error e => pure (fail e)
  | .ok r =>
  if !namesNodupGo {} (r.ctx.toList.flatMap Modular.declNames) then
    return .error ("invalid: a context record declares one of its names twice", 1)
  workerSay pace t0 s!"reach: {r.ctx.size} records"
  let owner := ownerMap r.ctx
  -- the challenge's own view, for the homes of what it imports
  match ← workerReads rd C jobs with
  | .error e => pure (fail e)
  | .ok wrC =>
  match ← importedAll rd wrC r owner imported.toList with
  | some why => pure (.error (s!"{S} does not solve {C}: {why}", 1))
  | none =>
  match ← cmpAll rd uses r owner ds.toList #[] with
  | .error why =>
    if declined.isPrefixOf why then pure (.error (why, 2))
    else pure (.error (s!"{S} does not solve {C}: {why}", 1))
  | .ok filled =>
    pure (.ok { home := l, emitted := ds, reads := wr, view := wrC, reach := r, filled })

/-- **The compare worker** (see the module docstring), generic in the IO class. -/
def checkCmpModuleG {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (C S : Name)
    (mode : CheckMode) (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  CheckerIO.liftIO (readStarts pace s!"challenge {C}")
  match ← cmpModuleRead rd C S pace t0 jobs with
  | .error (why, code) =>
    diagLine s!"con-leche: challenge {C}: {why} ({modeTag})"
    return code
  | .ok w =>
    outLine s!"con-leche: accepted: {S} solves {C}: {w.emitted.size} challenge declarations \
      compared, {w.filled.size} holes filled, against {w.reach.ctx.size} context records \
      ({modeTag})"
    for f in w.filled do
      outLine s!"con-leche: hole {f.name} ({f.hole}) filled by {f.home}'s {f.filler}"
    return 0

end ConLeche.Driver
