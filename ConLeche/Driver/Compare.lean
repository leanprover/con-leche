module

public import ConLeche.Driver.CheckMain
public import ConLeche.Driver.Reach
import ConLeche.Verify.Cached.DeclNames

@[expose] public section

/-!
# A challenge and its solution (task #607)

`con-leche --olean --compare [--trusted-search-path=DIRS] --search-path=DIRS -- C S` says
whether the module `S` solves the challenge `C`: every hole of `C` (an axiom of `C` itself, or a
declaration of `C` whose value uses `sorry`) is met by `S`'s constant of the same name and type,
every other constant of `C` and every constant they read is `S`'s, and `S`'s closure is
accepted.

**The two reads.**  A challenge and its solution declare the same names (that is the point), so
there is no one merged environment: the challenge's closure is read (`readOleansAt`) through the
TRUSTED lookup alone, the solution's through the trusted path first and the search path after it
(`Roots.fallback`).  Without `--trusted-search-path` both read through the search path.  Nothing
of the challenge is checked: its records are compared, and the solution's are checked as an
`--olean` run checks a closure.  A module both closures hold is checked once, in the solution.

**What is compared** (`chalRecs`): the challenge module's own records and what they read,
closed under reads, every hole as its statement (`readCone`, which the comparison of two
lean4export files shares): what only a hole's value or a theorem's proof reads is not compared,
nor a module `C` imports and never reads from, which cannot change what its holes say.  Under
`--constant` the roots are the records of the named declarations (the challenge's read holds
their cone).  The modular compare worker compares the same records.

**The comparison** (`cmpRecord`), record by record in the challenge's prepared order, each
compared challenge record against the solution's record of its key (`recKey`):

* a record of a module `C` imports (its key's home is not `C`, `Olean.homesOf`): the solution's
  record has the same home — for a theorem, the same statement, Lean's key for a proof — and is
  the same record (`sameRecord`);
* a hole of `C` (`isHole`): the solution's constant has the hole's name and type, up to the
  names of its level parameters (`sameCvUpToLevels`); it stands in the challenge's environment
  as its statement (`Modular.stmtOf`), or as itself where it is an axiom;
* any other record of `C`: the solution's is the same record up to the names of its level
  parameters (`sameUpToLevels`; an inductive block or a quotient record exactly).

`Expr`s hold no binder name, no binder info and no metadata, so the comparison ignores those.
What each challenge record stands for (`ctx`) is a solution record or its statement, and the
comparison then checks that every one of them reads only names installed by itself or the ones
before it, each name installed once (`ctxScoped`).

**The verdict**: exit 1 for a failed comparison, with the reason; otherwise the solution's
closure is checked, and on its accept the success line and the holes, each with what fills it.
-/

namespace ConLeche.Driver

open ConLeche Frontend.Olean

/-! ## The comparison -/

/-- **The name a record is found under**: its constant's, an inductive block's first. -/
def recKey : Declaration → Name
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv =>
    cv.name
  | .indDecl b _ => (b.head?.map (·.name)).getD .anonymous

/-- The statement a record declares, where it declares one constant. -/
def recCv? : Declaration → Option ConstantVal
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv =>
    some cv
  | .indDecl _ _ => none

/-- A record's kind, for the messages. -/
def recKind : Declaration → String
  | .axiomDecl _ => "axiom"
  | .defnDecl .. => "definition"
  | .thmDecl .. => "theorem"
  | .opaqueDecl .. => "opaque constant"
  | .quotDecl .. => "quotient constant"
  | .indDecl .. => "inductive type"

/-- Two lists of level-parameter names a renaming relates: as many, neither with a repeat. -/
def levelsRenaming (ps ps' : List Name) : Bool :=
  ps.length == ps'.length && decide ps.Nodup && decide ps'.Nodup

/-- **A challenge's statement, the solution's up to the names of its level parameters**: the
same, or as many names, each list without repeats, and the solution's (`cv'`) at the
challenge's names the challenge's.  The solution's is the one renamed: it is checked, so its
level parameters are all among its names, and the renaming reads it whole. -/
def sameCvUpToLevels (cv cv' : ConstantVal) : Bool :=
  if cv.levelParams == cv'.levelParams then cv.beqP cv'
  else levelsRenaming cv.levelParams cv'.levelParams && (cv'.atLps cv.levelParams).beqP cv

/-- **A challenge's constant, the solution's up to the names of its level parameters**
(`ConstantInfo.atLps`, the solution's renamed). -/
def sameUpToLevels (c c' : ConstantInfo) : Bool :=
  let ps := c.toConstantVal.levelParams
  let ps' := c'.toConstantVal.levelParams
  if ps == ps' then c.beqP c'
  else levelsRenaming ps ps' && (c'.atLps ps).beqP c

/-- **Two records, the same**: of one kind, their constants equal (a theorem by its statement:
its record's value is where to read it), an inductive block's parameter count and a
quotient record's slot equal. -/
def sameRecord : Declaration → Declaration → Bool
  | .indDecl b n, .indDecl b' n' => n == n' && listBeqBy ConstantInfo.beqP b b'
  | .quotDecl k cv, .quotDecl k' cv' => k.slot == k'.slot && cv.beqP cv'
  | .opaqueDecl cv v, .opaqueDecl cv' v' => cv.beqP cv' && v == v'
  | .thmDecl cv _, .thmDecl cv' _ => cv.beqP cv'
  | d@(.defnDecl ..), d'@(.defnDecl ..) | d@(.axiomDecl _), d'@(.axiomDecl _) =>
    listBeqBy ConstantInfo.beqP (declConstants d) (declConstants d')
  | _, _ => false

/-- **The same record up to the names of its level parameters**: a definition, theorem or
opaque constant (an opaque's value as well); any other record exactly. -/
def sameRecordUpToLevels : Declaration → Declaration → Bool
  | .defnDecl cv v h, .defnDecl cv' v' h' =>
    sameUpToLevels (.defnInfo cv v h) (.defnInfo cv' v' h')
  | .thmDecl cv _, .thmDecl cv' _ => sameCvUpToLevels cv cv'
  | .opaqueDecl cv v, .opaqueDecl cv' v' =>
    sameUpToLevels (.defnInfo cv v .opaque) (.defnInfo cv' v' .opaque)
  | d, d' => sameRecord d d'

/-- **A hole of the challenge** (of `C`'s own records): an axiom, or a definition, theorem or
opaque constant whose value uses `sorryAx`; a theorem's value is read off its file (`uses`). -/
def isHole (uses : Declaration → Array Name) : Declaration → Bool
  | .axiomDecl _ => true
  | .defnDecl _ v _ | .opaqueDecl _ v => (Frontend.usedConstsGo {} #[] v).2.contains sorryAxName
  | d@(.thmDecl _ _) => (uses d).contains sorryAxName
  | _ => false

/-- What starts the reason of a comparison that positively detects a feature con-leche does
not support: the run declines (exit 2) instead of rejecting. -/
def declined : String := "declined: "

/-- A hole and what fills it, for the report. -/
structure Filled where
  name : Name
  hole : String
  filler : String
  home : Name

/-- **One challenge record against the solution's of its key**: what it stands for in the
challenge's environment, and, for a hole, what fills it; or why the solution does not meet it.
`own` says the record is `C`'s; `homeC` and `homeS` are the key's homes on the two sides. -/
def cmpRecord (C : Name) (uses : Declaration → Array Name) (own : Bool)
    (homeC homeS : Option Name) (dC dS : Declaration) :
    Except String (Declaration × Option Filled) :=
  let n := recKey dC
  let homeName (h : Option Name) : String := (h.map toString).getD "the built-in prelude"
  if !own then
    let proofKey := match dC with
      | .thmDecl .. => true
      | _ => false
    if !proofKey && homeC != homeS then
      .error s!"{n}: the challenge reads it from {homeName homeC}, the solution's is \
        {homeName homeS}'s; a name the challenge imports must be its home's constant"
    else if sameRecord dC dS then .ok (dS, none)
    else .error s!"{n}: the solution's {recKind dS} differs from the challenge's {recKind dC} \
      of {homeName homeC}"
  else if isHole uses dC then
    let label := match dC with
      | .axiomDecl _ => "axiom"
      | d => s!"{recKind d} := sorry"
    let filled : Except String (Declaration × Option Filled) :=
      match recCv? dC, recCv? dS with
      | some cv, some cv' =>
        if sameCvUpToLevels cv cv' then
          .ok (Modular.stmtOf dS, some ⟨n, label, recKind dS, (homeS.getD C)⟩)
        else .error s!"{n}: the solution's {recKind dS} is not of the hole's type"
      | _, _ => .error s!"{n}: the solution's {recKind dS} is not of the hole's type"
    if n == quotSoundName || n == sorryAxName then
      .error s!"{declined}{n}: a hole at {if n == quotSoundName then "the quotient's axiom"
        else "the placeholder axiom"}, which installs no axiom of its own; con-leche cannot \
        fill it"
    else
    match dS with
    | .axiomDecl _ | .opaqueDecl .. => filled
    | .defnDecl .. | .thmDecl .. =>
      if reduceOpNames.contains n then
        .error s!"{declined}{n}: the solution fills this hole at a compiler-trust name with a \
          {recKind dS}; con-leche can fill it only with an opaque constant or an axiom"
      else filled
    | _ => .error s!"{declined}{n}: the solution fills this hole with an {recKind dS}; \
        con-leche can fill a hole only with a definition, a theorem, an opaque constant or an \
        axiom at the moment"
  else if sameRecordUpToLevels dC dS then .ok (dS, none)
  else .error s!"{n}: the solution's {recKind dS} differs from the challenge's {recKind dC}"

/-- **A challenge record in the challenge's own environment**: a hole of `C` as its statement
(`Modular.stmtOf`), any other record as it is. -/
def chalRecord (C : Name) (uses : Declaration → Array Name) (homesC : Std.HashMap Name Name)
    (d : Declaration) : Declaration :=
  if homesC[recKey d]? == some C && isHole uses d then Modular.stmtOf d else d

/-- **Where the solution's record of a name is**: its position, by its key and by every name it
installs. -/
def recIndex (recs : Array Declaration) : Std.HashMap Name Nat :=
  recs.foldl (init := ({}, 0)) (fun (m, i) d =>
    ((m.insert (recKey d) i).insertMany ((Modular.declNames d).map (·, i)), i + 1)) |>.1

/-- The worklist of `readCone`: record positions, each pushed once (`seen` marks it), so that
`fuel = recs.size + 1` steps empty it. -/
def readConeGo (form : Declaration → Declaration) (recs : Array Declaration)
    (idx : Std.HashMap Name Nat) : Nat → List Nat → Array Bool → Array Bool
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, i :: rest, seen =>
    match recs[i]? with
    | none => readConeGo form recs idx fuel rest seen
    | some d =>
      let next := (recordReads (form d)).foldl (init := (rest, seen)) fun (st, seen) y =>
        match idx[y]? with
        | some j => if seen[j]?.getD true then (st, seen) else (j :: st, seen.set! j true)
        | none => (st, seen)
      readConeGo form recs idx fuel next.1 next.2

/-- **The records a challenge's environment needs**: those `root` names, and what they read,
closed under reads, each record read as `form` gives it (a hole as its statement): what only a
hole's value or a theorem's proof reads is not needed (`recordReads` never reads a theorem's
value).  In their order, so that every record follows what it reads. -/
def readCone (root : Declaration → Bool) (form : Declaration → Declaration)
    (recs : Array Declaration) : Array Declaration :=
  let roots := (List.range recs.size).filter fun i => (recs[i]?.map root).getD false
  let seen := roots.foldl (fun seen i => seen.set! i true) (Array.replicate recs.size false)
  let need := readConeGo form recs (recIndex recs) (recs.size + 1) roots seen
  (recs.zipIdx.filter fun (_, i) => need[i]?.getD false).map (·.1)

/-- **A root of the challenge's comparison**: a record of the challenge module `C` itself, and,
under `--constant`, one that installs a name it gives. -/
def chalRoot (C : Name) (homesC : Std.HashMap Name Name) (constants : Option (Array Name))
    (d : Declaration) : Bool :=
  homesC[recKey d]? == some C &&
    constants.all fun cs => (recKey d :: Modular.declNames d).any cs.contains

/-- **The challenge's records that are compared**: the roots (`chalRoot`) and what they read,
closed under reads, every hole of `C` as its statement (`readCone`).  A module `C` imports and
never reads from cannot change what its holes say, and is not compared. -/
def chalRecs (C : Name) (uses : Declaration → Array Name) (homesC : Std.HashMap Name Name)
    (constants : Option (Array Name)) (recs : Array Declaration) : Array Declaration :=
  readCone (chalRoot C homesC constants) (chalRecord C uses homesC) recs

/-- **What the challenge's records stand for**, in order, and the holes filled, or the first
record the solution does not meet.  `idxS` finds the solution's prepared record of a key. -/
def compareRecords (C : Name) (uses : Declaration → Array Name) (homesC homesS : Std.HashMap Name Name)
    (recsS : Array Declaration) (idxS : Std.HashMap Name Nat) (recsC : Array Declaration) :
    Except String (Array Declaration × Array Filled) :=
  recsC.foldlM (init := (#[], #[])) fun (ctx, filled) dC =>
    let n := recKey dC
    match idxS[n]?.bind (recsS[·]?) with
    | none => .error s!"{n}: the solution has no constant of this name"
    | some dS =>
      match cmpRecord C uses (homesC[n]? == some C) homesC[n]? homesS[n]? dC dS with
      | .error e => .error e
      | .ok (d, f) => .ok (ctx.push d, match f with
        | some f => filled.push f
        | none => filled)

/-- **What the challenge's records stand for reads only what the records before it, or itself,
install**, each name installed once; otherwise the first record that does not. -/
def ctxScoped (ctx : Array Declaration) : Option String :=
  let install (seen : Std.HashSet Name) (n : Name) : Except String (Std.HashSet Name) :=
    if seen.contains n then .error s!"{n}: installed twice by the challenge's records"
    else .ok (seen.insert n)
  let step (seen : Std.HashSet Name) (e : Declaration) : Except String (Std.HashSet Name) :=
    match (Modular.declNames e).foldlM install seen with
    | .error why => .error why
    | .ok seen =>
      match (recordReads e).find? (!seen.contains ·) with
      | some y => .error s!"{recKey e}: reads {y}, which no challenge record before it installs"
      | none => .ok seen
  match ctx.foldlM step {} with
  | .error e => some e
  | .ok _ => none

/-! ## The run -/

/-- **A compared run's request**: the challenge and solution modules, the trusted directories
(none given: the search path is trusted), the search path, and the `--constant` names. -/
structure CmpReq where
  challenge : Name
  solution : Name
  trusted : SearchPath
  path : SearchPath
  constants : Option (Array Name)

/-- **The challenge's lookup**: the trusted path, never anything else. -/
def CmpReq.chalRoots (r : CmpReq) : Roots :=
  if r.trusted.isEmpty then { path := r.path } else { path := r.trusted }

/-- **The solution's lookup**: the trusted path first, then the search path. -/
def CmpReq.solRoots (r : CmpReq) : Roots :=
  if r.trusted.isEmpty then { path := r.path } else { path := r.trusted, fallback := r.path }

/-- **Why a challenge module is not on the trusted path**, where it is on the search path: the
challenge's closure walked through the solution's lookup, and the first module whose root only
the search path holds.  Only after the challenge's read failed, and only for the message: the
challenge's read itself never looks at the search path. -/
def fallbackOnly {μ : Type → Type} [CheckerIO μ] (r : CmpReq) : μ (Option String) := do
  if r.trusted.isEmpty then return none
  match ← closureOrder r.solRoots #[r.challenge] with
  | .error _ => return none
  | .ok (order, T) =>
    for m in order do
      if (← rootAt r.trusted m.root) matches .missing then
        if let some (.dir d) := T.map[m.root]? then
          return some s!"the challenge's module {m} is not on the trusted path \
            ({":".intercalate (r.trusted.map toString)}); it is in {d}, on the search path, \
            which only the solution reads"
    return none

/-- **A `--constant` name that is no declaration of the challenge module**, and why; `homes` the
challenge closure's. -/
def foreignConstant (r : CmpReq) (homes : Std.HashMap Name Name) : Option String := do
  let c ← (← r.constants).find? (homes[·]? != some r.challenge)
  return s!"--constant={c}: not a declaration of the challenge module {r.challenge}\
    {match homes[c]? with
      | some h => s!" (it is {h}'s)"
      | none => " (no module of its closure declares it)"}"

/-- The receipt of the records hoisted ahead of the pinned `Nat` operations they ground. -/
def hoistedNote {μ : Type → Type} [CheckerIO μ] (hoisted : Array Name) : μ Unit :=
  if hoisted.size > 0 then
    diagLine s!"con-leche: {hoisted.size} declarations hoisted ahead of the pinned Nat \
      operations they ground: {String.intercalate ", " (hoisted.toList.map toString)}"
  else pure ()

/-- **The verdict of a failed read**: its line and exit code. -/
def readFailed {μ : Type → Type} [CheckerIO μ] (modeTag label : String) :
    CheckError × Nat → μ UInt8
  | (.notImplemented what, _) => do
    diagLine s!"con-leche: declined: {what} ({modeTag})"
    return 2
  | (.invalid what, _) => do
    diagLine s!"con-leche: invalid: {what} ({modeTag})"
    return 1
  | (.internal msg, line) => do
    diagLine s!"con-leche: {label}:{line}: {msg}"
    return 3

/-- **The compared run** (see the module docstring). -/
def compareG {μ : Type → Type} [CheckerIO μ] (r : CmpReq) (mode : CheckMode) (maxNatSize : Nat)
    (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let prelude ← match Frontend.builtinPreludeE with
    | .ok p => pure p
    | .error (_, line) =>
      diagLine s!"con-leche: the built-in prelude does not parse (line {line}); regenerate it \
        with `lake exe natop-pins-export` ({modeTag})"
      return 3
  -- the challenge, through the trusted lookup alone
  CheckerIO.liftIO (readStarts pace s!"{r.challenge}")
  match ← readOleansAt r.chalRoots #[r.challenge] r.constants jobs pace (lenient := true)
      (homes := true) with
  | .error e =>
    if let some why := ← fallbackOnly r then
      diagLine s!"con-leche: {why} ({modeTag})"
      return 1
    readFailed modeTag (toString r.challenge) e
  | .ok rdC =>
  -- `--constant`: declarations of the challenge module itself
  if let some why := foreignConstant r rdC.homes then
    diagLine s!"con-leche: {why} ({modeTag})"
    return 1
  -- the challenge's records that are compared: its own and what they read
  let usesC := usedOf (some (r.chalRoots.path, rdC))
  let recsC := chalRecs r.challenge usesC rdC.homes r.constants
    (Frontend.prepareD prelude rdC.decls usesC).decls
  -- the solution, from the constants the compared records need, or all of it
  let need := r.constants.map fun _ => recsC.map recKey
  match ← readOleansAt r.solRoots #[r.solution] need jobs pace (lenient := true)
      (homes := true) with
  | .error e => readFailed modeTag (toString r.solution) e
  | .ok rdS =>
  -- a solution importing its challenge is no solution (task #608: as the modular run's cycle)
  if rdS.values.any (·.name == r.challenge) then
    diagLine s!"con-leche: {r.solution} does not solve {r.challenge}: the solution's closure \
      holds the challenge ({modeTag})"
    return 1
  let ⟨recsS, _, hoisted⟩ := Frontend.prepareD prelude rdS.decls
    (usedOf (some (r.solRoots.path, rdS)))
  match compareRecords r.challenge usesC rdC.homes rdS.homes recsS (recIndex recsS) recsC with
  | .error why =>
    if declined.isPrefixOf why then
      diagLine s!"con-leche: {why} ({modeTag})"
      return 2
    diagLine s!"con-leche: {r.solution} does not solve {r.challenge}: {why} ({modeTag})"
    return 1
  | .ok (ctx, filled) =>
  if let some why := ctxScoped ctx then
    diagLine s!"con-leche: {r.solution} does not solve {r.challenge}: {why} ({modeTag})"
    return 1
  hoistedNote hoisted
  -- the solution's closure, checked
  let tIndex ← clockMs
  let J ← CheckerIO.liftIO (Jobs.build recsS)
  let tParse ← clockMs
  match ← checkOleansG mode maxNatSize pace t0 tIndex tParse jobs rdS.roots rdS.values J with
  | .error e =>
    verdictG modeTag rdS.decls.size t0 recsS (.error e) s!"the solution {r.solution}: "
  | .ok () =>
    outLine s!"con-leche: accepted: {r.solution} solves {r.challenge}: {recsC.size} \
      challenge declarations compared, {filled.size} holes filled, {rdS.decls.size} solution \
      declarations checked ({modeTag})"
    for f in filled do
      outLine s!"con-leche: hole {f.name} ({f.hole}) filled by {f.home}'s {f.filler}"
    return 0

end ConLeche.Driver
