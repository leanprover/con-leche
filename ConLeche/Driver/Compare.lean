module

public import ConLeche.Driver.CheckMain
public import ConLeche.Driver.CmpReq
import ConLeche.Verify.Cached.DeclNames

@[expose] public section

/-!
# A challenge and its solution (tasks #607, #619)

`con-leche --olean --compare [--trusted-search-path=DIRS] --search-path=DIRS -- C S` checks the
challenge module `C`'s closure with its axioms justified by the solution module `S`'s closure, as
`--compare` checks a lean4export challenge with a solution file (`Driver/CompareJson.lean`): the
solution's closure is checked in full, as an `--olean` run checks a closure, and its environment
is the **solution** of the challenge's check (`Cached.checkDeclsWith … (some envS)`,
`ConLeche/Cached/Justify.lean`).  The challenge's closure is checked in full too; only its axioms
other than the built-in ones, and its declarations whose value uses `sorryAx` (the holes, each
read as the axiom of its statement), take the justification route: the solution holds a constant
of the same name and type, up to the names of its level parameters, and everything the type reads
is the same constant in both.

**The two reads.**  A challenge and its solution declare the same names (that is the point), so
there is no one merged environment: the challenge's closure is read (`readOleansAt`) through the
TRUSTED lookup alone, the solution's through the trusted path first and the search path after it
(`Roots.fallback`).  Without `--trusted-search-path` both read through the search path.  Under
`--constant` the challenge's read holds the named declarations of `C` and what they read, and the
solution's read the constants of the names those records install.

**A theorem's hole.**  An `--olean` run reads a theorem's value in its check, after the frozen
index is built, and a hole is an axiom in that index.  So which theorems are holes is decided
before the index, by what the theorem's file says its value uses (`holeRecord`, from
`OleanRead.thmUses`).  Nothing rests on that being right: a theorem read as a hole whose value
uses no `sorry` is only the axiom of its statement, justified like any, and one read as a theorem
whose value does use `sorry` is checked as a theorem, which no check accepts.

**The verdict**: the solution's failed check is reported as the solution's; the challenge's as any
check's, an axiom the solution does not justify with the reason (exit 1); on the accept the success
line and one line per justified record.
-/

namespace ConLeche.Driver

open ConLeche Frontend.Olean

/-! ## Records (the modular compare mode reads them too) -/

/-- **The name a record is found under**: its constant's, an inductive block's first. -/
def recKey : Declaration → Name
  | .axiomDecl cv | .defnDecl cv _ _ | .thmDecl cv _ | .opaqueDecl cv _ | .quotDecl _ cv =>
    cv.name
  | .indDecl b _ => (b.head?.map (·.name)).getD .anonymous

/-- A record's kind, for the messages. -/
def recKind : Declaration → String
  | .axiomDecl _ => "axiom"
  | .defnDecl .. => "definition"
  | .thmDecl .. => "theorem"
  | .opaqueDecl .. => "opaque constant"
  | .quotDecl .. => "quotient constant"
  | .indDecl .. => "inductive type"

/-- **A theorem read as the hole it is** (`--olean --compare`): a theorem whose file says its
value uses `sorryAx` (`uses`, the file-read constants) is the axiom of its statement, where a
solution may justify it, as `Cached.sideRecord` reads a definition or opaque constant whose value
uses it; a theorem at a built-in axiom's name keeps its own check. -/
def holeRecord (uses : Declaration → Array Name) : Declaration → Declaration
  | d@(.thmDecl cv _) =>
    if !Cached.builtinAxiomName cv.name && (uses d).contains sorryAxName then .axiomDecl cv else d
  | d => d

/-! ## The run -/

/-- **The challenge's directories**: the trusted path, or the search path where none is given. -/
def trustedOr (trusted path : SearchPath) : SearchPath :=
  if trusted.isEmpty then path else trusted

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

/-- **The challenge's records as its check reads them**: its prepared records, every theorem its
file marks as a hole the axiom of its statement (`holeRecord`), and with the solution's
environment `envS` every definition and opaque constant whose value uses `sorryAx` too
(`Cached.sideRecords`). -/
def chalRecords (envS : Env) (uses : Declaration → Array Name) (recs : Array Declaration) :
    Array Declaration :=
  Cached.sideRecords (some envS) (recs.map (holeRecord uses))

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
  let usesC := usedOf (some (r.chalRoots.path, rdC))
  let ⟨recsC₀, _, hoistedC⟩ := Frontend.prepareD prelude rdC.decls usesC
  -- the solution, from the constants the challenge's records install, or all of it
  CheckerIO.liftIO (readStarts pace s!"{r.solution}")
  let need := r.constants.map fun _ => recsC₀.map recKey
  match ← readOleansAt r.solRoots #[r.solution] need jobs pace (lenient := true) with
  | .error e => readFailed modeTag (toString r.solution) e
  | .ok rdS =>
  -- a solution importing its challenge is no solution (task #608: as the modular run's cycle)
  if rdS.values.any (·.name == r.challenge) then
    diagLine s!"con-leche: {r.solution} does not solve {r.challenge}: the solution's closure \
      holds the challenge ({modeTag})"
    return 1
  -- the solution's closure, checked as an `--olean` run checks one
  let ⟨recsS, _, hoistedS⟩ := Frontend.prepareD prelude rdS.decls
    (usedOf (some (r.solRoots.path, rdS)))
  hoistedNote hoistedS
  let tIndex ← clockMs
  let JS ← CheckerIO.liftIO (Jobs.build recsS)
  let tParse ← clockMs
  match ← checkOleansG mode maxNatSize pace t0 tIndex tParse jobs rdS.roots rdS.values JS with
  | .error e =>
    verdictG modeTag rdS.decls.size t0 recsS (.error e) s!"the solution {r.solution}: "
  | .ok () =>
  -- the challenge's closure, checked with the solution
  let envS := streamEnv recsS.toList
  hoistedNote hoistedC
  let recsC := chalRecords envS usesC recsC₀
  let tIndexC ← clockMs
  let JC ← CheckerIO.liftIO (Jobs.build recsC (some envS))
  let tParseC ← clockMs
  match ← checkOleansG mode maxNatSize pace t0 tIndexC tParseC jobs rdC.roots rdC.values JC with
  | .error e => verdictG modeTag rdC.decls.size t0 recsC (.error e)
  | .ok () =>
    -- the justified records, labelled as the challenge declares them
    let holes := recsC₀.filter fun d =>
      (Cached.justifiable (Cached.sideRecord (holeRecord usesC d))).isSome
    outLine s!"con-leche: accepted {rdC.decls.size} declarations, {holes.size} axioms justified \
      by the solution {r.solution} ({rdS.decls.size} declarations accepted) ({modeTag})"
    for d in holes do
      outLine s!"con-leche: {Cached.declCLabel d} justified by the solution"
    return 0

end ConLeche.Driver
