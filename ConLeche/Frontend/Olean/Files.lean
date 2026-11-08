module

public import ConLeche.Frontend.Olean.Module
public import ConLeche.Frontend.CheckerIO

@[expose] public section

/-!
# Reading `.olean` files: from the file system, through the IO class

Where a module's files are on the search path, and each of the reads, as
actions of the checker's IO class (`CheckerIO`,
`ConLeche/Frontend/CheckerIO.lean`): the bytes come from the class's
operations, and everything done with them is a pure function of them
(`ConLeche/Frontend/Olean/View.lean`), so that on one snapshot of the
files every read of a module sees one value
(`ConLeche/Verify/Frontend/Olean/Files.lean`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The search path: the directories holding `.olean` trees, as
`LEAN_PATH` lists them. -/
abbrev SearchPath := List System.FilePath

/-- A module's path below a directory, without an extension: its components as
directories (Lean's `modToFilePath`). -/
def modDir (dir : System.FilePath) (m : Name) : System.FilePath :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  (comps m).foldl (fun (p : System.FilePath) (c : String) => p / c) dir

/-- **A module name's root**: its first component (Lean's `Name.root`). -/
def _root_.ConLeche.Name.root : Name → Name
  | .anonymous => .anonymous
  | .str .anonymous s => .str .anonymous s
  | .num .anonymous n => .num .anonymous n
  | .str p _ => ConLeche.Name.root p
  | .num p _ => ConLeche.Name.root p

/-- The file a module's level is stored in. -/
def modFile (dir : System.FilePath) (m : Name) (ext : String) : System.FilePath :=
  (modDir dir m).addExtension ext

/-- Where the scan of a name is. -/
inductive NameScan where
  | start | plain | esc | closed

/-- A component as written without an escape: at `nums`, one of digits alone is a
number, as Lean's name literals read it. -/
def Name.pushPlain (n : Name) (cur : String) (nums : Bool) : Name :=
  if nums && !cur.isEmpty && cur.all Char.isDigit then n.num cur.toNat! else n.str cur

/-- The scan of a name, one character at a time: `st` says where it is (at a component's
start, in a plain or an escaped component, just after an escape's `»`), `cur` holds the
component read so far. -/
def scanName (nums : Bool) : List Char → Name → NameScan → String → Option Name
  | [], n, .plain, cur => some (Name.pushPlain n cur nums)
  | [], n, .closed, _ => some n
  | [], _, _, _ => none
  | c :: cs, n, .start, _ =>
    if c == '«' then scanName nums cs n .esc ""
    else if c == '.' then none
    else scanName nums cs n .plain (String.singleton c)
  | c :: cs, n, .plain, cur =>
    if c == '.' then scanName nums cs (Name.pushPlain n cur nums) .start ""
    else scanName nums cs n .plain (cur.push c)
  | c :: cs, n, .esc, cur =>
    if c == '»' then (if cur.isEmpty then none else scanName nums cs (n.str cur) .closed "")
    else scanName nums cs n .esc (cur.push c)
  | c :: cs, n, .closed, _ => if c == '.' then scanName nums cs n .start "" else none

/-- **A module name as the command line spells it**: its components separated by dots,
a component in `«»` taken literally, dots included (Lean's own spelling of a name:
Lake's module `Challenge.«12.34».«5»` is stored as `Challenge/12.34/5.olean`).  `none`
for an empty component or an escape without its `»`.  An unescaped component is never
read as a number: a module name has string components only. -/
def parseModName (s : String) : Option Name :=
  scanName false s.toList .anonymous .start ""

/-- **A constant's name as the command line spells it**: as `parseModName`, a component
of digits being a number (`_private.M.0.foo`), as Lean's name literals read it. -/
def parseConstName (s : String) : Option Name :=
  scanName true s.toList .anonymous .start ""

/-- **Where a root's modules are** (task #511): the one search-path directory holding the
root, or why there is none. -/
inductive RootAt where
  /-- the directory holding it -/
  | dir (d : System.FilePath)
  /-- no directory holds it -/
  | missing
  /-- directories in two or more locations hold it, these (the first spelling of each) -/
  | twice (ds : List System.FilePath)
  /-- an exception while looking, its message -/
  | failed (e : String)

/-- **A search path with its roots resolved**: the directories, and the roots looked up on
them so far, each with where its modules are.  A run resolves each root once, the first
time it reads a module of it (`Roots.resolve`); a root not in the map is looked up on the
directories. -/
structure Roots where
  path : SearchPath
  map : Std.HashMap Name RootAt := {}

/-- A search path, no root resolved yet. -/
instance : Coe SearchPath Roots := ⟨fun sp => { path := sp }⟩

/-- **Whether a directory holds a root**, as Lean asks it (`SearchPath.findWithExt`): a
directory of the root's name, or a file of that name with `.olean`. -/
def holdsRoot {μ : Type → Type} [CheckerIO μ] (r : Name) (d : System.FilePath) : μ Bool := do
  if ← CheckerIO.isDir (modDir d r) then return true
  CheckerIO.pathExists (modFile d r "olean")

/-- The directories, one for each location: real paths compared, the first spelling kept. -/
def oneEach (ds : List (System.FilePath × System.FilePath)) : List System.FilePath :=
  (ds.foldl (fun (acc : Array (System.FilePath × System.FilePath)) d =>
    if acc.any (·.2 == d.2) then acc else acc.push d) #[]).toList.map (·.1)

/-- **Where a root's modules are on the search path** (task #511): the directories holding
the root (`holdsRoot`); where two or more do, their real paths compared, so that a directory
listed twice, or reached through a symbolic link, is one location. -/
def rootHits {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (r : Name) : μ RootAt := do
  let held ← sp.mapM fun d => return (d, ← holdsRoot r d)
  match (held.filter (·.2)).map (·.1) with
  | [] => return .missing
  | [d] => return .dir d
  | hits@(d :: _) =>
    match oneEach (← hits.mapM fun d => return (d, ← CheckerIO.realPath d)) with
    | [_] => return .dir d
    | locs => return .twice locs

/-- `rootHits`, an exception while looking its answer's reason. -/
def rootAt {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (r : Name) : μ RootAt :=
  tryCatchThe IO.Error (rootHits sp r) fun e => return .failed (toString e)

/-- **Where a root's modules are**, from the map or looked up. -/
def Roots.rootOf {μ : Type → Type} [CheckerIO μ] (R : Roots) (r : Name) : μ RootAt :=
  match R.map[r]? with
  | some a => pure a
  | none => rootAt R.path r

/-- **The roots with module `m`'s resolved.** -/
def Roots.resolve {μ : Type → Type} [CheckerIO μ] (R : Roots) (m : Name) : μ Roots := do
  if R.map.contains m.root then return R
  return { R with map := R.map.insert m.root (← rootAt R.path m.root) }

/-- **Where a module's files are** (task #392): the search-path directory holding its
root. -/
structure Located where
  dir : System.FilePath

/-- **The module's location from where its root is** (`findModule`), or why there is none. -/
def locatedOf (m : Name) : RootAt → Except CheckError Located
  | .dir d => .ok ⟨d⟩
  | .missing => .error (.internal s!"module {m}: no .olean on the search path (no directory \
      of it holds {m.root} or {m.root}.olean)")
  | .twice ds => .error (.internal s!"module {m}: its root {m.root} is in more than one \
      location on the search path ({", ".intercalate (ds.map toString)}); the search path \
      must hold each root once")
  | .failed e => .error (.internal s!"module {m}: locating its files: {e}")

/-- **Find a module, as Lean does, strictly** (tasks #392, #511).  Lean takes the first
search-path directory holding the module's ROOT (a directory `<Root>` or a file
`<Root>.olean`, `SearchPath.findWithExt`) and expects the module's files there; a copy in a
directory further down is never looked at, so two directories holding one root would let two
tools (or two search-path orders) read two different modules under one name.  Here every
directory is asked whether it holds the root, and where two or more do, they are compared by
their real paths, so that a directory listed twice, or reached through a symbolic link, is
one location (`rootAt`).  Each root is looked up once per run (`Roots`); the module's files
are then `M.olean`, `M.olean.server` and `M.olean.private` in that directory, and reading
them says whether they are there (`readImportsAt`, `readFilesAt`).  Malformed input
(`.internal`, exit 3):

* the root in directories of two locations;
* no directory holding the root (Lean's "unknown module prefix").

What the reads refuse: no `M.olean` in the root's directory (another directory holding one
is not looked at, as in Lean); parts without an `.olean` beside them; and, depending on the
exported part's module-system flag, a part missing or one too many (`readFilesAt`). -/
def findModule {μ : Type → Type} [CheckerIO μ] (R : Roots) (m : Name) :
    μ (Except CheckError Located) :=
  locatedOf m <$> R.rootOf m.root

/-- **Why a module's `.olean` cannot be read at its location**: it is not there, with or
without parts beside it, or it is there and cannot be read (the exception's text is not
kept: in the model it is any exception, and the reason is the snapshot's alone). -/
def oleanFailed {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) (_ : IO.Error) :
    μ CheckError := do
  if ← CheckerIO.pathExists (modFile loc.dir m "olean") then
    return .internal s!"module {m}: {modFile loc.dir m "olean"} cannot be read"
  let s ← CheckerIO.pathExists (modFile loc.dir m "olean.server")
  let p ← CheckerIO.pathExists (modFile loc.dir m "olean.private")
  let held := (if s then ["olean.server"] else []) ++ (if p then ["olean.private"] else [])
  if held.isEmpty then
    return .internal s!"module {m}: no {m}.olean in {loc.dir}, the search-path directory \
      holding its root {m.root}"
  return .internal s!"module {m}: {" and ".intercalate (held.map (s!"{m}." ++ ·))} without \
    {m}.olean in {loc.dir}"

/-- Read and validate one file. -/
def readPart {μ : Type → Type} [CheckerIO μ] (p : System.FilePath) :
    μ (Except CheckError Part) := do
  let b ← CheckerIO.readBinFile p
  pure (Part.ofBytes p.toString b)

/-- **Read and validate one of a module's files**, `absent` saying why where it cannot be
read. -/
def readPartOr {μ : Type → Type} [CheckerIO μ] (p : System.FilePath)
    (absent : IO.Error → μ CheckError) : μ (Except CheckError Part) :=
  tryCatchThe IO.Error (readPart p) fun e => Except.error <$> absent e

/-- Why a part of a module of the module system cannot be read at its location. -/
def partFailed {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) (ext : String)
    (_ : IO.Error) : μ CheckError := do
  if ← CheckerIO.pathExists (modFile loc.dir m ext) then
    return .internal s!"module {m}: {modFile loc.dir m ext} cannot be read"
  return .internal s!"module {m}: a module of the module system without its {m}.{ext} in \
    {loc.dir}"

/-- The header read's chunk size: one read of the start of the file holds
the imports of 97 % of the CFSG closure's modules. -/
def hdrChunk : USize := 4096

/-- The header read's step: the bytes so far, a read added; done (the
fold's stop) once the walk to the imports array is inside them. -/
def hdrStep (path : String) (acc c : ByteArray) :
    Except (Except CheckError (Option (Array ImportRec))) ByteArray :=
  let acc := acc ++ c
  match hdrWalk acc dataStart with
  | .short => .ok acc
  | _ => .error ((Part.ofBytes path acc).map fun _ => importsPre acc)

/-- The header read at the end of the file: the walk over all of it. -/
def hdrFin (path : String) (acc : ByteArray) : Except CheckError (Option (Array ImportRec)) :=
  (Part.ofBytes path acc).map fun _ => importsPre acc

/-- **A module's imports, read off the start of its exported `.olean`**
at its location (task #425): the file read forward in `hdrChunk` reads
until the walk to the imports array is inside what was read
(`foldChunks`, which stops reading there), the header validated and the
imports decoded from that prefix (`importsPre`).  A file that cannot be read is
`oleanFailed`'s error. -/
def readImportsAt {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) :
    μ (Except CheckError (Array ImportRec)) := do
  let p := modFile loc.dir m "olean"
  match ← tryCatchThe IO.Error (Except.ok <$> foldChunks p hdrChunk ByteArray.empty
      (hdrStep p.toString) (hdrFin p.toString)) (fun e => Except.error <$> oleanFailed loc m e) with
  | .ok (.ok (some imps)) => pure (.ok imps)
  | .ok (.ok none) => pure (.error (undecodable m))
  | .ok (.error e) => pure (.error e)
  | .error e => pure (.error e)

/-- **A module's imports**, off the start of its exported `.olean`, located
on the search path. -/
def moduleImports {μ : Type → Type} [CheckerIO μ] (sp : Roots) (m : Name) :
    μ (Except CheckError (Array ImportRec)) := do
  match ← findModule sp m with
  | .error e => pure (.error e)
  | .ok loc => readImportsAt loc m

/-- **The files of a module a view reads at its location**, each validated
(`ModFiles.viewRegion`).  A part beside a classic `.olean` is no part of it,
and a module of the module system has all three: reading the parts a view
needs says whether they are there, and a server view asks for the private
part's existence besides. -/
def readFilesAt {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) (level : OLeanLevel) :
    μ (Except CheckError ModFiles) := do
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  match ← readPartOr (modFile loc.dir m "olean") (oleanFailed loc m) with
  | .error e => pure (.error e)
  | .ok ex =>
    if level == .exported then return .ok { exported := ex }
    if !(ModFiles.isModule { exported := ex }) then
      let hasServer ← CheckerIO.pathExists (modFile loc.dir m "olean.server")
      let hasPrivate ← CheckerIO.pathExists (modFile loc.dir m "olean.private")
      if hasServer || hasPrivate then
        return .error (bad s!"a module outside the module system (its {m}.olean), with \
          {if hasPrivate then s!"{m}.olean.private" else s!"{m}.olean.server"} beside it \
          in {loc.dir}")
      return .ok { exported := ex }
    match ← readPartOr (modFile loc.dir m "olean.server") (partFailed loc m "olean.server") with
    | .error e => pure (.error e)
    | .ok s =>
      if level == .server then
        if !(← CheckerIO.pathExists (modFile loc.dir m "olean.private")) then
          return .error (bad s!"a module of the module system without its {m}.olean.private \
            in {loc.dir}")
        return .ok { exported := ex, server := some s }
      match ← readPartOr (modFile loc.dir m "olean.private") (partFailed loc m "olean.private") with
      | .error e => pure (.error e)
      | .ok p => pure (.ok { exported := ex, server := some s, «private» := some p })

/-- **The files of a module a view reads**, located on the search path (`findModule`), then
read at that location (`readFilesAt`). -/
def readFiles {μ : Type → Type} [CheckerIO μ] (sp : Roots) (m : Name) (level : OLeanLevel) :
    μ (Except CheckError ModFiles) := do
  match ← findModule sp m with
  | .error e => pure (.error e)
  | .ok loc => readFilesAt loc m level

/-- **One view of a module**, located on the search path. -/
def readView {μ : Type → Type} [CheckerIO μ] (sp : Roots) (m : Name) (level : OLeanLevel) :
    μ (Except CheckError ModDecoded) := do
  match ← readFiles sp m level with
  | .error e => pure (.error e)
  | .ok f =>
    match parseView f level with
    | some d => pure (.ok d)
    | none => pure (.error (viewError m f level))

/-- **One part's name positions**, read off its files at their location. -/
def readPartNamesAt {μ : Type → Type} [CheckerIO μ] (loc : Located) (x : Name × OLeanLevel) :
    μ (Except CheckError NamePositions) := do
  match ← readFilesAt loc x.1 x.2 with
  | .error e => pure (.error e)
  | .ok f =>
    match readNamePositions f x.2 with
    | some ps => pure (.ok ps)
    | none => pure (.error (viewError x.1 f x.2))

/-- **One part's name positions**, located on the search path. -/
def readPartNames {μ : Type → Type} [CheckerIO μ] (sp : Roots) (x : Name × OLeanLevel) :
    μ (Except CheckError NamePositions) := do
  match ← findModule sp x.1 with
  | .error e => pure (.error e)
  | .ok loc => readPartNamesAt loc x

/-- **What a worker reads off the files**: a module's imports (off the start of its
`M.olean`), the files of a view, a part's name positions.  On the search path
(`OleanReads.ofPath`) each is the read of the files it names; a worker and the one-process
mode answer from the tables they read once up front (`ModTables.reads`,
`ConLeche/Driver/Tables.lean`), and where those have nothing, by the same read. -/
structure OleanReads (μ : Type → Type) where
  /-- a module's imports (`moduleImports`) -/
  imports : Name → μ (Except CheckError (Array ImportRec))
  /-- the files of a module's view at a level (`readFiles`) -/
  files : Name → OLeanLevel → μ (Except CheckError ModFiles)
  /-- a part's name positions (`readPartNames`) -/
  names : Name × OLeanLevel → μ (Except CheckError NamePositions)

/-- **The reads on the search path.** -/
def OleanReads.ofPath {μ : Type → Type} [CheckerIO μ] (sp : Roots) : OleanReads μ where
  imports := moduleImports sp
  files := readFiles sp
  names := readPartNames sp

/-- **A module's home read**: its private view loaded (`loadView`, its theorems' values
left in the file; `i` its place in the order the references name), and its three parts
checked against each other (`checkViews`). -/
def readHome {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (m : Name) (i : Nat := 0) :
    μ (Except CheckError (Loaded × Array Expo)) := do
  match ← rd.files m .private with
  | .error e => pure (.error e)
  | .ok f =>
    match loadView i m f with
    | .error e => pure (.error e)
    | .ok l =>
      match checkViews m f l with
      | .ok expo => pure (.ok (l, expo))
      | .error e => pure (.error e)

/-- **All three views of a module, each parsed whole, and the home's check of them**
(`checkViews` over the load): for the tools that compare the views. -/
def readAllViews {μ : Type → Type} [CheckerIO μ] (sp : Roots) (m : Name) :
    μ (Except CheckError (AllViews × Array Expo)) := do
  match ← readFiles sp m .private with
  | .error e => pure (.error e)
  | .ok f =>
    match parseAllViews f with
    | none =>
      let level := ([OLeanLevel.exported, .server].find? fun l => (parseView f l).isNone).getD .private
      pure (.error (viewError m f level))
    | some v =>
      match loadView 0 m f with
      | .error e => pure (.error e)
      | .ok l =>
        match checkViews m f l with
        | .ok expo => pure (.ok (v, expo))
        | .error e => pure (.error e)

end ConLeche.Frontend.Olean
