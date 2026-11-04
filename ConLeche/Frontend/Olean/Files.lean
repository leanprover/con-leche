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
(`ConLeche/Frontend/Olean/Module.lean`), so that on one snapshot of the
files every read of a module sees one value
(`ConLeche/Verify/Frontend/Olean/Files.lean`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The search path: the directories holding `.olean` trees, as
`LEAN_PATH` lists them. -/
abbrev SearchPath := List System.FilePath

/-- The file a module's level is stored in. -/
def modFile (dir : System.FilePath) (m : Name) (ext : String) : System.FilePath :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  (comps m).foldl (· / ·) dir |>.addExtension ext

/-- Where `parseModName`'s scan is. -/
inductive ModNameScan where
  | start | plain | esc | closed

/-- **A module name as the command line spells it** (task #384): its
components separated by dots, a component in `«»` taken literally, dots
included (Lean's own spelling of a name, `String.toName`: Lake's module
`Challenge.«12.34».«5»` is stored as `Challenge/12.34/5.olean`).  `none`
for an empty component or an escape without its `»`.  Unlike
`String.toName`, an unescaped component is never read as a number: a
module name has string components only. -/
def parseModName (s : String) : Option Name :=
  go s.toList .anonymous .start ""
where
  /-- The scan, one character at a time: `st` says where it is (at a
  component's start, in a plain or an escaped component, just after an
  escape's `»`), `cur` holds the component read so far. -/
  go : List Char → Name → ModNameScan → String → Option Name
    | [], n, .plain, cur => some (n.str cur)
    | [], n, .closed, _ => some n
    | [], _, _, _ => none
    | c :: cs, n, .start, _ =>
      if c == '«' then go cs n .esc ""
      else if c == '.' then none
      else go cs n .plain (String.singleton c)
    | c :: cs, n, .plain, cur =>
      if c == '.' then go cs (n.str cur) .start "" else go cs n .plain (cur.push c)
    | c :: cs, n, .esc, cur =>
      if c == '»' then (if cur.isEmpty then none else go cs (n.str cur) .closed "")
      else go cs n .esc (cur.push c)
    | c :: cs, n, .closed, _ => if c == '.' then go cs n .start "" else none

/-- **Where a module's files are** (task #392): the search-path directory
holding them, and which of the two parts beside its `.olean` it holds. -/
structure Located where
  dir : System.FilePath
  hasServer : Bool
  hasPrivate : Bool

/-- The three files of a module, by extension. -/
def partExts : List String := ["olean", "olean.server", "olean.private"]

/-- The real paths of a module's three files in one directory, `none` where
absent. -/
def locateIn {μ : Type → Type} [CheckerIO μ] (m : Name) (d : System.FilePath) :
    μ (System.FilePath × List (Option String)) := do
  let fs ← partExts.mapM fun e => do
    let p := modFile d m e
    if ← CheckerIO.pathExists p then
      return some (← CheckerIO.realPath p).toString
    else return none
  return (d, fs)

/-- **The search path's directories holding any of module `m`'s files**
(`locateModule`), in order: each with the real paths of the three files. -/
def locateHits {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Array (System.FilePath × List (Option String))) := do
  let hs ← sp.mapM (locateIn m)
  return (hs.filter fun h => h.2.any (·.isSome)).toArray

/-- **The module's location from the directories holding its files**
(`locateHits`), or why there is none (`locateModule`). -/
def locateOf (m : Name) (hits : Array (System.FilePath × List (Option String))) :
    Except CheckError (Option Located) := Id.run do
  let some (d, fs) := hits[0]? | return .ok none
  -- the locations: the directories up to real paths, first spelling kept
  let locs := hits.foldl (fun (acc : Array (System.FilePath × List (Option String))) h =>
    if acc.any (·.2 == h.2) then acc else acc.push h) #[]
  let names (xs : Array (System.FilePath × List (Option String))) : String :=
    ", ".intercalate (xs.toList.map (·.1.toString))
  if locs.size > 1 then
    let twice := (List.range 3).any fun i =>
      let rs := locs.toList.filterMap fun l => (l.2[i]?).join
      rs.any fun r => rs.any (· != r)
    if twice then
      return .error (.internal s!"module {m}: its files are in more than one location on \
        the search path ({names locs}); the search path must hold each module once")
    else
      let desc (l : System.FilePath × List (Option String)) : String :=
        let held := (partExts.zip l.2).filterMap fun (e, r) => r.map fun _ => s!"{m}.{e}"
        s!"{", ".intercalate held} in {l.1}"
      return .error (.internal s!"module {m}: its parts are split across directories \
        ({"; ".intercalate (locs.toList.map desc)}); a module's files must be in one directory")
  match fs with
  | [o, s, p] =>
    if o.isNone then
      let held := [("olean.server", s), ("olean.private", p)].filterMap fun (e, r) =>
        r.map fun _ => s!"{m}.{e}"
      return .error (.internal s!"module {m}: {" and ".intercalate held} without \
        {m}.olean in {d}")
    return .ok (some ⟨d, s.isSome, p.isSome⟩)
  | _ => return .error (.internal s!"module {m}: locating its files")

/-- **Find a module, strictly** (task #392).  Lean takes the first
search-path directory holding `M.olean` and reads the other parts beside
it; a copy further down is ignored, so two copies would let two tools
(or two search-path orders) read two different modules under one name.
Here every directory is looked at, each of the module's files
(`M.olean`, `M.olean.server`, `M.olean.private`) taken by its real path,
so that a directory listed twice, or reached through a symbolic link, is
one location.  Malformed input (`.internal`, exit 3):

* one of the files with two real paths: the module is in two places;
* the directories holding some of the files not all holding the same
  ones: the parts are split across directories;
* parts without an `.olean` beside them.

`none`: the module has no file on the search path.  Whether the parts
the `.olean` needs are there is `readModule`'s check (it depends on the
exported part's module-system flag). -/
def locateModule {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError (Option Located)) := do
  match ← tryCatchThe IO.Error (Except.ok <$> locateHits sp m) (fun e => pure (.error e)) with
  | .ok hits => return locateOf m hits
  | .error e => return .error (.internal s!"module {m}: locating its files: {e}")

/-- The module's location, `.internal` if it has no file on the search
path. -/
def findModule {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError Located) := do
  match ← locateModule sp m with
  | .ok (some l) => pure (.ok l)
  | .ok none => pure (.error (.internal s!"module {m}: no .olean on the search path"))
  | .error e => pure (.error e)

/-- Read and validate one file. -/
def readPart {μ : Type → Type} [CheckerIO μ] (p : System.FilePath) :
    μ (Except CheckError Part) := do
  let b ← CheckerIO.readBinFile p
  pure (Part.ofBytes p.toString b)

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
imports decoded from that prefix (`importsPre`). -/
def readImportsAt {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) :
    μ (Except CheckError (Array ImportRec)) := do
  let p := modFile loc.dir m "olean"
  match ← foldChunks p hdrChunk ByteArray.empty (hdrStep p.toString)
      (hdrFin p.toString) with
  | .ok (some imps) => pure (.ok imps)
  | .ok none => pure (.error (undecodable m))
  | .error e => pure (.error e)

/-- A module's imports off the start of its exported `.olean`, located on
the search path; `none` where the module has no file there. -/
def readImports {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError (Option (Array ImportRec))) := do
  match ← locateModule sp m with
  | .error e => pure (.error e)
  | .ok none => pure (.ok none)
  | .ok (some loc) => pure ((← readImportsAt loc m).map some)

/-- **The bytes of a module's exported `.olean`, validated**, at its
location. -/
def readExpAt {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) :
    μ (Except CheckError Part) :=
  readPart (modFile loc.dir m "olean")

/-- **A module's exported part, read in full** (`parseExported`). -/
def readExported {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError ModDecoded) := do
  match ← findModule sp m with
  | .error e => pure (.error e)
  | .ok loc =>
    match ← readExpAt loc m with
    | .error e => pure (.error e)
    | .ok ex => pure (parseExported m ex)

/-- **A module's exported part, read lightly** (`readLight`), with the part,
for the reads of its constants (`readEntry`, `readStmts`). -/
def readExportedLight {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError (Part × LightPart)) := do
  match ← findModule sp m with
  | .error e => pure (.error e)
  | .ok loc =>
    match ← readExpAt loc m with
    | .error e => pure (.error e)
    | .ok ex =>
      match readLight (Region.single ex) ex.root with
      | some l => pure (.ok (ex, l))
      | none => pure (.error (undecodable m))

/-- **Read one module in full** at its location: the exported part alone,
then the other parts.  A part beside a classic `.olean` is no part of it,
and a module of the module system has all three. -/
def readModuleAt {μ : Type → Type} [CheckerIO μ] (loc : Located) (m : Name) :
    μ (Except CheckError ModRead) := do
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  match ← readExpAt loc m with
  | .error e => pure (.error e)
  | .ok ex =>
    match parseExported m ex with
    | .error e => pure (.error e)
    | .ok er =>
      if !er.isModule then
        if loc.hasServer || loc.hasPrivate then
          return .error (bad s!"a module outside the module system (its {m}.olean), with \
            {if loc.hasPrivate then s!"{m}.olean.private" else s!"{m}.olean.server"} beside it \
            in {loc.dir}")
        return .ok (classicModule m er)
      if !loc.hasServer then
        return .error (bad s!"a module of the module system without its {m}.olean.server in {loc.dir}")
      if !loc.hasPrivate then
        return .error (bad s!"a module of the module system without its {m}.olean.private in {loc.dir}")
      match ← readPart (modFile loc.dir m "olean.server"),
          ← readPart (modFile loc.dir m "olean.private") with
      | .ok s, .ok p => pure (parseModule m er ex s p)
      | .error e, _ | _, .error e => pure (.error e)

/-- **Read one module in full**, located on the search path. -/
def readModule {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError ModRead) := do
  match ← findModule sp m with
  | .error e => pure (.error e)
  | .ok loc => readModuleAt loc m

end ConLeche.Frontend.Olean
