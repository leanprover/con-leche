module

public import ConLeche.Driver.CheckMain
public import ConLeche.Driver.Reach
public import ConLeche.Driver.Compare
import ConLeche.Verify.Cached.DeclNames

@[expose] public section

/-!
# The worker: one module checked against the records it is checked against

`con-leche --olean --module --search-path=DIRS -- M` checks the module `M` alone (DESIGN #460 §3),
in the phases below, generic in the IO class like `checkMainG`, its reads of the files `rd`
(`OleanReads`).  Its theorem in the model is `ConLeche/Verify/Driver/Worker.lean`'s.  The run of
`--module` gives it the reads answered from its tables (`workerTables`,
`ConLeche/Driver/Tables.lean`: every module its header fixpoint loads located once, up front).

1. **The home** (`homeOf`, off `M`'s private part's files, which give the theorems' values'
   region too; under `--module` the tables hold the files, read once): `M`'s private view loaded (`loadAt`, its theorems' values left in
   the file) and its three parts checked against each other (`checkViews`: what `M` presents to
   its importers refines its own constants; a mismatch exit 1).
2. **The reads** (`workerReads`): the header fixpoint, the name index of every loaded part, Lean's
   clash rule over every loaded name, freshness of `M`'s names.
3. **The own records** (`ownRecords`): the loaded constants, unsafe and partial ones left out,
   emitted from every own constant (`emitAll`, `declsOf`): a name that is not `M`'s is a context
   read, not a record.  The ground hoist (`hoistNatOpGround`) moves a pinned `Nat` operation's
   ground ahead of it, as `preparePrelude` does to a stream.
4. **The reach** (`reach`): the context records, from the names the own records read and the
   names their theorems' values read, validated; their names distinct (`namesNodupGo`).
5. **The jobs**: the index of the context's records followed by the own records (`buildIndex
   (ctx ++ own)`), and the own records' jobs alone, each at its view (everything of the context
   visible), on the worker map; a theorem's value read in its job (`readValue`).  Every own job
   passing is a run of the own records from the context's environment (`checkDecls_of_jobs_from`).

Exit 0 needs every phase; a failure's exit code is its error's (`CheckError.exitCode`).
-/

namespace ConLeche.Driver

open ConLeche.Cached (recordReads needsGo NeedsSt litNeeds)

open ConLeche ConLeche.Frontend.Olean

/-- **A module's own records**: its loaded constants, unsafe and partial ones left out, their
inductive groups checked (`blocksOk`), emitted from every one of them; a name the emission meets
that is not among them is a context read. -/
def ownRecords (l : Loaded) : Except (CheckError × Nat) (Array Declaration) :=
  let mg := mergedOfList (l.constants.toList.filter (!·.skipped))
  match blocksOk mg with
  | .error e => .error (e, 0)
  | .ok () => declsOf (emitAll mg mg.order)

/-- **A certified operation's pin ground**: the names its install check asks resolved beyond
`pinFootprint`, over every pin variant of `pins` (`divModPinGuard`, `divModCertsGuard`,
`divModEnvGuard`): the constants of the variant's pinned defining expression, of its certificates'
proofs and statements, its type pins' names and types, and `Eq`.  Empty at every other name.  At
the operation's home these are no read of any of its records: the certificates are the install
check's own terms (DESIGN #446). -/
def pinGround (pins : List NatOpPinSet) (c : Name) : Array Name :=
  if !natDivModNames.contains c then #[] else
  let go : Std.HashSet Expr × Array Name → Expr → Std.HashSet Expr × Array Name :=
    fun x e => Frontend.usedConstsGo x.1 x.2 e
  let x := (divModCertStmts c).foldl (fun x st => go (st.1.foldl go x) st.2) ({}, #[eqName])
  (pins.foldl (fun x ps =>
    (divModTypePins ps c).foldl (fun x p => go (x.1, x.2.push p.1) p.2)
      ((divModCertProofs ps c).foldl go (go x (divModDeclPin ps c)))) x).2

/-- **The reach's roots**: what each own record reads, what each own constant's load read
(a theorem's value's names, which its record holds as a reference), and the pin ground of each
own certified operation (`pinGround` over `natOpPinSets`) that a loaded module holds; an unsafe
or partial own constant is no record, and what it reads is no root.  A name a pinned own
constant's fast path reads (`pinFootprint`) that no loaded module holds is left to that
constant's own check, which asks it stored (`natOpGuard`) and gives the stream path's verdict;
so is a name of a pin ground no loaded module holds (another toolchain's variant's, or one the
check then finds absent and declines). -/
def ownRoots (ix : NameIndex) (l : Loaded) (ds : Array Declaration) : Array Name :=
  let fp : Std.HashSet Name := l.constants.foldl
    (fun s c => (pinFootprint c.name).foldl (fun s n => s.insert n) s) {}
  (ds.foldl (fun acc d => acc ++ recordReads d) #[] ++
    l.constants.foldl (fun acc (c : CEntry) =>
      if c.skipped then acc else acc ++ c.uses.toArray) #[]).filter
    (fun x => ix.first.contains x || !fp.contains x) ++
  (l.constants.foldl (fun acc (c : CEntry) =>
      if c.skipped then acc else acc ++ pinGround natOpPinSets c.name) #[]).filter
    ix.first.contains

/-- What an own theorem's record mentions, which its reference does not say: what the load read
off the file (for the ground hoist). -/
def ownUses (l : Loaded) : Declaration → Array Name
  | .thmDecl cv v =>
    match l.constants.find? (·.name == cv.name) with
    | some c => c.uses.toArray
    | none => Declaration.usedConsts (.thmDecl cv v)
  | d => d.usedConsts

/-- **A module's own names**: every constant of its private view, unsafe and partial ones
included (no context record may hold one). -/
def ownNames (l : Loaded) : Std.HashSet Name := l.constants.foldl (fun s c => s.insert c.name) {}

/-- **No name twice**, one hash set along the list. -/
def namesNodupGo (s : Std.HashSet Name) : List Name → Bool
  | [] => true
  | n :: ns => !s.contains n && namesNodupGo (s.insert n) ns

/-! ## A compared challenge's copies (task #619)

At a compared challenge (`x`, the imports a run adds to its header: `import all` of its solution,
`Graph.solutionImport`), the worker loads the solution with the challenge's own imports, under
Lean's clash rule over every loaded name.  A record of the challenge some name of which a loaded
module stores is a **copy**: not the challenge's own record, its names read from the loads into
the context, as any name the challenge imports.  A copy must be what the loaded constant is
(`copyCheck`), up to the names of its level parameters (ruling B of #619):

* a hole (an axiom; a definition whose value uses `sorryAx`), a theorem or an opaque constant: one
  constant that only its statement describes (`IsModel` reads it so), of the loaded constant's
  statement.  For a theorem, Lean's own rule for two loaded copies of one name (`subsumesInfo`);
* a definition: the loaded definition, its value too;
* an inductive block: the context's record of its names, the same record, one the kernel's reader
  reads (`BlockRead`); a quotient record never.

Every other record is the challenge's own, checked as any module's; a hole among them is one the
solution does not fill (`ownHoleOk`). -/

/-- **A record some name of which a loaded module stores.** -/
def loadedRec (ix : NameIndex) (d : Declaration) : Bool := (Modular.declNames d).any ix.first.contains

/-- **The own records** of a worker that adds the imports `x`, before the hoist: every emitted
record; at a compared challenge (`x` not empty), those no name of which is loaded. -/
def ownRecs (x : Array ImportRec) (ix : NameIndex) (ds : Array Declaration) : Array Declaration :=
  if x.isEmpty then ds else ds.filter (!loadedRec ix ·)

/-- **The copies** (see above): none, but at a compared challenge, the emitted records some name of
which is loaded. -/
def copyRecs (x : Array ImportRec) (ix : NameIndex) (ds : Array Declaration) : Array Declaration :=
  if x.isEmpty then #[] else ds.filter (loadedRec ix)

/-- **The own names** of a worker that adds the imports `x`: every constant of the private view
(`ownNames`); at a compared challenge, those no loaded module stores. -/
def ownNamesOf (x : Array ImportRec) (ix : NameIndex) (l : Loaded) : Std.HashSet Name :=
  if x.isEmpty then ownNames l
  else l.constants.foldl (fun s c => if ix.first.contains c.name then s else s.insert c.name) {}

/-- **The reach's roots** of a worker that adds the imports `x`: what the own records read
(`ownRoots`); at a compared challenge, what the own records and the own constants read, and the
copies' names, whose loaded constants the comparison reads (what a copy's value reads is no
root: the copy is the loaded constant). -/
def rootsAt (x : Array ImportRec) (ix : NameIndex) (l : Loaded) (ds : Array Declaration) :
    Array Name :=
  if x.isEmpty then ownRoots ix l ds
  else
    ownRoots ix { l with constants := l.constants.filter (!ix.first.contains ·.name) }
      (ownRecs x ix ds) ++
    (copyRecs x ix ds).flatMap fun d => (Modular.declNames d).toArray

/-- **The statement a copy may be read by**: a hole's (an axiom; a definition whose value uses
`sorryAx`), a theorem's or an opaque constant's; none for any other record. -/
def copyStmt? : Declaration → Option ConstantVal
  | .axiomDecl cv => some cv
  | .defnDecl cv v _ => if Expr.mentionsAnyConstC [sorryAxName] v then some cv else none
  | .opaqueDecl cv _ => some cv
  | .thmDecl cv _ => some cv
  | _ => none

/-- **A definition of the challenge, the loaded one** up to the names of its level parameters (the
loaded one renamed: it is checked, so its level parameters are all among its names). -/
def sameDefUpToLevels (c c' : ConstantInfo) : Bool :=
  let ps := c.toConstantVal.levelParams
  let ps' := c'.toConstantVal.levelParams
  if ps == ps' then c.beqP c' else Cached.levelsRenaming ps ps' && (c'.atLpsC ps).beqP c

/-- **Two blocks, the same record.** -/
def copyRecEq : Declaration → Declaration → Bool
  | .indDecl b n, .indDecl b' n' => n == n' && listBeqBy ConstantInfo.beqP b b'
  | _, _ => false

/-- **A block the kernel's reader reads** (`readBlock`), its constructors' names distinct and in
the block's order; true for any other record. -/
def blockReadB : Declaration → Bool
  | .indDecl block nP =>
    match readBlock nP block with
    | .error _ => false
    | .ok p =>
      let names := p.allCtors.map (·.1.name)
      namesNodupGo {} names &&
        match blockSplit block with
        | some (_, cs, _) => names == cs.map (·.1.name)
        | none => true
  | _ => true

/-- **A copy against the loaded constants of its names** (see above; `r`, the context; `owner`,
the record of each of its names). -/
def copyCheck (m : Name) (ld : HeaderLoads) (ix : NameIndex) (r : Reach)
    (owner : Std.HashMap Name Nat) (d : Declaration) : Except CheckError Unit :=
  let n := recKey d
  let src := ((ix.first[n]?).map fun c => ld.nameAt c.mod).getD .anonymous
  if n == quotSoundName || n == sorryAxName then
    let what := if n == quotSoundName then "the quotient's axiom" else "the placeholder axiom"
    .error (.notImplemented s!"{n}: a hole at {what}, which installs no axiom of its own; \
      con-leche cannot fill it")
  else if !basisNamesOk d then
    .error (.invalid s!"module {m} declares {n}, a name the checker reserves")
  else
  match owner[n]? with
  | none => .error (.internal s!"{n}: the context does not hold the loaded constant")
  | some k =>
    let e := r.ctx.getD k default
    let h := r.homes.getD k .anonymous
    let ci? := (declConstants e).find? (·.toConstantVal.name == n)
    match copyStmt? d, d, ci? with
    | some cv, _, some ci =>
      if Cached.sameCvUpToLevels cv ci.toConstantVal then .ok ()
      else .error (.invalid s!"{n}: the constant of {h} is not of the statement of {m}'s \
        {recKind d}")
    | none, .defnDecl cv v hint, some ci =>
      if sameDefUpToLevels (.defnInfo cv v hint) ci then .ok ()
      else .error (.invalid s!"{n}: the constant of {h} is not {m}'s definition")
    | none, .indDecl .., _ =>
      if copyRecEq d e && blockReadB d then .ok ()
      else .error (.invalid s!"{n}: the constants of {h} are not {m}'s inductive type")
    | _, _, none => .error (.internal s!"{n}: the context's record does not declare it")
    | none, _, _ => .error (.invalid s!"module {m} declares {n}, which the module {src} it \
        loads stores")

/-- **A hole** (an axiom other than a built-in one; a definition, opaque constant or theorem whose
value uses `sorryAx`; `uses`, what a theorem's value read off the file). -/
def isHoleRec (uses : Declaration → Array Name) : Declaration → Bool
  | .axiomDecl cv => !Cached.builtinAxiomName cv.name
  | .defnDecl _ v _ | .opaqueDecl _ v => Expr.mentionsAnyConstC [sorryAxName] v
  | d@(.thmDecl ..) => (uses d).contains sorryAxName
  | _ => false

/-- **A hole of the challenge's own records** (an axiom other than a built-in one, a definition,
opaque constant or theorem whose value uses `sorryAx`; `uses`, what a theorem's value read off the
file): the solution does not fill it. -/
def ownHoleOk (m : Name) (uses : Declaration → Array Name) (d : Declaration) :
    Except CheckError Unit :=
  if isHoleRec uses d then .error (.invalid s!"{recKey d}: a hole of {m} no loaded module fills (the \
    solution has no constant of this name)")
  else .ok ()

/-- **Every copy against the loaded constants of its names** (`copyCheck`). -/
def copiesOk (m : Name) (x : Array ImportRec) (wr : WorkerReads) (r : Reach)
    (ds : Array Declaration) : Except CheckError Unit :=
  let owner := ownerMap r.ctx
  (copyRecs x wr.index ds).toList.forM (copyCheck m wr.loads wr.index r owner)

/-- **No hole among the own records** of a compared challenge (`ownHoleOk`); nothing to ask of
any other worker's. -/
def ownHolesOk (m : Name) (x : Array ImportRec) (uses : Declaration → Array Name)
    (ix : NameIndex) (ds : Array Declaration) : Except CheckError Unit :=
  if x.isEmpty then .ok () else (ownRecs x ix ds).toList.forM (ownHoleOk m uses)

/-- **What a worker has read and checked before its jobs.** -/
structure WorkerRead where
  /-- the module's private view, loaded -/
  home : Loaded
  /-- each own constant's exported level (`checkViews`) -/
  expo : Array Expo
  /-- the header fixpoint, the name index, the clash rule's copies -/
  reads : WorkerReads
  /-- the own records, as the emission gives them -/
  emitted : Array Declaration
  /-- the own records, in the order they are checked -/
  own : Array Declaration
  /-- the context -/
  reach : Reach
  /-- the records moved by the ground hoist -/
  hoisted : Array Name
  /-- the home's region, which the theorems' values are read from (`readValue`): the home's
  files, read once -/
  values : ValueCache

/-- A line of the worker's heartbeat (`--progress`). -/
def workerSay {μ : Type → Type} [CheckerIO μ] (pace : Pace) (t0 : Nat) (line : String) : μ Unit :=
  CheckerIO.liftIO do
    if pace.on then
      let e ← IO.getStderr
      let ms := (← IO.monoMsNow) - t0
      e.putStrLn s!"con-leche: read: {line} t={ms / 1000}.{(ms % 1000) / 100}s{← residentSet}"
      e.flush

/-- **Phases 1–4 of the worker at module `m`** (see the module docstring); `x` the imports a run
adds to its header (a compared challenge's solution: its own records are those no loaded module
stores, `ownRecs`, and its copies are checked against the loaded constants, `copiesOk`). -/
def workerRead {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (m : Name) (pace : Pace)
    (t0 jobs : Nat) (x : Array ImportRec := #[]) : μ (Except (CheckError × Nat) WorkerRead) := do
  match ← rd.files m .private with
  | .error e => pure (.error (e, 0))
  | .ok f =>
  match homeOf m f with
  | .error e => pure (.error (e, 0))
  | .ok (l, expo) =>
    -- the home's files give the values' region too
    let values : ValueCache := match f.viewRegion .private with
      | some (r, _) => { idx := 0, region := some r }
      | none => {}
    workerSay pace t0 s!"the home of {m}: {l.constants.size} constants, views checked"
    match ← workerReads rd m jobs x with
    | .error e => pure (.error (e, 0))
    | .ok wr =>
      if !x.isEmpty && wr.loads.index.contains m then
        return .error (.invalid s!"the module {m} is loaded by the imports added to its \
          header: the solution's closure holds the challenge", 0)
      workerSay pace t0 s!"loads {wr.loads.order.size} modules, {wr.index.first.size} names; \
        {wr.clashes.size} names held twice, merged"
      match ownRecords l with
      | .error e => pure (.error e)
      | .ok ds =>
        match ownHolesOk m x (ownUses l) wr.index ds with
        | .error e => pure (.error (e, 0))
        | .ok () =>
        match ← reach rd m wr (ownNamesOf x wr.index l) (rootsAt x wr.index l ds) with
        | .error e => pure (.error (e, 0))
        | .ok r =>
          if !namesNodupGo {} (r.ctx.toList.flatMap Modular.declNames) then
            return .error (.invalid "a context record declares one of its names twice", 0)
          match copiesOk m x wr r ds with
          | .error e => pure (.error (e, 0))
          | .ok () =>
          let mods := (r.homes.foldl (fun (s : Std.HashSet Name) h => s.insert h) {}).size
          workerSay pace t0 s!"reach: {r.ctx.size} records from {mods} modules, \
            {r.completed.size} completed, {r.inferred} flags inferred"
          let (ownDs, hoisted) := Frontend.hoistNatOpGround (ownUses l) (ownRecs x wr.index ds)
          pure (.ok { home := l, expo, reads := wr, emitted := ds, own := ownDs, reach := r,
                      hoisted, values })

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

/-- **A copy, for the report** (`--compare`'s worker): a hole and the kind of what justifies it,
or a constant the challenge restates, with the module it is read from. -/
def copyLine (w : WorkerRead) (d : Declaration) : String :=
  let n := recKey d
  let h := ((ownerMap w.reach.ctx)[n]?.map fun k => w.reach.homes.getD k .anonymous).getD .anonymous
  let kind := tagKind (((w.reads.index.first[n]?).bind w.reads.index.at |>.map (·.tag)).getD 8)
  if isHoleRec (ownUses w.home) d then
    let label := match d with
      | .axiomDecl _ => "axiom"
      | d => s!"{recKind d} := sorry"
    s!"hole {n} ({label}) justified by {h}'s {kind}"
  else s!"{recKind d} {n}: {h}'s {kind}"

/-- **The worker at module `m`**, generic in the IO class: phases 1–4 (`workerRead`, its reads of
the files `rd`), then the own records' jobs over the index of the context and the own records, and
the verdict.  `alone`: the process's one check (`--module`); else one module of the one-process
mode, whose data is freed with it (nothing marked persistent, no statistics) and whose verdict
line names it.  `x`: the imports a run adds to the header (a compared challenge's solution, whose
accept then lists the copies, `copyLine`). -/
def checkModuleG {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (sp : Roots) (m : Name)
    (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat) (alone : Bool := true)
    (x : Array ImportRec := #[]) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  CheckerIO.liftIO (readStarts pace s!"module {m}")
  match ← workerRead rd m pace t0 jobs x with
  | .error (e, _) =>
    diagLine s!"con-leche: module {m}: {e} ({modeTag})"
    return e.exitCode
  | .ok w =>
    if w.hoisted.size > 0 then
      diagLine s!"con-leche: {if alone then "" else s!"module {m}: "}{w.hoisted.size} \
        declarations hoisted ahead of the pinned Nat operations they ground: \
        {String.intercalate ", " (w.hoisted.toList.map toString)}"
    let ds := w.reach.ctx ++ w.own
    let tIndex ← clockMs
    let J ← CheckerIO.liftIO (if alone then Jobs.build ds else pure (Jobs.plain ds))
    let tParse ← clockMs
    if pace.on then
      diagLine s!"con-leche: parse done: {w.own.size} records of module {m} after \
        {w.reach.ctx.size} context records t={ConLeche.Cached.msSecs (tParse - t0)}s \
        (parse {ConLeche.Cached.msSecs (tParse - t0)}s)"
    let c ← verdictG modeTag w.own.size t0 ds
      (← checkOleansG mode maxNatSize pace t0 tIndex tParse jobs sp #[⟨m, w.home.frontier⟩] J
        w.reach.ctx.size alone w.values)
      (if alone then "" else s!"module {m}: ")
    if c == 0 && !x.isEmpty then
      let cs := copyRecs x w.reads.index w.emitted
      CheckerIO.liftIO do
        let o ← IO.getStdout
        o.putStrLn s!"con-leche: {if alone then "" else s!"module {m}: "}{cs.size} \
          declarations of {m} are the loaded constants of their names"
        for d in cs do o.putStrLn s!"con-leche: {copyLine w d}"
    return c

end ConLeche.Driver
