module

public import ConLeche.Driver.CheckMain
public import ConLeche.Driver.Reach

@[expose] public section

/-!
# The worker: one module checked against the records it is checked against

`con-leche --olean --module --search-path=DIRS -- M` checks the module `M` alone (DESIGN #460 §3),
in the phases below, generic in the IO class like `checkMainG`.  Its theorem in the model is
`ConLeche/Verify/Driver/Worker.lean`'s.

1. **The home** (`readHome`): `M`'s private view loaded (`loadAt`, its theorems' values left in
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

open ConLeche ConLeche.Frontend.Olean

/-- **A module's own records**: its loaded constants, unsafe and partial ones left out, their
inductive groups checked (`blocksOk`), emitted from every one of them; a name the emission meets
that is not among them is a context read. -/
def ownRecords (l : Loaded) : Except (CheckError × Nat) (Array Declaration) :=
  let mg := mergedOfList (l.constants.toList.filter (!·.skipped))
  match blocksOk mg with
  | .error e => .error (e, 0)
  | .ok () => declsOf (emitAll mg mg.order)

/-- **The reach's roots**: what each own record reads, and what each own constant's load read
(a theorem's value's names, which its record holds as a reference).  A name a pinned own
constant's fast path reads (`pinFootprint`) that no loaded module holds is left to that
constant's own check, which asks it stored (`natOpGuard`) and gives the stream path's verdict. -/
def ownRoots (ix : NameIndex) (l : Loaded) (ds : Array Declaration) : Array Name :=
  let fp : Std.HashSet Name := l.constants.foldl
    (fun s c => (Modular.pinFootprint c.name).foldl (fun s n => s.insert n) s) {}
  (ds.foldl (fun acc d => acc ++ recordReads d) #[] ++
    l.constants.foldl (fun acc (c : CEntry) => acc ++ c.uses.toArray) #[]).filter
    fun x => ix.first.contains x || !fp.contains x

/-- What an own theorem's record mentions, which its reference does not say: what the load read
off the file (for the ground hoist). -/
def ownUses (l : Loaded) : Declaration → Array Name
  | .thmDecl cv v =>
    match l.constants.find? (·.name == cv.name) with
    | some c => c.uses.toArray
    | none => Declaration.usedConsts (.thmDecl cv v)
  | d => d.usedConsts

/-- **No name twice**, one hash set along the list. -/
def namesNodupGo (s : Std.HashSet Name) : List Name → Bool
  | [] => true
  | n :: ns => !s.contains n && namesNodupGo (s.insert n) ns

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

/-- A line of the worker's heartbeat (`--progress`). -/
def workerSay {μ : Type → Type} [CheckerIO μ] (pace : Pace) (t0 : Nat) (line : String) : μ Unit :=
  CheckerIO.liftIO do
    if pace.on then
      let e ← IO.getStderr
      let ms := (← IO.monoMsNow) - t0
      e.putStrLn s!"con-leche: read: {line} t={ms / 1000}.{(ms % 1000) / 100}s{← residentSet}"
      e.flush

/-- **Phases 1–4 of the worker at module `m`** (see the module docstring). -/
def workerRead {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) (pace : Pace)
    (t0 jobs : Nat) : μ (Except (CheckError × Nat) WorkerRead) := do
  match ← readHome sp m with
  | .error e => pure (.error (e, 0))
  | .ok (l, expo) =>
    workerSay pace t0 s!"the home of {m}: {l.constants.size} constants, views checked"
    match ← workerReads sp m jobs with
    | .error e => pure (.error (e, 0))
    | .ok wr =>
      workerSay pace t0 s!"loads {wr.loads.order.size} modules, {wr.index.first.size} names; \
        {wr.clashes.size} names held twice, merged"
      match ownRecords l with
      | .error e => pure (.error e)
      | .ok ds =>
        let own : Std.HashSet Name := l.constants.foldl (fun s c => s.insert c.name) {}
        match ← reach sp m wr own (ownRoots wr.index l ds) with
        | .error e => pure (.error (e, 0))
        | .ok r =>
          if !namesNodupGo {} (r.ctx.toList.flatMap Modular.declNames) then
            return .error (.invalid "a context record declares one of its names twice", 0)
          let mods := (r.homes.foldl (fun (s : Std.HashSet Name) h => s.insert h) {}).size
          workerSay pace t0 s!"reach: {r.ctx.size} records from {mods} modules, \
            {r.completed.size} completed, {r.inferred} flags inferred"
          let (ownDs, hoisted) := Frontend.hoistNatOpGround (ownUses l) ds
          pure (.ok { home := l, expo, reads := wr, emitted := ds, own := ownDs, reach := r,
                      hoisted })

/-- **The worker at module `m`**, generic in the IO class: phases 1–4 (`workerRead`), then the own
records' jobs over the index of the context and the own records, and the verdict. -/
def checkModuleG {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) (mode : CheckMode)
    (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  CheckerIO.liftIO (readStarts pace s!"module {m}")
  match ← workerRead sp m pace t0 jobs with
  | .error (e, _) =>
    diagLine s!"con-leche: module {m}: {e} ({modeTag})"
    return e.exitCode
  | .ok w =>
    if w.hoisted.size > 0 then
      diagLine s!"con-leche: {w.hoisted.size} declarations hoisted ahead of \
        the pinned Nat operations they ground: \
        {String.intercalate ", " (w.hoisted.toList.map toString)}"
    let ds := w.reach.ctx ++ w.own
    let tIndex ← clockMs
    let J ← CheckerIO.liftIO (Jobs.build ds)
    let tParse ← clockMs
    if pace.on then
      diagLine s!"con-leche: parse done: {w.own.size} records of module {m} after \
        {w.reach.ctx.size} context records t={ConLeche.Cached.msSecs (tParse - t0)}s \
        (parse {ConLeche.Cached.msSecs (tParse - t0)}s)"
    verdictG modeTag w.own.size t0 ds
      (← checkOleansG mode pace t0 tIndex tParse jobs sp #[⟨m, w.home.frontier⟩] J
        w.reach.ctx.size)

end ConLeche.Driver
