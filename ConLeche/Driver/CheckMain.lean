module

public import ConLeche.Frontend.Prelude
public import ConLeche.Driver.StreamParse
public import ConLeche.Driver.Run
public import ConLeche.Frontend.Olean

/-!
# The driver's sequencing, generic in the IO class (tasks #424, #450)

`checkMainG` is the driver of one run — the built-in prelude, the
input's records (a stream, read through the class's file operations),
the preparation, the fold, the verdict line and the exit code —
written against `CheckerIO`.  The binary runs it at `IO` (`Cli.lean`
runs it through `runReq`); the theorem below is about its run in the
model `ModelIO` over a snapshot of the files.  The output, the clock
the index build (`Jobs.build`, `ConLeche/Driver/CheckPool.lean`) and the
check phase with its thread pool (`checkDeclsIO`,
`ConLeche/Driver/Run.lean`) are `IO` actions handed to
`CheckerIO.liftIO`; the check's result carries its proof in its type.

* `checkMainG_ndjson_accept`: an exit 0 on a stream means the file's
  bytes in the snapshot, as one chunk, parse to records that
  `checkDecls` accepts once prepared with the built-in prelude — the
  hypothesis of the main corollary (`ConLeche.no_False_declaration`)
  about the file itself, under the assumptions stated in
  `ConLeche/Frontend/CheckerIO.lean`.
-/

@[expose] public section

/-- Exit codes follow the lean kernel arena convention: 0 all
declarations accepted, 1 a declaration was rejected as invalid, 2 the
checker declined (positively detected an unsupported feature), 3 bad
usage, malformed input, or an internal failure of unclear cause. -/
def ConLeche.CheckError.exitCode : CheckError → UInt8
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- No error is an accept. -/
theorem ConLeche.CheckError.exitCode_ne_zero (e : ConLeche.CheckError) : e.exitCode ≠ 0 := by
  cases e <;> simp [ConLeche.CheckError.exitCode]

namespace ConLeche.Driver

/-- A declaration's display name, for the direct-parse `Declaration` records.  The
formatting itself lives beside the checker (`ConLeche.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : ConLeche.Declaration → String := ConLeche.Cached.declCLabel

open ConLeche

/-- **What a run reads**: a lean4export stream, or the import closure of
root modules read from their `.olean` files along a search path.  Either
read ends in `Declaration` records, and everything after it works on
those. -/
inductive Input where
  | ndjson (file : String)
  | oleans (searchPath : List System.FilePath) (roots : Array ConLeche.Name)
      (constants : Option (Array ConLeche.Name))

/-- The input's name in a diagnostic. -/
def Input.label : Input → String
  | .ndjson f => f
  | .oleans _ rs _ => String.intercalate " " (rs.toList.map toString)

/-- A line on stderr: a diagnostic (`liftIO`). -/
@[inline] def diagLine {μ : Type → Type} [CheckerIO μ] (s : String) : μ Unit :=
  CheckerIO.liftIO do
    let e ← IO.getStderr
    e.putStrLn s
    e.flush

/-- A line on stdout, flushed: the verdict (`liftIO`). -/
@[inline] def outLine {μ : Type → Type} [CheckerIO μ] (s : String) : μ Unit :=
  CheckerIO.liftIO do
    let o ← IO.getStdout
    o.putStrLn s
    o.flush

/-- The monotonic clock in milliseconds, for diagnostics (`liftIO`). -/
@[inline] def clockMs {μ : Type → Type} [CheckerIO μ] : μ Nat :=
  CheckerIO.liftIO IO.monoMsNow

/-- The input's declaration records: the stream's, by the stream parse
(`parseStreamG`), or the closure's, by the `.olean` reader
(`Frontend.Olean.readOleans`), whose theorems hold references to their values, with what
their checks need to read them. -/
def readInputG {μ : Type → Type} [CheckerIO μ] (inp : Input) (pace : Pace) (jobs : Nat) :
    μ (Except (CheckError × Nat)
      (Array Declaration × Option (List System.FilePath × Frontend.Olean.OleanRead))) :=
  match inp with
  | .ndjson file => do
    return (← parseStreamG file jobs).map fun r => (r.decls, none)
  | .oleans sp roots cs => do
    return (← Frontend.Olean.readOleans sp roots cs jobs pace).map fun rd => (rd.decls, some (sp, rd))

/-- What a record mentions, for the preparation: the record's expressions say it, except a
theorem's read from an `.olean`, whose load read it off the file. -/
def usedOf : Option (List System.FilePath × Frontend.Olean.OleanRead) → Declaration → Array Name
  | none => Declaration.usedConsts
  | some (_, rd) => fun d => (rd.thmUses d).getD d.usedConsts

/-! ## The check phase of an `--olean` run

A theorem's value is read in its check, through the class, so the check phase's
reads are in the model like the load's; the check itself is a pure function of what
they return.  What the phase establishes is then a theorem about the run in the
model (`ConLeche/Verify/Driver/Oleans.lean`), not a value's type. -/

/-- Record `d`'s check at position `t`, its error tagged with the position. -/
def jobRun (mode : CheckMode) {ds : Array Declaration} (J : Jobs ds) (t : Nat) (d : Declaration) :
    Except (CheckError × Nat) Unit :=
  match Cached.recordJob mode natOpPinSets J.I t d with
  | .ok () => .ok ()
  | .error e => .error (e, t)

/-- **One job's run**, from the region a worker kept: a theorem whose value is still in its
file reads it and is checked with it in place, any other record as it stands.  The value is
dropped when the check ends. -/
def oleanJobRun {μ : Type → Type} [CheckerIO μ] (mode : CheckMode) {ds : Array Declaration}
    (J : Jobs ds) (sp : List System.FilePath) (values : Array Frontend.Olean.ModRef)
    (c : Frontend.Olean.ValueCache) (t : Nat) :
    μ (Frontend.Olean.ValueCache × Except (CheckError × Nat) Unit) :=
  match ds[t]? with
  | some (.thmDecl cv (.bvar code)) => do
    match ← Frontend.Olean.readValue sp values c code with
    | (c, .error e) => pure (c, .error (e, t))
    | (c, .ok v) => pure (c, jobRun mode J t (.thmDecl cv v))
  | some d => pure (c, jobRun mode J t d)
  | none => pure (c, .error (.internal s!"check phase: no job {t}", t))

/-- A worker of an `--olean` run's check phase: which one, its statistics, and the
module it read last. -/
structure OleanWorker where
  w : Nat
  st : WStats := {}
  cache : Frontend.Olean.ValueCache := {}

/-- **One job of the pool**: timed, with the heartbeat. -/
def oleanStep {μ : Type → Type} [CheckerIO μ] (mode : CheckMode) (run : OleanRun) (pl : PoolLive)
    {ds : Array Declaration} (J : Jobs ds) (sp : List System.FilePath)
    (values : Array Frontend.Olean.ModRef) (s : OleanWorker) (t : Nat) :
    μ (OleanWorker × Except (CheckError × Nat) Unit) := do
  let ts ← CheckerIO.liftIO (jobBegin pl run.pace s.w t)
  let (c, r) ← oleanJobRun mode J sp values s.cache t
  let st ← CheckerIO.liftIO (jobEnd run.err run.pace run.t0 ds pl s.w t ts (r matches .ok _) s.st)
  pure ({ s with st, cache := c }, r)

/-- **The check phase of an `--olean` run**: the jobs on the worker map, in fold order; the
first failure in that order is the result, whatever the workers' timing. -/
def checkOleansG {μ : Type → Type} [CheckerIO μ] (mode : CheckMode)
    (pace : Pace) (t0 tIndex tParse jobs : Nat) (sp : List System.FilePath)
    (values : Array Frontend.Olean.ModRef) {ds : Array Declaration} (J : Jobs ds) :
    μ (Except (CheckError × Nat) Unit) := do
  let run ← CheckerIO.liftIO (OleanRun.new pace t0 tIndex tParse jobs)
  let workers := max 1 (min jobs ds.size)
  let (pl, tStart) ← CheckerIO.liftIO (run.pool ds.size workers values)
  let (ss, res) ← CheckerIO.parMapWorkers jobs (fun w => ({ w } : OleanWorker))
    (oleanStep mode run pl J sp values) (List.range ds.size)
  let failure := match res with
    | .error e => some e
    | .ok _ => none
  CheckerIO.liftIO (run.done ds tStart workers (ss.map (·.st)) failure)
  pure (match res with
    | .error e => .error e
    | .ok _ => .ok ())

/-- **The verdict of a run**: the line and the exit code, from the fold's result. -/
def verdictG {μ : Type → Type} [CheckerIO μ] (modeTag : String) (size t0 : Nat)
    (decls : Array Declaration) (r : Except (CheckError × Nat) Unit) : μ UInt8 := do
  match r with
  | .ok _ =>
    -- **The headline number is the FILE's declaration-record
    -- count**: the records
    -- the PARSE produced, which are the file's own.  Nothing the
    -- prepare step does — prepending the prelude, dropping a
    -- stream copy of one of its records, hoisting — moves it: a
    -- stream re-declaring `Bool` identically reports the same
    -- count as before the prelude existed, and a stream's five
    -- quotient records count as the five records they are.
    --
    -- The number of environment CONSTANTS is not that number —
    -- an inductive block's type former, its constructors, its
    -- recursor, its projection table and the basis extras count
    -- separately — and it is a property of our REPRESENTATION,
    -- not of the input: it moves whenever the representation
    -- moves.  The record count is a property of the input.
    --
    -- It still does not equal the official checker's number, and
    -- it cannot: official prints `constMap.size`, its PARSED
    -- export, where an inductive record counts as its type
    -- formers, its constructors and its recursors (less the three
    -- `Quot.mk`/`.lift`/`.ind` entries it erases).  That is a
    -- third unit — also a function of the file, just a larger one.
    -- `scripts/stream-census.py` derives BOTH numbers from a
    -- stream and is checked against both checkers' actual output,
    -- which is where a run's constant count is read off.
    outLine s!"con-leche: accepted {size} \
      declarations ({modeTag})"
    return 0
  | .error (e, i) =>
    -- **No second pass**: the fold's error carries the failing
    -- declaration's FOLD POSITION, so the message is read off the
    -- record array the driver already holds — never a diagnostic
    -- re-run of the accepted prefix, which would be a lie waiting
    -- to happen if the two runs ever disagreed.
    --
    -- `i` is the FOLD position.  The file's declaration-record
    -- index is NOT a fixed offset from it: the prepared list
    -- starts with the prelude's records and drops the stream's
    -- identical copies of them (see above).  The declaration NAME
    -- is the portable handle.
    let loc := if h : i < decls.size then
        s!" [at {declCName decls[i]}, fold position {i}]"
      else s!" [at fold position {i}]"
    let now ← clockMs
    diagLine s!"con-leche: {e}{loc} ({modeTag}) \
      t={ConLeche.Cached.msSecs (now - t0)}s"
    return e.exitCode

/-- **The driver, generic in the IO class** (tasks #424, #450): what
`main` runs in process (at `IO`) and what the theorem is about (at
`ModelIO`).  `mode` is the
checking mode, validated once by the caller and consumed here as
configuration.

**One core at two modes, one parse.**  The stream is parsed directly
to `Expr` (`parseStreamG`) and checked by the one
driver — `checkDeclsIO` in `ConLeche/Driver/Run.lean`, through `liftIO` — at `.verified` under `--verified` (the
default), at `.trusted` under `--trusted`.  The driver returns the
proof that the fold `checkDecls` accepts the records, the
fold the main theorem `ConLeche.model_exists`
(`ConLeche/MainTheorem.lean`) is about; the trusted instance is
unverified by design.

**The main corollary's chain is what the three phases below compute**
(`ConLeche.no_False_declaration`, `ConLeche/MainTheorem.lean`: the
built-in prelude parses, the chunks parse, `checkDecls .verified`
accepts the parsed records prepared with the prelude).  The prelude
step is the same function, `Frontend.builtinPreludeE`.  The parse
(`parseStreamG`) reads the file through the class's folds: every step
is `chunkStep`, run by the serial parse or, for a window of the rounds
parse, established from the good entries its rounds built
(`Frontend.GOK.window`), so that in the model the parse is
`Frontend.parseChunks` of the file's reads, and the chunk boundaries
are proved invisible (`parseStreamG_model`: the file's bytes as one
chunk).  `Frontend.prepareD` is `Frontend.preparePrelude` plus the
receipts printed below.  `checkDeclsIO` returns the evidence
`∃ env, checkDecls mode natOpPinSets ds = .ok env`.  What the driver adds is
IO — the heartbeat, the parallel check pool, the diagnostics that say
which step failed and with what exit code — and none of it touches
the verdict.  The three steps fail in ONE error type, the checker's
`CheckError` with the failure's position, which is why the
chain is one `do` block up there and why the exit code below is
`CheckError.exitCode` whichever step produced it. -/
def checkMainG {μ : Type → Type} [CheckerIO μ] (input : Input) (mode : CheckMode)
    (pace : Pace) (jobs : Nat) : μ UInt8 := do
    -- The opt-in progress heartbeat (`--progress[=<pace>]`):
    -- validated by the argument parse, before any work is done, and
    -- handed down as configuration.  EVERY SWITCH THAT SHAPES A
    -- VERDICT IS A COMMAND-LINE FLAG, so a verdict's provenance is
    -- readable off the invocation and off nothing else.  The binary
    -- reads no environment variable.
    let t0 ← clockMs
    -- Every VERDICT line names the mode: a `--trusted`
    -- run — the unverified lane — must never be mistaken for a
    -- `--verified` one in a log, whatever it says.
    let modeTag : String := match mode with
      | .verified => "--verified"
      | .trusted => "--trusted"
    -- THE BUILT-IN PRELUDE (`ConLeche/Frontend/Prelude.lean`): the
    -- pinned basis blocks, `Bool` and `And`, parsed from the
    -- committed `pins/<toolchain>.prelude.ndjson`.  `preparePrelude`
    -- PREPENDS them to the parsed stream, so the fold
    -- checks them first and unconditionally; a stream's own copy of
    -- one is dropped there when identical, and the fold declines the
    -- run when it differs.  A prelude that does not parse is a
    -- corrupted build, reported before any input is read.
    let prelude ← match Frontend.builtinPreludeE with
      | .ok p => pure p
      | .error (.internal msg, line) =>
        diagLine s!"con-leche: the built-in prelude does not parse (line \
          {line}: {msg}); regenerate it with `lake exe natop-pins-export` \
          ({modeTag})"
        return 3
      | .error (.notImplemented what, _) =>
        diagLine s!"con-leche: the built-in prelude is unsupported ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
      | .error (.invalid what, _) =>
        diagLine s!"con-leche: the built-in prelude contradicts itself ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
    -- Streaming frontend: the parse reads the file line by line, so
    -- neither a wholesale text buffer nor a scratch file exists in
    -- this process.
    CheckerIO.liftIO (readStarts pace input.label)
    match ← readInputG input pace jobs with
    | .error (.notImplemented what, _) =>
      diagLine s!"con-leche: declined: {what} ({modeTag})"
      return 2
    -- A stream whose inductive block
    -- contradicts its own declarations in a REDUNDANT field is
    -- rejected at the parse, as official's replay rejects a recursor
    -- or constructor record that is not the generated one.
    | .error (.invalid what, _) =>
      diagLine s!"con-leche: invalid: {what} ({modeTag})"
      return 1
    | .error (.internal msg, line) =>
      diagLine s!"con-leche: {input.label}:{line}: {msg}"
      return 3
    | .ok (parsed, src) =>
      -- **PREPARE** (`ConLeche/Frontend/Prepare.lean`): the
      -- parsed array is the FILE's records; what the fold runs over is `preparePrelude` of it —
      -- the built-in prelude's records, then the stream's, recognised,
      -- deduped against the prelude and ground-hoisted.  Fold positions
      -- count from the prelude's first record; the VERDICT's count is
      -- the file's own (`parsed.size`), which no step
      -- below changes.
      let ⟨decls, synthesised, hoisted⟩ := Frontend.prepareD prelude parsed (usedOf src)
      -- the ground hoist's receipt
      -- (`ConLeche/Frontend/NatOpGround.lean`): records moved ahead of a
      -- pinned Nat operation whose certificate statements they ground
      if hoisted.size > 0 then
        diagLine s!"con-leche: {hoisted.size} declarations hoisted ahead of \
          the pinned Nat operations they ground: \
          {String.intercalate ", " (hoisted.toList.map toString)}"
      -- ONE driver, two modes: the trusted
      -- mode is the shared bodies at `.trusted`, the verified mode the
      -- same bodies at `.verified` — the mode is passed straight down.
      -- **One driver, and it returns its proof.**  `checkDeclsIO`
      -- checks every record at the frozen index's view of its position
      -- and carries every check, and what comes out is the proof that
      -- `ConLeche.Cached.checkDecls` accepts the records, the fold the
      -- main theorem `ConLeche.model_exists`
      -- (`ConLeche/MainTheorem.lean`) is about.  The success line below is printed from that value and
      -- from nothing else.  Printing between the steps (`--progress`)
      -- changes nothing about the proof, so there is no second loop.
      --
      -- **Reading the index**: `i` is the *fold* position, and it is
      -- NOT the file's declaration-record index.  The prepared list
      -- begins with the built-in prelude's records and drops the
      -- stream's identical copies of them.  (Raw `init-full` declares
      -- every prelude declaration itself, so there the preparation
      -- synthesises NONE of them and only moves the stream's own
      -- records to the front.)  The declaration NAME on the line is
      -- the portable handle.
      -- The records' frozen index, the last step of the parse phase.
      let tIndex ← clockMs
      let J ← CheckerIO.liftIO (Jobs.build decls)
      -- The heartbeat's first line (`--progress`): the parse is done,
      -- and the check phase is about to start on this many records.  It
      -- prints its own lines (`checkDeclsIO`), and the summary closes
      -- the run.
      let tParse ← clockMs
      if pace.on then
        diagLine s!"con-leche: parse done: {decls.size} fold records — \
          the file's {parsed.size}, \
          {synthesised} built-in prelude records synthesised \
          t={ConLeche.Cached.msSecs (tParse - t0)}s \
          (parse {ConLeche.Cached.msSecs (tParse - t0)}s)"
      match src with
      | none =>
        let verdict ← CheckerIO.liftIO do
          checkDeclsIO mode (← IO.getStderr) pace t0 tIndex tParse jobs J
        verdictG modeTag parsed.size t0 decls (match verdict with
          | .ok _ => .ok ()
          | .error e => .error e)
      | some (sp, rd) =>
        -- the theorems' values are read in their checks, and what the
        -- read kept of the merge is dropped here
        verdictG modeTag parsed.size t0 decls
          (← checkOleansG mode pace t0 tIndex tParse jobs sp rd.values J)

/-- **An exit 0 is the fold's accept**: the verdict's code is 0 only on an `.ok`. -/
theorem verdictG_ok {modeTag : String} {size t0 : Nat} {decls : Array Declaration}
    {r : Except (CheckError × Nat) Unit} {fs : FS} {hs : HS} {c : UInt8} {hs' : HS}
    (h : (verdictG modeTag size t0 decls r : ModelIO _) fs hs (.ok c) hs') (h0 : c = 0) :
    r = .ok () := by
  suffices H : ModelIO.AllOk (verdictG modeTag size t0 decls r) fs hs
      (fun c => c = 0 → r = .ok ()) from
    H c hs' h h0
  cases r with
  | ok u => exact fun _ _ _ _ => rfl
  | error x =>
    obtain ⟨e, i⟩ := x
    simp only [verdictG, clockMs, diagLine, ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq,
      ModelIO.allOk_pure]
    intro _ _ h0
    exact absurd h0 (CheckError.exitCode_ne_zero _)

/-- **An accepted stream run, in the model** (tasks #424, #450): every
outcome of the driver's run on a lean4export stream `file` over a
snapshot `fs` that is an exit 0 means the built-in prelude parses, the
file has bytes `b` in the snapshot, they parse as one chunk to records
`r`, and `checkDecls` accepts those prepared with the prelude — the
hypothesis of the main corollary (`ConLeche.no_False_declaration`, at
the chunks `[b]`) about the file's own bytes, at any `--jobs`, whatever
the `liftIO` actions answered.  Under the assumptions of
`ConLeche/Frontend/CheckerIO.lean` the binary's run is one of these
outcomes. -/
theorem checkMainG_ndjson_accept {file : String} {mode : CheckMode}
    {pace : Pace} {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (checkMainG (.ndjson file) mode pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre b r env, Frontend.builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      Frontend.parseChunks [b] = .ok r ∧
      Cached.checkDecls mode natOpPinSets (Frontend.preparePrelude pre r.decls) = .ok env := by
  -- every value outcome `c` of the run: `c = 0` gives the chain
  suffices H : ModelIO.AllOk (checkMainG (.ndjson file) mode pace jobs) fs hs
      (fun c => c = 0 → ∃ pre b r env, Frontend.builtinPreludeE = .ok pre ∧
        fs.file file = some b ∧ Frontend.parseChunks [b] = .ok r ∧
        Cached.checkDecls mode natOpPinSets (Frontend.preparePrelude pre r.decls) = .ok env) from
    H 0 hs' h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [checkMainG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [checkMainG, hp, readInputG, clockMs, diagLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_eq]
    intro _ pre' _ hpre _ x _ hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    obtain ⟨rfl, rfl⟩ := hpre
    simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨x, _, hx, rfl, rfl⟩ := hx
    rcases x with ⟨_ | _ | _, _⟩ | r
    rotate_right
    · obtain ⟨b, hb, hpc⟩ := parseStreamG_model hx
      simp only [Except.map]
      -- the tail after the parse: the receipts, the index, the check through
      -- `liftIO`, whose value carries its proof, and the verdict
      refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq, forall_const] <;>
        intros <;>
        refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_eq, forall_const] <;>
        intro v <;>
        intro c _ hc h0 <;>
        rcases v with ⟨e, _⟩ | ⟨⟨env, henv⟩⟩
      -- a rejection's exit code is not 0; an accept carries its proof
      all_goals first
        | exact ⟨_, b, r, env, rfl, hb, hpc, henv⟩
        | exact absurd (verdictG_ok hc h0) (by simp)
    all_goals simp [Except.map]

end ConLeche.Driver
