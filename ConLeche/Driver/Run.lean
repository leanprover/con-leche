module

public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.Pipeline
public import ConLeche.Driver.ParInstall
public import ConLeche.Driver.CheckPool
public import ConLeche.Driver.ParParse

/-!
# The driver: `checkDeclsIO` and the phase sequencing (task #329)

Pulled out of `Main.lean` when the driver split into `ConLeche/Driver/*`
(the CLI stays in `Main.lean`: argument parsing, I/O, exit codes; the
proof-carrying driver moved here and to `Driver/CheckPool.lean`,
`Driver/ParInstall.lean`).  A pure move: no logic changed, only the
module boundary.

`checkDeclsIO` is **the driver**: `installLoop`/`parInstall` then the
check phase — `checkLoop` on one dedicated worker thread at `--jobs=1`,
`checkPool` otherwise — and what comes out is the environment together
with the proof that the fold `checkDecls`
(`ConLeche/Cached/Installed.lean`) returns it — the subject of the main
theorem `ConLeche.model_exists` (`ConLeche/MainTheorem.lean`).
`checkMain` sequences the built-in prelude, the stream parse and
`checkDeclsIO`, and turns the result into the verdict line and the exit
code `Main.lean`'s `main` returns.
-/

@[expose] public section

open ConLeche

/-- Exit codes follow the lean kernel arena convention: 0 all
declarations accepted, 1 a declaration was rejected as invalid, 2 the
checker declined (positively detected an unsupported feature), 3 bad
usage, malformed input, or an internal failure of unclear cause. -/
def ConLeche.CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

namespace ConLeche.Driver

/-- A declaration's display name, for the direct-parse `Declaration` records.  The
formatting itself lives beside the checker (`ConLeche.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : ConLeche.Declaration → String := ConLeche.Cached.declCLabel

/-- The whole input side of a run: the parsed declarations, read
straight from the file, with the evidence that the streaming parse
`Frontend.parseChunks` returns them (`Frontend.ParseOutcome`).  There
is nothing else — no preprocessor detection, no spawn, no pipe.

At `--jobs=1` the parse is the pipelined one
(`Frontend.parseExportHandleP`): the chunks are scanned on two tasks
ahead of the applying thread.  Above one worker it is the rounds parse
(`ParParse.parseExportStreamR`): windows of `4 * jobs` chunks (at most
256), applied in rounds on `jobs` workers, `jobs` chunks read and
scanned ahead.  A chunk is about an eighth of a window's share of the
file, between 64 KiB and 1 MiB (1 MiB when the size is unknown), so
that a small file is one window and a large one has many. -/
def parseInput (file : String) (jobs : Nat) (noMark : Bool) : IO Frontend.ParseOutcome := do
  if jobs ≤ 1 then
    Frontend.parseExportStreamP file 2
  else
    let size ← try pure (← System.FilePath.metadata file).byteSize.toNat catch _ => pure 0
    let m := min 256 (4 * jobs)
    let csz := if size == 0 then 1048576 else max 65536 (min 1048576 (size / (8 * m)))
    ParParse.parseExportStreamR file jobs m csz.toUSize jobs 2 noMark

/-- **The driver**: `installLoop` then the check phase — `checkLoop` on
one dedicated worker thread at `--jobs=1`, `checkPool` otherwise — and
what comes out
is the environment together with the proof that the fold `checkDecls`
(`ConLeche/Cached/Installed.lean`) returns it — the subject of the main
theorem `ConLeche.model_exists` (`ConLeche/MainTheorem.lean`).  The
loops are the fold's two phases with the heartbeat printed between the
steps; the fully checked environment they assemble
is an accept of the fold (`ConLeche.Cached.fullyChecked_checkDecls`), so
the success line `checkMain` prints is printed from an accept of
`checkDecls` and from nothing else.  A rejection carries the fold
position of the declaration it names.  With `--progress`, one line at
the phase boundary, one when the check phase ends, and a summary with
the three phase durations (`tParse` is when the parse finished) and
the worker count. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride total t0 tParse jobs : Nat)
    (noMark : Bool) (fallbackAt : Option Nat) (ds : Array ConLeche.Declaration) :
    IO (Except (ConLeche.CheckError × Nat)
      { env : ConLeche.Env // ConLeche.Cached.checkDecls mode ConLeche.natOpPinSets ds = .ok env }) := do
  let heartbeat (line : String) : IO Unit := do
    if stride > 0 then
      err.putStr s!"con-leche: {line}\n"
      err.flush
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  let installed ← if jobs ≤ 1 then
      installLoop mode err stride total t0 ds
        (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) 0
        (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) (.nil _)
    else
      parInstall mode err stride total t0 jobs noMark fallbackAt ds
  match installed with
  | .error e =>
    let now ← IO.monoMsNow
    heartbeat s!"install failed at {e.2}/{total} t={secs (now - t0)}s \
      (install {secs (now - tParse)}s)"
    heartbeat s!"done: parse {secs (tParse - t0)}s, install {secs (now - tParse)}s, \
      check not reached t={secs (now - t0)}s"
    return .error e
  | .ok ⟨(n, fe, pend), ⟨r⟩⟩ =>
    let e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds.toList :=
      ⟨fe, pend, ⟨n, r⟩⟩
    let tCheck ← IO.monoMsNow
    heartbeat s!"install done: {total}/{total} declarations installed, \
      {pend.size} checks pending t={secs (tCheck - t0)}s \
      (install {secs (tCheck - tParse)}s)"
    -- **THE PERSISTENT MARK AT THE PHASE BOUNDARY.**  The installed
    -- environment is complete and READ-ONLY from here on: every
    -- recorded check reads a prefix view of it from a fresh memo state
    -- and writes nothing back.  The check phase runs on worker threads
    -- at every `--jobs=<n>`, so the runtime marks that graph
    -- MULTI-THREADED and every reference count on it becomes an atomic
    -- read-modify-write on a cache line all the workers touch — pure
    -- overhead, since nothing in the graph is freed or mutated again.
    -- Marking it PERSISTENT instead removes the counting altogether:
    -- on the pool that is worth 19-50 % of the run's cycles and
    -- 18-32 % of its WALL TIME, growing with the worker count, and
    -- 3.5 % at `--jobs=1`.  (The check phase is on a thread of its own
    -- in that lane too, because phase B's per-record memo state is
    -- allocated out of the running thread's own mimalloc heap and the
    -- main thread's heap is the one parse and install have just
    -- fragmented: the same instructions out of a FRESH heap run at
    -- 2.68 IPC against 1.29, with 24x fewer demand fills from DRAM per
    -- instruction — a factor of two in wall time at Mathlib scale.
    -- The measurement is DESIGN.md's task #269 section.)
    --
    -- The result is DISCARDED and the original `fe`/`pend` are what the
    -- phase below reads: `Runtime.markPersistent` is the identity on
    -- the value and marks the object graph in place, so nothing
    -- downstream — the `InstalledEnv` above, the `InstallRun` it
    -- carries — has to be transported across it, and no verdict can
    -- turn on it.  Term-level `unsafe`, the escape
    -- `Lean.Environment.finalizeImport` uses for this same call; it is
    -- unsafe only in that the marked closure is never freed, and the
    -- process exits right after.  `--no-mark-persistent` turns it off,
    -- which is how the A/B above is measured on the shipped binary.
    if !noMark then
      let _ ← unsafe Runtime.markPersistent fe
      let _ ← unsafe Runtime.markPersistent pend
    let tMark ← IO.monoMsNow
    heartbeat s!"persistent mark {secs (tMark - tCheck)}s"
    let workers := max 1 (min jobs pend.size)
    let res ← if jobs ≤ 1 then
        -- ONE worker, and no pool: no shared claim counter, no result
        -- table, the same `checkLoop` accumulator — only the thread is
        -- new.  A worker that fails as an `IO` action (not a check
        -- failing) is an internal error, exit 3, never a verdict.
        match ← IO.wait (← IO.asTask (prio := .dedicated)
            (checkLoop mode err stride t0 e 0 (fun j hj => absurd hj (Nat.not_lt_zero j)))) with
        | .ok r => pure r
        | .error ioe =>
          pure (.error (.internal s!"check phase: the worker failed: {ioe}", 0))
      else
        checkPool mode err stride t0 jobs e
    let now ← IO.monoMsNow
    let summary := s!"done: parse {secs (tParse - t0)}s, install {secs (tCheck - tParse)}s, \
      check {secs (now - tCheck)}s, {workers} worker{if workers = 1 then "" else "s"} \
      t={secs (now - t0)}s"
    match res with
    | .error e' =>
      heartbeat s!"check failed at fold position {e'.2} t={secs (now - t0)}s \
        (check {secs (now - tCheck)}s)"
      heartbeat summary
      return .error e'
    | .ok ⟨hall⟩ =>
      heartbeat s!"check done: {pend.size}/{pend.size} t={secs (now - t0)}s \
        (check {secs (now - tCheck)}s)"
      heartbeat summary
      let fc : ConLeche.Cached.FullyChecked mode ConLeche.natOpPinSets ds.toList :=
        ⟨e, hall⟩
      return .ok ⟨fc.env, ConLeche.Cached.fullyChecked_checkDecls mode fc⟩

/-- The real driver, which `Main.lean`'s `main` calls in process.  `mode`
is the checking mode, validated once by the caller and consumed here as
configuration.

**One core at two modes, one parse.**  The stream is parsed directly
to `Expr` (`Frontend.parseExportStreamP`) and checked by the one
driver — `checkDeclsIO` above — at `.verified` under `--verified` (the
default), at `.trusted` under `--trusted`.  The driver returns the
environment with the proof that the fold `checkDecls` returns it, the
fold the main theorem `ConLeche.model_exists`
(`ConLeche/MainTheorem.lean`) is about; the trusted instance is
unverified by design.

**The main corollary's chain is what the three phases below compute**
(`ConLeche.no_False_declaration`, `ConLeche/MainTheorem.lean`: the
built-in prelude parses, the chunks parse, `checkDecls .verified`
accepts the parsed records prepared with the prelude).  The prelude
step is the same function, `Frontend.builtinPreludeE`.  The parse
(`Frontend.parseExportStreamP`) returns its result with the evidence
that `Frontend.parseChunks` returns it on the chunks the parse cut from
its reads: the chunks are scanned on worker tasks and applied in order,
every step is `chunkStep` (`Frontend.chunkStepF_of_encodes`), and the
chunk boundaries are proved invisible.  `Frontend.prepareD` is `Frontend.preparePrelude` plus the
receipts printed below.  `checkDeclsIO` returns its environment with
the evidence `checkDecls mode natOpPinSets ds = .ok env`.  What the driver adds is
IO — the heartbeat, the parallel check pool, the diagnostics that say
which step failed and with what exit code — and none of it touches
the verdict.  The three steps fail in ONE error type, the checker's
`CheckError` with the failure's position, which is why the
chain is one `do` block up there and why the exit code below is
`CheckError.exitCode` whichever step produced it. -/
def checkMain (file : String) (mode : CheckMode) (stride jobs : Nat)
    (noMark : Bool) (fallbackAt : Option Nat) : IO UInt32 := do
    -- The opt-in progress heartbeat (`--progress[=<stride>]`):
    -- validated by the argument parse, before any work is done, and
    -- handed down as configuration.  EVERY SWITCH THAT SHAPES A
    -- VERDICT IS A COMMAND-LINE FLAG, so a verdict's provenance is
    -- readable off the invocation and off nothing else.  The binary
    -- reads no environment variable.
    let t0 ← IO.monoMsNow
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
    -- installs them first and unconditionally; a stream's own copy of
    -- one is dropped there when identical, and the fold declines the
    -- run when it differs.  A prelude that does not parse is a
    -- corrupted build, reported before any input is read.
    let prelude ← match Frontend.builtinPreludeE with
      | .ok p => pure p
      | .error (.internal msg, line) =>
        IO.eprintln s!"con-leche: the built-in prelude does not parse (line \
          {line}: {msg}); regenerate it with `lake exe natop-pins-export` \
          ({modeTag})"
        return 3
      | .error (.notImplemented what, _) =>
        IO.eprintln s!"con-leche: the built-in prelude is unsupported ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
      | .error (.invalid what, _) =>
        IO.eprintln s!"con-leche: the built-in prelude contradicts itself ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
    -- Streaming frontend: the parse reads the file line by line, so
    -- neither a wholesale text buffer nor a scratch file exists in
    -- this process.
    match (← parseInput file jobs noMark).val with
    | .error (.notImplemented what, _) =>
      IO.eprintln s!"con-leche: declined: {what} ({modeTag})"
      return 2
    -- A stream whose inductive block
    -- contradicts its own declarations in a REDUNDANT field is
    -- rejected at the parse, as official's replay rejects a recursor
    -- or constructor record that is not the generated one.
    | .error (.invalid what, _) =>
      IO.eprintln s!"con-leche: invalid: {what} ({modeTag})"
      return 1
    | .error (.internal msg, line) =>
      IO.eprintln s!"con-leche: {file}:{line}: {msg}"
      return 3
    | .ok ⟨parsed⟩ =>
      -- **PREPARE** (`ConLeche/Frontend/Prepare.lean`): the
      -- parsed array is the FILE's records; what the fold runs over is `preparePrelude` of it —
      -- the built-in prelude's records, then the stream's, recognised,
      -- deduped against the prelude and ground-hoisted.  Fold positions
      -- count from the prelude's first record; the VERDICT's count is
      -- the file's own (`parsed.size`), which no step
      -- below changes.
      let ⟨decls, synthesised, hoisted⟩ := Frontend.prepareD prelude parsed
      -- the ground hoist's receipt
      -- (`ConLeche/Frontend/NatOpGround.lean`): records moved ahead of a
      -- pinned Nat operation whose certificate statements they ground
      if hoisted.size > 0 then
        IO.eprintln s!"con-leche: {hoisted.size} declarations hoisted ahead of \
          the pinned Nat operations they ground: \
          {String.intercalate ", " (hoisted.toList.map toString)}"
      -- ONE driver, two modes: the trusted
      -- mode is the shared bodies at `.trusted`, the verified mode the
      -- same bodies at `.verified` — the mode is passed straight down.
      -- **One driver, and it returns its proof.**  `checkDeclsIO`
      -- above runs the fold's two phases — phase A installs every
      -- record and carries its accepting run, phase B checks every
      -- recorded declaration against the prefix view of the installed
      -- index and carries every check — and what comes out is the
      -- environment with the proof that `ConLeche.Cached.checkDecls`
      -- returns it, the fold the main theorem
      -- `ConLeche.model_exists` (`ConLeche/MainTheorem.lean`) is
      -- about.  The success line below is printed from that value and
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
      -- The heartbeat's first line (`--progress`): the parse is done,
      -- and the fold is about to start on this many records.  The
      -- install and check phases print their own lines
      -- (`checkDeclsIO`), and the summary closes the run.
      let tParse ← IO.monoMsNow
      if stride > 0 then
        IO.eprintln s!"con-leche: parse done: {decls.size} fold records — \
          the file's {parsed.size}, \
          {synthesised} built-in prelude records synthesised \
          t={ConLeche.Cached.msSecs (tParse - t0)}s \
          (parse {ConLeche.Cached.msSecs (tParse - t0)}s)"
        (← IO.getStderr).flush
      let err ← IO.getStderr
      let verdict ← checkDeclsIO mode err stride decls.size t0 tParse jobs noMark fallbackAt decls
      match verdict with
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
        IO.println s!"con-leche: accepted {parsed.size} \
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
        let now ← IO.monoMsNow
        IO.eprintln s!"con-leche: {e}{loc} ({modeTag}) \
          t={ConLeche.Cached.msSecs (now - t0)}s"
        return e.exitCode

end ConLeche.Driver
