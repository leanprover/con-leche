module

public import ConLeche.Frontend.Prelude
public import ConLeche.Driver.CheckPool

/-!
# The driver: the install loop, `checkDeclsIO` and the phase sequencing

Part of the proof-carrying driver (`ConLeche/Driver/*`; the CLI —
argument parsing, I/O, exit codes — is `Main.lean`).

`checkDeclsIO` is **the driver**: `installLoop` then the check phase —
`checkLoop` on one dedicated worker thread at `--jobs=1`, `checkPool`
otherwise (`Driver/CheckPool.lean`) — and what comes out is the
environment together with the proof that the fold `checkDecls`
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
straight from the file.  There is nothing else — no preprocessor
detection, no spawn, no pipe. -/
def parseInput (file : String) :
    IO (Except (ConLeche.CheckError × Nat) Frontend.ParseResultD) :=
  Frontend.parseExportStreamD file

/-- **Phase A's loop — the driver's install pass, carrying its own
accepting run.**  Each record is installed by
`ConLeche.Cached.annotDeclStep`: a separable value declaration is
annotated and pushed with its check recorded, everything else is checked
in full.  The loop carries the chain of accepting steps
(`ConLeche.Cached.InstallRun`) of the records it has consumed — a
proposition, so nothing at run time — and returns it with the result:
what this loop returns IS an `InstalledEnv mode natOpPinSets ds.toList`
(`ConLeche/Cached/Installed.lean`), phase A of the fold `checkDecls`.
The records are the ARRAY the prepare step produced and the driver
holds to the end anyway (a rejection names its declaration by indexing
it), so the loop walks it BY INDEX — nothing converts a million
records into a list — while the run it carries is over
`ds.toList.take i`, the shape every lemma above it is stated in.
Whatever it prints between steps is irrelevant to that type, which is
why ONE loop serves the plain run and the `--progress` heartbeat
alike.

**Written tail-recursively, threading `p` and `s` LINEARLY**: a
`for … in ds` loop with `let mut` accumulators desugars to code that
`lean_inc`s both the `FEnv` and the `CState` before each step, so
`lean_is_exclusive` is false at the index inserts and every hashmap
copies its bucket array per declaration — quadratic at Mathlib
scale.  Here the previous `p`/`s` are dead at the
recursive call, so the C carries no `lean_inc` of either before the
step, and the cost per declaration is flat.  The run is carried in the
SNOC direction (`InstallRun.snoc`) precisely so that the call stays a
tail call: a cons-direction proof would wrap the result on the way
back, one frame per declaration.  (The index measure makes this a
well-founded recursion; the compiler's recursive function is the same
tail call, and the measure is erased.)

**Stride 1 is the localisation lane.**  With `--progress` (bare, or
`--progress=1`) every declaration is announced before it is installed,
so a run that dies — an OOM, a timeout, a `SIGKILL` — names on its last
line the declaration it died in.  The index is the FOLD position, not
the stream's record index: the prepare step prepends the built-in
prelude and drops the stream's identical copies of its records, so the
two drift apart by a stream-dependent amount.  Calibrate by NAME.

Each step is timed into `st` (`WStats`, performance-only: a ref only
this thread touches). -/
def installLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) (st : IO.Ref WStats)
    (ds : Array ConLeche.Declaration)
    (p₀ : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) (s₀ : ConLeche.Cached.CState) :
    (i : Nat) →
    (p : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) →
    (s : ConLeche.Cached.CState) →
    ConLeche.Cached.InstallRun mode ConLeche.natOpPinSets (ds.toList.take i) p₀ s₀ p s →
      IO (Except (ConLeche.CheckError × Nat)
        (Σ' (p' : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck)
          (s' : ConLeche.Cached.CState),
          PLift (ConLeche.Cached.InstallRun mode ConLeche.natOpPinSets
            ds.toList p₀ s₀ p' s')))
  | i, p, s, hrun => do
    if hi : i < ds.size then
      let pd := ds[i]
      if stride > 0 && p.1 % stride == 0 then
        let now ← IO.monoMsNow
        err.putStr s!"con-leche: install {p.1}/{total} \
          {ConLeche.Cached.declCLabel pd} \
          t={ConLeche.Cached.msSecs (now - t0)}s\n"
        err.flush
      let ts ← IO.monoNanosNow
      match h : ConLeche.Cached.annotDeclStep mode ConLeche.natOpPinSets p pd s with
      | .ok (p₁, s₁) =>
        let te ← IO.monoNanosNow
        st.modify (·.add i ts te)
        installLoop mode err stride total t0 st ds p₀ s₀ (i + 1) p₁ s₁ (by
          have hlist : ds.toList.take (i + 1) = ds.toList.take i ++ [pd] := by
            rw [List.take_add_one]
            simp [pd, Array.getElem?_eq_getElem hi]
          rw [hlist]
          exact ConLeche.Cached.InstallRun.snoc mode hrun h)
      | .error e =>
        let te ← IO.monoNanosNow
        st.modify (·.add i ts te)
        return .error e
    else
      return .ok ⟨p, s, ⟨by
        rw [List.take_of_length_le (by simp; omega)] at hrun
        exact hrun⟩⟩
  termination_by i => ds.size - i

/-- The end-of-run statistics (performance-only): the phase times, the
install's and the check's reports (`PoolRep.line`, the slowest five of
each), the peak resident set.  Every line starts `con-leche: stats:`. -/
def printStats (err : IO.FS.Stream) (parseMs installMs : Nat) (checkMs : Option Nat)
    (inst : PoolRep) (instLabel : Nat → String)
    (chk : Option PoolRep) (chkLabel : Nat → String) : IO Unit := do
  let line (l : String) : IO Unit := err.putStr s!"con-leche: stats: {l}\n"
  let secs := ConLeche.Cached.msSecs
  line s!"phases: parse {secs parseMs}s, install {secs installMs}s, check \
    {match checkMs with | some c => s!"{secs c}s" | none => "not reached"}"
  line inst.line
  line (inst.topLine "installs" instLabel)
  if let some c := chk then
    line c.line
    line (c.topLine "checks" chkLabel)
  if let some r ← peakRss then line s!"peak RSS {r}"
  err.flush

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
the worker count.

**The statistics** (`printStats`, always, flag or not): after the
phases that ran, a few `con-leche: stats:` lines on stderr — the phase
times, each pool's utilisation and tail, the slowest installs and
checks, the peak resident set.  Performance-only: printed after the
verdict is known, from timings the loops accumulate beside their
proofs; stdout and the exit code do not see them. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride total t0 tParse jobs : Nat)
    (noMark : Bool) (ds : Array ConLeche.Declaration) :
    IO (Except (ConLeche.CheckError × Nat)
      { env : ConLeche.Env // ConLeche.Cached.checkDecls mode ConLeche.natOpPinSets ds = .ok env }) := do
  let heartbeat (line : String) : IO Unit := do
    if stride > 0 then
      err.putStr s!"con-leche: {line}\n"
      err.flush
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  let instLabel (k : Nat) : String := match ds[k]? with
    | some d => s!"{ConLeche.Cached.declCLabel d} (#{k})"
    | none => s!"record {k}"
  let serialStats ← IO.mkRef ({} : WStats)
  let tI0 ← IO.monoNanosNow
  let installed ← installLoop mode err stride total t0 serialStats ds
      (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) {} 0
      -- the install environment's index marked linear (task #331): a
      -- copy of it panics instead of silently copying (`main` sets
      -- `LEAN_ABORT_ON_NONLINEAR`).  Marked HERE, on the value the loop
      -- threads, not on the closed term `mkFEnv Env.empty`, which is
      -- persistent and copied by its first insert anyway.
      (0, (ConLeche.mkFEnv ConLeche.Env.empty).markLinear, #[]) {}
      (ConLeche.FEnv.markLinear_eq _ ▸ .nil _ _)
  let tI1 ← IO.monoNanosNow
  -- the install's report: the main thread's loop
  let instRep : IO PoolRep := do
    pure { name := "install (main thread)", workers := 1, tStart := tI0, tEnd := tI1,
           stats := #[← serialStats.get] }
  match installed with
  | .error e =>
    let now ← IO.monoMsNow
    heartbeat s!"install failed at {e.2}/{total} t={secs (now - t0)}s \
      (install {secs (now - tParse)}s)"
    heartbeat s!"done: parse {secs (tParse - t0)}s, install {secs (now - tParse)}s, \
      check not reached t={secs (now - t0)}s"
    printStats err (tParse - t0) (now - tParse) none (← instRep) instLabel none (fun _ => "")
    return .error e
  | .ok ⟨(n, fe, pend), s, ⟨r⟩⟩ =>
    let e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds.toList :=
      ⟨fe, pend, ⟨n, s, r⟩⟩
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
    let tC0 ← IO.monoNanosNow
    let (chkRep, res) ← if jobs ≤ 1 then
        -- ONE worker, and no pool: no shared claim counter, no result
        -- table, the same `checkLoop` accumulator — only the thread is
        -- new.  A worker that fails as an `IO` action (not a check
        -- failing) is an internal error, exit 3, never a verdict.
        let (st, r) ← match ← IO.wait (← IO.asTask (prio := .dedicated)
            (checkLoop mode err stride t0 e 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) {})) with
          | .ok r => pure r
          | .error ioe =>
            pure ({}, .error (.internal s!"check phase: the worker failed: {ioe}", 0))
        let tC1 ← IO.monoNanosNow
        let rep : PoolRep := { name := "check (one worker)", workers := 1, tStart := tC0,
                               tEnd := tC1, stats := #[st] }
        pure (rep, r)
      else
        checkPool mode err stride t0 jobs e
    let now ← IO.monoMsNow
    let stats : IO Unit :=
      printStats err (tParse - t0) (tCheck - tParse) (some (now - tCheck)) (← instRep)
        instLabel (some chkRep) (checkLabel e)
    let summary := s!"done: parse {secs (tParse - t0)}s, install {secs (tCheck - tParse)}s, \
      check {secs (now - tCheck)}s, {workers} worker{if workers = 1 then "" else "s"} \
      t={secs (now - t0)}s"
    match res with
    | .error e' =>
      heartbeat s!"check failed at fold position {e'.2} t={secs (now - t0)}s \
        (check {secs (now - tCheck)}s)"
      heartbeat summary
      stats
      return .error e'
    | .ok ⟨hall⟩ =>
      heartbeat s!"check done: {pend.size}/{pend.size} t={secs (now - t0)}s \
        (check {secs (now - tCheck)}s)"
      heartbeat summary
      stats
      let fc : ConLeche.Cached.FullyChecked mode ConLeche.natOpPinSets ds.toList :=
        ⟨e, hall⟩
      return .ok ⟨fc.env, ConLeche.Cached.fullyChecked_checkDecls mode fc⟩

/-- The real driver, which `main` calls in process.  `mode` is the
checking mode, validated once by the caller and consumed here as
configuration.

**One core at two modes, one parse.**  The stream is parsed directly
to `Expr` (`Frontend.parseExportStreamD`) and checked by the one
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
step is the same function, `Frontend.builtinPreludeE`.  The parse loop
(`Frontend.parseExportStreamD`) is `Frontend.parseChunks` of the
chunks the handle hands out, with the reads interleaved — every step
is the shared `chunkStep`, and the chunk boundaries are proved
invisible.  `Frontend.prepareD` is `Frontend.preparePrelude` plus the
receipts printed below.  `checkDeclsIO` returns its environment with
the evidence `checkDecls mode natOpPinSets ds = .ok env`.  What the driver adds is
IO — the heartbeat, the parallel check pool, the diagnostics that say
which step failed and with what exit code — and none of it touches
the verdict.  The three steps fail in ONE error type, the checker's
`CheckError` with the failure's position, which is why the
chain is one `do` block up there and why the exit code below is
`CheckError.exitCode` whichever step produced it. -/
def checkMain (file : String) (mode : CheckMode) (stride jobs : Nat)
    (noMark : Bool) : IO UInt32 := do
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
    match ← parseInput file with
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
      let verdict ← checkDeclsIO mode err stride decls.size t0 tParse jobs noMark decls
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
