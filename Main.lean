module

public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.InModelDump
public import ConLeche.Cached.Installed

@[expose] public section

/-!
Command-line driver: `con-leche FILE.ndjson` reads a **raw** lean4export
NDJSON file and checks the declarations in order.  There is no
preprocessor and no external dependency (task #207): every inductive
block is installed by the fixed-point route, or through a `_model`
family the frontend generates in-process at parse time
(`ConLeche/Frontend/InModel/*`) and then checks as ordinary
declarations; no model is ever read from the input (task #219).

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid.  An out-of-memory
  condition also exits 1: it is the Lean runtime's own panic
  (`lean_internal_panic_out_of_memory` prints "INTERNAL PANIC: out of
  memory" on stderr and calls `exit(1)`), uncatchable in process, so
  the message on stderr is what tells the two apart (task #230).
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
* 3 — bad usage, malformed input, or an internal failure of unclear cause

**NO TEMPORARY FILES** (task #180, 2026-09-07).  The checker writes
nothing outside its own stdout/stderr, and reads its input strictly
forward, one `getLine` at a time (`Frontend.parseExportHandleD`), so a
Mathlib-scale export never materialises anywhere — not on disk, and in
particular not in `/tmp`, which is commonly a RAM-backed tmpfs where a
multi-gigabyte scratch file would be charged to memory.  There is
nothing to clean up on any exit path.  The rule for anything that
*does* need scratch space — the test scripts, which gunzip fixtures —
is: honour `TMPDIR` if set, otherwise `./_tmp/tmp` (the project's
on-disk scratch convention); never default to the system temp
directory.
-/

open ConLeche

def ConLeche.CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- The whole input side of a run: the parsed declarations, read
straight from the file.  Since task #207 there is nothing else —
no preprocessor detection, no spawn, no pipe. -/
def parseInput (file : String) (prelude : Frontend.PreludeIx) (inModel : Bool) :
    IO (Except Frontend.FrontendError Frontend.ParseResultD) := do
  let census := (← IO.getEnv "CON_LECHE_INMODEL_CENSUS") == some "1"
  Frontend.parseExportStreamD file prelude inModel census

/-- `declPName` for the direct-parse `DeclC` records (task #171).  The
formatting itself lives beside the checker (`ConLeche.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : ConLeche.Cached.DeclC → String := ConLeche.Cached.declCLabel

/-- **Phase A's loop — the driver's install pass, carrying its own
accepting run.**  Each record is installed by
`ConLeche.Cached.annotDeclStep`: a separable value declaration is
annotated and pushed with its check recorded, everything else is checked
in full.  The loop carries the chain of accepting steps
(`ConLeche.Cached.InstallRun`) of the records it has consumed — a
proposition, so nothing at run time — and returns it with the result:
what this loop returns IS an `InstalledEnv mode ds`
(`ConLeche/Cached/Installed.lean`), phase A of the fold `checkDecls`.
Whatever it prints between steps is irrelevant to that type, which is
why ONE loop serves the plain run, the `--progress` heartbeat and the
route trace alike.

**Written tail-recursively, threading `p` and `s` LINEARLY** (task
#182's finding, `agent/fenv-linear`): a `for … in ds` loop with
`let mut` accumulators desugars to code that `lean_inc`s both the
`FEnv` and the `CState` before each step, so `lean_is_exclusive` is
false at the index inserts and every hashmap copies its bucket array
per declaration — quadratic at Mathlib scale, which is what made the
`traceLoopC` probe unusable.  Here the previous `p`/`s` are dead at the
recursive call, so the C carries no `lean_inc` of either before the
step, and the cost per declaration is flat.  The run is carried in the
SNOC direction (`InstallRun.snoc`) precisely so that the call stays a
tail call: a cons-direction proof would wrap the result on the way
back, one frame per declaration.

**Stride 1 is the localisation lane.**  With `--progress` (bare, or
`--progress=1`) every declaration is announced before it is installed,
so a run that dies — an OOM, a timeout, a `SIGKILL` — names on its last
line the declaration it died in.  The index is the FOLD position, not
the stream's record index: the parse folds the basis and `quot` blocks
and drops taint-skipped records, so the two drift apart by a
stream-dependent amount.  Calibrate by NAME. -/
def installLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) (trace : Bool) (inModelled : Array Name)
    (ds : List ConLeche.Cached.DeclC)
    (p₀ : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) (s₀ : ConLeche.Cached.CState) :
    (rest : List ConLeche.Cached.DeclC) →
    (p : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) →
    (s : ConLeche.Cached.CState) →
    (∃ done, done ++ rest = ds ∧ ConLeche.Cached.InstallRun mode done p₀ s₀ p s) →
      IO (Except (ConLeche.CheckError × Nat)
        (Σ' (p' : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck)
          (s' : ConLeche.Cached.CState), PLift (ConLeche.Cached.InstallRun mode ds p₀ s₀ p' s')))
  | [], p, s, hrun =>
    return .ok ⟨p, s, ⟨by
      obtain ⟨done, hds, hr⟩ := hrun
      rw [List.append_nil] at hds
      exact hds ▸ hr⟩⟩
  | pd :: rest, p, s, hrun => do
    if stride > 0 && p.1 % stride == 0 then
      let now ← IO.monoMsNow
      err.putStr s!"con-leche: progress {p.1}/{total} \
        {ConLeche.Cached.declCLabel pd} \
        t={ConLeche.Cached.msSecs (now - t0)}s\n"
      err.flush
    -- THE ROUTE TRACE (`CON_LECHE_ROUTE_TRACE`, task #193): one line per
    -- inductive block naming the install route the checker is about
    -- to take — the recognisers run here on the same environment the
    -- step sees, so the line is exactly the dispatch of
    -- `checkIndDeclSF` (`ConLeche/Cached/CheckerC.lean`).  It is the
    -- route census's instrument (`tests/route-census.sh`): every block
    -- must read `fix`, `inmodel` or `basis` — a `modeled` line means
    -- the block is on NO route (the recogniser refused it and the
    -- in-process modeller did not model it), so the install declines.
    -- Since task #219 a `_model` record in the stream is an ordinary
    -- declaration and cannot route a block.
    if trace then
      match pd with
      | .indDecl block nP =>
        let route :=
          if (ConLeche.nativeParts? nP block).isSome then "fix"
          else if inModelled.contains ((block.head?.map (·.name)).getD .anonymous)
            then "inmodel"
          else "modeled"
        err.putStr s!"con-leche: route \
          {(block.head?.map (·.name)).getD .anonymous} {route}\n"
        err.flush
      | .basisDecl k =>
        -- a pinned basis block: matched by the parse before any
        -- recogniser runs, installed from the pin
        err.putStr s!"con-leche: route \
          {(k.decls.head?.map (·.name)).getD .anonymous} basis\n"
        err.flush
      | _ => pure ()
    match h : ConLeche.Cached.annotDeclStep mode p pd s with
    | .ok (p₁, s₁) =>
      installLoop mode err stride total t0 trace inModelled ds p₀ s₀ rest p₁ s₁ (by
        obtain ⟨done, hds, hr⟩ := hrun
        exact ⟨done ++ [pd], by rw [List.append_assoc]; exact hds,
          ConLeche.Cached.InstallRun.snoc mode hr h⟩)
    | .error e => return .error e

/-- **Phase B's loop — the driver's check pass, carrying the checks it
has established.**  Record `k` is checked against the prefix view of
the installed index from a fresh memo state
(`ConLeche.Cached.checkPending`), and the accumulator — `GroupChecked`
of every record below `k`, a proposition — grows by one; at the end the
installed environment and the accumulator ARE a `FullyChecked mode ds`,
phase B of the fold `checkDecls`.  The records are independent: a
later loop may hand them to workers and collect the same facts.  With
`--progress`, one line per record. -/
def checkLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Cached.DeclC} (e : ConLeche.Cached.InstalledEnv mode ds) :
    (k : Nat) → (∀ j, j < k → ConLeche.Cached.GroupChecked mode e j) →
      IO (Except (ConLeche.CheckError × Nat) (ConLeche.Cached.FullyChecked mode ds))
  | k, acc =>
    if hk : k < e.pend.size then do
      if stride > 0 && k % stride == 0 then
        let now ← IO.monoMsNow
        err.putStr s!"con-leche: progress check {k}/{e.pend.size} {e.pend[k].vg.cvA.name} \
          (fold position {e.pend[k].pos}) t={ConLeche.Cached.msSecs (now - t0)}s\n"
        err.flush
      match h : ConLeche.Cached.checkPending mode e.fe e.pend[k] {} with
      | .ok ((), _) =>
        checkLoop mode err stride t0 e (k + 1)
          (ConLeche.Cached.groupChecked_extend mode acc
            (ConLeche.Cached.groupChecked_of_run mode e hk h))
      | .error e' => return .error (e', e.pend[k].pos)
    else
      return .ok ⟨e, ConLeche.Cached.groupChecked_all mode
        (fun j hj => acc j (Nat.lt_of_lt_of_le hj (Nat.le_of_not_lt hk)))⟩
  termination_by k => e.pend.size - k

/-- **The driver**: `installLoop` then `checkLoop`, and what comes out is
the environment together with the proof that the fold `checkDecls`
(`ConLeche/Cached/Installed.lean`) returns it — the subject of the main
theorem `ConLeche.no_proof_of_False` (`ConLeche/MainTheorem.lean`).  The
two loops are the fold's two phases with the heartbeat and the route
trace printed between the steps; the fully checked environment they
assemble is an accept of the fold (`ConLeche.Cached.fullyChecked_checkDecls`),
so the success line `checkMain` prints is printed from an accept of
`checkDecls` and from nothing else.  A rejection carries the fold
position of the declaration it names. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride total t0 : Nat)
    (trace : Bool) (inModelled : Array Name) (ds : List ConLeche.Cached.DeclC) :
    IO (Except (ConLeche.CheckError × Nat)
      { env : ConLeche.Env // ConLeche.Cached.checkDecls mode ds = .ok env }) := do
  match ← installLoop mode err stride total t0 trace inModelled ds
      (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) {} ds
      (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) {} ⟨[], rfl, .nil _ _⟩ with
  | .error e => return .error e
  | .ok ⟨(n, fe, pend), s, ⟨r⟩⟩ =>
    let e : ConLeche.Cached.InstalledEnv mode ds := ⟨fe, pend, ⟨n, s, r⟩⟩
    if stride > 0 then
      let now ← IO.monoMsNow
      err.putStr s!"con-leche: progress install done: {pend.size} \
        pending checks t={ConLeche.Cached.msSecs (now - t0)}s\n"
      err.flush
    match ← checkLoop mode err stride t0 e 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) with
    | .error e => return .error e
    | .ok fc => return .ok ⟨fc.env, ConLeche.Cached.fullyChecked_checkDecls mode fc⟩

/-- The progress heartbeat's stride, read off the `--progress[=<stride>]`
flag (2026-09-07; a FLAG since task #229 — it selects a run mode, the
unverified progress fold instead of the verified one, which is what
flags are for, and it was an environment variable before).  No flag is
off; bare `--progress` is stride 1.  A value that is not a decimal
numeral, and `0` — the flag asking for no heartbeat — are usage errors
(exit 3), per the provenance discipline the retired spellings follow: a
run's output must be readable off its invocation, never silently
degraded. -/
def progressStride (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--progress takes a declaration stride of at least 1 \
      (a decimal numeral); omit the flag for no heartbeat"
  | some n => .ok n
  | none => .error s!"--progress takes a declaration stride \
      (a decimal numeral of at least 1), got {repr v}"

/-- The real driver, which `main` calls in process (task #230 removed
the OOM supervisor that used to re-exec this as a child).  `mode` is
the three-mode setting (task #147), validated once by the caller and
consumed here as configuration.

**One core at two modes, one parse.**  The interned representation
and every driver over it retired with the arena (task #172), the R
core retired with the collapsed model (2026-09-05), and the
hand-written trusted twin retired into an instantiation
(2026-09-06), so the stream is parsed directly to `ExprC`
(`Frontend.parseExportStreamD`, task #171) and checked by the one
driver — `checkDeclsIO` above — at `.verified` under `--verified` (the
default), at `.trusted` under `--trusted`.  The driver returns the
environment with the proof that the fold `checkDecls` returns it, the
fold the main theorem `ConLeche.no_proof_of_False`
(`ConLeche/MainTheorem.lean`) is about; the trusted instance is
unverified by design. -/
def checkMain (file : String) (mode : CheckMode) (stride : Nat) : IO UInt32 := do
    -- The retired environment variables (tasks #76/#134) are hard
    -- errors, not silently ignored: a verdict's provenance must be
    -- readable off the invocation (task #147).
    if (← IO.getEnv "CON_LECHE_NO_PROOF_CERTS") == some "1" then
      IO.eprintln "con-leche: CON_LECHE_NO_PROOF_CERTS is retired; the \
        cert-skipping measurement lane is the --trusted mode \
        (checking-mode front door included — see DESIGN.md, task #147)"
      return 3
    if (← IO.getEnv "CON_LECHE_INFER_ONLY") == some "1" then
      IO.eprintln "con-leche: CON_LECHE_INFER_ONLY is retired; the infer-only \
        internal discipline is part of the --trusted mode, and the \
        certified mode is --verified, the default \
        (see DESIGN.md, task #147)"
      return 3
    -- The opt-in progress heartbeat (2026-09-07, `--progress[=<stride>]`):
    -- validated by the argument parse, before any work is done, and
    -- handed down as configuration.
    -- The route trace (`CON_LECHE_ROUTE_TRACE`, task #193): one `con-leche:
    -- route <block> <struct|sum|fix|inmodel|modeled>` line per inductive block,
    -- on the progress lane (so a traced run is as unverified as a
    -- heartbeat run, and says so).
    let trace := (← IO.getEnv "CON_LECHE_ROUTE_TRACE").isSome
    let t0 ← IO.monoMsNow
    -- Every VERDICT line names the mode (2026-09-07): a `--trusted`
    -- run — the unverified lane — must never be mistaken for a
    -- `--verified` one in a log, whatever it says.
    let modeTag : String := match mode with
      | .verified => "--verified"
      | .trusted => "--trusted"
    -- THE BUILT-IN PRELUDE (task #191, `ConLeche/Frontend/Prelude.lean`):
    -- the pinned basis blocks and `Bool`, parsed from the committed
    -- `pins/<toolchain>.prelude.ndjson` and PREPENDED to every parsed
    -- stream, so the fold installs them first and unconditionally; a
    -- stream's own copy of one is dropped when identical and declines
    -- the run when different.  A prelude that does not parse is a
    -- corrupted build, reported before any input is read.
    let prelude ← match Frontend.builtinPreludeE with
      | .ok p => pure p
      | .error (.parseError line msg) =>
        IO.eprintln s!"con-leche: the built-in prelude does not parse (line \
          {line}: {msg}); regenerate it with `lake exe natop-pins-export` \
          ({modeTag})"
        return 3
      | .error (.unsupported what) =>
        IO.eprintln s!"con-leche: the built-in prelude is unsupported ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
    -- Streaming frontend (task #57, task #180): the parse reads the
    -- file line by line, so neither a wholesale text buffer nor a
    -- scratch file exists in this process.
    -- THE IN-PROCESS MODELLER (task #200; the ONLY model source, and
    -- since task #219 the only one there is): mutual and nested blocks
    -- get their `_model` family generated at parse time
    -- (`ConLeche/Frontend/InModel.lean`);
    -- `CON_LECHE_INMODEL=0` turns it off, `CON_LECHE_INMODEL_DUMP=OUT`
    -- writes the raw input with the generated records spliced in (the
    -- generator's debug gate).
    let inModel := (← IO.getEnv "CON_LECHE_INMODEL") != some "0"
    match ← parseInput file prelude inModel with
    | .error (.unsupported what) =>
      IO.eprintln s!"con-leche: declined: {what} ({modeTag})"
      return 2
    | .error (.parseError line msg) =>
      IO.eprintln s!"con-leche: {file}:{line}: {msg}"
      return 3
    | .ok ⟨decls, taintSkipped, projRewrites, preludeCount,
           preludeDropped, hoisted, inModelled, genRecords, genOwner,
           inModelGen, inModelDeclined⟩ =>
      -- the in-process modeller's receipt (task #200)
      if inModelled.size > 0 then
        IO.eprintln s!"con-leche: {inModelled.size} inductive blocks modelled \
          in-process: {String.intercalate ", " (inModelled.toList.map toString)} \
          ({genRecords} generated records, checked by the fold as \
          declarations and not counted as records of the file)"
      -- the census (`CON_LECHE_INMODEL_CENSUS=1`): every mutual/nested block's
      -- outcome, then stop — the parse only, no fold
      if (← IO.getEnv "CON_LECHE_INMODEL_CENSUS") == some "1" then
        for (n, why) in inModelDeclined do
          IO.eprintln s!"con-leche: inmodel declined {n}: {why}"
        IO.eprintln s!"con-leche: inmodel census: {inModelled.size} modelled, \
          {inModelDeclined.size} declined ({modeTag}, parse only)"
        return 0
      if let some out ← IO.getEnv "CON_LECHE_INMODEL_DUMP" then
        if inModelGen.size > 0 then
          Frontend.dumpInModel file out inModelGen
          IO.eprintln s!"con-leche: in-process models dumped to {out}"
      -- `decls` = the prelude's `preludeCount` records, then the
      -- stream's (minus `preludeDropped` identical copies of prelude
      -- records); fold positions count from the prelude's first record,
      -- and the stream's accepted-record count is
      -- `decls.size - preludeCount + preludeDropped`
      -- the projection-function rewrite's receipt (2026-09-06,
      -- `ConLeche/Frontend/ProjRec.lean`): how many non-direct
      -- structure-like projection functions the parse replaced by
      -- recursor applications
      if projRewrites.size > 0 then
        IO.eprintln s!"con-leche: {projRewrites.size} projection functions of \
          non-direct structure-likes rewritten to recursor form"
        if (← IO.getEnv "CON_LECHE_PROJREC_TRACE").isSome then
          for n in projRewrites do
            IO.eprintln s!"con-leche:   rewritten {n}"
      -- the ground hoist's receipt (task #191,
      -- `ConLeche/Frontend/NatOpGround.lean`): records moved ahead of a
      -- pinned Nat operation whose certificate statements they ground
      if hoisted.size > 0 then
        IO.eprintln s!"con-leche: {hoisted.size} declarations hoisted ahead of \
          the pinned Nat operations they ground: \
          {String.intercalate ", " (hoisted.toList.map toString)}"
      -- Taint-skip verdict (user directive 2026-08-24): declarations
      -- using tolerated axioms were *skipped* during parsing (they
      -- are absent from `decls`, so nothing tainted can be checked
      -- or installed) and the rest of the stream was checked; a
      -- clean run over a stream with skips is still a decline —
      -- uses of tolerated axioms are never accepted.
      -- On a stream that also FAILED, the skips are reported beside
      -- the failure and the failure's own exit code stands.  (The
      -- accepting case is the arm below: it never prints "accepted".)
      let taintNote : IO Unit := do
        unless taintSkipped.isEmpty do
          IO.eprintln s!"con-leche: declined: \
            {Frontend.taintSummary taintSkipped} ({modeTag})"
      -- ONE driver, two modes (2026-09-06; task #185): the trusted
      -- mode is the shared bodies at `.trusted`, the verified mode the
      -- same bodies at `.verified` — the mode is passed straight down.
      -- **One driver, and it returns its proof.**  `checkDeclsIO`
      -- above runs the fold's two phases — phase A installs every
      -- record and carries its accepting run, phase B checks every
      -- recorded declaration against the prefix view of the installed
      -- index and carries every check — and what comes out is the
      -- environment with the proof that `ConLeche.Cached.checkDecls`
      -- returns it, the fold the main theorem
      -- `ConLeche.no_proof_of_False` (`ConLeche/MainTheorem.lean`) is
      -- about.  The success line below is printed from that value and
      -- from nothing else.  Printing between the steps (`--progress`,
      -- the route trace) changes nothing about the proof, so there is
      -- no second loop.
      --
      -- **Reading the index**: `i` is the *fold* position, and it is
      -- NOT the stream's declaration-record index.  The parse folds
      -- the four `quot` records into one `basisDecl` and drops a few
      -- others, a taint-skipping stream loses more, and — since task
      -- #200 — the in-process modeller ADDS records the file does not
      -- contain, so the fold can run AHEAD of the file's index.
      -- Measured on raw `init-full`: 53 093 declaration records in the
      -- file against 53 118 fold positions, the +25 being
      -- `Lean.Syntax`'s generated model family (30 records) less the
      -- 5 folded and skipped ones.  Since task #219 the generated
      -- records are subtracted from the VERDICT's count (they are
      -- declarations of the fold, never records of the file) and a
      -- generated record that fails is named with its block; the fold
      -- POSITION still counts them.  The declaration NAME on the line
      -- is the portable handle.
      let tParse ← IO.monoMsNow
      if stride > 0 then
        IO.eprintln s!"con-leche: progress parse done: {decls.size - preludeCount} \
          declarations after the {preludeCount} built-in prelude records \
          ({preludeDropped} stream copies of prelude records dropped) \
          t={ConLeche.Cached.msSecs (tParse - t0)}s (parse)"
        (← IO.getStderr).flush
      -- The closing line: how far the loop got (`= N` on an accept,
      -- the failing position otherwise) and how long it took.
      let progressDone : Nat → IO Unit := fun reached => do
        if stride > 0 then
          let now ← IO.monoMsNow
          IO.eprintln s!"con-leche: progress fold done: {reached}/\
            {decls.size} t={ConLeche.Cached.msSecs (now - t0)}s \
            (fold {ConLeche.Cached.msSecs (now - tParse)}s)"
          (← IO.getStderr).flush
      let err ← IO.getStderr
      let verdict ← checkDeclsIO mode err stride decls.size t0 trace inModelled decls.toList
      match verdict with
      | .ok ⟨env, _⟩ =>
        progressDone decls.size
        -- A DECLINED stream never says "accepted" (2026-09-07).  The
        -- taint-skip verdict (user directive 2026-08-24) is a
        -- decline: declarations using tolerated axioms were skipped
        -- at parse, so nothing tainted was checked or installed, and
        -- a clean run over the rest is still not an acceptance of
        -- the stream.  It used to print the accept line and *then*
        -- the decline, which reads as an accept in a log and in
        -- anything that greps for one.
        -- **The headline number is the STREAM's declaration-record
        -- count** (task #191 arithmetic, task #187 unit): the records
        -- the fold consumed minus the built-in prelude's, plus the
        -- stream records dropped as identical copies of prelude
        -- records (they ARE installed — from the prelude).  So a
        -- stream re-declaring `Bool` identically reports the same
        -- count as before the prelude existed.
        --
        -- What it replaced was `env.consts.length`, the number of
        -- environment CONSTANTS — an inductive block's type former,
        -- its constructors, its recursor, its projection table and the
        -- basis extras counted separately.  That is a property of our
        -- REPRESENTATION, not of the input: it moved whenever the
        -- representation moved (task #175 S1's one projection table
        -- per structure dropped init-full by 499 with no verdict
        -- change).  The record count is a property of the input.
        --
        -- It still does not equal the official checker's number, and
        -- it cannot: official prints `constMap.size`, its PARSED
        -- export, where an inductive record counts as its type
        -- formers, its constructors and its recursors (less the three
        -- `Quot.mk`/`.lift`/`.ind` entries it erases).  That is a
        -- third unit — also a function of the file, just a larger one.
        -- `scripts/stream-census.py` derives BOTH numbers from a
        -- stream and is checked against both checkers' actual output.
        -- The environment-constant count stays on stderr under
        -- `CON_LECHE_VERBOSE=1`.
        -- ... and minus the records the in-process modeller generated
        -- (task #219): they are checked as declarations, but they are
        -- not in the file, and the headline number is the FILE's.
        let streamRecords := decls.size - preludeCount + preludeDropped - genRecords
        let verboseCounts : IO Unit := do
          if (← IO.getEnv "CON_LECHE_VERBOSE").isSome then
            IO.eprintln s!"con-leche: environment: {env.consts.length} constants \
              from {decls.size} fold records ({preludeCount} built-in \
              prelude records, {preludeDropped} stream copies of them \
              dropped)"
        if taintSkipped.isEmpty then
          IO.println s!"con-leche: accepted {streamRecords} \
            declarations ({modeTag})"
          verboseCounts
          return 0
        else
          IO.eprintln s!"con-leche: declined ({streamRecords} \
            declarations checked, {taintSkipped.size} skipped for \
            tolerated axioms) ({modeTag}): \
            {Frontend.taintDetail taintSkipped}"
          verboseCounts
          return 2
      | .error (e, i) =>
        progressDone i
        -- **No second pass** (2026-09-07): the fold's error carries
        -- the failing declaration's FOLD POSITION, so the message is
        -- read off the record array the driver already holds.  What
        -- this replaced was a diagnostic re-run (`diagLoopC`) of the
        -- same step over the same records — a full re-check of the
        -- accepted prefix, and a lie waiting to happen if the two
        -- runs ever disagreed.
        --
        -- `i` is the FOLD position.  The stream's
        -- declaration-record index is NOT a fixed offset from it —
        -- measured, 2026-09-07: the parse folds the four `quot`
        -- records into one `basisDecl` and drops a few others, so
        -- `init-full` runs at offset 0 for most of the stream and
        -- ends 5 short (54 351 declaration records, 54 346 fold
        -- positions), while the `CON_LECHE_TRACE_DECLS` lane measured
        -- +4 on the Mathlib stream.  The declaration NAME is the
        -- portable handle (`_tmp/frontier3/decl_index.py <stream>
        -- <name>` turns it into a record index and a percentage).
        let loc := if h : i < decls.size then
            let d := decls[i]
            match d.names.findSome? (fun n => genOwner[n]?) with
            | some T =>
              -- a record the in-process modeller generated: the file has
              -- no position for it, so the BLOCK it models is the handle
              s!" [at {declCName d}, a generated model record of \
                inductive {T}, fold position {i}]"
            | none => s!" [at {declCName d}, fold position {i}]"
          else s!" [at fold position {i}]"
        let now ← IO.monoMsNow
        IO.eprintln s!"con-leche: {e}{loc} ({modeTag}) \
          t={ConLeche.Cached.msSecs (now - t0)}s"
        taintNote
        return e.exitCode


def usage : String := String.intercalate "\n" [
  "usage: con-leche [--verified|--trusted] [--progress[=<stride>]] FILE.ndjson",
  "       con-leche --help",
  "",
  "  --verified        the default, and the mode the main theorem is",
  "                    about: the graded model with the annotation-",
  "                    gated checks.  The validated-annotation beta",
  "                    gate skips per-redex argument certificates at",
  "                    provably non-Prop binders, and the io-graded",
  "                    knot skips the per-argument application",
  "                    certificate under the same licence; every other",
  "                    certificate family runs.  The theorem: if the",
  "                    declaration fold accepts a stream in this mode",
  "                    (checkDecls .verified ds = .ok env), the",
  "                    environment env holds no constant whose type is",
  "                    False (ConLeche.no_proof_of_False,",
  "                    ConLeche/MainTheorem.lean)",
  "  --trusted         the unverified mode: the SAME checker bodies as",
  "                    --verified, instantiated at the mode with the",
  "                    certification-only work switched off (the",
  "                    verifiedChecks and certs mode functions false):",
  "                    the annotation validations, the lambda-codomain",
  "                    sort check, and the certificate families the",
  "                    reference kernel does not run (the beta/io",
  "                    argument certificates, the iota/eta/unit/K",
  "                    telescope certificates, the projection",
  "                    certificate) are omitted; every check the",
  "                    official kernel performs stays.  Everything",
  "                    believed necessary for SOUNDNESS stays, which is",
  "                    not the same as necessary for the soundness",
  "                    proof to go through: an accept in this mode is",
  "                    outside the theorem.  The mode is never",
  "                    optimized on its own — it is the verified mode",
  "                    with certain steps omitted",
  "  --progress[=<stride>]",
  "                    opt-in progress heartbeat on STDERR.  The driver",
  "                    runs two phases and every <stride>-th step of",
  "                    each announces itself: 'con-leche: progress",
  "                    <i>/<N> <decl> t=<s>s' per record installed, and",
  "                    'con-leche: progress check <k>/<M> <name> (fold",
  "                    position <i>) t=<s>s' per recorded declaration",
  "                    checked.  Around them come one line when the",
  "                    parse finishes, one when the install phase does",
  "                    ('progress install done: <M> pending checks')",
  "                    and one when the fold does ('progress fold done:",
  "                    <reached>/<N>').  t= is the elapsed time since",
  "                    the run started, so a declaration that sits for",
  "                    minutes is visible as a gap between two lines;",
  "                    each line is printed BEFORE its declaration is",
  "                    handled, so a run that dies names the",
  "                    declaration it died in.  <i> is the FOLD",
  "                    position, which the stream's declaration-record",
  "                    index sits near but not at a fixed offset above.",
  "                    Bare --progress is stride 1 (the localisation",
  "                    lane: every declaration is announced before it is",
  "                    checked).  Without the flag there is no",
  "                    heartbeat; a stride that is not a decimal",
  "                    numeral, or 0, is a usage error.  The flag may",
  "                    come before or after --verified/--trusted.",
  "",
  "                    The heartbeat is printed between the steps of",
  "                    the ONE driver the binary has: it installs every",
  "                    record, then checks every recorded declaration,",
  "                    and returns the environment together with the",
  "                    proof that checkDecls returns it — what it",
  "                    prints in between does not touch that value, so",
  "                    a run with the flag is covered exactly as a run",
  "                    without it.",
  "  --help            print this text on STDOUT and exit 0, in any",
  "                    argument position; no input is read.",
  "",
  "  CON_LECHE_ROUTE_TRACE=1",
  "                    the install-route audit (task #193): one",
  "                    'con-leche: route <block> <struct|sum|fix|inmodel|modeled>'",
  "                    line",
  "                    on STDERR per inductive block, naming the route",
  "                    the checker takes for it (the fixed-point route",
  "                    (task #188/#210), the in-process model (task",
  "                    #200), a pinned basis block, or 'modeled' — a",
  "                    block on NO route, which declines).",
  "                    tests/route-census.sh pins the per-route counts",
  "                    over every good fixture: no block may read",
  "                    'modeled'.",
  "                    Printed by the install phase of the one",
  "                    driver, beside the --progress heartbeat.",
  "",
  "  CON_LECHE_INMODEL=0    turn the IN-PROCESS MODELLER off (task #200).  By",
  "                    default every mutual or nested inductive block",
  "                    gets a model generated at parse time",
  "                    (ConLeche/Frontend/InModel/*) and pushed ahead of",
  "                    the block; the generated records are checked by",
  "                    the fold like any declaration -- and counted as",
  "                    what they are, declarations of the fold rather",
  "                    than records of the file, so the verdict line",
  "                    reports the file's own count (task #219).  A",
  "                    generator decline is the run's decline, naming",
  "                    the class.  The route trace reads `inmodel` for",
  "                    such a block.  DEBUG SWITCH ONLY: the in-process",
  "                    modeller is the checker's only model source --",
  "                    a stream record named `T._model` is an ordinary",
  "                    declaration and routes nothing (task #219) -- so",
  "                    with the flag off",
  "                    every mutual or nested block reaches the fold",
  "                    bare and the run declines with 'no install",
  "                    route for'.",
  "                    A verdict produced with it set is not the",
  "                    checker's verdict on the stream.",
  "  CON_LECHE_INMODEL_DUMP=OUT",
  "                    write a copy of the raw input with the generated",
  "                    records spliced in ahead of each modelled block",
  "                    (lean4export format; the generator's debug gate,",
  "                    tests/inmodel.sh).",
  "",
  "  CON_LECHE_VERBOSE=1    add one stderr line beside the verdict giving the",
  "                    ENVIRONMENT-CONSTANT count and the fold's record",
  "                    count.  The verdict line counts the STREAM's",
  "                    accepted declaration RECORDS: one per",
  "                    def/theorem/opaque/axiom/inductive record the",
  "                    stream declared and the fold consumed.  The",
  "                    built-in prelude's own records are not counted,",
  "                    and a stream record dropped as an identical copy",
  "                    of a prelude record is (it is installed, from the",
  "                    prelude).  That count is a property of the INPUT.",
  "                    The constant count is not: an inductive record",
  "                    installs several constants (type former,",
  "                    constructors, recursor, projection table), so it",
  "                    moves when the representation moves.  NB the",
  "                    official kernel's 'Accepted N declarations' is a",
  "                    THIRD unit — its parsed constMap, where an",
  "                    inductive record counts as its members — also a",
  "                    function of the file, just a larger one;",
  "                    scripts/stream-census.py derives both from a",
  "                    stream.",
  "",

  "THE BUILT-IN PRELUDE (task #191).  Every run installs, first and",
  "unconditionally, the checker's own little prelude — the six pinned",
  "basis blocks (Eq, Nat, PUnit, Empty, False, Quot) and the toolchain's",
  "Bool block (pins/<toolchain>.prelude.ndjson, embedded at build time;",
  "ConLeche/Frontend/Prelude.lean) — so the pin-certified Nat operations",
  "find their ground whatever order the export chose.  A stream's own",
  "copy of a prelude declaration is dropped when it is the same",
  "declaration and DECLINES the run (exit 2, naming it) when it differs;",
  "a mismatching basis block still REJECTS (reserved name), as before.",
  "A pinned operation's stream-certified structural ground (Nat.ble,",
  "Nat.sub, Nat.mul — spelled into the certificate statements, not",
  "reachable from the operation's own value) is HOISTED ahead of the",
  "operation when the stream declares it later (ConLeche/Frontend/",
  "NatOpGround.lean): a dependency-closed reorder of the parsed list,",
  "reported on stderr.  Both are pure transformations of the parsed",
  "list below the verified fold; the main theorem is about the fold",
  "over prelude ++ stream.",
  "",
  "NO PREPROCESSOR (task #207).  The input is a RAW lean4export stream:",
  "there is no external tool, no dependency and no spawn.  Every",
  "inductive block is installed by the fixed-point route — structures,",
  "sums, indexed families, finitary fixed points and reflexive blocks —",
  "or through a `_model` family the frontend generates IN-PROCESS at",
  "parse time and then checks as ordinary declarations.  No model is",
  "ever read from the input (task #219): a stream record whose name",
  "carries a `_model` component is an ordinary declaration with no",
  "effect on any block.  The generator is not trusted: a wrong record",
  "is rejected or declined by the fold, never accepted; it decides",
  "coverage only.  A block no route takes declines (exit 2) naming",
  "its class.",
  "",
  "There is ONE core at two modes and one parse: the verified mode",
  "(--verified, the default) and the unverified trusted mode",
  "(--trusted).  The stream is read directly to the cached",
  "representation and checked by the one driver, which returns its",
  "environment together with the proof that the fold checkDecls — the",
  "function the main theorem ConLeche.no_proof_of_False",
  "(ConLeche/MainTheorem.lean) is stated on — returns it.",
  "",
  "RETIRED FLAGS.  --set-model, --set-model=p, --set-model=r,",
  "--no-model, --tt-model, --yolo, --infer-only, --pre, --core,",
  "--core=<c>, --install-only, --check-range and --check-range=<r>",
  "are not part of the synopsis and are never silent aliases: each is",
  "rejected with a message naming what stands in its place, and the",
  "run exits 3 without reading the input, so a verdict's provenance",
  "is readable off the invocation."]

structure Args where
  mode : ConLeche.CheckMode := .verified
  /-- The progress heartbeat's stride (`--progress[=<stride>]`, task
  #229); `0` is "no flag given", i.e. no heartbeat. -/
  progress : Nat := 0
  files : Array String := #[]
  bad : Option String := none

def parseArgs : List String → Args → Args
  | [], a => a
  -- The verified lane is the GRADED core since the R core's retirement
  -- (2026-09-05); `no_proof_of_Empty_cached` is its letter.
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  -- The retired-spelling discipline (task #172): a verdict's
  -- provenance must be readable off the invocation, so a retired
  -- spelling is a hard error naming what replaced it — never a silent
  -- alias.  The mode rename (2026-09-06) is under the same rule: the
  -- old spellings name a *vocabulary*, not a different core, but they
  -- are still errors rather than aliases.
  | "--set-model" :: _, a =>
    { a with bad := some "--set-model is retired; the verified mode is \
        --verified, still the default (mode rename 2026-09-06 — see \
        DESIGN.md, \"MODE RENAME\")" }
  | "--set-model=p" :: _, a =>
    { a with bad := some "--set-model=p is retired; the verified mode is \
        --verified, still the default (mode rename 2026-09-06 — see \
        DESIGN.md, \"MODE RENAME\")" }
  | "--no-model" :: _, a =>
    { a with bad := some "--no-model is retired; the unverified lane is \
        --trusted (mode rename 2026-09-06 — see DESIGN.md, \"MODE \
        RENAME\")" }
  | "--set-model=r" :: _, a =>
    { a with bad := some "--set-model=r is retired; the R core (all \
        certificates unconditional) and the collapsed-model consistency \
        proof it was the subject of were deleted 2026-09-05 after the \
        acceptance delta against the graded core measured ZERO. The \
        verified lane is --verified" }
  | "--tt-model" :: _, a =>
    { a with bad := some "--tt-model is retired; the declarative \
        verification lane it selected was deleted with the mode, and \
        the certified mode is --verified (default) (task #148 T7b)" }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  -- The progress heartbeat (task #229): a FLAG, in either order with
  -- `--verified`/`--trusted`, and independent of them — it turns on
  -- the heartbeat the ONE driver prints between the steps of its two
  -- phases (`installLoop`/`checkLoop`), which is the same driver, at
  -- the same mode, as a run without it.  Bare is stride 1;
  -- `--progress=<n>` is the general form (below, with the other
  -- `=`-carrying spellings).
  | "--progress" :: rest, a => parseArgs rest { a with progress := 1 }
  | "--yolo" :: _, a =>
    { a with bad := some "--yolo is retired; the cert-skipping lane is \
        --trusted (checking-mode front door included, task #147)" }
  | "--infer-only" :: _, a =>
    { a with bad := some "--infer-only is retired; its discipline is part \
        of --trusted, and the certified mode is --verified \
        (default) (task #147)" }
  | "--pre" :: _, a =>
    { a with bad := some "--pre is retired; there is no preprocessor — \
        every input is a raw lean4export stream (task #207)" }
  -- Task #172: `--core`, `--install-only` and `--check-range` are hard
  -- errors, not silently ignored — the rule the retired mode
  -- environment variables already follow: a verdict's provenance must
  -- be readable off the invocation.
  | "--core" :: _, a =>
    { a with bad := some "--core is retired; there is one core and one \
        expression representation since task #172 (the interned arena \
        and every driver over it were deleted)" }
  | "--install-only" :: _, a =>
    { a with bad := some "--install-only is retired; the split \
        install/check driver was arena machinery and went with the \
        interned representation (task #172)" }
  | "--check-range" :: _, a =>
    { a with bad := some "--check-range is retired; the split \
        install/check driver was arena machinery and went with the \
        interned representation (task #172)" }
  | s :: rest, a =>
    if s.startsWith "--core=" then
      { a with bad := some "--core is retired; there is one core and one \
          expression representation since task #172 (the interned arena \
          and every driver over it were deleted)" }
    else if s.startsWith "--progress=" then
      match progressStride ((s.drop "--progress=".length).toString) with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if s.startsWith "--check-range=" then
      { a with bad := some "--check-range is retired; the split \
          install/check driver was arena machinery and went with the \
          interned representation (task #172)" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    return 0
  -- `--verified`/`--trusted`: the mode setting (task #147), validated
  -- here once and threaded as configuration.  Two cores since the R
  -- core's retirement (2026-09-05): the graded verified one and the
  -- unverified trusted one.
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"con-leche: {msg}"
    IO.eprintln usage
    return 3
  match a.files.toList with
  | [file] =>
    -- The checker runs IN THIS PROCESS.  Task #65 used to re-exec it as
    -- a supervised child so that the Lean runtime's out-of-memory
    -- handler (`lean_internal_panic_out_of_memory`, which prints
    -- "INTERNAL PANIC: out of memory" and calls `exit(1)`, uncatchable
    -- in process) could be translated from exit 1 into exit 3.  Task
    -- #230 removed that supervisor: a checker that spawns a copy of
    -- itself is not what belongs in the finished product, and an
    -- out-of-memory condition simply exits 1 with the runtime's panic
    -- message on stderr, which is what distinguishes it from a reject.
    checkMain file a.mode a.progress
  | _ =>
    IO.eprintln usage
    return 3
