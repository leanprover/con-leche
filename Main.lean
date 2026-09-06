import Setlec.Cached.ParsedC
import Setlec.Frontend.ExportC

/-!
Command-line driver: `setlec FILE.ndjson` reads a lean4export NDJSON file
(the `setlec-preprocess` front end for lean-inductive-models is run
transparently first, unless `--pre` says the input is already
preprocessed) and checks the declarations in order.

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
* 3 — bad usage, malformed input, or an internal failure of unclear cause

**NO TEMPORARY FILES** (task #180, 2026-09-07).  The checker writes
nothing outside its own stdout/stderr.  The preprocessor used to be run
with `-o TMPFILE` and the scratch file parsed afterwards; since the
tool's default output target *is* stdout and the frontend reads its
input strictly forward, one `getLine` at a time
(`Frontend.parseExportHandleD`), the tool is spawned with a piped
stdout and its export goes straight into the parser.  A Mathlib-scale
raw export therefore never materialises anywhere — not on disk, and in
particular not in `/tmp`, which is commonly a RAM-backed tmpfs where a
multi-gigabyte scratch file would be charged to memory.  The scratch
file is gone rather than relocated, so there is nothing left to clean
up on any exit path (a crash, an OOM kill of the supervised child, a
`--pre` run).  The rule for anything that *does* need scratch space —
the test scripts, which gunzip fixtures — is: honour `TMPDIR` if set,
otherwise `./_tmp/tmp` (the project's on-disk scratch convention);
never default to the system temp directory.

**THE PREPROCESSOR'S VERDICT IS OURS** (user ruling, 2026-09-07).  The
tool is spawned `--quiet --no-type-check-generated` (its kernel
re-check of the model islands is work setlec repeats declaration by
declaration; its structural checks stay, `--type-check-input` stays
off), and a nonzero exit is *passed through* — 1 reject, 2 decline,
anything else an error — instead of the old fallback that re-checked
the raw stream and reported a missing model.  A preprocessor that
cannot be *run* still falls back to the raw stream; that is the one
remaining fallback.
-/

open Setlec

def Setlec.CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- Resolve a tool name to an existing path: as given if it names
something that exists, else looked up on `$PATH`; `none` if neither. -/
def resolveTool (p : String) : IO (Option String) := do
  if ← System.FilePath.pathExists p then
    return some p
  if let some path ← IO.getEnv "PATH" then
    for dir in path.splitOn ":" do
      if !dir.isEmpty then
        let cand := dir ++ "/" ++ p
        if ← System.FilePath.pathExists cand then
          return some cand
  return none

/-- Locate the preprocessor (task #178: `setlec-preprocess`, the checker's own
front end for `lean-inductive-models` — the tool's `main` passed setlec's
`NativeSupport`, so the blocks `directParts?` installs directly come back
unmodelled; `SetlecPreprocess.lean`).  Search order:

1. `$SETLEC_INDUCTIVE_MODELS` — the explicit override, unchanged; the test
   harnesses point it at a nonexistent path to run a stream *raw*.
2. this build's `setlec-preprocess`;
3. the stock `lean-inductive-models` development checkout under `_tmp/` — the
   legacy fallback, which costs one `pathExists` and keeps a tree without a
   built `setlec-preprocess` working (its output is a superset: every block
   left native here is modelled there, and the direct install ignores the
   model either way);
4. `setlec-preprocess` on `$PATH`.

**Every branch resolves to a path that EXISTS, or to `none`** (task
#180): since a nonzero preprocessor exit is now setlec's verdict, "the
tool is not there" has to be decided *before* the spawn — Lean's
`IO.Process.spawn` does not fail for a missing binary, it succeeds and
the child exits 255 after printing "could not execute external
process", which is indistinguishable at the exit-code level from a tool
that ran and failed.  So the `$PATH` step is resolved here rather than
at spawn time, and a `$SETLEC_INDUCTIVE_MODELS` naming nothing that
exists means "no preprocessor" — which is exactly what the `raw` test
fixtures mean by pointing it at `/nonexistent`. -/
def findPreprocessor : IO (Option String) := do
  if let some p ← IO.getEnv "SETLEC_INDUCTIVE_MODELS" then
    return ← resolveTool p
  let dev := ".lake/build/bin/setlec-preprocess"
  if ← System.FilePath.pathExists dev then
    return some dev
  let legacy := "_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models"
  if ← System.FilePath.pathExists legacy then
    return some legacy
  resolveTool "setlec-preprocess"

/-- Does the input contain records the preprocessor must reduce
(`inductive`/`quot`)?  Streaming scan, line by line — the keys cannot
span a line boundary (ndjson, no newlines inside a record). -/
partial def needsPreprocess (file : String) : IO Bool := do
  let h ← IO.FS.Handle.mk file .read
  let rec loop : IO Bool := do
    let line ← h.getLine
    if line.isEmpty then
      return false
    if line.contains "\"inductive\"" || line.contains "\"quot\"" then
      return true
    loop
  loop

/-- What the input side of a run produced: either a parse (successful
or not) of the stream the checker is to check, or a verdict of the
*preprocessor's* own that is, per the user's ruling of 2026-09-07,
setlec's verdict. -/
inductive InputResult where
  /-- the stream was read and parsed (`.error` = the checker's own
  decline or a malformed stream) -/
  | parsed (res : Except Frontend.FrontendError Frontend.ParseResultD)
  /-- the preprocessor rejected/declined/failed; `code` is already
  translated to setlec's exit code -/
  | preVerdict (code : UInt32)

/-- Translate a nonzero preprocessor exit code into setlec's, and say
so on stderr.  **"A preprocessor reject is our reject"** (user ruling,
2026-09-07): `lean-inductive-models` follows the same arena contract we
do (its README: 1 rejected by a requested structural or kernel check,
2 a requested generation route declined an unsupported owner, 3 parser/
IO/CLI/internal error), and its kernel *is* Lean's — a block it rejects
(a non-positive occurrence, a wrong parameter count) is invalid input,
not a limitation of ours.  Until now such a run fell back to checking
the *raw* stream, which then declined for a missing model: 29 arena bad
tests expecting a reject got a decline out of it (finding F1).  That
fallback is gone; only a preprocessor that cannot be *run* falls back.

The tool's own diagnostics are on our stderr already (it is spawned
with `stderr := .inherit`, and `--quiet` silences its success reports
but never its failures) — except for the per-owner decline lines, which
are success-path reports; hence the pointer in the decline message. -/
def preprocessorVerdict (code : UInt32) (modeTag : String) : IO UInt32 := do
  if code = 1 then
    IO.eprintln s!"setlec: the preprocessor rejected the input (message \
      above) ({modeTag})"
    return 1
  else if code = 2 then
    IO.eprintln s!"setlec: declined: the preprocessor declined to model a \
      block (re-run setlec-preprocess without --quiet for the owner names) \
      ({modeTag})"
    return 2
  else
    IO.eprintln s!"setlec: the preprocessor failed (exit {code}) ({modeTag})"
    return 3

/-- Read a handle to EOF and discard it.  Used only when the parse
stopped early on a malformed line: we must stop the *writer* from
blocking on a pipe nobody drains before we can ask for its exit code,
and the tool's verdict is worth more than a fast exit here — a tool
that failed mid-stream has stopped writing anyway, so the drain is
short exactly when it matters. -/
partial def drainHandle (h : IO.FS.Handle) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return () else drainHandle h

/-- Run the preprocessor over the input, reducing inductives to the
modelled basis, and parse **its standard output as it is written**
(task #180): the tool is spawned with a piped stdout and the parser
reads that pipe line by line, so neither process holds the reduced
stream whole and nothing is written to disk.  (Task #57 had the tool
write a temp file, `-o path`, which the checker then parsed; the
streaming pipe replaces it.  The tool's own working memory — ~650 MB
on init-full — is its own, residual until lean-inductive-models itself
streams.)  Its stdout is the export by default (`outputTarget := "-"`),
so no output flag is passed at all.

**The flags.**  `--quiet` silences the per-owner success reports (a
line per generated model — thousands on `init-full`) and nothing else:
every failure message is printed unconditionally.
`--no-type-check-generated` switches off the tool's *kernel* re-check
of each generated model island: setlec checks those generated
definitions and theorems itself, as ordinary declarations of the
stream it is handed, so running Lean's kernel over them first is
duplicated work and buys no trust we would otherwise lack.  The two
*structural* checks stay on (`--check-input`/`--check-output`, the
tool's defaults: model families are checked for shape), and
`--type-check-input` stays off — submitting the untrusted input to
Lean's kernel is exactly the job we are here to do ourselves.

The child's stderr is *inherited*: with `--quiet` the tool prints only
fatal errors there, and inheriting means they reach the user (through
the supervisor's buffered stderr) instead of being swallowed by an
output capture, and no second pipe can fill while we are draining the
first.

`none` means "the tool could not be run" — the *only* remaining
fallback to the raw input (the checker then declines at the first
inductive); it is what the `raw` test fixtures exercise by pointing
`SETLEC_INDUCTIVE_MODELS` at a nonexistent path.  A nonzero exit is a
`.preVerdict` (see `preprocessorVerdict`).  A checker decline reached
before the tool exits is ours: the child is killed first, since we have
stopped draining its pipe and a blocked writer would never exit.  A *parse
error* drains instead of killing, so that a tool which failed
mid-stream — leaving us a truncated record — still gets to state its
verdict, which then wins over our reading of its debris. -/
def preprocessParse (tool file modeTag : String) : IO (Option InputResult) := do
  let child ← try
      IO.Process.spawn
        { cmd := tool
          args := #["--quiet", "--no-type-check-generated", file]
          stdin := .null, stdout := .piped, stderr := .inherit }
    catch _ => return none
  match ← Frontend.parseExportHandleD child.stdout (modeled := true) with
  | .error (.unsupported what) =>
    try child.kill catch _ => pure ()
    let _ ← child.wait
    return some (.parsed (.error (.unsupported what)))
  | .error e =>
    drainHandle child.stdout
    let code ← child.wait
    if code = 0 then
      return some (.parsed (.error e))
    else
      return some (.preVerdict (← preprocessorVerdict code modeTag))
  | .ok r =>
    let code ← child.wait
    if code = 0 then
      return some (.parsed (.ok r))
    else
      return some (.preVerdict (← preprocessorVerdict code modeTag))

/-- The whole input side of a run: the parsed declarations, obtained
either straight from the file (`--pre`, or an input with nothing for
the preprocessor to do, or a preprocessor that could not be run) or
through the preprocessor's pipe — or the preprocessor's own verdict. -/
def parseInput (file : String) (pre : Bool) (modeTag : String) :
    IO InputResult := do
  let raw : IO InputResult :=
    InputResult.parsed <$> Frontend.parseExportStreamD file (modeled := true)
  if pre then return ← raw
  unless ← needsPreprocess file do return ← raw
  let some tool ← findPreprocessor | raw
  match ← preprocessParse tool file modeTag with
  | some res => return res
  | none => raw

/-- `declPName` for the direct-parse `DeclC` records (task #171).  The
formatting itself lives beside the checker (`Setlec.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : Setlec.Cached.DeclC → String := Setlec.Cached.declCLabel

/-- **The progress lane's fold — UNVERIFIED, and the only unverified
loop in the driver** (`SETLEC_PROGRESS`, user ruling 2026-09-07).

The default run calls `Setlec.Cached.checkDeclsSPCachedD` — the pure
function `Setlec.no_proof_of_False` is about — and prints nothing per
declaration.  A pure fold cannot print, and the ways to make it print
without leaving the verified statement behind all cost more than the
printing is worth: a compiled-only hook (`@[implemented_by]`, refused
by the project's standing ruling), a `dbgTrace` branch on the checked
path, or a monad-generic loop with callbacks plus a `LawfulMonad IO`
instance core does not ship.  The user's ruling ends that: run a
*different, plainly unverified* fold when the heartbeat is on.

It is the same steps in the same order — `checkDeclStepIdxC mode`, the
position-carrying step of the verified fold, over the same records from
the same empty environment and state — with one line printed before
each declaration.  Nobody should be bothered by the difference between
these two trivial folds; what matters is that the difference is
*stated*: a run with `SETLEC_PROGRESS` set is not covered by the main
theorem, and a run without it is.

**Written tail-recursively, threading `fe` and `s` LINEARLY** (task
#182's finding, `agent/fenv-linear`): a `for … in ds` loop with
`let mut` accumulators desugars to code that `lean_inc`s both the
`FEnv` and the `CState` before each step, so `lean_is_exclusive` is
false at the index inserts and every hashmap copies its bucket array
per declaration — quadratic at Mathlib scale, which is what made the
`traceLoopC` probe unusable.  Here the previous `fe`/`s` are dead at
the recursive call, so the C carries no `lean_inc` of either before the
step (checked in `.lake/build/ir/Main.c`), and the cost per declaration
is flat.

**Stride 1 is the localisation lane.**  With `SETLEC_PROGRESS=1` every
declaration is announced before it is checked, so a run that dies — an
OOM, a timeout, a `SIGKILL` — names on its last line the declaration it
died in.  The index is the FOLD position, not the stream's record
index: the parse folds the basis and `quot` blocks and drops
taint-skipped records, so the two drift apart by a stream-dependent
amount.  Calibrate by NAME. -/
def checkDeclsProgressIO (mode : Setlec.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) :
    List Setlec.Cached.DeclC → Nat → Setlec.FEnv → Setlec.Cached.CState →
      IO (Except (Setlec.CheckError × Nat) Setlec.Env)
  | [], _, fe, _ => return .ok fe.env
  | pd :: ds, i, fe, s => do
    if stride > 0 && i % stride == 0 then
      let now ← IO.monoMsNow
      err.putStr s!"setlec: progress {i}/{total} \
        {Setlec.Cached.declCLabel pd} \
        t={Setlec.Cached.msSecs (now - t0)}s\n"
      err.flush
    match Setlec.Cached.checkDeclStepIdxC mode (i, fe) pd s with
    | .ok ((i', fe'), s') => checkDeclsProgressIO mode err stride total t0 ds i' fe' s'
    | .error e => return .error e

/-- The progress heartbeat's stride (`SETLEC_PROGRESS=<stride>`;
2026-09-07).  `none` — the variable unset — is off; a value that is not
a decimal numeral is a hard error, per the provenance discipline the
retired-variable arms follow (a run's output must be readable off its
invocation, never silently degraded).  `0` is the explicit "off". -/
def progressStride : IO (Except String Nat) := do
  match ← IO.getEnv "SETLEC_PROGRESS" with
  | none => return .ok 0
  | some s =>
    match s.toNat? with
    | some n => return .ok n
    | none => return .error s!"SETLEC_PROGRESS must be a declaration stride \
        (a decimal numeral; 0 or unset is off), got {repr s}"

/-- The real driver (run in the supervised child process).  `mode` is
the three-mode setting (task #147), validated once by the caller and
consumed here as configuration; `pre` asserts the input is already
preprocessed (`--pre`), skipping preprocessor detection and spawn.

**One core at two modes, one parse.**  The interned representation
and every driver over it retired with the arena (task #172), the R
core retired with the collapsed model (2026-09-05), and the
hand-written trusted twin retired into an instantiation
(2026-09-06), so the stream is parsed directly to `ExprC`
(`Frontend.parseExportStreamD`, task #171) and checked by the one
cached driver — at `.verified` under `--verified` (the default), at `.trusted`
under `--trusted`.  The verified instance is covered by
`no_proof_of_Empty_SPCD_P` over `checkDeclsSPCachedD`
(`Setlec/Verify/Cached/MainC.lean`); the trusted one is unverified by
design and agrees with it on the install skeletons whenever both
accept (`trusted_agrees_P_skels_shipped`). -/
def checkMain (file : String) (mode : CheckMode) (pre : Bool) : IO UInt32 := do
    -- The retired environment variables (tasks #76/#134) are hard
    -- errors, not silently ignored: a verdict's provenance must be
    -- readable off the invocation (task #147).
    if (← IO.getEnv "SETLEC_NO_PROOF_CERTS") == some "1" then
      IO.eprintln "setlec: SETLEC_NO_PROOF_CERTS is retired; the \
        cert-skipping measurement lane is the --trusted mode \
        (checking-mode front door included — see DESIGN.md, task #147)"
      return 3
    if (← IO.getEnv "SETLEC_INFER_ONLY") == some "1" then
      IO.eprintln "setlec: SETLEC_INFER_ONLY is retired; the infer-only \
        internal discipline is part of the --trusted mode, and the \
        certified mode is --verified, the default \
        (see DESIGN.md, task #147)"
      return 3
    -- The opt-in progress heartbeat (2026-09-07): validated here, once,
    -- before any work is done.
    let stride ← match ← progressStride with
      | .error msg => IO.eprintln s!"setlec: {msg}"; return 3
      | .ok n => pure n
    let t0 ← IO.monoMsNow
    -- Every VERDICT line names the mode (2026-09-07): a `--trusted`
    -- run — the unverified lane — must never be mistaken for a
    -- `--verified` one in a log, whatever it says.
    let modeTag : String := match mode with
      | .verified => "--verified"
      | .trusted => "--trusted"
    -- Streaming frontend (task #57, task #180): the preprocessor's
    -- stdout *is* the parser's input — the parse reads it line by line
    -- off the pipe, so neither a wholesale text buffer nor a scratch
    -- file exists in this process.  `--pre` (an explicit user
    -- assertion, never content sniffing) skips detection and the
    -- preprocessor spawn.
    match ← parseInput file pre modeTag with
    | .preVerdict code =>
      -- the preprocessor's verdict is ours (user ruling 2026-09-07);
      -- `preVerdict` has already printed the line, which names the mode
      -- and is never an accept (it is reached only on a nonzero exit)
      return code
    | .parsed (.error (.unsupported what)) =>
      IO.eprintln s!"setlec: declined: {what} ({modeTag})"
      return 2
    | .parsed (.error (.parseError line msg)) =>
      IO.eprintln s!"setlec: {file}:{line}: {msg}"
      return 3
    | .parsed (.ok ⟨decls, taintSkipped, projRewrites⟩) =>
      -- the projection-function rewrite's receipt (2026-09-06,
      -- `Setlec/Frontend/ProjRec.lean`): how many non-direct
      -- structure-like projection functions the parse replaced by
      -- recursor applications
      if projRewrites.size > 0 then
        IO.eprintln s!"setlec: {projRewrites.size} projection functions of \
          non-direct structure-likes rewritten to recursor form"
        if (← IO.getEnv "SETLEC_PROJREC_TRACE").isSome then
          for n in projRewrites do
            IO.eprintln s!"setlec:   rewritten {n}"
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
          IO.eprintln s!"setlec: declined: \
            {Frontend.taintSummary taintSkipped} ({modeTag})"
      -- ONE driver, two modes (2026-09-06; task #185): the trusted
      -- mode is the shared bodies at `.trusted`, the verified mode the
      -- same bodies at `.verified` — the mode is passed straight down.
      -- **Two loops** (user ruling, 2026-09-07).  Without
      -- `SETLEC_PROGRESS` the driver calls the verified fold
      -- `Setlec.Cached.checkDeclsSPCachedD` directly — the exact
      -- function `Setlec.no_proof_of_False` (`Setlec/MainTheorem.lean`)
      -- is about.  With it, the driver calls `checkDeclsProgressIO`
      -- above: the same steps in the same order, in `IO`, printing one
      -- line before each declaration — plainly unverified, and said so
      -- in its docstring, in `--help` and in DESIGN.  The two folds
      -- differ in the print and nothing else, and nothing about the
      -- verified statement is bent to accommodate the printing.
      --
      -- **Reading the index**: `i` is the *fold* position.  The
      -- stream's declaration-record index is close to it but not a
      -- fixed offset above it — the parse folds the four `quot`
      -- records into one `basisDecl` and drops a few others, and a
      -- taint-skipping stream loses more (measured on
      -- `init-full-pre-native`: 54 351 records against 54 346 fold
      -- positions, offset 0 through position 5 000 and 5 by the end;
      -- the `SETLEC_TRACE_DECLS` lane's `+4` is the Mathlib stream's
      -- own total).  The declaration NAME on the line is the
      -- portable handle.
      let tParse ← IO.monoMsNow
      if stride > 0 then
        IO.eprintln s!"setlec: progress parse done: {decls.size} \
          declarations t={Setlec.Cached.msSecs (tParse - t0)}s \
          (preprocess and parse; the progress lane's fold is \
          UNVERIFIED — see --help)"
        (← IO.getStderr).flush
      -- The closing line: how far the loop got (`= N` on an accept,
      -- the failing position otherwise) and how long it took.
      let progressDone : Nat → IO Unit := fun reached => do
        if stride > 0 then
          let now ← IO.monoMsNow
          IO.eprintln s!"setlec: progress fold done: {reached}/\
            {decls.size} t={Setlec.Cached.msSecs (now - t0)}s \
            (fold {Setlec.Cached.msSecs (now - tParse)}s)"
          (← IO.getStderr).flush
      let verdict ←
        if stride > 0 then
          checkDeclsProgressIO mode (← IO.getStderr) stride decls.size t0
            decls.toList 0 (Setlec.mkFEnv Setlec.Env.empty) {}
        else
          pure (Setlec.Cached.checkDeclsSPCachedD mode decls.toList)
      match verdict with
      | .ok env =>
        progressDone decls.size
        -- A DECLINED stream never says "accepted" (2026-09-07).  The
        -- taint-skip verdict (user directive 2026-08-24) is a
        -- decline: declarations using tolerated axioms were skipped
        -- at parse, so nothing tainted was checked or installed, and
        -- a clean run over the rest is still not an acceptance of
        -- the stream.  It used to print the accept line and *then*
        -- the decline, which reads as an accept in a log and in
        -- anything that greps for one.
        if taintSkipped.isEmpty then
          IO.println s!"setlec: accepted {env.consts.length} \
            declarations ({modeTag})"
          return 0
        else
          IO.eprintln s!"setlec: declined ({env.consts.length} \
            declarations checked, {taintSkipped.size} skipped for \
            tolerated axioms) ({modeTag}): \
            {Frontend.taintDetail taintSkipped}"
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
        -- positions), while the `SETLEC_TRACE_DECLS` lane measured
        -- +4 on the Mathlib stream.  The declaration NAME is the
        -- portable handle (`_tmp/frontier3/decl_index.py <stream>
        -- <name>` turns it into a record index and a percentage).
        let loc := if h : i < decls.size then
            s!" [at {declCName decls[i]}, fold position {i}]"
          else s!" [at fold position {i}]"
        let now ← IO.monoMsNow
        IO.eprintln s!"setlec: {e}{loc} ({modeTag}) \
          t={Setlec.Cached.msSecs (now - t0)}s"
        taintNote
        return e.exitCode


def usage : String := String.intercalate "\n" [
  "usage: setlec [--verified|--trusted] [--pre] FILE.ndjson",
  "",
  "  --verified        the default: the verified mode (graded model,",
  "                    annotation-gated checks).  The validated-",
  "                    annotation beta gate skips per-redex argument",
  "                    certificates at provably non-Prop binders, and",
  "                    the io-graded knot skips the per-argument",
  "                    application certificate under the same licence.",
  "                    The seven TT-lane checks (tasks #126/#129/#130/",
  "                    #135/#136/#137/#146) are off; every other",
  "                    certificate family runs.  Covered by",
  "                    no_proof_of_Empty_SPCD_P over the driver this",
  "                    binary runs (Setlec/Verify/Cached/MainC.lean)",
  "  --trusted         the unverified mode: the SAME checker bodies as",
  "                    --verified, instantiated at the mode with the",
  "                    certification-only work switched off (the",
  "                    verifiedChecks and certs mode functions false):",
  "                    the annotation validations and the lambda-",
  "                    codomain sort check, and the certificate",
  "                    families the reference kernel does not run (the",
  "                    beta/io argument certificates, the iota/eta/unit/K",
  "                    telescope certificates, the projection",
  "                    certificate) are omitted; every check official",
  "                    performs stays.  Everything believed necessary",
  "                    for SOUNDNESS stays (which is",
  "                    not the same as necessary for the soundness",
  "                    proof to go through), and the mode is never",
  "                    optimized on its own: it is the real mode with",
  "                    certain steps omitted.  Replaces the retired",
  "                    --yolo/SETLEC_NO_PROOF_CERTS and",
  "                    --infer-only/SETLEC_INFER_ONLY",
  "  SETLEC_PROGRESS=<stride>",
  "                    opt-in progress heartbeat on STDERR: one",
  "                    'setlec: progress <i>/<N> <decl> t=<s>s' line",
  "                    every <stride> declarations, plus one line when",
  "                    the parse finishes and one when the fold does.",
  "                    t= is the elapsed time since the run started, so",
  "                    a declaration that sits for minutes is visible",
  "                    as a gap between two lines; the line is printed",
  "                    BEFORE the declaration is checked, so a run that",
  "                    dies names the declaration it died in.",
  "                    <i> is the FOLD position, which the stream's",
  "                    declaration-record index sits near but not at a",
  "                    fixed offset above.  Unset or 0 is off.",
  "",
  "                    NOTE: this lane runs a SEPARATE, UNVERIFIED fold",
  "                    (Main.checkDeclsProgressIO) — the same steps in",
  "                    the same order as the verified one with a line",
  "                    printed before each declaration, because a pure",
  "                    fold cannot print.  A run WITHOUT this variable",
  "                    calls checkDeclsSPCachedD, the function the main",
  "                    theorem (Setlec.no_proof_of_False) is about; a",
  "                    run with it is not covered by that theorem.",
  "",
  "  --pre             assert FILE is already preprocessed output of",
  "                    setlec-preprocess (or the stock",
  "                    lean-inductive-models): skip the preprocessor",
  "                    detection scan and spawn entirely",
  "",
  "THE PREPROCESSOR.  Unless --pre says otherwise, an input containing",
  "inductive/quot records is run through setlec-preprocess, which",
  "reduces inductives to the modelled basis.  It is spawned with",
  "--quiet --no-type-check-generated (setlec checks the generated",
  "declarations itself; its structural model checks stay on, and the",
  "input is never submitted to Lean's kernel), it writes its export to",
  "its stdout, and setlec parses that pipe as it is produced: no",
  "temporary file is created, by either process, anywhere.",
  "",
  "A PREPROCESSOR REJECT IS OUR REJECT.  The tool follows the same",
  "arena exit-code contract; its verdict is passed through — exit 1",
  "(its kernel rejected a block: a non-positive occurrence, a wrong",
  "parameter count) is setlec's reject, exit 2 its decline, any other",
  "failure an error (3), each with the tool's own message on stderr.",
  "Only a preprocessor that cannot be RUN falls back to checking the",
  "raw stream (which then declines at the first inductive); set",
  "SETLEC_INDUCTIVE_MODELS to a nonexistent path to force that.",
  "",
  "There is ONE core at two modes and one parse: the verified mode",
  "(--verified, the default) and the unverified trusted mode",
  "(--trusted).  The stream is read directly to the cached",
  "representation and checked by the one driver, which the capstone",
  "letter is about at the verified mode (no_proof_of_Empty_SPCD_P in",
  "Setlec/Verify/Cached/MainC.lean).  Retired: --set-model/",
  "--set-model=p (now --verified) and --no-model (now --trusted),",
  "2026-09-06; the --core selector, the interned arena and the",
  "--install-only/--check-range split driver (task #172); and the R",
  "core with --set-model=r (2026-09-05, with the collapsed-model",
  "consistency proof it was the subject of)."]

structure Args where
  mode : Setlec.CheckMode := .verified
  pre : Bool := false
  files : Array String := #[]
  bad : Option String := none

def parseArgs : List String → Args → Args
  | [], a => a
  -- The verified lane is the GRADED core since the R core's retirement
  -- (2026-09-05); `no_proof_of_Empty_SPCD_P` is its letter.
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
  | "--yolo" :: _, a =>
    { a with bad := some "--yolo is retired; the cert-skipping lane is \
        --trusted (checking-mode front door included, task #147)" }
  | "--infer-only" :: _, a =>
    { a with bad := some "--infer-only is retired; its discipline is part \
        of --trusted, and the certified mode is --verified \
        (default) (task #147)" }
  | "--pre" :: rest, a => parseArgs rest { a with pre := true }
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
    else if s.startsWith "--check-range=" then
      { a with bad := some "--check-range is retired; the split \
          install/check driver was arena machinery and went with the \
          interned representation (task #172)" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- The child's argument vector, reassembled from the parsed options. -/
def childArgs (a : Args) (file : String) : Array String :=
  #[file]
    -- Two modes, and `.verified` is the default, so it re-emits
    -- nothing.  (The dead R arm this replaced went with the
    -- constructor when `CheckMode` collapsed to two values.)
    ++ (match a.mode with
        | .verified => #[]
        | .trusted => #["--trusted"])
    ++ (if a.pre then #["--pre"] else #[])

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    return 0
  -- `--verified`/`--trusted`: the mode setting (task #147), validated
  -- here once and threaded as configuration.  Two cores since the R
  -- core's retirement (2026-09-05): the graded verified one and the
  -- unverified trusted one.
  -- `--pre`: the input is already-preprocessed `setlec-preprocess`
  -- output (explicit user assertion — the checker never sniffs input
  -- content for it); skips the `needsPreprocess` scan and the
  -- preprocessor spawn.
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"setlec: {msg}"
    IO.eprintln usage
    return 3
  let pre := a.pre
  match a.files.toList with
  | [file] =>
    -- OOM supervision: the Lean runtime's out-of-memory handler
    -- (`lean_internal_panic_out_of_memory`) prints "INTERNAL PANIC:
    -- out of memory" and calls `exit(1)` — not catchable in-process
    -- and indistinguishable from a *reject* at the exit-code level.
    -- Re-exec the checker as a supervised child and translate a
    -- panicking child (exit 1 with a panic marker on stderr) into
    -- exit 3 (error), per the arena convention that 1 means "invalid
    -- input proof".  Progress output streams through (stdout is
    -- inherited); stderr is buffered for inspection and re-printed.
    if (← IO.getEnv "SETLEC_SUPERVISED").isSome then
      checkMain file a.mode pre
    else
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := childArgs a file
        env := #[("SETLEC_SUPERVISED", some "1")]
        stdout := .inherit
        stderr := .piped }
      -- The child's stderr is STREAMED, line by line, rather than read
      -- to EOF and re-printed at the end (2026-09-07): a progress
      -- heartbeat that only appears once the run is over is not a
      -- heartbeat, and the same goes for the localisation lane's TRACE
      -- lines when the run dies without returning.  The panic marker is
      -- looked for on the way past, so the supervision below is
      -- unchanged.
      let errOut ← IO.getStderr
      let mut panicked := false
      repeat
        let line ← child.stderr.getLine
        if line.isEmpty then break
        errOut.putStr line
        errOut.flush
        if (line.splitOn "INTERNAL PANIC").length > 1 then panicked := true
      let code ← child.wait
      if code = 1 ∧ panicked then
        IO.eprintln "setlec: internal panic in the checker process"
        return 3
      return code
  | _ =>
    IO.eprintln usage
    return 3
