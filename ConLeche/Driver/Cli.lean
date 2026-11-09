module

public import ConLeche.Driver.Dispatch

@[expose] public section

/-!
Command-line driver: `con-leche FILE.ndjson` reads a **raw** lean4export
NDJSON file and checks the declarations in order.  There is no
preprocessor and no external dependency; no model is ever read from the
input.

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid.
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
* 3 — bad usage, malformed input, or an internal failure of unclear cause

A panic is none of these: `main` sets `LEAN_ABORT_ON_PANIC` (and
`LEAN_ABORT_ON_NONLINEAR`) before anything runs, so the runtime's out of
memory, a Lean-level `panic!`, and a copy of an array marked linear all
print their message on stderr and `abort()` — the process dies of
`SIGABRT` (status 134 in a shell), never with a code that reads as a
verdict.

**NO TEMPORARY FILES.**  The checker writes
nothing outside its own stdout/stderr, and reads its input strictly
forward, a chunk at a time (`Driver.parseStreamG`), so a
Mathlib-scale export never materialises anywhere — not on disk, and in
particular not in `/tmp`, which is commonly a RAM-backed tmpfs where a
multi-gigabyte scratch file would be charged to memory.  There is
nothing to clean up on any exit path.  The rule for anything that
*does* need scratch space — the test scripts, which gunzip fixtures —
is: honour `TMPDIR` if set, otherwise `./_tmp/tmp` (the project's
on-disk scratch convention); never default to the system temp
directory.

**This file and `Main.lean` are the CLI**: argument parsing, I/O, exit
codes; here everything generic in the IO class, `runArgs`, which the
main corollary lifted to the driver (`ConLeche.main_no_False`) is about,
in `Main.lean` the plumbing around it, followed by the exit.  The
proof-carrying driver — the parallel parse, the check loops and the
phase sequencing — lives in
`ConLeche/Driver/*` (`OwnerParse.lean`, `StreamParse.lean`,
`CheckPool.lean`, `Run.lean`, `CheckMain.lean`, `Dispatch.lean`).  The driver may import `ConLeche/Verify/*`
(the theorems about kernel functions that need no model) and nothing
else of the theory; `ConLeche/{Kernel,Cached,Frontend}/*` keep the full
fence. -/

namespace ConLeche.Driver

open ConLeche


/-- The progress heartbeat's pace, read off the `--progress[=N|P%|Ss]`
flag: every `N` declarations, per `P` percent of a phase, or at the first
one done after `S` seconds (`Pace`).  No flag is off; bare `--progress` is every
one.  A value of another form, and a zero — the flag asking for no heartbeat —
are usage errors (exit 3): a run's output must be readable off its
invocation, never silently degraded. -/
def progressPace (v : String) : Except String Pace :=
  let bad : Except String Pace := .error s!"--progress takes a number of declarations of at \
    least 1, a percentage from 1% to 100%, or seconds of at least 1s, got {Display.str v}; \
    omit the flag for no heartbeat"
  if v.endsWith "%" then
    match (v.dropEnd 1).toString.toNat? with
    | some p => if 1 ≤ p && p ≤ 100 then .ok (.percent p) else bad
    | none => bad
  else if v.endsWith "s" then
    match (v.dropEnd 1).toString.toNat? with
    | some 0 | none => bad
    | some s => .ok (.seconds s)
  else
    match v.toNat? with
    | some 0 | none => bad
    | some n => .ok (.every n)

/-- The worker count, read off the `--jobs=<n>` flag: a decimal numeral
of at least 1 (`1` is one worker, a worker THREAD all the same: see
`checkPool` for the heap the check phase must not allocate from).
`0` and a non-numeral are usage errors (exit 3).  Without the flag the
count is the machine's hardware thread count (`main`).

**Address space.**  The runtime reserves one gigabyte of ADDRESS
SPACE per thread it creates (a 1 GiB anonymous mapping per worker —
its stack reservation, lazily committed: the resident set grows by
about 25 MB per worker), so a run under an address-space limit
(`ulimit -v`) can only afford so many workers — about ten under
16 GB, four under 8 GB — and past that the thread creation fails and
the runtime aborts ("failed to create thread", exit 134).  Such a run
lowers the count with the flag; the shipped default is not shaped by
a development-environment limit, and the project's own gates run
under no address-space limit (only a `timeout`). -/
def jobsCount (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--jobs takes a worker count of at least 1 \
      (a decimal numeral); omit the flag for one worker per hardware thread"
  | some n => .ok n
  | none => .error s!"--jobs takes a worker count \
      (a decimal numeral of at least 1), got {Display.str v}"


/-- The numeral budget, read off the `--nat-max-size=<bytes>` flag: a
decimal byte count, the official kernel's `LEAN_NAT_MAX_SIZE` (the
largest `Nat` numeral the checker takes in or computes; a larger one
rejects the declaration).  A non-numeral is a usage error (exit 3).
Without the flag the budget is the official default, 128 MiB
(`Cached.natMaxSizeDefault`). -/
def natMaxSizeArg (v : String) : Except String Nat :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"--nat-max-size takes a byte count \
      (a decimal numeral), got {Display.str v}"

/-- The invocation forms, printed on their own when there are no arguments. -/
def synopsis : String := String.intercalate "\n" [
  "Usage:",
  "  con-leche [OPTIONS] [--] FILE.ndjson",
  "  con-leche [OPTIONS] --olean --search-path=DIRS [--] MODULE..."]

/-- The line after a usage error. -/
def tryHelp : String := "Try 'con-leche --help' for more information."

/-- The `--help` text. -/
def helpText : String := String.intercalate "\n" [
  "Check Lean declarations from a lean4export file or from .olean modules.",
  "",
  synopsis,
  "",
  "Options:",
  "  --verified          Check in the mode the soundness theorem covers (default)",
  "  --trusted           Skip the checks only the proof needs; outside the theorem",
  "  --jobs=N            Worker threads (default: one per hardware thread)",
  "  --nat-max-size=N    Largest Nat numeral in bytes the checker takes in or",
  "                      computes; a larger one is rejected (default 134217728)",
  "  --progress[=PACE]   Report progress on stderr: PACE is N declarations",
  "                      (default 1), P% of each phase, or Ss seconds",
  "  --help              Print this help and exit",
  "  --                  End of options",
  "",
  ".olean input:",
  "  --olean             Read modules and their import closure from .olean files",
  "  --search-path=DIRS  Colon-separated .olean directories; repeatable",
  "  --constant=NAME     Check only NAME and what it mentions; repeatable",
  "",
  "Exit status:",
  "  0  accepted",
  "  1  rejected: a declaration is invalid",
  "  2  declined: an unsupported feature",
  "  3  error: bad usage, malformed input or an internal failure",
  "",
  "Documentation:",
  "  https://github.com/leanprover/con-leche/blob/master/README.md",
  "  https://github.com/leanprover/con-leche/blob/master/OVERVIEW.md"]

structure Args where
  mode : ConLeche.CheckMode := .verified
  /-- The progress heartbeat's pace (`--progress[=N|P%|Ss]`); `.off` is
  "no flag given", i.e. no heartbeat. -/
  progress : Pace := .off
  /-- The check phase's worker count (`--jobs=<n>`); `none` is "no flag
  given": one worker per hardware thread. -/
  jobs : Option Nat := none
  /-- The numeral budget in bytes (`--nat-max-size=<n>`). -/
  natMax : Nat := Cached.natMaxSizeDefault
  /-- `--olean`: the positional arguments are root module names, read
  with their import closure from `.olean` files. -/
  olean : Bool := false
  /-- `--search-path=DIR:DIR…`: where `--olean` looks for the files. -/
  searchPath : List System.FilePath := []
  /-- `--constant=NAME`: with `--olean`, the constants to start from. -/
  constants : Array String := #[]
  files : Array String := #[]
  bad : Option String := none

/-- `--help` before any `--`: after a `--` every argument is a file,
whatever it is called. -/
def helpWanted (args : List String) : Bool :=
  (args.takeWhile (· != "--")).contains "--help"

/-- The value of a flag spelled `<prefix><value>`, where `s` starts with the prefix. -/
def flagValue (pre s : String) : Option String :=
  if pre.toList.isPrefixOf s.toList then some (String.ofList (s.toList.drop pre.toList.length))
  else none

/-- A `--search-path=` value: the directories, separated by `:`. -/
def searchPathOf (dirs : String) : List System.FilePath :=
  ((dirs.splitOn ":").filter (· != "")).map System.FilePath.mk

def parseArgs : List String → Args → Args
  | [], a => a
  -- The end of the options: every argument after it is a file, so
  -- `con-leche -- <file>` is safe for any file name.
  | "--" :: rest, a => { a with files := a.files ++ rest.toArray }
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  -- The progress heartbeat: a FLAG, in either order with
  -- `--verified`/`--trusted`, and independent of them — it turns on
  -- the heartbeat the ONE driver prints between the steps of its
  -- check phase (`checkPool`), which is the same driver, at the same
  -- mode, as a run without it.  Bare is every declaration;
  -- `--progress=<pace>` is the general form (below, with the other
  -- `=`-carrying spellings).
  | "--progress" :: rest, a => parseArgs rest { a with progress := .every 1 }
  | "--olean" :: rest, a => parseArgs rest { a with olean := true }
  | s :: rest, a =>
    if let some v := flagValue "--progress=" s then
      match progressPace v with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if let some v := flagValue "--jobs=" s then
      match jobsCount v with
      | .ok n => parseArgs rest { a with jobs := some n }
      | .error msg => { a with bad := some msg }
    else if let some v := flagValue "--nat-max-size=" s then
      match natMaxSizeArg v with
      | .ok n => parseArgs rest { a with natMax := n }
      | .error msg => { a with bad := some msg }
    else if s == "--jobs" then
      { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
          flag for one worker per hardware thread" }
    else if let some v := flagValue "--constant=" s then
      parseArgs rest { a with constants := a.constants.push v }
    else if let some v := flagValue "--search-path=" s then
      parseArgs rest { a with searchPath := a.searchPath ++ searchPathOf v }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {Display.str s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- An error line on stderr (`liftIO`). -/
@[inline] def eprintln {m : Type → Type} [CheckerIO m] (s : String) : m Unit :=
  CheckerIO.liftIO (IO.eprintln s)

/-- The constants `--constant=` names: `none` is every constant of the closure. -/
def Args.rootConstants (a : Args) : Option (Array Name) :=
  if a.constants.isEmpty then none else some (a.constants.filterMap Frontend.Olean.parseConstName)

/-- **What `main` runs, generic in the IO class** (tasks #424, #450): the
argument parse, `--help` and the usage errors, the request run, and the
catch of `IO` errors into exit 3.  It reaches the runtime through
`CheckerIO.liftIO`, and the exit code, the `UInt8` `IO.Process.exit`
takes, is computed here and returned outside `liftIO`, so that what the
model says of the code is what the run computed.  The binary's `main`
(`Main.lean`) is the plumbing around this at `IO`.

**An uncaught IO exception is an internal error, exit 3 — never a REJECT
(task #335).**  `IO.Error` can surface anywhere below: the input path
naming a directory, a read failing mid-stream, a write to stdout/stderr
failing (a closed pipe).  Left uncaught, it would reach the Lean
runtime's own top-level handler, which prints "uncaught exception: …"
and exits with status 1 — exactly the code the arena convention reserves
for a declaration *positively* rejected as invalid.  This `try` is the
one place that turns any such exception into exit 3 instead, and it is
here, not in `main`, so that the model sees it.  A verdict that is
deliberately exit 1 (`.invalid`) or exit 2 (`.notImplemented`) is a plain
`return` out of `runReq`, never a `throw`, so it passes through
untouched.  The catch handler's own write can itself fail (that same
closed stderr, say); that must not flip the exit code either, so it is
best-effort and its own failure is swallowed. -/
def runArgs {m : Type → Type} [CheckerIO m] (args : List String) : m UInt8 :=
  tryCatchThe IO.Error
    (do
      if helpWanted args then
        CheckerIO.liftIO (IO.println helpText)
        return 0
      -- `--verified`/`--trusted`: the mode setting, validated here once
      -- and threaded as configuration — the graded verified core and the
      -- unverified trusted one.
      let a := parseArgs args {}
      if let some msg := a.bad then
        eprintln s!"con-leche: {msg}"
        eprintln tryHelp
        return 3
      if a.olean then
        -- `--olean`: the arguments are root modules (`Init`, `Mathlib`),
        -- read with their import closure along the search path, module
        -- names as Lean spells them, `«»` escapes included.
        if a.files.isEmpty || a.searchPath.isEmpty then
          eprintln "con-leche: --olean takes one or more module names and a \
            --search-path=DIRS"
          eprintln tryHelp
          return 3
        if let some m := a.files.find? (fun f => (Frontend.Olean.parseModName f).isNone) then
          eprintln s!"con-leche: not a module name: {Display.str m}"
          eprintln tryHelp
          return 3
        if let some c := a.constants.find? (fun c => (Frontend.Olean.parseConstName c).isNone) then
          eprintln s!"con-leche: not a constant's name: {Display.str c}"
          eprintln tryHelp
          return 3
        let jobs := a.jobs.getD
          (let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
           if hw = 0 then 1 else hw)
        return ← runReq (.oleans a.searchPath (a.files.filterMap Frontend.Olean.parseModName)
          a.rootConstants a.mode a.natMax a.progress jobs)
      if !a.searchPath.isEmpty || !a.constants.isEmpty then
        eprintln "con-leche: --search-path and --constant take --olean"
        eprintln tryHelp
        return 3
      match a.files.toList with
      | [file] =>
        -- The checker runs IN THIS PROCESS: it spawns no copy of itself,
        -- and an out-of-memory condition is the Lean runtime's own panic
        -- ("INTERNAL PANIC: out of memory", uncatchable in process), an
        -- `abort()` under the `LEAN_ABORT_ON_PANIC` set by `main`.
        -- `--jobs=<n>`: the check phase's worker count; without the flag,
        -- one worker per hardware thread (1 if the runtime cannot tell).
        let jobs := a.jobs.getD
          (let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
           if hw = 0 then 1 else hw)
        runReq (.stream file a.mode a.natMax a.progress jobs)
      | [] =>
        eprintln synopsis
        eprintln tryHelp
        return 3
      | _ =>
        eprintln "con-leche: takes one input file"
        eprintln tryHelp
        return 3)
    fun e => do
      CheckerIO.liftIO
        (try IO.eprintln s!"con-leche: internal error: {e}" catch _ => pure ())
      return 3

end ConLeche.Driver
