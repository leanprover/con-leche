module

public import ConLeche.Driver.Dispatch

@[expose] public section

/-!
Command-line driver: `con-leche FILE.ndjson` reads a **raw** lean4export
NDJSON file and checks the declarations in order.  There is no
preprocessor and no external dependency: every inductive block is
installed by the uniform installer; no model is ever read from the
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
proof-carrying driver — the parallel parse, the install and check
loops and the phase sequencing — lives in
`ConLeche/Driver/*` (`OwnerParse.lean`, `StreamParse.lean`,
`CheckPool.lean`, `ParInstall.lean`, `Run.lean`, `CheckMain.lean`,
`Dispatch.lean`).  The driver may import `ConLeche/Verify/*`
(the theorems about kernel functions that need no model) and nothing
else of the theory; `ConLeche/{Kernel,Cached,Frontend}/*` keep the full
fence. -/

namespace ConLeche.Driver

open ConLeche


/-- The progress heartbeat's stride, read off the `--progress[=<stride>]`
flag.  No flag is off; bare `--progress` is stride 1.  A value that is
not a decimal numeral, and `0` — the flag asking for no heartbeat —
are usage errors (exit 3): a run's output must be readable off its
invocation, never silently degraded. -/
def progressStride (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--progress takes a declaration stride of at least 1 \
      (a decimal numeral); omit the flag for no heartbeat"
  | some n => .ok n
  | none => .error s!"--progress takes a declaration stride \
      (a decimal numeral of at least 1), got {Display.str v}"

/-- The worker count, read off the `--jobs=<n>` flag: a decimal numeral
of at least 1 (`1` is the sequential lane — one worker, no shared
counter and no result table, but a worker THREAD all the same: see
`checkDeclsIO` for the heap the check phase must not allocate from).
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


def usage : String := String.intercalate "\n" [
  "usage: con-leche [--verified|--trusted] [--jobs=<n>] [--progress[=<stride>]] [--] FILE.ndjson",
  "       con-leche [flags] --olean --search-path=DIR[:DIR...] [--] MODULE...",
  "       con-leche --help",
  "",
  "  --verified        the default, and the mode the main theorem is",
  "                    about.  Beyond the official kernel's checks it",
  "                    runs the work the soundness proof consumes: the",
  "                    bodies' types compared at the innermost level of",
  "                    a lambda/lambda comparison and at the eta rule,",
  "                    the projection certificate and the certificate",
  "                    families (iota's case 3, the K and And rescues).",
  "                    Internal inference is the official",
  "                    kernel's infer_only.  The theorem: a file that",
  "                    declares a theorem of type False is never",
  "                    accepted in this mode (no_False_declaration,",
  "                    ConLeche/MainTheorem.lean)",
  "  --trusted         the unverified mode: the SAME checker bodies as",
  "                    --verified, instantiated at the mode with the",
  "                    certification-only work switched off (the",
  "                    verifiedChecks mode function false):",
  "                    the lambda/lambda and eta body-type comparisons,",
  "                    the projection certificate and the certificate",
  "                    families (at iota's case 3 the level, parameter",
  "                    and index comparisons and the telescope",
  "                    certificate; the K and And rescues' proof",
  "                    checks) are",
  "                    omitted; every official check stays.  Everything",
  "                    believed necessary for SOUNDNESS stays, which is",
  "                    not the same as necessary for the soundness proof",
  "                    to go through: an accept in this mode is outside",
  "                    the theorem.  The mode is never optimized on its",
  "                    own — it is the verified mode with certain steps",
  "                    omitted",
  "  --jobs=<n>        the number of worker threads (default: the",
  "                    machine's hardware thread count).",
  "                    At <n> > 1 the PARSE runs on <n> owner threads,",
  "                    a window of chunks of whole lines at a time;",
  "                    its result is the one-thread parse's, and a",
  "                    window it cannot take is parsed serially.",
  "                    The run has two phases: the INSTALL phase",
  "                    installs the records in stream order (a",
  "                    definition or opaque passes the syntactic",
  "                    guards of its type and value, a theorem those",
  "                    of its type, and each is pushed with its check",
  "                    recorded; everything else",
  "                    is checked in full as it is installed).  At",
  "                    <n> > 1 the records are installed on <n> worker",
  "                    threads, each against a view of the records",
  "                    before it, while the main thread commits them in",
  "                    stream order (and installs any record it reaches",
  "                    before a worker has): the installed environment",
  "                    is the one-thread install's at every <n>.  The",
  "                    CHECK phase checks every",
  "                    recorded declaration against the prefix of the",
  "                    installed environment it was installed at, from a",
  "                    fresh memo state.  The recorded checks are",
  "                    independent of one another, so the check phase",
  "                    runs on <n> threads: long-lived workers claim",
  "                    one record at a time off one shared counter, so",
  "                    that a cluster of heavy declarations is spread",
  "                    over the pool, and the results are merged by record",
  "                    index and walked in record order, so the verdict",
  "                    -- and the declaration a rejection names, the",
  "                    first failing one in fold order -- is the same at",
  "                    every <n>.  Without the flag <n> is the machine's",
  "                    hardware thread count; --jobs=1 runs ONE worker",
  "                    with no shared counter and no result table (the",
  "                    sequential lane a measurement is made on), but",
  "                    it is still a worker THREAD: the check phase",
  "                    allocates its per-record memo state out of the",
  "                    running thread's heap, and the main thread's",
  "                    heap is the one parse and install have just",
  "                    fragmented, which at Mathlib scale costs the",
  "                    lane a factor of two in wall time at the same",
  "                    instruction count.  0 or a non-numeral is a",
  "                    usage error.",
  "                    At --jobs=1 the parse and the install phase run",
  "                    in the main thread alone.  ADDRESS",
  "                    SPACE: each worker thread reserves about 1 GiB",
  "                    of address space (its stack reservation, lazily",
  "                    committed; the resident set grows by about",
  "                    25 MB per worker), so a run under an address-",
  "                    space limit (ulimit -v) must lower the count to",
  "                    what the limit affords -- about ten workers",
  "                    under 16 GB, four under 8 GB; past it the",
  "                    runtime cannot create the thread and aborts",
  "                    ('failed to create thread', exit 134).",
  "                    The installed environment is marked PERSISTENT",
  "                    once at the phase boundary, at every <n>: it is",
  "                    read-only from there on, and the mark removes",
  "                    the atomic reference counting the workers would",
  "                    otherwise pay on every object of it -- worth",
  "                    18-32 % of wall time on the pool, growing with",
  "                    <n>, and 3.5 % at <n> = 1.",
  "  --progress[=<stride>]",
  "                    opt-in progress heartbeat on STDERR, one line",
  "                    shape per phase:",
  "                      con-leche: parse done: <N> fold records ... t=<s>s",
  "                      con-leche: install <i>/<N> <decl> t=<s>s",
  "                      con-leche: install done: <N>/<N> ..., <M> checks pending t=<s>s",
  "                      con-leche: check <done>/<M> <decl> t=<s>s",
  "                      con-leche: check done: <M>/<M> t=<s>s",
  "                      con-leche: done: parse <p>s, install <i>s, check <c>s, <n> workers",
  "                    An install line is printed BEFORE every",
  "                    <stride>-th declaration is installed (<i> is its",
  "                    FOLD position, which the stream's record index",
  "                    sits near but not at a fixed offset above), so a",
  "                    run that dies in the install phase names the",
  "                    declaration it died in on its last line.  A check",
  "                    line is printed AFTER every <stride>-th COMPLETED",
  "                    check: <done> counts completed checks -- in the",
  "                    pool, from whichever worker finished, monotone --",
  "                    and <decl> is the one just completed; <M>, the",
  "                    number of recorded checks, is below <N>.  t= is",
  "                    the time since the run started, so a declaration",
  "                    that sits for minutes is visible as a gap between",
  "                    two lines.  On a failure the phase's closing line",
  "                    says so ('install failed at', 'check failed at')",
  "                    and the summary still prints.  Bare --progress is",
  "                    stride 1 (every declaration announced, every",
  "                    check reported).  Without the flag there is no",
  "                    heartbeat; a stride that is not a decimal numeral,",
  "                    or 0, is a usage error.  The flag may come before",
  "                    or after the other flags.  On more than one",
  "                    worker an install or check line ends with",
  "                    'busy=<b>/<n>, oldest <decl> <age>s': how many",
  "                    workers are on a record, and the one running",
  "                    longest.",
  "",
  "                    The heartbeat is printed by the ONE driver: it",
  "                    installs every record, then checks every recorded",
  "                    declaration -- in one thread or on the pool --",
  "                    and returns its environment with the proof that",
  "                    checkDecls (the function the main theorem",
  "                    ConLeche.model_exists is about) returns it;",
  "                    what it prints in between does not touch that",
  "                    type, so a run with the flag is covered exactly",
  "                    as a run without it, and so is a run on the pool.",
  "  --                the end of the options: every argument after it",
  "                    is a file, whatever it is called.",
  "  --olean           read the input from .olean files instead of a",
  "                    lean4export stream: the arguments are root",
  "                    modules (Init, Std, Mathlib, ...; a component in",
  "                    «» is taken literally, as in Challenge.«12.34».«5»),",
  "                    checked with every constant of their import closure.  The",
  "                    closure is read at the private level (theorems",
  "                    with proofs, definitions with bodies), merged as",
  "                    Lean's own import merges it, and emitted as the",
  "                    records lean4export would write, so the same",
  "                    checker checks them.  Every object read is",
  "                    validated, nothing in the files is trusted; a",
  "                    theorem's proof is read when its check needs it.  A",
  "                    file of another .olean format version declines (2).",
  "  --constant=NAME   with --olean: check only this constant and what it",
  "                    mentions, not every constant of the closure, as",
  "                    lean4export's arguments after -- do; a component of",
  "                    digits is a number (_private.M.0.foo).  May be given",
  "                    more than once.  A name the closure does not hold is",
  "                    an error (3).",
  "  --search-path=DIR[:DIR...]",
  "                    the directories holding .olean trees, as",
  "                    LEAN_PATH lists them (the toolchain's lib/lean,",
  "                    a package's .lake/build/lib/lean).  May be",
  "                    given more than once.  Every module is looked",
  "                    up in every directory: its files (M.olean and,",
  "                    for a module of the module system, exactly",
  "                    M.olean.server and M.olean.private beside it)",
  "                    must be in one directory, counted once however",
  "                    often it is reached (a repeated entry, a",
  "                    symbolic link).  A module in two places, a",
  "                    missing, stray or split part is an error (3).",
  "  --help            print this text on STDOUT and exit 0, in any",
  "                    argument position before a --; no input is read.",
  "",
  "STATISTICS.  Every run, flag or not, ends its STDERR with a few",
  "'con-leche: stats:' lines: the phase times; for the install and the",
  "check phase the wall time, workers, busy time and utilisation (busy /",
  "(workers x wall)) and, on more than one worker, the tail after the",
  "last record started; the five slowest installs and checks with their",
  "fold positions (#<i>); the peak resident set.  They change neither",
  "STDOUT nor the exit code.",
  "",
  "THE VERDICT LINE'S COUNT.  It counts the FILE's accepted",
  "declaration RECORDS: one per def/theorem/opaque/axiom/inductive/quot",
  "record the file declares.  The built-in prelude's own records are not",
  "counted; a stream record dropped as an identical copy of a prelude",
  "record IS counted (it is installed, from the prelude).  That count is",
  "a property of the INPUT.  The",
  "number of environment CONSTANTS is not: an inductive record installs",
  "several constants (type former, constructors, recursor, projection",
  "table), so it moves when the representation moves.  NB the official",
  "kernel's 'Accepted N declarations' is a THIRD unit — its parsed",
  "constMap, where an inductive record counts as its members — also a",
  "function of the file, just a larger one; scripts/stream-census.py",
  "derives every one of these numbers from a stream.",
  "",

  "THE sorryAx AXIOM.  An export declares sorryAx whenever the module",
  "it came from mentions sorry, whether or not anything uses it, so a",
  "stream that merely DECLARES it is accepted: the record is checked",
  "for well-formedness and installs NOTHING (there is no set model for",
  "it).  Any USE of the name -- in a declaration's type or value, or in",
  "an inductive member's -- DECLINES the run (exit 2) at the record",
  "that uses it, naming the slot.  The fold owns that decision: the",
  "parse forwards every record, sorryAx's included.  Every other",
  "non-pinned axiom declines at its own record.",
  "",

  "THE BUILT-IN PRELUDE.  Every run installs, first and",
  "unconditionally, the checker's own little prelude — the five pinned",
  "basis blocks (Eq, Nat, Empty, False, Quot) and the toolchain's",
  "Bool and And blocks (pins/<toolchain>.prelude.ndjson, embedded at",
  "build time; ConLeche/Frontend/Prelude.lean) — so the pin-certified",
  "Nat operations find their ground whatever order the export chose.  A",
  "stream's own copy of a prelude declaration is dropped when it is the",
  "same declaration, and the fold DECLINES the run (exit 2, naming it)",
  "when it differs; a mismatching basis block still REJECTS (reserved",
  "name), as before.  A pinned operation's stream-certified structural",
  "ground (Nat.ble, Nat.sub, Nat.mul — spelled into the certificate",
  "statements, not reachable from the operation's own value) is HOISTED",
  "ahead of the operation when the stream declares it later",
  "(ConLeche/Frontend/NatOpGround.lean): a dependency-closed reorder.",
  "All of this is preparePrelude (ConLeche/Frontend/Prepare.lean), one",
  "pure total function from the file's records to the fold's input; the",
  "parse itself only decodes, and the main theorem is about the fold",
  "over prelude ++ stream.",
  "",
  "NO PREPROCESSOR, NO MODELS.  The input is a RAW lean4export",
  "stream: there is no external tool, no dependency and no spawn.",
  "Every inductive block -- structures, sums, indexed families,",
  "recursive, reflexive, mutual and nested blocks -- is installed by",
  "the ONE uniform installer (ConLeche/Kernel/Inductives/",
  "BlockInstall.lean): it checks the type formers and constructors,",
  "runs the positivity check, and GENERATES the block's recursors;",
  "the stream's recursor records supply only their types, compared",
  "with the generated ones up to definitional equality, and their",
  "classes -- the rule bodies the stream carries are ignored.",
  "No model is ever read from the input: a stream record whose name",
  "carries a `_model` component is an ordinary declaration with no",
  "effect on any block.  A block whose shape the installer does not",
  "recognise declines (exit 2), naming it.",
  "",
  "There is ONE core at two modes and one parse: the verified mode",
  "(--verified, the default) and the unverified trusted mode",
  "(--trusted).  The stream is read directly to the cached",
  "representation and checked by the one driver, which returns its",
  "environment together with the proof that the fold checkDecls — the",
  "function the main theorem ConLeche.model_exists",
  "(ConLeche/MainTheorem.lean) is stated on — returns it."]

structure Args where
  mode : ConLeche.CheckMode := .verified
  /-- The progress heartbeat's stride (`--progress[=<stride>]`); `0`
  is "no flag given", i.e. no heartbeat. -/
  progress : Nat := 0
  /-- The check phase's worker count (`--jobs=<n>`); `none` is "no flag
  given": one worker per hardware thread. -/
  jobs : Option Nat := none
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
  -- the heartbeat the ONE driver prints between the steps of its two
  -- phases (`installLoop`/`checkPool`), which is the same driver, at
  -- the same mode, as a run without it.  Bare is stride 1;
  -- `--progress=<n>` is the general form (below, with the other
  -- `=`-carrying spellings).
  | "--progress" :: rest, a => parseArgs rest { a with progress := 1 }
  | "--olean" :: rest, a => parseArgs rest { a with olean := true }
  | s :: rest, a =>
    if let some v := flagValue "--progress=" s then
      match progressStride v with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if let some v := flagValue "--jobs=" s then
      match jobsCount v with
      | .ok n => parseArgs rest { a with jobs := some n }
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
        CheckerIO.liftIO (IO.println usage)
        return 0
      -- `--verified`/`--trusted`: the mode setting, validated here once
      -- and threaded as configuration — the graded verified core and the
      -- unverified trusted one.
      let a := parseArgs args {}
      if let some msg := a.bad then
        eprintln s!"con-leche: {msg}"
        eprintln usage
        return 3
      if a.olean then
        -- `--olean`: the arguments are root modules (`Init`, `Mathlib`),
        -- read with their import closure along the search path, module
        -- names as Lean spells them, `«»` escapes included.
        if a.files.isEmpty || a.searchPath.isEmpty then
          eprintln "con-leche: --olean takes one or more module names and a \
            --search-path=DIR[:DIR…]"
          eprintln usage
          return 3
        if let some m := a.files.find? (fun f => (Frontend.Olean.parseModName f).isNone) then
          eprintln s!"con-leche: not a module name: {Display.str m}"
          eprintln usage
          return 3
        if let some c := a.constants.find? (fun c => (Frontend.Olean.parseConstName c).isNone) then
          eprintln s!"con-leche: not a constant's name: {Display.str c}"
          eprintln usage
          return 3
        let jobs := a.jobs.getD
          (let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
           if hw = 0 then 1 else hw)
        return ← runReq (.oleans a.searchPath (a.files.filterMap Frontend.Olean.parseModName)
          a.rootConstants a.mode a.progress jobs)
      if !a.searchPath.isEmpty || !a.constants.isEmpty then
        eprintln "con-leche: --search-path and --constant take --olean"
        eprintln usage
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
        runReq (.stream file a.mode a.progress jobs)
      | _ =>
        eprintln usage
        return 3)
    fun e => do
      CheckerIO.liftIO
        (try IO.eprintln s!"con-leche: internal error: {e}" catch _ => pure ())
      return 3

end ConLeche.Driver
