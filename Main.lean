module

public import ConLeche.Driver.Run
public import Std.Async.System

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
forward, one `getLine` at a time (`Frontend.parseExportHandleD`), so a
Mathlib-scale export never materialises anywhere — not on disk, and in
particular not in `/tmp`, which is commonly a RAM-backed tmpfs where a
multi-gigabyte scratch file would be charged to memory.  There is
nothing to clean up on any exit path.  The rule for anything that
*does* need scratch space — the test scripts, which gunzip fixtures —
is: honour `TMPDIR` if set, otherwise `./_tmp/tmp` (the project's
on-disk scratch convention); never default to the system temp
directory.

**This file is the CLI only**: argument parsing, I/O, exit codes.  The
proof-carrying driver — the install and check loops and the phase
sequencing — lives in `ConLeche/Driver/*` (`CheckPool.lean`,
`Run.lean`).  The driver and this file may import `ConLeche/Verify/*`
(the theorems about kernel functions that need no model) and nothing
else of the theory; `ConLeche/{Kernel,Cached,Frontend}/*` keep the full
fence. -/

open ConLeche ConLeche.Driver

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
      (a decimal numeral of at least 1), got {repr v}"

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
      (a decimal numeral of at least 1), got {repr v}"


def usage : String := String.intercalate "\n" [
  "usage: con-leche [--verified|--trusted] [--jobs=<n>] [--progress[=<stride>]] FILE.ndjson",
  "       con-leche --help",
  "",
  "  --verified        the default, and the mode the main theorem is",
  "                    about: the graded model with the annotation-",
  "                    gated checks.  The validated-annotation beta",
  "                    gate skips per-redex argument certificates at",
  "                    provably non-Prop binders, and the io-graded",
  "                    knot skips the per-argument application",
  "                    certificate under the same licence; every other",
  "                    certificate family runs.  The theorem: a file",
  "                    that declares a theorem of type False is never",
  "                    accepted in this mode",
  "                    (ConLeche.no_False_declaration,",
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
  "  --jobs=<n>        the number of worker threads for the check phase",
  "                    (default: the machine's hardware thread count).",
  "                    The run has two phases: the INSTALL phase reads",
  "                    the records in order and installs every one of",
  "                    them in a single thread (a definition, theorem or",
  "                    opaque is annotated and pushed with its check",
  "                    recorded; everything else is checked in full as it",
  "                    is installed), and the CHECK phase checks every",
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
  "                    The install phase is never parallel: it is the",
  "                    parse and the fold's serial floor.  ADDRESS",
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
  "  --no-mark-persistent",
  "                    turn that mark off.  It changes no verdict --",
  "                    the marked graph is read-only from the boundary",
  "                    on -- so this is a MEASUREMENT switch: it is how",
  "                    the mark's effect is measured on the shipped",
  "                    binary.",
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
  "                    or after the other flags.",
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
  "  --help            print this text on STDOUT and exit 0, in any",
  "                    argument position; no input is read.",
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
  /-- `--no-mark-persistent`: do NOT mark the installed environment
  persistent at the phase boundary.  The mark is on by default whenever
  the check phase runs on the pool; this turns it off, which is what
  measures its effect on the shipped binary. -/
  noMark : Bool := false
  files : Array String := #[]
  bad : Option String := none

def parseArgs : List String → Args → Args
  | [], a => a
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  -- The progress heartbeat: a FLAG, in either order with
  -- `--verified`/`--trusted`, and independent of them — it turns on
  -- the heartbeat the ONE driver prints between the steps of its two
  -- phases (`installLoop`/`checkLoop`), which is the same driver, at
  -- the same mode, as a run without it.  Bare is stride 1;
  -- `--progress=<n>` is the general form (below, with the other
  -- `=`-carrying spellings).
  | "--progress" :: rest, a => parseArgs rest { a with progress := 1 }
  -- The persistent mark is on by default on the pool; this turns it off.
  | "--no-mark-persistent" :: rest, a => parseArgs rest { a with noMark := true }
  | s :: rest, a =>
    if s.startsWith "--progress=" then
      match progressStride ((s.drop "--progress=".length).toString) with
      | .ok n => parseArgs rest { a with progress := n }
      | .error msg => { a with bad := some msg }
    else if s.startsWith "--jobs=" then
      match jobsCount ((s.drop "--jobs=".length).toString) with
      | .ok n => parseArgs rest { a with jobs := some n }
      | .error msg => { a with bad := some msg }
    else if s == "--jobs" then
      { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
          flag for one worker per hardware thread" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- The argument parse and dispatch — everything `main` below does, up
to computing the exit code.  Split out (task #336) so that `main` can
wrap the whole thing in a flush-then-`exit`: see there for why. -/
def run (args : List String) : IO UInt32 := do
  -- **Linearity is enforced, in every run** (task #331).  The install
  -- environment's index and the parse tables are marked linear
  -- (`FEnv.markLinear`, `StateD.markLinear`); with
  -- `LEAN_ABORT_ON_NONLINEAR` set, a copy of a marked array is a runtime
  -- panic instead of a silent copy of a million-slot array, and with
  -- `LEAN_ABORT_ON_PANIC` set every panic — that one, a Lean-level
  -- `panic!`, an out-of-bounds `get!`, the runtime's out-of-memory —
  -- is an `abort()` (exit 134, SIGABRT), never an exit code that reads
  -- as a verdict.  The runtime reads both variables with `getenv` at the
  -- moment it needs them, so setting them here, before any thread is
  -- started, covers the whole run.
  try
    Std.Async.System.setEnvVar "LEAN_ABORT_ON_NONLINEAR" "1"
    Std.Async.System.setEnvVar "LEAN_ABORT_ON_PANIC" "1"
  catch e =>
    IO.eprintln s!"con-leche: cannot set the runtime's abort variables: {e}"
    return 3
  if args.contains "--help" then
    IO.println usage
    return 0
  -- `--verified`/`--trusted`: the mode setting, validated here once
  -- and threaded as configuration — the graded verified core and the
  -- unverified trusted one.
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"con-leche: {msg}"
    IO.eprintln usage
    return 3
  match a.files.toList with
  | [file] =>
    -- The checker runs IN THIS PROCESS: it spawns no copy of itself,
    -- and an out-of-memory condition is the Lean runtime's own panic
    -- ("INTERNAL PANIC: out of memory", uncatchable in process), an
    -- `abort()` under the `LEAN_ABORT_ON_PANIC` set above.
    -- `--jobs=<n>`: the check phase's worker count; without the flag,
    -- one worker per hardware thread (1 if the runtime cannot tell).
    let jobs := a.jobs.getD
      (let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
       if hw = 0 then 1 else hw)
    checkMain file a.mode a.progress jobs a.noMark
  | _ =>
    IO.eprintln usage
    return 3

/-- **The CLI entry point (task #336).**  `run` above computes the exit
code — the verdict line and the end-of-run summary (`--progress`) are
the LAST things it does on every path, immediately before its own
`return` — and this wrapper, instead of letting that code flow back
out of `main` and returning normally, flushes both streams and ends
the process right there with `IO.Process.exit`.

**Why**: returning normally lets the generated `main` wrapper run to
completion — `lean_finalize_task_manager` (harmless here: every
worker this driver spawns is already joined, via `IO.wait`, before
`checkMain` can return, so there is nothing left to join), and then,
as the `IO` value unwinds back through `checkMain`'s and `run`'s `do`
blocks to produce the final `UInt32`, the runtime drops every
still-live local along the way — the parsed declaration array, the
installed index's non-persistent parts, the pending-check table, the
parse's own tables — which on a 105 GB export is a multi-gigabyte
object graph and measured 200-570 s of wall time *after* the verdict
line was already on stdout (`DESIGN.md`, task #336).  `IO.Process.exit`
is `lean_io_exit`, which calls the C runtime's `exit()` directly:
`checkMain`'s and `run`'s frames are simply abandoned mid-unwind, nothing
above this call ever runs, and `exit()` only does what libc's own
teardown does — flush/close the C streams, run anything registered
with `atexit` (nothing in this binary registers any) — never the
dropped-local cascade above.  The exit codes are exactly `run`'s:
0/1/2/3, per `CheckError.exitCode` and the usage/declines above;
`UInt32.toUInt8` is the identity on all four.

**Flushing first**: `IO.Process.exit`'s own `exit()` call flushes the C
streams if `IO.FS.Stream.stdout`/`stderr` are backed by them, but this
does not depend on that — `run`'s last action on every path is already
the verdict/diagnostic print, so flushing both streams here, right
before `exit`, is flushing exactly what that print just wrote and
nothing more. -/
def main (args : List String) : IO UInt32 := do
  let code ← run args
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8
