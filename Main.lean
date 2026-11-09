module

public import ConLeche.Driver.Cli
public import Std.Async.System

@[expose] public section

/-!
The binary's entry point, all plumbing: `main` is the abort variables
(`enableAbortOnNonlinear`), then the generic `ConLeche.Driver.runArgs`
(`ConLeche/Driver/Cli.lean`, all the real logic) at `IO`, then the flush
and the exit.  These few lines are read, not proved: the theorems
(`Driver.runArgs_accept`, `ConLeche.main_no_False`) cover `runArgs` in the
model, and the exit takes the code `runArgs` returned.
-/

/-- **Linearity is enforced, in every run** (task #331).  The parse's
tables are marked linear (`StateD.markLinear`, on the serial parse's state
and on the state a rounds window falls back to; the rounds mark the arrays
they push onto); with `LEAN_ABORT_ON_NONLINEAR`
set, a copy of a marked array is a runtime panic instead of a silent
copy of a million-slot array, and with `LEAN_ABORT_ON_PANIC` set every
panic — that one, a Lean-level `panic!`, an out-of-bounds `get!`, the
runtime's out-of-memory — is an `abort()` (exit 134, SIGABRT), never an
exit code that reads as a verdict.  The runtime reads both variables with
`getenv` at the moment it needs them, so setting them here, before any
thread is started, covers the whole run. -/
def enableAbortOnNonlinear : IO Unit := do
  Std.Async.System.setEnvVar "LEAN_ABORT_ON_NONLINEAR" "1"
  Std.Async.System.setEnvVar "LEAN_ABORT_ON_PANIC" "1"

/-- **The flush** before the exit: both streams, so that what `runArgs`
printed last — the verdict or diagnostic line — is written out, and the
exit code: `code`, or 3 if the flush fails (task #490, issue #14).
`IO.Process.exit`'s own `exit()` call flushes the C streams if
`IO.FS.Stream.stdout`/`stderr` are backed by them, but `main` does not
depend on that.

**The flush failing**: the message, best-effort, and 3 whatever code
`runArgs` returned — an exception here would reach the runtime's
top-level handler, which exits 1, the code of a rejection, and a run
whose output did not get out has no verdict anyone read.  `runArgs`'
last action on every path is the verdict/diagnostic print, so the flush
writes exactly what that print wrote; a failing stdout mostly fails at
that print already (exit 3 from `runArgs`: `/dev/full`, a closed
stdout), but a buffered write can fail only here. -/
def flushStdoutStderr (code : UInt8) : IO UInt8 := do
  try
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    pure code
  catch e =>
    try IO.eprintln s!"con-leche: cannot write the output: {e}" catch _ => pure ()
    pure 3

/-- **The CLI entry point (task #336).**  `runArgs` computes the exit
code — the verdict line and the end-of-run summary (`--progress`) are
the LAST things it prints on every path, and no worker is left running
(`checkDeclsIO` waits for the ones it starts); `main` flushes both streams
(`flushStdoutStderr`, 3 if that fails) and ends the process right there
with `IO.Process.exit`, instead of letting that code flow back out of
`main` and returning normally.

**The abort variables failing**: the message and exit 3, not an
exception, which the runtime's top-level handler would turn into exit 1,
the code of a rejection; the message's own write is best-effort for the
same reason.

**Why the exit**: returning normally lets the generated `main` wrapper run to
completion — `lean_finalize_task_manager` (which joins the runtime's
threads: both pools' are joined, via `IO.wait`, before
`checkDeclsIO` returns),
and then,
as the `IO` value unwinds back through the `do` blocks to produce the
exit code, the runtime drops every
still-live local along the way — the check phase's result table, the
parse's own tables — which on a 105 GB export is a multi-gigabyte
object graph and measured 200-570 s of wall time *after* the verdict
line was already on stdout (`DESIGN.md`, task #336).  `IO.Process.exit`
is `lean_io_exit`, which calls the C runtime's `exit()` directly:
the frames are simply abandoned mid-unwind, nothing
above this call ever runs, and `exit()` only does what libc's own
teardown does — flush/close the C streams, run anything registered
with `atexit` (nothing in this binary registers any) — never the
dropped-local cascade above.  The exit codes are exactly `runArgs`':
0/1/2/3, per `CheckError.exitCode` and the usage/declines there: a
`UInt8` from the generic code on, the type `IO.Process.exit` takes, so
no conversion stands between the code the theorems speak of and the
exit status, and `main` itself is at `IO Unit`.

**Composes with task #335's own top-level `try`** (inside `runArgs`): that
`try` already turns every uncaught `IO.Error` into a `return 3`, so
`runArgs` itself never throws, and every path, verdict or internal error
alike, reaches this same flush-then-exit. -/
def main (args : List String) : IO Unit := do
  try
    enableAbortOnNonlinear
  catch e =>
    try IO.eprintln s!"con-leche: cannot set the runtime's abort variables: {e}" catch _ => pure ()
    IO.Process.exit 3
  let code ← ConLeche.Driver.runArgs args
  let code ← flushStdoutStderr code
  IO.Process.exit code
