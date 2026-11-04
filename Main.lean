module

public import ConLeche.Driver.Cli

@[expose] public section

/-!
The binary's entry point: `ConLeche.Driver.mainG`
(`ConLeche/Driver/Cli.lean`, the command line and the run, generic in
the IO class) at `IO`, followed by the exit.  The theorems over `main`
(`ConLeche.main_model`, `ConLeche.main_no_False`) are about `mainG` in
the model; the exit takes the code `mainG` returned.
-/

/-- **The CLI entry point (task #336).**  `mainG` computes the exit
code — the verdict line and the end-of-run summary (`--progress`) are
the LAST things it prints on every path — and flushes both streams;
this ends the process right there
with `IO.Process.exit`, instead of letting that code flow back out of
`main` and returning normally.

**Why**: returning normally lets the generated `main` wrapper run to
completion — `lean_finalize_task_manager` (which joins the runtime's
threads: both pools' are joined, via `IO.wait`, before
`checkDeclsIO` returns),
and then,
as the `IO` value unwinds back through the `do` blocks to produce the
exit code, the runtime drops every
still-live local along the way — the parsed declaration array, the
installed index's non-persistent parts, the pending-check table, the
parse's own tables — which on a 105 GB export is a multi-gigabyte
object graph and measured 200-570 s of wall time *after* the verdict
line was already on stdout (`DESIGN.md`, task #336).  `IO.Process.exit`
is `lean_io_exit`, which calls the C runtime's `exit()` directly:
the frames are simply abandoned mid-unwind, nothing
above this call ever runs, and `exit()` only does what libc's own
teardown does — flush/close the C streams, run anything registered
with `atexit` (nothing in this binary registers any) — never the
dropped-local cascade above.  The exit codes are exactly `run`'s:
0/1/2/3, per `CheckError.exitCode` and the usage/declines above: a
`UInt8` from the generic code on, the type `IO.Process.exit` takes, so
no conversion stands between the code the theorems speak of and the
exit status, and `main` itself is at `IO Unit`.

**Composes with task #335's own top-level `try`** (inside `run`): that
`try` already turns every uncaught `IO.Error` into a `return 3`, so
`run` itself never throws, and every path, verdict or internal error
alike, reaches this same flush-then-exit. -/
def main (args : List String) : IO Unit := do
  IO.Process.exit (← ConLeche.Driver.mainG args)
