module

public import ConLeche.Driver.CheckMain

/-!
# What a run does, by its request, generic in the IO class (task #424)

`runArgs` (`ConLeche/Driver/Cli.lean`) reads its arguments into a request (`Req`): a
lean4export stream, or the import closure of root modules from their `.olean` files.  `runReq` runs the request's driver,
`checkMainG`, generic in the IO class: the binary runs it at `IO`
(`ConLeche/Driver/Cli.lean`, `Main.lean`), and `runArgs_accept`
(`ConLeche/Verify/Driver/Main.lean`) is about the whole run in the
model, at the arguments `-- <file>`.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche

/-- **A run's request**: the driver and its configuration. -/
inductive Req where
  /-- a lean4export stream (`checkMainG` on `.ndjson`) -/
  | stream (file : String) (mode : CheckMode) (budget : Nat) (pace : Pace) (jobs : Nat)
  /-- the import closure of root modules (`checkMainG` on `.oleans`) -/
  | oleans (searchPath : List System.FilePath) (roots : Array Name)
      (constants : Option (Array Name)) (mode : CheckMode) (budget : Nat) (pace : Pace) (jobs : Nat)

/-- **A request run** by its driver. -/
def runReq {μ : Type → Type} [CheckerIO μ] : Req → μ UInt8
  | .stream file mode budget pace jobs => checkMainG (.ndjson file) mode budget pace jobs
  | .oleans sp roots cs mode budget pace jobs =>
    checkMainG (.oleans sp roots cs) mode budget pace jobs

end ConLeche.Driver
