module

public import ConLeche.Driver.CheckMain

/-!
# What a run does, by its request, generic in the IO class (task #424)

`run` (`ConLeche/Driver/Cli.lean`) reads its arguments into a request (`Req`): today
a lean4export stream.  `runReq` runs the request's driver,
`checkMainG`, generic in the IO class: the binary runs it at `IO`
(`ConLeche/Driver/Cli.lean`, `Main.lean`), and `mainG_accept`
(`ConLeche/Verify/Driver/Main.lean`) is about the whole run in the
model, at the arguments `-- <file>`.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche

/-- **A run's request**: the driver and its configuration. -/
inductive Req where
  /-- a lean4export stream (`checkMainG` on `.ndjson`) -/
  | stream (file : String) (mode : CheckMode) (stride jobs : Nat) (noMark : Bool)

/-- **A request run** by its driver.  `drain` is where the install
leaves the join of its stopped workers, for `main` to run before the
exit. -/
def runReq {μ : Type → Type} [CheckerIO μ] (drain : Drain) : Req → μ UInt32
  | .stream file mode stride jobs noMark => checkMainG (.ndjson file) mode stride jobs noMark drain

end ConLeche.Driver
