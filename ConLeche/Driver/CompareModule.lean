module

public import ConLeche.Driver.Worker
public import ConLeche.Driver.Graph

@[expose] public section

/-!
# The compare worker: a challenge as one more module of a modular run (tasks #608, #619)

`con-leche --olean --module --compare [--trusted-search-path=T] --search-path=DIRS -- C S` is the
worker of the challenge `C` in a modular run over the closures of `C` and of its solution `S`
(`--check-graph --compare`, `--schedule --compare`): the worker of `C` (`checkModuleG`) with
`import all S` added to `C`'s header (`Graph.solutionImport`), every module read through the
trusted path, then the search path.  It loads what Lean loads for a module importing both `C`'s
imports and the whole of `S`, under Lean's clash rule over every loaded name.  A record of `C` some
name of which a loaded module stores is a copy of that constant (`copyRecs`, `copyCheck`): a hole
of `C` (an axiom, a definition or opaque constant whose value uses `sorryAx`) or a theorem of `C`,
of the loaded constant's statement up to the names of its level parameters; its names are read
from the loads into the context, as any name `C` imports.  Every other record of `C` is its own,
checked against that context as any worker checks its module's.  So `C`'s holes are justified by
the solution's checked constants, and a name a hole's statement reads means one constant on both
sides: there is one context.

The graph check reads the challenge's closure through the trusted path alone (a module of it only
the search path holds is invalid input, as in `--olean --compare`).

Exit 0 needs every phase; the accept lists the copies, each with the module and the kind of the
constant it is a copy of.
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **The challenge's closure through the trusted path alone** (`--trusted-search-path`, its
verdict only): where a module of it is not there, the line saying so and the exit code (1 where
the search path holds it, as in `--olean --compare`); none where the walk succeeds or no trusted
path is given. -/
def chalWalk {μ : Type → Type} [CheckerIO μ] (r : CmpReq) (jobs : Nat) :
    μ (Option (String × UInt8)) := do
  if r.trusted.isEmpty then return none
  match ← Graph.graphOf r.chalRoots [r.challenge] jobs with
  | .ok _ => return none
  | .error e =>
    match ← fallbackOnly r with
    | some why => return some (s!"con-leche: graph: {why}", 1)
    | none => return some (s!"con-leche: graph: {e}", e.exitCode)

/-- **The compare worker** (see the module docstring), generic in the IO class: the challenge's
closure walked through the trusted path alone (`pre`, `chalWalk`), then the worker of `C` with the
solution `S` added to its header, every read through `rd`. -/
def checkCmpModuleG {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (sp : Roots) (C S : Name)
    (pre : μ (Option (String × UInt8))) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace)
    (jobs : Nat) (alone : Bool := true) : μ UInt8 := do
  match ← pre with
  | some (line, c) =>
    diagLine line
    return c
  | none => checkModuleG rd sp C mode maxNatSize pace jobs alone #[Graph.solutionImport S]

/-- **The graph check of a compared run** (`--check-graph --compare`), generic in the IO class:
with a trusted path, the challenge's closure first, through the challenge's lookup alone
(`chalWalk`); then the graph of both closures through the solution's lookup, the solution added to
the challenge's header (`Graph.checkGraphG`). -/
def checkGraphCmpG {μ : Type → Type} [CheckerIO μ] (r : CmpReq) (jobs : Nat) : μ UInt8 := do
  match ← chalWalk r jobs with
  | some (line, c) =>
    diagLine line
    pure c
  | none =>
    Graph.checkGraphG r.solRoots [r.challenge] jobs (Graph.cmpExtra r.challenge r.solution)

end ConLeche.Driver
