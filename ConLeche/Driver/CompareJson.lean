module

public import ConLeche.Driver.Compare
import ConLeche.Verify.Cached.DeclNames
public import ConLeche.Verify.Cached.Justify

@[expose] public section

/-!
# Checking a lean4export file with a sidecar

`con-leche --compare [--] CHALLENGE.ndjson SOLUTION.ndjson` checks `CHALLENGE.ndjson`, justifying
its axioms by `SOLUTION.ndjson`: the solution's file is checked as any input is, and its
environment is the **sidecar** of the challenge's check (`checkDecls … (some envS)`,
`ConLeche/Cached/Justify.lean`).  The challenge's file is checked as any input is, its definitions,
theorems and inductive types included; only its axioms other than the built-in ones, and its
declarations whose value uses `sorryAx` (the holes: a definition's is read as the axiom of its
statement, `sideRecord`), take the justification route: the sidecar holds a constant of the same
name and type, up to the names of its level parameters, and everything the type reads is the
same constant in both.  An axiom the sidecar does not justify is a rejection, exit 1, with the
reason.

So a challenge `def f : Nat := 3`, `theorem t : f = 5 := sorry` has no accepted solution: `t`'s
type reads `f`, so the sidecar must hold `t` over the same `f := 3`, which it cannot prove.
-/

namespace ConLeche.Driver

open ConLeche

/-- **A run of a lean4export file with a sidecar**: the challenge's file and the solution's. -/
structure JCmpReq where
  challenge : String
  solution : String

/-- **The run** (see the module docstring): the solution's file checked, then the challenge's
with the solution's environment as its sidecar. -/
def compareJsonG {μ : Type → Type} [CheckerIO μ] (r : JCmpReq) (mode : CheckMode)
    (maxNatSize : Nat) (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let prelude ← match Frontend.builtinPreludeE with
    | .ok p => pure p
    | .error (_, line) =>
      diagLine s!"con-leche: the built-in prelude does not parse (line {line}); regenerate it \
        with `lake exe natop-pins-export` ({modeTag})"
      return 3
  CheckerIO.liftIO (readStarts pace r.challenge)
  match ← parseStreamG r.challenge jobs with
  | .error e => readFailed modeTag r.challenge e
  | .ok rC =>
  CheckerIO.liftIO (readStarts pace r.solution)
  match ← parseStreamG r.solution jobs with
  | .error e => readFailed modeTag r.solution e
  | .ok rS =>
  -- the sidecar, checked as any input
  let ⟨recsS, _, hoistedS⟩ := Frontend.prepareD prelude rS.decls
  hoistedNote hoistedS
  let tIndex ← clockMs
  let JS ← CheckerIO.liftIO (Jobs.build recsS)
  let tParse ← clockMs
  let vS ← CheckerIO.liftIO do
    checkDeclsIO mode maxNatSize (← IO.getStderr) pace t0 tIndex tParse jobs JS rfl
  match vS with
  | .error e =>
    verdictG modeTag rS.decls.size t0 recsS (.error e) s!"the sidecar {r.solution}: "
  | .ok _ =>
  -- the challenge, checked with the sidecar
  let envS := streamEnv recsS.toList
  let ⟨recsC₀, _, hoistedC⟩ := Frontend.prepareD prelude rC.decls
  hoistedNote hoistedC
  let recsC := Cached.sideRecords (some envS) recsC₀
  let tIndexC ← clockMs
  let JC ← CheckerIO.liftIO (Jobs.build recsC (some envS))
  let tParseC ← clockMs
  let vC ← CheckerIO.liftIO do
    checkDeclsIO mode maxNatSize (← IO.getStderr) pace t0 tIndexC tParseC jobs JC
      (Cached.sideRecords_idem _ _)
  match vC with
  | .error e => verdictG modeTag rC.decls.size t0 recsC (.error e)
  | .ok _ =>
    -- the justified records, labelled as the challenge declares them
    let holes := recsC₀.filter fun d => (Cached.justifiable (Cached.sideRecord d)).isSome
    outLine s!"con-leche: accepted {rC.decls.size} declarations, {holes.size} axioms justified \
      by the sidecar {r.solution} ({rS.decls.size} declarations accepted) ({modeTag})"
    for d in holes do
      outLine s!"con-leche: {Cached.declCLabel d} justified by the sidecar"
    return 0

end ConLeche.Driver
