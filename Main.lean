import ConLeche.Cached.ParsedC
import ConLeche.Frontend.ExportC
import ConLeche.Frontend.Prelude
import ConLeche.Frontend.InModelDump

/-!
Command-line driver: `con-leche FILE.ndjson` reads a **raw** lean4export
NDJSON file and checks the declarations in order.  There is no
preprocessor and no external dependency (task #207): every inductive
block is installed by a direct route, or through a `_model` family the
frontend generates in-process at parse time
(`ConLeche/Frontend/InModel/*`) and then checks as ordinary
declarations of the stream.

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
* 3 — bad usage, malformed input, or an internal failure of unclear cause

**NO TEMPORARY FILES** (task #180, 2026-09-07).  The checker writes
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
-/

open ConLeche

def ConLeche.CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- The whole input side of a run: the parsed declarations, read
straight from the file.  Since task #207 there is nothing else —
no preprocessor detection, no spawn, no pipe. -/
def parseInput (file : String) (prelude : Frontend.PreludeIx) (inModel : Bool) :
    IO (Except Frontend.FrontendError Frontend.ParseResultD) := do
  let census := (← IO.getEnv "CON_LECHE_INMODEL_CENSUS") == some "1"
  Frontend.parseExportStreamD file prelude inModel census

/-- `declPName` for the direct-parse `DeclC` records (task #171).  The
formatting itself lives beside the checker (`ConLeche.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : ConLeche.Cached.DeclC → String := ConLeche.Cached.declCLabel

/-- **The progress lane's fold — UNVERIFIED, and the only unverified
loop in the driver** (`CON_LECHE_PROGRESS`, user ruling 2026-09-07).

The default run calls `ConLeche.Cached.checkDeclsSPCachedD` — the pure
function `ConLeche.no_proof_of_False` is about — and prints nothing per
declaration.  A pure fold cannot print, so when the heartbeat is on the
driver runs a *different, plainly unverified* fold instead.

It is the same steps in the same order — `checkDeclStepIdxC mode`, the
position-carrying step of the verified fold, over the same records from
the same empty environment and state — with one line printed before
each declaration.  Nobody should be bothered by the difference between
these two trivial folds; what matters is that the difference is
*stated*: a run with `CON_LECHE_PROGRESS` set is not covered by the main
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

**Stride 1 is the localisation lane.**  With `CON_LECHE_PROGRESS=1` every
declaration is announced before it is checked, so a run that dies — an
OOM, a timeout, a `SIGKILL` — names on its last line the declaration it
died in.  The index is the FOLD position, not the stream's record
index: the parse folds the basis and `quot` blocks and drops
taint-skipped records, so the two drift apart by a stream-dependent
amount.  Calibrate by NAME. -/
def checkDeclsProgressIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) (trace : Bool) (inModelled : Array Name) :
    List ConLeche.Cached.DeclC → Nat → ConLeche.FEnv → ConLeche.Cached.CState →
      IO (Except (ConLeche.CheckError × Nat) ConLeche.Env)
  | [], _, fe, _ => return .ok fe.env
  | pd :: ds, i, fe, s => do
    if stride > 0 && i % stride == 0 then
      let now ← IO.monoMsNow
      err.putStr s!"con-leche: progress {i}/{total} \
        {ConLeche.Cached.declCLabel pd} \
        t={ConLeche.Cached.msSecs (now - t0)}s\n"
      err.flush
    -- THE ROUTE TRACE (`CON_LECHE_ROUTE_TRACE`, task #193): one line per
    -- inductive block naming the install route the checker is about
    -- to take — the recognisers run here on the same environment the
    -- step sees, so the line is exactly the dispatch of
    -- `checkIndDeclSF` (`ConLeche/Cached/CheckerC.lean`).  It is the
    -- route census's instrument (`tests/route-census.sh`): every block
    -- must read `struct`, `sum`, `fix`, `inmodel` or `basis` — a
    -- `modeled` line on a raw stream means the block's model came
    -- from the stream itself, and nothing emits one since task #207.
    if trace then
      match pd with
      | .indDecl block =>
        let route :=
          if (ConLeche.directFixParts? block).isSome then "fix"
          else if inModelled.contains ((block.head?.map (·.name)).getD .anonymous)
            then "inmodel"
          else "modeled"
        err.putStr s!"con-leche: route \
          {(block.head?.map (·.name)).getD .anonymous} {route}\n"
        err.flush
      | .basisDecl k =>
        -- a pinned basis block: matched by the parse before any
        -- recogniser runs, installed from the pin
        err.putStr s!"con-leche: route \
          {(k.decls.head?.map (·.name)).getD .anonymous} basis\n"
        err.flush
      | _ => pure ()
    match ConLeche.Cached.checkDeclStepIdxC mode (i, fe) pd s with
    | .ok ((i', fe'), s') =>
      checkDeclsProgressIO mode err stride total t0 trace inModelled ds i' fe' s'
    | .error e => return .error e

/-- The progress heartbeat's stride (`CON_LECHE_PROGRESS=<stride>`;
2026-09-07).  `none` — the variable unset — is off; a value that is not
a decimal numeral is a hard error, per the provenance discipline the
retired-variable arms follow (a run's output must be readable off its
invocation, never silently degraded).  `0` is the explicit "off". -/
def progressStride : IO (Except String Nat) := do
  match ← IO.getEnv "CON_LECHE_PROGRESS" with
  | none => return .ok 0
  | some s =>
    match s.toNat? with
    | some n => return .ok n
    | none => return .error s!"CON_LECHE_PROGRESS must be a declaration stride \
        (a decimal numeral; 0 or unset is off), got {repr s}"

/-! ## The parallel-ceiling probe — A MEASUREMENT LANE, NOT A VERDICT

`CON_LECHE_PROBE_SKIP=thm|thmdef` runs the ordinary fold with the
*body* check of theorem (and, at `thmdef`, definition) declarations
omitted: everything that produces the installed constant still runs —
the statement check, the value's syntactic guards, `annotate`, the
`ienv` recording and the push — and exactly the two steps that need the
body, `infer` and `defeq`, do not.  The difference in `instructions:u`
against a baseline run is the work a declaration-body fan-out could
move off the critical path, measured before any thread exists.

**This is not a checker.**  A run under the variable accepts streams it
must reject, and it says so on stderr.  It exists to measure Amdahl's
serial fraction for the deferred-body design and belongs in a
measurement lane, never on master. -/

section Probe
open ConLeche.Cached

/-- Which declaration kinds' body checks the probe omits. -/
inductive ProbeSkip where
  | off
  | thm
  | thmDef
  /-- also skips the value-side guards and `annotate`, installing the
  RAW value: not even a well-formedness check, but it measures how much
  of the install pass is per-body work that a fan-out could take. -/
  | thmBare
  /-- skips the value-side GUARDS only, keeping `annotate` — the cell
  that splits `thmbare`'s number into guards and annotation. -/
  | thmNoGuard
deriving BEq

/-- `CON_LECHE_PROBE_SKIP`, validated once (unset is off). -/
def probeSkipEnv : IO (Except String ProbeSkip) := do
  match ← IO.getEnv "CON_LECHE_PROBE_SKIP" with
  | none => return .ok .off
  | some "thm" => return .ok .thm
  | some "thmdef" => return .ok .thmDef
  | some "thmbare" => return .ok .thmBare
  | some "thmnoguard" => return .ok .thmNoGuard
  | some s => return .error s!"CON_LECHE_PROBE_SKIP must be thm or thmdef \
      (unset is off), got {repr s}"

/-- `checkThmValC` with its two body steps (`infer`, `defeq`) omitted;
every step that produces the installed constant is copied verbatim. -/
def probeThmInstall (mode : CheckMode) (fe : FEnv) (cvA : ConstantVal)
    (jty : ExprC) (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty (some (jv, jv))
  pure (fe.push (.thmInfo cvA jv))

/-- The `thmbare` arm: the statement check, then the RAW value pushed —
no value guards, no `annotate`, no body check.  Its only purpose is to
price the per-body work that sits in the install pass. -/
def probeThmBare (mode : CheckMode) (fe : FEnv) (cvA : ConstantVal)
    (jty : ExprC) (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  recordCConst cvA.name cvA.type jty (some (value, value))
  pure (fe.push (.thmInfo cvA value))

/-- The `thmnoguard` arm: `probeThmInstall` without the three value-side
guards (loose bvars, free variables, level parameters, resolvable
constants), `annotate` kept — those guards are pure predicates on the
body, so a fan-out could carry them; `annotate` cannot, since its result
is what gets installed. -/
def probeThmNoGuard (mode : CheckMode) (fe : FEnv) (cvA : ConstantVal)
    (jty : ExprC) (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  recordCConst cvA.name cvA.type jty (some (jv, jv))
  pure (fe.push (.thmInfo cvA jv))

/-- `checkDefnValC` with its two body steps omitted (the `thmdef`
arm only; the pinned Nat/div-mod names never take this route). -/
def probeDefnInstall (mode : CheckMode) (fe : FEnv) (cvA : ConstantVal)
    (jty : ExprC) (value : ExprC) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty (some (jv, jv))
  pure (fe.push (.defnInfo cvA jv hint))

/-- The probe's step: `checkDeclSPStepC` with the selected kinds'
bodies left unchecked.  The pinned Nat operations and div/mod keep the
full path (their certificates are part of the install). -/
def probeStep (mode : CheckMode) (skip : ProbeSkip) (fe : FEnv) (pd : DeclC) :
    CheckCM FEnv := do
  flushC
  match pd with
  | .thmDecl cv value =>
    let (cvA, jty) ← checkConstantValC mode fe cv
    if skip == .thmBare then probeThmBare mode fe cvA jty value
    else if skip == .thmNoGuard then probeThmNoGuard mode fe cvA jty value
    else probeThmInstall mode fe cvA jty value
  | .defnDecl cv value hint =>
    if skip == .thmDef && !(natOpNames.contains cv.name)
        && !(natDivModNames.contains cv.name) then do
      let (cvA, jty) ← checkConstantValC mode fe cv
      probeDefnInstall mode fe cvA jty value hint
    else checkDeclSPC mode fe pd
  | _ => checkDeclSPC mode fe pd

/-- The probe's fold: `checkDeclsSPCachedD`'s shape exactly, over
`probeStep`. -/
def probeFold (mode : CheckMode) (skip : ProbeSkip) (ds : List DeclC) :
    Except (CheckError × Nat) Env := do
  let step : Nat × FEnv → DeclC → StateT CState (Except (CheckError × Nat)) (Nat × FEnv) :=
    fun p pd s =>
      match probeStep mode skip p.2 pd s with
      | .ok (fe', s') => .ok ((p.1 + 1, fe'), s')
      | .error e => .error (e, p.1)
  let p ← (ds.foldlM step (0, mkFEnv Env.empty)).run' {}
  pure p.2.env

end Probe

/-! ## The deferred-body fan-out — AN EXPERIMENT, NOT A VERDICT LANE

`CON_LECHE_PAR=<workers>` runs the stream in two passes:

1. a sequential install pass — the ordinary fold, except that a
   theorem's two body steps (`infer`, `defeq`) are not run; instead the
   annotated statement and value are recorded as a `BodyJob` together
   with `fe.visibleBelow` at that point, i.e. the number of constants
   installed *before* the theorem;
2. a parallel body pass — `workers` tasks, round-robin over the jobs,
   each running `infer`/`defeq` against `feFinal.restrictTo job.bound`
   with its own `CState`.

The bound is what keeps this honest: `mkFEnv_find?_visibleBelow_some`
(`ConLeche/Verify/EnvBound.lean`) says a bounded lookup cannot reach a
constant installed at or after it, so no theorem can be justified by
one declared later.  The verdict is the failing job of LOWEST fold
position, so it does not depend on the schedule.

Not covered by `no_proof_of_False`: that theorem is about
`checkDeclsSPCachedD`, and this is a different function.  The bridge
that would cover it is stated in DESIGN (FEnv-extensionality across the
knot + the `.thmDecl` install/check decomposition); until it exists
this lane is an experiment. -/

section Par
open ConLeche.Cached

/-- A deferred theorem-body check. -/
structure BodyJob where
  idx : Nat
  /-- The index the body must be checked at: the very `FEnv` the fold
  held before this theorem's push, CAPTURED.  It costs a pointer because
  `FEnv.idx` is persistent (`Std.TreeMap`); with the hash index a
  capture would have cost the next insert its exclusivity, i.e. task
  #179's bucket-array copy per constant. -/
  fe : FEnv
  name : Name
  jty : ExprC
  jv : ExprC

/-- The install half of a theorem, emitting its deferred body job.
It IS the branch's own install half — `thmPrepC`
(`ConLeche/Cached/ParsedC.lean`) — followed by the push, so what the
fan-out defers is exactly what `checkThmValC_split` says it is. -/
def parThmInstall (mode : CheckMode) (fe : FEnv) (cvA : ConstantVal)
    (jty : ExprC) (value : ExprC) : CheckCM (FEnv × BodyJob) :=
  thmPrepC mode fe cvA jty value (fun jv =>
    pure (fe.push (.thmInfo cvA jv), ⟨0, fe, cvA.name, jty, jv⟩))

/-- The install pass's step: `checkDeclSPStepC` with theorem bodies
deferred.  The accumulator carries the fold position, the environment
and the jobs collected so far. -/
def parInstallStep (mode : CheckMode) (p : Nat × FEnv × Array BodyJob) (pd : DeclC) :
    StateT CState (Except (CheckError × Nat)) (Nat × FEnv × Array BodyJob) := fun s =>
  let (i, fe, jobs) := p
  match pd with
  | .thmDecl cv value =>
    match (do flushC; let (cvA, jty) ← checkConstantValC mode fe cv
              parThmInstall mode fe cvA jty value : CheckCM (FEnv × BodyJob)) s with
    | .ok ((fe', job), s') => .ok ((i + 1, fe', jobs.push { job with idx := i }), s')
    | .error e => .error (e, i)
  | _ =>
    match checkDeclSPStepC mode fe pd s with
    | .ok (fe', s') => .ok ((i + 1, fe', jobs), s')
    | .error e => .error (e, i)

/-- The install pass. -/
def parInstall (mode : CheckMode) (ds : List DeclC) :
    Except (CheckError × Nat) (FEnv × Array BodyJob) := do
  let p ← (ds.foldlM (parInstallStep mode) (0, mkFEnv Env.empty, #[])).run' {}
  pure (p.2.1, p.2.2)

/-- One deferred body's check: the branch's own body half (`thmBodyC`)
at the index the fold held, and nothing else. -/
def bodyAct (mode : CheckMode) (j : BodyJob) : CheckCM Unit := do
  flushC
  thmBodyC mode j.fe j.name j.jty j.jv (pure ())

/-- Keep the failure of lowest fold position. -/
def firstFailure : Option (CheckError × Nat) → Option (CheckError × Nat) →
    Option (CheckError × Nat)
  | none, b => b
  | a, none => a
  | some a, some b => if a.2 ≤ b.2 then some a else some b

/-- One job, checked at its own bounded view of the final environment
with a fresh memo state. -/
def checkOneJob (mode : CheckMode) (j : BodyJob) :
    Option (CheckError × Nat) :=
  match (bodyAct mode j).run' {} with
  | .ok _ => none
  | .error e => some (e, j.idx)

/-- One job, timed.  `IO.lazyPure` is what puts the work between the two
clock reads: a plain `let` is a PURE binding and the compiler sinks it to
its use site — past the second read — which is how the first cut of this
instrument measured 0 ns for every job while the pass still took
seconds. -/
def timedJob (mode : CheckMode) (j : BodyJob) :
    IO (Option (CheckError × Nat) × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => checkOneJob mode j
  let t1 ← IO.monoNanosNow
  pure (r, t1 - t0)

/-- The alternative schedule: ONE TASK PER JOB, Lean's own pool doing
the balancing and `LEAN_NUM_THREADS` bounding the threads.  Kept beside
the queue so the two can be compared on the same binary; selected by
`CON_LECHE_PAR_JOB=1`. -/
def parBodiesPerJob (mode : CheckMode) (jobs : Array BodyJob) :
    IO (Option (CheckError × Nat) × Nat × Nat) := do
  let ts ← jobs.mapM fun j => IO.asTask (timedJob mode j)
  let mut err : Option (CheckError × Nat) := none
  let mut span := 0
  let mut sum := 0
  for t in ts do
    match t.get with
    | .ok (r, dt) =>
      err := firstFailure err r
      span := max span dt
      sum := sum + dt
    | .error e => throw e
  pure (err, span, sum)

/-- Pull the next job index, or `none` when the queue is drained. -/
def nextJob (q : Std.Mutex Nat) (n : Nat) : BaseIO (Option Nat) :=
  q.atomically do
    let i ← get
    if i < n then
      set (i + 1)
      return some i
    else
      return none

/-- One worker: pull, check, repeat, carrying the lowest-position
failure, the largest single-body time (the SPAN) and the total. -/
partial def pullLoop (mode : CheckMode) (jobs : Array BodyJob)
    (q : Std.Mutex Nat) (acc : Option (CheckError × Nat)) (span sum : Nat) :
    IO (Option (CheckError × Nat) × Nat × Nat) := do
  match ← nextJob q jobs.size with
  | none => pure (acc, span, sum)
  | some i =>
    match jobs[i]? with
    | none => pure (acc, span, sum)   -- unreachable: `nextJob` bounds `i`
    | some j =>
    let t0 ← IO.monoNanosNow
    -- `IO.lazyPure`, not a `let`: a pure binding is sunk to its use site
    -- by the compiler, past the second clock read, and every job then
    -- measures 0 ns.
    let r ← IO.lazyPure fun _ => checkOneJob mode j
    let t1 ← IO.monoNanosNow
    let dt := t1 - t0
    pullLoop mode jobs q (firstFailure acc r) (max span dt) (sum + dt)

/-- The body pass: `workers` tasks pulling from ONE shared queue.

Two constraints pick this shape.  **Skew**: the body-time distribution
is long-tailed (FLT cone: p50 423 us, span 248 ms — 590 x; on the full
FLT export one declaration carries 10.5 M expression nodes against a
mean of 628), so assignment must be dynamic — a static round-robin can
hand one worker several giants while the rest idle.  **`ulimit -v`**:
one task per job lets Lean's pool grow to `nproc` threads, whose
mimalloc arenas blow the address-space cap this project runs every
checker under (`failed to create thread`, exit 134 — the failure DESIGN
already records for builds).  Spawning exactly `workers` tasks bounds
the thread count without an environment variable.

The verdict is the failing job of LOWEST fold position, so it does not
depend on the schedule. -/
def parBodies (mode : CheckMode) (jobs : Array BodyJob)
    (workers : Nat) : IO (Option (CheckError × Nat) × Nat × Nat) := do
  let q ← Std.Mutex.new 0
  let ts ← (List.range (max workers 1)).mapM fun _ =>
    IO.asTask (pullLoop mode jobs q none 0 0)
  let mut err : Option (CheckError × Nat) := none
  let mut span := 0
  let mut sum := 0
  for t in ts do
    match t.get with
    | .ok (e, sp, su) =>
      err := firstFailure err e
      span := max span sp
      sum := sum + su
    | .error e => throw e
  pure (err, span, sum)

/-- The install pass with a heartbeat: the same steps as `parInstall`,
in `IO`, printing one line every `stride` declarations.  A run that takes
hours must not be blind. -/
partial def parInstallIO (mode : CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) :
    List DeclC → Nat → FEnv → Array BodyJob → CState →
      IO (Except (CheckError × Nat) (FEnv × Array BodyJob))
  | [], _, fe, jobs, _ => return .ok (fe, jobs)
  | pd :: ds, i, fe, jobs, s => do
    if stride > 0 && i % stride == 0 then
      let now ← IO.monoMsNow
      err.putStr s!"con-leche: par install {i}/{total} \
        {ConLeche.Cached.declCLabel pd} \
        t={ConLeche.Cached.msSecs (now - t0)}s ({jobs.size} deferred)\n"
      err.flush
    match parInstallStep mode (i, fe, jobs) pd s with
    | .ok ((i', fe', jobs'), s') =>
      parInstallIO mode err stride total t0 ds i' fe' jobs' s'
    | .error e => return .error e

end Par

/-- The real driver (run in the supervised child process).  `mode` is
the three-mode setting (task #147), validated once by the caller and
consumed here as configuration.

**One core at two modes, one parse.**  The interned representation
and every driver over it retired with the arena (task #172), the R
core retired with the collapsed model (2026-09-05), and the
hand-written trusted twin retired into an instantiation
(2026-09-06), so the stream is parsed directly to `ExprC`
(`Frontend.parseExportStreamD`, task #171) and checked by the one
cached driver — at `.verified` under `--verified` (the default), at `.trusted`
under `--trusted`.  The verified instance is covered by
`no_proof_of_Empty_SPCD_P` over `checkDeclsSPCachedD`
(`ConLeche/Verify/Cached/MainC.lean`); the trusted one is unverified by
design and agrees with it on the install skeletons whenever both
accept (`trusted_agrees_P_skels_shipped`). -/
def checkMain (file : String) (mode : CheckMode) : IO UInt32 := do
    -- The retired environment variables (tasks #76/#134) are hard
    -- errors, not silently ignored: a verdict's provenance must be
    -- readable off the invocation (task #147).
    if (← IO.getEnv "CON_LECHE_NO_PROOF_CERTS") == some "1" then
      IO.eprintln "con-leche: CON_LECHE_NO_PROOF_CERTS is retired; the \
        cert-skipping measurement lane is the --trusted mode \
        (checking-mode front door included — see DESIGN.md, task #147)"
      return 3
    if (← IO.getEnv "CON_LECHE_INFER_ONLY") == some "1" then
      IO.eprintln "con-leche: CON_LECHE_INFER_ONLY is retired; the infer-only \
        internal discipline is part of the --trusted mode, and the \
        certified mode is --verified, the default \
        (see DESIGN.md, task #147)"
      return 3
    -- The opt-in progress heartbeat (2026-09-07): validated here, once,
    -- before any work is done.
    let stride ← match ← progressStride with
      | .error msg => IO.eprintln s!"con-leche: {msg}"; return 3
      | .ok n => pure n
    -- The parallel-ceiling probe (`CON_LECHE_PROBE_SKIP`): validated
    -- here, once, and announced loudly — a probe run is a MEASUREMENT,
    -- not a verdict.
    let skip ← match ← probeSkipEnv with
      | .error msg => IO.eprintln s!"con-leche: {msg}"; return 3
      | .ok s => pure s
    -- The deferred-body fan-out (`CON_LECHE_PAR=<workers>`): an
    -- EXPERIMENT, announced as loudly as the probe.
    let par ← match ← IO.getEnv "CON_LECHE_PAR" with
      | none => pure 0
      | some s => match s.toNat? with
        | some n => pure n
        | none =>
          IO.eprintln s!"con-leche: CON_LECHE_PAR must be a worker count \
            (a decimal numeral; 0 or unset is off), got {repr s}"
          return 3
    unless skip == .off do
      let what := if skip == .thm then "theorem"
        else if skip == .thmNoGuard then "theorem (bodies and value guards)"
        else if skip == .thmBare then "theorem (bodies, guards and annotation)"
        else "theorem and definition"
      IO.eprintln s!"con-leche: PROBE LANE — {what} BODIES ARE NOT CHECKED; \
        this run measures the deferred-body design's serial fraction and its \
        exit code is not a verdict."
    -- The route trace (`CON_LECHE_ROUTE_TRACE`, task #193): one `con-leche:
    -- route <block> <struct|sum|fix|inmodel|modeled>` line per inductive block,
    -- on the progress lane (so a traced run is as unverified as a
    -- heartbeat run, and says so).
    let trace := (← IO.getEnv "CON_LECHE_ROUTE_TRACE").isSome
    let t0 ← IO.monoMsNow
    -- Every VERDICT line names the mode (2026-09-07): a `--trusted`
    -- run — the unverified lane — must never be mistaken for a
    -- `--verified` one in a log, whatever it says.
    let modeTag : String := match mode with
      | .verified => "--verified"
      | .trusted => "--trusted"
    -- THE BUILT-IN PRELUDE (task #191, `ConLeche/Frontend/Prelude.lean`):
    -- the pinned basis blocks and `Bool`, parsed from the committed
    -- `pins/<toolchain>.prelude.ndjson` and PREPENDED to every parsed
    -- stream, so the fold installs them first and unconditionally; a
    -- stream's own copy of one is dropped when identical and declines
    -- the run when different.  A prelude that does not parse is a
    -- corrupted build, reported before any input is read.
    let prelude ← match Frontend.builtinPreludeE with
      | .ok p => pure p
      | .error (.parseError line msg) =>
        IO.eprintln s!"con-leche: the built-in prelude does not parse (line \
          {line}: {msg}); regenerate it with `lake exe natop-pins-export` \
          ({modeTag})"
        return 3
      | .error (.unsupported what) =>
        IO.eprintln s!"con-leche: the built-in prelude is unsupported ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
    -- Streaming frontend (task #57, task #180): the parse reads the
    -- file line by line, so neither a wholesale text buffer nor a
    -- scratch file exists in this process.
    -- THE IN-PROCESS MODELLER (task #200; the only model source since
    -- task #207): mutual and nested blocks get their `_model` family
    -- generated at parse time (`ConLeche/Frontend/InModel.lean`);
    -- `CON_LECHE_INMODEL=0` turns it off, `CON_LECHE_INMODEL_DUMP=OUT`
    -- writes the raw input with the generated records spliced in (the
    -- generator's debug gate).
    let inModel := (← IO.getEnv "CON_LECHE_INMODEL") != some "0"
    match ← parseInput file prelude inModel with
    | .error (.unsupported what) =>
      IO.eprintln s!"con-leche: declined: {what} ({modeTag})"
      return 2
    | .error (.parseError line msg) =>
      IO.eprintln s!"con-leche: {file}:{line}: {msg}"
      return 3
    | .ok ⟨decls, taintSkipped, projRewrites, preludeCount,
           preludeDropped, hoisted, inModelled, inModelGen, inModelDeclined⟩ =>
      -- the in-process modeller's receipt (task #200)
      if inModelled.size > 0 then
        IO.eprintln s!"con-leche: {inModelled.size} inductive blocks modelled \
          in-process: {String.intercalate ", " (inModelled.toList.map toString)}"
      -- the census (`CON_LECHE_INMODEL_CENSUS=1`): every mutual/nested block's
      -- outcome, then stop — the parse only, no fold
      if (← IO.getEnv "CON_LECHE_INMODEL_CENSUS") == some "1" then
        for (n, why) in inModelDeclined do
          IO.eprintln s!"con-leche: inmodel declined {n}: {why}"
        IO.eprintln s!"con-leche: inmodel census: {inModelled.size} modelled, \
          {inModelDeclined.size} declined ({modeTag}, parse only)"
        return 0
      if let some out ← IO.getEnv "CON_LECHE_INMODEL_DUMP" then
        if inModelGen.size > 0 then
          Frontend.dumpInModel file out inModelGen
          IO.eprintln s!"con-leche: in-process models dumped to {out}"
      -- `decls` = the prelude's `preludeCount` records, then the
      -- stream's (minus `preludeDropped` identical copies of prelude
      -- records); fold positions count from the prelude's first record,
      -- and the stream's accepted-record count is
      -- `decls.size - preludeCount + preludeDropped`
      -- the projection-function rewrite's receipt (2026-09-06,
      -- `ConLeche/Frontend/ProjRec.lean`): how many non-direct
      -- structure-like projection functions the parse replaced by
      -- recursor applications
      if projRewrites.size > 0 then
        IO.eprintln s!"con-leche: {projRewrites.size} projection functions of \
          non-direct structure-likes rewritten to recursor form"
        if (← IO.getEnv "CON_LECHE_PROJREC_TRACE").isSome then
          for n in projRewrites do
            IO.eprintln s!"con-leche:   rewritten {n}"
      -- the ground hoist's receipt (task #191,
      -- `ConLeche/Frontend/NatOpGround.lean`): records moved ahead of a
      -- pinned Nat operation whose certificate statements they ground
      if hoisted.size > 0 then
        IO.eprintln s!"con-leche: {hoisted.size} declarations hoisted ahead of \
          the pinned Nat operations they ground: \
          {String.intercalate ", " (hoisted.toList.map toString)}"
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
          IO.eprintln s!"con-leche: declined: \
            {Frontend.taintSummary taintSkipped} ({modeTag})"
      -- ONE driver, two modes (2026-09-06; task #185): the trusted
      -- mode is the shared bodies at `.trusted`, the verified mode the
      -- same bodies at `.verified` — the mode is passed straight down.
      -- **Two loops** (user ruling, 2026-09-07).  Without
      -- `CON_LECHE_PROGRESS` the driver calls the verified fold
      -- `ConLeche.Cached.checkDeclsSPCachedD` directly — the exact
      -- function `ConLeche.no_proof_of_False` (`ConLeche/MainTheorem.lean`)
      -- is about.  With it, the driver calls `checkDeclsProgressIO`
      -- above: the same steps in the same order, in `IO`, printing one
      -- line before each declaration — plainly unverified, and said so
      -- in its docstring, in `--help` and in DESIGN.  The two folds
      -- differ in the print and nothing else, and nothing about the
      -- verified statement is bent to accommodate the printing.
      --
      -- **Reading the index**: `i` is the *fold* position, and it is
      -- NOT the stream's declaration-record index.  The parse folds
      -- the four `quot` records into one `basisDecl` and drops a few
      -- others, a taint-skipping stream loses more, and — since task
      -- #200 — the in-process modeller ADDS records the file does not
      -- contain, so the fold can run AHEAD of the file's index.
      -- Measured on raw `init-full` (task #207): 53 093 declaration
      -- records in the file against 53 118 fold positions, the +25
      -- being `Lean.Syntax`'s generated model family (30 records) less
      -- the 5 folded and skipped ones.  The declaration NAME on the
      -- line is the portable handle.
      let tParse ← IO.monoMsNow
      if stride > 0 then
        IO.eprintln s!"con-leche: progress parse done: {decls.size - preludeCount} \
          declarations after the {preludeCount} built-in prelude records \
          ({preludeDropped} stream copies of prelude records dropped) \
          t={ConLeche.Cached.msSecs (tParse - t0)}s \
          (parse; the progress lane's fold is UNVERIFIED — see --help)"
        (← IO.getStderr).flush
      -- The closing line: how far the loop got (`= N` on an accept,
      -- the failing position otherwise) and how long it took.
      let progressDone : Nat → IO Unit := fun reached => do
        if stride > 0 then
          let now ← IO.monoMsNow
          IO.eprintln s!"con-leche: progress fold done: {reached}/\
            {decls.size} t={ConLeche.Cached.msSecs (now - t0)}s \
            (fold {ConLeche.Cached.msSecs (now - tParse)}s)"
          (← IO.getStderr).flush
      let verdict : Except (ConLeche.CheckError × Nat) ConLeche.Env ←
        if par > 0 then do
          IO.eprintln s!"con-leche: PAR LANE — the deferred body pass is an \
            EXPERIMENT, not covered by the main theorem (pool size is \
            LEAN_NUM_THREADS; cap it under ulimit -v)."
          let inst ←
            if stride > 0 then
              parInstallIO mode (← IO.getStderr) stride decls.size t0
                decls.toList 0 (ConLeche.mkFEnv ConLeche.Env.empty) #[] {}
            else pure (parInstall mode decls.toList)
          match inst with
          | .error e => pure (.error e)
          | .ok (feFinal, jobs) =>
            let tI ← IO.monoMsNow
            IO.eprintln s!"con-leche: par install pass: {jobs.size} deferred \
              theorem bodies, t={ConLeche.Cached.msSecs (tI - tParse)}s"
            (← IO.getStderr).flush
            -- ONE TASK PER JOB.  The schedule is Lean's pool, not ours:
            -- the body-time distribution is heavily skewed (measured on
            -- the FLT cone: p50 423 us, max 248 ms — 590x), so a static
            -- round-robin assignment risks one worker drawing several
            -- giants while the rest idle.  Dropping the striping cost
            -- +0.9 % instructions (the level memos are no longer reused
            -- across a worker's jobs) and no wall time.
            let perJob := (← IO.getEnv "CON_LECHE_PAR_JOB") == some "1"
            let (res, span, sum) ←
              if perJob then parBodiesPerJob mode jobs
              else parBodies mode jobs par
            IO.eprintln s!"con-leche: par job stats: {jobs.size} bodies, \
              Σ={sum / 1000000}ms, span(max)={span / 1000000}ms, \
              workers={par}"
            let tB ← IO.monoMsNow
            IO.eprintln s!"con-leche: par body pass: \
              t={ConLeche.Cached.msSecs (tB - tI)}s"
            match res with
            | none => pure (.ok feFinal.env)
            | some e => pure (.error e)
        else if stride > 0 || trace then
          checkDeclsProgressIO mode (← IO.getStderr) stride decls.size t0 trace
            inModelled decls.toList 0 (ConLeche.mkFEnv ConLeche.Env.empty) {}
        else if skip != .off then
          pure (probeFold mode skip decls.toList)
        else
          pure (ConLeche.Cached.checkDeclsSPCachedD mode decls.toList)
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
        -- **The headline number is the STREAM's declaration-record
        -- count** (task #191 arithmetic, task #187 unit): the records
        -- the fold consumed minus the built-in prelude's, plus the
        -- stream records dropped as identical copies of prelude
        -- records (they ARE installed — from the prelude).  So a
        -- stream re-declaring `Bool` identically reports the same
        -- count as before the prelude existed.
        --
        -- What it replaced was `env.consts.length`, the number of
        -- environment CONSTANTS — an inductive block's type former,
        -- its constructors, its recursor, its projection table and the
        -- basis extras counted separately.  That is a property of our
        -- REPRESENTATION, not of the input: it moved whenever the
        -- representation moved (task #175 S1's one projection table
        -- per structure dropped init-full by 499 with no verdict
        -- change).  The record count is a property of the input.
        --
        -- It still does not equal the official checker's number, and
        -- it cannot: official prints `constMap.size`, its PARSED
        -- export, where an inductive record counts as its type
        -- formers, its constructors and its recursors (less the three
        -- `Quot.mk`/`.lift`/`.ind` entries it erases).  That is a
        -- third unit — also a function of the file, just a larger one.
        -- `scripts/stream-census.py` derives BOTH numbers from a
        -- stream and is checked against both checkers' actual output.
        -- The environment-constant count stays on stderr under
        -- `CON_LECHE_VERBOSE=1`.
        let streamRecords := decls.size - preludeCount + preludeDropped
        let verboseCounts : IO Unit := do
          if (← IO.getEnv "CON_LECHE_VERBOSE").isSome then
            IO.eprintln s!"con-leche: environment: {env.consts.length} constants \
              from {decls.size} fold records ({preludeCount} built-in \
              prelude records, {preludeDropped} stream copies of them \
              dropped)"
        if taintSkipped.isEmpty then
          IO.println s!"con-leche: accepted {streamRecords} \
            declarations ({modeTag})"
          verboseCounts
          return 0
        else
          IO.eprintln s!"con-leche: declined ({streamRecords} \
            declarations checked, {taintSkipped.size} skipped for \
            tolerated axioms) ({modeTag}): \
            {Frontend.taintDetail taintSkipped}"
          verboseCounts
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
        -- positions), while the `CON_LECHE_TRACE_DECLS` lane measured
        -- +4 on the Mathlib stream.  The declaration NAME is the
        -- portable handle (`_tmp/frontier3/decl_index.py <stream>
        -- <name>` turns it into a record index and a percentage).
        let loc := if h : i < decls.size then
            s!" [at {declCName decls[i]}, fold position {i}]"
          else s!" [at fold position {i}]"
        let now ← IO.monoMsNow
        IO.eprintln s!"con-leche: {e}{loc} ({modeTag}) \
          t={ConLeche.Cached.msSecs (now - t0)}s"
        taintNote
        return e.exitCode


def usage : String := String.intercalate "\n" [
  "usage: con-leche [--verified|--trusted] FILE.ndjson",
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
  "                    binary runs (ConLeche/Verify/Cached/MainC.lean)",
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
  "                    --yolo/CON_LECHE_NO_PROOF_CERTS and",
  "                    --infer-only/CON_LECHE_INFER_ONLY",
  "  CON_LECHE_PROGRESS=<stride>",
  "                    opt-in progress heartbeat on STDERR: one",
  "                    'con-leche: progress <i>/<N> <decl> t=<s>s' line",
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
  "                    theorem (ConLeche.no_proof_of_False) is about; a",
  "                    run with it is not covered by that theorem.",
  "  CON_LECHE_ROUTE_TRACE=1",
  "                    the install-route audit (task #193): one",
  "                    'con-leche: route <block> <struct|sum|fix|inmodel|modeled>'",
  "                    line",
  "                    on STDERR per inductive block, naming the route",
  "                    the checker takes for it (the direct structure",
  "                    route, the direct sum/indexed route, the direct",
  "                    fixed-point route (task #188), the in-process",
  "                    model (task #200), or a model the STREAM itself",
  "                    carries).  tests/route-census.sh pins the",
  "                    per-route counts over every good fixture: on a",
  "                    raw stream no block may read 'modeled', since",
  "                    nothing emits a _model family since task #207.",
  "                    Runs on the progress lane's UNVERIFIED fold",
  "                    (above).",
  "",
  "  CON_LECHE_INMODEL=0    turn the IN-PROCESS MODELLER off (task #200).  By",
  "                    default a mutual or nested inductive block the",
  "                    stream carries no `_model` family for gets one",
  "                    generated at parse time (ConLeche/Frontend/InModel/*)",
  "                    and pushed ahead of the block; the generated",
  "                    records are checked by the fold like any stream",
  "                    declaration, and the block installs through the",
  "                    modeled route.  A generator decline is the run's",
  "                    decline, naming the class.  The route trace reads",
  "                    `inmodel` for such a block.  DEBUG SWITCH ONLY:",
  "                    the in-process modeller is the checker's only",
  "                    model source (task #207), so with the flag off",
  "                    every mutual or nested block reaches the fold",
  "                    bare and the run declines with 'no install",
  "                    route for'.",
  "                    A verdict produced with it set is not the",
  "                    checker's verdict on the stream.",
  "  CON_LECHE_INMODEL_DUMP=OUT",
  "                    write a copy of the raw input with the generated",
  "                    records spliced in ahead of each modelled block",
  "                    (lean4export format; the generator's debug gate,",
  "                    tests/inmodel.sh).",
  "",
  "  CON_LECHE_VERBOSE=1    add one stderr line beside the verdict giving the",
  "                    ENVIRONMENT-CONSTANT count and the fold's record",
  "                    count.  The verdict line counts the STREAM's",
  "                    accepted declaration RECORDS: one per",
  "                    def/theorem/opaque/axiom/inductive record the",
  "                    stream declared and the fold consumed.  The",
  "                    built-in prelude's own records are not counted,",
  "                    and a stream record dropped as an identical copy",
  "                    of a prelude record is (it is installed, from the",
  "                    prelude).  That count is a property of the INPUT.",
  "                    The constant count is not: an inductive record",
  "                    installs several constants (type former,",
  "                    constructors, recursor, projection table), so it",
  "                    moves when the representation moves.  NB the",
  "                    official kernel's 'Accepted N declarations' is a",
  "                    THIRD unit — its parsed constMap, where an",
  "                    inductive record counts as its members — also a",
  "                    function of the file, just a larger one;",
  "                    scripts/stream-census.py derives both from a",
  "                    stream.",
  "",

  "THE BUILT-IN PRELUDE (task #191).  Every run installs, first and",
  "unconditionally, the checker's own little prelude — the six pinned",
  "basis blocks (Eq, Nat, PUnit, Empty, False, Quot) and the toolchain's",
  "Bool block (pins/<toolchain>.prelude.ndjson, embedded at build time;",
  "ConLeche/Frontend/Prelude.lean) — so the pin-certified Nat operations",
  "find their ground whatever order the export chose.  A stream's own",
  "copy of a prelude declaration is dropped when it is the same",
  "declaration and DECLINES the run (exit 2, naming it) when it differs;",
  "a mismatching basis block still REJECTS (reserved name), as before.",
  "A pinned operation's stream-certified structural ground (Nat.ble,",
  "Nat.sub, Nat.mul — spelled into the certificate statements, not",
  "reachable from the operation's own value) is HOISTED ahead of the",
  "operation when the stream declares it later (ConLeche/Frontend/",
  "NatOpGround.lean): a dependency-closed reorder of the parsed list,",
  "reported on stderr.  Both are pure transformations of the parsed",
  "list below the verified fold; the main theorem is about the fold",
  "over prelude ++ stream.",
  "",
  "NO PREPROCESSOR (task #207).  The input is a RAW lean4export stream:",
  "there is no external tool, no dependency and no spawn.  Every",
  "inductive block is installed by a direct route — structures, sums,",
  "indexed families, finitary fixed points and reflexive blocks — or",
  "through a `_model` family the frontend generates IN-PROCESS at parse",
  "time and then checks as ordinary declarations of the stream.  The",
  "generator is not trusted: a wrong record is rejected or declined by",
  "the fold, never accepted; it decides coverage only.  A block no",
  "route takes declines (exit 2) naming its class.",
  "",
  "There is ONE core at two modes and one parse: the verified mode",
  "(--verified, the default) and the unverified trusted mode",
  "(--trusted).  The stream is read directly to the cached",
  "representation and checked by the one driver, which the capstone",
  "letter is about at the verified mode (no_proof_of_Empty_SPCD_P in",
  "ConLeche/Verify/Cached/MainC.lean).  Retired: --set-model/",
  "--set-model=p (now --verified) and --no-model (now --trusted),",
  "2026-09-06; the --core selector, the interned arena and the",
  "--install-only/--check-range split driver (task #172); and the R",
  "core with --set-model=r (2026-09-05, with the collapsed-model",
  "consistency proof it was the subject of)."]

structure Args where
  mode : ConLeche.CheckMode := .verified
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
  | "--pre" :: _, a =>
    { a with bad := some "--pre is retired; there is no preprocessor — \
        every input is a raw lean4export stream (task #207)" }
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

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    return 0
  -- `--verified`/`--trusted`: the mode setting (task #147), validated
  -- here once and threaded as configuration.  Two cores since the R
  -- core's retirement (2026-09-05): the graded verified one and the
  -- unverified trusted one.
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"con-leche: {msg}"
    IO.eprintln usage
    return 3
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
    if (← IO.getEnv "CON_LECHE_SUPERVISED").isSome then
      checkMain file a.mode
    else
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := childArgs a file
        env := #[("CON_LECHE_SUPERVISED", some "1")]
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
        IO.eprintln "con-leche: internal panic in the checker process"
        return 3
      return code
  | _ =>
    IO.eprintln usage
    return 3
