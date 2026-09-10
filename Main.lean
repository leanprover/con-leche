module

public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.InModelDump
public import ConLeche.Cached.Installed

@[expose] public section

/-!
Command-line driver: `con-leche FILE.ndjson` reads a **raw** lean4export
NDJSON file and checks the declarations in order.  There is no
preprocessor and no external dependency (task #207): every inductive
block is installed by the fixed-point route, or through a `_model`
family the frontend generates in-process at parse time
(`ConLeche/Frontend/InModel/*`) and then checks as ordinary
declarations; no model is ever read from the input (task #219).

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid.  An out-of-memory
  condition also exits 1: it is the Lean runtime's own panic
  (`lean_internal_panic_out_of_memory` prints "INTERNAL PANIC: out of
  memory" on stderr and calls `exit(1)`), uncatchable in process, so
  the message on stderr is what tells the two apart (task #230).
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
  A diagnostic run that stops before the fold exits 2 for the same
  reason it is not an accept: `CON_LECHE_INMODEL_CENSUS=1` reports the
  in-process modeller's outcomes after the parse and never checks
  anything (task #271).
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

/-- **Phase A's loop — the driver's install pass, carrying its own
accepting run.**  Each record is installed by
`ConLeche.Cached.annotDeclStep`: a separable value declaration is
annotated and pushed with its check recorded, everything else is checked
in full.  The loop carries the chain of accepting steps
(`ConLeche.Cached.InstallRun`) of the records it has consumed — a
proposition, so nothing at run time — and returns it with the result:
what this loop returns IS an `InstalledEnv mode ds`
(`ConLeche/Cached/Installed.lean`), phase A of the fold `checkDecls`.
Whatever it prints between steps is irrelevant to that type, which is
why ONE loop serves the plain run, the `--progress` heartbeat and the
route trace alike.

**Written tail-recursively, threading `p` and `s` LINEARLY** (task
#182's finding, `agent/fenv-linear`): a `for … in ds` loop with
`let mut` accumulators desugars to code that `lean_inc`s both the
`FEnv` and the `CState` before each step, so `lean_is_exclusive` is
false at the index inserts and every hashmap copies its bucket array
per declaration — quadratic at Mathlib scale, which is what made the
`traceLoopC` probe unusable.  Here the previous `p`/`s` are dead at the
recursive call, so the C carries no `lean_inc` of either before the
step, and the cost per declaration is flat.  The run is carried in the
SNOC direction (`InstallRun.snoc`) precisely so that the call stays a
tail call: a cons-direction proof would wrap the result on the way
back, one frame per declaration.

**Stride 1 is the localisation lane.**  With `--progress` (bare, or
`--progress=1`) every declaration is announced before it is installed,
so a run that dies — an OOM, a timeout, a `SIGKILL` — names on its last
line the declaration it died in.  The index is the FOLD position, not
the stream's record index: the parse folds the basis and `quot` blocks
and drops taint-skipped records, so the two drift apart by a
stream-dependent amount.  Calibrate by NAME. -/
def installLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) (trace : Bool) (inModelled : Array Name)
    (ds : List ConLeche.Cached.DeclC)
    (p₀ : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) (s₀ : ConLeche.Cached.CState) :
    (rest : List ConLeche.Cached.DeclC) →
    (p : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) →
    (s : ConLeche.Cached.CState) →
    (∃ done, done ++ rest = ds ∧ ConLeche.Cached.InstallRun mode done p₀ s₀ p s) →
      IO (Except (ConLeche.CheckError × Nat)
        (Σ' (p' : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck)
          (s' : ConLeche.Cached.CState), PLift (ConLeche.Cached.InstallRun mode ds p₀ s₀ p' s')))
  | [], p, s, hrun =>
    return .ok ⟨p, s, ⟨by
      obtain ⟨done, hds, hr⟩ := hrun
      rw [List.append_nil] at hds
      exact hds ▸ hr⟩⟩
  | pd :: rest, p, s, hrun => do
    if stride > 0 && p.1 % stride == 0 then
      let now ← IO.monoMsNow
      err.putStr s!"con-leche: install {p.1}/{total} \
        {ConLeche.Cached.declCLabel pd} \
        t={ConLeche.Cached.msSecs (now - t0)}s\n"
      err.flush
    -- THE ROUTE TRACE (`CON_LECHE_ROUTE_TRACE`, task #193): one line per
    -- inductive block naming the install route the checker is about
    -- to take — the recognisers run here on the same environment the
    -- step sees, so the line is exactly the dispatch of
    -- `checkIndDeclSF` (`ConLeche/Cached/CheckerC.lean`).  It is the
    -- route census's instrument (`tests/route-census.sh`): every block
    -- must read `fix`, `inmodel` or `basis` — a `modeled` line means
    -- the block is on NO route (the recogniser refused it and the
    -- in-process modeller did not model it), so the install declines.
    -- Since task #219 a `_model` record in the stream is an ordinary
    -- declaration and cannot route a block.
    if trace then
      match pd with
      | .indDecl block nP =>
        let route :=
          if (ConLeche.nativeParts? nP block).isSome then "fix"
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
    match h : ConLeche.Cached.annotDeclStep mode p pd s with
    | .ok (p₁, s₁) =>
      installLoop mode err stride total t0 trace inModelled ds p₀ s₀ rest p₁ s₁ (by
        obtain ⟨done, hds, hr⟩ := hrun
        exact ⟨done ++ [pd], by rw [List.append_assoc]; exact hds,
          ConLeche.Cached.InstallRun.snoc mode hr h⟩)
    | .error e => return .error e

/-- The check phase's heartbeat: on the `stride`-th completed check
(`n` completed so far, record `k` the one just completed), one line
naming it.  The counter is the number of COMPLETED checks, so in the
pool it is monotone whichever worker finished, and the line is printed
after the check rather than before it: a check that is running is not
on any line, the gap between two lines is where it sits. -/
def checkHeartbeat (err : IO.FS.Stream) (stride t0 : Nat) {mode : ConLeche.CheckMode}
    {ds : List ConLeche.Cached.DeclC} (e : ConLeche.Cached.InstalledEnv mode ds)
    (n k : Nat) (hk : k < e.pend.size) : IO Unit := do
  if stride > 0 && n % stride == 0 then
    let now ← IO.monoMsNow
    err.putStr s!"con-leche: check {n}/{e.pend.size} \
      {e.pend[k].vg.kind.word} {e.pend[k].vg.cvA.name} \
      t={ConLeche.Cached.msSecs (now - t0)}s\n"
    err.flush

/-- **Phase B in one thread — the check pass at `--jobs=1`.**  Record
`k` is checked against the prefix view of the installed index from a
fresh memo state (`ConLeche.Cached.checkRecord`), and the accumulator —
`GroupChecked` of every record below `k`, a proposition — grows by
one; at the end every record is checked, which with the installed
environment IS a `FullyChecked mode ds`, phase B of the fold
`checkDecls`.  Nothing is shared with any other thread, and nothing is
marked for multi-threaded reference counting: this loop is the
sequential baseline the pool below is measured against.  With
`--progress`, one line per `stride` completed checks. -/
def checkLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Cached.DeclC} (e : ConLeche.Cached.InstalledEnv mode ds) :
    (k : Nat) → (∀ j, j < k → ConLeche.Cached.GroupChecked mode e j) →
      IO (Except (ConLeche.CheckError × Nat) (PLift (∀ i, ConLeche.Cached.GroupChecked mode e i)))
  | k, acc =>
    if hk : k < e.pend.size then do
      match ConLeche.Cached.checkRecord mode e k hk with
      | .ok ⟨h⟩ =>
        checkHeartbeat err stride t0 e (k + 1) k hk
        checkLoop mode err stride t0 e (k + 1) (ConLeche.Cached.groupChecked_extend mode acc h)
      | .error e' => return .error e'
    else
      return .ok ⟨ConLeche.Cached.groupChecked_all mode
        (fun j hj => acc j (Nat.lt_of_lt_of_le hj (Nat.le_of_not_lt hk)))⟩
  termination_by k => e.pend.size - k

/-! ### The pool: phase B on `--jobs=<n>` threads

The records' checks are independent by construction — each reads the
installed index at its own prefix view, its own record, and a fresh
memo state — so phase B is handed to `n` long-lived worker tasks
(`IO.asTask` on dedicated threads: exactly `n` threads whatever the
runtime's own pool size).  The work is millions of mostly tiny checks
with a skewed tail (single bodies of an hour exist) and the heavy ones
sit CLOSE TOGETHER in the stream, so a worker claims ONE record per
atomic claim off one shared counter: a cluster of heavy declarations is
spread over the whole pool instead of serialising inside one claimed
range, and the only item that can strand the pool is the single largest
check.  The claim costs one `modifyGet` on an `IO.Ref` per record,
which is below the third decimal of a run.  Each worker keeps
its results in its own array (record index, `RecordResult`), which
is what a record's check IS: the `GroupChecked` fact of that record
or its tagged error (`ConLeche.Cached.checkRecordResult`).  The pool
merges the arrays by index into one table and walks it in record
order (`ConLeche.Cached.collectChecks`): the walk stops at the first
failing record in FOLD order, so the verdict — and the declaration the
rejection names — is the sequential walk's, `checkPendingList`'s,
whatever the workers' timing.  **Determinism on a failure**: a worker
that fails record `f` lowers the shared `limit` to `f`, and no worker
starts a record at or above the limit — every record below `f` was
claimed before `f` was (the counter is monotone) and is finished by
the worker that claimed it, so the table is complete below the first
failure; records above it may be missing, and the walk never reaches
them.  A worker cannot be cancelled mid-check (a check is a pure
computation), so the pool drains.

Each worker thread reserves 1 GiB of address space — see
`jobsCount`; the default count is the hardware thread count.

Nothing in the pool touches the driver's type: what a worker returns
carries its own evidence, and `collectChecks` assembles the
`∀ i, GroupChecked mode e i` the fully checked environment asks for
from the table alone.  The transfer theorem is untouched.

The runtime marks everything reachable from a task's closure — the
installed index and the records — for multi-threaded reference
counting once, on the first spawn (an object already marked is not
walked again); every reference-count operation on those objects is
atomic from then on, which is the pool's instruction overhead over
the sequential loop.  A plain run pays, on top of that, one atomic
claim per record; the heartbeat lane (`--progress`) pays a second
atomic increment per completed record, for an exact completed-count. -/

/-- One claimed record of one worker: below the shared `limit` it is
checked and its result appended; a failure lowers the limit to its
index; on the heartbeat lane the completed-count is bumped.  A record
at or above the limit is skipped — it is above a known failure and the
walk will never ask for it. -/
def checkOne (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Cached.DeclC} (e : ConLeche.Cached.InstalledEnv mode ds)
    (limit done : IO.Ref Nat) (k : Nat) (hk : k < e.pend.size)
    (acc : Array (Nat × ConLeche.Cached.RecordResult mode e)) :
    IO (Array (Nat × ConLeche.Cached.RecordResult mode e)) := do
  if k < (← limit.get) then
    let r := ConLeche.Cached.checkRecordResult mode e k hk
    if r matches .error _ then
      limit.modify (min · k)
    let acc := acc.push (k, r)
    if stride > 0 then
      let n ← done.modifyGet fun d => (d + 1, d + 1)
      checkHeartbeat err stride t0 e n k hk
    return acc
  else return acc

/-- One worker: claim ONE record off the shared counter, check it,
repeat until the counter is past the records.  The fuel is exact:
every claim advances the counter by exactly one, so `pend.size + 1`
claims see it past the end whatever the other workers do. -/
def checkWorker (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Cached.DeclC} (e : ConLeche.Cached.InstalledEnv mode ds)
    (next limit done : IO.Ref Nat) :
    (fuel : Nat) → Array (Nat × ConLeche.Cached.RecordResult mode e) →
      IO (Array (Nat × ConLeche.Cached.RecordResult mode e))
  | 0, acc => pure acc
  | fuel + 1, acc => do
    let k ← next.modifyGet fun a => (a, a + 1)
    if hk : k < e.pend.size then
      let acc ← checkOne mode err stride t0 e limit done k hk acc
      checkWorker mode err stride t0 e next limit done fuel acc
    else pure acc

/-- The workers' arrays merged by record index into one table. -/
def mergeResults {mode : ConLeche.CheckMode} {ds : List ConLeche.Cached.DeclC}
    {e : ConLeche.Cached.InstalledEnv mode ds}
    (tab : Array (Option (ConLeche.Cached.RecordResult mode e))) :
    List (Array (Nat × ConLeche.Cached.RecordResult mode e)) →
      Array (Option (ConLeche.Cached.RecordResult mode e))
  | [] => tab
  | rs :: rest => mergeResults (rs.foldl (fun tab (k, r) => tab.set! k (some r)) tab) rest

/-- **Phase B on a pool of `jobs` worker threads.**  Spawns
`min jobs pend.size` workers, waits for all of them, merges their
results and walks the table in record order.  A worker that failed as
an `IO` action (not a check failing — the pool's own machinery) is an
internal error, exit 3, never a verdict on the input. -/
def checkPool (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 jobs : Nat)
    {ds : List ConLeche.Cached.DeclC} (e : ConLeche.Cached.InstalledEnv mode ds) :
    IO (Except (ConLeche.CheckError × Nat) (PLift (∀ i, ConLeche.Cached.GroupChecked mode e i))) := do
  let m := e.pend.size
  let workers := max 1 (min jobs m)
  let next ← IO.mkRef 0
  let limit ← IO.mkRef m
  let done ← IO.mkRef 0
  let mut tasks : Array (Task (Except IO.Error (Array (Nat × ConLeche.Cached.RecordResult mode e)))) := #[]
  for _ in [0:workers] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated)
      (checkWorker mode err stride t0 e next limit done (m + 1) #[]))
  let mut results : List (Array (Nat × ConLeche.Cached.RecordResult mode e)) := []
  let mut failure : Option IO.Error := none
  for t in tasks do
    match ← IO.wait t with
    | .ok rs => results := rs :: results
    | .error ioe => failure := some ioe
  if let some ioe := failure then
    return .error (.internal s!"check phase: a worker failed: {ioe}", 0)
  let tab := mergeResults (Array.replicate m none) results
  return ConLeche.Cached.collectChecks mode e tab 0 (fun j hj => absurd hj (Nat.not_lt_zero j))

/-- **The driver**: `installLoop` then the check phase — `checkLoop` in
this thread at `--jobs=1`, `checkPool` otherwise — and what comes out
is the environment together with the proof that the fold `checkDecls`
(`ConLeche/Cached/Installed.lean`) returns it — the subject of the main
theorem `ConLeche.no_proof_of_False` (`ConLeche/MainTheorem.lean`).  The
loops are the fold's two phases with the heartbeat and the route trace
printed between the steps; the fully checked environment they assemble
is an accept of the fold (`ConLeche.Cached.fullyChecked_checkDecls`), so
the success line `checkMain` prints is printed from an accept of
`checkDecls` and from nothing else.  A rejection carries the fold
position of the declaration it names.  With `--progress`, one line at
the phase boundary, one when the check phase ends, and a summary with
the three phase durations (`tParse` is when the parse finished) and
the worker count. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride total t0 tParse jobs : Nat)
    (trace : Bool) (noMark : Bool)
    (inModelled : Array Name) (ds : List ConLeche.Cached.DeclC) :
    IO (Except (ConLeche.CheckError × Nat)
      { env : ConLeche.Env // ConLeche.Cached.checkDecls mode ds = .ok env }) := do
  let heartbeat (line : String) : IO Unit := do
    if stride > 0 then
      err.putStr s!"con-leche: {line}\n"
      err.flush
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  match ← installLoop mode err stride total t0 trace inModelled ds
      (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) {} ds
      (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]) {} ⟨[], rfl, .nil _ _⟩ with
  | .error e =>
    let now ← IO.monoMsNow
    heartbeat s!"install failed at {e.2}/{total} t={secs (now - t0)}s \
      (install {secs (now - tParse)}s)"
    heartbeat s!"done: parse {secs (tParse - t0)}s, install {secs (now - tParse)}s, \
      check not reached t={secs (now - t0)}s"
    return .error e
  | .ok ⟨(n, fe, pend), s, ⟨r⟩⟩ =>
    let e : ConLeche.Cached.InstalledEnv mode ds := ⟨fe, pend, ⟨n, s, r⟩⟩
    let tCheck ← IO.monoMsNow
    heartbeat s!"install done: {total}/{total} declarations installed, \
      {pend.size} checks pending t={secs (tCheck - t0)}s \
      (install {secs (tCheck - tParse)}s)"
    -- **THE PERSISTENT MARK AT THE PHASE BOUNDARY.**  The installed
    -- environment is complete and READ-ONLY from here on: every
    -- recorded check reads a prefix view of it from a fresh memo state
    -- and writes nothing back.  Handing that graph to a worker makes
    -- the runtime mark it MULTI-THREADED, and every reference count on
    -- it becomes an atomic read-modify-write on a cache line all the
    -- workers touch — pure overhead, since nothing in the graph is
    -- freed or mutated again.  Marking it PERSISTENT instead removes
    -- the counting altogether, and on the pool that is worth 19-50 % of
    -- the run's cycles and 18-32 % of its WALL TIME, growing with the
    -- worker count.  Only for the pool: in the in-thread lane the
    -- runtime's inlined single-threaded counting is nearly free and a
    -- persistent object mispredicts its `m_rc > 0` fast path, so the
    -- mark LOSES there and `--jobs=1` stays overhead-free.
    --
    -- The result is DISCARDED and the original `fe`/`pend` are what the
    -- phase below reads: `Runtime.markPersistent` is the identity on
    -- the value and marks the object graph in place, so nothing
    -- downstream — the `InstalledEnv` above, the `InstallRun` it
    -- carries — has to be transported across it, and no verdict can
    -- turn on it.  Term-level `unsafe`, the escape
    -- `Lean.Environment.finalizeImport` uses for this same call; it is
    -- unsafe only in that the marked closure is never freed, and the
    -- process exits right after.  `--no-mark-persistent` turns it off,
    -- which is how the A/B above is measured on the shipped binary.
    if jobs > 1 && !noMark then
      let _ ← unsafe Runtime.markPersistent fe
      let _ ← unsafe Runtime.markPersistent pend
    let workers := if jobs ≤ 1 then 1 else max 1 (min jobs pend.size)
    let res ← if jobs ≤ 1 then
        checkLoop mode err stride t0 e 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
      else
        checkPool mode err stride t0 jobs e
    let now ← IO.monoMsNow
    let summary := s!"done: parse {secs (tParse - t0)}s, install {secs (tCheck - tParse)}s, \
      check {secs (now - tCheck)}s, {workers} worker{if workers = 1 then "" else "s"} \
      t={secs (now - t0)}s"
    match res with
    | .error e' =>
      heartbeat s!"check failed at fold position {e'.2} t={secs (now - t0)}s \
        (check {secs (now - tCheck)}s)"
      heartbeat summary
      return .error e'
    | .ok ⟨hall⟩ =>
      heartbeat s!"check done: {pend.size}/{pend.size} t={secs (now - t0)}s \
        (check {secs (now - tCheck)}s)"
      heartbeat summary
      let fc : ConLeche.Cached.FullyChecked mode ds := ⟨e, hall⟩
      return .ok ⟨fc.env, ConLeche.Cached.fullyChecked_checkDecls mode fc⟩

/-- The progress heartbeat's stride, read off the `--progress[=<stride>]`
flag (2026-09-07; a FLAG since task #229 — it selects a run mode, the
unverified progress fold instead of the verified one, which is what
flags are for, and it was an environment variable before).  No flag is
off; bare `--progress` is stride 1.  A value that is not a decimal
numeral, and `0` — the flag asking for no heartbeat — are usage errors
(exit 3), per the provenance discipline the retired spellings follow: a
run's output must be readable off its invocation, never silently
degraded. -/
def progressStride (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--progress takes a declaration stride of at least 1 \
      (a decimal numeral); omit the flag for no heartbeat"
  | some n => .ok n
  | none => .error s!"--progress takes a declaration stride \
      (a decimal numeral of at least 1), got {repr v}"

/-- The worker count, read off the `--jobs=<n>` flag: a decimal numeral
of at least 1 (`1` is the in-thread check loop, the sequential lane —
no thread, no shared state, no multi-threaded marking).  `0` and a
non-numeral are usage errors (exit 3).  Without the flag the count is
the machine's hardware thread count (`main`).

**Address space.**  The runtime reserves one gigabyte of ADDRESS
SPACE per thread it creates (a 1 GiB anonymous mapping per worker —
its stack reservation, lazily committed: the resident set grows by
about 25 MB per worker), so a run under an address-space limit
(`ulimit -v`) can only afford so many workers — about ten under
16 GB, four under 8 GB — and past that the thread creation fails and
the runtime aborts ("failed to create thread", exit 134).  Such a run
lowers the count with the flag; the shipped default is not shaped by
a development-environment limit (user ruling, task #260), and the
project's own capped gates pass an explicit count. -/
def jobsCount (v : String) : Except String Nat :=
  match v.toNat? with
  | some 0 => .error "--jobs takes a worker count of at least 1 \
      (a decimal numeral); omit the flag for one worker per hardware thread"
  | some n => .ok n
  | none => .error s!"--jobs takes a worker count \
      (a decimal numeral of at least 1), got {repr v}"

/-- The real driver, which `main` calls in process (task #230 removed
the OOM supervisor that used to re-exec this as a child).  `mode` is
the three-mode setting (task #147), validated once by the caller and
consumed here as configuration.

**One core at two modes, one parse.**  The interned representation
and every driver over it retired with the arena (task #172), the R
core retired with the collapsed model (2026-09-05), and the
hand-written trusted twin retired into an instantiation
(2026-09-06), so the stream is parsed directly to `ExprC`
(`Frontend.parseExportStreamD`, task #171) and checked by the one
driver — `checkDeclsIO` above — at `.verified` under `--verified` (the
default), at `.trusted` under `--trusted`.  The driver returns the
environment with the proof that the fold `checkDecls` returns it, the
fold the main theorem `ConLeche.no_proof_of_False`
(`ConLeche/MainTheorem.lean`) is about; the trusted instance is
unverified by design. -/
def checkMain (file : String) (mode : CheckMode) (stride jobs : Nat)
    (noMark : Bool) : IO UInt32 := do
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
    -- The opt-in progress heartbeat (2026-09-07, `--progress[=<stride>]`):
    -- validated by the argument parse, before any work is done, and
    -- handed down as configuration.
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
      | .error (.invalid what) =>
        IO.eprintln s!"con-leche: the built-in prelude contradicts itself ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
    -- Streaming frontend (task #57, task #180): the parse reads the
    -- file line by line, so neither a wholesale text buffer nor a
    -- scratch file exists in this process.
    -- THE IN-PROCESS MODELLER (task #200; the ONLY model source, and
    -- since task #219 the only one there is): mutual and nested blocks
    -- get their `_model` family generated at parse time
    -- (`ConLeche/Frontend/InModel.lean`);
    -- `CON_LECHE_INMODEL=0` turns it off, `CON_LECHE_INMODEL_DUMP=OUT`
    -- writes the raw input with the generated records spliced in (the
    -- generator's debug gate).
    let inModel := (← IO.getEnv "CON_LECHE_INMODEL") != some "0"
    match ← parseInput file prelude inModel with
    | .error (.unsupported what) =>
      IO.eprintln s!"con-leche: declined: {what} ({modeTag})"
      return 2
    -- TASK #271 (issues #5 and #7): a stream whose inductive block
    -- contradicts its own declarations in a REDUNDANT field is
    -- rejected at the parse, as official's replay rejects a recursor
    -- or constructor record that is not the generated one.
    | .error (.invalid what) =>
      IO.eprintln s!"con-leche: invalid: {what} ({modeTag})"
      return 1
    | .error (.parseError line msg) =>
      IO.eprintln s!"con-leche: {file}:{line}: {msg}"
      return 3
    | .ok ⟨decls, taintSkipped, projRewrites, preludeCount,
           preludeDropped, hoisted, inModelled, genRecords, genOwner,
           inModelGen, inModelDeclined⟩ =>
      -- the in-process modeller's receipt (task #200)
      if inModelled.size > 0 then
        IO.eprintln s!"con-leche: {inModelled.size} inductive blocks modelled \
          in-process: {String.intercalate ", " (inModelled.toList.map toString)} \
          ({genRecords} generated records, checked by the fold as \
          declarations and not counted as records of the file)"
      -- the census (`CON_LECHE_INMODEL_CENSUS=1`): every mutual/nested block's
      -- outcome, then stop — the parse only, no fold
      if (← IO.getEnv "CON_LECHE_INMODEL_CENSUS") == some "1" then
        for (n, why) in inModelDeclined do
          IO.eprintln s!"con-leche: inmodel declined {n}: {why}"
        IO.eprintln s!"con-leche: inmodel census: {inModelled.size} modelled, \
          {inModelDeclined.size} declined ({modeTag}, parse only)"
        -- TASK #271 (issue #8): exit 2, never 0.  The census stops
        -- after the parse, so `Cached.checkDecls` never runs and there
        -- is no accepting fold to report; exit 0 is the code reserved
        -- for one, and a caller that reads the code alone would take
        -- the run for an accept.  A DECLINE is what this run is:
        -- nothing is claimed about the stream.
        return 2
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
      -- **One driver, and it returns its proof.**  `checkDeclsIO`
      -- above runs the fold's two phases — phase A installs every
      -- record and carries its accepting run, phase B checks every
      -- recorded declaration against the prefix view of the installed
      -- index and carries every check — and what comes out is the
      -- environment with the proof that `ConLeche.Cached.checkDecls`
      -- returns it, the fold the main theorem
      -- `ConLeche.no_proof_of_False` (`ConLeche/MainTheorem.lean`) is
      -- about.  The success line below is printed from that value and
      -- from nothing else.  Printing between the steps (`--progress`,
      -- the route trace) changes nothing about the proof, so there is
      -- no second loop.
      --
      -- **Reading the index**: `i` is the *fold* position, and it is
      -- NOT the stream's declaration-record index.  The parse folds
      -- the four `quot` records into one `basisDecl` and drops a few
      -- others, a taint-skipping stream loses more, and — since task
      -- #200 — the in-process modeller ADDS records the file does not
      -- contain, so the fold can run AHEAD of the file's index.
      -- Measured on raw `init-full`: 53 093 declaration records in the
      -- file against 53 118 fold positions, the +25 being
      -- `Lean.Syntax`'s generated model family (30 records) less the
      -- 5 folded and skipped ones.  Since task #219 the generated
      -- records are subtracted from the VERDICT's count (they are
      -- declarations of the fold, never records of the file) and a
      -- generated record that fails is named with its block; the fold
      -- POSITION still counts them.  The declaration NAME on the line
      -- is the portable handle.
      -- The heartbeat's first line (`--progress`): the parse is done,
      -- and the fold is about to start on this many records.  The
      -- install and check phases print their own lines
      -- (`checkDeclsIO`), and the summary closes the run.
      let tParse ← IO.monoMsNow
      if stride > 0 then
        IO.eprintln s!"con-leche: parse done: {decls.size} fold records — \
          {decls.size - preludeCount} declarations after the {preludeCount} \
          built-in prelude records ({preludeDropped} stream copies of prelude \
          records dropped) t={ConLeche.Cached.msSecs (tParse - t0)}s \
          (parse {ConLeche.Cached.msSecs (tParse - t0)}s)"
        (← IO.getStderr).flush
      let err ← IO.getStderr
      let verdict ← checkDeclsIO mode err stride decls.size t0 tParse jobs trace noMark inModelled
        decls.toList
      match verdict with
      | .ok ⟨env, _⟩ =>
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
        -- ... and minus the records the in-process modeller generated
        -- (task #219): they are checked as declarations, but they are
        -- not in the file, and the headline number is the FILE's.
        let streamRecords := decls.size - preludeCount + preludeDropped - genRecords
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
            let d := decls[i]
            match d.names.findSome? (fun n => genOwner[n]?) with
            | some T =>
              -- a record the in-process modeller generated: the file has
              -- no position for it, so the BLOCK it models is the handle
              s!" [at {declCName d}, a generated model record of \
                inductive {T}, fold position {i}]"
            | none => s!" [at {declCName d}, fold position {i}]"
          else s!" [at fold position {i}]"
        let now ← IO.monoMsNow
        IO.eprintln s!"con-leche: {e}{loc} ({modeTag}) \
          t={ConLeche.Cached.msSecs (now - t0)}s"
        taintNote
        return e.exitCode


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
  "                    certificate family runs.  The theorem: if the",
  "                    declaration fold accepts a stream in this mode",
  "                    (checkDecls .verified ds = .ok env), the",
  "                    environment env holds no constant whose type is",
  "                    False (ConLeche.no_proof_of_False,",
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
  "                    hardware thread count; --jobs=1 checks in the",
  "                    main thread with no thread and no shared state",
  "                    at all (the sequential lane a measurement is",
  "                    made on).  0 or a non-numeral is a usage error.",
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
  "                    At <n> of 2 or more the installed environment is",
  "                    marked PERSISTENT once at the phase boundary: it",
  "                    is read-only from there on, and the mark removes",
  "                    the atomic reference counting the workers would",
  "                    otherwise pay on every object of it -- worth",
  "                    18-32 % of wall time, growing with <n>.",
  "                    --jobs=1 never marks: single-threaded the",
  "                    counting is nearly free and the mark costs more",
  "                    than it saves.",
  "  --no-mark-persistent",
  "                    turn that mark off.  It changes no verdict --",
  "                    the marked graph is read-only from the boundary",
  "                    on -- so this is a MEASUREMENT switch: it is how",
  "                    the mark's effect is measured on the shipped",
  "                    binary.  At --jobs=1 there is no mark to turn",
  "                    off and the flag does nothing.",
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
  "                    ConLeche.no_proof_of_False is about) returns it;",
  "                    what it prints in between does not touch that",
  "                    type, so a run with the flag is covered exactly",
  "                    as a run without it, and so is a run on the pool.",
  "  --help            print this text on STDOUT and exit 0, in any",
  "                    argument position; no input is read.",
  "",
  "  CON_LECHE_ROUTE_TRACE=1",
  "                    the install-route audit (task #193): one",
  "                    'con-leche: route <block> <struct|sum|fix|inmodel|modeled>'",
  "                    line",
  "                    on STDERR per inductive block, naming the route",
  "                    the checker takes for it (the fixed-point route",
  "                    (task #188/#210), the in-process model (task",
  "                    #200), a pinned basis block, or 'modeled' — a",
  "                    block on NO route, which declines).",
  "                    tests/route-census.sh pins the per-route counts",
  "                    over every good fixture: no block may read",
  "                    'modeled'.",
  "                    Printed by the install phase of the one",
  "                    driver, beside the --progress heartbeat.",
  "",
  "  CON_LECHE_INMODEL=0    turn the IN-PROCESS MODELLER off (task #200).  By",
  "                    default every mutual or nested inductive block",
  "                    gets a model generated at parse time",
  "                    (ConLeche/Frontend/InModel/*) and pushed ahead of",
  "                    the block; the generated records are checked by",
  "                    the fold like any declaration -- and counted as",
  "                    what they are, declarations of the fold rather",
  "                    than records of the file, so the verdict line",
  "                    reports the file's own count (task #219).  A",
  "                    generator decline is the run's decline, naming",
  "                    the class.  The route trace reads `inmodel` for",
  "                    such a block.  DEBUG SWITCH ONLY: the in-process",
  "                    modeller is the checker's only model source --",
  "                    a stream record named `T._model` is an ordinary",
  "                    declaration and routes nothing (task #219) -- so",
  "                    with the flag off",
  "                    every mutual or nested block reaches the fold",
  "                    bare and the run declines with 'no install",
  "                    route for'.",
  "                    A verdict produced with it set is not the",
  "                    checker's verdict on the stream.",
  "  CON_LECHE_INMODEL_CENSUS=1",
  "                    report every mutual or nested block's modelling",
  "                    outcome and STOP AFTER THE PARSE.  The fold does",
  "                    not run, so nothing is checked and the run",
  "                    always EXITS 2 (declined) -- exit 0 is reserved",
  "                    for a stream the fold accepted, and a census run",
  "                    obtains no such verdict.",
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
  "inductive block is installed by the fixed-point route — structures,",
  "sums, indexed families, finitary fixed points and reflexive blocks —",
  "or through a `_model` family the frontend generates IN-PROCESS at",
  "parse time and then checks as ordinary declarations.  No model is",
  "ever read from the input (task #219): a stream record whose name",
  "carries a `_model` component is an ordinary declaration with no",
  "effect on any block.  The generator is not trusted: a wrong record",
  "is rejected or declined by the fold, never accepted; it decides",
  "coverage only.  A block no route takes declines (exit 2) naming",
  "its class.",
  "",
  "There is ONE core at two modes and one parse: the verified mode",
  "(--verified, the default) and the unverified trusted mode",
  "(--trusted).  The stream is read directly to the cached",
  "representation and checked by the one driver, which returns its",
  "environment together with the proof that the fold checkDecls — the",
  "function the main theorem ConLeche.no_proof_of_False",
  "(ConLeche/MainTheorem.lean) is stated on — returns it.",
  "",
  "RETIRED FLAGS.  --set-model, --set-model=p, --set-model=r,",
  "--no-model, --tt-model, --yolo, --infer-only, --pre, --core,",
  "--core=<c>, --install-only, --check-range and --check-range=<r>",
  "are not part of the synopsis and are never silent aliases: each is",
  "rejected with a message naming what stands in its place, and the",
  "run exits 3 without reading the input, so a verdict's provenance",
  "is readable off the invocation."]

structure Args where
  mode : ConLeche.CheckMode := .verified
  /-- The progress heartbeat's stride (`--progress[=<stride>]`, task
  #229); `0` is "no flag given", i.e. no heartbeat. -/
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
  -- The verified lane is the GRADED core since the R core's retirement
  -- (2026-09-05); `no_proof_of_Empty_cached` is its letter.
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
  -- The progress heartbeat (task #229): a FLAG, in either order with
  -- `--verified`/`--trusted`, and independent of them — it turns on
  -- the heartbeat the ONE driver prints between the steps of its two
  -- phases (`installLoop`/`checkLoop`), which is the same driver, at
  -- the same mode, as a run without it.  Bare is stride 1;
  -- `--progress=<n>` is the general form (below, with the other
  -- `=`-carrying spellings).
  | "--progress" :: rest, a => parseArgs rest { a with progress := 1 }
  -- The persistent mark is on by default on the pool; this turns it off.
  | "--no-mark-persistent" :: rest, a => parseArgs rest { a with noMark := true }
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
    else if s.startsWith "--progress=" then
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
    else if s.startsWith "--check-range=" then
      { a with bad := some "--check-range is retired; the split \
          install/check driver was arena machinery and went with the \
          interned representation (task #172)" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

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
    -- The checker runs IN THIS PROCESS.  Task #65 used to re-exec it as
    -- a supervised child so that the Lean runtime's out-of-memory
    -- handler (`lean_internal_panic_out_of_memory`, which prints
    -- "INTERNAL PANIC: out of memory" and calls `exit(1)`, uncatchable
    -- in process) could be translated from exit 1 into exit 3.  Task
    -- #230 removed that supervisor: a checker that spawns a copy of
    -- itself is not what belongs in the finished product, and an
    -- out-of-memory condition simply exits 1 with the runtime's panic
    -- message on stderr, which is what distinguishes it from a reject.
    -- `--jobs=<n>`: the check phase's worker count; without the flag,
    -- one worker per hardware thread (1 if the runtime cannot tell).
    let jobs := a.jobs.getD
      (let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
       if hw = 0 then 1 else hw)
    checkMain file a.mode a.progress jobs a.noMark
  | _ =>
    IO.eprintln usage
    return 3
