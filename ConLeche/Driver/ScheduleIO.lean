module

public import ConLeche.Cached.ParsedC
public import Std.Async.Signal

@[expose] public section

/-!
# The scheduler's processes (outside the theorem)

`con-leche --olean --schedule … -- ROOT` (`ConLeche/Driver/Schedule.lean`) runs one worker
process (`con-leche --olean --module`) per module of `ROOT`'s closure and aggregates their exit
codes.  This module is its runtime half, an `IO` action handed to `CheckerIO.liftIO`: no theorem
is about a `--schedule` run, and nothing here reads a file the checks read.  What it does, all of
it plain `IO`:

* **one worker per module, in any order** (the workers depend on the files only, never on each
  other's results); every module that admission lets in starts in the tick it is admitted;
* **`jobs` is the thread budget**: the running workers' threads (each worker's `--jobs`) sum to at
  most `jobs`.  A worker starts with `threadsFor`'s threads: `max 1 (min cap (decls ÷ threadDiv))`,
  `cap` (`threadCap`) the free threads less those the memory could still fill with workers (as
  many as fit into the room after this start at the typical peak, and as are queued besides it),
  `decls` the module's declarations, read just before the start off its own files
  (`Schedule.declCount`, `ConLeche/Driver/Schedule.lean`; only where `cap` is above 1).  A free thread goes to a new worker where one can start; where
  memory, not the jobs, keeps workers from starting, it goes to an extra thread of a starting
  module with many declarations: its threads share the worker's context, so a thread costs far
  less memory than a worker.  Admission counts a worker at its measured peak as before, which
  includes its threads.  A module killed while running with more than one thread runs with one
  from then on (`single`), so a heavy many-declaration module costs at most one kill before it
  runs as before;
* **workers that inherit nothing but their three standard streams**, all pipes: stdin closed at
  the start, stdout and stderr each read to the end by a thread of its own (so no worker blocks
  on a full pipe), stderr passed on for a verdict other than 0 (`WCfg`, `spawnW`);
* **a memory limit** (`memory`, KiB, 0 for none; `--schedule-memory=47G`): every tick the
  resident sets of the running workers are read (`workerRss`: the scheduler's children in `/proc/self/task/*/children`, each
  by its last argument, `/proc/<pid>/status`'s `VmRSS` and `VmHWM`, the peak so far).  The limit
  is **hard**: workers are killed only when their current sets sum to more than it.  Admission
  plans against a lower **planning budget** (`planOf`), so that growth admission could not foresee
  lands in the gap instead of causing a kill.  The gap is learned in the run: a **surprise** is how
  far the running workers' current sets ended above what admission had reserved for them when it
  last started one, the worker furthest above its own reservation left out (`surpriseOf`: one
  worker outgrowing its reservation is for the kills and the known sizes; the margin is for
  several at once), the largest over the ticks until the next start (`epMax`,
  `surprises`); the
  margin is the larger of 10 % of the limit and the 99th percentile of the last 200 surprises
  (`surpriseWindow`, the nonzero ones), and the planning budget the limit minus the margin, at
  least half the limit.
  **Admission by size**: every module has a known size: the largest resident set seen when it was
  killed, at least double its previous known size and at least the typical peak (a kill sees a
  lower bound only); a module never killed counts as the typical peak.  The typical peak is the
  median of the peaks of the last 200 finished workers, the log's recorded ones included (the limit
  divided by the jobs until 20 are known in total; the median, not a high percentile, so that a few outliers do not make
  every running and unknown module count as huge and starve the start of workers).  The room is the planning budget minus the running workers' peaks, each counted
  at least at the typical peak (a young worker has not shown its growth yet).
  **The queue is fixed**: every module has its position in the start order for the whole run;
  a killed module is unstarted again at its own position (`insertAt`), before every module after
  it.  **The head slot**: one worker, whenever it has none, runs the unstarted module of the lowest
  position (`nextHead`), whether it fits into the room or not (stderr, for a killed module back at
  the head: `head slot starts 9.1 GiB into a room of 2.0 GiB: M`), and it is never killed for
  memory.  It starts first in a tick,
  counts against the jobs like any worker, and a slot it frees goes to its next module.  Every
  other start takes the unstarted module of the lowest position that fits into the room
  (`nextFit`: a killed one at its known size, a never started one at the typical peak), taking its
  size off the room, while the jobs and the room allow.  So no module starves: each one becomes
  the lowest unstarted position in turn, and the head slot then starts it.  **Kills**: when the
  current resident sets sum to more than the hard limit, the youngest workers by start time, the
  head slot's left out (`victims`), are killed (by their own process, `Child.kill` of the child
  this scheduler started, never by a name) until the sets fit, and are unstarted again at their
  positions: not a verdict, not logged, their sizes updated.  A worker alone over the limit, the
  head slot's or another's, is killed with the verdict `memory` (running alone could not help).
  Output: a short line per kill (the module named last), and one where the head slot starts a
  killed module that does not fit;
* **a timeout per worker** (`timeout`, seconds, 0 for none): a worker running longer is killed,
  its verdict `timeout`;
* **an append-only log** (`log`), written and flushed line by line.  A finished module:
  `<verdict>\t<module>\t<ms>\t<rss>\t<at>\t<decls>\t<parse>\t<check>\t<busy>\t<slowest>\t<threads>`: the
  worker's wall time in ms, its peak resident set in KiB (`≥KiB`, with the sign, where it is the
  last value the scheduler sampled because the worker wrote no figure of its own), the ms since
  this run's start, and what the worker printed (`workerStats`, `-` where it printed nothing):
  its declarations (stdout's `accepted N declarations`), its parse and check phases in ms (the
  `stats: phases:` line, to 0.1 s), its check pool's busy time and its slowest single check in
  ms (the pool's `stats:` line and `slowest checks:`), and the threads the worker ran with.  The
  field order is fixed; new fields go at the end.  A kill (for memory, or by an
  interrupt): `killed\t<module>\t<ms>\t<rss KiB>\t<threads>`, the last sampled set and the threads the worker
  ran with (old logs have no threads field: one).  A restart with the same
  log skips every module that has a verdict line (the reader takes the first two fields, so
  old two-field logs work; a `killed` line is no verdict and is ignored), so a run interrupted
  anywhere resumes where it stopped.  **A resumed run reads the log's state back into admission**
  (`parseLog`; DESIGN #546): the typical peak's window starts with the last 200 exact peaks of the
  verdict lines (`≥` fallbacks left out), so that the median holds from the first tick where the log
  gives 20 of them; a module with `killed` lines that still has to run keeps its position in the
  queue, its known size the largest set of its kills, at least the typical peak (no
  doubling per logged kill), and with one thread where a kill came with more.  Nothing else of
  admission is read from the log;
* **statistics at the end** (stderr, `statsLines`; only this run, a resumed run says how many
  modules it skipped): the wall time; the time-weighted mean number of running workers, of the
  workers' current memory and of what admission reserved, against the jobs and the budget; where
  a declaration count was read, the workers started with more than one thread, the reads and their
  time, and the modules back at one thread after a kill; wall time and peak per module (mean, median, 90th percentile, the maximum with its module); the
  kills and the worker time lost to them; the head slot's starts that did not fit; the `memory`
  and the non-zero verdicts;
* **SIGINT and SIGTERM** (`Std.Async.Signal.Waiter`, polled every tick): no further start, every
  running worker killed through its own `Child` and waited for, logged as `killed` (no verdict),
  the log flushed, the statistics printed, and the exit code 130 (SIGINT) or 143 (SIGTERM);
* **progress**: each module's line (stdout) is `VERDICT  t=Ss  rss=X GiB  ×T  [done/total p %, k
  running, U/N threads, eta D]  M`, the module last so the statistics keep their columns (the verdict
  padded to 7, the time to 6, `X` to 5, `×T` the worker's threads where above 1, else blank, padded
  to the width of `N` and absent at `--jobs=1`, `done` to the width of `total`, `p` to 5, `k` and
  `U` to the width of `N`; `U/N threads`, the running workers' threads of the budget, only where
  they are more than the workers; only the estimate varies), `X` the worker's own peak from its stats line (`rss≥X` the last sampled one where it
  wrote none), `done` counting a resumed run's logged modules, the estimate `remaining modules × mean module time ÷ average running workers`: the mean over all
  finished modules with a known time (the log's verdict lines with the ms field, and this run's), the
  average this run's time-weighted one once it has lasted a minute and is at least 1, else the
  previous runs' from the log (Σ ms ÷ Σ each run's span, a run ending where `at` falls back), else
  `--jobs`; no estimate where no time is known.  It leans low: logged times come only from modules
  that finished, and the long ones are more often still running or interrupted; `killed` lines are
  lower bounds of modules that will run again, and are not counted
  (`progressText`; `n requeued` follows `k running`
  once a kill has put modules back); with a heartbeat (`heartbeat` ms), after that long without a
  line, three lines on stderr: `schedule: ` and the same padded counts; the memory (`memLine`):
  `mem 1.2 GiB (largest 0.6 GiB), reserved 3.0 GiB, plan 42.3 GiB of 47 GiB (typical 0.8 GiB)`,
  the running workers' total resident set now and the biggest one's, then what admission has
  reserved for them (each at the most of its peak so far, the typical peak and its known size; not
  their current use), the planning budget and the hard limit when set, and the typical peak
  admission assumes, then `n waiting for room` for the killed modules that do not fit yet; and `longest: M 7m01s`, the longest-running worker.  The
  memory is read every tick through the same `/proc` files as the budget and shown only where it
  can be read; the run's peak total ends the summary line;
* **the kill lines** (stderr): `schedule: killed at 0.4 GiB after 3m12s, requeued: M`, the worker's
  set and how long it had run (`dur`); a burst of several: `killed 2 workers, requeued: M 0.4 GiB
  after 3m12s, N 0.2 GiB after 42s`.  The log's `killed` line carries the ms as before;
* **the start order** (`--schedule-order=shuffled|graph`, default `shuffled`): the modules start
  sorted by the FNV-1a hash of their spelled names (`shuffle`), the same on every run and machine,
  so a resumed run keeps the order and skips the logged modules.  Neighbours in the graph's order are alike in size (runs of small or of big ones), which
  made the memory pressure come in waves and the modules run so far an unrepresentative sample.  `graph`
  starts them in the graph's order.  The verdicts are reported as ever, in the graph's order;
* **no worker outlives the scheduler**: a worker that cannot be started is that module's verdict
  3, with the reason, and no further one starts; the running ones are waited for.  On any other
  error the running workers are killed before the error is passed on.

A worker's verdict is its exit code (0 accept, 1 reject, 2 decline, 3 error), or `timeout`,
`memory`, or `signal` (ended otherwise); its stderr, but the statistics lines, is passed on.
-/

namespace ConLeche.Driver.Schedule

open ConLeche

/-- **The scheduler's settings.** -/
structure Opts where
  /-- the append-only log, resumed from -/
  log : Option System.FilePath := none
  /-- the hard memory limit for all running workers, KiB (0: none) -/
  memory : Nat := 0
  /-- the time limit of one worker, seconds (0: none) -/
  timeout : Nat := 0
  /-- the heartbeat: a line after this many milliseconds without one (0: none) -/
  heartbeat : Nat := 0
  /-- the start order: shuffled by a fixed hash of the names (`true`), or the graph's order -/
  shuffled : Bool := true

/-- A memory size in KiB: a number with a unit, `K`, `M`, `G` or `T` (KiB, MiB, GiB, TiB; the
lower-case letters too): `512M`, `40G`.  No unit is no size: a bare number could as well mean
bytes as MiB. -/
def parseSize (v : String) : Option Nat :=
  let unit : Option Nat := match v.back with
    | 'K' | 'k' => some 1
    | 'M' | 'm' => some 1024
    | 'G' | 'g' => some (1024 * 1024)
    | 'T' | 't' => some (1024 * 1024 * 1024)
    | _ => none
  match unit, (v.dropEnd 1).toString.toNat? with
  | some u, some n => some (n * u)
  | _, _ => none

/-- The settings, from the values of the `--schedule[-OPT=VALUE]` flags (`""` for the bare
flag, `-log=FILE`, `-memory=SIZE` (`parseSize`), `-timeout=S`, `-order=shuffled|graph`). -/
def Opts.parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | v :: vs, o =>
    let num (pre : String) (read : String → Option Nat) (what : String) (k : Nat → Opts) :
        Except String Opts :=
      let x := (v.drop pre.length).toString
      match read x with
      | some n => Opts.parse vs (k n)
      | none => .error s!"--schedule{pre.dropEnd 1} takes {what}, got \"{x}\""
    let n := "a number"
    if v == "" then Opts.parse vs o
    else if v.startsWith "-log=" then
      Opts.parse vs { o with log := some ((v.drop 5).toString : System.FilePath) }
    else if v.startsWith "-memory=" then
      num "-memory=" parseSize "a size with a unit, K, M, G or T (e.g. 512M, 40G)"
        fun n => { o with memory := n }
    else if v.startsWith "-timeout=" then num "-timeout=" String.toNat? n fun n => { o with timeout := n }
    else if v == "-order=shuffled" then Opts.parse vs { o with shuffled := true }
    else if v == "-order=graph" then Opts.parse vs { o with shuffled := false }
    else if v.startsWith "-order=" then
      .error s!"--schedule-order takes shuffled or graph, got \"{(v.drop 7).toString}\""
    else .error s!"unknown option --schedule{v}"

/-- A module's name as the command line spells it, each component escaped. -/
def spell (m : Name) : String :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  ".".intercalate ((comps m).map fun c => "«" ++ c ++ "»")

/-- The 64-bit FNV-1a hash of a string's bytes: fixed across runs and machines (no pointer, no
hash-map order). -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- The modules in a fixed pseudo-random order: by the hash of the spelled name, the name itself
breaking ties.  Neighbours in the graph's order are alike in size; this spreads them, so the
memory pressure does not come in waves and the modules run so far are a random sample, so the
estimate's cumulative rate is unbiased. -/
def shuffle (ms : List Name) : List Name :=
  (ms.toArray.map (fun m => (fnv1a (spell m), spell m, m))).qsort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)) |>.toList.map (·.2.2)

/-- A duration, `1h02m`, `12m30s` or `45s`. -/
def dur (ms : Nat) : String :=
  let s := ms / 1000
  let two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n
  if s ≥ 48 * 3600 then s!"{s / 86400}d{s % 86400 / 3600}h"
  else if s ≥ 10 * 3600 then s!"{s / 3600}h"
  else if s ≥ 3600 then s!"{s / 3600}h{two (s % 3600 / 60)}m"
  else if s ≥ 60 then s!"{s / 60}m{two (s % 60)}s"
  else s!"{s}s"

/-- The workers' standard streams, all three pipes, so that the worker inherits nothing else.
(Lean's `IO.Process.spawn` opens `/dev/null` in the child for a `.null` stream without checking
the result or closing it: the worker would inherit the open `/dev/null` descriptor, and where
the open fails, at the descriptor limit, the PARENT's stream.  A pipe is `dup2`ed from a
descriptor opened close-on-exec.) -/
abbrev WCfg : IO.Process.StdioConfig := { stdin := .piped, stdout := .piped, stderr := .piped }

/-- The running worker's streams: its stdin closed at the start (`Child.takeStdin`). -/
abbrev RCfg : IO.Process.StdioConfig := { stdin := .null, stdout := .piped, stderr := .piped }

/-- A running worker. -/
structure Running where
  m : Name
  /-- `spell m`, the worker's last argument (`/proc/<pid>/cmdline`, see `workerRss`) -/
  arg : String
  child : IO.Process.Child RCfg
  /-- its stdout and stderr, each read to the end by a thread of its own, so that no write of the
  worker ever blocks on a full pipe -/
  out : Task (Except IO.Error String)
  diag : Task (Except IO.Error String)
  start : Nat
  /-- the worker's threads (its `--jobs`) -/
  threads : Nat := 1

/-- A worker started: the binary `app` at the arguments, the last of which is `spell m`, with
`threads` threads; its stdin closed, its stdout and stderr drained. -/
def spawnW (app : System.FilePath) (m : Name) (args : Array String) (now : Nat)
    (threads : Nat := 1) : IO Running := do
  let c ← IO.Process.spawn { cmd := app.toString, args, stdin := .piped, stdout := .piped
                           , stderr := .piped : IO.Process.SpawnArgs }
  let (_, c) ← c.takeStdin
  let out ← IO.asTask (prio := .dedicated) c.stdout.readToEnd
  let diag ← IO.asTask (prio := .dedicated) c.stderr.readToEnd
  return { m, arg := spell m, child := c, out, diag, start := now, threads }

/-- What a finished worker wrote to stdout (its verdict line; read for the log's statistics,
otherwise dropped) and to stderr. -/
def Running.texts (r : Running) : IO (String × String) := do
  let out := match ← IO.wait r.out with
    | .ok s => s
    | .error _ => ""
  match ← IO.wait r.diag with
  | .ok s => pure (out, s)
  | .error e => pure (out, s!"con-leche: schedule: {r.m}: its stderr could not be read: {e}")

/-- What a finished worker wrote to stderr. -/
def Running.diagText (r : Running) : IO String := do
  return (← r.texts).2

/-- A file's contents, `none` where it cannot be read. -/
def readOpt (p : System.FilePath) : IO (Option String) := do
  try some <$> IO.FS.readFile p catch _ => pure none

/-- A size field of a `/proc/<pid>/status` in KiB (`VmRSS:`, `VmHWM:`), 0 where it has none. -/
def vmField (key : String) (s : String) : Nat :=
  match (s.splitOn "\n").find? (·.startsWith key) with
  | some l =>
    let ws := ((l.drop key.length).toString.split (fun c => c == ' ' || c == '\t')).toList.map
      (·.toString) |>.filter (· != "")
    (ws.head?.bind String.toNat?).getD 0
  | none => 0

/-- The resident set in KiB of a `/proc/<pid>/status`, 0 where it has none. -/
def vmRss (s : String) : Nat := vmField "VmRSS:" s

/-- The peak resident set so far in KiB of a `/proc/<pid>/status`, 0 where it has none. -/
def vmHwm (s : String) : Nat := vmField "VmHWM:" s

/-- A size in KiB as `X.YZ GiB`, rounded down to 0.01 GiB (the worker's own format, `peakRss`). -/
def gibText (kib : Nat) : String :=
  let x := kib * 100 / 1048576
  s!"{x / 100}.{(x % 100) / 10}{x % 10} GiB"

/-- The peak a worker reported on its stderr (`con-leche: stats: peak RSS X.YZ GiB`, from
`peakRss`, exact to 0.01 GiB) in KiB, rounded up to the next KiB so `gibText` shows it again;
`none` where the worker wrote no such line (killed or crashed). -/
def reportedPeak (msg : String) : Option Nat :=
  let key := "con-leche: stats: peak RSS "
  (msg.splitOn "\n").findSome? fun l =>
    if l.startsWith key then
      match ((l.drop key.length).toString.splitOn " ").head?.map (·.splitOn ".") with
      | some [a, b] =>
        match a.toNat?, b.toNat? with
        | some a, some b => if b < 100
            then some ((a * 100 + b) * 1048576 / 100 + 1) else none
        | _, _ => none
      | _ => none
    else none

/-- Seconds as a worker prints them (`1.234s`, `0.3s`, `12.0`), in ms; `none` where it is no such
number. -/
def secsMs (s : String) : Option Nat :=
  let s := if s.endsWith "s" then (s.dropEnd 1).toString else s
  match s.splitOn "." with
  | [a] => a.toNat?.map (· * 1000)
  | [a, b] =>
    match a.toNat?, (String.ofList ((b.toList ++ ['0', '0', '0']).take 3)).toNat? with
    | some a, some f => if b.length ≤ 3 && b.all Char.isDigit then some (a * 1000 + f) else none
    | _, _ => none
  | _ => none

/-- What a finished worker printed of its work (each `none` where it printed nothing): its own
declarations (stdout, `con-leche: accepted N declarations`), its parse and check phases (ms,
`con-leche: stats: phases: parse P (index I), check C`), its check pool's busy time and its slowest
single check (ms, the pool's `con-leche: stats: check …: … busy B …` and `con-leche: stats:
slowest checks: D …` lines). -/
structure WorkerStats where
  decls : Option Nat := none
  parse : Option Nat := none
  check : Option Nat := none
  busy : Option Nat := none
  slowest : Option Nat := none

/-- `workerStats` read from a worker's stdout `out` and stderr `diag`. -/
def workerStats (out diag : String) : WorkerStats := Id.run do
  let words (l : String) : Array String :=
    ((l.splitOn " ").filter (· != "")).toArray
  let mut s : WorkerStats := {}
  for l in out.splitOn "\n" do
    if l.startsWith "con-leche: accepted " then
      s := { s with decls := (words l)[2]?.bind String.toNat? }
  for l in diag.splitOn "\n" do
    let ws := words l
    if l.startsWith "con-leche: stats: phases: " then
      s := { s with parse := ws[4]?.bind secsMs, check := ws[8]?.bind secsMs }
    else if l.startsWith "con-leche: stats: slowest checks: " then
      s := { s with slowest := some ((ws[4]?.bind secsMs).getD 0) }
    else if l.startsWith "con-leche: stats: check" then
      match ws.findIdx? (· == "busy") with
      | some i => s := { s with busy := ws[i + 1]?.bind secsMs }
      | none => pure ()
  return s

/-- The log's fields for `workerStats`: `\t<decls>\t<parse>\t<check>\t<busy>\t<slowest>`, `-` for
a missing one. -/
def WorkerStats.logText (s : WorkerStats) : String :=
  let f (x : Option Nat) : String := (x.map toString).getD "-"
  s!"\t{f s.decls}\t{f s.parse}\t{f s.check}\t{f s.busy}\t{f s.slowest}"

/-- **The workers' resident sets**: every child of this process
(`/proc/self/task/<tid>/children`) by its last argument (`/proc/<pid>/cmdline`, a worker's
`spell m`), with its resident set and its peak so far in KiB.  Not by `Child.pid`: in Lean's runtime that function
takes the child owned and never releases it, so every call would keep the child, and its
pipes, open to the end of the run. -/
def workerRss : IO (List (String × Nat × Nat)) := do
  let mut acc := []
  for t in ← System.FilePath.readDir "/proc/self/task" do
    let some cs ← readOpt (t.path / "children") | continue
    for pid in (cs.splitOn " ").filter (· != "") do
      let some cmd ← readOpt s!"/proc/{pid}/cmdline" | continue
      let some st ← readOpt s!"/proc/{pid}/status" | continue
      match ((cmd.splitOn "\x00").filter (· != "")).getLast? with
      | some a => acc := (a, vmRss st, vmHwm st) :: acc
      | none => pure ()
  return acc

/-- `workerRss`, `none` where `/proc` cannot be read (the status line then shows no memory). -/
def workerRssOpt : IO (Option (List (String × Nat × Nat))) := do
  try some <$> workerRss catch _ => pure none

/-- KiB as GiB with one decimal (`1.2 GiB`), rounded down; below 0.1 GiB in MiB (`37 MiB`). -/
def gib (kib : Nat) : String :=
  if kib < 104858 then s!"{kib / 1024} MiB" else
  let t := kib * 10 / (1024 * 1024)
  s!"{t / 10}.{t % 10} GiB"

/-- A budget in KiB as GiB, without the decimal where it is whole (`40 GiB`, `0.5 GiB`). -/
def gibBudget (kib : Nat) : String :=
  if kib % (1024 * 1024) = 0 then s!"{kib / (1024 * 1024)} GiB" else gib kib

/-- Can `workerRss` see this process's children? -/
def childrenReadable : IO Bool := do
  try
    let ts ← System.FilePath.readDir "/proc/self/task"
    match ts[0]? with
    | some t => return (← readOpt (t.path / "children")).isSome
    | none => return false
  catch _ => return false

/-- The declarations per thread a worker's threads are counted by (`threadsFor`): calibrated
with `scripts/schedsim.py` on the Mathlib data set and its heavy variants (DESIGN #544). -/
def threadDiv : Nat := 30

/-- **The threads of a starting worker**: `max 1 (min cap (decls ÷ threadDiv))`, `cap` the
free threads (`free`, the jobs minus the running workers' threads) less those the memory could
still fill with workers: `fit` workers at the typical peak fit into the room after this one
(unbounded without a limit), and `queued` modules wait besides this one; a free thread goes to
a new worker where one can start, to an extra thread only where memory, not the jobs, keeps
workers from starting (a worker's threads share its context, so they cost far less memory than
as many workers).  `decls` is read only where `cap` is above 1. -/
def threadCap (free fit queued : Nat) : Nat :=
  free - min (free - 1) (min fit queued)

/-- `threadCap`'s threads for a module of `decls` declarations. -/
def threadsFor (cap decls : Nat) : Nat := max 1 (min cap (decls / threadDiv))

/-- **What the log holds**: the verdicts by module, and the times the estimate uses (`etaMs`). -/
structure Logged where
  /-- the verdict of each logged module -/
  verdicts : Std.HashMap Name String := {}
  /-- the wall times (ms) of the verdict lines that carry one, their sum and count -/
  msSum : Nat := 0
  msN : Nat := 0
  /-- the previous runs' time-weighted average of running workers, in thousandths: the sum of
  those times over the sum of the runs' spans (a run's span: its last `at`; a run ends where `at`
  falls back), `0` where there is none to compute -/
  workers : Nat := 0
  /-- the exact peaks (KiB) of the last `typWindow` verdict lines that carry an rss field, in
  log order (`≥` fallbacks left out): the start of the typical peak's window -/
  peaks : Array Nat := #[]
  /-- the largest resident set (KiB) at any `killed` line of each module -/
  killSize : Std.HashMap Name Nat := {}
  /-- the modules with a `killed` line that ran with more than one thread -/
  killMulti : Std.HashSet Name := {}

/-- How many finished workers' peaks the typical peak looks at. -/
def typWindow : Nat := 200

/-- The log's verdicts, by module: every line `<verdict>\t<module>(\t…)` of it, the module's name
read by `parse`; `killed` lines are no verdicts and give no time (a lower bound of a module that
will run again, and it would pull the mean below the modules that finish; their sizes and threads
are kept apart: `killSize` the largest `<rss>` (fourth field) of a module's kills, `killMulti` the
modules with a kill that ran with more than one thread (fifth field, absent in old logs: one
thread)).  The exact `<rss>` of the verdict lines (fourth field,
not `≥`) fill `peaks`, the last `typWindow` of them.  The `<ms>` of a verdict
line (the third field; old two-field lines have none) is summed for the mean module time, and with
the `<at>` (fifth field) of each run's last line gives the previous runs' average of running
workers. -/
def parseLog (parse : String → Option Name) (s : String) : Logged :=
  -- the fold's state: the log so far, the closed runs' span, the open run's last `at`
  let (lg, span, lastAt) := (s.splitOn "\n").foldl (fun (lg, span, lastAt) l =>
    match l.splitOn "\t" with
    | w :: n :: rest =>
      if w == "killed" then
        match parse n with
        | none => (lg, span, lastAt)
        | some x =>
          let k := (rest[1]?.bind String.toNat?).getD 0
          let lg := { lg with killSize := lg.killSize.insert x (max k (lg.killSize.getD x 0)),
                              killMulti := if (rest[2]?.bind String.toNat?).getD 1 > 1
                                then lg.killMulti.insert x else lg.killMulti }
          (lg, span, lastAt)
      else
      match parse n with
      | none => (lg, span, lastAt)
      | some x =>
        let lg := { lg with verdicts := lg.verdicts.insert x w }
        let lg := match rest[1]?.bind String.toNat? with
          | some k => { lg with peaks := lg.peaks.push k }
          | none => lg
        match rest[0]?.bind String.toNat? with
        | none => (lg, span, lastAt)
        | some ms =>
          let lg := { lg with msSum := lg.msSum + ms, msN := lg.msN + 1 }
          match rest[2]?.bind String.toNat? with
          | some at_ => if at_ < lastAt then (lg, span + lastAt, at_) else (lg, span, at_)
          | none => (lg, span, lastAt)
    | _ => (lg, span, lastAt)) (({} : Logged), 0, 0)
  let span := span + lastAt
  { lg with workers := if span = 0 then 0 else lg.msSum * 1000 / span,
            peaks := if lg.peaks.size > typWindow then
              lg.peaks.extract (lg.peaks.size - typWindow) lg.peaks.size else lg.peaks }

/-- `parseLog` of the log file `p`, nothing where there is none. -/
def readLog (parse : String → Option Name) (p : System.FilePath) : IO Logged := do
  if !(← p.pathExists) then return {}
  return parseLog parse (← IO.FS.readFile p)

/-- **The estimate** (ms) of the time left: `remaining × mean ÷ workers`, the mean module time
`(logged sum + this run's sum) ÷ (logged count + this run's count)` over every finished module with
a known time, `workers` the average number of running workers (in thousandths): this run's
(`runMs ÷ wall`) once the run has lasted a minute and the average is at least 1, else the previous
runs' (`logged`, also where it is below 1: a memory-bound run averages fewer than one worker), else
`jobs`.  `none` where no module has a known time. -/
def etaMs (remaining sum n runMs wall logged jobs : Nat) : Option Nat :=
  if n = 0 then none else
  let w := if wall ≥ 60000 && runMs * 1000 / wall ≥ 1000 then runMs * 1000 / wall
    else if logged > 0 then logged else jobs * 1000
  some (remaining * sum * 1000 / n / w)

/-- A finished worker of this run: its wall time (ms), its peak (KiB). -/
structure Rec where
  m : Name
  ms : Nat
  pk : Nat

/-- **The scheduler's state.** -/
structure St where
  /-- the modules never started, in the queue's order -/
  pending : List Name
  /-- the killed modules not started again, in the queue's order (each at its own position;
  their sizes are in `sizes`) -/
  again : List Name := []
  /-- the head slot's module while it runs (`nextHead`) -/
  head : Option Name := none
  /-- the known sizes (KiB) of killed modules: the set at a kill, doubled by each further one -/
  sizes : Std.HashMap Name Nat := {}
  running : Array Running := #[]
  verdicts : Std.HashMap Name String
  /-- modules with a verdict, the logged ones of a resumed run included -/
  nDone : Nat := 0
  /-- modules finished in this run, and the sum of their wall times (ms) -/
  finished : Nat := 0
  doneMs : Nat := 0
  /-- the time of the last line, module or heartbeat -/
  lastLine : Nat := 0
  /-- a worker could not be started: no more start -/
  stopped : Bool := false
  /-- the running workers' resident memory at the last tick, KiB: the total now, the largest
  now, and the sum of the peaks so far (`none`: `/proc` could not be read) -/
  mem : Option (Nat × Nat × Nat) := none
  /-- the largest total over the run, KiB -/
  peak : Nat := 0
  /-- modules put back in the queue by a kill for memory, counted with repeats -/
  requeued : Nat := 0
  /-- the kills for memory, by module -/
  kills : Std.HashMap Name Nat := {}
  /-- the largest resident set seen of each running module, KiB -/
  seen : Std.HashMap Name Nat := {}
  /-- the peaks of the last `typWindow` finished workers, KiB -/
  peaks : Array Nat := #[]
  /-- the typical peak of a worker, KiB: the median of `peaks`; before `typMin` finishes,
  the limit divided by the jobs -/
  typ : Nat := 0
  /-- the running workers' peaks each at least `typ`, at the last tick: what admission counts -/
  effPk : Nat := 0
  /-- what admission had reserved for each running worker (KiB) when it last started one -/
  resv : Std.HashMap Name Nat := {}
  /-- the largest surprise since the last start, KiB: the running workers' current sets minus
  `resv` of them, the one furthest above its own left out (`surpriseOf`) -/
  epMax : Nat := 0
  /-- the last `surpriseWindow` nonzero surprises, KiB, one per stretch between two starts -/
  surprises : Array Nat := #[]
  /-- the largest surprise of the run, KiB (statistics) -/
  surpriseTop : Nat := 0
  /-- this run's finished workers (statistics) -/
  recs : Array Rec := #[]
  /-- the time of the last tick; the sums below are weighted by the ms between ticks -/
  lastTick : Nat := 0
  /-- Σ running × ms, Σ current KiB × ms, Σ reserved KiB × ms -/
  runMs : Nat := 0
  memMs : Nat := 0
  resMs : Nat := 0
  /-- could the memory be read at some tick -/
  memSeen : Bool := false
  /-- the head slot's starts of a module that did not fit into the room -/
  headOver : Nat := 0
  /-- kills for memory and the run time of the killed; all worker run time -/
  killN : Nat := 0
  killMs : Nat := 0
  /-- workers killed by an interrupt -/
  intrN : Nat := 0
  workMs : Nat := 0
  /-- verdicts `memory`, verdicts other than 0 -/
  memVerdicts : Nat := 0
  nonzero : Nat := 0
  /-- modules killed while running with more than one thread: one thread from then on -/
  single : Std.HashSet Name := {}
  /-- workers started with more than one thread; the declaration reads (`Schedule.declCount`)
  and their time (ms) -/
  threadStarts : Nat := 0
  declReads : Nat := 0
  declMs : Nat := 0

/-- How many peaks the typical peak needs before it replaces the start value (it looks at the
last `typWindow`, and takes their median). -/
def typMin : Nat := 20

/-- The median of a window of peaks (`none` for an empty one). -/
def medianPeak (w : Array Nat) : Option Nat := (w.qsort (· < ·))[w.size / 2]?

/-- **The seeded typical peak**: the window of the log's recorded peaks and, from `typMin` of them,
their median, else the start value `typ`. -/
def seedPeaks (peaks : Array Nat) (typ : Nat) : Array Nat × Nat :=
  (peaks, if peaks.size < typMin then typ else (medianPeak peaks).getD typ)

/-- The typical peak after a finished worker's peak `pk`: the window of recent peaks and its
median (`typ` is kept while the window is short). -/
def pushPeak (peaks : Array Nat) (typ pk : Nat) : Array Nat × Nat :=
  let w := peaks.push pk
  let w := if w.size > typWindow then w.extract 1 w.size else w
  if w.size < typMin then (w, typ)
  else (w, (medianPeak w).getD typ)

/-- How many surprises the margin looks at, and its quantile (99 %: with 200, the second largest;
the largest of all kept the planning budget at its floor for long after one big module). -/
def surpriseWindow : Nat := 200
def surpriseQ : Nat := 99

/-- **A surprise** (KiB) of the running workers, each given as (its current set, what admission
reserved for it at the last start): how far their current sets sum above their reservations,
leaving out the one worker that is furthest above its own (at least 0).  One worker outgrowing
its reservation is what the kills and the known sizes handle; the margin is for several
outgrowing theirs at once.  (With that worker counted, one module of 35 GiB
counted at a typical peak of 2.8 GiB was a surprise of most of the limit, and the planning
budget sat at its floor while the rest of the memory and most of the cores stayed unused.) -/
def surpriseOf (ws : List (Nat × Nat)) : Nat :=
  let cur := ws.foldl (· + ·.1) 0
  let res := ws.foldl (· + ·.2) 0
  let top := ws.foldl (fun a (k, v) => max a (k - v)) 0
  cur - (res + top)

/-- **The planning budget** (KiB) under the hard limit `hard`: `hard - margin`, the margin the
larger of 10 % of `hard` and the `surpriseQ` percentile of the recent `surprises`, the result at
least half of `hard`.  Admission fits the running workers' reservations into it; the gap to
`hard` takes the growth admission could not foresee.  No limit: 0. -/
def planOf (hard : Nat) (surprises : Array Nat) : Nat :=
  let q := if surprises.isEmpty then 0 else
    let v := surprises.qsort (· < ·)
    (v[min (v.size - 1) (v.size * surpriseQ / 100)]?).getD 0
  max (hard / 2) (hard - min hard (max (hard / 10) q))

/-- **The head slot's next module**: the unstarted module of the lowest queue position `pos`, of
the killed ones not started again (`again`, in the queue's order) and the never started ones
(`pending`, in the queue's order), whether it fits or not. -/
def nextHead (pos : Name → Nat) (again pending : List Name) : Option Name :=
  match again.head?, pending.head? with
  | some a, some p => some (if pos p < pos a then p else a)
  | some a, none => some a
  | none, p => p

/-- **Another slot's next module**: the unstarted module of the lowest queue position that fits
into `room`, a killed one at the larger of its known size (`size`) and the typical peak `typ`, a
never started one at `typ` (so only the first of `pending` can be the one). -/
def nextFit (pos : Name → Nat) (size : Name → Nat) (typ room : Nat) (again pending : List Name) :
    Option Name :=
  let a := again.find? fun m => max typ (size m) ≤ room
  let p := if typ ≤ room then pending.head? else none
  match a, p with
  | some a, some p => some (if pos p < pos a then p else a)
  | some a, none => some a
  | none, p => p

/-- A killed module back among the unstarted ones (in the queue's order) at its own position. -/
def insertAt (pos : Name → Nat) (m : Name) : List Name → List Name
  | [] => [m]
  | x :: xs => if pos m < pos x then m :: x :: xs else x :: insertAt pos m xs

/-- **The victims of an overflow**: of the running workers (module, start time, current set), the
head slot's left out, the youngest (the latest start; on a tie the later one in the list) first,
until the current sets sum to `limit` at most. -/
def victims (ws : List (Name × Nat × Nat)) (head : Option Name) (total limit : Nat) : List Name :=
  let cs := (ws.filter fun w => some w.1 != head).reverse.mergeSort fun a b => a.2.1 ≥ b.2.1
  (cs.foldl (fun (left, acc) (m, _, k) =>
    if left > limit then (left - min left k, m :: acc) else (left, acc)) (total, [])).2.reverse

/-- `s` padded with spaces on the left to `w` characters. -/
def padL (w : Nat) (s : String) : String := "".pushn ' ' (w - s.length) ++ s

/-- `s` padded with spaces on the right to `w` characters. -/
def padR (w : Nat) (s : String) : String := s.pushn ' ' (w - s.length)

/-- The longest verdict word (`timeout`): the width of the verdict column. -/
def verdictWidth : Nat := 7

/-- The counts of a run: `[done/total p %, k running, eta D]`, as the middle of each module's line
and the heartbeat's first line, in fixed columns: `done` padded to the width of `total`, the
percentage to `100.0`, `k` to the width of `jobs`; only the estimate, last in the bracket, has a
variable width.  `done` counts the logged modules of a resumed run.  The estimate `eta` (ms, from
`etaMs`: remaining modules × mean module time ÷ average running workers) is shown where there is
one and modules are left.  The mean is taken over all finished modules with a known time, the log's
and this run's; with the shuffled order they are a sample of the whole, and the module times are
heavy-tailed (most 1 to 3 s, a few 30 to 50 minutes).  It leans low: logged times come only from
modules that finished, and the long ones are more often still running or interrupted (logged
`killed` lines, lower bounds, are not counted).  Past 48 hours it is in days and hours
(`51d16h`), from 10 hours in hours, below that with minutes (`dur`).  `T/N threads` follows `k running` where the running workers hold more threads (`T`)
than there are workers, `N` the thread budget (`jobs`), and `n requeued` (`requeued`) follows
once a kill has put modules back. -/
def progressText (total done running : Nat) (eta : Option Nat) (requeued : Nat := 0)
    (jobs : Nat := 0) (threads : Nat := 0) : String :=
  let pm := if total = 0 then 1000 else done * 1000 / total
  let eta := match eta with
    | some ms => if done ≥ total then "" else s!", eta {dur ms}"
    | none => ""
  let rq := if requeued = 0 then "" else s!", {requeued} requeued"
  let jw := (toString jobs).length
  let th := if threads ≤ running then "" else s!", {padL jw (toString threads)}/{jobs} threads"
  let w := (toString total).length
  s!"[{padL w (toString done)}/{total} {padL 5 s!"{pm / 10}.{pm % 10}"} %, \
    {padL jw (toString running)} running{th}{rq}{eta}]"

/-- A duration: seconds with a decimal below a minute, else `dur`. -/
def msText (ms : Nat) : String :=
  if ms < 60000 then s!"{ConLeche.Cached.msSecs ms}s" else dur ms

/-- The mean, median, 90th percentile and maximum (with its module) of `xs`, each shown by `fmt`. -/
def distText (xs : Array (Name × Nat)) (fmt : Nat → String) : String :=
  if xs.isEmpty then "none" else
  let v := xs.qsort (fun a b => a.2 < b.2)
  let n := v.size
  let pick (i : Nat) := fmt ((v[i]?).map (·.2) |>.getD 0)
  let (mx, mv) := (v[n - 1]?).getD (.anonymous, 0)
  s!"mean {fmt (xs.foldl (· + ·.2) 0 / n)}, median {pick (n / 2)}, p90 {pick (min (n - 1) (n * 9 / 10))}, \
    max {fmt mv} ({mx})"

/-- The run's statistics, a few lines for stderr.  `wall` is the run's time (ms), `skipped` the
modules a resumed run found logged, `signal` the signal that ended it early. -/
def statsLines (st : St) (wall jobs budget skipped : Nat) (signal : Option String) : List String :=
  let w := max 1 wall
  let tenth (x : Nat) : String := s!"{x / 10}.{x % 10}"
  let running := st.runMs * 10 / w
  let skip := if skipped = 0 then "" else s!", {skipped} skipped from the log"
  let sig := match signal with | some s => s!", interrupted by {s} ({st.intrN} running workers killed)" | none => ""
  let memL := if !st.memSeen then [] else
    let of := if budget > 0 then s!" of {gibBudget budget}" else ""
    let pl := if budget > 0 then
        s!"; plan {gib (planOf budget st.surprises)} at the end, largest surprise {gib st.surpriseTop}"
      else ""
    [s!"  memory: {gib (st.memMs / w)} in use and {gib (st.resMs / w)} reserved on average{of}{pl}"]
  let kinds := st.kills.size
  let work := max 1 st.workMs
  let lost := st.killMs * 1000 / work
  let threadsL := if st.declReads = 0 then [] else
    [s!"  threads: {st.threadStarts} workers started with more than one; {st.declReads} \
      declaration counts read in {msText st.declMs}; {st.single.size} modules back at one \
      thread after a kill"]
  [ s!"con-leche: schedule: statistics: {st.recs.size} modules run{skip}, wall {msText wall}{sig}",
    s!"  workers: {tenth running} running on average ({running * 10 / jobs} % of {jobs} threads)" ] ++
  threadsL ++
  memL ++
  [ s!"  time per module: {distText (st.recs.map fun r => (r.m, r.ms)) msText}",
    s!"  peak per module: {distText (st.recs.map fun r => (r.m, r.pk)) gib}",
    s!"  kills: {st.killN} ({kinds} modules), {msText st.killMs} lost = {lost / 10}.{lost % 10} % \
      of the worker time {msText st.workMs}; the head slot started {st.headOver} modules \
      beyond the room",
    s!"  verdicts: {st.memVerdicts} memory, {st.nonzero} not 0" ]

/-- The memory line of the heartbeat, `none` where nothing runs or `/proc` could not be read:
`mem 9.6 GiB (largest 9.1 GiB), reserved 28.5 GiB, plan 42.3 GiB of 47 GiB (typical 0.8 GiB)`.
`mem` is the running workers' total resident set now and `largest` the biggest one's now;
`reserved` is what admission counts, each running worker at the most of its peak so far, the
typical peak and its known size (not their current use), `plan` the planning budget it fits them
into (`plan`, `planOf`) and `of` the hard limit (KiB, `budget`, 0 for none: both left out).  Then
`n waiting for room` (`waiting`) where it applies. -/
def memLine (running : Nat) (mem : Option (Nat × Nat × Nat)) (typ : Nat) (budget : Nat := 0)
    (waiting : Nat := 0) (plan : Nat := 0) :
    Option String :=
  match mem with
  | some (t, m, pk) =>
    if running = 0 then none
    else
      let of := if budget > 0 then s!", plan {gib plan} of {gibBudget budget}" else ""
      let wt := if waiting = 0 then "" else s!", {waiting} waiting for room"
      some s!"mem {gib t} (largest {gib m}), reserved {gib pk}{of} (typical {gib typ}){wt}"
  | none => none

/-- **The scheduler**: the modules' workers (`args m`, the worker's arguments at `m`, of the
binary `app`; its last argument `spell m`) run as the module docstring says; the verdict of
every module of `mods`, the peak of the running workers' total resident memory in KiB
(0 where `/proc` cannot be read), and the signal that ended the run early, with its exit code. -/
def run (parse : String → Option Name) (app : System.FilePath) (args : Name → Nat → Array String)
    (decls : Name → IO (Option Nat)) (mods : Array Name) (o : Opts) (jobs : Nat) :
    IO (Std.HashMap Name String × Nat × Option (String × UInt8)) := do
  let err ← IO.getStderr
  let out ← IO.getStdout
  let logged ← match o.log with
    | some p => readLog parse p
    | none => pure {}
  let todo := (mods.toList.filter (!logged.verdicts.contains ·))
  let todo := if o.shuffled then shuffle todo else todo
  -- the queue is fixed: each module's position in it, for good
  let posMap : Std.HashMap Name Nat := (todo.foldl (fun (m, i) x => (m.insert x i, i + 1))
    (({} : Std.HashMap Name Nat), 0)).1
  let pos (m : Name) : Nat := posMap.getD m 0
  let total := mods.size
  if logged.verdicts.size > 0 then
    err.putStrLn s!"con-leche: schedule: {total - todo.length} modules logged, \
      {todo.length} to run"
  let logH ← match o.log with
    | some p => some <$> IO.FS.Handle.mk p .append
    | none => pure none
  let t0 ← IO.monoMsNow
  -- the room: the planning budget minus the running workers' peaks (no limit: unbounded)
  let planNow (st : St) : Nat := planOf o.memory st.surprises
  let roomOf (st : St) (pk : Nat) : Nat :=
    if o.memory = 0 then 1 <<< 60 else planNow st - min (planNow st) pk
  let threadsOf (st : St) : Nat := st.running.foldl (· + ·.threads) 0
  let progress (st : St) (now : Nat) : String :=
    progressText total st.nDone st.running.size
      (etaMs (total - st.nDone) (logged.msSum + st.doneMs)
        (logged.msN + st.finished) st.runMs (now - t0) logged.workers jobs) st.requeued jobs
      (threadsOf st)
  let memory (st : St) : Option String :=
    memLine st.running.size st.mem st.typ o.memory
      (if st.running.isEmpty then 0
       else (st.again.filter (st.sizes.getD · 0 > roomOf st st.effPk)).length)
      (planNow st)
  let finish (st : St) (r : Running) (w : String) : IO St := do
    let (outText, msg) ← r.texts
    let now ← IO.monoMsNow
    -- the worker's own peak where it reported one, else the last one sampled (a lower bound)
    let sampled := st.seen.getD r.m 0
    let (pk, rssText, logRss) := match reportedPeak msg with
      | some k => (k, s!"rss={padL 9 (gibText k)}", toString k)
      | none => (sampled, s!"rss≥{padL 9 (gibText sampled)}", s!"≥{sampled}")
    if let some h := logH then
      h.putStrLn s!"{w}\t{spell r.m}\t{now - r.start}\t{logRss}\t{now - t0}\
        {(workerStats outText msg).logText}\t{r.threads}"
      h.flush
    let (peaks, typ) := pushPeak st.peaks st.typ pk
    let st := { st with verdicts := st.verdicts.insert r.m w, finished := st.finished + 1, doneMs := st.doneMs + (now - r.start),
                        peaks, typ, seen := st.seen.erase r.m,
                        nDone := st.nDone + 1, lastLine := now,
                        recs := st.recs.push { m := r.m, ms := now - r.start, pk },
                        workMs := st.workMs + (now - r.start),
                        memVerdicts := st.memVerdicts + (if w == "memory" then 1 else 0),
                        nonzero := st.nonzero + (if w == "0" then 0 else 1) }
    -- the worker's threads where above 1 (`×4`), a blank column of that width otherwise; no
    -- column where the budget is one thread
    let thr := if jobs ≤ 1 then "" else
      padR ((toString jobs).length + 3) (if r.threads > 1 then s!"  ×{r.threads}" else "")
    out.putStrLn s!"{padR verdictWidth w}  t={padL 6 (ConLeche.Cached.msSecs (now - r.start))}s  \
      {rssText}{thr}  {progress st now}  {r.m}"
    out.flush
    let lines := (msg.splitOn "\n").filter fun l => l != "" && !l.startsWith "con-leche: stats:"
    if w != "0" then
      for l in lines do err.putStrLn l
      err.flush
    return st
  -- a kill's log line: the module, the run time, the last sampled resident set
  let logKill (st : St) (r : Running) (now : Nat) : IO Unit := do
    if let some h := logH then
      h.putStrLn s!"killed\t{spell r.m}\t{now - r.start}\t{st.seen.getD r.m 0}\t{r.threads}"
      h.flush
  let jobs := max 1 jobs
  -- a start: the worker's threads from `threadCap` (`cap`), the declarations read only where
  -- `cap` is above 1, one thread for a module once killed with more
  let start (st : St) (m : Name) (now : Nat) (cap : Nat) : IO St := do
    let mut st := st
    let mut t := 1
    if cap > 1 && !st.single.contains m then
      let t0 ← IO.monoMsNow
      let n ← decls m
      let t1 ← IO.monoMsNow
      st := { st with declReads := st.declReads + 1, declMs := st.declMs + (t1 - t0) }
      t := threadsFor cap (n.getD 0)
    match ← (spawnW app m (args m t) now t).toBaseIO with
    | .ok r => return { st with running := st.running.push r,
                                threadStarts := st.threadStarts + (if t > 1 then 1 else 0) }
    | .error e =>
      err.putStrLn s!"con-leche: schedule: {m}: 3: no worker started: {e}; no further \
        worker starts, the running ones are waited for"
      err.flush
      return { st with verdicts := st.verdicts.insert m "3", nDone := st.nDone + 1,
                       stopped := true, nonzero := st.nonzero + 1 }
  -- one tick: the running workers looked at, the budget, the starts, the heartbeat
  let tick (st : St) : IO St := do
    let now ← IO.monoMsNow
    let mut st := st
    -- the time-weighted sums: the state of the last tick holds until this one
    let dt := now - st.lastTick
    st := { st with lastTick := now, runMs := st.runMs + st.running.size * dt,
                    memMs := st.memMs + (st.mem.map (·.1)).getD 0 * dt,
                    resMs := st.resMs + st.effPk * dt,
                    memSeen := st.memSeen || st.mem.isSome }
    -- the resident sets, every tick, budget or not
    let rss ← workerRssOpt
    let look (l : List (String × Nat × Nat)) (r : Running) : Nat × Nat :=
      ((l.find? (·.1 == r.arg)).map (·.2)).getD (0, 0)
    let sample (rs : Array Running) : Option (Nat × Nat × Nat) := rss.map fun l =>
      rs.foldl (fun (t, m, pk) r =>
        let (k, h) := look l r
        (t + k, max m k, pk + max (max k h) (max st.typ (st.sizes.getD r.m 0)))) (0, 0, 0)
    if let some (t, _, _) := sample st.running then st := { st with peak := max st.peak t }
    -- the largest set seen of each running module, for the typical peak of the finished ones
    st := { st with seen := st.running.foldl (fun m r =>
      let (k, h) := look (rss.getD []) r
      m.insert r.m (max (m.getD r.m 0) (max k h))) st.seen }
    -- what admission counts per running worker: its peak, at least the typical peak and its
    -- known size (a worker started in this tick has no sample yet: the latter two)
    let eff1 (st : St) (r : Running) : Nat :=
      let (k, h) := look (rss.getD []) r
      max (max k h) (max st.typ (st.sizes.getD r.m 0))
    let eff (st : St) (rs : Array Running) : Nat := rs.foldl (fun a r => a + eff1 st r) 0
    let mut still : Array Running := #[]
    let mut ended : Array (Running × String) := #[]
    for r in st.running do
      match ← r.child.tryWait with
      | some c => ended := ended.push (r, if c ≤ 3 then toString c else "signal")
      | none =>
        if o.timeout > 0 && now - r.start > o.timeout * 1000 then
          r.child.kill
          let _ ← r.child.wait
          ended := ended.push (r, "timeout")
        else still := still.push r
    st := { st with running := still, mem := sample still, effPk := eff st still }
    -- the surprise: how far the current sets are above what admission reserved at its last
    -- start, the worker furthest above its own left out (`surpriseOf`)
    if o.memory > 0 then
      if let some l := rss then
        let ws := st.running.toList.map fun w => ((look l w).1, st.resv.getD w.m 0)
        st := { st with epMax := max st.epMax (surpriseOf ws) }
    for (r, w) in ended do st ← finish st r w
    -- the head slot's worker ended: the slot is free
    if let some h := st.head then
      if !st.running.any (·.m == h) then st := { st with head := none }
    if o.memory > 0 && !st.running.isEmpty then
      let rss := rss.getD []
      let cur := st.running.foldl (fun a r => a + (look rss r).1) 0
      if cur > o.memory then
        if h : st.running.size = 1 then
          -- alone over the limit: running alone could not help
          let p := st.running[0]
          p.child.kill
          let _ ← p.child.wait
          err.putStrLn s!"con-leche: schedule: memory: {gib cur} alone, over the limit of \
            {gibBudget o.memory}: {p.m}"
          err.flush
          st := { st with running := #[], head := none }
          st ← finish st p "memory"
        else
          -- the youngest workers but the head slot's make room, until the sets sum to the limit
          -- at most; each is unstarted again at its own position; one line for the burst
          let vs := victims (st.running.toList.map fun r => (r.m, r.start, (look rss r).1))
            st.head cur o.memory
          let mut killed : Array (Name × Nat × Nat) := #[]
          for v in vs do
            if let some i := st.running.findIdx? (·.m == v) then
              if h3 : i < st.running.size then
                let r := st.running[i]
                r.child.kill
                let _ ← r.child.wait
                let _ ← r.diagText
                logKill st r now
                let kr := (look rss r).1
                killed := killed.push (r.m, kr, now - r.start)
                -- the known size grows at least by doubling, and is at least the typical peak:
                -- the set at the kill is a lower bound, a restart must not die again
                let sz := max (max kr st.typ) (2 * st.sizes.getD r.m 0)
                st := { st with running := st.running.eraseIdx i,
                                sizes := st.sizes.insert r.m sz,
                                single := if r.threads > 1 then st.single.insert r.m
                                  else st.single,
                                again := insertAt pos r.m st.again,
                                requeued := st.requeued + 1, killN := st.killN + 1,
                                killMs := st.killMs + (now - r.start),
                                workMs := st.workMs + (now - r.start),
                                kills := st.kills.insert r.m ((st.kills.getD r.m 0) + 1) }
          if killed.size = 1 then
            err.putStrLn s!"con-leche: schedule: killed at \
              {gib killed[0]!.2.1} after {dur killed[0]!.2.2}, requeued: {killed[0]!.1}"
          else if killed.size > 1 then
            let items := ", ".intercalate (killed.toList.map fun (m, k, a) => s!"{m} {gib k} after {dur a}")
            err.putStrLn s!"con-leche: schedule: killed {killed.size} workers, \
              requeued: {items}"
          err.flush
    -- starts: first the head slot, where it has no worker: the unstarted module of the lowest
    -- position, fitting or not; then, while the jobs allow, the unstarted module of the lowest
    -- position that fits into the room (the planning budget minus the running workers'
    -- reservations), each taking its size off the room
    let now ← IO.monoMsNow
    -- a module out of the unstarted ones: a killed one, or the first never started one
    let take (st : St) (m : Name) : St :=
      { st with again := st.again.erase m,
                pending := if st.pending.head? == some m then st.pending.tail else st.pending }
    if st.stopped then
      st := { st with pending := [], again := [] }
    else
      let mut room := roomOf st (eff st st.running)
      let mut started := false
      -- the threads a start may take (`threadCap`): the free ones less those the room could still
      -- fill with workers at the typical peak, as many as are queued besides it
      let capOf (st : St) (room : Nat) : Nat :=
        let fit := if o.memory = 0 || st.typ = 0 then jobs else room / st.typ
        threadCap (jobs - threadsOf st) fit (total - st.nDone - st.running.size - 1)
      if st.head.isNone && threadsOf st < jobs then
        if let some m := nextHead pos st.again st.pending then
          let need := max st.typ (st.sizes.getD m 0)
          if o.memory > 0 && !st.running.isEmpty && need > room then
            st := { st with headOver := st.headOver + 1 }
            -- a line only for a killed module back at the head: one never started that does not
            -- fit is routine (it counts at the typical peak)
            if st.sizes.contains m then
              err.putStrLn s!"con-leche: schedule: head slot starts {gib need} into a room of \
                {gib room}: {m}"
              err.flush
          room := room - min room need
          st ← start (take st m) m now (capOf st room)
          st := { st with head := some m }
          started := true
      for _ in [0:jobs] do
        if st.stopped || threadsOf st ≥ jobs then break
        match nextFit pos (st.sizes.getD · 0) st.typ room st.again st.pending with
        | some m =>
          room := room - min room (max st.typ (st.sizes.getD m 0))
          st ← start (take st m) m now (capOf st room)
          started := true
        | none => break
      -- a start ends the stretch: its surprise is kept, and what admission reserved now is the
      -- new reference
      if started && o.memory > 0 then
        let ws := if st.epMax > 0 then st.surprises.push st.epMax else st.surprises
        let ws := if ws.size > surpriseWindow then ws.extract (ws.size - surpriseWindow) ws.size else ws
        st := { st with surprises := ws, surpriseTop := max st.surpriseTop st.epMax, epMax := 0,
                        resv := st.running.foldl (fun m r => m.insert r.m (eff1 st r)) {} }
    -- the heartbeat: after `heartbeat` ms without a line, the counts and the longest runs
    if o.heartbeat > 0 && now - st.lastLine ≥ o.heartbeat && !st.running.isEmpty then
      let longest := (st.running.qsort (fun a b => a.start < b.start)).toList.take 1
      let ls := ", ".intercalate (longest.map fun r => s!"{r.m} {dur (now - r.start)}")
      st := { st with mem := sample st.running }
      err.putStrLn s!"schedule: {progress st now}"
      if let some l := memory st then err.putStrLn s!"  {l}"
      err.putStrLn s!"  longest: {ls}"
      err.flush
      st := { st with lastLine := now }
    return st
  -- the log's state read back (DESIGN #546): the typical peak's window; the modules killed before
  -- that still have to run keep their positions, with their known sizes, and run with one thread
  -- where the kill came with more
  let (peaks0, typ0) := seedPeaks logged.peaks (o.memory / jobs)
  let again := todo.filter (logged.killSize.contains ·)
  let st0 : St := { pending := todo.filter (!logged.killSize.contains ·), again,
                    verdicts := logged.verdicts, peaks := peaks0, typ := typ0,
                    sizes := again.foldl (fun m x =>
                      m.insert x (max typ0 (logged.killSize.getD x 0))) {},
                    single := again.foldl (fun s x =>
                      if logged.killMulti.contains x then s.insert x else s) {} }
  if peaks0.size > 0 || !again.isEmpty then
    err.putStrLn s!"con-leche: schedule: from the log: {peaks0.size} peaks (typical peak \
      {gib typ0}), {again.length} killed modules to run again"
  let stRef ← IO.mkRef { st0 with nDone := total - todo.length, lastLine := t0, lastTick := t0 }
  -- SIGINT and SIGTERM, polled every tick; where they cannot be set up the run has no handler
  let sigs : Array (Std.Async.AsyncTask Int × String × UInt8) ←
    try
      let mkW (s : Std.Async.Signal) (name : String) (code : UInt8) := do
        let w ← Std.Async.Signal.Waiter.mk s false
        return ((← w.wait), name, code)
      pure #[← mkW .sigint "SIGINT" 130, ← mkW .sigterm "SIGTERM" 143]
    catch _ => pure #[]
  let rec loop : Nat → IO (Option (String × UInt8))
    | 0 => pure none
    | fuel + 1 => do
      let st ← stRef.get
      if st.running.isEmpty && st.pending.isEmpty && st.again.isEmpty then return none
      for (t, name, code) in sigs do
        if (← t.getState) matches IO.TaskState.finished then return some (name, code)
      stRef.set (← tick st)
      IO.sleep 50
      loop fuel
  let mut intr : Option (String × UInt8) := none
  try
    intr ← loop (1 <<< 62)
  catch e =>
    -- no worker outlives the scheduler: every running one is killed, by its own child
    let st ← stRef.get
    err.putStrLn s!"con-leche: schedule: stopped by an error: {e}; killing the \
      {st.running.size} running workers"
    err.flush
    for r in st.running do
      try r.child.kill; let _ ← r.child.wait catch _ => pure ()
    throw e
  let mut st ← stRef.get
  if let some (name, _) := intr then
    -- no further start; every running worker killed by its own child, logged as killed (no
    -- verdict), the log flushed
    let now ← IO.monoMsNow
    err.putStrLn s!"con-leche: schedule: {name}: killing the {st.running.size} running workers"
    err.flush
    for r in st.running do
      try r.child.kill; let _ ← r.child.wait catch _ => pure ()
      logKill st r now
      st := { st with workMs := st.workMs + (now - r.start) }
    st := { st with running := #[], intrN := st.running.size }
  let now ← IO.monoMsNow
  for l in statsLines st (now - t0) jobs o.memory (total - todo.length) (intr.map (·.1)) do
    err.putStrLn l
  err.flush
  return (st.verdicts, st.peak, intr)

/-- **The run's verdict**: 0 when every module's worker answered 0; else the first module in
the graph's order that did not, its code (`timeout`, `memory`, `signal`: 3). -/
def summary (mods : Array Name) (vs : Std.HashMap Name String) (modeTag : String)
    (peak : Nat := 0) : IO UInt8 := do
  let peakText := if peak = 0 then "" else s!"; peak {gib peak} of the running workers"
  let bad := mods.filter fun m => (vs[m]?).getD "missing" != "0"
  match bad[0]? with
  | none =>
    let o ← IO.getStdout
    o.putStrLn s!"con-leche: accepted {mods.size} modules, one worker each ({modeTag}){peakText}"
    o.flush
    return 0
  | some m =>
    let w := (vs[m]?).getD "missing"
    let e ← IO.getStderr
    let unrun := (bad.filter fun m => !vs.contains m).size
    let unrunText := if unrun = 0 then "" else s!" ({unrun} not run)"
    e.putStrLn s!"con-leche: {bad.size} of {mods.size} modules not accepted{unrunText}; the \
      first in the graph's order: {m} ({w}) ({modeTag}){peakText}"
    e.flush
    return match w with
      | "1" => 1
      | "2" => 2
      | _ => 3

/-- **The scheduler's run**: the workers of `mods`, this binary at the arguments `args m`
(`run`), then the verdict (`summary`). -/
def runAll (parse : String → Option Name) (args : Name → Nat → Array String)
    (decls : Name → IO (Option Nat)) (mods : Array Name) (o : Opts) (jobs : Nat)
    (modeTag : String) : IO UInt8 := do
  if o.memory > 0 && !(← childrenReadable) then
    let e ← IO.getStderr
    e.putStrLn "con-leche: --schedule-memory reads the workers' resident sets through \
      /proc/self/task/<tid>/children, which this system does not provide"
    return 3
  let (vs, peak, intr) ← run parse (← IO.appPath) args decls mods o jobs
  match intr with
  | some (name, code) =>
    let e ← IO.getStderr
    e.putStrLn s!"con-leche: interrupted by {name}: {vs.size} of {mods.size} modules have a verdict"
    e.flush
    return code
  | none => summary mods vs modeTag peak

end ConLeche.Driver.Schedule
