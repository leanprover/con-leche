module

public import ConLeche.Driver.Schedule.Log
public import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# The scheduler's output: status lines, the heartbeat, the statistics

All of it pure text, printed by `ConLeche/Driver/Schedule/Run.lean`.

* **progress**: every finish line (stdout, `finishText`) and every heartbeat (stderr) starts with
  the SAME status part, in the same fixed columns (`statusText`):
  `[ 3804 ( 1.5%)  3 wrkr  25 thds  RSS 34.1G tot 27.7G biggest  15d12h eta]`: the modules with
  a verdict (a resumed run's logged ones included) and their percentage; the running workers; the
  threads they hold; the running workers' resident sets now, summed (`tot`), and the largest
  one's (`biggest`), left out where `/proc` cannot be read; the estimate.  A finish line goes on
  with `t=Ss  rss=X GiB  ×T  [FAILED V  ]M`: the time padded to 6, `X` the worker's own peak
  from its stats line (`rss≥X` the last sampled one where it wrote none), `×T` the worker's
  threads where above 1 (blank, and absent at `--jobs=1`, otherwise), then, only for a non-zero
  verdict (`1`, `2`, `3`, `timeout`, `memory`, `stack`, `oom-kill`, `signal 11 (SIGSEGV)`),
  `FAILED V` (grep `FAILED`; an accepted module shows no verdict), the module last.  The log
  keeps every verdict.
* **the heartbeat** (`heartbeat` ms): after that long without a line, ONE line on stderr: the
  status part and what explains the wait (`waitText`), `waiting: longest M 7m01s (+2 more), 13
  requeued, 5 waiting for room: reserved 43.4 GiB of plan 40.5 GiB`: the longest-running worker
  and how many others run; the modules a kill has put back; and the killed modules whose known
  size does not fit the room, with what admission has reserved for the running workers (each at
  the most of its windowed peak, the typical peak and its known size; not their current use)
  against the planning budget it fits them into (`planOf`), the last two parts only where
  non-zero.  While modules wait for room, a second, indented heartbeat line names the workers
  whose reservation is above their current set by at least 1 GiB (or 25 % and 256 MiB), largest
  excess first, at most three and `+N more`: `over-reserved: M 18.0G for 2.1G (learned,
  9h49m)`, the reservation, the set, the term that sets the reservation (`learned` the known
  size, `window peak`, `typical` peak) and the age (`overText`, DESIGN #571).
* **the estimate** `eta` (`etaMs`) is `remaining modules × mean module time ÷ average running
  workers`: the mean over all finished modules with a known time (the log's verdict lines with
  the ms field, and this run's), the average this run's time-weighted one once it has lasted a
  minute and is at least 1, else the previous runs' from the log (Σ ms ÷ Σ each run's span, a run
  ending where `at` falls back), else `--jobs`; no estimate (`?`) where no time is known.  It
  leans low: logged times come only from modules that finished, and the long ones are more often
  still running or interrupted; `killed` lines are lower bounds of modules that will run again,
  and are not counted.
* **the kill lines** (stderr, `killText`): `schedule: killed at 0.4 GiB after 3m12s, requeued: M`,
  the worker's set and how long it had run (`dur`); a burst of several: `killed 2 workers,
  requeued: M 0.4 GiB after 3m12s, N 0.2 GiB after 42s`.
* **statistics at the end** (stderr, `statsLines`; only this run, a resumed run says how many
  modules it skipped): the wall time; the time-weighted mean number of running workers, of the
  workers' current memory and of what admission reserved, against the jobs and the budget; where
  a declaration count was read, the workers started with more than one thread, the reads and
  their time, and the modules back at one thread after a kill; wall time and peak per module
  (mean, median, 90th percentile, the maximum with its module); the kills and the worker time
  lost to them; the head slot's starts that did not fit; the `memory` and the non-zero verdicts.
-/

namespace ConLeche.Driver.Schedule

open ConLeche

/-- A duration, `1h02m`, `12m30s` or `45s`. -/
def dur (ms : Nat) : String :=
  let s := ms / 1000
  let two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n
  if s ≥ 48 * 3600 then s!"{s / 86400}d{s % 86400 / 3600}h"
  else if s ≥ 10 * 3600 then s!"{s / 3600}h"
  else if s ≥ 3600 then s!"{s / 3600}h{two (s % 3600 / 60)}m"
  else if s ≥ 60 then s!"{s / 60}m{two (s % 60)}s"
  else s!"{s}s"

/-- KiB as GiB with one decimal (`1.2 GiB`), rounded down; below 0.1 GiB in MiB (`37 MiB`). -/
def gib (kib : Nat) : String :=
  if kib < 104858 then s!"{kib / 1024} MiB" else
  let t := kib * 10 / (1024 * 1024)
  s!"{t / 10}.{t % 10} GiB"

/-- A budget in KiB as GiB, without the decimal where it is whole (`40 GiB`, `0.5 GiB`). -/
def gibBudget (kib : Nat) : String :=
  if kib % (1024 * 1024) = 0 then s!"{kib / (1024 * 1024)} GiB" else gib kib

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

/-- The rows whose reservation is above the current set by a meaningful amount: at least 1 GiB, or
at least 25 % of the set and 256 MiB; the largest excess first. -/
def overRows (ws : List ResRow) : List ResRow :=
  let big := ws.filter fun (_, _, k, r, _) =>
    r ≥ k + 1048576 || (r ≥ k + 262144 && (r - k) * 4 ≥ k)
  (big.toArray.qsort fun a b => b.2.2.2.1 - b.2.2.1 < a.2.2.2.1 - a.2.2.1).toList

/-- A size in KiB as `18.0G`, tenths of GiB, `M` below 0.1 GiB. -/
def gibShort (kib : Nat) : String :=
  if kib < 104858 then s!"{kib / 1024}M" else
  let t := kib * 10 / (1024 * 1024)
  s!"{t / 10}.{t % 10}G"

/-- **The over-reserved explanation**: `over-reserved: M 18.0G for 2.1G (learned, 9h49m), … +N
more`, the (at most 3) rows of `overRows` as reservation, current set, the term and the age;
empty where there is none. -/
def overText (ws : List ResRow) : String :=
  match overRows ws with
  | [] => ""
  | rs =>
    let items := (rs.take 3).map fun (m, a, k, r, t) =>
      s!"{m} {gibShort r} for {gibShort k} ({t}, {dur a})"
    let more := if rs.length > 3 then s!" +{rs.length - 3} more" else ""
    "over-reserved: " ++ ", ".intercalate items ++ more

/-- `s` padded with spaces on the left to `w` characters. -/
def padL (w : Nat) (s : String) : String := "".pushn ' ' (w - s.length) ++ s

/-- `s` padded with spaces on the right to `w` characters. -/
def padR (w : Nat) (s : String) : String := s.pushn ' ' (w - s.length)

/-- A size in KiB as GiB with one decimal (two where `dec` is 2), without the unit, padded to a
fixed width, for the status part's columns. -/
def gibCol (dec : Nat) (kib : Nat) : String :=
  let sc := if dec = 1 then 10 else 100
  let t := kib * sc / (1024 * 1024)
  let f := if dec = 1 then s!"{t % 10}" else (if t % 100 < 10 then s!"0{t % 100}" else s!"{t % 100}")
  padL (if dec = 1 then 5 else 6) s!"{t / sc}.{f}"

/-- **The status part**, the start of every finish line (stdout) and every heartbeat (stderr), so
the first columns read the same down the terminal:
`[ 3804 ( 1.5%)  3 wrkr  25 thds  RSS 34.1G tot 27.7G biggest  15d12h eta]`.
`3804 ( 1.5%)`: the modules with a verdict, counting a resumed run's logged ones, and their
percentage of `total`; `wrkr` the running workers; `thds` the threads they hold; `RSS tot` the
running workers' resident sets now, summed, and `biggest` the largest one's (GiB; left out where
`/proc` could not be read); `eta` the estimate (`etaMs`: remaining modules × mean module time ÷
average running workers; `dur`: `51d16h` past 48 hours, `12h` from 10, below that with minutes;
`?` where no time is known, `-` once nothing is left).  It leans low: logged times come only from
modules that finished, and the long ones are more often still running or interrupted (logged
`killed` lines, lower bounds, are not counted).  Every field has a fixed width: `done` that of
`total`, the percentage `100.0`, the counts that of `jobs`, the sizes (two decimals where the limit
is under 10 GiB) and the estimate seven characters. -/
def statusText (total done running : Nat) (eta : Option Nat) (jobs threads : Nat)
    (mem : Option (Nat × Nat × Nat)) (limit : Nat) : String :=
  let pm := if total = 0 then 1000 else done * 1000 / total
  let eta := match eta with
    | some ms => if done ≥ total then "-" else dur ms
    | none => "?"
  let dec := if limit > 0 && limit < 10 * 1024 * 1024 then 2 else 1
  let g := gibCol dec
  let memT := match mem with
    | none => ""
    | some (t, m, _) =>
      let (t, m) := if running = 0 then (0, 0) else (t, m)
      s!"  RSS {g t}G tot {g m}G biggest"
  let jw := (toString jobs).length
  let w := (toString total).length
  s!"[{padL w (toString done)} ({padL 5 s!"{pm / 10}.{pm % 10}"}%)  \
    {padL jw (toString running)} wrkr  {padL jw (toString threads)} thds{memT}  \
    {padL 7 eta} eta]"

/-- A finished worker's peak: the one it reported (`reportedPeak` of its stderr `msg`), else the
last one sampled (a lower bound); with its text on the finish line and in the log. -/
def finishPeak (msg : String) (sampled : Nat) : Nat × String × String :=
  match reportedPeak msg with
  | some k => (k, s!"rss={padL 9 (gibText k)}", toString k)
  | none => (sampled, s!"rss≥{padL 9 (gibText sampled)}", s!"≥{sampled}")

/-- **A finish line** (stdout): the status part, the worker's time `ms`, its peak (`finishPeak`),
its threads where above 1 (`×4`, a blank column of that width otherwise; no column where the
budget `jobs` is one thread), `FAILED V` only for a non-zero verdict `w`, the module. -/
def finishText (status : String) (ms : Nat) (rssText : String) (jobs threads : Nat) (w : String)
    (m : Name) : String :=
  let thr := if jobs ≤ 1 then "" else
    padR ((toString jobs).length + 3) (if threads > 1 then s!"  ×{threads}" else "")
  let mark := if w == "0" then "" else s!"FAILED {w}  "
  s!"{status}  t={padL 6 (ConLeche.Cached.msSecs ms)}s  {rssText}{thr}  {mark}{m}"

/-- **What explains a wait** (the heartbeat after the status part): the longest-running worker and
its age, how many `others` run, the `requeued` modules, the killed modules `waiting` for room with
what admission `reserved` against the `plan` (where there is a limit). -/
def waitText (longest : Option (Name × Nat)) (others requeued waiting : Nat)
    (reserved plan : Option Nat) : String :=
  let more := if others > 0 then s!" (+{others} more)" else ""
  let rq := if requeued = 0 then "" else s!", {requeued} requeued"
  let room := if waiting = 0 then "" else
    let rsv := match reserved with
      | some pk => s!": reserved {gib pk}" ++ (match plan with
        | some p => s!" of plan {gib p}"
        | none => "")
      | none => ""
    s!", {waiting} waiting for room{rsv}"
  match longest with
  | some (m, age) => s!"waiting: longest {m} {dur age}{more}{rq}{room}"
  | none => "waiting"

/-- **The kill line** of a burst of kills for memory, each (module, its set, its run time); none
for no kill. -/
def killText (killed : Array (Name × Nat × Nat)) : Option String :=
  match killed.toList with
  | [] => none
  | [(m, k, a)] => some s!"con-leche: schedule: killed at {gib k} after {dur a}, requeued: {m}"
  | ks =>
    let items := ", ".intercalate (ks.map fun (m, k, a) => s!"{m} {gib k} after {dur a}")
    some s!"con-leche: schedule: killed {killed.size} workers, requeued: {items}"

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

/-- A finished worker of this run: its wall time (ms), its peak (KiB). -/
structure Rec where
  m : Name
  ms : Nat
  pk : Nat

/-- **The run's statistics so far**: what `statsLines` reports. -/
structure Stats where
  /-- this run's finished workers -/
  recs : Array Rec := #[]
  /-- Σ running × ms, Σ current KiB × ms, Σ reserved KiB × ms, weighted by the ms between ticks -/
  runMs : Nat := 0
  memMs : Nat := 0
  resMs : Nat := 0
  /-- could the memory be read at some tick -/
  memSeen : Bool := false
  /-- the largest surprise of the run, KiB -/
  surpriseTop : Nat := 0
  /-- the kills for memory, by module -/
  kills : Std.HashMap Name Nat := {}
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
  /-- workers started with more than one thread; the declaration reads (`Schedule.declCount`)
  and their time (ms) -/
  threadStarts : Nat := 0
  declReads : Nat := 0
  declMs : Nat := 0

/-- The run's statistics, a few lines for stderr.  `wall` is the run's time (ms), `budget` the
memory limit and `plan` the planning budget at the end, `singles` the modules back at one thread,
`skipped` the modules a resumed run found logged, `signal` the signal that ended it early. -/
def statsLines (st : Stats) (wall jobs budget plan singles skipped : Nat)
    (signal : Option String) : List String :=
  let w := max 1 wall
  let tenth (x : Nat) : String := s!"{x / 10}.{x % 10}"
  let running := st.runMs * 10 / w
  let skip := if skipped = 0 then "" else s!", {skipped} skipped from the log"
  let sig := match signal with | some s => s!", interrupted by {s} ({st.intrN} running workers killed)" | none => ""
  let memL := if !st.memSeen then [] else
    let of := if budget > 0 then s!" of {gibBudget budget}" else ""
    let pl := if budget > 0 then
        s!"; plan {gib plan} at the end, largest surprise {gib st.surpriseTop}"
      else ""
    [s!"  memory: {gib (st.memMs / w)} in use and {gib (st.resMs / w)} reserved on average{of}{pl}"]
  let kinds := st.kills.size
  let work := max 1 st.workMs
  let lost := st.killMs * 1000 / work
  let threadsL := if st.declReads = 0 then [] else
    [s!"  threads: {st.threadStarts} workers started with more than one; {st.declReads} \
      declaration counts read in {msText st.declMs}; {singles} modules back at one \
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

end ConLeche.Driver.Schedule
