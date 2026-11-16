module

@[expose] public section

/-!
# The scheduler's engine: admission, kills, the head slot, the threads

The scheduler's policy as pure functions, generic in what a job is: a key `α` (the scheduler's
are modules, spelled on the command line by `Schedule.spell`), the command line that runs it
and its thread count, each the caller's.  Nothing here knows of Lean, of a worker's output or
of a process; `ConLeche/Driver/Schedule/Run.lean` runs the jobs and calls these.

* **one job per key, in any order** (the jobs depend on the files only, never on each other's
  results); every job that admission lets in starts in the tick it is admitted;
* **`jobs` is the thread budget**: the running jobs' threads sum to at most `jobs`.  A job starts
  with `threadsFor`'s threads: `max 1 (min cap (size ÷ threadDiv))`, `cap` (`threadCap`) the
  free threads less those the memory could still fill with jobs (as many as fit into the room
  after this start at the typical peak, and as are queued besides it), `size` the job's work
  (the module's declarations, read just before the start, `Schedule.declCount`; only where `cap`
  is above 1).  A free thread goes to a new job where one can start; where memory, not the
  jobs, keeps jobs from starting, it goes to an extra thread of a starting job with much work:
  its threads share the process's context, so a thread costs far less memory than a process.
  Admission counts a job at its measured (windowed) peak, which includes its threads.  A job
  killed while running with more than one thread runs with one from then on (`single`), so a
  heavy many-declaration module costs at most one kill before it runs as before;
* **a memory limit** (`memory`, KiB, 0 for none; `--schedule-memory=47G`): every tick the
  resident sets of the running jobs are read (`Schedule.workerRss`, `Proc.lean`; a job's sample
  of a tick is its `VmRSS`, or its `VmHWM` where that rose since the last tick).  The limit is
  **hard**: jobs are killed only when their current sets sum to more than it.  Admission plans
  against a lower **planning budget** (`planOf`), so that growth admission could not foresee
  lands in the gap instead of causing a kill.  The gap is learned in the run: a **surprise** is
  how far the running jobs' current sets ended above what admission had reserved for them when
  it last started one, the job furthest above its own reservation left out (`surpriseOf`: one
  job outgrowing its reservation is for the kills and the known sizes; the margin is for several
  at once), the largest over the ticks until the next start (`epMax`, `surprises`); the margin
  is the larger of 10 % of the limit and the 99th percentile of the last 200 surprises
  (`surpriseWindow`, the nonzero ones), and the planning budget the limit minus the margin, at
  least half the limit.
  **Admission by size**: every job has a known size: the largest resident set seen when it was
  killed, at least double its previous known size and at least the typical peak (a kill sees a
  lower bound only); a job never killed counts as the typical peak.  The typical peak is the
  median of the peaks of the last 200 finished jobs, the log's recorded ones included (the limit
  divided by the jobs until 20 are known in total; the median, not a high percentile, so that a
  few outliers do not make every running and unknown job count as huge and starve the start of
  jobs).  The room is the planning budget minus the running jobs' reservations: each job's
  **windowed peak**, its largest sample over the last `peakWindow` (5) minutes of its run
  (`pushMinute`, not its peak so far: a job that fell back from a peak frees the room; DESIGN
  #567), at least the typical peak (a young job has not shown its growth yet) and its known size.
  **The queue is fixed**: every job has its position in the start order for the whole run; a
  killed job is unstarted again at its own position (`insertAt`), before every job after it.
  **The head slot**: one job, whenever it has none, runs the unstarted job of the lowest position
  (`nextHead`), whether it fits into the room or not, and it is never killed for memory.  It
  starts first in a tick, counts against the jobs like any job, and a slot it frees goes to its
  next job.  Every other start takes the unstarted job of the lowest position that fits into the
  room (`nextFit`: a killed one at its known size, a never started one at the typical peak),
  taking its size off the room, while the jobs and the room allow.  So no job starves: each one
  becomes the lowest unstarted position in turn, and the head slot then starts it.  **Kills**:
  when the current resident sets sum to more than the hard limit, the youngest jobs by start
  time, the head slot's left out (`victims`), are killed until the sets fit, and are unstarted
  again at their positions: not a verdict, their sizes updated.  A job alone over the limit, the
  head slot's or another's, is killed with the verdict `memory` (running alone could not help)
  where it runs one thread; with more threads it is killed and queued again at one thread
  (`aloneAct`; DESIGN #595: its threads' memos add up, one thread can need far less);
* **the start order** (`--schedule-order=shuffled|graph`, default `shuffled`): the jobs start
  sorted by the FNV-1a hash of their spelled keys (`shuffle`), the same on every run and machine,
  so a resumed run keeps the order and skips the logged jobs.  Neighbours in the graph's order
  are alike in size (runs of small or of big ones), which made the memory pressure come in waves
  and the jobs run so far an unrepresentative sample.  `graph` starts them in the graph's order.
-/

namespace ConLeche.Driver.Schedule

/-- The 64-bit FNV-1a hash of a string's bytes: fixed across runs and machines (no pointer, no
hash-map order). -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

/-- The jobs in a fixed pseudo-random order: by the hash of each one's spelling `key`, the
spelling itself breaking ties.  Neighbours in the graph's order are alike in size; this spreads
them, so the memory pressure does not come in waves and the jobs run so far are a random
sample, so the estimate's cumulative rate is unbiased. -/
def shuffle {α : Type} (key : α → String) (ms : List α) : List α :=
  (ms.toArray.map (fun m => (fnv1a (key m), key m, m))).qsort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)) |>.toList.map (·.2.2)

/-- **How many minutes a running job's peak looks back** (DESIGN #567): admission counts a
running job at its largest sample of the current minute of its run and the `peakWindow`
before it, not at its peak so far.  Workers that rise and fall (CFSG's went 13.5 → 1.1 → 11.4
GiB) held most of the reservation above the current sets with their all-time peaks; with 5
minutes the simulated CFSG-like runs of sawtooth workers were 8 % shorter, at 24 % more kills and
5 % more worker time lost (`scripts/schedsim.py --window-compare`). -/
def peakWindow : Nat := 5

/-- A running job's per-minute samples after a sample `k` (KiB) in minute `mi` of its run: the
minute's largest sample, the minutes before `mi - peakWindow` dropped. -/
def pushMinute (ring : Array (Nat × Nat)) (mi k : Nat) : Array (Nat × Nat) :=
  let ring := match ring.back? with
    | some (m, x) => if m == mi then ring.pop.push (m, max x k) else ring.push (mi, k)
    | none => ring.push (mi, k)
  ring.filter (fun (m, _) => m + peakWindow ≥ mi)

/-- The windowed peak of a running job's per-minute samples (0 for none). -/
def windowPeak (ring : Array (Nat × Nat)) : Nat := ring.foldl (fun a (_, x) => max a x) 0

/-- What a job alone over the memory limit gets (DESIGN #595): with one thread the verdict
`memory`, with more it is killed and queued again at one thread (its threads each hold memos of
their own, so one thread can need far less). -/
inductive AloneAct where
  | memory
  | requeueSingle
  deriving DecidableEq

/-- `AloneAct` of a job alone over the limit with `threads` threads. -/
def aloneAct (threads : Nat) : AloneAct := if threads > 1 then .requeueSingle else .memory

/-- The work units (declarations) per thread a job's threads are counted by (`threadsFor`):
calibrated with `scripts/schedsim.py` on the Mathlib data set and its heavy variants (DESIGN
#544). -/
def threadDiv : Nat := 30

/-- **The threads of a starting job**: `max 1 (min cap (size ÷ threadDiv))`, `cap` the free
threads (`free`, the jobs minus the running jobs' threads) less those the memory could still
fill with jobs: `fit` jobs at the typical peak fit into the room after this one (unbounded
without a limit), and `queued` jobs wait besides this one; a free thread goes to a new job where
one can start, to an extra thread only where memory, not the jobs, keeps jobs from starting (a
job's threads share its context, so they cost far less memory than as many jobs).  The size is
read only where `cap` is above 1. -/
def threadCap (free fit queued : Nat) : Nat :=
  free - min (free - 1) (min fit queued)

/-- `threadCap`'s threads for a job of `decls` work units. -/
def threadsFor (cap decls : Nat) : Nat := max 1 (min cap (decls / threadDiv))

/-- How many finished jobs' peaks the typical peak looks at. -/
def typWindow : Nat := 200

/-- How many peaks the typical peak needs before it replaces the start value (it looks at the
last `typWindow`, and takes their median). -/
def typMin : Nat := 20

/-- The median of a window of peaks (`none` for an empty one). -/
def medianPeak (w : Array Nat) : Option Nat := (w.qsort (· < ·))[w.size / 2]?

/-- **The seeded typical peak**: the window of the log's recorded peaks and, from `typMin` of them,
their median, else the start value `typ`. -/
def seedPeaks (peaks : Array Nat) (typ : Nat) : Array Nat × Nat :=
  (peaks, if peaks.size < typMin then typ else (medianPeak peaks).getD typ)

/-- The typical peak after a finished job's peak `pk`: the window of recent peaks and its
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

/-- **A surprise** (KiB) of the running jobs, each given as (its current set, what admission
reserved for it at the last start): how far their current sets sum above their reservations,
leaving out the one job that is furthest above its own (at least 0).  One job outgrowing its
reservation is what the kills and the known sizes handle; the margin is for several outgrowing
theirs at once.  (With that job counted, one module of 35 GiB counted at a typical peak of 2.8
GiB was a surprise of most of the limit, and the planning budget sat at its floor while the rest
of the memory and most of the cores stayed unused.) -/
def surpriseOf (ws : List (Nat × Nat)) : Nat :=
  let cur := ws.foldl (· + ·.1) 0
  let res := ws.foldl (· + ·.2) 0
  let top := ws.foldl (fun a (k, v) => max a (k - v)) 0
  cur - (res + top)

/-- **The planning budget** (KiB) under the hard limit `hard`: `hard - margin`, the margin the
larger of 10 % of `hard` and the `surpriseQ` percentile of the recent `surprises`, the result at
least half of `hard`.  Admission fits the running jobs' reservations into it; the gap to `hard`
takes the growth admission could not foresee.  No limit: 0. -/
def planOf (hard : Nat) (surprises : Array Nat) : Nat :=
  let q := if surprises.isEmpty then 0 else
    let v := surprises.qsort (· < ·)
    (v[min (v.size - 1) (v.size * surpriseQ / 100)]?).getD 0
  max (hard / 2) (hard - min hard (max (hard / 10) q))

/-- **The head slot's next job**: the unstarted job of the lowest queue position `pos`, of the
killed ones not started again (`again`, in the queue's order) and the never started ones
(`pending`, in the queue's order), whether it fits or not. -/
def nextHead {α : Type} (pos : α → Nat) (again pending : List α) : Option α :=
  match again.head?, pending.head? with
  | some a, some p => some (if pos p < pos a then p else a)
  | some a, none => some a
  | none, p => p

/-- **Another slot's next job**: the unstarted job of the lowest queue position that fits into
`room`, a killed one at the larger of its known size (`size`) and the typical peak `typ`, a
never started one at `typ` (so only the first of `pending` can be the one). -/
def nextFit {α : Type} (pos : α → Nat) (size : α → Nat) (typ room : Nat)
    (again pending : List α) : Option α :=
  let a := again.find? fun m => max typ (size m) ≤ room
  let p := if typ ≤ room then pending.head? else none
  match a, p with
  | some a, some p => some (if pos p < pos a then p else a)
  | some a, none => some a
  | none, p => p

/-- A killed job back among the unstarted ones (in the queue's order) at its own position. -/
def insertAt {α : Type} (pos : α → Nat) (m : α) : List α → List α
  | [] => [m]
  | x :: xs => if pos m < pos x then m :: x :: xs else x :: insertAt pos m xs

/-- **The victims of an overflow**: of the running jobs (key, start time, current set), the head
slot's left out, the youngest (the latest start; on a tie the later one in the list) first,
until the current sets sum to `limit` at most. -/
def victims {α : Type} [BEq α] (ws : List (α × Nat × Nat)) (head : Option α) (total limit : Nat) :
    List α :=
  let cs := (ws.filter fun w => some w.1 != head).reverse.mergeSort fun a b => a.2.1 ≥ b.2.1
  (cs.foldl (fun (left, acc) (m, _, k) =>
    if left > limit then (left - min left k, m :: acc) else (left, acc)) (total, [])).2.reverse

/-- **Which term sets a running job's reservation** (DESIGN #571): its current set `k` and its
windowed peak `win` (together the peak), the typical peak `typ`, its known size `size` (0: never
killed); the reservation is their largest, and the answer names the one that is it: `learned`
where the known size is strictly above the others, `window peak` where the peak is at least the
typical peak, else `typical`. -/
def resTerm (k win typ size : Nat) : String :=
  let pk := max k win
  if size > max pk typ then "learned" else if pk ≥ typ then "window peak" else "typical"

end ConLeche.Driver.Schedule
