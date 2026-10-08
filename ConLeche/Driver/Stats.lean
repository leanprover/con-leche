module

public import Init.System.IO

/-!
# Run statistics on stderr (task #329)

The end-of-run summary every run prints on stderr — the slowest
installs and checks, each pool's utilisation and its tail, the peak
resident set — and the `--progress` heartbeat's in-flight report (how
many workers are busy, and the oldest record one of them is on).

**Performance-only IO.**  Nothing here is read by anything that
decides a verdict: the statistics are accumulated beside the loops
that carry the proofs, and printed after the verdict is known.  They
change neither stdout nor the exit code.

**Cost.**  Per record two monotonic clock reads (`IO.monoNanosNow`,
a vDSO `clock_gettime`) and one update of the worker's OWN `WStats`,
a value threaded through the worker's loop (or, where a loop's type
is fixed by its proof, a ref only that thread touches); the workers'
statistics are merged after the pool ends, so no state is shared per
record.  The heartbeat's in-flight report is the exception, and it
exists only on the `--progress` lane: there each worker publishes the
record it starts and when (`Live`, one pair of scalar refs per
worker, written by that worker only, read by whoever prints a line).
-/

@[expose] public section

namespace ConLeche.Driver

/-- How many of the slowest records each pool remembers. -/
def statsTopN : Nat := 5

/-- One worker's timing: records done, busy nanoseconds, the slowest
records as `(nanoseconds, record)` in descending order (at most
`statsTopN`), and its latest record with its start and end. -/
structure WStats where
  n : Nat := 0
  busy : Nat := 0
  top : Array (Nat × Nat) := #[]
  lastK : Nat := 0
  lastStart : Nat := 0
  lastEnd : Nat := 0
  deriving Inhabited

/-- Insert `(d, k)` into a descending top list, keeping `statsTopN`. -/
def insertTop (top : Array (Nat × Nat)) (d k : Nat) : Array (Nat × Nat) :=
  let pos := (top.findIdx? (fun e => d > e.1)).getD top.size
  if pos ≥ statsTopN then top
  else ((top.extract 0 pos).push (d, k) ++ top.extract pos top.size).extract 0 statsTopN

/-- Record `k`, run from `t0` to `t1` (nanoseconds). -/
@[inline] def WStats.add (s : WStats) (k t0 t1 : Nat) : WStats :=
  let d := t1 - t0
  let top := if s.top.size < statsTopN || d > (s.top.back?.map (·.1)).getD 0
    then insertTop s.top d k else s.top
  { n := s.n + 1, busy := s.busy + d, top, lastK := k, lastStart := t0, lastEnd := t1 }

/-- A pool's report: its window (nanoseconds), worker count and the
workers' statistics (a commit thread that installs records itself is
one more entry). -/
structure PoolRep where
  name : String
  workers : Nat
  tStart : Nat
  tEnd : Nat
  stats : Array WStats
  deriving Inhabited

/-- Nanoseconds as seconds, three decimals. -/
def nsSecs (ns : Nat) : String :=
  let ms := ns / 1000000
  let f := toString (ms % 1000)
  s!"{ms / 1000}.{"".pushn '0' (3 - f.length)}{f}s"

/-- A percentage with one decimal. -/
def pct (a b : Nat) : String :=
  if b = 0 then "-" else
  let p := a * 1000 / b
  s!"{p / 10}.{p % 10}%"

/-- The slowest records over all workers, descending. -/
def PoolRep.top (r : PoolRep) : Array (Nat × Nat) :=
  r.stats.foldl (fun acc s => s.top.foldl (fun acc (d, k) => insertTop acc d k) acc) #[]

/-- The pool's summary line: wall time, workers, busy time and
utilisation (busy ÷ (workers × wall)), and — at more than one worker —
the tail: from the last record's start to the end of the phase, how
many workers were still busy at that moment, and their busy time inside
the window. -/
def PoolRep.line (r : PoolRep) : String :=
  let wall := r.tEnd - r.tStart
  let busy := r.stats.foldl (· + ·.busy) 0
  let n := r.stats.foldl (· + ·.n) 0
  let base := s!"{r.name}: {nsSecs wall} wall, {r.workers} \
    worker{if r.workers = 1 then "" else "s"}, {n} records, busy {nsSecs busy} \
    ({pct busy (r.workers * wall)})"
  if r.workers ≤ 1 || n = 0 then base else
  let tc := r.stats.foldl (fun m s => if s.n > 0 then max m s.lastStart else m) r.tStart
  let live := r.stats.filter (fun s => s.n > 0 && s.lastEnd > tc)
  let inTail := live.foldl (fun a s => a + (s.lastEnd - tc)) 0
  let tail := r.tEnd - min r.tEnd tc
  s!"{base}; tail {nsSecs tail} after the last start, {live.size} busy then, \
    {nsSecs inTail} worker-time in it ({pct inTail (r.workers * tail)})"

/-- The slowest-records line, `label k` naming record `k`. -/
def PoolRep.topLine (r : PoolRep) (what : String) (label : Nat → String) : String :=
  let items := r.top.toList.map fun (d, k) => s!"{nsSecs d} {label k}"
  s!"slowest {what}: {String.intercalate "; " items}"

/-- Peak resident set (`VmHWM` in `/proc/self/status`), if readable. -/
def peakRss : IO (Option String) := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    for l in s.splitOn "\n" do
      if l.startsWith "VmHWM:" then
        let kb := ((l.drop 6).trimAscii.toString.takeWhile Char.isDigit).toString.toNat!
        let x := kb * 100 / 1048576
        return some s!"{x / 100}.{(x % 100) / 10}{x % 10} GiB"
    return none
  catch _ => return none

/-! ### The heartbeat's in-flight report (`--progress` only) -/

/-- Per worker: the record it is on, plus one (`0` when idle), and
when it started it.  Written by that worker only. -/
structure Live where
  cur : Array (IO.Ref Nat)
  start : Array (IO.Ref Nat)

def Live.new (workers : Nat) : IO Live := do
  let mut cur := #[]
  let mut start := #[]
  for _ in [0:workers] do
    cur := cur.push (← IO.mkRef 0)
    start := start.push (← IO.mkRef 0)
  return { cur, start }

/-- Worker `w` starts record `k` at `t`. -/
@[inline] def Live.begin (lv : Live) (w k t : Nat) : IO Unit := do
  if let some r := lv.start[w]? then r.set t
  if let some r := lv.cur[w]? then r.set (k + 1)

/-- Worker `w` is idle. -/
@[inline] def Live.idle (lv : Live) (w : Nat) : IO Unit := do
  if let some r := lv.cur[w]? then r.set 0

/-- ` busy=<b>/<n>, oldest <label> <age>s`: the heartbeat's suffix. -/
def Live.report (lv : Live) (label : Nat → String) : IO String := do
  let now ← IO.monoNanosNow
  let mut busy := 0
  let mut oldest : Option (Nat × Nat) := none
  for h : w in [0:lv.cur.size] do
    let c ← lv.cur[w].get
    if c > 0 then
      busy := busy + 1
      let t ← match lv.start[w]? with
        | some r => r.get
        | none => pure now
      match oldest with
      | some (t', _) => if t < t' then oldest := some (t, c - 1)
      | none => oldest := some (t, c - 1)
  match oldest with
  | some (t, k) => return s!" busy={busy}/{lv.cur.size}, oldest {label k} {nsSecs (now - min now t)}"
  | none => return s!" busy=0/{lv.cur.size}"

end ConLeche.Driver
