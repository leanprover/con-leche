module

public import ConLeche.Driver.Schedule.Engine
public import ConLeche.Driver.Schedule.Worker
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# The scheduler's log: its lines, reading it back, resuming from it

`--schedule-log=FILE` is an append-only log, written and flushed line by line
(`ConLeche/Driver/Schedule/Run.lean` writes it; this module holds its format and its reader).

* A finished module, `verdictLine`:
  `<verdict>\t<module>\t<ms>\t<rss>\t<at>\t<decls>\t<parse>\t<check>\t<busy>\t<slowest>\t<threads>\t<stack>`:
  the worker's wall time in ms, its peak resident set in KiB (`≥KiB`, with the sign, where it is
  the last value the scheduler sampled because the worker wrote no figure of its own), the ms
  since this run's start, and what the worker printed (`workerStats`, `-` where it printed
  nothing): its declarations, its parse and check phases in ms (to 0.1 s), its check pool's busy
  time and its slowest single check in ms, the threads the worker ran with, and the
  `LEAN_STACK_SIZE_KB` of the scheduler's environment (`-` where unset).  The field order is
  fixed; new fields go at the end.
* A kill (for memory, or by an interrupt), `killLine`:
  `killed\t<module>\t<ms>\t<rss KiB>\t<threads>`, the last sampled set and the threads the worker
  ran with (old logs have no threads field: one).
* While modules wait for room, at most once a minute, per running worker, `reserveLine`:
  `reserve\t<module>\t<age ms>\t<rss KiB>\t<reserved KiB>\t<term>` (no verdict: `parseLog` and
  `schedsim.py` skip it).

**Resuming** (`parseLog`).  A restart with the same log skips every module that has a verdict
line (the reader takes the first two fields, so old two-field logs work; a `killed` line is no
verdict and is ignored), so a run interrupted anywhere resumes where it stopped.  The verdict
`stack` is the one exception: a resumed run runs that module again where its logged stack size
differs from the current `LEAN_STACK_SIZE_KB` (a line without the field counts as different).  So
is a `memory` verdict whose threads field (the eleventh) is above 1: that module runs again at
one thread (DESIGN #595); one at one thread, or an old line without the field, stays done.

**Seeding** (`seed`; DESIGN #546): a resumed run reads the log's state back into admission: the
typical peak's window starts with the last 200 exact peaks of the verdict lines (`≥` fallbacks
left out), so that the median holds from the first tick where the log gives 20 of them; a module
with `killed` lines that still has to run keeps its position in the queue, its known size the
largest set of its kills, at least the typical peak (no doubling per logged kill), and with one
thread where a kill came with more.  Nothing else of admission is read from the log.  The log's
times feed the estimate (`Logged.msSum`, `Logged.workers`, `etaMs`).
-/

namespace ConLeche.Driver.Schedule

open ConLeche

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
def parseLog (parse : String → Option Name) (s : String) (stackKb : String := "-") : Logged :=
  -- the fold's state: the log so far, the closed runs' span, the open run's last `at`
  let (lg, span, lastAt) := (s.splitOn "\n").foldl (fun (lg, span, lastAt) l =>
    match l.splitOn "\t" with
    | w :: n :: rest =>
      if w == "reserve" then (lg, span, lastAt)  -- a snapshot, no verdict (DESIGN #571)
      else if w == "killed" then
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
        -- a `stack` verdict (the twelfth field: the stack size) holds for that size only
        -- a `memory` verdict of a worker with more than one thread is no verdict either: the
        -- module runs again at one thread (DESIGN #595), like a killed one
        let multiMem := w == "memory" && (rest[8]?.bind String.toNat?).getD 1 > 1
        let lg := if w == "stack" && rest[9]? != some stackKb then lg
          else if multiMem then
            { lg with verdicts := lg.verdicts.erase x,
                      killSize := lg.killSize.insert x
                        (max ((rest[1]?.bind String.toNat?).getD 0) (lg.killSize.getD x 0)),
                      killMulti := lg.killMulti.insert x }
          else { lg with verdicts := lg.verdicts.insert x w }
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
def readLog (parse : String → Option Name) (p : System.FilePath) (stackKb : String) :
    IO Logged := do
  if !(← p.pathExists) then return {}
  return parseLog parse (← IO.FS.readFile p) stackKb

/-- **The state a run starts from**: the never started modules, the killed ones to run again
(each at its position in the queue), their known sizes, the modules back at one thread, and the
typical peak's window with its value. -/
structure Seed where
  pending : List Name
  again : List Name
  sizes : Std.HashMap Name Nat
  single : Std.HashSet Name
  peaks : Array Nat
  typ : Nat

/-- **The seeded state** of a run whose queue is `todo` (the modules without a verdict, in the
queue's order), the typical peak `typ` until enough are known: the log's peaks (`seedPeaks`); the
modules with a logged kill unstarted again at their positions, at the largest set of their kills
(at least the typical peak), at one thread where a kill came with more. -/
def Logged.seed (lg : Logged) (todo : List Name) (typ : Nat) : Seed :=
  let (peaks, typ) := seedPeaks lg.peaks typ
  let again := todo.filter (lg.killSize.contains ·)
  { pending := todo.filter (!lg.killSize.contains ·), again, peaks, typ,
    sizes := again.foldl (fun m x => m.insert x (max typ (lg.killSize.getD x 0))) {},
    single := again.foldl (fun s x => if lg.killMulti.contains x then s.insert x else s) {} }

/-- The log's fields for `workerStats`: `\t<decls>\t<parse>\t<check>\t<busy>\t<slowest>`, `-` for
a missing one. -/
def WorkerStats.logText (s : WorkerStats) : String :=
  let f (x : Option Nat) : String := (x.map toString).getD "-"
  s!"\t{f s.decls}\t{f s.parse}\t{f s.check}\t{f s.busy}\t{f s.slowest}"

/-- A finished module's log line: its verdict `w`, its wall time `ms`, its peak `rss` (KiB, `≥`
before a sampled one), the ms since the run's start `at_`, what the worker printed, its threads
and the stack size. -/
def verdictLine (w : String) (m : Name) (ms : Nat) (rss : String) (at_ : Nat) (s : WorkerStats)
    (threads : Nat) (stackKb : String) : String :=
  s!"{w}\t{spell m}\t{ms}\t{rss}\t{at_}{s.logText}\t{threads}\t{stackKb}"

/-- A kill's log line: the module, its run time (ms), its last sampled set (KiB), its threads. -/
def killLine (m : Name) (ms rss threads : Nat) : String :=
  s!"killed\t{spell m}\t{ms}\t{rss}\t{threads}"

/-- A running worker's reservation row: the module, its age (ms), its current set and its
reservation (KiB), the term that sets it (`resTerm`). -/
abbrev ResRow := String × Nat × Nat × Nat × String

/-- A running worker's `reserve` log line, no verdict (`parseLog` skips it): the module, its age
(ms), its current set and its reservation (KiB), the term. -/
def reserveLine (r : ResRow) : String :=
  let (m, a, k, res, t) := r
  s!"reserve\t{m}\t{a}\t{k}\t{res}\t{t}"

end ConLeche.Driver.Schedule
