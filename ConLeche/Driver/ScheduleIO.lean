module

public import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# The scheduler's processes (outside the theorem)

`con-leche --olean --schedule … -- ROOT` (`ConLeche/Driver/Schedule.lean`) runs one worker
process (`con-leche --olean --module`) per module of `ROOT`'s closure and aggregates their exit
codes.  This module is its runtime half, an `IO` action handed to `CheckerIO.liftIO`: no theorem
is about a `--schedule` run, and nothing here reads a file the checks read.  What it does, all of
it plain `IO`:

* **one worker per module, in any order** (the workers depend on the files only, never on each
  other's results), at most `jobs` at once, each started at least `stagger` milliseconds after
  the one before (**staggered starts**: the workers' read phases do not all peak together);
* **workers that inherit nothing but their three standard streams**, all pipes: stdin closed at
  the start, stdout and stderr each read to the end by a thread of its own (so no worker blocks
  on a full pipe), stderr passed on for a verdict other than 0 (`WCfg`, `spawnW`);
* **a memory budget** (`memory`, KiB, 0 for none; `--schedule-memory=40G`): every tick the
  resident sets of the running workers are read (`workerRss`: the scheduler's children in `/proc/self/task/*/children`, each
  by its last argument, `/proc/<pid>/status`'s `VmRSS` and `VmHWM`, the peak so far).
  **Admission by size**: every module has a known size, the largest resident set seen when it was
  killed (a lower bound of its peak), 0 while it was never killed.  The room is the budget minus
  the running workers' peaks; the first module of the queue (the killed ones, in order, then the
  others) whose size fits into the room starts, the ones that do not fit stay in their place
  (only the killed modules have a size, so the scan is over them alone); with nothing running the
  first one always starts, and then the verdict `memory` decides if it is over the budget.  **Preemption**: when the current resident sets sum to more than
  the budget and no worker is protected, **the largest worker becomes protected** (the largest
  current set, then the largest peak).  **The protection is sticky**: the protected worker stays
  protected while it runs, even when another grows larger.  Every overflow kills the youngest
  worker other than the protected one (by its own process, `Child.kill` of the child this
  scheduler started, never by a name) and puts it again at the front of the pending queue: not
  a verdict, not logged, its size updated.  Workers still start while the protected one runs,
  as the room allows (the newest are the youngest, so the first to be killed).  The protection
  ends when the protected worker finishes, or when it is killed, alone over the budget, with the
  verdict `memory` (running alone could not help).
  Output: one line when a protection begins, one when it ends, and a short line per kill;
* **a timeout per worker** (`timeout`, seconds, 0 for none): a worker running longer is killed,
  its verdict `timeout`;
* **an append-only log** (`log`): one line per finished module, `<verdict>\t<module>`, written
  and flushed as it finishes; a restart with the same log skips every module it names, so a
  run interrupted anywhere resumes where it stopped;
* **progress**: each module's line (stdout) is `M: VERDICT t=Ss [done/total p %, k running,
  eta D]`, `done` counting a resumed run's logged modules, the estimate the remaining modules at
  the finish rate of the last 200 finishes (`progressText`); with a heartbeat (`heartbeat` ms), after that
  long without a line, the same counts and the three longest-running workers (stderr); the
  running workers' total resident memory and the largest one's (and the budget, when set)
  follow `k running` (`1.2 GiB now (max 0.6 GiB), 3.0 GiB peaks of 40 GiB`; then `2 requeued`
  once a kill has put modules back, and `protecting M` while a worker is protected,
  `n waiting for room` for the killed modules that do not fit yet), read every tick through the same
  `/proc` files as the budget and shown only where they can be read; the run's peak total ends
  the summary line;
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
  /-- the memory budget for all running workers, KiB (0: none) -/
  memory : Nat := 0
  /-- the time limit of one worker, seconds (0: none) -/
  timeout : Nat := 0
  /-- the least time between two starts, milliseconds -/
  stagger : Nat := 200
  /-- the heartbeat: a line after this many milliseconds without one (0: none) -/
  heartbeat : Nat := 0

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
flag, `-log=FILE`, `-memory=SIZE` (`parseSize`), `-timeout=S`, `-stagger=MS`). -/
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
    else if v.startsWith "-stagger=" then num "-stagger=" String.toNat? n fun n => { o with stagger := n }
    else .error s!"unknown option --schedule{v}"

/-- A module's name as the command line spells it, each component escaped. -/
def spell (m : Name) : String :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  ".".intercalate ((comps m).map fun c => "«" ++ c ++ "»")

/-- A duration, `1h02m`, `12m30s` or `45s`. -/
def dur (ms : Nat) : String :=
  let s := ms / 1000
  let two (n : Nat) : String := if n < 10 then s!"0{n}" else toString n
  if s ≥ 3600 then s!"{s / 3600}h{two (s % 3600 / 60)}m"
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

/-- A worker started: the binary `app` at the arguments, the last of which is `spell m`; its
stdin closed, its stdout and stderr drained. -/
def spawnW (app : System.FilePath) (m : Name) (args : Array String) (now : Nat) :
    IO Running := do
  let c ← IO.Process.spawn { cmd := app.toString, args, stdin := .piped, stdout := .piped
                           , stderr := .piped : IO.Process.SpawnArgs }
  let (_, c) ← c.takeStdin
  let out ← IO.asTask (prio := .dedicated) c.stdout.readToEnd
  let diag ← IO.asTask (prio := .dedicated) c.stderr.readToEnd
  return { m, arg := spell m, child := c, out, diag, start := now }

/-- What a finished worker wrote to stderr (its stdout, the verdict line, is dropped). -/
def Running.diagText (r : Running) : IO String := do
  let _ ← IO.wait r.out
  match ← IO.wait r.diag with
  | .ok s => pure s
  | .error e => pure s!"con-leche: schedule: {r.m}: its stderr could not be read: {e}"

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

/-- The log's verdicts, by module: every line `<verdict>\t<module>` of it, the module's name
read by `parse`. -/
def readLog (parse : String → Option Name) (p : System.FilePath) :
    IO (Std.HashMap Name String) := do
  if !(← p.pathExists) then return {}
  let s ← IO.FS.readFile p
  return (s.splitOn "\n").foldl (fun m l =>
    match l.splitOn "\t" with
    | [w, n] => match parse n with
      | some x => m.insert x w
      | none => m
    | _ => m) {}

/-- **The scheduler's state.** -/
structure St where
  /-- the modules never killed (unknown size, 0), in order -/
  pending : List Name
  /-- the killed modules with their known sizes (KiB), in order, before `pending` -/
  front : List (Name × Nat) := []
  running : Array Running := #[]
  verdicts : Std.HashMap Name String
  lastStart : Nat := 0
  /-- modules with a verdict, the logged ones of a resumed run included -/
  nDone : Nat := 0
  /-- modules finished in this run -/
  finished : Nat := 0
  /-- the time of the last line, module or heartbeat -/
  lastLine : Nat := 0
  /-- a worker could not be started: no more start -/
  stopped : Bool := false
  /-- the running workers' resident memory at the last tick, KiB: the total now, the largest
  now, and the sum of the peaks so far (`none`: `/proc` could not be read) -/
  mem : Option (Nat × Nat × Nat) := none
  /-- the largest total over the run, KiB -/
  peak : Nat := 0
  /-- the protected worker of a memory overflow: no start while it runs -/
  prot : Option Name := none
  /-- modules put back in the queue by a kill for memory, counted with repeats -/
  requeued : Nat := 0
  /-- the kills for memory, by module -/
  kills : Std.HashMap Name Nat := {}
  /-- the times (ms since the start) of the last `etaWindow`
  finishes, and before them the start of the window (first element); `#[0]` at the start -/
  stamps : Array Nat := #[0]

/-- How many finishes the estimate looks back over. -/
def etaWindow : Nat := 200

/-- The estimate's window after a finish at active time `t` (ms since the start, the time with
): the last `etaWindow` finishes' times, with the start of the window first. -/
def pushStamp (stamps : Array Nat) (t : Nat) : Array Nat :=
  let s := stamps.push t
  if s.size > etaWindow + 1 then s.extract 1 s.size else s

/-- The progress of a run: `[done/total p %, k running, eta D]`.  `done` counts the logged
modules of a resumed run.  The estimate is the remaining modules at the finish rate of a recent
window: `window = (n, ms)`, the last `n ≤ 200` finishes of this run and the active time they took
(from the previous finish, or the start, to the last finish; a stretch without finishes does
not grow it until something finishes): `remaining × ms ÷ n`; none before the first finish.  With
`mem` (the running workers' total now, largest now and sum of peaks, KiB) and a `budget` (KiB,
0 for none): `k running, 1.2 GiB now (max 0.6 GiB), 3.0 GiB peaks of 40 GiB`; then `n requeued`
(`requeued`, when not 0), `protecting M` (`prot`) and `n waiting for room` (`waiting`). -/
def progressText (total done running : Nat) (window : Nat × Nat)
    (mem : Option (Nat × Nat × Nat) := none) (budget : Nat := 0) (requeued : Nat := 0)
    (prot : Option Name := none) (waiting : Nat := 0) : String :=
  let pm := if total = 0 then 1000 else done * 1000 / total
  let eta := if window.1 = 0 || done ≥ total then ""
    else s!", eta {dur (window.2 * (total - done) / window.1)}"
  let memText := match mem with
    | some (t, m, pk) =>
      if running = 0 then ""
      else s!", {gib t} now (max {gib m}), {gib pk} peaks\
        {if budget > 0 then s!" of {gibBudget budget}" else ""}"
    | none => ""
  let rq := if requeued = 0 then "" else s!", {requeued} requeued"
  let pz := (match prot with
    | some m => s!", protecting {m}"
    | none => "") ++ (if waiting = 0 then "" else s!", {waiting} waiting for room")
  s!"[{done}/{total} {pm / 10}.{pm % 10} %, {running} running{memText}{rq}{pz}{eta}]"

/-- **The scheduler**: the modules' workers (`args m`, the worker's arguments at `m`, of the
binary `app`; its last argument `spell m`) run as the module docstring says; the verdict of
every module of `mods`, and the peak of the running workers' total resident memory in KiB
(0 where `/proc` cannot be read). -/
def run (parse : String → Option Name) (app : System.FilePath) (args : Name → Array String)
    (mods : Array Name) (o : Opts) (jobs : Nat) : IO (Std.HashMap Name String × Nat) := do
  let err ← IO.getStderr
  let out ← IO.getStdout
  let logged ← match o.log with
    | some p => readLog parse p
    | none => pure {}
  let todo := mods.toList.filter (!logged.contains ·)
  let total := mods.size
  if logged.size > 0 then
    err.putStrLn s!"con-leche: schedule: {total - todo.length} modules logged, \
      {todo.length} to run"
  let logH ← match o.log with
    | some p => some <$> IO.FS.Handle.mk p .append
    | none => pure none
  let t0 ← IO.monoMsNow
  -- the room: the budget minus the running workers' peaks (no budget: unbounded)
  let roomOf (pk : Nat) : Nat :=
    if o.memory = 0 then 1 <<< 60 else o.memory - min o.memory pk
  let progress (st : St) (now : Nat) : String :=
    progressText total st.nDone st.running.size
      (st.stamps.size - 1, (st.stamps.back?.getD 0) - (st.stamps[0]?.getD 0)) st.mem o.memory
      st.requeued st.prot
      (if st.running.isEmpty then 0 else (st.front.filter (·.2 > roomOf ((st.mem.map (·.2.2)).getD 0))).length)
  let finish (st : St) (r : Running) (w : String) : IO St := do
    let msg ← r.diagText
    if let some h := logH then
      h.putStrLn s!"{w}\t{spell r.m}"
      h.flush
    let now ← IO.monoMsNow
    let st := { st with verdicts := st.verdicts.insert r.m w, finished := st.finished + 1,
                        nDone := st.nDone + 1, lastLine := now,
                        stamps := pushStamp st.stamps (now - t0) }
    out.putStrLn s!"con-leche: schedule: {r.m}: {w} t={ConLeche.Cached.msSecs (now - r.start)}s \
      {progress st now}"
    out.flush
    let lines := (msg.splitOn "\n").filter fun l => l != "" && !l.startsWith "con-leche: stats:"
    if w != "0" then
      for l in lines do err.putStrLn l
      err.flush
    return st
  let jobs := max 1 jobs
  let start (st : St) (m : Name) (now : Nat) : IO St := do
    match ← (spawnW app m (args m) now).toBaseIO with
    | .ok r => return { st with lastStart := now, running := st.running.push r }
    | .error e =>
      err.putStrLn s!"con-leche: schedule: {m}: 3: no worker started: {e}; no further \
        worker starts, the running ones are waited for"
      err.flush
      return { st with verdicts := st.verdicts.insert m "3", nDone := st.nDone + 1,
                       stopped := true }
  -- one tick: the running workers looked at, the budget, the starts, the heartbeat
  let tick (st : St) : IO St := do
    let now ← IO.monoMsNow
    let mut st := st
    -- the resident sets, every tick, budget or not
    let rss ← workerRssOpt
    let look (l : List (String × Nat × Nat)) (r : Running) : Nat × Nat :=
      ((l.find? (·.1 == r.arg)).map (·.2)).getD (0, 0)
    let sample (rs : Array Running) : Option (Nat × Nat × Nat) := rss.map fun l =>
      rs.foldl (fun (t, m, pk) r =>
        let (k, h) := look l r
        (t + k, max m k, pk + max h k)) (0, 0, 0)
    if let some (t, _, _) := sample st.running then st := { st with peak := max st.peak t }
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
    st := { st with running := still, mem := sample still }
    -- the protected worker finished: starts resume
    let mut resumed : Option Name := none
    if let some p := st.prot then
      if !st.running.any (·.m == p) then
        st := { st with prot := none }
        resumed := some p
    for (r, w) in ended do st ← finish st r w
    if let some p := resumed then
      err.putStrLn s!"con-leche: schedule: {p} finished, protection over"
      err.flush
    if o.memory > 0 && !st.running.isEmpty then
      let rss := rss.getD []
      let mut total := 0
      let mut big : Option (Nat × Nat × Nat) := none
      for h : i in [0:st.running.size] do
        let (k, hw) := look rss st.running[i]
        total := total + k
        big := match big with
          | some (j, kj, hj) => if k > kj || (k == kj && hw > hj) then some (i, k, hw)
                                else some (j, kj, hj)
          | none => some (i, k, hw)
      -- sticky: a protected worker that still runs stays the protected one
      if let some pm := st.prot then
        if let some i := st.running.findIdx? (·.m == pm) then
          if h : i < st.running.size then
            big := some (i, (look rss st.running[i]).1, 0)
      if total > o.memory then
        if let some (i, k, _) := big then
          if h : i < st.running.size then
            let p := st.running[i]
            if st.running.size = 1 then
              -- the protected worker alone: running alone could not help
              p.child.kill
              let _ ← p.child.wait
              err.putStrLn s!"con-leche: schedule: {p.m}: {gib k} alone, over the budget of \
                {gibBudget o.memory}: memory"
              err.flush
              st := { st with running := st.running.eraseIdx i, prot := none }
              st ← finish st p "memory"
            else
              if st.prot.isNone then
                err.putStrLn s!"con-leche: schedule: memory over {gibBudget o.memory}: \
                  protecting {p.m} ({gib k})"
                err.flush
              -- the youngest other worker makes room, and is queued again at the front
              let mut vs : Option (Nat × Nat) := none
              for h2 : j in [0:st.running.size] do
                if j != i then
                  let sj := st.running[j].start
                  vs := match vs with
                    | some (_, s0) => if sj ≥ s0 then some (j, sj) else vs
                    | none => some (j, sj)
              if let some (v, _) := vs then
                if h3 : v < st.running.size then
                  let r := st.running[v]
                  r.child.kill
                  let _ ← r.child.wait
                  let _ ← r.diagText
                  err.putStrLn s!"con-leche: schedule: {r.m}: killed at {gib (look rss r).1}, \
                    requeued"
                  err.flush
                  let sz := max (look rss r).1 ((st.front.find? (·.1 == r.m)).map (·.2) |>.getD 0)
                  st := { st with running := st.running.eraseIdx v, prot := some p.m,
                                  front := (r.m, sz) :: st.front.filter (·.1 != r.m),
                                  requeued := st.requeued + 1,
                                  kills := st.kills.insert r.m ((st.kills.getD r.m 0) + 1) }
    -- starts: the first module of the queue whose known size fits into the room (the budget
    -- minus the running workers' peaks); nothing running: the first one always starts
    let now ← IO.monoMsNow
    let room := roomOf (((sample st.running).map (·.2.2)).getD 0)
    if st.stopped then
      st := { st with pending := [], front := [] }
    else if now - st.lastStart ≥ o.stagger && st.running.size < jobs then
      match st.front.find? (fun (_, z) => st.running.isEmpty || z ≤ room) with
      | some (m, _) => st ← start { st with front := st.front.filter (·.1 != m) } m now
      | none =>
        match st.pending with
        | m :: ms => if st.running.isEmpty || room > 0 then st ← start { st with pending := ms } m now
        | [] => pure ()
    -- the heartbeat: after `heartbeat` ms without a line, the counts and the longest runs
    if o.heartbeat > 0 && now - st.lastLine ≥ o.heartbeat && !st.running.isEmpty then
      let longest := (st.running.qsort (fun a b => a.start < b.start)).toList.take 3
      let ls := ", ".intercalate (longest.map fun r => s!"{r.m} {dur (now - r.start)}")
      st := { st with mem := sample st.running }
      err.putStrLn s!"con-leche: schedule: {progress st now}; longest: {ls}"
      err.flush
      st := { st with lastLine := now }
    return st
  let st0 : St := { pending := todo, verdicts := logged }
  let stRef ← IO.mkRef { st0 with nDone := total - todo.length, lastLine := t0 }
  let rec loop : Nat → IO Unit
    | 0 => pure ()
    | fuel + 1 => do
      let st ← stRef.get
      if st.running.isEmpty && st.pending.isEmpty && st.front.isEmpty then return
      stRef.set (← tick st)
      IO.sleep 50
      loop fuel
  try
    loop (1 <<< 62)
  catch e =>
    -- no worker outlives the scheduler: every running one is killed, by its own child
    let st ← stRef.get
    err.putStrLn s!"con-leche: schedule: stopped by an error: {e}; killing the \
      {st.running.size} running workers"
    err.flush
    for r in st.running do
      try r.child.kill; let _ ← r.child.wait catch _ => pure ()
    throw e
  let st ← stRef.get
  if st.requeued > 0 then
    err.putStrLn s!"con-leche: schedule: {st.requeued} kills for memory put modules back in the \
      queue ({st.kills.size} modules, at most {st.kills.fold (fun m _ n => max m n) 0} times each)"
    err.flush
  return (st.verdicts, st.peak)

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
def runAll (parse : String → Option Name) (args : Name → Array String) (mods : Array Name)
    (o : Opts) (jobs : Nat) (modeTag : String) : IO UInt8 := do
  if o.memory > 0 && !(← childrenReadable) then
    let e ← IO.getStderr
    e.putStrLn "con-leche: --schedule-memory reads the workers' resident sets through \
      /proc/self/task/<tid>/children, which this system does not provide"
    return 3
  let (vs, peak) ← run parse (← IO.appPath) args mods o jobs
  summary mods vs modeTag peak

end ConLeche.Driver.Schedule
