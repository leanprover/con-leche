module

public import ConLeche.Driver.Schedule.Status
public import ConLeche.Driver.Schedule.Proc
public import Std.Async.Signal

@[expose] public section

/-!
# The scheduler's run: the processes (outside the theorem)

The IO loop of `con-leche --olean --schedule … -- ROOT` (`ConLeche/Driver/Schedule.lean`): one
worker process per module of `ROOT`'s closure, admitted by the engine (`Engine.lean`), its output
read (`Worker.lean`), logged (`Log.lean`) and reported (`Status.lean`).  It is an `IO` action
handed to `CheckerIO.liftIO`: no theorem is about a `--schedule` run, and nothing here reads a
file the checks read.  It is the one module of the checker that starts a process, kills one or
writes a file (`tests/trust-surface.sh`'s process fence).  What it does, all of it plain `IO`:

* **one tick every 50 ms** (`run`'s `tick`): the running workers' resident sets read
  (`workerRssOpt`), the finished ones collected, the kills for memory, the starts, the log's
  `reserve` lines and the heartbeat;
* **workers that inherit nothing but their three standard streams**, all pipes: stdin closed at
  the start, stdout and stderr each read to the end by a thread of its own (so no worker blocks
  on a full pipe), stderr passed on for a verdict other than 0 (`WCfg`, `spawnW`, `passedOn`);
* **kills of its own children only**: a victim of an overflow (`victims`), a worker alone over
  the limit (`aloneAct`), a worker past its time limit (`timeout`, seconds, 0 for none; its
  verdict `timeout`) and every running worker at an interrupt is killed by `Child.kill` of the
  child this scheduler started (its own PID), never by a name.  Output: a short line per burst of
  kills (`killText`), and one where the head slot starts a killed module that does not fit;
* **the log** (`--schedule-log`, `Log.lean`'s lines), written and flushed line by line;
* **SIGINT and SIGTERM** (`Std.Async.Signal.Waiter`, polled every tick): no further start, every
  running worker killed through its own `Child` and waited for, logged as `killed` (no verdict),
  the log flushed, the statistics printed, and the exit code 130 (SIGINT) or 143 (SIGTERM);
* **no worker outlives the scheduler**: a worker that cannot be started is that module's verdict
  3, with the reason, and no further one starts; the running ones are waited for.  On any other
  error the running workers are killed before the error is passed on;
* **the verdicts** are reported in the graph's order (`summary`);
* **the commands instead of a run** (`--schedule-commands`, `printCommands`): no process
  started; the commands that check the closure (`commandLines`) on stdout, nothing else.
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
  /-- print the commands that check the closure instead of running them -/
  commands : Bool := false

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
flag, `-log=FILE`, `-memory=SIZE` (`parseSize`), `-timeout=S`, `-order=shuffled|graph`,
`-commands`). -/
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
    else if v == "-commands" then Opts.parse vs { o with commands := true }
    else .error s!"unknown option --schedule{v}"

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
  /-- its `VmHWM` at the last tick, KiB -/
  hwm : Nat := 0
  /-- its largest sample in each of the last minutes of its run (`pushMinute`): (the minute,
  counted from its start, the sample in KiB), oldest first -/
  recent : Array (Nat × Nat) := #[]

/-- A running worker after a tick's reading `(k, h)` of its `VmRSS` and `VmHWM` at `now`: the
sample is `h` where `VmHWM` rose since the last tick (a peak between two ticks), else `k`. -/
def Running.sampled (r : Running) (now k h : Nat) : Running :=
  let x := if h > r.hwm then h else k
  { r with hwm := max r.hwm h, recent := pushMinute r.recent ((now - r.start) / 60000) x }

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

/-- **The scheduler's state**: the engine's queue and sizes, the running workers, and the
statistics (`Stats`). -/
structure St extends Stats where
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
  now, and the sum of their reservations (`none`: `/proc` could not be read) -/
  mem : Option (Nat × Nat × Nat) := none
  /-- the largest total over the run, KiB -/
  peak : Nat := 0
  /-- modules put back in the queue by a kill for memory, counted with repeats -/
  requeued : Nat := 0
  /-- the largest resident set seen of each running module, KiB -/
  seen : Std.HashMap Name Nat := {}
  /-- the peaks of the last `typWindow` finished workers, KiB -/
  peaks : Array Nat := #[]
  /-- the typical peak of a worker, KiB: the median of `peaks`; before `typMin` finishes,
  the limit divided by the jobs -/
  typ : Nat := 0
  /-- the running workers' windowed peaks each at least `typ` and their known sizes, at the last
  tick: what admission counts -/
  effPk : Nat := 0
  /-- what admission had reserved for each running worker (KiB) when it last started one -/
  resv : Std.HashMap Name Nat := {}
  /-- the largest surprise since the last start, KiB: the running workers' current sets minus
  `resv` of them, the one furthest above its own left out (`surpriseOf`) -/
  epMax : Nat := 0
  /-- the last `surpriseWindow` nonzero surprises, KiB, one per stretch between two starts -/
  surprises : Array Nat := #[]
  /-- the time of the last tick; the time-weighted sums are weighted by the ms between ticks -/
  lastTick : Nat := 0
  /-- the time of the last `reserve` log lines -/
  lastReserve : Nat := 0
  /-- modules killed while running with more than one thread: one thread from then on -/
  single : Std.HashSet Name := {}

/-- **The scheduler**: the modules' workers (`args m`, the worker's arguments at `m`, of the
binary `app`; its last argument `spell m`) run as the module docstring says; the verdict of
every module of `mods`, the peak of the running workers' total resident memory in KiB
(0 where `/proc` cannot be read), and the signal that ended the run early, with its exit code. -/
def run (parse : String → Option Name) (app : System.FilePath) (args : Name → Nat → Array String)
    (decls : Name → IO (Option Nat)) (mods : Array Name) (o : Opts) (jobs : Nat) :
    IO (Std.HashMap Name String × Nat × Option (String × UInt8)) := do
  let err ← IO.getStderr
  let out ← IO.getStdout
  -- the workers inherit the stack size; a `stack` verdict is logged with it
  let stackKb := (← IO.getEnv "LEAN_STACK_SIZE_KB").getD "-"
  -- the cgroup's OOM-kill counter, to tell a SIGKILL by the OOM killer from another
  let cg ← limitCgroup
  let oomRef ← IO.mkRef (← match cg with | some d => oomKills d | none => pure none)
  let oomRose : IO Bool := do
    let some d := cg | return false
    let now ← oomKills d
    let before ← oomRef.get
    oomRef.set now
    return match before, now with | some b, some n => n > b | _, _ => false
  let logged ← match o.log with
    | some p => readLog parse p stackKb
    | none => pure {}
  let todo := (mods.toList.filter (!logged.verdicts.contains ·))
  let todo := if o.shuffled then shuffle spell todo else todo
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
  let logLine (l : String) : IO Unit := do
    if let some h := logH then
      h.putStrLn l
      h.flush
  let t0 ← IO.monoMsNow
  -- the room: the planning budget minus the running workers' reservations (no limit: unbounded)
  let planNow (st : St) : Nat := planOf o.memory st.surprises
  let roomOf (st : St) (pk : Nat) : Nat :=
    if o.memory = 0 then 1 <<< 60 else planNow st - min (planNow st) pk
  let threadsOf (st : St) : Nat := st.running.foldl (· + ·.threads) 0
  -- the killed modules whose known size does not fit the room (nothing running: none)
  let waitingOf (st : St) : Nat :=
    if st.running.isEmpty then 0
    else (st.again.filter (st.sizes.getD · 0 > roomOf st st.effPk)).length
  let status (st : St) (now : Nat) : String :=
    statusText total st.nDone st.running.size
      (etaMs (total - st.nDone) (logged.msSum + st.doneMs)
        (logged.msN + st.finished) st.runMs (now - t0) logged.workers jobs)
      jobs (threadsOf st) st.mem o.memory
  let finish (st : St) (r : Running) (w : String) : IO St := do
    let (outText, msg) ← r.texts
    let now ← IO.monoMsNow
    -- the worker's own peak where it reported one, else the last one sampled (a lower bound)
    let (pk, rssText, logRss) := finishPeak msg (st.seen.getD r.m 0)
    logLine (verdictLine w r.m (now - r.start) logRss (now - t0) (workerStats outText msg)
      r.threads stackKb)
    let (peaks, typ) := pushPeak st.peaks st.typ pk
    let st := { st with verdicts := st.verdicts.insert r.m w, finished := st.finished + 1, doneMs := st.doneMs + (now - r.start),
                        peaks, typ, seen := st.seen.erase r.m,
                        nDone := st.nDone + 1, lastLine := now,
                        recs := st.recs.push { m := r.m, ms := now - r.start, pk },
                        workMs := st.workMs + (now - r.start),
                        memVerdicts := st.memVerdicts + (if w == "memory" then 1 else 0),
                        nonzero := st.nonzero + (if w == "0" then 0 else 1) }
    out.putStrLn (finishText (status st now) (now - r.start) rssText jobs r.threads w r.m)
    out.flush
    if w != "0" then
      for l in passedOn msg do err.putStrLn l
      if w == "stack" then err.putStrLn (stackHint r.m stackKb)
      err.flush
    return st
  -- a kill's log line: the module, the run time, the last sampled resident set
  let logKill (st : St) (r : Running) (now : Nat) : IO Unit :=
    logLine (killLine r.m (now - r.start) (st.seen.getD r.m 0) r.threads)
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
    -- each running worker's windowed peak takes this tick's sample
    if let some l := rss then
      st := { st with running := st.running.map fun r => r.sampled now (look l r).1 (look l r).2 }
    let sample (rs : Array Running) : Option (Nat × Nat × Nat) := rss.map fun l =>
      rs.foldl (fun (t, m, pk) r =>
        let (k, _) := look l r
        (t + k, max m k, pk + max (max k (windowPeak r.recent))
          (max st.typ (st.sizes.getD r.m 0)))) (0, 0, 0)
    if let some (t, _, _) := sample st.running then st := { st with peak := max st.peak t }
    -- the largest set seen of each running module, for the typical peak of the finished ones
    st := { st with seen := st.running.foldl (fun m r =>
      let (k, h) := look (rss.getD []) r
      m.insert r.m (max (m.getD r.m 0) (max k h))) st.seen }
    -- what admission counts per running worker: its peak over the last `peakWindow` minutes, at
    -- least the typical peak and its known size (a worker started in this tick has no sample
    -- yet: the latter two)
    let eff1 (st : St) (r : Running) : Nat :=
      let (k, _) := look (rss.getD []) r
      max (max k (windowPeak r.recent)) (max st.typ (st.sizes.getD r.m 0))
    let eff (st : St) (rs : Array Running) : Nat := rs.foldl (fun a r => a + eff1 st r) 0
    -- the running workers' reservation rows (DESIGN #571), for the heartbeat and the log
    let resRows (st : St) (now : Nat) (nm : Name → String) : List ResRow := st.running.toList.map fun r =>
      let (k, _) := look (rss.getD []) r
      (nm r.m, now - r.start, k, eff1 st r,
        resTerm k (windowPeak r.recent) st.typ (st.sizes.getD r.m 0))
    let mut still : Array Running := #[]
    let mut ended : Array (Running × String) := #[]
    for r in st.running do
      match ← r.child.tryWait with
      | some c =>
        let (_, msg) ← r.texts
        let oom ← if c.toNat == 137 then oomRose else pure false
        ended := ended.push (r, exitVerdict c.toNat msg oom)
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
        if h : st.running.size = 1 ∧ (st.running[0]?.any (aloneAct ·.threads == .memory)) then
          -- alone over the limit with one thread: running alone could not help
          let p := st.running[0]'(by have := h.1; omega)
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
          -- a worker alone with more than one thread is the victim: it is queued again at one
          -- thread (DESIGN #595)
          let vs := if st.running.size = 1 then st.running.toList.map (·.m) else
            victims (st.running.toList.map fun r => (r.m, r.start, (look rss r).1))
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
                                head := if st.head == some r.m then none else st.head,
                                sizes := st.sizes.insert r.m sz,
                                single := if r.threads > 1 then st.single.insert r.m
                                  else st.single,
                                again := insertAt pos r.m st.again,
                                requeued := st.requeued + 1, killN := st.killN + 1,
                                killMs := st.killMs + (now - r.start),
                                workMs := st.workMs + (now - r.start),
                                kills := st.kills.insert r.m ((st.kills.getD r.m 0) + 1) }
          if let some l := killText killed then err.putStrLn l
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
    -- while modules wait for room: the reservations in the log, at most once a minute
    if o.memory > 0 && rss.isSome && now - st.lastReserve ≥ 60000 && waitingOf st > 0 then
      if let some h := logH then
        for row in resRows st now spell do h.putStrLn (reserveLine row)
        h.flush
      st := { st with lastReserve := now }
    -- the heartbeat: after `heartbeat` ms without a line, the counts and the longest runs
    if o.heartbeat > 0 && now - st.lastLine ≥ o.heartbeat && !st.running.isEmpty then
      st := { st with mem := sample st.running }
      let byAge := st.running.qsort (fun a b => a.start < b.start)
      -- what explains the wait: the longest worker, the requeued modules, and the killed ones
      -- waiting for room, with what admission reserved against the planning budget
      let wt := waitingOf st
      let ls := waitText (byAge[0]?.map fun r => (r.m, now - r.start)) (byAge.size - 1)
        st.requeued wt (st.mem.map (·.2.2)) (if o.memory > 0 then some (planNow st) else none)
      err.putStrLn s!"{status st now}  {ls}"
      -- the workers reserved above their current set (only while modules wait for room)
      let ov := if wt = 0 || rss.isNone then "" else overText (resRows st now toString)
      if ov != "" then err.putStrLn s!"    {ov}"
      err.flush
      st := { st with lastLine := now }
    return st
  -- the log's state read back (DESIGN #546): the typical peak's window; the modules killed before
  -- that still have to run keep their positions, with their known sizes, and run with one thread
  -- where the kill came with more
  let s0 := logged.seed todo (o.memory / jobs)
  let st0 : St := { pending := s0.pending, again := s0.again, verdicts := logged.verdicts,
                    peaks := s0.peaks, typ := s0.typ, sizes := s0.sizes, single := s0.single }
  if s0.peaks.size > 0 || !s0.again.isEmpty then
    err.putStrLn s!"con-leche: schedule: from the log: {s0.peaks.size} peaks (typical peak \
      {gib s0.typ}), {s0.again.length} killed modules to run again"
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
  for l in statsLines st.toStats (now - t0) jobs o.memory (planOf o.memory st.surprises)
      st.single.size (total - todo.length) (intr.map (·.1)) do
    err.putStrLn l
  err.flush
  return (st.verdicts, st.peak, intr)

/-- **The run's verdict**: 0 when every module's worker answered 0; else the first module in
the graph's order that did not, its code (`timeout`, `memory`, `stack`, `oom-kill`, `signal …`: 3). -/
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

/-- **The commands instead of a run** (`--schedule-commands`): `commandLines` of this binary on
stdout, one per line, the modules in the queue's order (`shuffle`, or the graph's with
`--schedule-order=graph`); no process started, nothing on stderr, exit 0. -/
def printCommands (dirs : String) (root : Name) (mods : Array Name) (o : Opts)
    (args : Name → Array String) : IO UInt8 := do
  let app ← IO.appPath
  let order := if o.shuffled then shuffle spell mods.toList else mods.toList
  let out ← IO.getStdout
  for l in commandLines app.toString dirs root order args do out.putStrLn l
  out.flush
  return 0

end ConLeche.Driver.Schedule
