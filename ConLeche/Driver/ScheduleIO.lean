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
  by its last argument, `/proc/<pid>/status`'s `VmRSS`); above the budget the largest is killed, by
  its own process (`Child.kill` of the child this scheduler started, never by a name), and
  queued to run again **alone** once; killed again alone, its verdict is `memory`;
* **a timeout per worker** (`timeout`, seconds, 0 for none): a worker running longer is killed,
  its verdict `timeout`;
* **an append-only log** (`log`): one line per finished module, `<verdict>\t<module>`, written
  and flushed as it finishes; a restart with the same log skips every module it names, so a
  run interrupted anywhere resumes where it stopped;
* **progress**: each module's line (stdout) is `M: VERDICT t=Ss [done/total p %, k running,
  eta D]`, `done` counting a resumed run's logged modules, the estimate the remaining modules at
  this run's finish rate so far (`progressText`); with a heartbeat (`heartbeat` ms), after that
  long without a line, the same counts and the three longest-running workers (stderr); the
  running workers' total resident memory and the largest one's (and the budget, when set)
  follow `k running` (`1.2 GiB (max 0.6 GiB) of 40 GiB`), read every tick through the same
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
  /-- its run alone, after a kill for memory -/
  solo : Bool

/-- A worker started: the binary `app` at the arguments, the last of which is `spell m`; its
stdin closed, its stdout and stderr drained. -/
def spawnW (app : System.FilePath) (m : Name) (args : Array String) (now : Nat) (solo : Bool) :
    IO Running := do
  let c ← IO.Process.spawn { cmd := app.toString, args, stdin := .piped, stdout := .piped
                           , stderr := .piped : IO.Process.SpawnArgs }
  let (_, c) ← c.takeStdin
  let out ← IO.asTask (prio := .dedicated) c.stdout.readToEnd
  let diag ← IO.asTask (prio := .dedicated) c.stderr.readToEnd
  return { m, arg := spell m, child := c, out, diag, start := now, solo }

/-- What a finished worker wrote to stderr (its stdout, the verdict line, is dropped). -/
def Running.diagText (r : Running) : IO String := do
  let _ ← IO.wait r.out
  match ← IO.wait r.diag with
  | .ok s => pure s
  | .error e => pure s!"con-leche: schedule: {r.m}: its stderr could not be read: {e}"

/-- A file's contents, `none` where it cannot be read. -/
def readOpt (p : System.FilePath) : IO (Option String) := do
  try some <$> IO.FS.readFile p catch _ => pure none

/-- The resident set in KiB of a `/proc/<pid>/status`, 0 where it has none. -/
def vmRss (s : String) : Nat :=
  match (s.splitOn "\n").find? (·.startsWith "VmRSS:") with
  | some l =>
    let ws := ((l.drop 6).toString.split (fun c => c == ' ' || c == '\t')).toList.map
      (·.toString) |>.filter (· != "")
    (ws.head?.bind String.toNat?).getD 0
  | none => 0

/-- **The workers' resident sets**: every child of this process
(`/proc/self/task/<tid>/children`) by its last argument (`/proc/<pid>/cmdline`, a worker's
`spell m`), with its resident set in KiB.  Not by `Child.pid`: in Lean's runtime that function
takes the child owned and never releases it, so every call would keep the child, and its
pipes, open to the end of the run. -/
def workerRss : IO (List (String × Nat)) := do
  let mut acc := []
  for t in ← System.FilePath.readDir "/proc/self/task" do
    let some cs ← readOpt (t.path / "children") | continue
    for pid in (cs.splitOn " ").filter (· != "") do
      let some cmd ← readOpt s!"/proc/{pid}/cmdline" | continue
      let some st ← readOpt s!"/proc/{pid}/status" | continue
      match ((cmd.splitOn "\x00").filter (· != "")).getLast? with
      | some a => acc := (a, vmRss st) :: acc
      | none => pure ()
  return acc

/-- `workerRss`, `none` where `/proc` cannot be read (the status line then shows no memory). -/
def workerRssOpt : IO (Option (List (String × Nat))) := do
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
  pending : List Name
  solos : List Name
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
  /-- the running workers' resident memory at the last tick, KiB: the total and the largest
  (`none`: `/proc` could not be read) -/
  mem : Option (Nat × Nat) := none
  /-- the largest total over the run, KiB -/
  peak : Nat := 0

/-- The progress of a run: `[done/total p %, k running, eta D]`.  `done` counts the logged
modules of a resumed run; the estimate is the remaining modules at the rate this run has
finished them so far (`elapsed × remaining ÷ finished`), none before the first finishes.  With
`mem` (the running workers' total and largest, KiB) and a `budget` (KiB, 0 for none):
`k running, 1.2 GiB (max 0.6 GiB) of 40 GiB`. -/
def progressText (total done finished running elapsed : Nat)
    (mem : Option (Nat × Nat) := none) (budget : Nat := 0) : String :=
  let pm := if total = 0 then 1000 else done * 1000 / total
  let eta := if finished = 0 || done ≥ total then ""
    else s!", eta {dur (elapsed * (total - done) / finished)}"
  let memText := match mem with
    | some (t, m) =>
      if running = 0 then ""
      else s!", {gib t} (max {gib m}){if budget > 0 then s!" of {gibBudget budget}" else ""}"
    | none => ""
  s!"[{done}/{total} {pm / 10}.{pm % 10} %, {running} running{memText}{eta}]"

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
  let progress (st : St) (now : Nat) : String :=
    progressText total st.nDone st.finished st.running.size (now - t0) st.mem o.memory
  let finish (st : St) (r : Running) (w : String) : IO St := do
    let msg ← r.diagText
    if let some h := logH then
      h.putStrLn s!"{w}\t{spell r.m}"
      h.flush
    let now ← IO.monoMsNow
    let st := { st with verdicts := st.verdicts.insert r.m w, finished := st.finished + 1,
                        nDone := st.nDone + 1, lastLine := now }
    out.putStrLn s!"con-leche: schedule: {r.m}: {w} t={ConLeche.Cached.msSecs (now - r.start)}s \
      {progress st now}"
    out.flush
    let lines := (msg.splitOn "\n").filter fun l => l != "" && !l.startsWith "con-leche: stats:"
    if w != "0" then
      for l in lines do err.putStrLn l
      err.flush
    return st
  let jobs := max 1 jobs
  let start (st : St) (m : Name) (now : Nat) (solo : Bool) : IO St := do
    match ← (spawnW app m (args m) now solo).toBaseIO with
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
    let sample (rs : Array Running) : Option (Nat × Nat) := rss.map fun l =>
      rs.foldl (fun (t, m) r =>
        let k := ((l.find? (·.1 == r.arg)).map (·.2)).getD 0
        (t + k, max m k)) (0, 0)
    if let some (t, _) := sample st.running then st := { st with peak := max st.peak t }
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
    for (r, w) in ended do st ← finish st r w
    if o.memory > 0 && !st.running.isEmpty then
      let rss := rss.getD []
      let mut total := 0
      let mut big : Option (Nat × Nat) := none
      for h : i in [0:st.running.size] do
        let k := ((rss.find? (·.1 == st.running[i].arg)).map (·.2)).getD 0
        total := total + k
        big := match big with
          | some (j, kj) => if k > kj then some (i, k) else some (j, kj)
          | none => some (i, k)
      if total > o.memory then
        if let some (i, k) := big then
          if h : i < st.running.size then
            let r := st.running[i]
            r.child.kill
            let _ ← r.child.wait
            err.putStrLn s!"con-leche: schedule: {r.m}: killed at {k / 1024} MiB \
              (running workers {total / 1024} MiB, budget {o.memory / 1024} MiB)\
              {if r.solo then "" else "; to run again alone"}"
            st := { st with running := st.running.eraseIdx i }
            if r.solo then st ← finish st r "memory"
            else
              let _ ← r.diagText
              st := { st with solos := st.solos ++ [r.m] }
    -- starts: a module to run alone waits for every other worker; nothing starts beside it
    let now ← IO.monoMsNow
    let soloRuns := st.running.any (·.solo)
    if st.stopped then
      st := { st with pending := [], solos := [] }
    else if !soloRuns && now - st.lastStart ≥ o.stagger then
      match st.solos with
      | m :: ms =>
        if st.running.isEmpty then st ← start { st with solos := ms } m now true
      | [] =>
        if st.running.size < jobs then
          match st.pending with
          | m :: ms => st ← start { st with pending := ms } m now false
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
  let st0 : St := { pending := todo, solos := [], verdicts := logged }
  let stRef ← IO.mkRef { st0 with nDone := total - todo.length, lastLine := t0 }
  let rec loop : Nat → IO Unit
    | 0 => pure ()
    | fuel + 1 => do
      let st ← stRef.get
      if st.running.isEmpty && st.pending.isEmpty && st.solos.isEmpty then return
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
