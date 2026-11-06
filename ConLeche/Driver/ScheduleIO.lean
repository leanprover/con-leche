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
* **a memory budget** (`memory`, MiB, 0 for none): every tick the resident sets of the running
  workers are read (`/proc/<pid>/status`, `VmRSS`); above the budget the largest is killed, by
  its own process (`Child.kill` of the child this scheduler started, never by a name), and
  queued to run again **alone** once; killed again alone, its verdict is `memory`;
* **a timeout per worker** (`timeout`, seconds, 0 for none): a worker running longer is killed,
  its verdict `timeout`;
* **an append-only log** (`log`): one line per finished module, `<verdict>\t<module>`, written
  and flushed as it finishes; a restart with the same log skips every module it names, so a
  run interrupted anywhere resumes where it stopped.

A worker's verdict is its exit code (0 accept, 1 reject, 2 decline, 3 error), or `timeout`,
`memory`, or `signal` (ended otherwise); its stderr, but the statistics lines, is passed on.
-/

namespace ConLeche.Driver.Schedule

open ConLeche

/-- **The scheduler's settings.** -/
structure Opts where
  /-- the append-only log, resumed from -/
  log : Option System.FilePath := none
  /-- the memory budget for all running workers, MiB (0: none) -/
  memory : Nat := 0
  /-- the time limit of one worker, seconds (0: none) -/
  timeout : Nat := 0
  /-- the least time between two starts, milliseconds -/
  stagger : Nat := 200

/-- The settings, from the values of the `--schedule[-OPT=VALUE]` flags (`""` for the bare
flag, `-log=FILE`, `-memory=MIB`, `-timeout=S`, `-stagger=MS`). -/
def Opts.parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | v :: vs, o =>
    let num (pre : String) (k : Nat → Opts) : Except String Opts :=
      match (v.drop pre.length).toString.toNat? with
      | some n => Opts.parse vs (k n)
      | none => .error s!"--schedule{pre}: not a number"
    if v == "" then Opts.parse vs o
    else if v.startsWith "-log=" then
      Opts.parse vs { o with log := some ((v.drop 5).toString : System.FilePath) }
    else if v.startsWith "-memory=" then num "-memory=" fun n => { o with memory := n }
    else if v.startsWith "-timeout=" then num "-timeout=" fun n => { o with timeout := n }
    else if v.startsWith "-stagger=" then num "-stagger=" fun n => { o with stagger := n }
    else .error s!"unknown option --schedule{v}"

/-- A module's name as the command line spells it, each component escaped. -/
def spell (m : Name) : String :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  ".".intercalate ((comps m).map fun c => "«" ++ c ++ "»")

/-- The workers' standard streams: no input, no output, the diagnostics read back. -/
abbrev WCfg : IO.Process.StdioConfig := { stdin := .null, stdout := .null, stderr := .piped }

/-- A worker started: the binary `app` at the arguments. -/
def spawnW (app : System.FilePath) (args : Array String) : IO (IO.Process.Child WCfg) :=
  IO.Process.spawn { cmd := app.toString, args, stdin := .null, stdout := .null, stderr := .piped }

/-- A running worker. -/
structure Running where
  m : Name
  child : IO.Process.Child WCfg
  start : Nat
  /-- its run alone, after a kill for memory -/
  solo : Bool

/-- A process's resident set in KiB, 0 where it cannot be read. -/
def rssKiB (pid : UInt32) : IO Nat := do
  try
    let s ← IO.FS.readFile s!"/proc/{pid}/status"
    match (s.splitOn "\n").find? (·.startsWith "VmRSS:") with
    | some l =>
      let ws := ((l.drop 6).toString.split (fun c => c == ' ' || c == '\t')).toList.map
        (·.toString) |>.filter (· != "")
      pure ((ws.head?.bind String.toNat?).getD 0)
    | none => pure 0
  catch _ => pure 0

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

/-- **The scheduler**: the modules' workers (`args m`, the worker's arguments at `m`, of the
binary `app`) run as the module docstring says; the verdict of every module of `mods`. -/
def run (parse : String → Option Name) (app : System.FilePath) (args : Name → Array String)
    (mods : Array Name) (o : Opts) (jobs : Nat) : IO (Std.HashMap Name String) := do
  let err ← IO.getStderr
  let out ← IO.getStdout
  let logged ← match o.log with
    | some p => readLog parse p
    | none => pure {}
  let todo := mods.toList.filter (!logged.contains ·)
  if logged.size > 0 then
    err.putStrLn s!"con-leche: schedule: {mods.size - todo.length} modules logged, \
      {todo.length} to run"
  let logH ← match o.log with
    | some p => some <$> IO.FS.Handle.mk p .append
    | none => pure none
  let finish (st : St) (r : Running) (w : String) (msg : String) : IO St := do
    if let some h := logH then
      h.putStrLn s!"{w}\t{spell r.m}"
      h.flush
    let t := (← IO.monoMsNow) - r.start
    out.putStrLn s!"con-leche: schedule: {r.m}: {w} t={ConLeche.Cached.msSecs t}s"
    out.flush
    let lines := (msg.splitOn "\n").filter fun l => l != "" && !l.startsWith "con-leche: stats:"
    if w != "0" then
      for l in lines do err.putStrLn l
      err.flush
    return { st with verdicts := st.verdicts.insert r.m w }
  let jobs := max 1 jobs
  -- one tick: the running workers looked at, the budget, the starts
  let rec loop : Nat → St → IO St
    | 0, st => pure st
    | fuel + 1, st => do
      if st.running.isEmpty && st.pending.isEmpty && st.solos.isEmpty then return st
      let now ← IO.monoMsNow
      let mut st := st
      let mut still : Array Running := #[]
      for r in st.running do
        match ← r.child.tryWait with
        | some c =>
          let msg ← r.child.stderr.readToEnd
          st ← finish st r (if c ≤ 3 then toString c else "signal") msg
        | none =>
          if o.timeout > 0 && now - r.start > o.timeout * 1000 then
            r.child.kill
            let _ ← r.child.wait
            let msg ← r.child.stderr.readToEnd
            st ← finish st r "timeout" msg
          else still := still.push r
      st := { st with running := still }
      if o.memory > 0 && !st.running.isEmpty then
        let mut total := 0
        let mut big : Option (Nat × Nat) := none
        for h : i in [0:st.running.size] do
          let k ← rssKiB st.running[i].child.pid
          total := total + k
          big := match big with
            | some (j, kj) => if k > kj then some (i, k) else some (j, kj)
            | none => some (i, k)
        if total > o.memory * 1024 then
          if let some (i, k) := big then
            if h : i < st.running.size then
              let r := st.running[i]
              r.child.kill
              let _ ← r.child.wait
              let msg ← r.child.stderr.readToEnd
              err.putStrLn s!"con-leche: schedule: {r.m}: killed at {k / 1024} MiB \
                (running workers {total / 1024} MiB, budget {o.memory} MiB)\
                {if r.solo then "" else "; to run again alone"}"
              st := { st with running := st.running.eraseIdx i }
              if r.solo then st ← finish st r "memory" msg
              else st := { st with solos := st.solos ++ [r.m] }
      -- starts: a module to run alone waits for every other worker; nothing starts beside it
      let now ← IO.monoMsNow
      let soloRuns := st.running.any (·.solo)
      if !soloRuns && now - st.lastStart ≥ o.stagger then
        match st.solos with
        | m :: ms =>
          if st.running.isEmpty then
            let c ← spawnW app (args m)
            st := { st with solos := ms, lastStart := now,
                            running := st.running.push { m := m, child := c, start := now, solo := true } }
        | [] =>
          if st.running.size < jobs then
            match st.pending with
            | m :: ms =>
              let c ← spawnW app (args m)
              st := { st with pending := ms, lastStart := now,
                              running := st.running.push { m := m, child := c, start := now,
                                                           solo := false } }
            | [] => pure ()
      IO.sleep 50
      loop fuel st
  let st ← loop (1 <<< 62) { pending := todo, solos := [], verdicts := logged }
  return st.verdicts

/-- **The run's verdict**: 0 when every module's worker answered 0; else the first module in
the graph's order that did not, its code (`timeout`, `memory`, `signal`: 3). -/
def summary (mods : Array Name) (vs : Std.HashMap Name String) (modeTag : String) : IO UInt8 := do
  let bad := mods.filter fun m => (vs[m]?).getD "missing" != "0"
  match bad[0]? with
  | none =>
    let o ← IO.getStdout
    o.putStrLn s!"con-leche: accepted {mods.size} modules, one worker each ({modeTag})"
    o.flush
    return 0
  | some m =>
    let w := (vs[m]?).getD "missing"
    let e ← IO.getStderr
    e.putStrLn s!"con-leche: {bad.size} of {mods.size} modules not accepted; the first in \
      the graph's order: {m} ({w}) ({modeTag})"
    e.flush
    return match w with
      | "1" => 1
      | "2" => 2
      | _ => 3

/-- **The scheduler's run**: the workers of `mods`, this binary at the arguments `args m`
(`run`), then the verdict (`summary`). -/
def runAll (parse : String → Option Name) (args : Name → Array String) (mods : Array Name)
    (o : Opts) (jobs : Nat) (modeTag : String) : IO UInt8 := do
  let vs ← run parse (← IO.appPath) args mods o jobs
  summary mods vs modeTag

end ConLeche.Driver.Schedule
