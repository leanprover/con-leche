module

public import ConLeche.Kernel.Env

@[expose] public section

/-!
# The scheduler's workers: what con-leche is to it

A job of the scheduler is a worker process, `con-leche --olean --module --jobs=T` of the binary
itself on one module (`workerArgs`; the module last, spelled by `spell`, which is also how the
scheduler finds the worker in `/proc`).  This module holds what is particular to that worker,
all of it pure:

* **its command line** (`workerArgs`), and the commands a user runs to check a closure without
  the scheduler (`commandLines`, `--schedule-commands`), shell-quoted (`shellQuote`);
* **what it printed** (`workerStats`, `reportedPeak`): its declarations (stdout's `accepted N
  declarations`), its parse and check phases (the `stats: phases:` line), its check pool's busy
  time and its slowest single check (the pool's `stats:` line and `slowest checks:`), and its own
  peak resident set (`stats: peak RSS`);
* **its verdict** (`exitVerdict`): its exit code (0 accept, 1 reject, 2 decline, 3 error), or
  what ended it otherwise (DESIGN #569): `Child.tryWait` returns 128 + the signal for a signalled
  child and a worker's own codes are 0 to 3, so a code above 128 is the signal `c - 128`.
  `stack` is SIGABRT with `Stack overflow detected` on the worker's stderr (Lean's
  `segv_handler`: the declaration needs a larger `LEAN_STACK_SIZE_KB`, which the workers inherit;
  the finish line adds the hint); `oom-kill` is SIGKILL while the `oom_kill` counter of the
  nearest cgroup with a memory limit (`memory.events`, found through `/proc/self/cgroup`) rose
  since the last look; any other signal reads `signal 11 (SIGSEGV)` (the number alone for an
  unnamed one), and a code between 4 and 128 `exit N`.  The scheduler's own verdicts are
  `timeout` and `memory`.
-/

namespace ConLeche.Driver.Schedule

open ConLeche

/-- A module's name as the command line spells it, each component escaped. -/
def spell (m : Name) : String :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  ".".intercalate ((comps m).map fun c => "«" ++ c ++ "»")

/-- The check mode's flag, as the workers get it and the summary names it. -/
def modeTag : CheckMode → String
  | .verified => "--verified"
  | .trusted => "--trusted"

/-- **The flags of a lookup**: `--search-path=D`, or with trusted directories `T`,
`--trusted-search-path=T --search-path=D` (each colon-separated). -/
def pathArgs (trusted dirs : String) : Array String :=
  if trusted.isEmpty then #["--search-path=" ++ dirs]
  else #["--trusted-search-path=" ++ trusted, "--search-path=" ++ dirs]

/-- **A worker's arguments** at module `m`: `--olean --module`, `--jobs=T` where `jobs` is
`some T`, the mode, the numeral bound, the lookup's flags `paths` (`pathArgs`), then `--` and
`spell m` last. -/
def workerArgs (mode : CheckMode) (maxNatSize : Nat) (paths : Array String) (jobs : Option Nat)
    (m : Name) : Array String :=
  #["--olean", "--module"] ++ (match jobs with | some t => #[s!"--jobs={t}"] | none => #[]) ++
    #[modeTag mode, s!"--max-nat-size={maxNatSize}"] ++ paths ++ #["--", spell m]

/-- **The compare worker's arguments** at challenge `c` and solution `s` (task #608):
`--olean --module --compare`, as `workerArgs`, then `--`, `spell c` and `spell s`. -/
def cmpWorkerArgs (mode : CheckMode) (paths : Array String) (jobs : Option Nat) (c s : Name) :
    Array String :=
  #["--olean", "--module", "--compare"] ++
    (match jobs with | some t => #[s!"--jobs={t}"] | none => #[]) ++
    #[modeTag mode] ++ paths ++ #["--", spell c, spell s]

/-- A word as a POSIX shell reads it back: as it is where it is not empty and holds only
letters, digits and `_-./=:,+@%`, else in single quotes, a `'` in it as `'\''`. -/
def shellQuote (s : String) : String :=
  let plain (c : Char) : Bool :=
    c.isAlphanum && c.toNat < 128 || "_-./=:,+@%".contains c
  if !s.isEmpty && s.all plain then s
  else "'" ++ "'\\''".intercalate (s.splitOn "'") ++ "'"

/-- **The commands that check a closure** (`--schedule-commands`), one line each, shell-quoted:
the graph check of `root` (`app --check-graph PATHS -- root`, `paths` the lookup's flags), then
one worker per module of `mods`, in the order given (`workerArgs` at each). -/
def commandLines (app : String) (paths : Array String) (root : Name) (cmp : Option Name)
    (mods : List Name) (args : Name → Array String) : List String :=
  let line (ws : Array String) : String := " ".intercalate (ws.toList.map shellQuote)
  line (match cmp with
    | none => #[app, "--check-graph"] ++ paths ++ #["--", spell root]
    | some s => #[app, "--check-graph", "--compare"] ++ paths ++ #["--", spell root,
        spell s]) ::
    mods.map fun m => line (#[app] ++ args m)

/-- The usual signals' names. -/
def signalName (n : Nat) : Option String :=
  match n with
  | 1 => some "SIGHUP" | 2 => some "SIGINT" | 3 => some "SIGQUIT" | 4 => some "SIGILL"
  | 6 => some "SIGABRT" | 7 => some "SIGBUS" | 8 => some "SIGFPE" | 9 => some "SIGKILL"
  | 11 => some "SIGSEGV" | 13 => some "SIGPIPE" | 15 => some "SIGTERM"
  | _ => none

/-- **A worker's verdict** from its exit code `c` (`Child.tryWait`: 128 + the signal for a signalled
child), its stderr `diag`, and whether the cgroup's OOM-kill counter rose (read only for SIGKILL):
`0` to `3` as they are; above 128 `stack` (SIGABRT and `Stack overflow detected`), `oom-kill`
(SIGKILL and a rise), else `signal N (NAME)`; `exit N` between. -/
def exitVerdict (c : Nat) (diag : String) (oom : Bool) : String :=
  if c ≤ 3 then toString c
  else if c ≤ 128 then s!"exit {c}"
  else
    let s := c - 128
    if s == 6 && (diag.splitOn "Stack overflow detected").length > 1 then "stack"
    else if s == 9 && oom then "oom-kill"
    else match signalName s with
      | some n => s!"signal {s} ({n})"
      | none => s!"signal {s}"

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

/-- The lines of a worker's stderr the scheduler passes on (for a verdict other than 0): all but
the empty ones and its statistics. -/
def passedOn (msg : String) : List String :=
  (msg.splitOn "\n").filter fun l => l != "" && !l.startsWith "con-leche: stats:"

/-- The hint after a `stack` verdict: the stack size `stackKb` the workers inherited. -/
def stackHint (m : Name) (stackKb : String) : String :=
  s!"con-leche: schedule: {m}: the worker overflowed its stack; rerun with a \
    larger LEAN_STACK_SIZE_KB (now {stackKb}; a resumed run retries it once the value \
    differs)"

end ConLeche.Driver.Schedule
