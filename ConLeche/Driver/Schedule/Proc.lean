module

@[expose] public section

/-!
# What the scheduler reads of the system: `/proc` and the cgroup

Reads only: the running workers' resident sets (`workerRss`: the scheduler's children in
`/proc/self/task/*/children`, each by its last argument, `/proc/<pid>/status`'s `VmRSS` and
`VmHWM`), and the OOM-kill counter of the nearest cgroup with a memory limit (`limitCgroup`,
`oomKills`), which tells a SIGKILL by the OOM killer from another (`exitVerdict`'s `oom-kill`).
Nothing here starts, kills or writes anything.
-/

namespace ConLeche.Driver.Schedule

/-- A file's contents, `none` where it cannot be read. -/
def readOpt (p : System.FilePath) : IO (Option String) := do
  try some <$> IO.FS.readFile p catch _ => pure none

/-- The cgroup the scheduler's memory is limited by: from `/proc/self/cgroup` (`0::/path`) up
through the ancestors to the first whose `memory.max` is not `max`; `none` where the files cannot
be read or no ancestor has a limit. -/
def limitCgroup : IO (Option System.FilePath) := do
  let some s ← readOpt "/proc/self/cgroup" | return none
  let some l := (s.splitOn "\n").find? (·.startsWith "0::") | return none
  let parts := ((l.drop 3).toString.splitOn "/").filter (· != "")
  for i in [0:parts.length] do
    let dir : System.FilePath := "/sys/fs/cgroup/" ++ "/".intercalate (parts.take (parts.length - i))
    if let some m ← readOpt (dir / "memory.max") then
      if m.trimAscii.toString != "max" then return some dir
  return none

/-- The `oom_kill` counter of a cgroup's `memory.events` (hierarchical), `none` where unreadable. -/
def oomKills (dir : System.FilePath) : IO (Option Nat) := do
  let some s ← readOpt (dir / "memory.events") | return none
  return (s.splitOn "\n").findSome? fun l =>
    if l.startsWith "oom_kill " then (l.drop 9).toString.trimAscii.toString.toNat? else none

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

/-- Can `workerRss` see this process's children? -/
def childrenReadable : IO Bool := do
  try
    let ts ← System.FilePath.readDir "/proc/self/task"
    match ts[0]? with
    | some t => return (← readOpt (t.path / "children")).isSome
    | none => return false
  catch _ => return false

end ConLeche.Driver.Schedule
