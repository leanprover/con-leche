module

public import ConLeche.Frontend.Pace

@[expose] public section

/-!
# Reading `.olean` files: what `--progress` says while they are read

The read's heartbeat (task #484): a line per step of `readOleans`, and during the load lines at
`--progress`'s pace (at a count of declarations, one per twentieth of the modules), each with the time and the resident set, so that a run that does
not get through the read says how far it got and at what size.  `IO` actions, handed to
`CheckerIO.liftIO`: nothing here changes what the read returns.
-/

namespace ConLeche.Frontend.Olean

/-- The heartbeat of one read. -/
structure ReadNotes where
  pace : Pace
  t0 : Nat
  loaded : IO.Ref Nat
  /-- when the last line was -/
  last : IO.Ref Nat

def ReadNotes.new (pace : Pace) : IO ReadNotes := do
  return ⟨pace, ← IO.monoMsNow, ← IO.mkRef 0, ← Pace.clock⟩

/-- The resident set, in the kernel's words; empty where it cannot be read. -/
def residentSet : IO String := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    for l in s.splitOn "\n" do
      if l.startsWith "VmRSS:" then
        let kb := ((l.drop 6).trimAscii.toString.takeWhile Char.isDigit).toString.toNat!
        let x := kb * 100 / 1048576
        return s!" RSS={x / 100}.{(x % 100) / 10}{x % 10}G"
    return ""
  catch _ => return ""

/-- One line of the heartbeat. -/
def ReadNotes.say (n : ReadNotes) (line : String) : IO Unit := do
  if n.pace.on then
    let e ← IO.getStderr
    let ms := (← IO.monoMsNow) - n.t0
    e.putStrLn s!"con-leche: read: {line} t={ms / 1000}.{(ms % 1000) / 100}s{← residentSet}"
    e.flush

/-- A module of `total` is loaded: a line when `Pace.coarse` of the pace says so. -/
def ReadNotes.moduleLoaded (n : ReadNotes) (total : Nat) : IO Unit := do
  if n.pace.on then
    let k ← n.loaded.modifyGet fun a => (a + 1, a + 1)
    if ← n.pace.coarse.due n.last k total then
      n.say s!"loaded {k}/{total} modules"

end ConLeche.Frontend.Olean
