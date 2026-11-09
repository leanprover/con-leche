module

public import ConLeche.Frontend.Pace

@[expose] public section

/-!
# Reading `.olean` files: what `--progress` says while they are read

The read's heartbeat (task #484): a line per step of `readOleans`, and during the load lines at
`--progress`'s pace, each with the time and the resident set, so that a run that does
not get through the read says how far it got and at what size.  `IO` actions, handed to
`CheckerIO.liftIO`: nothing here changes what the read returns.
-/

namespace ConLeche.Frontend.Olean

/-- The heartbeat of one read. -/
structure ReadNotes where
  pace : Pace
  t0 : Nat
  /-- the modules and the constants loaded so far -/
  loaded : IO.Ref (Nat × Nat)
  /-- when the last line was -/
  last : IO.Ref Nat

def ReadNotes.new (pace : Pace) : IO ReadNotes := do
  return ⟨pace, ← IO.monoMsNow, ← IO.mkRef (0, 0), ← Pace.clock⟩

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

/-- **A module of `total` is loaded**, with `size` constants.  A count of declarations is
counted in constants, so that `--progress=N` means one thing all along a run; a percentage or
the clock in modules, whose total is known. -/
def ReadNotes.moduleLoaded (n : ReadNotes) (total size : Nat) : IO Unit := do
  if n.pace.on then
    let (k, c) ← n.loaded.modifyGet fun (k, c) => ((k + 1, c + size), (k + 1, c + size))
    let due ← match n.pace with
      | .every m => pure (m > 0 && c / m != (c - size) / m)
      | p => p.due n.last k total
    if due then
      n.say s!"loaded {k} modules ({k * 100 / max 1 total}%), {c} constants"

end ConLeche.Frontend.Olean
