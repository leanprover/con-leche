module

@[expose] public section

/-!
# Reading `.olean` files: what `--progress` says while they are read

The read's heartbeat (task #484): a line per step of `readOleans`, and during the load a line
per twentieth of the modules, each with the time and the resident set, so that a run that does
not get through the read says how far it got and at what size.  `IO` actions, handed to
`CheckerIO.liftIO`: nothing here changes what the read returns.
-/

namespace ConLeche.Frontend.Olean

/-- The heartbeat of one read: `stride` is `--progress`'s, `0` off. -/
structure ReadNotes where
  stride : Nat
  t0 : Nat
  loaded : IO.Ref Nat

def ReadNotes.new (stride : Nat) : IO ReadNotes := do
  return ⟨stride, ← IO.monoMsNow, ← IO.mkRef 0⟩

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
  if n.stride > 0 then
    let e ← IO.getStderr
    let ms := (← IO.monoMsNow) - n.t0
    e.putStrLn s!"con-leche: read: {line} t={ms / 1000}.{(ms % 1000) / 100}s{← residentSet}"
    e.flush

/-- A module of `total` is loaded: a line per twentieth of them. -/
def ReadNotes.moduleLoaded (n : ReadNotes) (total : Nat) : IO Unit := do
  if n.stride > 0 then
    let k ← n.loaded.modifyGet fun a => (a + 1, a + 1)
    if k % (max 1 (total / 20)) == 0 then
      n.say s!"loaded {k}/{total} modules"

end ConLeche.Frontend.Olean
