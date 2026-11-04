module

public import ConLeche.Verify.Frontend.ModelIO
public import ConLeche.Driver.Cli
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Verify.Frontend.ModelIO
meta import ConLeche.Driver.Cli

public section

/-!
# The binary's file operations against the model (tasks #424, #450)

The trust assumption of `ConLeche/Frontend/CheckerIO.lean` is that the
binary's file operations give the model's answers on a snapshot of the
files.  Here the snapshot of a few committed fixtures (`tests/e2e`), a
directory and a path that names nothing is taken with the runtime's
calls, and every operation of the binary's instance is compared with
the model's answer on it — the instance's definitions restated as data
(`modelAnswer_*`, each the model by `rfl`): the positional read inside,
across and past the end of each file and at huge offsets and lengths,
the size, the bytes, existence and the real path.  The folds over a
file's reads are compared with what the model's folds are
(`foldChunks_model`, `foldWindows_model`): the reads `readsFrom` and the
windows `windowsOf` of the snapshot's bytes.  The binary's exit codes
are the end-to-end fixtures' (`tests/e2e-expected.txt`), and a FIFO as
the input is `tests/arena.sh`'s.
-/

namespace ConLecheTests.CheckerIOTests

open ConLeche

/-- **The snapshot of some files**, taken now: each path's real path,
and each regular file's bytes by its real path; a path that names
nothing has none. -/
def snapshot (paths : List System.FilePath) : IO FS := do
  let mut real : Array (System.FilePath × System.FilePath) := #[]
  let mut bytes : Array (System.FilePath × ByteArray) := #[]
  for p in paths do
    if ← p.pathExists then
      let r ← IO.FS.realPath p
      real := real.push (p, r)
      unless ← p.isDir do bytes := bytes.push (r, ← IO.FS.readBinFile p)
  let reals := real
  let files := bytes
  return { real := fun q => (reals.find? (·.1 == q)).map (·.2),
           bytes := fun r => (files.find? (·.1 == r)).map (·.2) }

/-! ## The model's answers, as data -/

def modelPathExists (fs : FS) (p : System.FilePath) : Option Bool := some (fs.real p).isSome
def modelRealPath (fs : FS) (p : System.FilePath) : Option System.FilePath := fs.real p
def modelReadBinFile (fs : FS) (p : System.FilePath) : Option ByteArray := fs.file p
def modelReadRange (fs : FS) (p : System.FilePath) (off len : Nat) : Option ByteArray :=
  (fs.file p).map fun b => b.extract off (min (off + len) b.size)
def modelFileSize (fs : FS) (p : System.FilePath) : Option Nat := (fs.file p).map (·.size)

example (fs : FS) (p : System.FilePath) :
    (CheckerIO.pathExists p : ModelIO _) fs = ModelIO.answer (modelPathExists fs p) := rfl
example (fs : FS) (p : System.FilePath) :
    (CheckerIO.realPath p : ModelIO _) fs = ModelIO.answer (modelRealPath fs p) := rfl
example (fs : FS) (p : System.FilePath) :
    (CheckerIO.readBinFile p : ModelIO _) fs = ModelIO.answer (modelReadBinFile fs p) := rfl
example (fs : FS) (p : System.FilePath) (off len : Nat) :
    (CheckerIO.readRange p off len : ModelIO _) fs =
      ModelIO.answer (modelReadRange fs p off len) := rfl
example (fs : FS) (p : System.FilePath) :
    (CheckerIO.fileSize p : ModelIO _) fs = ModelIO.answer (modelFileSize fs p) := rfl

/-- A model's answer, rendered: the value, or an exception (its value is
not compared, as the trust assumption has it). -/
def render {α : Type} (show_ : α → String) : Option α → String
  | some a => show_ a
  | none => "IO error"

/-- The binary's outcome, rendered as the model's is. -/
def renderIO {α : Type} (show_ : α → String) (x : IO α) : IO String := do
  match ← x.toBaseIO with
  | .ok a => pure (show_ a)
  | .error _ => pure "IO error"

def same (what a b : String) : IO Unit :=
  unless a == b do throw (IO.userError s!"{what}: the model and the binary differ:\n{a}\n{b}")

/-- The windows' fold with a recording step, in the model: each window's
chunk sizes and the size of the window handed to it as the next, then
the tail's size (what `ModelIO.foldWins` over `windowsOf` returns for
the step below). -/
def recordWins : List (Array ByteArray) → ByteArray → List (List Nat)
  | [], tail => [[tail.size]]
  | w :: ws, tail => [w.toList.map (·.size), [(ws.headD #[]).size]] ++ recordWins ws tail

def fixtures : List String :=
  ["tests/e2e/and_rec_def.ndjson", "tests/e2e/final_line_no_newline.ndjson",
   "tests/e2e/nat_ops.ndjson", "tests/e2e/malformed_midstream.ndjson",
   "tests/e2e/str_lit_declined.ndjson", "tests/e2e/nat_add_wrong.ndjson"]

#eval show IO Unit from do
  let missing := "tests/e2e/no_such_file.ndjson"
  let dir := "tests/e2e"
  let paths : List System.FilePath := (fixtures ++ [missing, dir]).map (⟨·⟩)
  let fs ← snapshot paths
  -- the file operations, against the model's answers
  for p in paths do
    same s!"pathExists {p}" (← renderIO toString (CheckerIO.pathExists p))
      (render toString (modelPathExists fs p))
    same s!"realPath {p}" (← renderIO toString (CheckerIO.realPath p))
      (render toString (modelRealPath fs p))
    same s!"readBinFile {p}" (← renderIO (toString ·.toList) (CheckerIO.readBinFile p))
      (render (toString ·.toList) (modelReadBinFile fs p))
    same s!"fileSize {p}" (← renderIO toString (CheckerIO.fileSize p))
      (render toString (modelFileSize fs p))
    -- the positional read: inside, across and past the end, and huge
    -- offsets and lengths (below `2^64`: the runtime's `ByteArray.extract`,
    -- which the model's read is, runs out of memory at a start that is
    -- not a machine word)
    let size := (modelFileSize fs p).getD 0
    for (off, len) in [(0, 0), (0, 1), (0, 100), (5, 7), (100, 4096), (0, 1 <<< 40),
        (size - 3, 10), (size, 1), (size + 1, 5), (size - 1, 1),
        (1 <<< 20, 10), (1 <<< 62, 10), (1 <<< 63, 10), (1 <<< 63, 1 <<< 70)] do
      same s!"readRange {p} {off} {len}"
        (← renderIO (toString ·.toList) (CheckerIO.readRange p off len))
        (render (toString ·.toList) (modelReadRange fs p off len))
  -- the folds over a file's reads: every read in order (`readsFrom`),
  -- and every window with the one handed to it as the next (`windowsOf`)
  let chunkStep (acc : List (List UInt8)) (c : ByteArray) :
      Except (List (List UInt8)) (List (List UInt8)) := .ok (acc ++ [c.toList])
  let winStep (acc : List (List Nat)) (w : Array ByteArray)
      (nxt : IO (Array ByteArray)) : IO (Except (List (List Nat)) (List (List Nat))) := do
    let n ← nxt
    pure (.ok (acc ++ [w.toList.map (·.size), [n.size]]))
  for p in paths do
    for csz in [1, 7, 64, 4096] do
      same s!"foldChunks {p} {csz}"
        (← renderIO toString (foldChunks p csz.toUSize [] chunkStep id : IO _))
        (render toString ((modelReadBinFile fs p).map fun b =>
          (readsFrom csz b 0).map (·.toList)))
      for w in [0, 1, 3] do
        same s!"foldWindows {p} {csz} {w}"
          (← renderIO toString (foldWindows p csz.toUSize w [] winStep
            (fun acc t => acc ++ [[t.size]]) : IO _))
          (render toString ((modelReadBinFile fs p).map fun b =>
            recordWins (windowsOf csz.toUSize w b).1 (windowsOf csz.toUSize w b).2))

/-! ## The command line (`--`): after it, everything is a file -/

example : (ConLeche.Driver.parseArgs ["--", "--help"] {}).files = #["--help"] := by
  simp [ConLeche.Driver.parseArgs]
#guard (ConLeche.Driver.parseArgs ["--", "-weird-name.ndjson"] {}).files == #["-weird-name.ndjson"]
#guard (ConLeche.Driver.parseArgs ["--", "-weird-name.ndjson"] {}).bad.isNone
#guard (ConLeche.Driver.parseArgs ["--jobs=2", "--", "--trusted", "--"] {}).files ==
  #["--trusted", "--"]
#guard (ConLeche.Driver.parseArgs ["--jobs=2", "--", "--trusted"] {}).jobs == some 2
#guard !ConLeche.Driver.helpWanted ["--", "--help"]
#guard ConLeche.Driver.helpWanted ["--help", "--", "x"]
#guard ConLeche.Driver.helpWanted ["x", "--help"]
/-- No flag: the verified mode. -/
example : (ConLeche.Driver.parseArgs ["--", "x"] {}).mode = .verified := by
  simp [ConLeche.Driver.parseArgs]

end ConLecheTests.CheckerIOTests
