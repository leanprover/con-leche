module

public import ConLeche.Frontend.ReadRange

@[expose] public section

/-!
# The checker's file reads, as a type class with a model (task #450)

The driver's reads of the files are written against `CheckerIO m`, a
monad with the few file operations the checker needs, instead of
against `IO`; everything else the driver does at the runtime — output,
diagnostics, the clock, the persistent mark,
and every thread (the rounds parse's owners, the install and the check
pools) — is an `IO` action handed to the class's one escape,
`CheckerIO.liftIO`.  The same code runs at two instances:

* **`IO`** (`instCheckerIOIO`): the binary.  Each file operation is the
  runtime's own call (`System.FilePath.pathExists`, `IO.FS.realPath`,
  `IO.FS.readBinFile`, a file's metadata, and the positional read
  `readRangeIO`, `pread(2)` in C), and `liftIO` is the identity.
* **`ModelIO`**: a model, a NON-DETERMINISM monad over a file system
  snapshot `FS` (a real path for every path that names something, bytes
  for every regular file by its real path): an action is the set of its
  possible outcomes, a value or an exception, on the snapshot.  The file
  operations' outcomes are determined by the snapshot (an exception
  where it has no such file, its value not specified); `liftIO a` may
  have EVERY outcome, any value of its type or any exception.  The model
  is reasoned about, not executed.

**What is proved, and what is trusted.**  The theorems
(`Driver.runArgs_accept`, `ConLeche.main_model`, `ConLeche.main_no_False`)
say: every outcome of `Driver.runArgs` in the model that is the exit code
0 implies the statement.  The binary's `main` is `enableAbortOnNonlinear`,
then the same generic `runArgs` at `IO`, then the flush and the exit with
the code it returned; those few lines are read, not proved, and the
theorems cover `runArgs`.  The code is computed by the generic code and returned outside `liftIO`
(were it `liftIO`'s result, the model would allow any).  The binary's
run is one of the model's outcomes, and its exit code that outcome's,
if

1. the binary's file operations give the model's answers on one
   snapshot of the files during the run — the same value where the
   model has one, an exception where the model's outcome is one —
   including the C function behind `readRange` (`readRangeIO`,
   `native/read_range.c`), which must return the model's slice;
2. the actions passed to `liftIO` do not change what the file operations
   see (none of them writes a file: they print, read the clock and
   `/proc/self/status`, start and join threads, and compute), and do not
   themselves end the process with an exit code: `IO.Process.exit` is
   only in `main`, outside `runArgs`, last with the code `runArgs`
   returned and, before `runArgs` starts, with 3 if the abort variables
   cannot be set (`tests/trust-surface.sh` checks that these two are
   the only ones, textually); a panic is an `abort()`, status 134, never
   a verdict; and
3. Lean's compiler and runtime run the code as written.

The argument is then plain: the generic code is the same at both
instances; at every file operation the binary's answer is, by (1) and
(2), the model's; at every `liftIO` the binary's answer is SOME value or
exception, and the model allows every one.  So, by induction along the
run, the binary's outcome is one of the model's outcomes, and what is
proved about all of those holds of it.  Where the driver needs a fact
about a `liftIO` result (the fold's accept), the result's type carries
it (`{ env // checkDecls … = .ok env }`), so every outcome the model
allows carries it too.

**Reading a file in pieces** is ordinary code over the class, not an
operation of it: `foldReads` steps through a file's positional reads in
order, `foldChunks` (the serial parse) and `foldWindows` (the rounds
parse: the reads cut at their last newlines, taken a window at a time)
are folds over it.  In the model they are folds over the snapshot's
bytes cut as the reads cut them (`ConLeche/Verify/Frontend/ModelIO.lean`).
-/

namespace ConLeche

/-! ## Reading a stream: the cuts -/

/-- The last newline of `b` below `i`. -/
def lastNewlineBelow (b : @& ByteArray) : Nat → Option Nat
  | 0 => none
  | i + 1 => if b.get! i == 10 then some i else lastNewlineBelow b i

/-- **One read, cut at its last newline** (the windows' chunks): the
chunk of whole lines the read completes, with the bytes carried from
the reads before it in front, if the read holds a newline; and the
bytes after the last newline, carried into the next read (all of them,
the carried bytes and the read, when it holds none). -/
@[inline] def cutRead (pending buf0 : ByteArray) : Option ByteArray × ByteArray :=
  match lastNewlineBelow buf0 buf0.size with
  | none => (none, pending ++ buf0)
  | some k =>
    (some (if pending.isEmpty then buf0.extract 0 (k + 1)
      else pending ++ buf0.extract 0 (k + 1)), buf0.extract (k + 1) buf0.size)

/-- **The checker's file reads** (task #450): what the driver's reads of
the files need, and the escape `liftIO` for everything else.
`MonadExceptOf IO.Error`: an operation may fail, as the runtime's
does. -/
class CheckerIO (m : Type → Type) extends Monad m, MonadExceptOf IO.Error m where
  /-- whether the path names something (a file, a directory) -/
  pathExists : System.FilePath → m Bool
  /-- the path with every symbolic link resolved, absolute; throws where
  the path names nothing -/
  realPath : System.FilePath → m System.FilePath
  /-- a regular file's bytes; throws where there is none -/
  readBinFile : System.FilePath → m ByteArray
  /-- **a positional read** of a regular file: the bytes from `off` up to
  `off + len` or the end of the file, whichever comes first (a read at or
  past the end is empty); throws where the path names no regular file.
  It keeps no state: every read names its file and its offset. -/
  readRange : System.FilePath → (off len : Nat) → m ByteArray
  /-- the size of a regular file in bytes; throws where the path names
  none -/
  fileSize : System.FilePath → m Nat
  /-- **the escape**: an `IO` action that performs none of the operations
  above — output, diagnostics, the clock, threads; in the model, any
  outcome at all.  An explicit method on purpose: there is no
  `MonadLift IO m` instance, so `IO` is never lifted implicitly by a
  `←`, and every unverified call site spells `CheckerIO.liftIO` (the
  boundary stays visible and greppable). -/
  liftIO : {α : Type} → IO α → m α

/-! ## Reading a file in pieces: ordinary code over the class -/

/-- **The reads of a file, in order**: `rd off` for `off = 0, csz, 2·csz, …`
below `size`, each read handed to `step` with the state, up to the first
`.error`, which is the result; after the last read, `fin` of the state.
No read at `csz = 0`.  The state is a plain argument, so that it stays
uniquely referenced across the step (task #78). -/
@[specialize] def foldReads {m : Type → Type} [Monad m] {σ ρ : Type} (rd : Nat → m ByteArray)
    (csz size : Nat) (step : σ → ByteArray → m (Except ρ σ)) (fin : σ → m ρ)
    (off : Nat) (s : σ) : m ρ :=
  if _h : 0 < csz ∧ off < size then do
    match ← step s (← rd off) with
    | .error r => pure r
    | .ok s => foldReads rd csz size step fin (min (off + csz) size) s
  else fin s
termination_by size - off
decreasing_by omega

/-- **The serial fold over a file's bytes**: `step` on every read of
`csz` bytes in order, from `init`, up to its first `.error`, which is
the result; at the end of the file, `fin` of the state.  The file's
size is read first: a path that names no regular file fails there. -/
@[inline] def foldChunks {m : Type → Type} [CheckerIO m] {σ ρ : Type} (p : System.FilePath)
    (csz : USize) (init : σ) (step : σ → ByteArray → Except ρ σ) (fin : σ → ρ) : m ρ := do
  let size ← CheckerIO.fileSize p
  foldReads (fun off => CheckerIO.readRange p off csz.toNat) csz.toNat size
    (fun s c => pure (step s c)) (fun s => pure (fin s)) 0 init

/-- The windows' fold state: the caller's state, the last full window
not yet stepped, the chunks gathered for the next window, the bytes
after the last newline read. -/
abbrev WinBuf (σ : Type) := σ × Option (Array ByteArray) × Array ByteArray × ByteArray

/-- One read of the windows' fold: cut at its last newline (`cutRead`),
its chunk, if any, gathered; when `w` chunks are gathered they are the
next full window, and the full window before it is stepped, handed this
one as the window to come. -/
@[inline] def winRead {m : Type → Type} [Monad m] {σ ρ : Type} (w : Nat)
    (step : σ → Array ByteArray → m (Array ByteArray) → m (Except ρ σ)) :
    WinBuf σ → ByteArray → m (Except ρ (WinBuf σ))
  | (s, prev, acc, pending), r =>
    match cutRead pending r with
    | (none, p) => pure (.ok (s, prev, acc, p))
    | (some c, p) =>
      let acc := acc.push c
      if w ≤ acc.size then
        match prev with
        | none => pure (.ok (s, some acc, #[], p))
        | some pw => do
          match ← step s pw (pure acc) with
          | .error r => pure (.error r)
          | .ok s => pure (.ok (s, some acc, #[], p))
      else pure (.ok (s, prev, acc, p))

/-- The last chunks gathered, a window of their own unless there are
none, stepped as the last window. -/
@[inline] def winLast {m : Type → Type} [Monad m] {σ ρ : Type}
    (step : σ → Array ByteArray → m (Array ByteArray) → m (Except ρ σ))
    (fin : σ → ByteArray → ρ) (s : σ) (acc : Array ByteArray) (pending : ByteArray) : m ρ :=
  if acc.isEmpty then pure (fin s pending)
  else do
    match ← step s acc (pure #[]) with
    | .error r => pure r
    | .ok s => pure (fin s pending)

/-- The windows' fold's end: the full window not yet stepped, handed the
last chunks as the window to come, then those. -/
@[inline] def winEnd {m : Type → Type} [Monad m] {σ ρ : Type}
    (step : σ → Array ByteArray → m (Array ByteArray) → m (Except ρ σ))
    (fin : σ → ByteArray → ρ) : WinBuf σ → m ρ
  | (s, none, acc, pending) => winLast step fin s acc pending
  | (s, some pw, acc, pending) => do
    match ← step s pw (pure acc) with
    | .error r => pure r
    | .ok s => winLast step fin s acc pending

/-- **The fold over a file's windows**: the file read in reads of `csz`
bytes, each cut at its last newline (`cutRead`), and the chunks of whole
lines taken `w` at a time; `step` on every window in order, handed
besides the next window to come (an empty array after the last), up to
its first `.error`; at the end, `fin` of the state and the bytes after
the file's last newline.  Sequential: a window is stepped once the next
one has been read.  No window at `w = 0`. -/
@[inline] def foldWindows {m : Type → Type} [CheckerIO m] {σ ρ : Type} (p : System.FilePath)
    (csz : USize) (w : Nat) (init : σ)
    (step : σ → Array ByteArray → m (Array ByteArray) → m (Except ρ σ))
    (fin : σ → ByteArray → ρ) : m ρ := do
  let size ← CheckerIO.fileSize p
  if w = 0 then return fin init .empty
  foldReads (fun off => CheckerIO.readRange p off csz.toNat) csz.toNat size
    (winRead w step) (winEnd step fin) 0 (init, none, #[], .empty)

/-! ## The model -/

/-- **A file system snapshot**: the real path of every path that names
something, and the bytes of every regular file, by its real path. -/
structure FS where
  /-- the real path of a path that names something, `none` where nothing is -/
  real : System.FilePath → Option System.FilePath
  /-- a regular file's bytes, by its real path; `none` for a directory or
  anything else that is not a readable regular file -/
  bytes : System.FilePath → Option ByteArray

/-- A regular file's bytes by any path to it. -/
def FS.file (fs : FS) (p : System.FilePath) : Option ByteArray := (fs.real p).bind fs.bytes

/-- **The model's monad**: an action is the set of its possible
outcomes on a snapshot — a value, or an exception.  A run that does not
end has no outcome (no loop of the driver needs one: they all
terminate). -/
def ModelIO (α : Type) : Type := FS → Except IO.Error α → Prop

instance : Monad ModelIO where
  pure a := fun _ o => o = .ok a
  bind x f := fun fs o => (∃ a, x fs (.ok a) ∧ f a fs o) ∨ (∃ e, o = .error e ∧ x fs (.error e))

instance : MonadExceptOf IO.Error ModelIO where
  throw e := fun _ o => o = .error e
  tryCatch x h := fun fs o => (∃ a, o = .ok a ∧ x fs (.ok a)) ∨ (∃ e, x fs (.error e) ∧ h e fs o)

/-- An outcome determined by a snapshot's answer: the value where there
is one, some exception where there is none. -/
def ModelIO.answer {α : Type} : Option α → Except IO.Error α → Prop
  | some a, o => o = .ok a
  | none, o => ∃ e, o = .error e

/-- **The model**: every file operation is determined by the snapshot; a
positional read is the slice of the file's bytes from `off` to
`off + len`, cut at the end of the file (`min (off + len) b.size`; the
slice is defined at every `Nat` offset and length, empty where the
start is not below the end); `liftIO` may have any outcome. -/
instance : CheckerIO ModelIO where
  pathExists p := fun fs o => o = .ok (fs.real p).isSome
  realPath p := fun fs => ModelIO.answer (fs.real p)
  readBinFile p := fun fs => ModelIO.answer (fs.file p)
  readRange p off len := fun fs =>
    ModelIO.answer ((fs.file p).map fun b => b.extract off (min (off + len) b.size))
  fileSize p := fun fs => ModelIO.answer ((fs.file p).map (·.size))
  liftIO _ := fun _ _ => True

/-! ## The binary's instance -/

/-- **A positional read at `IO`**: `readRangeIO` (`pread(2)`).  A regular
file has fewer than `2^63` bytes (its size is an `off_t`), so a read at
an offset of `2^63` or more is past its end and empty, and no read
returns more than `2^63 - 1` bytes: the arguments the C function takes
as 64-bit words are those, and the slice is the model's. -/
def readRangeOf (p : System.FilePath) (off len : Nat) : IO ByteArray :=
  if off < 2 ^ 63 then readRangeIO p.toString off.toUInt64 (min len (2 ^ 63 - 1)).toUInt64
  else do
    -- past the end of any regular file: the read is empty, once the
    -- path is known to name one (the C function's checks)
    let _ ← readRangeIO p.toString 0 0
    pure .empty

/-- **The binary's instance**: the runtime's calls; `liftIO` the identity. -/
instance instCheckerIOIO : CheckerIO IO where
  pathExists p := p.pathExists
  realPath p := IO.FS.realPath p
  readBinFile p := IO.FS.readBinFile p
  readRange p off len := readRangeOf p off len
  fileSize p := do
    let md ← System.FilePath.metadata p
    if md.type == .file then pure md.byteSize.toNat
    else throw (.inappropriateType (some p.toString) 21 "not a regular file")
  liftIO a := a

end ConLeche
