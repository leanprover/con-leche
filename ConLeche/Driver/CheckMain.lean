module

public import ConLeche.Frontend.Prelude
public import ConLeche.Driver.StreamParse
public import ConLeche.Driver.Run
public import ConLeche.Frontend.Olean

/-!
# The driver's sequencing, generic in the IO class (tasks #424, #450)

`checkMainG` is the driver of one run — the built-in prelude, the
input's records (a stream, read through the class's file operations),
the preparation, the fold, the verdict line and the exit code —
written against `CheckerIO`.  The binary runs it at `IO` (`Cli.lean`
runs it through `runReq`); the theorem below is about its run in the
model `ModelIO` over a snapshot of the files.  The output, the clock
and the fold's two phases with their thread pools (`checkDeclsIO`,
`ConLeche/Driver/Run.lean`) are `IO` actions handed to
`CheckerIO.liftIO`; the fold's result carries its proof in its type.

* `checkMainG_ndjson_accept`: an exit 0 on a stream means the file's
  bytes in the snapshot, as one chunk, parse to records that
  `checkDecls` accepts once prepared with the built-in prelude — the
  hypothesis of the main corollary (`ConLeche.no_False_declaration`)
  about the file itself, under the assumptions stated in
  `ConLeche/Frontend/CheckerIO.lean`.
-/

@[expose] public section

/-- Exit codes follow the lean kernel arena convention: 0 all
declarations accepted, 1 a declaration was rejected as invalid, 2 the
checker declined (positively detected an unsupported feature), 3 bad
usage, malformed input, or an internal failure of unclear cause. -/
def ConLeche.CheckError.exitCode : CheckError → UInt8
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- No error is an accept. -/
theorem ConLeche.CheckError.exitCode_ne_zero (e : ConLeche.CheckError) : e.exitCode ≠ 0 := by
  cases e <;> simp [ConLeche.CheckError.exitCode]

namespace ConLeche.Driver

/-- A declaration's display name, for the direct-parse `Declaration` records.  The
formatting itself lives beside the checker (`ConLeche.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : ConLeche.Declaration → String := ConLeche.Cached.declCLabel

open ConLeche

/-- **What a run reads**: a lean4export stream, or the import closure of
root modules read from their `.olean` files along a search path.  Either
read ends in `Declaration` records, and everything after it works on
those. -/
inductive Input where
  | ndjson (file : String)
  | oleans (searchPath : List System.FilePath) (roots : Array ConLeche.Name)
      (constants : Option (Array ConLeche.Name))

/-- The input's name in a diagnostic. -/
def Input.label : Input → String
  | .ndjson f => f
  | .oleans _ rs _ => String.intercalate " " (rs.toList.map toString)

/-- A line on stderr: a diagnostic (`liftIO`). -/
@[inline] def diagLine {μ : Type → Type} [CheckerIO μ] (s : String) : μ Unit :=
  CheckerIO.liftIO do
    let e ← IO.getStderr
    e.putStrLn s
    e.flush

/-- A line on stdout, flushed: the verdict (`liftIO`). -/
@[inline] def outLine {μ : Type → Type} [CheckerIO μ] (s : String) : μ Unit :=
  CheckerIO.liftIO do
    let o ← IO.getStdout
    o.putStrLn s
    o.flush

/-- The monotonic clock in milliseconds, for diagnostics (`liftIO`). -/
@[inline] def clockMs {μ : Type → Type} [CheckerIO μ] : μ Nat :=
  CheckerIO.liftIO IO.monoMsNow

/-- The input's declaration records: the stream's, by the stream parse
(`parseStreamG`), or the closure's, by the `.olean` reader
(`Frontend.Olean.readOleans`). -/
def readInputG {μ : Type → Type} [CheckerIO μ] (inp : Input) (jobs : Nat) :
    μ (Except (CheckError × Nat) (Array Declaration)) :=
  match inp with
  | .ndjson file => do
    return (← parseStreamG file jobs).map (·.decls)
  | .oleans sp roots cs => Frontend.Olean.readOleans sp roots cs jobs

/-- **The driver, generic in the IO class** (tasks #424, #450): what
`main` runs in process (at `IO`) and what the theorem is about (at
`ModelIO`).  `mode` is the
checking mode, validated once by the caller and consumed here as
configuration.

**One core at two modes, one parse.**  The stream is parsed directly
to `Expr` (`parseStreamG`) and checked by the one
driver — `checkDeclsIO` in `ConLeche/Driver/Run.lean`, through `liftIO` — at `.verified` under `--verified` (the
default), at `.trusted` under `--trusted`.  The driver returns the
environment with the proof that the fold `checkDecls` returns it, the
fold the main theorem `ConLeche.model_exists`
(`ConLeche/MainTheorem.lean`) is about; the trusted instance is
unverified by design.

**The main corollary's chain is what the three phases below compute**
(`ConLeche.no_False_declaration`, `ConLeche/MainTheorem.lean`: the
built-in prelude parses, the chunks parse, `checkDecls .verified`
accepts the parsed records prepared with the prelude).  The prelude
step is the same function, `Frontend.builtinPreludeE`.  The parse
(`parseStreamG`) reads the file through the class's folds: every step
is `chunkStep`, run by the serial parse or, for a window of the rounds
parse, established from the good entries its rounds built
(`Frontend.GOK.window`), so that in the model the parse is
`Frontend.parseChunks` of the file's reads, and the chunk boundaries
are proved invisible (`parseStreamG_model`: the file's bytes as one
chunk).  `Frontend.prepareD` is `Frontend.preparePrelude` plus the
receipts printed below.  `checkDeclsIO` returns its environment with
the evidence `checkDecls mode natOpPinSets ds = .ok env`.  What the driver adds is
IO — the heartbeat, the parallel check pool, the diagnostics that say
which step failed and with what exit code — and none of it touches
the verdict.  The three steps fail in ONE error type, the checker's
`CheckError` with the failure's position, which is why the
chain is one `do` block up there and why the exit code below is
`CheckError.exitCode` whichever step produced it. -/
def checkMainG {μ : Type → Type} [CheckerIO μ] (input : Input) (mode : CheckMode)
    (stride jobs : Nat) : μ UInt8 := do
    -- The opt-in progress heartbeat (`--progress[=<stride>]`):
    -- validated by the argument parse, before any work is done, and
    -- handed down as configuration.  EVERY SWITCH THAT SHAPES A
    -- VERDICT IS A COMMAND-LINE FLAG, so a verdict's provenance is
    -- readable off the invocation and off nothing else.  The binary
    -- reads no environment variable.
    let t0 ← clockMs
    -- Every VERDICT line names the mode: a `--trusted`
    -- run — the unverified lane — must never be mistaken for a
    -- `--verified` one in a log, whatever it says.
    let modeTag : String := match mode with
      | .verified => "--verified"
      | .trusted => "--trusted"
    -- THE BUILT-IN PRELUDE (`ConLeche/Frontend/Prelude.lean`): the
    -- pinned basis blocks, `Bool` and `And`, parsed from the
    -- committed `pins/<toolchain>.prelude.ndjson`.  `preparePrelude`
    -- PREPENDS them to the parsed stream, so the fold
    -- installs them first and unconditionally; a stream's own copy of
    -- one is dropped there when identical, and the fold declines the
    -- run when it differs.  A prelude that does not parse is a
    -- corrupted build, reported before any input is read.
    let prelude ← match Frontend.builtinPreludeE with
      | .ok p => pure p
      | .error (.internal msg, line) =>
        diagLine s!"con-leche: the built-in prelude does not parse (line \
          {line}: {msg}); regenerate it with `lake exe natop-pins-export` \
          ({modeTag})"
        return 3
      | .error (.notImplemented what, _) =>
        diagLine s!"con-leche: the built-in prelude is unsupported ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
      | .error (.invalid what, _) =>
        diagLine s!"con-leche: the built-in prelude contradicts itself ({what}); \
          regenerate it with `lake exe natop-pins-export` ({modeTag})"
        return 3
    -- Streaming frontend: the parse reads the file line by line, so
    -- neither a wholesale text buffer nor a scratch file exists in
    -- this process.
    match ← readInputG input jobs with
    | .error (.notImplemented what, _) =>
      diagLine s!"con-leche: declined: {what} ({modeTag})"
      return 2
    -- A stream whose inductive block
    -- contradicts its own declarations in a REDUNDANT field is
    -- rejected at the parse, as official's replay rejects a recursor
    -- or constructor record that is not the generated one.
    | .error (.invalid what, _) =>
      diagLine s!"con-leche: invalid: {what} ({modeTag})"
      return 1
    | .error (.internal msg, line) =>
      diagLine s!"con-leche: {input.label}:{line}: {msg}"
      return 3
    | .ok parsed =>
      -- **PREPARE** (`ConLeche/Frontend/Prepare.lean`): the
      -- parsed array is the FILE's records; what the fold runs over is `preparePrelude` of it —
      -- the built-in prelude's records, then the stream's, recognised,
      -- deduped against the prelude and ground-hoisted.  Fold positions
      -- count from the prelude's first record; the VERDICT's count is
      -- the file's own (`parsed.size`), which no step
      -- below changes.
      let ⟨decls, synthesised, hoisted⟩ := Frontend.prepareD prelude parsed
      -- the ground hoist's receipt
      -- (`ConLeche/Frontend/NatOpGround.lean`): records moved ahead of a
      -- pinned Nat operation whose certificate statements they ground
      if hoisted.size > 0 then
        diagLine s!"con-leche: {hoisted.size} declarations hoisted ahead of \
          the pinned Nat operations they ground: \
          {String.intercalate ", " (hoisted.toList.map toString)}"
      -- ONE driver, two modes: the trusted
      -- mode is the shared bodies at `.trusted`, the verified mode the
      -- same bodies at `.verified` — the mode is passed straight down.
      -- **One driver, and it returns its proof.**  `checkDeclsIO`
      -- above runs the fold's two phases — phase A installs every
      -- record and carries its accepting run, phase B checks every
      -- recorded declaration against the prefix view of the installed
      -- index and carries every check — and what comes out is the
      -- environment with the proof that `ConLeche.Cached.checkDecls`
      -- returns it, the fold the main theorem
      -- `ConLeche.model_exists` (`ConLeche/MainTheorem.lean`) is
      -- about.  The success line below is printed from that value and
      -- from nothing else.  Printing between the steps (`--progress`)
      -- changes nothing about the proof, so there is no second loop.
      --
      -- **Reading the index**: `i` is the *fold* position, and it is
      -- NOT the file's declaration-record index.  The prepared list
      -- begins with the built-in prelude's records and drops the
      -- stream's identical copies of them.  (Raw `init-full` declares
      -- every prelude declaration itself, so there the preparation
      -- synthesises NONE of them and only moves the stream's own
      -- records to the front.)  The declaration NAME on the line is
      -- the portable handle.
      -- The heartbeat's first line (`--progress`): the parse is done,
      -- and the fold is about to start on this many records.  The
      -- install and check phases print their own lines
      -- (`checkDeclsIO`), and the summary closes the run.
      let tParse ← clockMs
      if stride > 0 then
        diagLine s!"con-leche: parse done: {decls.size} fold records — \
          the file's {parsed.size}, \
          {synthesised} built-in prelude records synthesised \
          t={ConLeche.Cached.msSecs (tParse - t0)}s \
          (parse {ConLeche.Cached.msSecs (tParse - t0)}s)"
      let verdict ← CheckerIO.liftIO do
        checkDeclsIO mode (← IO.getStderr) stride decls.size t0 tParse jobs decls
      match verdict with
      | .ok _ =>
        -- **The headline number is the FILE's declaration-record
        -- count**: the records
        -- the PARSE produced, which are the file's own.  Nothing the
        -- prepare step does — prepending the prelude, dropping a
        -- stream copy of one of its records, hoisting — moves it: a
        -- stream re-declaring `Bool` identically reports the same
        -- count as before the prelude existed, and a stream's five
        -- quotient records count as the five records they are.
        --
        -- The number of environment CONSTANTS is not that number —
        -- an inductive block's type former, its constructors, its
        -- recursor, its projection table and the basis extras count
        -- separately — and it is a property of our REPRESENTATION,
        -- not of the input: it moves whenever the representation
        -- moves.  The record count is a property of the input.
        --
        -- It still does not equal the official checker's number, and
        -- it cannot: official prints `constMap.size`, its PARSED
        -- export, where an inductive record counts as its type
        -- formers, its constructors and its recursors (less the three
        -- `Quot.mk`/`.lift`/`.ind` entries it erases).  That is a
        -- third unit — also a function of the file, just a larger one.
        -- `scripts/stream-census.py` derives BOTH numbers from a
        -- stream and is checked against both checkers' actual output,
        -- which is where a run's constant count is read off.
        outLine s!"con-leche: accepted {parsed.size} \
          declarations ({modeTag})"
        return 0
      | .error (e, i) =>
        -- **No second pass**: the fold's error carries the failing
        -- declaration's FOLD POSITION, so the message is read off the
        -- record array the driver already holds — never a diagnostic
        -- re-run of the accepted prefix, which would be a lie waiting
        -- to happen if the two runs ever disagreed.
        --
        -- `i` is the FOLD position.  The file's declaration-record
        -- index is NOT a fixed offset from it: the prepared list
        -- starts with the prelude's records and drops the stream's
        -- identical copies of them (see above).  The declaration NAME
        -- is the portable handle.
        let loc := if h : i < decls.size then
            s!" [at {declCName decls[i]}, fold position {i}]"
          else s!" [at fold position {i}]"
        let now ← clockMs
        diagLine s!"con-leche: {e}{loc} ({modeTag}) \
          t={ConLeche.Cached.msSecs (now - t0)}s"
        return e.exitCode

/-- **An accepted stream run, in the model** (tasks #424, #450): every
outcome of the driver's run on a lean4export stream `file` over a
snapshot `fs` that is an exit 0 means the built-in prelude parses, the
file has bytes `b` in the snapshot, they parse as one chunk to records
`r`, and `checkDecls` accepts those prepared with the prelude — the
hypothesis of the main corollary (`ConLeche.no_False_declaration`, at
the chunks `[b]`) about the file's own bytes, at any `--jobs`, whatever
the `liftIO` actions answered.  Under the assumptions of
`ConLeche/Frontend/CheckerIO.lean` the binary's run is one of these
outcomes. -/
theorem checkMainG_ndjson_accept {file : String} {mode : CheckMode}
    {stride jobs : Nat} {fs : FS}
    (h : (checkMainG (.ndjson file) mode stride jobs : ModelIO _) fs (.ok 0)) :
    ∃ pre b r env, Frontend.builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      Frontend.parseChunks [b] = .ok r ∧
      Cached.checkDecls mode natOpPinSets (Frontend.preparePrelude pre r.decls) = .ok env := by
  -- every value outcome `c` of the run: `c = 0` gives the chain
  suffices H : ModelIO.AllOk (checkMainG (.ndjson file) mode stride jobs) fs
      (fun c => c = 0 → ∃ pre b r env, Frontend.builtinPreludeE = .ok pre ∧
        fs.file file = some b ∧ Frontend.parseChunks [b] = .ok r ∧
        Cached.checkDecls mode natOpPinSets (Frontend.preparePrelude pre r.decls) = .ok env) from
    H 0 h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [checkMainG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [checkMainG, hp, readInputG, clockMs, diagLine, outLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_const]
    intro _ pre' hpre x hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    cases hpre
    simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    rcases x with ⟨_ | _ | _, _⟩ | r
    rotate_right
    · obtain ⟨b, hb, hpc⟩ := parseStreamG_model hx
      simp only [Except.map]
      -- the tail after the parse: the receipts, the fold through
      -- `liftIO`, whose value carries its proof, and the verdict
      refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const] <;>
        intro _ <;>
        refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const] <;>
        intro v <;>
        rcases v with ⟨e, _⟩ | ⟨env, henv⟩ <;>
        simp only [ModelIO.allOk_bind, ModelIO.allOk_pure, ModelIO.liftIO_iff, forall_const]
      -- a rejection's exit code is not 0; an accept carries its proof
      all_goals first
        | exact fun h0 => absurd h0 (CheckError.exitCode_ne_zero _)
        | exact ⟨pre, b, r, env, rfl, hb, hpc, henv⟩
    all_goals simp [Except.map]

/-- **An accepted `--olean` run, in the model**: every outcome of the
driver's run on the import closure of `roots` over a snapshot `fs` that is
an exit 0 means the built-in prelude parses, the reader has an outcome on
that snapshot that is records `ds` (at one job: the parallel map's model is
the sequential map), and `checkDecls` accepts those prepared with the
prelude, whatever the `liftIO` actions answered. -/
theorem checkMainG_oleans_accept {sp : List System.FilePath} {roots : Array ConLeche.Name}
    {cs : Option (Array ConLeche.Name)} {mode : CheckMode} {stride jobs : Nat} {fs : FS}
    (h : (checkMainG (.oleans sp roots cs) mode stride jobs : ModelIO _) fs (.ok 0)) :
    ∃ pre ds env, Frontend.builtinPreludeE = .ok pre ∧
      (Frontend.Olean.readOleans sp roots cs : ModelIO _) fs (.ok (.ok ds)) ∧
      Cached.checkDecls mode natOpPinSets (Frontend.preparePrelude pre ds) = .ok env := by
  suffices H : ModelIO.AllOk (checkMainG (.oleans sp roots cs) mode stride jobs) fs
      (fun c => c = 0 → ∃ pre ds env, Frontend.builtinPreludeE = .ok pre ∧
        (Frontend.Olean.readOleans sp roots cs : ModelIO _) fs (.ok (.ok ds)) ∧
        Cached.checkDecls mode natOpPinSets (Frontend.preparePrelude pre ds) = .ok env) from
    H 0 h rfl
  cases hp : Frontend.builtinPreludeE with
  | error x =>
    rcases x with ⟨_ | _ | _, _⟩ <;>
      simp [checkMainG, hp, clockMs, diagLine]
  | ok pre =>
    simp only [checkMainG, hp, readInputG, clockMs, diagLine, outLine, ModelIO.allOk_bind,
      ModelIO.liftIO_iff, forall_const]
    intro _ pre' hpre x hx
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hpre
    cases hpre
    rcases x with ⟨_ | _ | _, _⟩ | ds
    rotate_right
    · have hx' : (Frontend.Olean.readOleans sp roots cs : ModelIO _) fs (.ok (.ok ds)) := hx
      refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const] <;>
        intro _ <;>
        refine ModelIO.allOk_ite (fun _ => ?_) (fun _ => ?_) <;>
        simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const] <;>
        intro v <;>
        rcases v with ⟨e, _⟩ | ⟨env, henv⟩ <;>
        simp only [ModelIO.allOk_bind, ModelIO.allOk_pure, ModelIO.liftIO_iff, forall_const]
      all_goals first
        | exact fun h0 => absurd h0 (CheckError.exitCode_ne_zero _)
        | exact ⟨pre, ds, env, rfl, hx', henv⟩
    all_goals simp

end ConLeche.Driver
