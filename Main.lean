import Setlec.Kernel.CheckerS
import Setlec.Kernel.CheckerNC
import Setlec.Frontend.Export

/-!
Command-line driver: `setlec FILE.ndjson` reads a lean4export NDJSON file
(the lean-inductive-models preprocessor will eventually be run transparently
first) and checks the declarations in order.

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
* 3 — bad usage, malformed input, or an internal failure of unclear cause
-/

open Setlec

def Setlec.CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- Locate the lean-inductive-models preprocessor: `$SETLEC_INDUCTIVE_MODELS`,
then `$PATH`, then the development checkout under `_tmp/`. -/
def findPreprocessor : IO (Option String) := do
  if let some p ← IO.getEnv "SETLEC_INDUCTIVE_MODELS" then
    return some p
  let dev := "_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models"
  if ← System.FilePath.pathExists dev then
    return some dev
  -- fall back to PATH resolution by just trying the bare name at spawn time
  return some "lean-inductive-models"

/-- Does the input contain records the preprocessor must reduce
(`inductive`/`quot`)?  Streaming scan, line by line — the keys cannot
span a line boundary (ndjson, no newlines inside a record). -/
partial def needsPreprocess (file : String) : IO Bool := do
  let h ← IO.FS.Handle.mk file .read
  let rec loop : IO Bool := do
    let line ← h.getLine
    if line.isEmpty then
      return false
    if (line.splitOn "\"inductive\"").length > 1 ||
        (line.splitOn "\"quot\"").length > 1 then
      return true
    loop
  loop

/-- Run the preprocessor over the input, reducing inductives to the
modelled basis.  Returns the path to parse plus whether it is a temp
file the caller must remove: the tool writes its output *to a file*
(`-o path`), so this process never buffers input or output wholesale
(task #57; the tool's own working memory — ~650 MB on init-full — is
its own, residual until lean-inductive-models itself streams).  The
temp file lives in the system temp directory (honors `TMPDIR`; note
`/tmp` is commonly tmpfs, so point `TMPDIR` at a disk for huge
streams).  On any failure to run the tool, fall back to the raw input
(the checker then declines at the first inductive). -/
def preprocess (file : String) : IO (String × Bool) := do
  unless (← needsPreprocess file) do
    return (file, false)
  let some tool ← findPreprocessor | return (file, false)
  -- only the fresh path is needed; the dropped handle is closed by its
  -- finalizer, and the tool overwrites the (empty) file via `-o`
  let (_, tmpPath) ← IO.FS.createTempFile
  try
    let out ← IO.Process.output
      { cmd := tool, args := #["--quiet", "-o", tmpPath.toString, file] }
    if out.exitCode = 0 then
      return (tmpPath.toString, true)
    else
      IO.eprintln s!"setlec: preprocessor exited {out.exitCode}; using raw input"
      try IO.FS.removeFile tmpPath catch _ => pure ()
      return (file, false)
  catch _ =>
    try IO.FS.removeFile tmpPath catch _ => pure ()
    return (file, false)

/-- Progress-mode driver loop, as explicit recursion with the
accumulators passed as plain arguments: a `for`-loop's boxed state
tuple survives into the next step call in compiled code, so the
interned state enters every declaration shared (RC 2) and the first
arena mutation copies the whole node/hash tables (one whole-arena
copy-on-write strike per declaration, ~40 % of a probe run). -/
partial def progressLoop (stats : Bool)
    (stepF : Nat → Setlec.FEnv → Setlec.DeclP → Setlec.IState →
      Except Setlec.CheckError (Setlec.FEnv × Setlec.IState))
    (n0 : Nat) (decls : Array Setlec.DeclP) (i : Nat)
    (fe : Setlec.FEnv) (s : Setlec.IState) : IO UInt32 := do
  if h : i < decls.size then
    let d := decls[i]
    IO.println s!"DECL: {d.name}"
    (← IO.getStdout).flush
    match stepF n0 fe d s with
    | .error e =>
      IO.eprintln s!"setlec: {e}"
      pure e.exitCode
    | .ok (fe, s) => do
      if stats then
        IO.eprintln s!"STATS: nodes={s.store.nodes.size} lnodes={s.store.lnodes.size} bvarB={s.bvarB.size} annotC={s.annotC.size} inferC={s.inferC.size} whnfC={s.whnfC.size} whnfCoreC={s.whnfCoreC.size} defeqC={s.defeqC.size}"
      progressLoop stats stepF n0 decls (i + 1) fe s
  else do
    IO.println s!"setlec: accepted {fe.env.consts.length} declarations"
    pure 0

/-- The real driver (run in the supervised child process).  `yolo`
selects the unverified cert-skipping stack (same as
`SETLEC_NO_PROOF_CERTS=1`). -/
def checkMain (file : String) (yolo : Bool) : IO UInt32 := do
    -- Measurement mode (task #76): SETLEC_NO_PROOF_CERTS=1 (or the
    -- `--yolo` flag) selects the cert-skipping knot
    -- (Setlec/Kernel/CheckerNC.lean) — the proof-feeding infer/defeq
    -- calls the reference kernels do not perform are skipped.
    -- UNVERIFIED: the consistency statements cover only the default
    -- drivers below.
    let noCerts := yolo || (← IO.getEnv "SETLEC_NO_PROOF_CERTS") == some "1"
    let stepF := if noCerts then checkDeclSPStepNC else checkDeclSPStep
    let foldF := if noCerts then checkDeclsSPNC else checkDeclsSP
    -- Streaming frontend (task #57): the preprocessor writes to a temp
    -- file and the parse reads line by line — no wholesale text buffer
    -- in this process; retained memory is the parse arena plus the
    -- declaration records.
    let (path, isTemp) ← preprocess file
    try
      match ← Frontend.parseExportStream path (modeled := true) with
      | .error (.unsupported what) =>
        IO.eprintln s!"setlec: declined: {what}"
        return 2
      | .error (.parseError line msg) =>
        IO.eprintln s!"setlec: {file}:{line}: {msg}"
        return 3
      | .ok (store, decls) =>
        -- Progress instrumentation for long runs (init-prelude probes):
        -- with SETLEC_PROGRESS set, check declaration by declaration and
        -- print a `DECL:` line before each (fold and interned state
        -- threaded exactly as in checkDeclsSP).
        let n0 := store.nodes.size
        if (← IO.getEnv "SETLEC_PROGRESS").isSome then
          unless store.wfB do
            IO.eprintln "setlec: parse store not canonical"
            return 3
          let stats := (← IO.getEnv "SETLEC_STATS").isSome
          return ← progressLoop stats stepF n0 decls 0
            (Setlec.mkFEnv Setlec.Env.empty) { store := store }
        match foldF store decls.toList with
        | .ok env =>
          IO.println s!"setlec: accepted {env.consts.length} declarations"
          return 0
        | .error e =>
          -- Diagnostic second pass: the verdict above is the verified
          -- run; this only locates the failing declaration for the
          -- message.  The input is re-parsed (from the file, streaming):
          -- the verified run must own the parse store exclusively (a
          -- live second reference would turn every arena push into a
          -- whole-table copy), so the original store was moved into it.
          let declName : Setlec.DeclP → String := fun d =>
            match d with
            | .defnDecl cv _ _ => s!"def {cv.name}"
            | .thmDecl cv _ => s!"theorem {cv.name}"
            | .opaqueDecl cv _ => s!"opaque {cv.name}"
            | .axiomDecl cv => s!"axiom {cv.name}"
            | .indDecl b => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
            | .basisDecl k => s!"basis block {repr k}"
          let ctx := match ← Frontend.parseExportStream path (modeled := true) with
            | .error _ => ""
            | .ok (store2, decls2) => Id.run do
              let n2 := store2.nodes.size
              let mut fe := Setlec.mkFEnv Setlec.Env.empty
              let mut s : Setlec.IState := { store := store2 }
              for d in decls2 do
                match stepF n2 fe d s with
                | .ok (fe', s') => fe := fe'; s := s'
                | .error _ => return s!" [at {declName d}]"
              return ""
          IO.eprintln s!"setlec: {e}{ctx}"
          return e.exitCode
    finally
      if isTemp then
        try IO.FS.removeFile path catch _ => pure ()

def main (args : List String) : IO UInt32 := do
  -- `--yolo`: command-line alias for SETLEC_NO_PROOF_CERTS=1 (the
  -- unverified measurement mode, task #76).
  let yolo := args.contains "--yolo"
  let args := args.filter (· != "--yolo")
  match args with
  | [file] =>
    -- OOM supervision: the Lean runtime's out-of-memory handler
    -- (`lean_internal_panic_out_of_memory`) prints "INTERNAL PANIC:
    -- out of memory" and calls `exit(1)` — not catchable in-process
    -- and indistinguishable from a *reject* at the exit-code level.
    -- Re-exec the checker as a supervised child and translate a
    -- panicking child (exit 1 with a panic marker on stderr) into
    -- exit 3 (error), per the arena convention that 1 means "invalid
    -- input proof".  Progress output streams through (stdout is
    -- inherited); stderr is buffered for inspection and re-printed.
    if (← IO.getEnv "SETLEC_SUPERVISED").isSome then
      checkMain file yolo
    else
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := if yolo then #[file, "--yolo"] else #[file]
        env := #[("SETLEC_SUPERVISED", some "1")]
        stdout := .inherit
        stderr := .piped }
      let err ← child.stderr.readToEnd
      let code ← child.wait
      IO.eprint err
      if code = 1 ∧ (err.splitOn "INTERNAL PANIC").length > 1 then
        IO.eprintln "setlec: internal panic in the checker process"
        return 3
      return code
  | _ =>
    IO.eprintln "usage: setlec [--yolo] FILE.ndjson"
    return 3
