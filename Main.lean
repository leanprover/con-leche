import Setlec.Cached.ParsedC
import Setlec.Frontend.ExportC

/-!
Command-line driver: `setlec FILE.ndjson` reads a lean4export NDJSON file
(the `setlec-preprocess` front end for lean-inductive-models is run
transparently first, unless `--pre` says the input is already
preprocessed) and checks the declarations in order.

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

/-- Locate the preprocessor (task #178: `setlec-preprocess`, the checker's own
front end for `lean-inductive-models` — the tool's `main` passed setlec's
`NativeSupport`, so the blocks `directParts?` installs directly come back
unmodelled; `SetlecPreprocess.lean`).  Search order:

1. `$SETLEC_INDUCTIVE_MODELS` — the explicit override, unchanged; the test
   harnesses point it at a nonexistent path to run a stream *raw*.
2. this build's `setlec-preprocess`;
3. the stock `lean-inductive-models` development checkout under `_tmp/` — the
   legacy fallback, which costs one `pathExists` and keeps a tree without a
   built `setlec-preprocess` working (its output is a superset: every block
   left native here is modelled there, and the direct install ignores the
   model either way);
4. `setlec-preprocess` on `$PATH`, resolved at spawn time. -/
def findPreprocessor : IO (Option String) := do
  if let some p ← IO.getEnv "SETLEC_INDUCTIVE_MODELS" then
    return some p
  let dev := ".lake/build/bin/setlec-preprocess"
  if ← System.FilePath.pathExists dev then
    return some dev
  let legacy := "_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models"
  if ← System.FilePath.pathExists legacy then
    return some legacy
  -- fall back to PATH resolution by just trying the bare name at spawn time
  return some "setlec-preprocess"

/-- Does the input contain records the preprocessor must reduce
(`inductive`/`quot`)?  Streaming scan, line by line — the keys cannot
span a line boundary (ndjson, no newlines inside a record). -/
partial def needsPreprocess (file : String) : IO Bool := do
  let h ← IO.FS.Handle.mk file .read
  let rec loop : IO Bool := do
    let line ← h.getLine
    if line.isEmpty then
      return false
    if line.contains "\"inductive\"" || line.contains "\"quot\"" then
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

/-- `declPName` for the direct-parse `DeclC` records (task #171).  The
formatting itself lives beside the checker (`Setlec.Cached.declCLabel`)
because the progress heartbeat's compiled hook prints it too, and the
two must never drift apart. -/
def declCName : Setlec.Cached.DeclC → String := Setlec.Cached.declCLabel

/-- The progress heartbeat's stride (`SETLEC_PROGRESS=<stride>`;
2026-09-07).  `none` — the variable unset — is off; a value that is not
a decimal numeral is a hard error, per the provenance discipline the
retired-variable arms follow (a run's output must be readable off its
invocation, never silently degraded).  `0` is the explicit "off". -/
def progressStride : IO (Except String Nat) := do
  match ← IO.getEnv "SETLEC_PROGRESS" with
  | none => return .ok 0
  | some s =>
    match s.toNat? with
    | some n => return .ok n
    | none => return .error s!"SETLEC_PROGRESS must be a declaration stride \
        (a decimal numeral; 0 or unset is off), got {repr s}"

/-- Diagnostic second-pass loop over `DeclC` (task #171; the direct
pipeline needs no re-parse — the records carry no arena, so the fold
never shared a store with them). -/
partial def diagLoopC
    (stepF : Setlec.FEnv → Setlec.Cached.DeclC → Setlec.Cached.CState →
      Except Setlec.CheckError (Setlec.FEnv × Setlec.Cached.CState))
    (decls : Array Setlec.Cached.DeclC) (i : Nat)
    (fe : Setlec.FEnv) (s : Setlec.Cached.CState) : String :=
  if h : i < decls.size then
    let d := decls[i]
    match stepF fe d s with
    | .ok (fe, s) => diagLoopC stepF decls (i + 1) fe s
    | .error _ => s!" [at {declCName d}]"
  else ""

/-- The real driver (run in the supervised child process).  `mode` is
the three-mode setting (task #147), validated once by the caller and
consumed here as configuration; `pre` asserts the input is already
preprocessed (`--pre`), skipping preprocessor detection and spawn.

**One core at two configs, one parse.**  The interned representation
and every driver over it retired with the arena (task #172), the R
core retired with the collapsed model (2026-09-05), and the
hand-written trusted twin retired into an instantiation
(2026-09-06), so the stream is parsed directly to `ExprC`
(`Frontend.parseExportStreamD`, task #171) and checked by the one
cached driver — at `cfgP` under `--verified` (the default), at `cfgT`
under `--trusted`.  The verified instance is covered by
`no_proof_of_Empty_SPCD_P` over `checkDeclsSPCachedD`
(`Setlec/Verify/Cached/MainC.lean`); the trusted one is unverified by
design and agrees with it on the install skeletons whenever both
accept (`trusted_agrees_P_skels_shipped`). -/
def checkMain (file : String) (mode : CheckMode) (pre : Bool) : IO UInt32 := do
    -- The retired environment variables (tasks #76/#134) are hard
    -- errors, not silently ignored: a verdict's provenance must be
    -- readable off the invocation (task #147).
    if (← IO.getEnv "SETLEC_NO_PROOF_CERTS") == some "1" then
      IO.eprintln "setlec: SETLEC_NO_PROOF_CERTS is retired; the \
        cert-skipping measurement lane is the --trusted mode \
        (checking-mode front door included — see DESIGN.md, task #147)"
      return 3
    if (← IO.getEnv "SETLEC_INFER_ONLY") == some "1" then
      IO.eprintln "setlec: SETLEC_INFER_ONLY is retired; the infer-only \
        internal discipline is part of the --trusted mode, and the \
        certified mode is --verified, the default \
        (see DESIGN.md, task #147)"
      return 3
    -- The opt-in progress heartbeat (2026-09-07): validated here, once,
    -- before any work is done.
    let stride ← match ← progressStride with
      | .error msg => IO.eprintln s!"setlec: {msg}"; return 3
      | .ok n => pure n
    let t0 ← IO.monoMsNow
    -- Streaming frontend (task #57): the preprocessor writes to a temp
    -- file and the parse reads line by line — no wholesale text buffer
    -- in this process.  `--pre` (an explicit user assertion, never
    -- content sniffing) skips detection and the preprocessor spawn.
    let (path, isTemp) ← if pre then pure (file, false) else preprocess file
    try
      match ← Frontend.parseExportStreamD path (modeled := true) with
      | .error (.unsupported what) =>
        IO.eprintln s!"setlec: declined: {what}"
        return 2
      | .error (.parseError line msg) =>
        IO.eprintln s!"setlec: {file}:{line}: {msg}"
        return 3
      | .ok ⟨decls, taintSkipped, projRewrites⟩ =>
        -- the projection-function rewrite's receipt (2026-09-06,
        -- `Setlec/Frontend/ProjRec.lean`): how many non-direct
        -- structure-like projection functions the parse replaced by
        -- recursor applications
        if projRewrites.size > 0 then
          IO.eprintln s!"setlec: {projRewrites.size} projection functions of \
            non-direct structure-likes rewritten to recursor form"
          if (← IO.getEnv "SETLEC_PROJREC_TRACE").isSome then
            for n in projRewrites do
              IO.eprintln s!"setlec:   rewritten {n}"
        -- Taint-skip verdict (user directive 2026-08-24): declarations
        -- using tolerated axioms were *skipped* during parsing (they
        -- are absent from `decls`, so nothing tainted can be checked
        -- or installed) and the rest of the stream was checked; a
        -- clean run over a stream with skips is still a decline —
        -- uses of tolerated axioms are never accepted.
        let finish : UInt32 → IO UInt32 := fun code => do
          if taintSkipped.isEmpty then return code
          IO.eprintln s!"setlec: declined: {Frontend.taintSummary taintSkipped}"
          return (if code = 0 then 2 else code)
        -- ONE driver, two configs (2026-09-06): the trusted mode is
        -- the shared bodies at `cfgT`, the verified mode the same
        -- bodies at `cfgP` (`cfgOf .verified`, `rfl`).
        let cfg : Setlec.CoreCfg :=
          if mode == Setlec.CheckMode.trusted then Setlec.cfgT else Setlec.cfgP
        -- The progress heartbeat (`SETLEC_PROGRESS=<stride>`,
        -- 2026-09-07).  The fold below is the verified one, unchanged
        -- and unforked: the per-declaration lines come from the
        -- identity hook inside `checkDeclSPStepC`
        -- (`Setlec.Cached.progressTick` — its definition is `x`; the
        -- printing is its `@[implemented_by]` companion).  All the
        -- driver does is hand it the stride and `N` and bracket the
        -- fold with the two lines it cannot produce itself.
        --
        -- **Reading the index**: `i` is the *fold* position, which the
        -- stream's declaration-record index sits a constant **+4**
        -- above — the parse folds the pinned basis blocks into one
        -- `basisDecl` record (the same offset the `SETLEC_TRACE_DECLS`
        -- lane documents, checked there at fold positions 1 000 /
        -- 50 000 / 100 000 / 150 000 of the full Mathlib stream).
        let tParse ← IO.monoMsNow
        if stride > 0 then
          Setlec.Cached.progressC.set
            { stride := stride, total := decls.size, idx := 0, startMs := t0 }
          IO.eprintln s!"setlec: progress parse done: {decls.size} \
            declarations t={Setlec.Cached.msSecs (tParse - t0)}s \
            (preprocess and parse)"
          (← IO.getStderr).flush
        -- The closing line, and the hook's disarm: the counter says how
        -- far the fold got (`= N` on an accept, the failing position
        -- otherwise), and the stride goes back to 0 so the diagnostic
        -- second pass below — which runs the same step — is not counted
        -- or printed a second time.
        let progressDone : IO Unit := do
          if stride > 0 then
            let st ← Setlec.Cached.progressC.get
            Setlec.Cached.progressC.set { st with stride := 0 }
            let now ← IO.monoMsNow
            IO.eprintln s!"setlec: progress fold done: {st.idx}/\
              {decls.size} t={Setlec.Cached.msSecs (now - t0)}s \
              (fold {Setlec.Cached.msSecs (now - tParse)}s)"
            (← IO.getStderr).flush
        match Setlec.Cached.checkDeclsSPCachedD cfg decls.toList with
        | .ok env =>
          progressDone
          IO.println s!"setlec: accepted {env.consts.length} declarations"
          return ← finish 0
        | .error e =>
          progressDone
          -- Diagnostic second pass: the verdict above is the verified
          -- run; this only locates the failing declaration for the
          -- message.  No re-parse is needed — the records carry no
          -- arena, so the fold never shared a store with them.
          let stepD := fun fe d s =>
            (Setlec.Cached.checkDeclSPStepC cfg fe d).run s
          let ctx := diagLoopC stepD decls 0
            (Setlec.mkFEnv Setlec.Env.empty) {}
          IO.eprintln s!"setlec: {e}{ctx}"
          return ← finish e.exitCode
    finally
      if isTemp then
        try IO.FS.removeFile path catch _ => pure ()


def usage : String := String.intercalate "\n" [
  "usage: setlec [--verified|--trusted] [--pre] FILE.ndjson",
  "",
  "  --verified        the default: the verified mode (graded model,",
  "                    annotation-gated checks).  The validated-",
  "                    annotation beta gate skips per-redex argument",
  "                    certificates at provably non-Prop binders, and",
  "                    the io-graded knot skips the per-argument",
  "                    application certificate under the same licence.",
  "                    The seven TT-lane checks (tasks #126/#129/#130/",
  "                    #135/#136/#137/#146) are off; every other",
  "                    certificate family runs.  Covered by",
  "                    no_proof_of_Empty_SPCD_P over the driver this",
  "                    binary runs (Setlec/Verify/Cached/MainC.lean)",
  "  --trusted         the unverified mode: the SAME checker bodies as",
  "                    --verified, instantiated at the config with the",
  "                    certification-only work switched off (cfgT =",
  "                    cfgP with verified := false, certs := false):",
  "                    the annotation validations and the lambda-",
  "                    codomain sort check, and the certificate",
  "                    families the reference kernel does not run (the",
  "                    beta/io argument certificates, the iota/eta/unit/K",
  "                    telescope certificates, the projection",
  "                    certificate) are omitted; every check official",
  "                    performs stays.  Everything believed necessary",
  "                    for SOUNDNESS stays (which is",
  "                    not the same as necessary for the soundness",
  "                    proof to go through), and the mode is never",
  "                    optimized on its own: it is the real mode with",
  "                    certain steps omitted.  Replaces the retired",
  "                    --yolo/SETLEC_NO_PROOF_CERTS and",
  "                    --infer-only/SETLEC_INFER_ONLY",
  "  SETLEC_PROGRESS=<stride>",
  "                    opt-in progress heartbeat on STDERR: one",
  "                    'setlec: progress <i>/<N> <decl> t=<s>s' line",
  "                    every <stride> declarations during the",
  "                    (unchanged, verified) fold, plus one line when",
  "                    the parse finishes (N and the elapsed parse) and",
  "                    one when the fold does.  t= is the elapsed time",
  "                    since the run started, so a declaration that",
  "                    sits for minutes is visible as a gap between two",
  "                    lines.  <i> is the FOLD position; the",
  "                    stream's declaration-record index is a constant",
  "                    +4 above it (the parse folds the pinned basis",
  "                    blocks into one record).  Unset or 0 is off",
  "",
  "  --pre             assert FILE is already preprocessed output of",
  "                    setlec-preprocess (or the stock",
  "                    lean-inductive-models): skip the preprocessor",
  "                    detection scan and spawn entirely",
  "",
  "There is ONE core at two configs and one parse: the verified config",
  "(--verified, the default) and the unverified trusted config",
  "(--trusted).  The stream is read directly to the cached",
  "representation and checked by the one driver, which the capstone",
  "letter is about at the verified config (no_proof_of_Empty_SPCD_P in",
  "Setlec/Verify/Cached/MainC.lean).  Retired: --set-model/",
  "--set-model=p (now --verified) and --no-model (now --trusted),",
  "2026-09-06; the --core selector, the interned arena and the",
  "--install-only/--check-range split driver (task #172); and the R",
  "core with --set-model=r (2026-09-05, with the collapsed-model",
  "consistency proof it was the subject of)."]

structure Args where
  mode : Setlec.CheckMode := .verified
  pre : Bool := false
  files : Array String := #[]
  bad : Option String := none

def parseArgs : List String → Args → Args
  | [], a => a
  -- The verified lane is the GRADED core since the R core's retirement
  -- (2026-09-05); `no_proof_of_Empty_SPCD_P` is its letter.
  | "--verified" :: rest, a => parseArgs rest { a with mode := .verified }
  -- The retired-spelling discipline (task #172): a verdict's
  -- provenance must be readable off the invocation, so a retired
  -- spelling is a hard error naming what replaced it — never a silent
  -- alias.  The mode rename (2026-09-06) is under the same rule: the
  -- old spellings name a *vocabulary*, not a different core, but they
  -- are still errors rather than aliases.
  | "--set-model" :: _, a =>
    { a with bad := some "--set-model is retired; the verified mode is \
        --verified, still the default (mode rename 2026-09-06 — see \
        DESIGN.md, \"MODE RENAME\")" }
  | "--set-model=p" :: _, a =>
    { a with bad := some "--set-model=p is retired; the verified mode is \
        --verified, still the default (mode rename 2026-09-06 — see \
        DESIGN.md, \"MODE RENAME\")" }
  | "--no-model" :: _, a =>
    { a with bad := some "--no-model is retired; the unverified lane is \
        --trusted (mode rename 2026-09-06 — see DESIGN.md, \"MODE \
        RENAME\")" }
  | "--set-model=r" :: _, a =>
    { a with bad := some "--set-model=r is retired; the R core (all \
        certificates unconditional) and the collapsed-model consistency \
        proof it was the subject of were deleted 2026-09-05 after the \
        acceptance delta against the graded core measured ZERO. The \
        verified lane is --verified" }
  | "--tt-model" :: _, a =>
    { a with bad := some "--tt-model is retired; the declarative \
        verification lane it selected was deleted with the mode, and \
        the certified mode is --verified (default) (task #148 T7b)" }
  | "--trusted" :: rest, a => parseArgs rest { a with mode := .trusted }
  | "--yolo" :: _, a =>
    { a with bad := some "--yolo is retired; the cert-skipping lane is \
        --trusted (checking-mode front door included, task #147)" }
  | "--infer-only" :: _, a =>
    { a with bad := some "--infer-only is retired; its discipline is part \
        of --trusted, and the certified mode is --verified \
        (default) (task #147)" }
  | "--pre" :: rest, a => parseArgs rest { a with pre := true }
  -- Task #172: `--core`, `--install-only` and `--check-range` are hard
  -- errors, not silently ignored — the rule the retired mode
  -- environment variables already follow: a verdict's provenance must
  -- be readable off the invocation.
  | "--core" :: _, a =>
    { a with bad := some "--core is retired; there is one core and one \
        expression representation since task #172 (the interned arena \
        and every driver over it were deleted)" }
  | "--install-only" :: _, a =>
    { a with bad := some "--install-only is retired; the split \
        install/check driver was arena machinery and went with the \
        interned representation (task #172)" }
  | "--check-range" :: _, a =>
    { a with bad := some "--check-range is retired; the split \
        install/check driver was arena machinery and went with the \
        interned representation (task #172)" }
  | s :: rest, a =>
    if s.startsWith "--core=" then
      { a with bad := some "--core is retired; there is one core and one \
          expression representation since task #172 (the interned arena \
          and every driver over it were deleted)" }
    else if s.startsWith "--check-range=" then
      { a with bad := some "--check-range is retired; the split \
          install/check driver was arena machinery and went with the \
          interned representation (task #172)" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- The child's argument vector, reassembled from the parsed options. -/
def childArgs (a : Args) (file : String) : Array String :=
  #[file]
    -- Two modes, and `.verified` is the default, so it re-emits
    -- nothing.  (The dead R arm this replaced went with the
    -- constructor when `CheckMode` collapsed to two values.)
    ++ (match a.mode with
        | .verified => #[]
        | .trusted => #["--trusted"])
    ++ (if a.pre then #["--pre"] else #[])

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    return 0
  -- `--verified`/`--trusted`: the mode setting (task #147), validated
  -- here once and threaded as configuration.  Two cores since the R
  -- core's retirement (2026-09-05): the graded verified one and the
  -- unverified trusted one.
  -- `--pre`: the input is already-preprocessed `setlec-preprocess`
  -- output (explicit user assertion — the checker never sniffs input
  -- content for it); skips the `needsPreprocess` scan and the
  -- preprocessor spawn.
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"setlec: {msg}"
    IO.eprintln usage
    return 3
  let pre := a.pre
  match a.files.toList with
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
      checkMain file a.mode pre
    else
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := childArgs a file
        env := #[("SETLEC_SUPERVISED", some "1")]
        stdout := .inherit
        stderr := .piped }
      -- The child's stderr is STREAMED, line by line, rather than read
      -- to EOF and re-printed at the end (2026-09-07): a progress
      -- heartbeat that only appears once the run is over is not a
      -- heartbeat, and the same goes for the localisation lane's TRACE
      -- lines when the run dies without returning.  The panic marker is
      -- looked for on the way past, so the supervision below is
      -- unchanged.
      let errOut ← IO.getStderr
      let mut panicked := false
      repeat
        let line ← child.stderr.getLine
        if line.isEmpty then break
        errOut.putStr line
        errOut.flush
        if (line.splitOn "INTERNAL PANIC").length > 1 then panicked := true
      let code ← child.wait
      if code = 1 ∧ panicked then
        IO.eprintln "setlec: internal panic in the checker process"
        return 3
      return code
  | _ =>
    IO.eprintln usage
    return 3
