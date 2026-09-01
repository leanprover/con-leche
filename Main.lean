import Setlec.Kernel.CheckerS
import Setlec.Kernel.CheckerNC
import Setlec.Cached.Driver
import Setlec.Kernel.Split
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

/-- Measurement-only (task #64, `SETLEC_STATS`): count the arena
nodes reachable from the interned environment's recorded type/value
indices — the parse-plus-stored floor of the tier decomposition.
Iterative DFS over `ENode.children`; runs once, at the end of a
progress-mode run. -/
partial def ienvReachStats (s : Setlec.IState) (n0 : Nat) : String :=
  Id.run do
    let st := s.store
    let n := st.nodes.size
    let mut seen : Array Bool := Array.replicate n false
    let mut stack : Array Setlec.EIdx := #[]
    for (_, ent) in s.ienv do
      stack := stack.push ent.ty
      if let some (_, vi) := ent.val then
        stack := stack.push vi
    let mut reach := 0
    let mut above := 0
    -- task #64 low-bit: indices are encoded; walk in decoded positions
    -- (end-of-run content is tier-one).
    let p0 := Setlec.epos n0
    while stack.size > 0 do
      let p := Setlec.epos stack.back!
      stack := stack.pop
      if p < n && !(seen.getD p true) then
        seen := seen.set! p true
        reach := reach + 1
        if p0 ≤ p then
          above := above + 1
        if let some nd := st.nodes[p]? then
          for c in nd.children do
            stack := stack.push c
    return s!"REACH: n0={p0} nodes={n} ienvReach={reach} storedAboveParse={above}"

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
        IO.eprintln s!"STATS: nodes={s.store.nodes.size} lnodes={s.store.lnodes.size} annotC={s.annotC.size} inferC={s.inferC.size} whnfC={s.whnfC.size} whnfCoreC={s.whnfCoreC.size} defeqC={s.defeqC.size}"
      progressLoop stats stepF n0 decls (i + 1) fe s
  else do
    if stats then
      IO.eprintln (ienvReachStats s n0)
    IO.println s!"setlec: accepted {fe.env.consts.length} declarations"
    pure 0

/-- Display name of a parsed declaration record (diagnostics). -/
def declPName : Setlec.DeclP → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .basisDecl k => s!"basis block {repr k}"

/-- Diagnostic second-pass loop (locates the failing declaration for
the error message), as explicit recursion with the accumulators passed
as plain arguments — exactly like `progressLoop` above, and for the
same reason: a `for`-loop's boxed state tuple keeps the re-parsed
arena shared (RC 2) into every step call, so each declaration's first
arena mutation copies the whole node/hash tables.  On a multi-gigabyte
arena that one-copy-per-declaration strike made error runs ~20×
slower than the (linear) verified first pass. -/
partial def diagLoop
    (stepF : Nat → Setlec.FEnv → Setlec.DeclP → Setlec.IState →
      Except Setlec.CheckError (Setlec.FEnv × Setlec.IState))
    (n2 : Nat) (decls : Array Setlec.DeclP) (i : Nat)
    (fe : Setlec.FEnv) (s : Setlec.IState) : String :=
  if h : i < decls.size then
    let d := decls[i]
    match stepF n2 fe d s with
    | .ok (fe, s) => diagLoop stepF n2 decls (i + 1) fe s
    | .error _ => s!" [at {declPName d}]"
  else ""

/-- Install-phase loop of the split driver (task #108).  Explicit
recursion with plain accumulators, exactly as `progressLoop` and for the
same reason.  `bounds[i]` is the number of constants installed *before*
declaration `i` — the visibility bound its check phase runs under. -/
partial def installLoop (mode : Setlec.CheckMode) (progress : Bool) (n0 : Nat)
    (decls : Array Setlec.DeclP) (i : Nat) (fe : Setlec.FEnv)
    (bounds : Array Nat) (s : Setlec.IState) :
    IO (Except Setlec.CheckError
      (Setlec.FEnv × Array Nat × Setlec.IState)) := do
  if h : i < decls.size then
    let d := decls[i]
    if progress then
      IO.println s!"INSTALL {i}: {declPName d}"
      (← IO.getStdout).flush
    let bounds := bounds.push fe.visibleBelow
    match Setlec.installDeclSPStep mode n0 fe d s with
    | .error e =>
      IO.eprintln s!"setlec: {e} [installing {declPName d}]"
      pure (.error e)
    | .ok (fe, s) => installLoop mode progress n0 decls (i + 1) fe bounds s
  else pure (.ok (fe, bounds, s))

/-- Check-phase loop of the split driver: declarations `[i, hi)` of the
stream, each against the *final* environment restricted to its own
install-time prefix. -/
partial def recheckLoop (mode : Setlec.CheckMode)
    (progress : Bool) (decls : Array Setlec.DeclP)
    (bounds : Array Nat) (i hi : Nat) (fe : Setlec.FEnv)
    (s : Setlec.IState) : IO (Except Setlec.CheckError Unit) := do
  if h : i < hi ∧ i < decls.size then
    let d := decls[i]'h.2
    if progress then
      IO.println s!"CHECK {i}: {declPName d}"
      (← IO.getStdout).flush
    match Setlec.recheckDeclSPStep mode fe (bounds[i]?.getD 0) d s with
    | .error e =>
      IO.eprintln s!"setlec: {e} [checking {declPName d}]"
      pure (.error e)
    | .ok (_, s) => recheckLoop mode progress decls bounds (i + 1) hi fe s
  else pure (.ok ())

/-- The real driver (run in the supervised child process).  `mode` is
the three-mode setting (task #147), validated once by the caller and
consumed here as configuration; `pre` asserts the input is already
preprocessed (`--pre`), skipping preprocessor detection and spawn;
`split?` selects the unverified install/check-split driver
(`--install-only` / `--check-range`, task #108) with the requested
half-open check range. -/
def checkMain (file : String) (mode : CheckMode) (pre : Bool)
    (split? : Option (Nat × Option Nat))
    (core : Setlec.Cached.CoreVariant := .production) : IO UInt32 := do
    -- The retired environment variables (tasks #76/#134) are hard
    -- errors, not silently ignored: a verdict's provenance must be
    -- readable off the invocation (task #147).
    if (← IO.getEnv "SETLEC_NO_PROOF_CERTS") == some "1" then
      IO.eprintln "setlec: SETLEC_NO_PROOF_CERTS is retired; the \
        cert-skipping measurement lane is the --no-model mode \
        (checking-mode front door included — see DESIGN.md, task #147)"
      return 3
    if (← IO.getEnv "SETLEC_INFER_ONLY") == some "1" then
      IO.eprintln "setlec: SETLEC_INFER_ONLY is retired; the infer-only \
        internal discipline is part of the --no-model mode, and the \
        certified mode is --set-model, the default \
        (see DESIGN.md, task #147)"
      return 3
    if mode == .noModel && split?.isSome then
      -- never silently ignored: the split driver is a different
      -- unverified stack, and combining the two would make the
      -- verdict's provenance unreadable
      IO.eprintln "setlec: --no-model cannot be combined with \
        --install-only/--check-range"
      return 3
    -- Task #64: the per-declaration tier-two snapshot bracket IS the
    -- default value pipeline (checkDeclsSP); the former
    -- SETLEC_TIER_BRACKET measurement knob is retired — its modes and
    -- their measurements are recorded in DESIGN.md (reproducible at
    -- the pre-flip commit 2794be4).
    -- Task #147: `--set-model` runs the certified drivers
    -- (`--tt-model` was retired with the declarative lane at #148
    -- T7b); `--no-model` runs the unverified lane
    -- (Setlec/Kernel/CheckerNC.lean — checking-mode front door over
    -- the cert-skipping internals).
    -- The performance pilot's core selector (`--core=…`): the two
    -- non-production variants run the *same* `Expr`-typed shared-state
    -- declaration driver, one over the interned core and one over the
    -- cached-clone core, so a comparison between them isolates the
    -- representation.  They are measurement instruments: unverified,
    -- and refused in combination with the split driver.
    if core != .production && split?.isSome then
      IO.eprintln "setlec: --core=… cannot be combined with \
        --install-only/--check-range"
      return 3
    let stepF :=
      if mode == .noModel then checkDeclSPStepNM else checkDeclSPStep mode
    let foldF :=
      match core with
      | .cached => Setlec.Cached.checkDeclsSharedC mode
      | .internedShared => Setlec.Cached.checkDeclsSharedI mode
      | .production =>
        if mode == CheckMode.noModel then checkDeclsSPNM else checkDeclsSP mode
    -- Streaming frontend (task #57): the preprocessor writes to a temp
    -- file and the parse reads line by line — no wholesale text buffer
    -- in this process; retained memory is the parse arena plus the
    -- declaration records.  `--pre` (an explicit user assertion, never
    -- content sniffing) skips detection and the preprocessor spawn.
    let (path, isTemp) ← if pre then pure (file, false) else preprocess file
    try
      match ← Frontend.parseExportStream path (modeled := true) with
      | .error (.unsupported what) =>
        IO.eprintln s!"setlec: declined: {what}"
        return 2
      | .error (.parseError line msg) =>
        IO.eprintln s!"setlec: {file}:{line}: {msg}"
        return 3
      | .ok ⟨store, decls, taintSkipped⟩ =>
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
        -- Progress instrumentation for long runs (init-prelude probes):
        -- with SETLEC_PROGRESS set, check declaration by declaration and
        -- print a `DECL:` line before each (fold and interned state
        -- threaded exactly as in checkDeclsSP).
        -- task #64 low-bit: the in-range bound is the encoded index bound
        let n0 := store.raw.nodes.size + store.raw.nodes.size
        -- Task #108: the unverified install/check-split driver.  A run
        -- that checks a subrange (or nothing at all) never accepts —
        -- exit 0 means "every declaration in this stream was checked".
        if let some (lo, hi?) := split? then
          let progress := (← IO.getEnv "SETLEC_PROGRESS").isSome
          let hi := min (hi?.getD decls.size) decls.size
          -- A run that skipped checks cannot make a *positive* claim
          -- about the stream in either direction: a skipped check might
          -- have declined (the checker's honest verdict) before the
          -- failure this run reports.  So a partial run downgrades
          -- `invalid` to a decline; the message still names the
          -- offending declaration, which is the point of the mode.
          let full := lo == 0 && hi == decls.size
          let verdict : Setlec.CheckError → UInt32 := fun e =>
            match e with
            | .invalid _ => if full then 1 else 2
            | _ => e.exitCode
          match ← installLoop mode progress n0 decls 0
              (Setlec.mkFEnv Setlec.Env.empty) #[] { store := store.raw } with
          | .error e => return ← finish (verdict e)
          | .ok (fe, bounds, s) =>
            match ← recheckLoop mode progress decls bounds lo hi fe s with
            | .error e => return ← finish (verdict e)
            | .ok () =>
              IO.println s!"setlec: installed {fe.env.consts.length} constants \
                from {decls.size} declarations"
              IO.println s!"setlec: checked declarations [{lo}, {hi})"
              IO.eprintln s!"setlec: declined: partial check \
                ({hi - min lo hi} of {decls.size} declarations checked)"
              return 2
        if (← IO.getEnv "SETLEC_PROGRESS").isSome ∧ core == .production then
          -- the parse arena is well-formed by construction (task #103);
          -- no validation sweep before checking
          let stats := (← IO.getEnv "SETLEC_STATS").isSome
          return ← finish (← progressLoop stats stepF n0 decls 0
            (Setlec.mkFEnv Setlec.Env.empty) { store := store.raw })
        match foldF store decls.toList with
        | .ok env =>
          IO.println s!"setlec: accepted {env.consts.length} declarations"
          return ← finish 0
        | .error e =>
          -- Diagnostic second pass: the verdict above is the verified
          -- run; this only locates the failing declaration for the
          -- message.  The input is re-parsed (from the file, streaming):
          -- the verified run must own the parse store exclusively (a
          -- live second reference would turn every arena push into a
          -- whole-table copy), so the original store was moved into it.
          -- The walk itself is `diagLoop` — explicit recursion, so the
          -- re-parsed store is owned exclusively too.
          let ctx := match ← Frontend.parseExportStream path (modeled := true) with
            | .error _ => ""
            | .ok ⟨store2, decls2, _⟩ =>
              -- The in-range bound is the *encoded* index bound
              -- (task #64 low-bit), exactly as in the verified run
              -- above: passing the raw node count instead made
              -- `checkDeclSPStep` reject the first declaration whose
              -- encoded indices exceed it with "parsed declaration
              -- index out of range", so the second pass reported a
              -- declaration that never failed in the real run
              -- (task #106).
              diagLoop stepF (store2.raw.nodes.size + store2.raw.nodes.size)
                decls2 0
                (Setlec.mkFEnv Setlec.Env.empty) { store := store2.raw }
          IO.eprintln s!"setlec: {e}{ctx}"
          return ← finish e.exitCode
    finally
      if isTemp then
        try IO.FS.removeFile path catch _ => pure ()

def usage : String := String.intercalate "\n" [
  "usage: setlec [--set-model|--no-model] [--pre]",
  "              [--install-only] [--check-range A:B] FILE.ndjson",
  "",
  "  --set-model       the default: the verified checker, the surface",
  "                    the set-theoretic consistency proofs are about.",
  "                    The seven TT-lane checks (tasks #126/#129/#130/",
  "                    #135/#136/#137/#146) are off; every always-on",
  "                    certificate family runs",
  "  --no-model        the unverified lane: full checking-mode front",
  "                    door per declaration (official-kernel parity),",
  "                    infer-only internal re-derivations, and no",
  "                    certificate families at all.  Replaces the",
  "                    retired --yolo/SETLEC_NO_PROOF_CERTS and",
  "                    --infer-only/SETLEC_INFER_ONLY",
  "  --pre             assert FILE is already preprocessed output of",
  "                    lean-inductive-models: skip the preprocessor",
  "                    detection scan and spawn entirely",
  "  --core=V          performance pilot (unverified measurement",
  "                    instrument): V = production (default),",
  "                    interned-shared, or cached — see DESIGN.md,",
  "                    \"The cached-clone pilot\"",
  "  --install-only    install the whole stream without checking any",
  "                    declaration (task #108)",
  "  --check-range A:B check only declarations [A, B) of the stream,",
  "                    after installing all of it; `A:` runs to the end",
  "",
  "--install-only and --check-range select the unverified split",
  "install/check driver; since less than the whole stream is checked,",
  "a successful run reports a decline (exit 2), never an acceptance."]

/-- `A:B`, `A:` or `:B` — a half-open declaration-index range. -/
def parseRangeSpec (s : String) : Option (Nat × Option Nat) :=
  match s.splitOn ":" with
  | [a, b] =>
    match (if a.isEmpty then some 0 else a.toNat?) with
    | none => none
    | some lo =>
      if b.isEmpty then some (lo, none)
      else match b.toNat? with
        | none => none
        | some hi => some (lo, some hi)
  | _ => none

structure Args where
  mode : Setlec.CheckMode := .setModel
  /-- performance-pilot core selector (`--core=…`) -/
  core : Setlec.Cached.CoreVariant := .production
  pre : Bool := false
  /-- the split driver's check range (`some (0, some 0)` for
  `--install-only`) -/
  split? : Option (Nat × Option Nat) := none
  files : Array String := #[]
  bad : Option String := none

def parseArgs : List String → Args → Args
  | [], a => a
  | "--set-model" :: rest, a => parseArgs rest { a with mode := .setModel }
  | "--tt-model" :: _, a =>
    { a with bad := some "--tt-model is retired; the declarative \
        verification lane it selected was deleted with the mode, and \
        the certified mode is --set-model (default) (task #148 T7b)" }
  | "--no-model" :: rest, a => parseArgs rest { a with mode := .noModel }
  | "--yolo" :: _, a =>
    { a with bad := some "--yolo is retired; the cert-skipping lane is \
        --no-model (checking-mode front door included, task #147)" }
  | "--infer-only" :: _, a =>
    { a with bad := some "--infer-only is retired; its discipline is part \
        of --no-model, and the certified mode is --set-model \
        (default) (task #147)" }
  | "--pre" :: rest, a => parseArgs rest { a with pre := true }
  | "--core" :: spec :: rest, a =>
    match spec with
    | "production" => parseArgs rest { a with core := .production }
    | "interned-shared" => parseArgs rest { a with core := .internedShared }
    | "cached" => parseArgs rest { a with core := .cached }
    | _ => { a with bad := some s!"unknown core variant {spec}" }
  | "--install-only" :: rest, a =>
    parseArgs rest { a with split? := some (0, some 0) }
  | "--check-range" :: spec :: rest, a =>
    match parseRangeSpec spec with
    | some r => parseArgs rest { a with split? := some r }
    | none => { a with bad := some s!"malformed --check-range {spec}" }
  | s :: rest, a =>
    if s.startsWith "--core=" then
      match (s.drop "--core=".length).toString with
      | "production" => parseArgs rest { a with core := .production }
      | "interned-shared" => parseArgs rest { a with core := .internedShared }
      | "cached" => parseArgs rest { a with core := .cached }
      | v => { a with bad := some s!"unknown core variant {v}" }
    else if s.startsWith "--check-range=" then
      match parseRangeSpec ((s.drop "--check-range=".length).toString) with
      | some r => parseArgs rest { a with split? := some r }
      | none => { a with bad := some s!"malformed {s}" }
    else if s.startsWith "-" then
      { a with bad := some s!"unknown option {s}" }
    else parseArgs rest { a with files := a.files.push s }

/-- The child's argument vector, reassembled from the parsed options. -/
def childArgs (a : Args) (file : String) : Array String :=
  #[file]
    ++ (match a.mode with
        | .setModel => #[]
        | .noModel => #["--no-model"])
    ++ (if a.pre then #["--pre"] else #[])
    ++ (match a.core with
        | .production => #[]
        | .internedShared => #["--core=interned-shared"]
        | .cached => #["--core=cached"])
    ++ (match a.split? with
        | some (0, some 0) => #["--install-only"]
        | some (lo, some hi) => #["--check-range", s!"{lo}:{hi}"]
        | some (lo, none) => #["--check-range", s!"{lo}:"]
        | none => #[])

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println usage
    return 0
  -- `--set-model`/`--no-model`: the mode setting (task #147; two
  -- modes since #148 T7b), validated here once and threaded as
  -- configuration.
  -- `--pre`: the input is already-preprocessed lean-inductive-models
  -- output (explicit user assertion — the checker never sniffs input
  -- content for it); skips the `needsPreprocess` scan and the
  -- preprocessor spawn.
  -- `--install-only` / `--check-range`: the split driver (task #108).
  let a := parseArgs args {}
  if let some msg := a.bad then
    IO.eprintln s!"setlec: {msg}"
    IO.eprintln usage
    return 3
  let pre := a.pre
  -- (the refusal of `--no-model` with the split driver lives in
  -- `checkMain`, which is where the retired environment variables are
  -- rejected too)
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
      checkMain file a.mode pre a.split? a.core
    else
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := childArgs a file
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
    IO.eprintln usage
    return 3
