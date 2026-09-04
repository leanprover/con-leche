import Setlec.Kernel.CheckerS
import Setlec.Kernel.CheckerNC
import Setlec.Cached.Driver
import Setlec.Cached.ParsedNC
import Setlec.Frontend.ExportC
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

/-- `declPName` for the direct-parse `DeclC` records (task #171). -/
def declCName : Setlec.Cached.DeclC → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .basisDecl k => s!"basis block {repr k}"

/-- Diagnostic second-pass loop over `DeclC` (task #171; the direct
pipeline needs no re-parse — the records carry no arena, so the fold
never shared a store with them). -/
partial def diagLoopC
    (stepF : Setlec.FEnv → Setlec.Cached.DeclC → Setlec.Cached.CState →
      Except Setlec.CheckError (Setlec.FEnv × Setlec.Cached.CState))
    (decls : Array Setlec.Cached.WDeclC) (i : Nat)
    (fe : Setlec.FEnv) (s : Setlec.Cached.CState) : String :=
  if h : i < decls.size then
    let d := decls[i]
    match stepF fe d.1 s with
    | .ok (fe, s) => diagLoopC stepF decls (i + 1) fe s
    | .error _ => s!" [at {declCName d.1}]"
  else ""

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
    (core? : Option Setlec.Cached.CoreVariant := none) : IO UInt32 := do
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
    -- The core selector (`--core=…`, task #163).  THE DEFAULT FLIPPED
    -- (user grant, 2026-09-03): the certified mode (`--set-model`)
    -- defaults to `cached-parsed`, whose acceptance is covered by the
    -- same consistency corollaries as production's
    -- (`Setlec/Verify/Cached/MainC.lean`:
    -- `checkDeclsSPCached_sound_R` + the `no_proof_of_Empty_SPC_*`
    -- family, all three carriers).  `--core=production` remains
    -- selectable.  THE DEFAULT IS MODE-AWARE — two carve-outs (an
    -- explicit `--core=` always wins):
    -- * `--no-model` keeps the production front door (`CheckerNC`,
    --   task #147), for two reasons: the cert-skipping lane was never
    --   cloned (its recorded expectations are relative to that front
    --   door), and MEASURED shape-dependence — on identical
    --   preprocessed input at --no-model the interned core wins
    --   decl-heavy streams (init-prelude 4.1x vs 7.0x official,
    --   init-full 4.0x vs 6.9x, grind 4.5x vs 6.2x) while cached wins
    --   term-heavy (app-lam 7.7x vs 13.2x, beta-ladder 4.4x vs 8.0x);
    --   a global cached default would cost 1.6-1.7x on the parity
    --   lane's init runs.  (The certified mode's table is different:
    --   cert machinery dominates there and cached wins everywhere,
    --   init-full included.)
    -- * the split driver (`--install-only`/`--check-range`) is
    --   production machinery (arena `stepF`) and runs it; only an
    --   *explicit* non-production core is refused with it.
    -- `interned-shared` and `cached` remain the pilot's unverified
    -- measurement instruments.
    if core?.any (· != .production) && split?.isSome then
      IO.eprintln "setlec: --core=… cannot be combined with \
        --install-only/--check-range"
      return 3
    let core := core?.getD
      (if mode == .noModel then .production else Setlec.Cached.defaultCore)
    let stepF :=
      if mode == .noModel then checkDeclSPStepNM else checkDeclSPStep mode
    let foldF :=
      match core with
      | .cached => Setlec.Cached.checkDeclsSharedC mode
      | .cachedParsed =>
        -- The cached parity lane (cross-core comparison prerequisite):
        -- at `--no-model` the cached-parsed core runs its own
        -- cert-skipping engine (Setlec/Cached/CoreNC.lean +
        -- ParsedNC.lean — the cached twin of CheckerNC), not the
        -- certified engine with mode-gated checks off.
        if mode == CheckMode.noModel then Setlec.Cached.checkDeclsSPCachedNM
        else Setlec.Cached.checkDeclsSPCached mode
      | .internedShared => Setlec.Cached.checkDeclsSharedI mode
      | .production =>
        if mode == CheckMode.noModel then checkDeclsSPNM else checkDeclsSP mode
    -- Streaming frontend (task #57): the preprocessor writes to a temp
    -- file and the parse reads line by line — no wholesale text buffer
    -- in this process; retained memory is the parse arena plus the
    -- declaration records.  `--pre` (an explicit user assertion, never
    -- content sniffing) skips detection and the preprocessor spawn.
    let (path, isTemp) ← if pre then pure (file, false) else preprocess file
    -- Task #171: the cached-parsed core parses DIRECTLY to `ExprC`
    -- (user order: no arena, no conversion detour).  The split driver
    -- (an arena-level diagnostic instrument) keeps the arena parse.
    if core == .cachedParsed ∧ split?.isNone ∧
        !(← IO.getEnv "SETLEC_PROGRESS").isSome then
      try
        match ← Frontend.parseExportStreamD path (modeled := true) with
        | .error (.unsupported what) =>
          IO.eprintln s!"setlec: declined: {what}"
          return 2
        | .error (.parseError line msg) =>
          IO.eprintln s!"setlec: {file}:{line}: {msg}"
          return 3
        | .ok ⟨decls, taintSkipped⟩ =>
          let finish : UInt32 → IO UInt32 := fun code => do
            if taintSkipped.isEmpty then return code
            IO.eprintln s!"setlec: declined: {Frontend.taintSummary taintSkipped}"
            return (if code = 0 then 2 else code)
          let foldD : List Setlec.Cached.WDeclC → Setlec.CheckM Setlec.Env :=
            if mode == Setlec.CheckMode.noModel then
              Setlec.Cached.checkDeclsSPCachedDNM
            else Setlec.Cached.checkDeclsSPCachedD mode
          match foldD decls.toList with
          | .ok env =>
            IO.println s!"setlec: accepted {env.consts.length} declarations"
            return ← finish 0
          | .error e =>
            let stepD := fun fe d s =>
              if mode == Setlec.CheckMode.noModel then
                (Setlec.Cached.checkDeclSPStepCNC fe d).run s
              else (Setlec.Cached.checkDeclSPStepC mode fe d).run s
            let ctx := diagLoopC stepD decls 0
              (Setlec.mkFEnv Setlec.Env.empty) {}
            IO.eprintln s!"setlec: {e}{ctx}"
            return ← finish e.exitCode
      finally
        if isTemp then
          try IO.FS.removeFile path catch _ => pure ()
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
  "usage: setlec [--set-model[=r|=p]|--no-model] [--pre]",
  "              [--install-only] [--check-range A:B] FILE.ndjson",
  "",
  "  --set-model,",
  "  --set-model=r     the default: verified (collapsed model, full",
  "                    certificates).  The surface the set-theoretic",
  "                    consistency proofs are about.  The seven",
  "                    TT-lane checks (tasks #126/#129/#130/#135/",
  "                    #136/#137/#146) are off; every always-on",
  "                    certificate family runs",
  "  --set-model=p     verified (graded model, annotation-gated",
  "                    checks): the validated-annotation beta gate",
  "                    skips per-redex argument certificates at",
  "                    provably non-Prop binders.  Covered by",
  "                    no_proof_of_Empty_P at the gated mode",
  "                    (Setlec/SetP; the coverage certificate",
  "                    betaGate_off_or_verified partitions the modes)",
  "  --no-model        the unverified lane: full checking-mode front",
  "                    door per declaration (official-kernel parity),",
  "                    infer-only internal re-derivations, and no",
  "                    certificate families at all.  Replaces the",
  "                    retired --yolo/SETLEC_NO_PROOF_CERTS and",
  "                    --infer-only/SETLEC_INFER_ONLY.  The parity",
  "                    claim is audited: DESIGN.md, \"THE CANONICAL",
  "                    VERIFICATION-TAX STATEMENT\"",
  "  --pre             assert FILE is already preprocessed output of",
  "                    lean-inductive-models: skip the preprocessor",
  "                    detection scan and spawn entirely",
  "  --core=V          core selector: V = cached-parsed (the certified",
  "                    mode's DEFAULT since the task-#163 flip: the",
  "                    verified computed-field core, covered by the",
  "                    same consistency theorems as production —",
  "                    no_proof_of_Empty_SPC_* in",
  "                    Setlec/Verify/Cached/MainC.lean) or production",
  "                    (the interned arena core; the default for",
  "                    --no-model and the split driver).  The default",
  "                    is mode-aware because the win is shape-",
  "                    dependent: term/reduction-heavy work runs",
  "                    faster on cached; declaration-heavy streams at",
  "                    --no-model run faster on production.",
  "                    interned-shared and cached remain unverified",
  "                    pilot instruments.  See DESIGN.md,",
  "                    \"Task #163 CACHED-LIVE\"",
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
  /-- core selector (`--core=…`); `none` = the mode's default
  (task #163 flip: `cached-parsed` for `--set-model`, the production
  front door for `--no-model` — resolved in `checkMain`) -/
  core : Option Setlec.Cached.CoreVariant := none
  pre : Bool := false
  /-- the split driver's check range (`some (0, some 0)` for
  `--install-only`) -/
  split? : Option (Nat × Option Nat) := none
  files : Array String := #[]
  bad : Option String := none

def parseArgs : List String → Args → Args
  | [], a => a
  | "--set-model" :: rest, a => parseArgs rest { a with mode := .setModel }
  | "--set-model=r" :: rest, a => parseArgs rest { a with mode := .setModel }
  -- Task #161: the β-certificate gate, a *mode value* on the one
  -- executable (`CheckMode.betaGate`), not a second knot.  Deliberately
  -- absent from `usage` until the gated mode's soundness theorem
  -- lands: reachable for measurement, not advertised.
  | "--set-model=p" :: rest, a => parseArgs rest { a with mode := .setModelP }
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
    | "production" => parseArgs rest { a with core := some .production }
    | "interned-shared" => parseArgs rest { a with core := some .internedShared }
    | "cached" => parseArgs rest { a with core := some .cached }
    | "cached-parsed" => parseArgs rest { a with core := some .cachedParsed }
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
      | "production" => parseArgs rest { a with core := some .production }
      | "interned-shared" => parseArgs rest { a with core := some .internedShared }
      | "cached" => parseArgs rest { a with core := some .cached }
      | "cached-parsed" => parseArgs rest { a with core := some .cachedParsed }
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
        | .setModelP => #["--set-model=p"]
        | .noModel => #["--no-model"])
    ++ (if a.pre then #["--pre"] else #[])
    ++ (match a.core with
        | none => #[]
        | some .production => #["--core=production"]
        | some .internedShared => #["--core=interned-shared"]
        | some .cached => #["--core=cached"]
        | some .cachedParsed => #["--core=cached-parsed"])
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
