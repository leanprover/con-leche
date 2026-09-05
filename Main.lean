import Setlec.Cached.ParsedNC
import Setlec.Frontend.ExportC

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

/-! ## PROBE (agent/pw-bitmask): a physical census of the persisted `pw` payload

Address-keyed (`ptrAddrUnsafe`) walk of every `Expr` reachable from the
final environment, counting distinct heap objects — so shared objects
(chain-rule data, static `.ifAllZero []`, shared sub-DAGs) are counted
once, exactly as the allocator sees them.  Gated by `SETLEC_PW_CENSUS`;
measurement-only, never to land. -/
namespace PwCensus

structure Acc where
  nodes : Std.HashSet USize := {}
  metas : Std.HashSet USize := {}
  pws : Std.HashSet USize := {}
  cells : Std.HashSet USize := {}
  headNames : Std.HashSet USize := {}
  paramNames : Std.HashSet USize := {}
  canon : Std.HashSet (List Name) := {}
  binders : Nat := 0
  never : Nat := 0
  ifz : Nat := 0
  lenHist : Array Nat := Array.replicate 17 0
  cellsLogical : Nat := 0
  bytesNodes : Nat := 0

@[inline] unsafe def addr (a : α) : USize := ptrAddrUnsafe a
@[inline] unsafe def isScalar (a : α) : Bool := (ptrAddrUnsafe a) &&& 1 == 1

unsafe def levelParams (acc : Acc) : Level → Acc
  | .zero => acc
  | .succ u => levelParams acc u
  | .max a b | .imax a b => levelParams (levelParams acc a) b
  | .param n => { acc with paramNames := acc.paramNames.insert (addr n) }

unsafe def cells (acc : Acc) : List Name → Nat → Acc × Nat
  | [], k => (acc, k)
  | l@(n :: rest), k =>
    let acc := { acc with cells := acc.cells.insert (addr l),
                          headNames := acc.headNames.insert (addr n) }
    cells acc rest (k + 1)

unsafe def metaOf (acc : Acc) (m : BinderMeta) : Acc :=
  let acc := { acc with metas := acc.metas.insert (addr m), binders := acc.binders + 1 }
  if m.pw == .never then { acc with never := acc.never + 1 }
  else
    let acc := { acc with ifz := acc.ifz + 1 }
    let k := (List.range 64).foldl (fun k i => if (m.pw &&& PropWhen.bit i) != 0 then k + 1 else k) 0
    let i := min k 16
    { acc with lenHist := acc.lenHist.set! i (acc.lenHist[i]! + 1),
               cellsLogical := acc.cellsLogical + k,
               canon := acc.canon.insert [Name.num .anonymous m.pw.toNat] }

/-- Object sizes (bytes) with the four computed fields (hash scalar, two
boxed `Nat`s, one `Bool` scalar): header 8 + 8/ptr + 8 hash + 1, rounded
up to 8. -/
def nodeBytes : Expr → Nat
  | .bvar .. => 48 | .fvar .. => 64 | .sort .. => 48 | .const .. => 56
  | .app .. => 56 | .lam .. => 72 | .forallE .. => 72 | .letE .. => 72
  | .lit .. => 48 | .proj .. => 64

unsafe def walk (acc : Acc) (root : Expr) : Acc := Id.run do
  let mut acc := acc
  let mut stk : Array Expr := #[root]
  while h : stk.size > 0 do
    let e := stk[stk.size - 1]
    stk := stk.pop
    let a := addr e
    if acc.nodes.contains a then continue
    acc := { acc with nodes := acc.nodes.insert a,
                      bytesNodes := acc.bytesNodes + nodeBytes e }
    match e with
    | .bvar _ | .lit _ => pure ()
    | .fvar _ _ ty => stk := stk.push ty
    | .sort u => acc := levelParams acc u
    | .const _ us => acc := us.foldl levelParams acc
    | .app f x => stk := (stk.push f).push x
    | .lam _ ty b m | .forallE _ ty b m =>
      acc := metaOf acc m
      stk := (stk.push ty).push b
    | .letE _ ty v b => stk := ((stk.push ty).push v).push b
    | .proj _ _ x => stk := stk.push x
  return acc

unsafe def const (acc : Acc) (ci : ConstantInfo) : Acc :=
  let cv := ci.toConstantVal
  let acc := cv.levelParams.foldl (fun acc n =>
    { acc with paramNames := acc.paramNames.insert (addr n) }) acc
  let acc := walk acc cv.type
  match ci with
  | .defnInfo _ v _ | .thmInfo _ v => walk acc v
  | .recInfo _ _ _ rules => rules.foldl (fun acc r =>
      let acc := walk acc r.rhs
      match r.fire with
      | .nested lvls pins => (lvls.foldl levelParams (pins.foldl walk acc))
      | _ => acc) acc
  | _ => acc

unsafe def report (env : Env) : IO Unit := do
  let acc := env.consts.foldl const {}
  let shared := acc.headNames.fold (fun k a => if acc.paramNames.contains a then k + 1 else k) 0
  let pwBytes := 16 * acc.pws.size + 24 * acc.cells.size
  IO.eprintln s!"pw-census: consts={env.consts.length} exprDagNodes={acc.nodes.size} \
    exprBytesEst={acc.bytesNodes}"
  IO.eprintln s!"pw-census: binders(DAG)={acc.binders} never={acc.never} ifAllZero={acc.ifz} \
    cellsLogical={acc.cellsLogical}"
  IO.eprintln s!"pw-census: distinct metaObjs={acc.metas.size} (24B each = {24 * acc.metas.size}) \
    distinct ifAllZeroObjs={acc.pws.size} distinct consCells={acc.cells.size} \
    pwPayloadBytes={pwBytes}"
  IO.eprintln s!"pw-census: distinct canonical sets={acc.canon.size} \
    headNameObjs={acc.headNames.size} ofWhichSharedWithTermParams={shared}"
  IO.eprintln s!"pw-census: lenHist(0..16+)={acc.lenHist}"

@[implemented_by report] def reportSafe (_ : Env) : IO Unit := pure ()

end PwCensus

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

**One core, one parse (task #172).**  The interned representation and
every driver over it retired with the arena, so there is no core
selector left: the stream is parsed directly to `ExprC`
(`Frontend.parseExportStreamD`, task #171) and checked by the cached
driver — the certified fold at `--set-model[=r|=p]`, its parity twin
at `--no-model`.  Both are covered by the capstone letters over
`checkDeclsSPCachedD` (`Setlec/Verify/Cached/MainC.lean`:
`no_proof_of_Empty_SPCD_{R,R2,R2M}` and `no_proof_of_Empty_SPCD_P`). -/
def checkMain (file : String) (mode : CheckMode) (pre : Bool) : IO UInt32 := do
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
      | .ok ⟨decls, taintSkipped⟩ =>
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
        let foldD : List Setlec.Cached.DeclC → Setlec.CheckM Setlec.Env :=
          if mode == Setlec.CheckMode.noModel then
            Setlec.Cached.checkDeclsSPCachedDNM
          else Setlec.Cached.checkDeclsSPCachedD mode
        match foldD decls.toList with
        | .ok env =>
          IO.println s!"setlec: accepted {env.consts.length} declarations"
          if (← IO.getEnv "SETLEC_PW_CENSUS").isSome then
            PwCensus.reportSafe env
          return ← finish 0
        | .error e =>
          -- Diagnostic second pass: the verdict above is the verified
          -- run; this only locates the failing declaration for the
          -- message.  No re-parse is needed — the records carry no
          -- arena, so the fold never shared a store with them.
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


def usage : String := String.intercalate "\n" [
  "usage: setlec [--set-model[=r|=p]|--no-model] [--pre] FILE.ndjson",
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
  "                    no_proof_of_Empty_SPCD_P at the gated mode",
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
  "",
  "There is one core and one parse (task #172): the stream is read",
  "directly to the cached representation and checked by the driver the",
  "capstone letters are about (no_proof_of_Empty_SPCD_* in",
  "Setlec/Verify/Cached/MainC.lean).  The retired --core selector, the",
  "interned arena, and the --install-only/--check-range split driver",
  "went with the second representation."]

structure Args where
  mode : Setlec.CheckMode := .setModel
  pre : Bool := false
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
    ++ (match a.mode with
        | .setModel => #[]
        | .setModelP => #["--set-model=p"]
        | .noModel => #["--no-model"])
    ++ (if a.pre then #["--pre"] else #[])

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
