import Setlec.Cached.CheckerC

/-!
# The parsed-declaration driver on the cached representation

The counterpart of the retired interned `checkDeclsSP`: one `CState`
for the whole stream, the environment-dependent caches flushed per
declaration, declarations consumed as `DeclC` records straight from
the direct parse (`Setlec/Frontend/ExportC.lean`, task #171 — no
arena, no conversion detour).

`checkDeclsSPCachedD cfg` is what the binary runs in BOTH modes — at
`cfgP` under `--verified`, at `cfgT` under `--trusted` (the twin driver
`checkDeclsSPCachedDT` / `Setlec/Cached/ParsedT.lean` retired
2026-09-06; the trusted lane is this driver at the other config, and
nothing else).  Acceptance at `cfgP` is covered by
`no_proof_of_Empty_SPCD_P` (`Setlec/Verify/Cached/MainC.lean`); the two
configs agree on the install skeletons whenever both accept
(`trusted_agrees_P_skels_D`, `Setlec/Verify/Cached/AgreeFloor.lean`).

The driver's parameter is the core's `CoreCfg`, not a `CheckMode`: the
knot it ties (`coreKnotI cfg`) is config-parametric, and the two
shipped configs are not both in `cfgOf`'s image
(`cfgOf_trusted_ne_cfgT`).  The install-time stages that still take a
`CheckMode` (`checkIotaRulesF`, `checkProjIotaF`, `indBlockCapsF`,
`ctorResidualOkF` — each reads only the uninhabited-true `ttChecks`)
get `cfg.iotaMode`, a literal at each shipped config.
-/

namespace Setlec.Cached

open Setlec

/-! ## Parsed declarations over `ExprC` -/

/-- `ConstantVal` with the type as an `ExprC`. -/
structure ConstantValC where
  name : Name
  levelParams : List Name
  type : ExprC

/-- A parsed declaration over `ExprC` (the counterpart of `DeclP`). -/
inductive DeclC where
  | axiomDecl (val : ConstantValC)
  | defnDecl (val : ConstantValC) (value : ExprC) (hint : ReducibilityHint)
  | thmDecl (val : ConstantValC) (value : ExprC)
  | opaqueDecl (val : ConstantValC) (value : ExprC)
  | basisDecl (kind : BasisKind)
  | indDecl (block : List ConstantInfo)

/-! ## The parsed-declaration checker -/

variable (cfg : CoreCfg)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : ExprC) : CheckCM Level :=
  ensureSortI (coreKnotI cfg fe checkFuel) d i

/-- `checkConstantVal` on a converted declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `ExprC`
DAG and the operations on `ExprC` values. -/
def checkConstantValC (fe : FEnv) (cv : ConstantValC) :
    CheckCM (ConstantVal × ExprC) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless ExprC.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotI cfg fe checkFuel).annotate 0 cv.type
  unless ExprC.allLevelParamsDefined cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotI cfg fe checkFuel).infer 0 jty
  let _u ← opSIxC cfg fe 0 jsty
  let tyE := jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValP` over `ExprC`. -/
def checkDefnValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI cfg fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI cfg fe checkFuel).infer 0 jv
  unless ← (coreKnotI cfg fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValP` over `ExprC`. -/
def checkThmValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotI cfg fe checkFuel).infer 0 jty
  let ul ← opSIxC cfg fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI cfg fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI cfg fe checkFuel).infer 0 jv
  unless ← (coreKnotI cfg fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValP` over `ExprC`. -/
def checkOpaqueValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI cfg fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI cfg fe checkFuel).infer 0 jv
  unless ← (coreKnotI cfg fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (fe.push (.axiomInfo cvA))

/-- One converted declaration (mirrors `checkDeclSPPlain` branch by
branch; inductive and basis blocks reuse the `Expr`-level drivers). -/
def checkDeclSPC (fe : FEnv) (pd : DeclC) : CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValC cfg fe cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValC cfg fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsC cfg fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsC cfg fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValC cfg fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValC cfg fe cv
    checkThmValC cfg fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValC cfg fe cv
    let fe2 ← checkOpaqueValC cfg fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE := value
      checkReducePinF (sharedOpsC cfg fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValC cfg fe cv
    if stdAxiomOkF fe cvA then do
      recordCConst cvA.name cvA.type jty none
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure fe
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    if kind = .quotK then
      unless fe.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDeclF fe
  | .indDecl block =>
    match directPartsF? fe block with
    | some p => checkDirectStructS cfg fe p
    | none => checkIndDeclSF cfg fe block

/-! ## The progress heartbeat (`SETLEC_PROGRESS`, 2026-09-07)

A multi-hour run over a big stream used to say nothing until it
finished: the driver's fold is a **pure** `foldlM` in
`StateT CState (Except CheckError)`, so there is no point at which the
driver could interleave an `IO` print without either forking the fold
or moving the statements that are about it
(`checkDeclsSPCachedD_run`, `foldSPC_PM`, `checkDeclSPStepC_skels`,
all stated over `ds.foldlM (checkDeclSPStepC cfg)`).  The
`SETLEC_TRACE_DECLS` localisation lane pays that price by *replacing*
the fold, which is why it is structurally unable to produce a verdict.

The heartbeat here is the opposite trade: it stays **inside** the
verified fold and buys its liveness with a *definitional identity*.
`progressTick pd x` is `x` — that is its whole definition, and
`progressTick_eq` is `rfl` — so the verdict, the fold's shape and
every theorem about it are literally unchanged; the only proof-side
cost is one extra name in the two `unfold`s that open the step.  What
makes it print is an `@[implemented_by]` companion: the *compiled*
`progressTickImpl` reads the shared counter, prints one line to stderr
every `stride` declarations, and returns its argument — the same
escape hatch `dbgTrace` is (a core `@[extern]` whose model is
`fun s f => f ()`), in the same shape, and with the same obligation
on the reader: **the impl must return `x` and touch nothing else.**
It does: its only effects are a counter bump and a `putStr`/`flush`.

Consequences worth stating plainly:

* the heartbeat is not covered by the soundness proof, and cannot be —
  a `Prop` cannot see a side effect.  What the proof *does* cover is
  everything the fold computes: the printed line is the only
  difference between the model and the binary here.
* the module set of every capstone's constant closure is unchanged
  (`tests/proofdeps.sh`): `progressTick` and the counter live in this
  module, which is already pinned, and `declCLabel` — which formats a
  name — is reached only from the *impl*, never from the logical body.
* `stride = 0` (the default: the environment variable unset) makes the
  impl one relaxed `IO.Ref` read per declaration, i.e. per declaration,
  not per node.
-/

/-- The heartbeat's configuration and running position, set once by the
driver (`Main.lean`) after the parse and read by `progressTickImpl`. -/
structure ProgressC where
  /-- Print every `stride` declarations; `0` — the default — is off. -/
  stride : Nat := 0
  /-- The number of declarations the fold will see (`N`). -/
  total : Nat := 0
  /-- The fold position of the next declaration (`i`). -/
  idx : Nat := 0
  /-- `IO.monoMsNow` at the driver's start, so every line can carry the
  elapsed time: a declaration that sits for minutes shows up as a *gap*
  between two heartbeats, which is the whole point of stamping them. -/
  startMs : Nat := 0
  deriving Inhabited

/-- Milliseconds as `s.d` seconds (`12345` ↦ `"12.3"`).  `Nat`
arithmetic — no `Float` formatting in a hot line. -/
def msSecs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

initialize progressC : IO.Ref ProgressC ← IO.mkRef {}

/-- A parsed declaration's display label (`Main.declCName`, shared with
the heartbeat).  Reached only from `progressTickImpl`, never from a
checked path. -/
def declCLabel : DeclC → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .basisDecl k => s!"basis block {repr k}"

/-- The compiled behaviour of `progressTick`: bump the fold position,
print `setlec: progress i/N <decl>` to stderr (flushed) every `stride`
declarations, **return `x`**.  `@[never_extract]` keeps the call where
it is written, so the line precedes the declaration's check. -/
@[never_extract] unsafe def progressTickImpl {α : Type}
    (pd : DeclC) (x : α) : α :=
  unsafeBaseIO do
    let st ← progressC.get
    if st.stride == 0 then
      return x
    progressC.set { st with idx := st.idx + 1 }
    if st.idx % st.stride == 0 then
      let now ← IO.monoMsNow
      let e ← IO.getStderr
      let _ ← (do
        e.putStr s!"setlec: progress {st.idx}/{st.total} {declCLabel pd} \
          t={msSecs (now - st.startMs)}s\n"
        e.flush).toBaseIO
    return x

/-- The progress hook: **the identity**, and nothing else (`rfl`).  Its
compiled companion prints the heartbeat; see the section note above. -/
@[implemented_by progressTickImpl]
def progressTick {α : Type} (_pd : DeclC) (x : α) : α := x

@[simp] theorem progressTick_eq {α : Type} (pd : DeclC) (x : α) :
    progressTick pd x = x := rfl

/-- One step of the converted-declaration fold: flush, then check
(wrapped in the identity `progressTick`, whose compiled companion emits
the opt-in heartbeat — the definition is `x`). -/
def checkDeclSPStepC (fe : FEnv) (pd : DeclC) : CheckCM FEnv :=
  progressTick pd do
    flushC
    checkDeclSPC cfg fe pd

/-- The fold's step with the **position carried and the error tagged**
(2026-09-07): the accumulator is `(i, fe)`, and a failing step reports
the `CheckError` together with `i`, the fold position of the
declaration that failed.  On the accepting side it is
`checkDeclSPStepC` exactly (`foldIdxC_ok`), which is why every
statement about the plain fold survives the change untouched. -/
def checkDeclStepIdxC (p : Nat × FEnv) (pd : DeclC) :
    StateT CState (Except (CheckError × Nat)) (Nat × FEnv) := fun s =>
  match checkDeclSPStepC cfg p.2 pd s with
  | .ok (fe', s') => .ok ((p.1 + 1, fe'), s')
  | .error e => .error (e, p.1)

/-- Task #171: the direct-parse driver.  `DeclC` records come straight
from the frontend (`Setlec/Frontend/ExportC.lean`) — no arena and no
conversion pass.

Task #172 B3b: the argument was `List WDeclC`, the subtype of records
whose `ExprC` slots carried the field invariant `WFc`, because the
capstone's entry premise was the parser's `WFc`-by-construction
theorem.  Under `@[computed_field]` (B3a) `WFc` held of everything, so
the receipt carried no information; the subtype, its predicate
`DeclCWFc` and the fold's unwrapping step are gone, and the capstone
letters below this driver are restated over `List DeclC` — strictly
stronger, by the coordinator's ratification.

**The error carries the position** (2026-09-07).  The failing
declaration used to be located by a *second pass* in `Main.lean`
(`diagLoopC`), which re-ran the same step over the same records until
it failed again — a full re-check of the accepted prefix, and a lie
waiting to happen if the two runs ever disagreed.  The fold's
accumulator now carries the position and the step tags its error with
it (`checkDeclStepIdxC`), so a rejection *is* `(CheckError × Nat)` and
the driver reports the declaration by indexing the record array it
already holds.  The **accept** side is untouched, deliberately:
`checkDeclsSPCachedD cfg ds = .ok env` is the same sentence it was, so
`no_proof_of_Empty_SPCD_P` and the agreement floor keep their
statements verbatim and reach the plain fold through `foldIdxC_ok`
below. -/
def checkDeclsSPCachedD (cfg : CoreCfg) (ds : List DeclC) :
    Except (CheckError × Nat) Env := do
  let p ← (ds.foldlM (checkDeclStepIdxC cfg) (0, mkFEnv Env.empty)).run' {}
  pure p.2.env

/-! ### The two folds agree on accepts

`foldIdxC_ok` and its `run'` corollary live here, beside the two folds,
rather than in `Setlec/Verify/*`: they are **self-contained** (they use
nothing but the two definitions above — the `Std.HashMap` exception in
CLAUDE.md), and their two consumers, `Verify/Cached/MainC.lean` and
`Verify/Cached/AgreeFloor.lean`, share no `Verify` module: a new one
holding them would enter all four capstones' proof closures, i.e. show
up as a **door** in `tests/proofdeps.sh`. -/

/-- An accepting run of the position-carrying fold is an accepting run
of the plain fold, at the same environment and residue state.  (The
error side is where they differ, and is the point of the change.) -/
theorem foldIdxC_ok (cfg : CoreCfg) (ds : List DeclC) :
    ∀ (i : Nat) (fe : FEnv) {p : Nat × FEnv} {s s' : CState},
      (ds.foldlM (checkDeclStepIdxC cfg) (i, fe)) s = .ok (p, s') →
      (ds.foldlM (checkDeclSPStepC cfg) fe) s = .ok (p.2, s') := by
  induction ds with
  | nil =>
    intro i fe p s s' h
    simp only [List.foldlM_nil, pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1 ▸ rfl, h.2⟩
  | cons pd ds ih =>
    intro i fe p s s' h
    rw [List.foldlM_cons] at h ⊢
    simp only [Bind.bind, StateT.bind] at h ⊢
    cases hstep : checkDeclSPStepC cfg fe pd s with
    | error e =>
      simp only [checkDeclStepIdxC, hstep, Except.bind] at h
      exact nomatch h
    | ok pr =>
      obtain ⟨fe₁, s₁⟩ := pr
      simp only [checkDeclStepIdxC, hstep] at h
      exact ih (i + 1) fe₁ h

/-- `foldIdxC_ok` at the shape the two capstone proofs use. -/
theorem foldIdxC_run'_ok (cfg : CoreCfg) (ds : List DeclC) (i : Nat)
    (fe : FEnv) {p : Nat × FEnv} {s : CState}
    (h : (ds.foldlM (checkDeclStepIdxC cfg) (i, fe)).run' s = .ok p) :
    (ds.foldlM (checkDeclSPStepC cfg) fe).run' s = .ok p.2 := by
  simp only [StateT.run'] at h ⊢
  cases hrun : (ds.foldlM (checkDeclStepIdxC cfg) (i, fe)) s with
  | error e => rw [hrun] at h; exact nomatch h
  | ok pr =>
    obtain ⟨p₁, s₁⟩ := pr
    rw [hrun] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    rw [foldIdxC_ok cfg ds i fe hrun]
    rfl

end Setlec.Cached
