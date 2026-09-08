import ConLeche.Cached.CheckerC

/-!
# The parsed-declaration driver on the cached representation

One `CState` for the whole stream, the environment-dependent caches
flushed per declaration, declarations consumed as `DeclC` records
straight from the direct parse (`ConLeche/Frontend/ExportC.lean`, task
#171 — no conversion detour).

`checkDeclsSPCachedD mode` is what the binary runs in BOTH modes — at
`.verified` under `--verified`, at `.trusted` under `--trusted` (the twin driver
`checkDeclsSPCachedDT` / `ConLeche/Cached/ParsedT.lean` retired
2026-09-06; the trusted lane is this driver at the other mode, and
nothing else).  Acceptance at `.verified` is covered by
`no_proof_of_Empty_SPCD_P` (`ConLeche/Verify/Cached/MainC.lean`); the two
modes agree on the install skeletons whenever both accept
(`trusted_agrees_P_skels_D`, `ConLeche/Verify/Cached/AgreeFloor.lean`).

The driver's parameter is the `CheckMode` itself (task #185; from
2026-09-06 to then a configuration record stood in for it): the knot it
ties (`coreKnotI mode`) and the install-time stages
(`checkIotaRulesF`, `checkProjIotaF`, `indBlockCapsF`,
`ctorResidualOkF` — each reads only the uninhabited-true `ttChecks`)
all take the same mode.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## Parsed declarations over `ExprC` -/

/-- A parsed declaration over `ExprC` (task #198: its constant-value
records *are* `ConLeche.ConstantVal` — the separate `ConstantValC`, whose
only difference was an `ExprC`-typed `type` field, went with the
interning-era distinction between the two expression types.  Note the
one consequence: `cv.type` is now `Expr`-typed, so dot notation on it
finds `ConLeche.Expr`'s members and NOT the cached namespace's — the two
`hasFvar`s differ (`O(1)` field read vs a walk), which is why the guard
below names `ExprC.hasFvar` outright.) -/
inductive DeclC where
  | axiomDecl (val : ConstantVal)
  | defnDecl (val : ConstantVal) (value : ExprC) (hint : ReducibilityHint)
  | thmDecl (val : ConstantVal) (value : ExprC)
  | opaqueDecl (val : ConstantVal) (value : ExprC)
  | basisDecl (kind : BasisKind)
  | indDecl (block : List ConstantInfo)

/-! ## The parsed-declaration checker -/

variable (mode : CheckMode)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : ExprC) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d i

/-- `checkConstantVal` on a converted declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `ExprC`
DAG and the operations on `ExprC` values. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) :
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
  if ExprC.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotI mode fe checkFuel).annotate 0 cv.type
  unless ExprC.allLevelParamsDefined cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let _u ← opSIxC mode fe 0 jsty
  let tyE := jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValP` over `ExprC`. -/
def checkDefnValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (fe.push (.defnInfo cvA vE hint))

/-! ## The theorem branch, cut in two (the deferred-body fan-out)

`checkThmValC` is the only branch whose work splits cleanly into "what
produces the installed constant" and "what needs the body": every step
up to and including the `ienv` recording is the former, and exactly two
— the value's `infer` and the `defeq` against the statement — are the
latter.  The cut is what lets a fan-out defer the second half; the
equation below says the two halves ARE the branch, so nothing about the
sequential fold's meaning is bent to allow it.

The cut is definitional: `thmPrepC` is the branch's prefix, `thmBodyC`
its two body steps, and the push is what the branch ends with. -/

/-- The install half of the theorem branch, in continuation-passing
form: `checkThmValC` up to and including the `ienv` recording, handing
the annotated value to `k`.  Everything here produces the installed
constant.

CPS rather than "returns `jv`" for a reason: with a return the branch
would be `thmPrepC >>= …`, and reassociating the branch's own text into
that shape is a monad law, not a definitional step (measured — `rfl`
fails).  With the continuation the cut is the text itself, and the
decomposition below is `rfl`. -/
def thmPrepC {α : Type} (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (k : ExprC → CheckCM α) : CheckCM α := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty (some (jv, jv))
  k jv

/-- The body half: the two steps of the theorem branch that need the
value — the only work a fan-out defers.  Continuation-passing for the
same reason as `thmPrepC`, and for one more: a body half that RETURNS
would re-associate the branch's binds (`(a >>= b) >>= c` against
`a >>= (b >>= c)`), which is a monad law rather than a definitional
step, and the simulation proofs follow the branch's own associativity.
With the continuation the elaborated term is the branch's, verbatim. -/
def thmBodyC {α : Type} (fe : FEnv) (nm : Name) (jty jv : ExprC)
    (k : CheckCM α) : CheckCM α := do
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {nm}")
  k

/-- `checkThmValP` over `ExprC`.

**Written as its two halves** (`thmPrepC`, `thmBodyC`): the text is the
branch's own, cut where the value first matters, so `checkThmValC_split`
below is `rfl` and the deferred-body fan-out compares against the branch
itself rather than against a restatement of it.  Cutting it after the
fact is NOT definitional — the `unless … do throw` guards elaborate to
`__do_jp` join points whose shape depends on the tail, so a prefix that
returns its value does not reassociate into the branch by `rfl`
(measured: `rfl` fails both at the function and pointwise). -/
def checkThmValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv :=
  thmPrepC mode fe cvA jty value (fun jv =>
    thmBodyC mode fe cvA.name jty jv (pure (fe.push (.thmInfo cvA jv))))

/-- **The prefix does not depend on its continuation**: running the
install half with any `k` is running it with `pure` and then `k`.  This
is what lets a run recorded with one continuation (the install pass's
job-building one) be composed with another (the branch's body half). -/
theorem thmPrepC_eq_bind {α : Type} (fe : FEnv) (cvA : ConstantVal)
    (jty value : ExprC) (k : ExprC → CheckCM α) :
    thmPrepC mode fe cvA jty value k
      = thmPrepC mode fe cvA jty value pure >>= k := by
  funext s
  unfold thmPrepC
  simp only [bind, StateT.bind, Except.bind, pure]
  -- the two sides run the same chain and differ only in the tail, so
  -- splitting each step's result closes every branch by `rfl`
  repeat' (first
    | rfl
    | dsimp only [bind, StateT.bind, Except.bind]
    | split)

/-- **The decomposition.**  The theorem branch IS its install half, its
body half and the push, in that order, at the same index and in the same
state — definitionally, because the two halves are the branch's own text
cut where the value first matters.

The first of the three lemmas the deferred-body fan-out's bridge needs
(DESIGN, "Parallelism"): index- and schedule-independent, so it stands
whatever is decided about the other two. -/
theorem checkThmValC_split (fe : FEnv) (cvA : ConstantVal)
    (jty : ExprC) (value : ExprC) :
    checkThmValC mode fe cvA jty value
      = thmPrepC mode fe cvA jty value (fun jv =>
          thmBodyC mode fe cvA.name jty jv
            (pure (fe.push (.thmInfo cvA jv)))) := rfl

/-- The install pass's own step: the same prefix, handing back the
environment the branch installs and the value a deferred body needs.
That it shares `thmPrepC` with the branch above is what makes the two
comparable at all. -/
def thmInstallOnlyC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM (FEnv × ExprC) :=
  thmPrepC mode fe cvA jty value (fun jv => pure (fe.push (.thmInfo cvA jv), jv))

/-- `checkOpaqueValP` over `ExprC`. -/
def checkOpaqueValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (fe.push (.axiomInfo cvA))

/-- One converted declaration (mirrors `checkDeclSPPlain` branch by
branch; inductive and basis blocks reuse the `Expr`-level drivers). -/
def checkDeclSPC (fe : FEnv) (pd : DeclC) : CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValC mode fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsC mode fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsC mode fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValC mode fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    checkThmValC mode fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    let fe2 ← checkOpaqueValC mode fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE := value
      checkReducePinF (sharedOpsC mode fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValC mode fe cv
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
    match directFixParts? block with
    | some p => checkDirectFixS mode fe p
    | none => checkIndDeclSF mode fe block

/-! ## Names and durations for the driver's messages -/

/-- Milliseconds as `s.d` seconds (`12345` ↦ `"12.3"`).  `Nat`
arithmetic — no `Float` formatting on a message path. -/
def msSecs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

/-- A parsed declaration's display label (`Main.declCName`, shared with
the driver's progress callback so the two can never drift). -/
def declCLabel : DeclC → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .basisDecl k => s!"basis block {repr k}"

/-- One step of the converted-declaration fold: flush, then check. -/
def checkDeclSPStepC (fe : FEnv) (pd : DeclC) : CheckCM FEnv := do
  flushC
  checkDeclSPC mode fe pd

/-- The fold's step with the **position carried and the error tagged**
(2026-09-07): the accumulator is `(i, fe)`, and a failing step reports
the `CheckError` together with `i`, the fold position of the
declaration that failed.  On the accepting side it is
`checkDeclSPStepC` exactly (`foldIdxC_ok`), which is why every
statement about the plain fold survives the change untouched. -/
def checkDeclStepIdxC (p : Nat × FEnv) (pd : DeclC) :
    StateT CState (Except (CheckError × Nat)) (Nat × FEnv) := fun s =>
  match checkDeclSPStepC mode p.2 pd s with
  | .ok (fe', s') => .ok ((p.1 + 1, fe'), s')
  | .error e => .error (e, p.1)

/-- Task #171: the direct-parse driver.  `DeclC` records come straight
from the frontend (`ConLeche/Frontend/ExportC.lean`) — no arena and no
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
`checkDeclsSPCachedD mode ds = .ok env` is the same sentence it was, so
`no_proof_of_Empty_SPCD_P` and the agreement floor keep their
statements verbatim and reach the plain fold through `foldIdxC_ok`
below. -/
def checkDeclsSPCachedD (mode : CheckMode) (ds : List DeclC) :
    Except (CheckError × Nat) Env := do
  let p ← (ds.foldlM (checkDeclStepIdxC mode) (0, mkFEnv Env.empty)).run' {}
  pure p.2.env

/-! ### The two folds agree on accepts

`foldIdxC_ok` and its `run'` corollary live here, beside the two folds,
rather than in `ConLeche/Verify/*`: they are **self-contained** (they use
nothing but the two definitions above — the `Std.HashMap` exception in
CLAUDE.md), and their two consumers, `Verify/Cached/MainC.lean` and
`Verify/Cached/AgreeFloor.lean`, share no `Verify` module: a new one
holding them would enter all four capstones' proof closures, i.e. show
up as a **door** in `tests/proofdeps.sh`. -/

/-- An accepting run of the position-carrying fold is an accepting run
of the plain fold, at the same environment and residue state.  (The
error side is where they differ, and is the point of the change.) -/
theorem foldIdxC_ok (mode : CheckMode) (ds : List DeclC) :
    ∀ (i : Nat) (fe : FEnv) {p : Nat × FEnv} {s s' : CState},
      (ds.foldlM (checkDeclStepIdxC mode) (i, fe)) s = .ok (p, s') →
      (ds.foldlM (checkDeclSPStepC mode) fe) s = .ok (p.2, s') := by
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
    cases hstep : checkDeclSPStepC mode fe pd s with
    | error e =>
      simp only [checkDeclStepIdxC, hstep, Except.bind] at h
      exact nomatch h
    | ok pr =>
      obtain ⟨fe₁, s₁⟩ := pr
      simp only [checkDeclStepIdxC, hstep] at h
      exact ih (i + 1) fe₁ h

/-! ### The deferred-body driver, as functions

The fan-out's own pieces, in the implementation layer so that the bridge
can be stated ABOUT them rather than about a restatement of them
(`Main.lean` drives these; the queue, the tasks and the reporting stay
there, because none of that is what a theorem is about).

The job carries the very `FEnv` the fold held before the theorem's push
— a pointer, because the index is persistent — so a worker checks the
body at exactly the environment the sequential fold would have. -/

/-- A deferred theorem body: where it sat in the fold, the index it must
be checked at, and the annotated statement and value. -/
structure BodyJob where
  idx : Nat
  fe : FEnv
  name : Name
  jty : ExprC
  jv : ExprC

/-- The install pass's theorem step: the branch's install half
(`thmPrepC`) and the push, with the body deferred as a job. -/
def thmInstallJobC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM (FEnv × BodyJob) :=
  thmPrepC mode fe cvA jty value (fun jv =>
    pure (fe.push (.thmInfo cvA jv), ⟨0, fe, cvA.name, jty, jv⟩))

/-- One step of the install pass: the ordinary step for every kind
except `thmDecl`, whose body is deferred. -/
def installStepC (p : Nat × FEnv × Array BodyJob) (pd : DeclC) :
    StateT CState (Except (CheckError × Nat)) (Nat × FEnv × Array BodyJob) :=
  fun s =>
    let (i, fe, jobs) := p
    match pd with
    | .thmDecl cv value =>
      match (do
          flushC
          let (cvA, jty) ← checkConstantValC mode fe cv
          thmInstallJobC mode fe cvA jty value : CheckCM (FEnv × BodyJob)) s with
      | .ok ((fe', job), s') => .ok ((i + 1, fe', jobs.push { job with idx := i }), s')
      | .error e => .error (e, i)
    | _ =>
      match checkDeclSPStepC mode fe pd s with
      | .ok (fe', s') => .ok ((i + 1, fe', jobs), s')
      | .error e => .error (e, i)

/-- The install pass over a stream. -/
def installPassC (ds : List DeclC) :
    Except (CheckError × Nat) (FEnv × Array BodyJob) := do
  let p ← (ds.foldlM (installStepC mode) (0, mkFEnv Env.empty, #[])).run' {}
  pure (p.2.1, p.2.2)

/-- One deferred body, checked at its captured index from a FRESH memo
state — which is the whole point: a worker shares no `CState` with the
fold, and `CSOK.empty` says the fresh state is sound, so the body's
cached run reaches the spec exactly as the fold's would. -/
def bodyCheckC (j : BodyJob) : Except CheckError Unit :=
  (thmBodyC mode j.fe j.name j.jty j.jv (pure ())).run' {}

/-! ### Checking in chunks is checking the stream

The second of the deferred-body bridge's three lemmas, and the one that
is pure list algebra: whatever a driver does with the stream, if it
folds the same step over consecutive pieces from the same start it has
folded over the stream.  `CheckCM` is `StateT CState (Except CheckError)`,
lawful, so both are `List.foldlM_append` and an induction on it. -/

/-- Two consecutive chunks. -/
theorem foldlM_chunk_two (ds₁ ds₂ : List DeclC) (fe : FEnv) :
    (ds₁ ++ ds₂).foldlM (checkDeclSPStepC mode) fe
      = (do
          let fe' ← ds₁.foldlM (checkDeclSPStepC mode) fe
          ds₂.foldlM (checkDeclSPStepC mode) fe') :=
  List.foldlM_append

/-- Any number of chunks: folding the step over each chunk in order,
threading the environment, is folding it over the stream.  This is what
lets a chunked driver's acceptance be an acceptance of
`checkDeclsSPCachedD`'s own fold. -/
theorem foldlM_chunks (cs : List (List DeclC)) (fe : FEnv) :
    cs.flatten.foldlM (checkDeclSPStepC mode) fe
      = cs.foldlM (fun fe' c => c.foldlM (checkDeclSPStepC mode) fe') fe := by
  induction cs generalizing fe with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatten_cons, foldlM_chunk_two, List.foldlM_cons]
    exact bind_congr fun fe' => ih fe'

/-- `foldIdxC_ok` at the shape the two capstone proofs use. -/
theorem foldIdxC_run'_ok (mode : CheckMode) (ds : List DeclC) (i : Nat)
    (fe : FEnv) {p : Nat × FEnv} {s : CState}
    (h : (ds.foldlM (checkDeclStepIdxC mode) (i, fe)).run' s = .ok p) :
    (ds.foldlM (checkDeclSPStepC mode) fe).run' s = .ok p.2 := by
  simp only [StateT.run'] at h ⊢
  cases hrun : (ds.foldlM (checkDeclStepIdxC mode) (i, fe)) s with
  | error e => rw [hrun] at h; exact nomatch h
  | ok pr =>
    obtain ⟨p₁, s₁⟩ := pr
    rw [hrun] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    rw [foldIdxC_ok mode ds i fe hrun]
    rfl

end ConLeche.Cached
