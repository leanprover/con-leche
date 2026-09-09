module

public import ConLeche.Cached.ParsedC
public import ConLeche.Kernel.CheckerSplit

@[expose] public section

/-!
# Installed environments, checked groups, fully checked environments
(task #253)

The binary's ONE driver (`Main.lean`) separates INSTALLING a declaration
from CHECKING it, and its output type is the assurance that it did what
it claims:

* **Phase A** folds `annotDeclStep` over the parsed records: a
  `defn`/`thm`/`opaque` record is annotated and INSTALLED without its
  inference — the syntactic guards and the annotation of its type and
  value run, the constant is pushed — and a `PendingCheck` records the
  datum the check needs (`ValueGroup`, `ConLeche/Kernel/CheckerSplit.lean`)
  together with the environment counter the declaration was installed
  at (`fe.visibleBelow`, task #108).  Every other kind — axioms,
  inductive and basis blocks, and the pinned `Nat`-operation and
  `reduce*` branches, whose checks are not separable from their
  installs — takes the ordinary step `checkDeclStepC`.  An accepting
  phase A over `ds` IS an `InstalledEnv mode ds`: the index, the
  records, and the chain of accepting steps (`InstallRun`) that produced
  them.
* **Phase B** checks each record against the PREFIX VIEW
  `fe.restrictTo vis` (`FEnv.restrictTo`: an `O(1)` field update whose
  `find?` is the lookup in the environment truncated to the first
  `vis` constants, `mkFEnv_find?_visibleBelow`), each from a FRESH memo
  state: `GroupChecked e i` says record `i`'s check succeeded.  It reads
  the installed environment, record `i`, and nothing else — a
  proposition workers can establish independently of one another.
* `FullyChecked mode ds` is the subtype of installed environments every
  record of which is checked, and `FullyChecked.assemble` the
  assembly.  The consistency theorem is stated on it
  (`ConLeche.no_proof_of_False`, `ConLeche/MainTheorem.lean`): whoever
  holds a `FullyChecked .verified ds` holds an environment with no
  constant of type `False`, whatever loop — pure, printing, parallel —
  produced it.

Nothing here is `IO`: the driver's loops in `Main.lean` run these
steps and carry their accepting runs as the proofs the subtypes ask
for.  The verdict is the ordinary fold's (`checkDecls`) on every accept
— both are `FullyCheckedSpec` environments
(`ConLeche/Verify/Cached/InstalledC.lean`) — and a phase-B failure is
tagged with the FOLD POSITION of the declaration it checks
(`PendingCheck.pos`), as the fold's errors are.  The two may report a
stream that fails for two reasons at different positions: phase A
annotates a value before the fold would have inferred the type's sort.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-! ## Phase A: install -/

/-- A phase-A record awaiting its phase-B check: the datum that crosses
the install/check seam, the fold position of the declaration (its
error tag) and the environment counter at the install — `fe.visibleBelow`
before the push, i.e. the number of constants installed before it. -/
structure PendingCheck where
  vg : ValueGroup
  pos : Nat
  vis : Nat

/-- `checkConstantValC` minus its inference: the syntactic guards and
the annotation of the type — `installConstantVal`'s cached twin. -/
def annotConstantValC (fe : FEnv) (cv : ConstantVal) :
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
  pure (⟨cv.name, cv.levelParams, jty⟩, jty)

/-- The value half of `checkDefnValC`/`checkThmValC`/`checkOpaqueValC`
minus its inference: the guards, the annotation, and the
converted-constant record (`record` is `false` for an opaque, whose
value is a discarded witness) — `installValue`'s cached twin. -/
def annotValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (record : Bool) : CheckCM ExprC := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty (if record then some (jv, jv) else none)
  pure jv

/-- Phase A's install of a separable value declaration: the
per-declaration flush, then the header's and the value's install halves;
returns the header with its annotated type, that type, and the
annotated value. -/
def annotValueC (fe : FEnv) (cv : ConstantVal) (value : ExprC) (record : Bool) :
    CheckCM (ConstantVal × ExprC × ExprC) := do
  flushC
  let (cvA, jty) ← annotConstantValC mode fe cv
  let jv ← annotValC mode fe cvA jty value record
  pure (cvA, jty, jv)

/-- Phase A's step body: annotate-and-install for the three value
kinds, the ordinary step `checkDeclStepC` for everything else.  `i` is
the fold position the record is tagged with.  (The continuations read
the install's result by projection, so that the statements about this
function match it syntactically.) -/
def annotStepC (i : Nat) (fe : FEnv) (pend : Array PendingCheck) :
    DeclC → CheckCM (FEnv × Array PendingCheck)
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then do
      pure (← checkDeclStepC mode fe (.defnDecl cv value hint), pend)
    else do
      let r ← annotValueC mode fe cv value true
      -- RC linearity: the counter is read BEFORE the push, so that
      -- `fe` reaches `push` unshared (read after it, the push copies
      -- the whole index at every install)
      let vis := fe.visibleBelow
      pure (fe.push (.defnInfo r.1 r.2.2 hint),
        pend.push ⟨⟨.defn, r.1, r.2.2⟩, i, vis⟩)
  | .thmDecl cv value => do
    let r ← annotValueC mode fe cv value true
    let vis := fe.visibleBelow
    pure (fe.push (.thmInfo r.1 r.2.2),
      pend.push ⟨⟨.thm, r.1, r.2.2⟩, i, vis⟩)
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then do
      pure (← checkDeclStepC mode fe (.opaqueDecl cv value), pend)
    else do
      let r ← annotValueC mode fe cv value false
      let vis := fe.visibleBelow
      pure (fe.push (.axiomInfo r.1),
        pend.push ⟨⟨.opaque, r.1, r.2.2⟩, i, vis⟩)
  | pd => do
    pure (← checkDeclStepC mode fe pd, pend)

/-- Phase A's step with the position carried and the error tagged,
exactly as `checkDeclStep` does. -/
def annotDeclStep (p : Nat × FEnv × Array PendingCheck) (pd : DeclC) :
    StateT CState (Except (CheckError × Nat)) (Nat × FEnv × Array PendingCheck) :=
  fun s =>
    match annotStepC mode p.1 p.2.1 p.2.2 pd s with
    | .ok ((fe', pend'), s') => .ok ((p.1 + 1, fe', pend'), s')
    | .error e => .error (e, p.1)

/-- **Phase A's accepting run**: a chain of accepting `annotDeclStep`s
over the records, from an accumulator and memo state to the final
ones.  A loop builds it step by step, whatever else it does between
the steps. -/
inductive InstallRun : List DeclC → (Nat × FEnv × Array PendingCheck) → CState →
    (Nat × FEnv × Array PendingCheck) → CState → Prop where
  | nil (p : Nat × FEnv × Array PendingCheck) (s : CState) : InstallRun [] p s p s
  | cons {pd : DeclC} {ds : List DeclC} {p p₁ p' : Nat × FEnv × Array PendingCheck}
      {s s₁ s' : CState} (h : annotDeclStep mode p pd s = .ok (p₁, s₁))
      (rest : InstallRun ds p₁ s₁ p' s') : InstallRun (pd :: ds) p s p' s'

/-- A run extends at its end by one accepting step: what a loop that
carries the run of the records it has consumed uses at each step. -/
theorem InstallRun.snoc {ds : List DeclC} {p p' : Nat × FEnv × Array PendingCheck}
    {s s' : CState} (h : InstallRun mode ds p s p' s') {pd : DeclC}
    {p₁ : Nat × FEnv × Array PendingCheck} {s₁ : CState}
    (hstep : annotDeclStep mode p' pd s' = .ok (p₁, s₁)) :
    InstallRun mode (ds ++ [pd]) p s p₁ s₁ := by
  induction h with
  | nil p s => exact .cons hstep (.nil _ _)
  | cons h₀ _ ih => exact .cons h₀ (ih hstep)

/-- **An environment properly installed from `ds`**: the index and the
records phase A produced, with the accepting run that produced them
from the empty environment and the fresh memo state. -/
structure InstalledEnv (ds : List DeclC) where
  fe : FEnv
  pend : Array PendingCheck
  run : ∃ (n : Nat) (s : CState),
    InstallRun mode ds (0, mkFEnv Env.empty, #[]) {} (n, fe, pend) s

/-- The environment of an installed environment. -/
def InstalledEnv.env {ds : List DeclC} (e : InstalledEnv mode ds) : Env := e.fe.env

/-! ## Phase B: check -/

/-- Phase B's check of one record against the prefix view, from a
flushed memo state: `checkValueGroup`'s inference and conversion calls
(`ConLeche/Kernel/CheckerSplit.lean`) — those of `checkConstantValC` and
`check{Defn,Thm,Opaque}ValC`, in their order, with their messages — on
the cached core at the view. -/
def checkPending (fe : FEnv) (pc : PendingCheck) : CheckCM Unit := do
  flushC
  let fe := fe.restrictTo pc.vis
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 pc.vg.cvA.type
  let u ← opSIxC mode fe 0 jsty
  if pc.vg.kind = .thm then
    unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
      throw (.invalid s!"type of theorem {pc.vg.cvA.name} is not a proposition")
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 pc.vg.jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt pc.vg.cvA.type do
    throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")

/-- **In a properly installed environment, record `i` has been
checked**: its check against the prefix view, from a fresh memo state,
succeeded.  (A declaration without a record was checked in full at its
install, inside `InstallRun`.) -/
def GroupChecked {ds : List DeclC} (e : InstalledEnv mode ds) (i : Nat) : Prop :=
  match e.pend[i]? with
  | some pc => ∃ s', checkPending mode e.fe pc {} = .ok ((), s')
  | none => True

/-- **A fully checked environment from `ds`**: properly installed, every
record checked. -/
def FullyChecked (ds : List DeclC) : Type :=
  { e : InstalledEnv mode ds // ∀ i, GroupChecked mode e i }

/-- Properly installed plus every record checked is fully checked. -/
def FullyChecked.assemble {ds : List DeclC} (e : InstalledEnv mode ds)
    (h : ∀ i, GroupChecked mode e i) : FullyChecked mode ds := ⟨e, h⟩

/-- The environment of a fully checked environment. -/
def FullyChecked.env {ds : List DeclC} (fc : FullyChecked mode ds) : Env := fc.1.fe.env

/-! ## The records' checks, in the type

A loop over the records that carries the checks it has established:
`GroupChecked` of every record below `k`, extended one record at a
time.  `checkRecord` is the one step both the pure fold and the driver's
printing loop take; the accumulator's extension and the closing
argument are the two lemmas beside it. -/

/-- Record `k`'s check, as its `GroupChecked` fact. -/
theorem groupChecked_of_run {ds : List DeclC} (e : InstalledEnv mode ds) {k : Nat}
    (hk : k < e.pend.size) {s' : CState}
    (h : checkPending mode e.fe e.pend[k] {} = .ok ((), s')) :
    GroupChecked mode e k := by
  unfold GroupChecked
  rw [Array.getElem?_eq_getElem hk]
  exact ⟨s', h⟩

/-- Beyond the records, nothing is pending. -/
theorem groupChecked_of_ge {ds : List DeclC} (e : InstalledEnv mode ds) {k : Nat}
    (hk : e.pend.size ≤ k) : GroupChecked mode e k := by
  unfold GroupChecked
  rw [Array.getElem?_eq_none hk]
  trivial

/-- The accumulator, one record further. -/
theorem groupChecked_extend {ds : List DeclC} {e : InstalledEnv mode ds} {k : Nat}
    (acc : ∀ j, j < k → GroupChecked mode e j) (hk : GroupChecked mode e k) :
    ∀ j, j < k + 1 → GroupChecked mode e j := by
  intro j hj
  by_cases hjk : j < k
  · exact acc j hjk
  · have : j = k := by omega
    subst this
    exact hk

/-- The closing argument: every record below the size, and nothing
beyond it. -/
theorem groupChecked_all {ds : List DeclC} {e : InstalledEnv mode ds}
    (acc : ∀ j, j < e.pend.size → GroupChecked mode e j) : ∀ i, GroupChecked mode e i := by
  intro i
  by_cases hi : i < e.pend.size
  · exact acc i hi
  · exact groupChecked_of_ge mode e (Nat.le_of_not_lt hi)

end ConLeche.Cached
