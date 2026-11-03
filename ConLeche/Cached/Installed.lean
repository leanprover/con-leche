module

public import ConLeche.Cached.ParsedC
public import ConLeche.Kernel.CheckerSplit

@[expose] public section

/-!
# The declaration fold: install first, check afterwards

`checkDecls mode pins ds` is the verified implementation: the pure fold the
main theorem and the main corollary are stated about
(`ConLeche/MainTheorem.lean`), and the algorithm the binary's driver
(`ConLeche/Driver/*`) runs — the driver's loops are this fold's two phases with
a heartbeat between the steps, and the driver returns its environment
together with the proof that `checkDecls` returns it
(`fullyChecked_checkDecls`).  The fold separates INSTALLING a
declaration from CHECKING it:

* **Phase A** folds `installDeclStep` over the parsed records: a
  `defn`/`opaque` record is INSTALLED without its inference — the
  syntactic guards of its type and value run, the constant is pushed —
  and a `thm` record is installed BY STATEMENT: its header alone is
  guarded and the constant pushed
  with its statement only (a stored theorem carries no value: it is
  opaque to reduction), so phase A never enters a theorem's body;
  either way a `PendingCheck` records the datum the check needs
  (`ValueGroup`, `ConLeche/Kernel/CheckerSplit.lean` — the value of
  a definition or opaque, the raw value of a theorem) together
  with the environment counter the declaration was installed at
  (`fe.visibleBelow`, task #108).  Every other kind — axioms,
  inductive and basis blocks, and the pinned `Nat`-operation and
  `reduce*` branches, whose checks are not separable from their
  installs — takes the ordinary step `checkDeclStepC`.  Every step
  runs from a FRESH memo state: nothing but the index crosses from one
  record to the next, so a record's install is a function of the
  index it sees and the record alone.  An accepting
  phase A over `ds` IS an `InstalledEnv mode ds`: the index, the
  records, and the chain of accepting steps (`InstallRun`) that produced
  them.
* **Phase B** checks each record against the PREFIX VIEW
  `fe.restrictTo vis` (`FEnv.restrictTo`: an `O(1)` field update whose
  `find?` is the lookup in the environment truncated to the first
  `vis` constants, `mkFEnv_find?_visibleBelow`), each from a FRESH memo
  state — a theorem's value is guarded here, at the view, before it
  is inferred: `GroupChecked e i` says record `i`'s check succeeded.  It reads
  the installed environment, record `i`, and nothing else — a
  proposition workers can establish independently of one another.
* `FullyChecked mode ds` is the subtype of installed environments every
  record of which is checked: the driver's intermediate.  **A fully
  checked environment is exactly an accept of the fold**:
  `fullyChecked_checkDecls` says `checkDecls` returns its environment,
  `checkDecls_fullyChecked` that every accept yields one.

**THE PIN LIST IS A PARAMETER** (task #304).  Every function of this
fold — `checkDecls`, `installDeclStep`, `installStepC` and, below them,
`checkDeclStepC`/`checkDeclC` and the `Expr`-level `checkDecl` — takes
the list of `Nat.div`/`Nat.mod` pin variants its install gate tries,
uniformly as its SECOND argument, right after `mode`; so do the types
stated over the steps (`InstallRun`, `InstalledEnv`, `GroupChecked`,
`FullyChecked` — implicitly wherever the installed environment already
determines it).  The shipped checker runs at `natOpPinSets`, the
variants this toolchain committed, and the binary's driver passes it;
the main theorem and the main corollary (`ConLeche/MainTheorem.lean`)
are stated for EVERY list, because nothing the model tier consumes
reads which list the matched variant came from.

Nothing here is `IO`: the driver's loops in `ConLeche/Driver/*` run these
steps and carry their accepting runs as the proofs the subtypes ask
for.  **The parallel install checks an inductive block in the check
phase** (tasks #411, #431): it pushes a block as stored
(`storedInstall`, `ConLeche/Cached/StoredInstall.lean`) and records the
block's checked install, compared with those pushes, as a job of the
check phase, so the run it carries is this fold's run CONDITIONAL on
those jobs; the check phase discharges them, and the run is this
fold's (`ConLeche/Verify/Cached/Defer.lean`).  A rejection carries the FOLD POSITION of the declaration it
names (`installDeclStep` tags its error with the position, a phase-B
failure with `PendingCheck.pos`), so the driver reports the
declaration by indexing the record array it already holds, with no
second pass.
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

/-- `checkConstantValC` minus its inference: the header's syntactic
guards — `installHeader`'s cached twin. -/
def installHeaderC (fe : FEnv) (cv : ConstantVal) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorL (strLitSupportedF fe) s!"type of {cv.name}" cv.type)

/-- The value's syntactic guards (those of `checkDefnValCI`, without its
inference) — `installValueGuards`'s cached twin. -/
def installValueGuardsC (fe : FEnv) (cv : ConstantVal) (value : Expr) : CheckCM Unit := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams value do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless constsResolveFC fe value do
    throw (unresolvedConstsErrorL (strLitSupportedF fe) s!"value of {cv.name}" value)

/-- Phase A's guards of a separable value declaration: the
per-declaration flush, then the header's and the value's guards. -/
def installGuardsC (fe : FEnv) (cv : ConstantVal) (value : Expr) :
    CheckCM Unit := do
  flushC
  installHeaderC fe cv
  installValueGuardsC fe cv value

/-- Phase A's step body: guard-and-install for the three value
kinds, the ordinary step `checkDeclStepC` for everything else.  `i` is
the fold position the record is tagged with.  (The continuations read
the install's result by projection, so that the statements about this
function match it syntactically.) -/
def installStepC (pins : List NatOpPinSet) (i : Nat) (fe : FEnv)
    (pend : Array PendingCheck) :
    Declaration → CheckCM (FEnv × Array PendingCheck)
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then do
      pure (← checkDeclStepC mode pins fe (.defnDecl cv value hint), pend)
    else do
      installGuardsC fe cv value
      -- RC linearity: the counter is read BEFORE the push, so that
      -- `fe` reaches `push` unshared (read after it, the push copies
      -- the whole index at every install)
      let vis := fe.visibleBelow
      pure (fe.push (.defnInfo cv value hint),
        pend.push ⟨⟨.defn, cv, value⟩, i, vis⟩)
  | .thmDecl cv value => do
    -- a theorem installs BY STATEMENT: the header's install half
    -- only; the value is recorded raw and never touched here (phase B
    -- guards it, `checkPending`), so phase A never enters a
    -- theorem's body
    flushC
    installHeaderC fe cv
    let vis := fe.visibleBelow
    pure (fe.push (.thmInfo cv),
      pend.push ⟨⟨.thm, cv, value⟩, i, vis⟩)
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then do
      pure (← checkDeclStepC mode pins fe (.opaqueDecl cv value), pend)
    else do
      installGuardsC fe cv value
      let vis := fe.visibleBelow
      pure (fe.push (.axiomInfo cv),
        pend.push ⟨⟨.opaque, cv, value⟩, i, vis⟩)
  | pd => do
    pure (← checkDeclStepC mode pins fe pd, pend)

/-- Phase A's step with the position carried and the error tagged: the
accumulator is `(i, fe, pend)`, and a failing step reports the
`CheckError` together with `i`, the fold position of the declaration
that failed.

**The `And` pin comes first** (`andPinOk`, `ConLeche/Kernel/Basis.lean`):
a record that declares `And`, `And.intro` or `And.rec` and is not the
toolchain's `And` block is REJECTED here, whatever its kind — so the
name `And` in an accepted environment is the pinned block, installed
by the ordinary installer, and the stuck-proof rescue that serves it
(`majorToCtor`'s `And` branch) is always available.  The test sits in
the fold's step, ahead of the kind dispatch, because it is one rule
over every kind of record; the soundness proofs never read it (the
rescue is sound for any `And`), so `checkDecl` does not repeat it. -/
def installDeclStep (pins : List NatOpPinSet)
    (p : Nat × FEnv × Array PendingCheck) (pd : Declaration) :
    Except (CheckError × Nat) (Nat × FEnv × Array PendingCheck) :=
  if andPinOk pd then
    match installStepC mode pins p.1 p.2.1 p.2.2 pd {} with
    | .ok ((fe', pend'), _) => .ok (p.1 + 1, fe', pend')
    | .error e => .error (e, p.1)
  else .error (.invalid "`And` must be the standard `And`", p.1)

/-- **Phase A's accepting run**: a chain of accepting `installDeclStep`s
over the records, from an accumulator to the final one.  A loop builds
it step by step, whatever else it does between the steps.  (No memo
state crosses a step: every record is installed from a fresh one.) -/
inductive InstallRun (pins : List NatOpPinSet) :
    List Declaration → (Nat × FEnv × Array PendingCheck) →
    (Nat × FEnv × Array PendingCheck) → Prop where
  | nil (p : Nat × FEnv × Array PendingCheck) :
      InstallRun pins [] p p
  | cons {pd : Declaration} {ds : List Declaration} {p p₁ p' : Nat × FEnv × Array PendingCheck}
      (h : installDeclStep mode pins p pd = .ok p₁)
      (rest : InstallRun pins ds p₁ p') :
      InstallRun pins (pd :: ds) p p'

/-- The tagged step's accept is the body's accept at the next position,
from a fresh memo state. -/
theorem installDeclStep_ok {mode : CheckMode} {pins : List NatOpPinSet}
    {p : Nat × FEnv × Array PendingCheck}
    {pd : Declaration} {q : Nat × FEnv × Array PendingCheck}
    (h : installDeclStep mode pins p pd = .ok q) :
    ∃ fe' pend' s', q = (p.1 + 1, fe', pend') ∧
      installStepC mode pins p.1 p.2.1 p.2.2 pd {} = .ok ((fe', pend'), s') := by
  unfold installDeclStep at h
  split at h
  case isFalse => exact nomatch h
  cases hs : installStepC mode pins p.1 p.2.1 p.2.2 pd {} with
  | error e => rw [hs] at h; exact nomatch h
  | ok r =>
    obtain ⟨⟨fe', pend'⟩, s₁⟩ := r
    rw [hs] at h
    simp only [Except.ok.injEq] at h
    exact ⟨fe', pend', s₁, h.symm, rfl⟩

/-- A run extends at its end by one accepting step: what a loop that
carries the run of the records it has consumed uses at each step. -/
theorem InstallRun.snoc {pins : List NatOpPinSet} {ds : List Declaration}
    {p p' : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p p') {pd : Declaration}
    {p₁ : Nat × FEnv × Array PendingCheck}
    (hstep : installDeclStep mode pins p' pd = .ok p₁) :
    InstallRun mode pins (ds ++ [pd]) p p₁ := by
  induction h with
  | nil p => exact .cons hstep (.nil _)
  | cons h₀ _ ih => exact .cons h₀ (ih hstep)

/-- **An environment properly installed from `ds`**: the index and the
records phase A produced, with the accepting run that produced them
from the empty environment. -/
structure InstalledEnv (pins : List NatOpPinSet) (ds : List Declaration) where
  fe : FEnv
  pend : Array PendingCheck
  run : ∃ (n : Nat),
    InstallRun mode pins ds (0, mkFEnv Env.empty, #[]) (n, fe, pend)

/-! ## Phase B: check -/

/-- Phase B's check of one record against the prefix view, from a
flushed memo state: `checkValueGroup`'s inference and conversion calls
(`ConLeche/Kernel/CheckerSplit.lean`) — those of `checkConstantValC` and
`check{Defn,Thm,Opaque}ValC`, in their order, with their messages — on
the cached core at the view. -/
def checkPending (fe : FEnv) (pc : PendingCheck) : CheckCM Unit := do
  flushC
  let fe := fe.restrictTo pc.vis
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 pc.vg.cv.type
  let u ← opSIxC mode fe 0 jsty
  if pc.vg.kind = .thm then do
      unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
        throw (.invalid s!"type of theorem {pc.vg.cv.name} is not a proposition")
      -- a theorem's value arrives raw: its guards run
      -- here, at the view (`installValueGuardsC` — `installValueGuards`'s twin)
      installValueGuardsC fe pc.vg.cv pc.vg.jv
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 pc.vg.jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt pc.vg.cv.type do
    throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cv.name}")

/-- **In a properly installed environment, record `i` has been
checked**: its check against the prefix view, from a fresh memo state,
succeeded.  (A declaration without a record was checked in full at its
install, inside `InstallRun`.) -/
def GroupChecked {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) (i : Nat) : Prop :=
  match e.pend[i]? with
  | some pc => ∃ s', checkPending mode e.fe pc {} = .ok ((), s')
  | none => True

/-- **A fully checked environment from `ds`**: properly installed, every
record checked. -/
def FullyChecked (pins : List NatOpPinSet) (ds : List Declaration) : Type :=
  { e : InstalledEnv mode pins ds // ∀ i, GroupChecked mode e i }

/-- The environment of a fully checked environment. -/
def FullyChecked.env {pins : List NatOpPinSet} {ds : List Declaration}
    (fc : FullyChecked mode pins ds) : Env := fc.1.fe.env

/-! ## The fold, and the fully checked environment it is

`checkDecls` is phase A as a `foldlM` over the records and phase B as a
walk over the records.  An accepting `InstallRun` is an accepting
`foldlM` and conversely; every record checked is the walk's accept and
conversely; so a `FullyChecked mode ds` and an accept of `checkDecls`
are the same evidence in two dressings.  The lemmas are self-contained
(they use nothing but the definitions above — the `Std.HashMap`
exception in CLAUDE.md), so they live beside the fold: a `Verify`
module holding them would enter every capstone's proof closure. -/

/-- Phase B as a pure walk: every record checked from a fresh memo
state, a failure tagged with the record's fold position. -/
def checkPendingList (fe : FEnv) : List PendingCheck → Except (CheckError × Nat) Unit
  | [] => .ok ()
  | pc :: rest =>
    match checkPending mode fe pc {} with
    | .ok _ => checkPendingList fe rest
    | .error e => .error (e, pc.pos)

/-- **The declaration fold**: install every record (phase A), check
every recorded declaration (phase B), return the environment.

The records are the ARRAY the frontend produces and the driver holds
(`Frontend.preparePrelude`) — phase A is `Array.foldlM` over it, phase
B a walk over the array of records phase A recorded, and nothing on
the run path builds a list of millions of declarations.  The PROOFS
below read the same fold as `ds.toList.foldlM` (`Array.foldlM_toList`),
which is where `InstallRun` and every lemma above it live; the
`× Nat` of the error is the failure's POSITION — here the record's
position in the fold, in the frontend's half of the same error type
the input's LINE number (`ConLeche/Frontend/Export.lean`). -/
def checkDecls (mode : CheckMode) (pins : List NatOpPinSet)
    (ds : Array Declaration) :
    Except (CheckError × Nat) Env := do
  let p ← ds.foldlM (installDeclStep mode pins) (0, mkFEnv Env.empty, #[])
  checkPendingList mode p.2.1 p.2.2.toList
  pure p.2.1.env

/-- An accepting run is an accepting `foldlM`. -/
theorem InstallRun.foldlM {pins : List NatOpPinSet} {ds : List Declaration}
    {p p' : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p p') :
    ds.foldlM (installDeclStep mode pins) p = .ok p' := by
  induction h with
  | nil p => rfl
  | cons hstep _ ih =>
    rw [List.foldlM_cons]
    simp only [Bind.bind, hstep, Except.bind]
    exact ih

/-- An accepting `foldlM` is an accepting run. -/
theorem InstallRun.of_foldlM {pins : List NatOpPinSet} :
    ∀ (ds : List Declaration) (p : Nat × FEnv × Array PendingCheck)
      {p' : Nat × FEnv × Array PendingCheck},
      ds.foldlM (installDeclStep mode pins) p = .ok p' →
      InstallRun mode pins ds p p'
  | [], p, p', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .nil p
  | pd :: ds, p, p', h => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind] at h
    cases hstep : installDeclStep mode pins p pd with
    | error e => simp only [hstep, Except.bind] at h; exact nomatch h
    | ok p₁ =>
      simp only [hstep, Except.bind] at h
      exact .cons hstep (InstallRun.of_foldlM ds p₁ h)

/-- Every record checked is the walk's accept. -/
theorem checkPendingList_ok (fe : FEnv) :
    ∀ (l : List PendingCheck),
      (∀ pc ∈ l, ∃ s', checkPending mode fe pc {} = .ok ((), s')) →
      checkPendingList mode fe l = .ok ()
  | [], _ => rfl
  | pc :: rest, h => by
    obtain ⟨s', hpc⟩ := h pc List.mem_cons_self
    unfold checkPendingList
    rw [hpc]
    exact checkPendingList_ok fe rest fun pc' hpc' => h pc' (List.mem_cons_of_mem _ hpc')

/-- The walk's accept checks every record. -/
theorem checkPendingList_records (fe : FEnv) :
    ∀ (l : List PendingCheck), checkPendingList mode fe l = .ok () →
      ∀ pc ∈ l, ∃ s', checkPending mode fe pc {} = .ok ((), s')
  | [], _, _, hpc => (List.not_mem_nil hpc).elim
  | pc :: rest, h, pc', hpc' => by
    unfold checkPendingList at h
    cases hchk : checkPending mode fe pc {} with
    | error e => rw [hchk] at h; exact nomatch h
    | ok r =>
      obtain ⟨⟨⟩, s'⟩ := r
      rw [hchk] at h
      rcases List.mem_cons.mp hpc' with rfl | hpc'
      · exact ⟨s', hchk⟩
      · exact checkPendingList_records fe rest h pc' hpc'

/-- Every record of a fully checked environment was checked from a
fresh memo state. -/
theorem FullyChecked.records {pins : List NatOpPinSet} {ds : List Declaration}
    (fc : FullyChecked mode pins ds) :
    ∀ pc ∈ fc.1.pend.toList, ∃ s'', checkPending mode fc.1.fe pc {} = .ok ((), s'') := by
  intro pc hpc
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpc
  have h := fc.2 k
  unfold GroupChecked at h
  rw [Array.getElem?_toList] at hk
  rw [hk] at h
  exact h

/-- **The fold returns a fully checked environment's environment**: what
the driver's loops assembled, `checkDecls` computes — the proof the
driver returns beside its environment. -/
theorem fullyChecked_checkDecls {pins : List NatOpPinSet} {ds : Array Declaration}
    (fc : FullyChecked mode pins ds.toList) :
    checkDecls mode pins ds = .ok fc.env := by
  obtain ⟨n, r⟩ := fc.1.run
  unfold checkDecls
  rw [← Array.foldlM_toList, r.foldlM]
  show (checkPendingList mode fc.1.fe fc.1.pend.toList >>= fun _ => pure fc.1.fe.env) = _
  rw [checkPendingList_ok mode fc.1.fe fc.1.pend.toList fc.records]
  rfl

/-- **Every accept of the fold is a fully checked environment.** -/
theorem checkDecls_fullyChecked {pins : List NatOpPinSet} {ds : Array Declaration}
    {env : Env} (h : checkDecls mode pins ds = .ok env) :
    ∃ fc : FullyChecked mode pins ds.toList, fc.env = env := by
  unfold checkDecls at h
  rw [← Array.foldlM_toList] at h
  cases hrun : ds.toList.foldlM (installDeclStep mode pins) (0, mkFEnv Env.empty, #[]) with
  | error e => rw [hrun] at h; exact nomatch h
  | ok r =>
    obtain ⟨n, fe, pend⟩ := r
    rw [hrun] at h
    change (checkPendingList mode fe pend.toList >>= fun _ => pure fe.env) = _ at h
    cases hchk : checkPendingList mode fe pend.toList with
    | error e => rw [hchk] at h; exact nomatch h
    | ok u =>
      rw [hchk] at h
      obtain rfl : fe.env = env := Except.ok.inj h
      let e : InstalledEnv mode pins ds.toList :=
        ⟨fe, pend, n, InstallRun.of_foldlM mode ds.toList _ hrun⟩
      refine ⟨⟨e, fun i => ?_⟩, rfl⟩
      unfold GroupChecked
      cases hi : pend[i]? with
      | none => trivial
      | some pc =>
        exact checkPendingList_records mode fe pend.toList hchk pc
          (List.mem_iff_getElem?.mpr ⟨i, by rw [Array.getElem?_toList]; exact hi⟩)

end ConLeche.Cached
