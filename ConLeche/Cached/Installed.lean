module

public import ConLeche.Cached.ParsedC
public import ConLeche.Kernel.CheckerSplit

@[expose] public section

/-!
# The declaration fold: install first, check afterwards

`checkDecls mode pins ds` is the verified implementation: the pure fold the
main theorem and the main corollary are stated about
(`ConLeche/MainTheorem.lean`), and the algorithm the binary's driver
(`Main.lean`) runs — the driver's loops are this fold's two phases with
a heartbeat between the steps, and the driver returns its environment
together with the proof that `checkDecls` returns it
(`fullyChecked_checkDecls`).  The fold separates INSTALLING a
declaration from CHECKING it:

* **Phase A** folds `annotDeclStep` over the parsed records: a
  `defn`/`opaque` record is annotated and INSTALLED without its
  inference — the syntactic guards and the annotation of its type and
  value run, the constant is pushed — and a `thm` record is installed
  BY STATEMENT: its header alone is annotated and the constant pushed
  with its statement only (a stored theorem carries no value: it is
  opaque to reduction), so phase A never enters a theorem's body;
  either way a `PendingCheck` records the datum the check needs
  (`ValueGroup`, `ConLeche/Kernel/CheckerSplit.lean` — the annotated
  value of a definition or opaque, the raw value of a theorem) together
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
  state — a theorem's value is annotated here, at the view, before it
  is inferred: `GroupChecked e i` says record `i`'s check succeeded.  It reads
  the installed environment, record `i`, and nothing else — a
  proposition workers can establish independently of one another.
* `FullyChecked mode ds` is the subtype of installed environments every
  record of which is checked: the driver's intermediate.  **A fully
  checked environment is exactly an accept of the fold**:
  `fullyChecked_checkDecls` says `checkDecls` returns its environment,
  `checkDecls_fullyChecked` that every accept yields one.

**THE PIN LIST IS A PARAMETER** (task #304).  Every function of this
fold — `checkDecls`, `annotDeclStep`, `annotStepC` and, below them,
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

Nothing here is `IO`: the driver's loops in `Main.lean` run these
steps and carry their accepting runs as the proofs the subtypes ask
for.  A rejection carries the FOLD POSITION of the declaration it
names (`annotDeclStep` tags its error with the position, a phase-B
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

/-- `checkConstantValC` minus its inference: the syntactic guards and
the annotation of the type — `installConstantVal`'s cached twin. -/
def annotConstantValC (fe : FEnv) (cv : ConstantVal) :
    CheckCM (ConstantVal × Expr) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotI mode fe checkFuel).annotate 0 cv.type
  unless Expr.allLevelParamsDefinedC cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (unresolvedConstsError s!"type of {cv.name}" jty)
  pure (⟨cv.name, cv.levelParams, jty⟩, jty)

/-- The value half of `checkDefnValC`/`checkThmValC`/`checkOpaqueValC`
minus its inference: the guards and the annotation —
`installValue`'s cached twin. -/
def annotValC (fe : FEnv) (cvA : ConstantVal) (value : Expr) : CheckCM Expr := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless Expr.allLevelParamsDefinedC cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsError s!"value of {cvA.name}" jv)
  pure jv

/-- Phase A's install of a separable value declaration: the
per-declaration flush, then the header's and the value's install halves;
returns the header with its annotated type, that type, and the
annotated value. -/
def annotValueC (fe : FEnv) (cv : ConstantVal) (value : Expr) :
    CheckCM (ConstantVal × Expr × Expr) := do
  flushC
  let (cvA, jty) ← annotConstantValC mode fe cv
  let jv ← annotValC mode fe cvA value
  pure (cvA, jty, jv)

/-- Phase A's step body: annotate-and-install for the three value
kinds, the ordinary step `checkDeclStepC` for everything else.  `i` is
the fold position the record is tagged with.  (The continuations read
the install's result by projection, so that the statements about this
function match it syntactically.) -/
def annotStepC (pins : List NatOpPinSet) (i : Nat) (fe : FEnv)
    (pend : Array PendingCheck) :
    Declaration → CheckCM (FEnv × Array PendingCheck)
  | .defnDecl cv value hint =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then do
      pure (← checkDeclStepC mode pins fe (.defnDecl cv value hint), pend)
    else do
      let r ← annotValueC mode fe cv value
      -- RC linearity: the counter is read BEFORE the push, so that
      -- `fe` reaches `push` unshared (read after it, the push copies
      -- the whole index at every install)
      let vis := fe.visibleBelow
      pure (fe.push (.defnInfo r.1 r.2.2 hint),
        pend.push ⟨⟨.defn, r.1, r.2.2⟩, i, vis⟩)
  | .thmDecl cv value => do
    -- a theorem installs BY STATEMENT: the header's install half
    -- only; the value is recorded raw and never touched here (phase B
    -- annotates it, `checkPending`), so phase A never enters a
    -- theorem's body
    flushC
    let r ← annotConstantValC mode fe cv
    let vis := fe.visibleBelow
    pure (fe.push (.thmInfo r.1),
      pend.push ⟨⟨.thm, r.1, value⟩, i, vis⟩)
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then do
      pure (← checkDeclStepC mode pins fe (.opaqueDecl cv value), pend)
    else do
      let r ← annotValueC mode fe cv value
      let vis := fe.visibleBelow
      pure (fe.push (.axiomInfo r.1),
        pend.push ⟨⟨.opaque, r.1, r.2.2⟩, i, vis⟩)
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
def annotDeclStep (pins : List NatOpPinSet)
    (p : Nat × FEnv × Array PendingCheck) (pd : Declaration) :
    Except (CheckError × Nat) (Nat × FEnv × Array PendingCheck) :=
  if andPinOk pd then
    match annotStepC mode pins p.1 p.2.1 p.2.2 pd {} with
    | .ok ((fe', pend'), _) => .ok (p.1 + 1, fe', pend')
    | .error e => .error (e, p.1)
  else .error (.invalid "`And` must be the standard `And`", p.1)

/-- **Phase A's accepting run**: a chain of accepting `annotDeclStep`s
over the records, from an accumulator to the final one.  A loop builds
it step by step, whatever else it does between the steps.  (No memo
state crosses a step: every record is installed from a fresh one.) -/
inductive InstallRun (pins : List NatOpPinSet) :
    List Declaration → (Nat × FEnv × Array PendingCheck) →
    (Nat × FEnv × Array PendingCheck) → Prop where
  | nil (p : Nat × FEnv × Array PendingCheck) :
      InstallRun pins [] p p
  | cons {pd : Declaration} {ds : List Declaration} {p p₁ p' : Nat × FEnv × Array PendingCheck}
      (h : annotDeclStep mode pins p pd = .ok p₁)
      (rest : InstallRun pins ds p₁ p') :
      InstallRun pins (pd :: ds) p p'

/-- The tagged step's accept is the body's accept at the next position,
from a fresh memo state. -/
theorem annotDeclStep_ok {mode : CheckMode} {pins : List NatOpPinSet}
    {p : Nat × FEnv × Array PendingCheck}
    {pd : Declaration} {q : Nat × FEnv × Array PendingCheck}
    (h : annotDeclStep mode pins p pd = .ok q) :
    ∃ fe' pend' s', q = (p.1 + 1, fe', pend') ∧
      annotStepC mode pins p.1 p.2.1 p.2.2 pd {} = .ok ((fe', pend'), s') := by
  unfold annotDeclStep at h
  split at h
  case isFalse => exact nomatch h
  cases hs : annotStepC mode pins p.1 p.2.1 p.2.2 pd {} with
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
    (hstep : annotDeclStep mode pins p' pd = .ok p₁) :
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
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 pc.vg.cvA.type
  let u ← opSIxC mode fe 0 jsty
  let jv ← if pc.vg.kind = .thm then do
      unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
        throw (.invalid s!"type of theorem {pc.vg.cvA.name} is not a proposition")
      -- a theorem's value arrives raw: its guards and annotation run
      -- here, at the view (`annotValC` — `installValue`'s twin)
      annotValC mode fe pc.vg.cvA pc.vg.jv
    else pure pc.vg.jv
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt pc.vg.cvA.type do
    throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")

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

/-! ## The records' checks, in the type

The driver's check loop carries the checks it has established —
`GroupChecked` of every record below `k`, extended one record at a
time — and these are its three lemmas: a record's check as its
`GroupChecked` fact, the accumulator's extension, and the closing
argument. -/

/-- Record `k`'s check, as its `GroupChecked` fact. -/
theorem groupChecked_of_run {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) {k : Nat}
    (hk : k < e.pend.size) {s' : CState}
    (h : checkPending mode e.fe e.pend[k] {} = .ok ((), s')) :
    GroupChecked mode e k := by
  unfold GroupChecked
  rw [Array.getElem?_eq_getElem hk]
  exact ⟨s', h⟩

/-- Beyond the records, nothing is pending. -/
theorem groupChecked_of_ge {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) {k : Nat}
    (hk : e.pend.size ≤ k) : GroupChecked mode e k := by
  unfold GroupChecked
  rw [Array.getElem?_eq_none hk]
  trivial

/-- The accumulator, one record further. -/
theorem groupChecked_extend {pins : List NatOpPinSet} {ds : List Declaration}
    {e : InstalledEnv mode pins ds} {k : Nat}
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
theorem groupChecked_all {pins : List NatOpPinSet} {ds : List Declaration}
    {e : InstalledEnv mode pins ds}
    (acc : ∀ j, j < e.pend.size → GroupChecked mode e j) : ∀ i, GroupChecked mode e i := by
  intro i
  by_cases hi : i < e.pend.size
  · exact acc i hi
  · exact groupChecked_of_ge mode e (Nat.le_of_not_lt hi)

/-! ## One record's check, as evidence

The driver's check phase — the in-thread loop or a pool of workers —
runs `checkRecord` on every record.  Its result is the record's own
evidence: on an accept the `GroupChecked` fact of that record, on a
failure the error tagged with the record's fold position, the tag
`checkPendingList` gives.  A worker hands back exactly this (a `Nat`
and an erased proof, or the error), so the thread that computed a
check is irrelevant to what it proves, and the results of any number
of workers, in whatever order they finished, are assembled into
`∀ i, GroupChecked mode e i` by `collectChecks` — a walk over the
results in record order, which is also what makes the verdict of a
pool the verdict of the walk `checkPendingList`: the first failing
record in fold order.  Nothing here is `IO`. -/

/-- Record `k`'s check: its `GroupChecked` fact, or the error tagged with
its fold position. -/
def checkRecord {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) (k : Nat)
    (hk : k < e.pend.size) : Except (CheckError × Nat) (PLift (GroupChecked mode e k)) :=
  match h : checkPending mode e.fe e.pend[k] {} with
  | .ok ((), _) => .ok ⟨groupChecked_of_run mode e hk h⟩
  | .error err => .error (err, e.pend[k].pos)

/-- A checked record: its index with its `GroupChecked` fact — a `Nat`
at run time. -/
abbrev CheckedRecord {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) : Type :=
  { k : Nat // GroupChecked mode e k }

/-- A worker's result for one record: the checked record, or the error
tagged with the record's fold position. -/
abbrev RecordResult {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) : Type :=
  Except (CheckError × Nat) (CheckedRecord mode e)

/-- Record `k`'s check as a worker's result. -/
def checkRecordResult {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds) (k : Nat)
    (hk : k < e.pend.size) : RecordResult mode e :=
  match checkRecord mode e k hk with
  | .ok ⟨h⟩ => .ok ⟨k, h⟩
  | .error err => .error err

/-- **The results, assembled in record order.**  Slot `j` of the table
must hold record `j`'s result; the walk carries the facts of the
records below `j` and stops at the first failure — the walk's verdict
is therefore `checkPendingList`'s whatever order the results were
produced in.  A slot that is empty or holds another record's result is
an internal error (a pool that did not do its job), never a verdict on
the input. -/
def collectChecks {pins : List NatOpPinSet} {ds : List Declaration}
    (e : InstalledEnv mode pins ds)
    (tab : Array (Option (RecordResult mode e))) :
    (j : Nat) → (∀ i, i < j → GroupChecked mode e i) →
      Except (CheckError × Nat) (PLift (∀ i, GroupChecked mode e i))
  | j, acc =>
    if hj : j < e.pend.size then
      match tab[j]? with
      | some (some (.ok ⟨k, hk⟩)) =>
        if h : k = j then
          collectChecks e tab (j + 1) (groupChecked_extend mode acc (h ▸ hk))
        else .error (.internal s!"check phase: slot {j} holds record {k}", e.pend[j].pos)
      | some (some (.error err)) => .error err
      | _ => .error (.internal s!"check phase: record {j} was never checked", e.pend[j].pos)
    else
      .ok ⟨groupChecked_all mode
        (fun i hi => acc i (Nat.lt_of_lt_of_le hi (Nat.le_of_not_lt hj)))⟩
  termination_by j => e.pend.size - j

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
  let p ← ds.foldlM (annotDeclStep mode pins) (0, mkFEnv Env.empty, #[])
  checkPendingList mode p.2.1 p.2.2.toList
  pure p.2.1.env

/-- An accepting run is an accepting `foldlM`. -/
theorem InstallRun.foldlM {pins : List NatOpPinSet} {ds : List Declaration}
    {p p' : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p p') :
    ds.foldlM (annotDeclStep mode pins) p = .ok p' := by
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
      ds.foldlM (annotDeclStep mode pins) p = .ok p' →
      InstallRun mode pins ds p p'
  | [], p, p', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .nil p
  | pd :: ds, p, p', h => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind] at h
    cases hstep : annotDeclStep mode pins p pd with
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
  cases hrun : ds.toList.foldlM (annotDeclStep mode pins) (0, mkFEnv Env.empty, #[]) with
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
