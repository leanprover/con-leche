module

public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Cached.StoredInstall

/-!
# Inductive blocks checked in the check phase (tasks #411, #431)

Phase A installs every inductive block **as stored** (`storedInstall`,
task #431: every constant and table read off the block's records,
nothing generated) and records the block's checked
install as a job of the check phase (`BlockCheck`): the checked install
of the block at a view that answers every lookup as the index the block
was installed at does (`Twin`), and the comparison of what it pushes
with what the stored install pushed (`pushesAgree`, pointer-first).  The
block's step in the serial fold's accepting run (`InstallRun`) is then
CONDITIONAL on that job: a driver's install loop carries
`(∀ b ∈ D, b.Ok) → InstallRun …` for the jobs `D` it has recorded, and
the check phase discharges the premise — the same Bool barrier as for
the recorded value checks: a run is accepted only if every job of the
check phase passes.

* `installDeclStep_defer` — where the checked install accepts the block
  at an empty-environment twin of an index and pushes `L` and `Q`
  there, the serial fold's step at the index pushes `L` and `Q`.  From
  the twin lemma (`checkDeclStepC_twin`).
* The view a deferred check runs at: the parallel install's worker
  view at the block's counter (its twin is the serial index by
  `ViewAgrees`, `Twin.ofViewAgrees`; `installStepG_ind`).
* The check phase's jobs (`Job`, `jobOrder`, `runJob`, `collectJobs`):
  the recorded value checks and the block checks in fold order, each
  job's verdict with its evidence, assembled into every record checked
  and every block job passed.

Nothing here is `IO`.
-/

@[expose] public section

namespace ConLeche.Cached

open ConLeche

/-! ## The deferred check of a block -/

/-- **A deferred block check**: the block, the view its checked install
runs at (on the parallel install, the worker view at the block's
counter, `workerView`), the block's fold position (its error tag), and
what the stored install pushed: the constants `L` and the tables `Q`,
in install order. -/
structure BlockCheck where
  view : FEnv
  block : List ConstantInfo
  nP : Nat
  pos : Nat
  L : List ConstantInfo
  Q : List ProjTable

/-- The block's name (its first constant's), for the messages. -/
def BlockCheck.name (b : BlockCheck) : Name :=
  match b.block with
  | ci :: _ => ci.name
  | [] => .anonymous

/-- **The checked install pushed `L` and `Q`** onto a view whose own
environment is empty: its constants and tables, in install order,
compared pointer-first. -/
def pushesAgree (W' : FEnv) (L : List ConstantInfo) (Q : List ProjTable) : Bool :=
  listBeqBy ConstantInfo.beqP W'.env.consts.reverse L &&
    listBeqBy ProjTable.beqP W'.env.tables.reverse Q

/-- **The block's job**: its checked install at the view, from a fresh
memo state, and the comparison of its pushes with the stored install's.
A difference is an internal error naming the block: the stored reading
(`storedInstall`) is not the checked install's, a defect of the reader,
not of the stream. -/
def blockCheck (mode : CheckMode) (pins : List NatOpPinSet) (b : BlockCheck) :
    Except CheckError Unit :=
  match checkDeclStepC mode pins b.view (.indDecl b.block b.nP) {} with
  | .ok (W', _) =>
    if pushesAgree W' b.L b.Q then .ok ()
    else .error (.internal s!"inductive block {b.name}: the stored install's constants or \
      tables are not the checked install's")
  | .error e => .error e

/-- The block check passed. -/
def BlockCheck.Ok (mode : CheckMode) (pins : List NatOpPinSet) (b : BlockCheck) : Prop :=
  blockCheck mode pins b = .ok ()

theorem blockCheck_ok {mode : CheckMode} {pins : List NatOpPinSet} {b : BlockCheck}
    (h : b.Ok mode pins) :
    ∃ W' s, checkDeclStepC mode pins b.view (.indDecl b.block b.nP) {} = .ok (W', s) ∧
      W'.env.consts.reverse = b.L ∧ W'.env.tables.reverse = b.Q := by
  unfold BlockCheck.Ok blockCheck at h
  split at h
  · rename_i W' s hc
    split at h
    · rename_i ha
      simp only [pushesAgree, Bool.and_eq_true] at ha
      exact ⟨W', s, hc, eq_of_listBeqBy (fun _ _ => ConstantInfo.eq_of_beqP) ha.1,
        eq_of_listBeqBy (fun _ _ => ProjTable.eq_of_beqP) ha.2⟩
    · exact nomatch h
  · exact nomatch h

/-- **An inductive block**, with its parts: every one is installed as
stored (`storedInstall`, task #431 cont. 5); every other record is
installed by its ordinary step. -/
def deferredBlock? : Declaration → Option (List ConstantInfo × Nat)
  | .indDecl block nP => some (block, nP)
  | _ => none

theorem deferredBlock?_some {pd : Declaration} {block : List ConstantInfo} {nP : Nat}
    (h : deferredBlock? pd = some (block, nP)) : pd = .indDecl block nP := by
  cases pd <;> simp only [deferredBlock?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

/-- **A record's install at a worker view, an inductive block as
stored**: the ordinary `installStep` but for an inductive block, whose
constants and tables are the stored install's — whatever the block, so
its verdict is always its job's. -/
def installStepG (mode : CheckMode) (pins : List NatOpPinSet) (W : FEnv) (pd : Declaration) :
    Except CheckError (List ConstantInfo × List ProjTable × Option ValueGroup) :=
  match deferredBlock? pd with
  | some (block, nP) =>
    let r := storedInstall mode W block nP
    .ok (r.1, r.2, none)
  | none => installStep mode pins W pd

theorem installStepG_none {mode : CheckMode} {pins : List NatOpPinSet} {pd : Declaration}
    (h : deferredBlock? pd = none) (W : FEnv) :
    installStepG mode pins W pd = installStep mode pins W pd := by
  unfold installStepG; rw [h]

/-! ## The step, conditional on its block check -/

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-- **The serial fold's step on a deferred block**: where the checked
install accepts the block at a twin `W` of `fe` whose own environment
is empty, pushing `L` and `Q`, the fold's step at `fe` pushes `L` and
`Q` and records nothing. -/
theorem installDeclStep_defer {fe W : FEnv} (ht : Twin fe W) (hW : W.env = ⟨[], []⟩) {i : Nat}
    {pend : Array PendingCheck} {block : List ConstantInfo} {nP : Nat}
    {L : List ConstantInfo} {Q : List ProjTable}
    (hand : andPinOk (.indDecl block nP) = true)
    (hok : ∃ W' s, checkDeclStepC mode pins W (.indDecl block nP) {} = .ok (W', s) ∧
      W'.env.consts.reverse = L ∧ W'.env.tables.reverse = Q) :
    installDeclStep mode pins (i, fe, pend) (.indDecl block nP) =
      .ok (i + 1, FEnv.pushDelta L Q fe, pend) := by
  obtain ⟨W', s, hW', hL, hQ⟩ := hok
  rcases checkDeclStepC_twin pins ht (.indDecl block nP) {} with
    ⟨e, -, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, L', Q', rfl, rfl⟩
  · rw [h₂] at hW'; exact nomatch hW'
  · rw [h₂] at hW'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hW')
    rw [pushDelta_env, hW] at hL hQ
    simp only [List.append_nil, List.reverse_reverse] at hL hQ
    subst hL hQ
    unfold installDeclStep
    simp only [hand, ↓reduceIte]
    show (match (checkDeclStepC mode pins fe (.indDecl block nP) {}).bind
        (fun v => (pure (v.1, pend) : CheckCM _) v.2) with
      | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
      | .error e => .error (e, i)) = _
    rw [h₁]
    rfl

/-- **A block installed as stored at a worker view**: no value check,
and the serial fold's step pushes what it pushed, conditional on the
block's checked install at the same view pushing it too. -/
theorem installStepG_ind {B : BaseIdx} {S : Slots} {fe : FEnv} (hag : ViewAgrees B S fe)
    (hidx : IdxBelow fe) {i : Nat} {pend : Array PendingCheck} {pd : Declaration}
    {block : List ConstantInfo} {nP : Nat}
    {L : List ConstantInfo} {Q : List ProjTable} {vg? : Option ValueGroup}
    (hd : deferredBlock? pd = some (block, nP))
    (hand : andPinOk (.indDecl block nP) = true)
    (h : installStepG mode pins (workerView B S fe.visibleBelow) pd = .ok (L, Q, vg?)) :
    vg? = none ∧
      ((∃ W' s, checkDeclStepC mode pins (workerView B S fe.visibleBelow)
          (.indDecl block nP) {} = .ok (W', s) ∧
          W'.env.consts.reverse = L ∧ W'.env.tables.reverse = Q) →
        installDeclStep mode pins (i, fe, pend) (.indDecl block nP) =
          .ok (i + 1, FEnv.pushDelta L Q fe, pend)) := by
  have ht := Twin.ofViewAgrees hag hidx
  unfold installStepG at h
  rw [hd] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, fun hok => installDeclStep_defer ht rfl hand hok⟩

/-- **An accepting install with its block checks deferred**: the final
accumulator, the deferred checks, and the serial fold's accepting run
once every deferred check passes. -/
structure DeferredRun (mode : CheckMode) (pins : List NatOpPinSet) (ds : List Declaration)
    (p₀ : Nat × FEnv × Array PendingCheck) where
  p : Nat × FEnv × Array PendingCheck
  D : Array BlockCheck
  run : (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins ds p₀ p

/-- The run extended by a real step. -/
theorem deferRun_snoc {ds : List Declaration} {p₀ p p₁ : Nat × FEnv × Array PendingCheck}
    {D : Array BlockCheck} (hrun : (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins ds p₀ p)
    {pd : Declaration} (h : installDeclStep mode pins p pd = .ok p₁) :
    (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins (ds ++ [pd]) p₀ p₁ :=
  fun hD => (hrun hD).snoc mode h

/-- The run extended by a step conditional on one more deferred check. -/
theorem deferRun_push {ds : List Declaration} {p₀ p p₁ : Nat × FEnv × Array PendingCheck}
    {D : Array BlockCheck} (hrun : (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins ds p₀ p)
    {pd : Declaration} {b : BlockCheck} (h : b.Ok mode pins → installDeclStep mode pins p pd = .ok p₁) :
    (∀ b' ∈ (D.push b).toList, b'.Ok mode pins) → InstallRun mode pins (ds ++ [pd]) p₀ p₁ :=
  fun hD => (hrun fun b' hb' => hD b' (by simp [hb'])).snoc mode
    (h (hD b (by simp)))

/-- The first failing deferred check, in order (the verdict when the
install fails after it: the serial fold would have failed there). -/
def blockFailure (mode : CheckMode) (pins : List NatOpPinSet) (D : Array BlockCheck) :
    Option (CheckError × Nat) :=
  D.findSome? fun b => match blockCheck mode pins b with
    | .error e => some (e, b.pos)
    | .ok _ => none

/-! ## The check phase's jobs

The check phase runs two kinds of job: a recorded value check
(`checkPending`, the record's `GroupChecked` fact) and a deferred block
check (`blockCheck`, the block's `BlockCheck.Ok`).  The jobs are put in
FOLD ORDER (`jobOrder`, the two position-sorted arrays merged), run by
any number of workers in any order, and assembled by a walk in job
order that stops at the first failure (`collectJobs`): the verdict is
the first failing job in fold order, whatever the workers' timing. -/

section Jobs

variable (mode : CheckMode) (pins : List NatOpPinSet)

/-- Record `i`'s value check passed (vacuous beyond the records). -/
def PendOk (fe : FEnv) (pend : Array PendingCheck) (i : Nat) : Prop :=
  ∀ h : i < pend.size, ∃ s, checkPending mode fe pend[i] {} = .ok ((), s)

/-- A job: a recorded value check (`false`) or a deferred block check
(`true`), by its index in its array. -/
abbrev Job := Bool × Nat

/-- A job passed. -/
def JobOk (fe : FEnv) (pend : Array PendingCheck) (D : Array BlockCheck) (j : Job) : Prop :=
  if j.1 then ∀ h : j.2 < D.size, D[j.2].Ok mode pins else PendOk mode fe pend j.2

/-- A job's result: the job with its evidence, or the error tagged with
its fold position. -/
abbrev JobResult (fe : FEnv) (pend : Array PendingCheck) (D : Array BlockCheck) : Type :=
  Except (CheckError × Nat) { j : Job // JobOk mode pins fe pend D j }

/-- **Run a job.** -/
def runJob (fe : FEnv) (pend : Array PendingCheck) (D : Array BlockCheck) (j : Job) :
    JobResult mode pins fe pend D :=
  if hb : j.1 = true then
    if h : j.2 < D.size then
      match hc : blockCheck mode pins D[j.2] with
      | .ok () => .ok ⟨j, by
          unfold JobOk
          rw [ite_eq_left hb]
          intro _
          exact hc⟩
      | .error e => .error (e, D[j.2].pos)
    else .error (.internal "check phase: no such block check", 0)
  else
    if h : j.2 < pend.size then
      match hc : checkPending mode fe pend[j.2] {} with
      | .ok ((), s) => .ok ⟨j, by
          unfold JobOk
          rw [ite_eq_right hb]
          intro _
          exact ⟨s, hc⟩⟩
      | .error e => .error (e, pend[j.2].pos)
    else .error (.internal "check phase: no such record", 0)

/-- **The jobs in fold order**: the recorded checks and the block checks,
each array sorted by position, merged (a block before a record at a
larger position). -/
def jobOrder (pend : Array PendingCheck) (D : Array BlockCheck) : Array Job :=
  go 0 0 (Array.mkEmpty (pend.size + D.size))
where
  go (a b : Nat) (acc : Array Job) : Array Job :=
    if ha : a < pend.size then
      if hb : b < D.size then
        if D[b].pos < pend[a].pos then go a (b + 1) (acc.push (true, b))
        else go (a + 1) b (acc.push (false, a))
      else go (a + 1) b (acc.push (false, a))
    else if b < D.size then go a (b + 1) (acc.push (true, b))
    else acc
  termination_by (pend.size - a) + (D.size - b)

/-- The facts the check phase establishes: every record checked, every
block check passed. -/
def AllOk (fe : FEnv) (pend : Array PendingCheck) (D : Array BlockCheck) : Prop :=
  (∀ i, PendOk mode fe pend i) ∧ ∀ b ∈ D.toList, b.Ok mode pins

/-- **The results, assembled in job order.**  Slot `t` of the table must
hold the result of the next record or the next block check (whichever
the walk is at); the walk carries the facts so far and stops at the
first failure.  A slot that is empty or out of place is an internal
error (a pool that did not do its job), never a verdict. -/
def collectJobs (fe : FEnv) (pend : Array PendingCheck) (D : Array BlockCheck)
    (tab : Array (Option (JobResult mode pins fe pend D))) :
    (t a b : Nat) → (∀ i, i < a → PendOk mode fe pend i) →
      (∀ i, i < b → ∀ h : i < D.size, D[i].Ok mode pins) →
      Except (CheckError × Nat) (PLift (AllOk mode pins fe pend D))
  | t, a, b, ha, hb =>
    if ht : t < tab.size then
      match tab[t] with
      | some (.ok ⟨j, hj⟩) =>
        if hj₁ : j = (false, a) then
          collectJobs fe pend D tab (t + 1) (a + 1) b (fun i hi => by
            by_cases hia : i < a
            · exact ha i hia
            · have : i = a := by omega
              subst this hj₁
              unfold JobOk at hj
              simpa using hj) hb
        else if hj₂ : j = (true, b) then
          collectJobs fe pend D tab (t + 1) a (b + 1) ha (fun i hi => by
            by_cases hib : i < b
            · exact hb i hib
            · have : i = b := by omega
              subst this hj₂
              unfold JobOk at hj
              simpa using hj)
        else .error (.internal s!"check phase: job {t} out of place", 0)
      | some (.error e) => .error e
      | none => .error (.internal s!"check phase: job {t} was never run", 0)
    else if hab : pend.size ≤ a ∧ D.size ≤ b then
      .ok ⟨⟨fun i => if hi : i < a then ha i hi else fun h => absurd h (by omega),
        fun bc hbc => by
          obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hbc)
          exact hb i (by omega) hi⟩⟩
    else .error (.internal "check phase: jobs missing", 0)
  termination_by t => tab.size - t

/-- Every record checked, as the installed environment's `GroupChecked`. -/
theorem groupChecked_of_pendOk {ds : List Declaration} {e : InstalledEnv mode pins ds}
    (h : ∀ i, PendOk mode e.fe e.pend i) : ∀ i, GroupChecked mode e i := by
  intro i
  unfold GroupChecked
  by_cases hi : i < e.pend.size
  · rw [Array.getElem?_eq_getElem hi]
    exact h i hi
  · rw [Array.getElem?_eq_none (by omega)]
    trivial

end Jobs

end ConLeche.Cached
