module

public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Verify.Cached.InstallPushes

/-!
# Every record's checked step in the check phase

Phase A installs every record from the record alone.  A definition, a
theorem or an opaque (a *value record*) is guarded and pushed with its
check recorded (`valueStep`, `PendingCheck`).  Every other record — an
inductive block, an axiom, a pinned `Nat` operation, a `reduce*` opaque,
a basis or quotient record (`deferredDecl`) — is pushed as the record
says (`declConstants`, `declTables`) and its checked step recorded as a
job of the check phase (`DeferredCheck`): the checked step at a view that
answers every lookup as the index the record was installed at does
(`Twin`).  What the checked step pushes is what the record says at every
view (`checkDeclStepC_pushes`), so the job's verdict is all that matters
of it.  The record's step in the serial fold's accepting run
(`InstallRun`) is then CONDITIONAL on that job: a driver's install loop
carries `(∀ b ∈ D, b.Ok) → InstallRun …` for the jobs `D` it has recorded,
and the check phase discharges the premise — the same Bool barrier as
for the recorded value checks: a run is accepted only if every job of
the check phase passes.

* `installDeclStep_defer` — where the checked step accepts the record
  at an empty-environment twin of an index, the serial fold's step at the
  index pushes what the record installs.  From the twin lemma
  (`checkDeclStepC_twin`).
* The view a deferred check runs at: the install's worker
  view at the record's counter (its twin is the serial index by
  `ViewAgrees`, `Twin.ofViewAgrees`; `installStepG_deferred`).  So a
  certificate is checked over exactly the declarations before its
  operation in fold order: `Frontend/NatOpGround.lean`'s reordering is
  what puts its ground there.
* The check phase's jobs (`Job`, `jobOrder`, `runJob`, `collectJobs`):
  the recorded value checks and the deferred checks in fold order, each
  job's verdict with its evidence, assembled into every record checked
  and every deferred check passed.

**What a job may observe of an earlier record that has not passed yet.**
Nothing the theorem reads: a later job sees a pinned operation pushed
before its certificate job has run, and may fire its literal fast path.
The accepted run needs every job, so a later job's verdict matters only
if every earlier one passed, and then the environment it ran at is the
serial fold's (the same as for a value record's unchecked value).
A wrong firing can therefore change nothing but which failure is
computed last: the walk in fold order (`collectJobs`) reports the
earliest.  A later job that does not terminate over a wrong operation
keeps the pool from draining, as over a wrong definition: no verdict,
never an accept.

Nothing here is `IO`.
-/

@[expose] public section

namespace ConLeche.Cached

open ConLeche

/-! ## The deferred check of a record -/

/-- **A deferred check**: the record, the view its checked step runs at
(the install's worker view at the record's counter, `workerView`), and the
record's fold position (its error tag). -/
structure DeferredCheck where
  view : FEnv
  pd : Declaration
  pos : Nat

/-- The record's label, for the messages. -/
def DeferredCheck.label (b : DeferredCheck) : String :=
  declCLabel b.pd

/-- **The record's job**: its checked step at the view, from a fresh
memo state. -/
def deferredCheck (mode : CheckMode) (pins : List NatOpPinSet) (b : DeferredCheck) :
    Except CheckError Unit :=
  match checkDeclStepC mode pins b.view b.pd {} with
  | .ok _ => .ok ()
  | .error e => .error e

/-- The deferred check passed. -/
def DeferredCheck.Ok (mode : CheckMode) (pins : List NatOpPinSet) (b : DeferredCheck) : Prop :=
  deferredCheck mode pins b = .ok ()

theorem deferredCheck_ok {mode : CheckMode} {pins : List NatOpPinSet} {b : DeferredCheck}
    (h : b.Ok mode pins) : ∃ W' s, checkDeclStepC mode pins b.view b.pd {} = .ok (W', s) := by
  unfold DeferredCheck.Ok deferredCheck at h
  split at h
  · rename_i r hc
    exact ⟨r.1, r.2, hc⟩
  · exact nomatch h

/-- **Is the record's check a job?**  Every record but a value record
(`valueStep`). -/
def deferredDecl : Declaration → Bool
  | .defnDecl cv _ _ => natOpNames.contains cv.name || natDivModNames.contains cv.name
  | .thmDecl _ _ => false
  | .opaqueDecl cv _ => reduceOpNames.contains cv.name
  | _ => true

theorem valueStep_of_deferred {pd : Declaration} (h : deferredDecl pd = true) (W : FEnv) :
    valueStep W pd = none := by
  cases pd with
  | defnDecl cv value hint =>
    have h' : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = true := h
    simp only [valueStep, h', ↓reduceIte]
  | thmDecl cv value => exact nomatch h
  | opaqueDecl cv value =>
    have h' : reduceOpNames.contains cv.name = true := h
    simp only [valueStep, h', ↓reduceIte]
  | axiomDecl _ => rfl
  | quotDecl _ _ => rfl
  | indDecl _ _ => rfl

theorem valueStep_of_not_deferred {pd : Declaration} (h : deferredDecl pd = false) (W : FEnv) :
    valueStep W pd ≠ none := by
  cases pd with
  | defnDecl cv value hint =>
    have h' : ¬(natOpNames.contains cv.name || natDivModNames.contains cv.name) = true := by
      rw [show (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false from h]
      exact Bool.false_ne_true
    unfold valueStep
    dsimp only
    rw [ite_eq_right h']
    exact nofun
  | thmDecl cv value => exact nofun
  | opaqueDecl cv value =>
    have h' : ¬reduceOpNames.contains cv.name = true := by
      rw [show reduceOpNames.contains cv.name = false from h]
      exact Bool.false_ne_true
    unfold valueStep
    dsimp only
    rw [ite_eq_right h']
    exact nofun
  | axiomDecl _ => exact nomatch h
  | quotDecl _ _ => exact nomatch h
  | indDecl _ _ => exact nomatch h

/-- **A record's install at a worker view**: a value record guarded, with
its check recorded; any other record as it says, so its verdict is always
its job's. -/
def installStepG (W : FEnv) (pd : Declaration) :
    Except CheckError (List ConstantInfo × List ProjTable × Option ValueGroup) :=
  match valueStep W pd with
  | some (.ok (ci, vg)) => .ok ([ci], [], some vg)
  | some (.error e) => .error e
  | none => .ok (declConstants pd, declTables pd, none)

/-! ## The step, conditional on its deferred check -/

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-- **The serial fold's step on a deferred record**: where the checked
step accepts the record at a twin `W` of `fe`, the fold's step at `fe`
pushes what the record installs and records nothing. -/
theorem installDeclStep_defer {fe W : FEnv} (ht : Twin fe W) {i : Nat}
    {pend : Array PendingCheck} {pd : Declaration}
    (hd : deferredDecl pd = true) (hand : andPinOk pd = true)
    (hok : ∃ W' s, checkDeclStepC mode pins W pd {} = .ok (W', s)) :
    installDeclStep mode pins (i, fe, pend) pd =
      .ok (i + 1, FEnv.pushDelta (declConstants pd) (declTables pd) fe, pend) := by
  obtain ⟨W', s, hW'⟩ := hok
  have hnone := valueStep_of_deferred (pd := pd) hd W
  rcases checkDeclStepC_twin pins ht pd {} with
    ⟨e, -, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, L', Q', rfl, rfl⟩
  · rw [h₂] at hW'; exact nomatch hW'
  · unfold installDeclStep installStepC
    simp only [hand, ↓reduceIte, installGuards_of_valueStep_none hnone,
      valueGroup?_of_valueStep_none hnone, checkDeclOnly, bind, StateT.bind, pure, StateT.pure,
      h₁, pushPending, Except.bind, Except.pure]

/-- **A deferred record installed at a worker view**: no value check,
and the serial fold's step pushes what it pushed, conditional on the
record's checked step at the same view accepting. -/
theorem installStepG_deferred {B : BaseIdx} {S : Slots} {fe : FEnv} (hag : ViewAgrees B S fe)
    (hidx : IdxBelow fe) {i : Nat} {pend : Array PendingCheck} {pd : Declaration}
    {L : List ConstantInfo} {Q : List ProjTable} {vg? : Option ValueGroup}
    (hd : deferredDecl pd = true)
    (hand : andPinOk pd = true)
    (h : installStepG (workerView B S fe.visibleBelow) pd = .ok (L, Q, vg?)) :
    vg? = none ∧
      ((∃ W' s, checkDeclStepC mode pins (workerView B S fe.visibleBelow) pd {} = .ok (W', s)) →
        installDeclStep mode pins (i, fe, pend) pd =
          .ok (i + 1, FEnv.pushDelta L Q fe, pend)) := by
  have ht := Twin.ofViewAgrees hag hidx
  unfold installStepG at h
  rw [valueStep_of_deferred hd] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, fun hok => installDeclStep_defer ht hd hand hok⟩

/-- **The commit step of a value record**: installed at the view whose
lookups are the serial index's, it is the serial fold's step — the same
constant pushed, the same pending check. -/
theorem installStepG_commit {B : BaseIdx} {S : Slots} {i : Nat}
    {fe : FEnv} {pend : Array PendingCheck} {pd : Declaration} {L : List ConstantInfo}
    {Q : List ProjTable} {vg? : Option ValueGroup} (hag : ViewAgrees B S fe)
    (hd : deferredDecl pd = false) (hand : andPinOk pd = true)
    (h : installStepG (workerView B S fe.visibleBelow) pd = .ok (L, Q, vg?)) :
    installDeclStep mode pins (i, fe, pend) pd =
      .ok (i + 1, FEnv.pushDelta L Q fe, pushPending pend i fe.visibleBelow vg?) := by
  unfold installStepG at h
  split at h
  · rename_i ci vg hv
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact valueStep_commit hag hand hv
  · exact nomatch h
  · rename_i hv
    exact absurd hv (valueStep_of_not_deferred hd _)

/-- A failing install (a value record's guards) is the serial step's
failure. -/
theorem installStepG_commit_error {B : BaseIdx} {S : Slots} {i : Nat}
    {fe : FEnv} {pend : Array PendingCheck} {pd : Declaration} {e : CheckError}
    (hag : ViewAgrees B S fe) (hand : andPinOk pd = true)
    (h : installStepG (workerView B S fe.visibleBelow) pd = .error e) :
    installDeclStep mode pins (i, fe, pend) pd = .error (e, i) := by
  unfold installStepG at h
  split at h
  · exact nomatch h
  · rename_i e' hv
    cases h
    exact valueStep_commit_error hag hand hv
  · exact nomatch h

/-- **An accepting install with its checks deferred**: the final
accumulator, the deferred checks, and the serial fold's accepting run
once every deferred check passes. -/
structure DeferredRun (mode : CheckMode) (pins : List NatOpPinSet) (ds : List Declaration)
    (p₀ : Nat × FEnv × Array PendingCheck) where
  p : Nat × FEnv × Array PendingCheck
  D : Array DeferredCheck
  run : (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins ds p₀ p

/-- The run extended by a real step. -/
theorem deferRun_snoc {ds : List Declaration} {p₀ p p₁ : Nat × FEnv × Array PendingCheck}
    {D : Array DeferredCheck} (hrun : (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins ds p₀ p)
    {pd : Declaration} (h : installDeclStep mode pins p pd = .ok p₁) :
    (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins (ds ++ [pd]) p₀ p₁ :=
  fun hD => (hrun hD).snoc mode h

/-- The run extended by a step conditional on one more deferred check. -/
theorem deferRun_push {ds : List Declaration} {p₀ p p₁ : Nat × FEnv × Array PendingCheck}
    {D : Array DeferredCheck} (hrun : (∀ b ∈ D.toList, b.Ok mode pins) → InstallRun mode pins ds p₀ p)
    {pd : Declaration} {b : DeferredCheck} (h : b.Ok mode pins → installDeclStep mode pins p pd = .ok p₁) :
    (∀ b' ∈ (D.push b).toList, b'.Ok mode pins) → InstallRun mode pins (ds ++ [pd]) p₀ p₁ :=
  fun hD => (hrun fun b' hb' => hD b' (by simp [hb'])).snoc mode
    (h (hD b (by simp)))

/-- The first failing deferred check, in order (the verdict when the
install fails after it: the serial fold would have failed there). -/
def deferredFailure (mode : CheckMode) (pins : List NatOpPinSet) (D : Array DeferredCheck) :
    Option (CheckError × Nat) :=
  D.findSome? fun b => match deferredCheck mode pins b with
    | .error e => some (e, b.pos)
    | .ok _ => none

/-! ## The check phase's jobs

The check phase runs two kinds of job: a recorded value check
(`checkPending`, the record's `GroupChecked` fact) and a deferred check
(`deferredCheck`, the record's `DeferredCheck.Ok`).  The jobs are put in
FOLD ORDER (`jobOrder`, the two position-sorted arrays merged), run by
any number of workers in any order, and assembled by a walk in job
order that stops at the first failure (`collectJobs`): the verdict is
the first failing job in fold order, whatever the workers' timing. -/

section Jobs

variable (mode : CheckMode) (pins : List NatOpPinSet)

/-- Record `i`'s value check passed (vacuous beyond the records). -/
def PendOk (fe : FEnv) (pend : Array PendingCheck) (i : Nat) : Prop :=
  ∀ h : i < pend.size, ∃ s, checkPending mode fe pend[i] {} = .ok ((), s)

/-- A job: a recorded value check (`false`) or a deferred check
(`true`), by its index in its array. -/
abbrev Job := Bool × Nat

/-- A job passed. -/
def JobOk (fe : FEnv) (pend : Array PendingCheck) (D : Array DeferredCheck) (j : Job) : Prop :=
  if j.1 then ∀ h : j.2 < D.size, D[j.2].Ok mode pins else PendOk mode fe pend j.2

/-- A job's result: the job with its evidence, or the error tagged with
its fold position. -/
abbrev JobResult (fe : FEnv) (pend : Array PendingCheck) (D : Array DeferredCheck) : Type :=
  Except (CheckError × Nat) { j : Job // JobOk mode pins fe pend D j }

/-- **Run a job.** -/
def runJob (fe : FEnv) (pend : Array PendingCheck) (D : Array DeferredCheck) (j : Job) :
    JobResult mode pins fe pend D :=
  if hb : j.1 = true then
    if h : j.2 < D.size then
      match hc : deferredCheck mode pins D[j.2] with
      | .ok () => .ok ⟨j, by
          unfold JobOk
          rw [ite_eq_left hb]
          intro _
          exact hc⟩
      | .error e => .error (e, D[j.2].pos)
    else .error (.internal "check phase: no such deferred check", 0)
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

/-- **The jobs in fold order**: the recorded checks and the deferred checks,
each array sorted by position, merged (a deferred check before a recorded
one at a larger position). -/
def jobOrder (pend : Array PendingCheck) (D : Array DeferredCheck) : Array Job :=
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
deferred check passed. -/
def AllOk (fe : FEnv) (pend : Array PendingCheck) (D : Array DeferredCheck) : Prop :=
  (∀ i, PendOk mode fe pend i) ∧ ∀ b ∈ D.toList, b.Ok mode pins

/-- **The results, assembled in job order.**  Slot `t` of the table must
hold the result of the next record or the next deferred check (whichever
the walk is at); the walk carries the facts so far and stops at the
first failure.  A slot that is empty or out of place is an internal
error (a pool that did not do its job), never a verdict. -/
def collectJobs (fe : FEnv) (pend : Array PendingCheck) (D : Array DeferredCheck)
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
