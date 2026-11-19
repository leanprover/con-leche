module

public import ConLeche.Verify.Driver.CompareModule
public import ConLeche.Verify.Frontend.Olean.Local
public import ConLeche.Verify.Driver.Graph

/-!
# The challenge's side of a compared modular run is local to the trusted directories (task #608)

A compared modular run with a trusted path reads the challenge's closure through the trusted
directories alone (`CmpReq.chalRoots`): every worker of a module of that closure, and the compare
worker's read of the challenge's files and of its own view.  On two snapshots that agree on every
path the reader can form under those directories (`FS.AgreeUnder`, #607's
`ConLeche/Verify/Frontend/Olean/Local.lean`), the reads there have the same outcomes
(`OleanReads.Within.local`: refinement across the two snapshots, `ModelIO.Within`, from #607's
locality of the three reads).  So:

* `WorkerFacts.local`: what an accepted worker read and checked on one snapshot it reads and
  checks alike on the other;
* `CmpFacts.chal_local`: the challenge's records and its own view, alike;
* `HdrClosure.trims`: the challenge's closure through the trusted path is in the run's closure.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

theorem readPartNames_local {dirs : List System.FilePath} {R : Roots} (hR : RootsIn dirs R)
    (x : Name × OLeanLevel) :
    (readPartNames R x : ModelIO (Except CheckError NamePositions)).LocalTo
      (FS.AgreeUnder dirs) (fun _ => True) := by
  simp only [readPartNames]
  refine (findModule_local hR x.1).bind fun y hy => ?_
  split
  · exact ModelIO.localTo_pure_true
  · simp only [readPartNamesAt]
    refine (readFilesAt_local (hy _ rfl) _ _).bind fun _ _ => ?_
    split <;> exact ModelIO.localTo_pure_true

/-- **The reads through a lookup inside the directories, across two snapshots that agree under
them**: each read's outcomes on the first are outcomes on the second. -/
theorem OleanReads.Within.local {dirs : List System.FilePath} {R : Roots} (hR : RootsIn dirs R)
    {fs₁ fs₂ : FS} (h : FS.AgreeUnder dirs fs₁ fs₂) :
    OleanReads.Within fs₁ fs₂ (.ofPath R) R :=
  ⟨fun m => .of_same (moduleImports_within fs₁ R m) ((moduleImports_local hR m).1 _ _ h),
    fun m l => .of_same (readFiles_within fs₁ R m l) ((readFiles_local hR m l).1 _ _ h),
    fun x => .of_same (readPartNames_within fs₁ R x) ((readPartNames_local hR x).1 _ _ h)⟩

theorem readFiles_canGive_local {dirs : List System.FilePath} {R : Roots} (hR : RootsIn dirs R)
    {fs₁ fs₂ : FS} (h : FS.AgreeUnder dirs fs₁ fs₂) {m : Name} {level : OLeanLevel}
    {f : ModFiles} (hf : ModelIO.CanGive (readFiles R m level) fs₁ (.ok f)) :
    ModelIO.CanGive (readFiles R m level) fs₂ (.ok f) := by
  obtain ⟨hs, hs', hf⟩ := hf
  exact ⟨hs, hs', by rw [← (readFiles_local hR m level).1 _ _ h]; exact hf⟩

/-- **An accepted worker's facts, through a lookup inside the directories, hold on every snapshot
that agrees under them.** -/
theorem WorkerFacts.local {dirs : List System.FilePath} {R : Roots} (hR : RootsIn dirs R)
    {fs₁ fs₂ : FS} (h : FS.AgreeUnder dirs fs₁ fs₂) {m : Name} {jobs : Nat} {w : WorkerRead}
    {x : Array ImportRec} (hw : WorkerFacts R fs₁ m jobs w x) : WorkerFacts R fs₂ m jobs w x := by
  have hrd := OleanReads.Within.local hR h
  obtain ⟨f, hf, hh⟩ := hw.home
  refine ⟨⟨f, readFiles_canGive_local hR h hf, hh⟩,
    (workerReads_within hrd m jobs x).canGive hw.reads, hw.emitted,
    (reach_within hrd m _ _ _).canGive hw.reach, hw.nodup, hw.own,
    hw.values.of_files fun _ _ hf => readFiles_canGive_local hR h hf⟩

/-- **The challenge's side of an accepted compare worker** (its files and its own view, read
through a lookup inside the directories) **is the same on every snapshot that agrees under
them.** -/
theorem CmpFacts.chal_local {dirs : List System.FilePath} {spC sp : Roots}
    (hR : RootsIn dirs spC) {fs₁ fs₂ : FS} (h : FS.AgreeUnder dirs fs₁ fs₂) {C S : Name}
    {jobs : Nat} {c : CmpModuleRead} (hc : CmpFacts spC sp fs₁ C S jobs c) :
    (∃ f, ModelIO.CanGive (readFiles spC C .private) fs₂ (.ok f) ∧
      homeOf C f = .ok (c.w.home, c.w.expo)) ∧
    ModelIO.CanGive (workerReads (.ofPath spC) C jobs) fs₂ (.ok c.view) := by
  obtain ⟨f, hf, hh⟩ := hc.home
  exact ⟨⟨f, readFiles_canGive_local hR h hf, hh⟩,
    (workerReads_within (OleanReads.Within.local hR h) C jobs #[]).canGive hc.view⟩

/-- **A module of a closure through a trimmed lookup is one through the full one.** -/
theorem Graph.HdrClosure.trims {a L : Roots} (ha : a.Trims L) {fs : FS} {roots : List Name}
    {m : Name} (h : Graph.HdrClosure a fs roots m) : Graph.HdrClosure L fs roots m := by
  induction h with
  | root hr => exact .root hr
  | step _ hc hi ih => exact .step ih (moduleImports_trims ha hc) hi

end ConLeche.Driver
