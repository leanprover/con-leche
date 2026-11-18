module

public import ConLeche.Verify.Driver.Worker
import ConLeche.Verify.Driver.Reach

/-!
# The compare worker, in the model (task #608)

What an exit 0 of the compare worker (`checkCmpModuleG`, `ConLeche/Driver/CompareModule.lean`)
establishes on a snapshot, for a challenge `C` and its solution `S` (`CmpFacts`):

* the worker's facts (`WorkerFacts` at the imports `#[import all S]`): `C`'s home read and checked,
  the reads at `C`'s header with the solution added, `C`'s records the emission of its loaded
  constants, the reach from `cmpRoots` with no own name, its names distinct, no record to check;
* the reads at `C`'s own header (`view`): `C`'s own view;
* the homes (`imported`): every name `C`'s records read that `C` imports is, in the context, of
  the module `C`'s own view loads it from first;
* the comparison (`cmp`, `CmpAt`): every record of `C` meets the context's record of its key.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean ConLeche.Cached

/-- **A challenge record meets the context's record of its key** (`cmpCtxRecord`, whatever kind
the home's private part names). -/
@[expose] def CmpAt (uses : Declaration → Array Name) (r : Reach) (owner : Std.HashMap Name Nat)
    (d : Declaration) : Prop :=
  ∃ k, owner[recKey d]? = some k ∧ ∃ kindS f,
    cmpCtxRecord uses d (r.ctx.getD k default) (r.homes.getD k .anonymous) kindS = .ok f

/-- **What an exit 0 of the compare worker establishes** (see the module docstring). -/
structure CmpFacts (sp : SearchPath) (fs : FS) (C S : Name) (jobs : Nat) (c : CmpModuleRead) :
    Prop where
  facts : WorkerFacts sp fs C jobs c.w #[Graph.solutionImport S]
  view : ModelIO.CanGive (workerReads (.ofPath sp) C jobs) fs (.ok c.view)
  imported : ∀ y ∈ cmpImported c.w.home c.w.emitted,
    importedAt c.view c.w.reach (ownerMap c.w.reach.ctx) y = none
  cmp : ∀ d ∈ c.w.emitted, CmpAt (ownUses c.w.home) c.w.reach (ownerMap c.w.reach.ctx) d

/-- An accepted comparison of one record meets it. -/
theorem cmpAt_ok {rd : OleanReads ModelIO} {uses : Declaration → Array Name} {r : Reach}
    {owner : Std.HashMap Name Nat} {d : Declaration} {f : Option Filled} {fs : FS} {hs hs' : HS}
    (h : (cmpAt rd uses r owner d : ModelIO _) fs hs (.ok (.ok f)) hs') : CmpAt uses r owner d := by
  unfold cmpAt at h
  cases hk : owner[recKey d]? with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, ModelIO.bind_ok] at h
    obtain ⟨pe, _, -, h⟩ := h
    refine ⟨k, hk, tagKind ((pe.map (·.1.tag)).getD 8), ?_⟩
    cases hc : cmpCtxRecord uses d (r.ctx.getD k default) (r.homes.getD k .anonymous)
        (tagKind ((pe.map (·.1.tag)).getD 8)) with
    | error e =>
      simp only [Array.getD_eq_getD_getElem?] at hc
      simp [hc] at h
    | ok g => exact ⟨g, rfl⟩

/-- Every record an accepted `cmpAll` compared meets the context's. -/
theorem cmpAll_ok {rd : OleanReads ModelIO} {uses : Declaration → Array Name} {r : Reach}
    {owner : Std.HashMap Name Nat} {fs : FS} :
    ∀ (ds : List Declaration) (acc : Array Filled) {res : Array Filled} {hs hs' : HS},
      (cmpAll rd uses r owner ds acc : ModelIO _) fs hs (.ok (.ok res)) hs' →
      ∀ d ∈ ds, CmpAt uses r owner d
  | [], _, _, _, _, _, d, hd => by simp at hd
  | d :: ds, acc, res, hs, hs', h, d', hd' => by
    simp only [cmpAll, ModelIO.bind_ok] at h
    obtain ⟨x, _, hx, h⟩ := h
    rcases x with e | f
    · simp at h
    simp only at h
    rcases List.mem_cons.1 hd' with rfl | hd'
    · exact cmpAt_ok hx
    · exact cmpAll_ok ds _ h d' hd'

/-- `findSome?` that finds nothing: the function is `none` everywhere. -/
theorem findSome?_none {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.findSome? f = none → ∀ a ∈ l, f a = none
  | [], _, a, ha => by simp at ha
  | b :: l, h, a, ha => by
    rw [List.findSome?_cons] at h
    cases hb : f b with
    | some y => simp [hb] at h
    | none =>
      simp only [hb] at h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hb
      · exact findSome?_none h a ha

/-- **The compare worker's accept** is `CmpFacts`, whatever the heartbeat answered, for any reads
`rd` that refine the search path's. -/
theorem cmpModuleRead_ok {rd : OleanReads ModelIO} {sp : SearchPath} {C S : Name} {pace : Pace}
    {t0 jobs : Nat} {fs : FS} {c : CmpModuleRead} (hrd : OleanReads.Within fs rd sp)
    {hs hs' : HS} (h : (cmpModuleRead rd C S pace t0 jobs : ModelIO _) fs hs (.ok (.ok c)) hs') :
    CmpFacts sp fs C S jobs c := by
  unfold cmpModuleRead at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨x, _, hx, h⟩ := h
  rcases x with e | f
  · simp at h
  have hf : ModelIO.CanGive (readFiles sp C .private) fs (.ok f) :=
    (hrd.files C .private).canGive ⟨_, _, hx⟩
  simp only at h
  cases hh : homeOf C f with
  | error e => simp [hh] at h
  | ok le =>
  obtain ⟨l, expo⟩ := le
  simp only [hh, ModelIO.bind_ok] at h
  obtain ⟨y, _, hy, h⟩ := h
  rcases y with e | wr
  · simp at h
  cases hcC : wr.loads.index.contains C with
  | true => simp [hcC] at h
  | false =>
  simp only [hcC, Bool.false_eq_true, ↓reduceIte, workerSay, ModelIO.bind_ok, ModelIO.liftIO_iff,
    exists_eq_left] at h
  obtain ⟨_, h⟩ := h
  cases hds : ownRecords l with
  | error e => simp [hds] at h
  | ok ds =>
  simp only [hds] at h
  cases hfd : (l.constants.filter (!·.skipped)).find? (!wr.index.first.contains ·.name) with
  | some c => simp [hfd] at h
  | none =>
  simp only [hfd, ModelIO.bind_ok] at h
  obtain ⟨z, _, hz, h⟩ := h
  rcases z with e | r
  · simp at h
  simp only at h
  cases hn : namesNodupGo {} (r.ctx.toList.flatMap declNames) with
  | false => simp [hn] at h
  | true =>
  simp only [hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ModelIO.bind_ok,
    ModelIO.liftIO_iff, exists_eq_left] at h
  obtain ⟨_, v, _, hv, h⟩ := h
  rcases v with e | wrC
  · simp at h
  simp only at h
  cases hi : (cmpImported l ds).toList.findSome? (importedAt wrC r (ownerMap r.ctx)) with
  | some why => simp [hi] at h
  | none =>
  simp only [hi, ModelIO.bind_ok] at h
  obtain ⟨u, _, hu, h⟩ := h
  rcases u with why | filled
  · simp only at h
    split at h <;> simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  refine ⟨⟨⟨f, hf, hh⟩, (workerReads_within hrd C jobs _).canGive ⟨_, _, hy⟩, hds,
    (reach_within hrd C wr _ _).canGive ⟨_, _, hz⟩, (namesNodupGo_spec hn).1, rfl,
    cacheOK_empty⟩, (workerReads_within hrd C jobs #[]).canGive ⟨_, _, hv⟩,
    fun y hy => findSome?_none hi y (Array.mem_toList_iff.2 hy),
    fun d hd => cmpAll_ok _ _ hu d (Array.mem_toList_iff.2 hd)⟩

/-- **An accepted compare worker, in the model**: every outcome of the compare worker at the
challenge `C` and solution `S` over a snapshot `fs` that is an exit 0 is `CmpFacts`, at any
`--jobs` and pace, whatever the `liftIO` actions answered, for any reads that refine the search
path's. -/
theorem checkCmpModuleG_accept {rd : OleanReads ModelIO} {sp : SearchPath} {C S : Name}
    {mode : CheckMode} {pace : Pace} {jobs : Nat} {fs : FS} (hrd : OleanReads.Within fs rd sp)
    {hs hs' : HS} (h : (checkCmpModuleG rd C S mode pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ c, CmpFacts sp fs C S jobs c := by
  suffices H : ModelIO.AllOk (checkCmpModuleG rd C S mode pace jobs) fs hs
      (fun v => v = 0 → ∃ c, CmpFacts sp fs C S jobs c) from H 0 hs' h rfl
  simp only [checkCmpModuleG, clockMs, diagLine, outLine, ModelIO.allOk_bind, ModelIO.liftIO_iff]
  rintro t0 _ rfl - _ rfl x _ hx
  rcases x with e | c
  · simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, ModelIO.allOk_pure]
    rintro - _ rfl h0
    exact absurd h0 (CheckError.exitCode_ne_zero _)
  · intro v _ _ _
    exact ⟨c, cmpModuleRead_ok hrd hx⟩
