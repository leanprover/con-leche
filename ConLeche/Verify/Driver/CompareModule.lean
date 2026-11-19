module

public import ConLeche.Verify.Driver.Worker
import ConLeche.Verify.Frontend.Olean.Emit
import ConLeche.Verify.Frontend.Olean.Group

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

**The challenge's environment** (`chalEnvOf`): the compare worker's context with every record of
one of `C`'s names at `C`'s level-parameter names (`chalRec`, `cmpLps`), every other record as it
is.  A record of the emission declares its key's stored constant (`ownRecords_cv`), so the
level-parameter names of `C`'s records are a function of their keys.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-- **A challenge record meets the context's record of its key** (`cmpCtxRecord`, whatever kind
the home's private part names). -/
@[expose] def CmpAt (uses : Declaration → Array Name) (r : Reach) (owner : Std.HashMap Name Nat)
    (d : Declaration) : Prop :=
  ∃ k, owner[recKey d]? = some k ∧ ∃ kindS f,
    cmpCtxRecord uses d (r.ctx.getD k default) (r.homes.getD k .anonymous) kindS = .ok f

/-- **What an exit 0 of the compare worker establishes** (see the module docstring). -/
structure CmpFacts (spC sp : Roots) (fs : FS) (C S : Name) (jobs : Nat) (c : CmpModuleRead) :
    Prop where
  facts : WorkerFacts sp fs C jobs c.w #[Graph.solutionImport S]
  /-- the home, read through the challenge's lookup -/
  home : ∃ f, ModelIO.CanGive (readFiles spC C .private) fs (.ok f) ∧
    homeOf C f = .ok (c.w.home, c.w.expo)
  view : ModelIO.CanGive (workerReads (.ofPath spC) C jobs) fs (.ok c.view)
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
theorem cmpModuleRead_ok {rdC rd : OleanReads ModelIO} {spC sp : Roots} (hC : spC.Trims sp)
    {C S : Name} {pace : Pace}
    {t0 jobs : Nat} {fs : FS} {c : CmpModuleRead} (hrdC : OleanReads.Within fs fs rdC spC)
    (hrd : OleanReads.Within fs fs rd sp)
    {hs hs' : HS} (h : (cmpModuleRead rdC rd C S pace t0 jobs : ModelIO _) fs hs (.ok (.ok c)) hs') :
    CmpFacts spC sp fs C S jobs c := by
  unfold cmpModuleRead at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨x, _, hx, h⟩ := h
  rcases x with e | f
  · simp at h
  have hf : ModelIO.CanGive (readFiles spC C .private) fs (.ok f) :=
    (hrdC.files C .private).canGive ⟨_, _, hx⟩
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
  refine ⟨⟨⟨f, readFiles_trims hC hf, hh⟩, (workerReads_within hrd C jobs _).canGive ⟨_, _, hy⟩, hds,
    (reach_within hrd C wr _ _).canGive ⟨_, _, hz⟩, (namesNodupGo_spec hn).1, rfl,
    cacheOK_empty⟩, ⟨f, hf, hh⟩, (workerReads_within hrdC C jobs #[]).canGive ⟨_, _, hv⟩,
    fun y hy => findSome?_none hi y (Array.mem_toList_iff.2 hy),
    fun d hd => cmpAll_ok _ _ hu d (Array.mem_toList_iff.2 hd)⟩

/-- **An accepted compare worker, in the model**: every outcome of the compare worker at the
challenge `C` and solution `S` over a snapshot `fs` that is an exit 0 is `CmpFacts`, at any
`--jobs` and pace, whatever the `liftIO` actions answered, for any reads that refine the search
path's. -/
theorem checkCmpModuleG_accept {rdC rd : OleanReads ModelIO} {spC sp : Roots} (hC : spC.Trims sp)
    {C S : Name} {why : ModelIO (Option String)}
    {mode : CheckMode} {pace : Pace} {jobs : Nat} {fs : FS} (hrdC : OleanReads.Within fs fs rdC spC)
    (hrd : OleanReads.Within fs fs rd sp)
    {hs hs' : HS} (h : (checkCmpModuleG rdC rd C S why mode pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ c, CmpFacts spC sp fs C S jobs c := by
  suffices H : ModelIO.AllOk (checkCmpModuleG rdC rd C S why mode pace jobs) fs hs
      (fun v => v = 0 → ∃ c, CmpFacts spC sp fs C S jobs c) from H 0 hs' h rfl
  simp only [checkCmpModuleG, clockMs, diagLine, outLine, ModelIO.allOk_bind, ModelIO.liftIO_iff]
  rintro t0 _ rfl - _ rfl x _ hx
  rcases x with e | c
  · simp only [ModelIO.allOk_bind]
    rintro w _ -
    rcases w with _ | w
    · simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, ModelIO.allOk_pure]
      rintro - _ rfl h0
      exact absurd h0 (CheckError.exitCode_ne_zero _)
    · simp [ModelIO.liftIO_iff]
  · intro v _ _ _
    exact ⟨c, cmpModuleRead_ok hC hrdC hrd hx⟩

/-! ## The challenge's environment -/

/-- **The level-parameter names of the challenge's statement of `n`** (the first record declaring
it; they all declare one: `ownRecords_cv_unique`). -/
@[expose] def cmpLps (ds : Array Declaration) (n : Name) : Option (List Name) :=
  (ds.toList.findSome? fun d => (recCv? d).filter (·.name == n)).map (·.levelParams)

/-- **The names to rename a record's level parameters to**: the challenge's, where they are other
names than the record's, as many, neither list with a repeat. -/
@[expose] def renamingTo (ps? : Option (List Name)) (lps : List Name) : Option (List Name) :=
  ps?.bind fun ps => if ps != lps && levelsRenaming ps lps then some ps else none

/-- **A context record at the challenge's level-parameter names** (`lpsOf`: the challenge's names
for a key): a definition, theorem, opaque constant or axiom renamed (`ConstantInfo.atLps`, its
value too), but the quotient's axiom; every other record as it is. -/
@[expose] def chalRec (lpsOf : Name → Option (List Name)) : Declaration → Declaration
  | d@(.axiomDecl cv) =>
    if cv.name = quotSoundName then d else
    match renamingTo (lpsOf cv.name) cv.levelParams with
    | some ps => .axiomDecl (cv.atLps ps)
    | none => d
  | d@(.defnDecl cv v h) =>
    match renamingTo (lpsOf cv.name) cv.levelParams with
    | some ps => .defnDecl (cv.atLps ps) (v.instantiateLevelParams cv.levelParams (ps.map .param)) h
    | none => d
  | d@(.thmDecl cv v) =>
    match renamingTo (lpsOf cv.name) cv.levelParams with
    | some ps => .thmDecl (cv.atLps ps) (v.instantiateLevelParams cv.levelParams (ps.map .param))
    | none => d
  | d@(.opaqueDecl cv v) =>
    match renamingTo (lpsOf cv.name) cv.levelParams with
    | some ps => .opaqueDecl (cv.atLps ps) (v.instantiateLevelParams cv.levelParams (ps.map .param))
    | none => d
  | d => d

/-- **The challenge's environment** (see the module docstring): the compare worker's context, every
record of one of the challenge's names at the challenge's level-parameter names. -/
@[expose] def chalEnvOf (c : CmpModuleRead) : Env :=
  streamEnv (c.w.reach.ctx.toList.map (chalRec (cmpLps c.w.emitted)))

/-- An inductive record declares no single statement. -/
theorem declOfF_ind_recCv {nm : Nat → M Name} {lv : Nat → M Level}
    {ex : Nat → M Expr} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {d : Declaration}
    (h : declOfF nm lv ex (.ind tys cts rcs) = .ok (.inl d)) : recCv? d = none := by
  simp only [declOfF, bind, Except.bind, pure, Except.pure] at h
  cases hv : validateIndF nm lv ex tys cts rcs with
  | error e => simp only [hv] at h; cases h
  | ok x =>
    simp only [hv] at h
    rcases x with x | ⟨c, n⟩
    · simp at h
    · simp only at h
      cases hb : indBlockOfF nm lv ex tys c rcs n with
      | error e => simp only [hb] at h; cases h
      | ok d' =>
        simp only [hb, Except.ok.injEq, Sum.inl.injEq] at h
        subst h
        obtain ⟨b, rfl⟩ := indBlockOfF_ind hb
        rfl

/-- **A record of the emission declares its key's stored constant**: its statement is that of
the constant the own constants' merge holds under its name. -/
theorem ownRecords_cv {l : Loaded} {ds : Array Declaration} (h : ownRecords l = .ok ds)
    {d : Declaration} (hd : d ∈ ds) {cv : ConstantVal} (hcv : recCv? d = some cv) :
    ∃ e : CEntry, (mergedOfList (l.constants.toList.filter (!·.skipped))).map[e.name]? = some e ∧
      cv = ⟨e.name, e.levelParams, e.type⟩ := by
  cases hb : blocksOk (mergedOfList (l.constants.toList.filter (!·.skipped))) with
  | error e => simp [ownRecords, hb] at h
  | ok u =>
  simp only [ownRecords, hb] at h
  have hN := mergedOfList_names (l.constants.toList.filter (!·.skipped))
  obtain ⟨r, hr, hdr⟩ := (declsOf_spec h).2 d hd
  have hR := (emitAll_spec hN _).1 r hr
  cases r with
  | ind ts cs rs => rw [declOfF_ind_recCv hdr] at hcv; cases hcv
  | ax cvr u =>
    obtain ⟨c, hst, hc1, -⟩ := hR
    simp only [declOfF, cvOfF_of hc1, bind, Except.bind, pure, Except.pure] at hdr
    split at hdr <;> simp only [Except.ok.injEq, Sum.inl.injEq, reduceCtorEq] at hdr
    subst hdr
    simp only [recCv?, Option.some.injEq] at hcv
    exact ⟨c, hst, hcv.symm⟩
  | defn cvr i hh s =>
    obtain ⟨c, hst, hc1, -⟩ := hR
    simp only [declOfF, cvOfF_of hc1, bind, Except.bind, pure, Except.pure] at hdr
    split at hdr
    · revert hdr
      cases (emitAll _ _).ex i <;> simp only [reduceCtorEq, Except.ok.injEq, Sum.inl.injEq,
        false_implies]
      rintro rfl
      simp only [recCv?, Option.some.injEq] at hcv
      exact ⟨c, hst, hcv.symm⟩
    · simp at hdr
  | thm cvr i =>
    obtain ⟨c, hst, hc1, -⟩ := hR
    simp only [declOfF, cvOfF_of hc1, bind, Except.bind, pure, Except.pure] at hdr
    revert hdr
    cases (emitAll _ _).ex i <;> simp only [reduceCtorEq, Except.ok.injEq, Sum.inl.injEq,
      false_implies]
    rintro rfl
    simp only [recCv?, Option.some.injEq] at hcv
    exact ⟨c, hst, hcv.symm⟩
  | opaq cvr i u =>
    obtain ⟨c, hst, hc1, -⟩ := hR
    simp only [declOfF, cvOfF_of hc1, bind, Except.bind, pure, Except.pure] at hdr
    split at hdr
    · simp at hdr
    · revert hdr
      cases (emitAll _ _).ex i <;> simp only [reduceCtorEq, Except.ok.injEq, Sum.inl.injEq,
        false_implies]
      rintro rfl
      simp only [recCv?, Option.some.injEq] at hcv
      exact ⟨c, hst, hcv.symm⟩
  | quot cvr k =>
    obtain ⟨c, hst, hc1, -⟩ := hR
    simp only [declOfF, cvOfF_of hc1, bind, Except.bind, pure, Except.pure] at hdr
    split at hdr <;> simp only [reduceCtorEq, Except.ok.injEq, Sum.inl.injEq] at hdr
    all_goals (subst hdr; simp only [recCv?, Option.some.injEq] at hcv; exact ⟨c, hst, hcv.symm⟩)

/-- **Two records of the emission declaring one name declare one statement.** -/
theorem ownRecords_cv_unique {l : Loaded} {ds : Array Declaration} (h : ownRecords l = .ok ds)
    {d₁ d₂ : Declaration} (h₁ : d₁ ∈ ds) (h₂ : d₂ ∈ ds) {cv₁ cv₂ : ConstantVal}
    (hc₁ : recCv? d₁ = some cv₁) (hc₂ : recCv? d₂ = some cv₂) (hn : cv₁.name = cv₂.name) :
    cv₁ = cv₂ := by
  obtain ⟨e₁, he₁, rfl⟩ := ownRecords_cv h h₁ hc₁
  obtain ⟨e₂, he₂, rfl⟩ := ownRecords_cv h h₂ hc₂
  simp only at hn
  rw [hn, he₂] at he₁
  cases Option.some.inj he₁
  rfl

theorem findSome?_filter_spec {ds : List Declaration} {n : Name} {cv : ConstantVal}
    (h : (ds.findSome? fun d => (recCv? d).filter (·.name == n)) = some cv) :
    ∃ d ∈ ds, recCv? d = some cv ∧ cv.name = n := by
  obtain ⟨d, hd, hf⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨d, hd, ?_⟩
  cases hc : recCv? d with
  | none => simp [hc] at hf
  | some cv' =>
    simp only [hc, Option.filter_some, beq_iff_eq] at hf
    split at hf
    · cases hf; exact ⟨rfl, by assumption⟩
    · cases hf

/-- **The challenge's names for one of its statements are that statement's.** -/
theorem cmpLps_of_mem {l : Loaded} {ds : Array Declaration} (h : ownRecords l = .ok ds)
    {d : Declaration} (hd : d ∈ ds) {cv : ConstantVal} (hcv : recCv? d = some cv) :
    cmpLps ds cv.name = some cv.levelParams := by
  unfold cmpLps
  cases hf : ds.toList.findSome? (fun d => (recCv? d).filter (·.name == cv.name)) with
  | none =>
    exfalso
    have := List.findSome?_eq_none_iff.1 hf d (Array.mem_toList_iff.2 hd)
    simp [hcv] at this
  | some cv' =>
    obtain ⟨d', hd', hc', hn⟩ := findSome?_filter_spec hf
    simp only [Option.map_some]
    rw [ownRecords_cv_unique h (Array.mem_toList_iff.1 hd') hd hc' hcv hn]
