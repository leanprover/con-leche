module

public import ConLeche.Driver.Worker
public import ConLeche.Driver.CompareModule
public import ConLeche.Verify.Driver.Oleans
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Driver.Shared
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Group
import ConLeche.Verify.Frontend.Olean.Emit
import ConLeche.Verify.Frontend.Prepare

/-!
# The worker, in the model

What an exit 0 of the worker at module `m` (`checkModuleG`, `ConLeche/Driver/Worker.lean`)
establishes on a snapshot, for the module `m`:

* `workerRead_ok` — **what was read and checked** (`WorkerFacts`): `m`'s home read and its three
  parts checked against each other (`readHome`, `checkViews`); the reads (`workerReads`: the
  header fixpoint, the name index, Lean's clash rule over every loaded name, freshness); the own
  records the emission of the loaded constants (`ownRecords`); the reach from their reads
  (`reach`); the context's names distinct; the own records checked in the hoist's order;
* `checkModuleG_accept` — **the own records accepted from the context**: a `DeclsRun` of the own
  records, the theorems' values in place (`fillOf`), from `mkFEnv (streamEnv ctx)` at position
  `ctx.length`, ending at the own environment (`checkDecls_of_jobs_from`): the specification's
  `ImportOk.accepted`;
* `worker_ctx` — **the context**: every context record `RecordScoped` in the prefix of the
  context ending with it (`ImportOk.ordered`) and in the context, every name
  it reads stored there, the context `EnvWF`, its names distinct (`ImportOk.nodup`), and each name
  read from one record of one home (`ctxHome`, `ImportOk.one_src`);
* `worker_thm` — **the own records are the module's**: every theorem of `m`'s private view by the
  specification (`ViewOf`) is an own record, with its statement, and its value in place is the
  specification's (`ValueAt`).
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean ConLeche.Cached

/-! ## The context's names -/

theorem namesNodupGo_spec :
    ∀ {s : Std.HashSet Name} {ns : List Name}, namesNodupGo s ns = true →
      ns.Nodup ∧ ∀ n ∈ ns, s.contains n = false
  | s, [], _ => ⟨List.nodup_nil, by simp⟩
  | s, n :: ns, h => by
    simp only [namesNodupGo, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := namesNodupGo_spec h.2
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, h1⟩, fun x hx => ?_⟩
    · have := h2 n hm
      simp [Std.HashSet.contains_insert] at this
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · have := h2 x hx
        simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
        exact this.2

/-- A theorem's value in place changes nothing a record installs. -/
theorem streamEnv_fill (F : Expr → Expr) :
    ∀ (ds : List Declaration) (env : Env), streamEnv (ds.map (fillDecl F)) env = streamEnv ds env
  | [], _ => rfl
  | d :: ds, env => by
    simp only [List.map_cons, streamEnv, List.foldl_cons, declConstants_fillDecl,
      declTables_fillDecl]
    exact streamEnv_fill F ds _

/-! ## What the worker read -/

/-- With no import added, a worker's own part is its private part's. -/
@[simp] theorem _root_.ConLeche.Frontend.Olean.NamePositions.withImports_empty
    (own : NamePositions) : own.withImports #[] = own := by
  simp [NamePositions.withImports]

/-- Imports added: the header's, followed by them. -/
theorem _root_.ConLeche.Frontend.Olean.NamePositions.withImports_imports (own : NamePositions)
    (x : Array ImportRec) : (own.withImports x).header.imports = own.header.imports ++ x := by
  unfold NamePositions.withImports
  split <;> simp_all

/-- Imports added: of the module system as the module is. -/
theorem _root_.ConLeche.Frontend.Olean.NamePositions.withImports_isModule (own : NamePositions)
    (x : Array ImportRec) : (own.withImports x).header.isModule = own.header.isModule := by
  unfold NamePositions.withImports
  split <;> rfl

/-- **The reach's own names at a module with imports `x` added**: its own names; none at a
compared challenge (`x` not empty, task #608), whose names are read from its solution. -/
@[expose] def ownOf (x : Array ImportRec) (w : WorkerRead) : Std.HashSet Name :=
  if x.isEmpty then ownNames w.home else {}

/-- **The reach's roots at a module with imports `x` added**: what its own records read
(`ownRoots`); at a compared challenge, its names and what its records read of what it imports
(`cmpRoots`). -/
@[expose] def rootsOf (x : Array ImportRec) (w : WorkerRead) : Array Name :=
  if x.isEmpty then ownRoots w.reads.index w.home w.emitted else cmpRoots w.home w.emitted

/-- **The records a worker checks**: its own records in the hoist's order; none at a compared
challenge, whose records are compared, not checked. -/
@[expose] def recsOf (x : Array ImportRec) (w : WorkerRead) : Array Declaration :=
  if x.isEmpty then (Frontend.hoistNatOpGround (ownUses w.home) w.emitted).1 else #[]

/-- **What a worker read and checked before its jobs, on a snapshot** (`workerRead`'s phases, see
`ConLeche/Driver/Worker.lean`); `x` the imports the run adds to the module's header (none, but at
a compared challenge, whose worker is `cmpModuleRead`, task #608). -/
structure WorkerFacts (sp : SearchPath) (fs : FS) (m : Name) (jobs : Nat) (w : WorkerRead)
    (x : Array ImportRec := #[]) : Prop where
  /-- the home: its private part's files, the private view loaded off them, its three parts
  checked against each other -/
  home : ∃ f, ModelIO.CanGive (readFiles sp m .private) fs (.ok f) ∧
    homeOf m f = .ok (w.home, w.expo)
  /-- the header fixpoint, the name index, Lean's clash rule over every loaded name, freshness -/
  reads : ModelIO.CanGive (workerReads (.ofPath sp) m jobs x) fs (.ok w.reads)
  /-- the own records: the emission of the loaded constants -/
  emitted : ownRecords w.home = .ok w.emitted
  /-- the context: the reach from the own records' reads -/
  reach : ModelIO.CanGive (reach (.ofPath sp) m w.reads (ownOf x w) (rootsOf x w)) fs (.ok w.reach)
  /-- the context's names, distinct -/
  nodup : (w.reach.ctx.toList.flatMap declNames).Nodup
  /-- the own records, in the hoist's order -/
  own : w.own = recsOf x w
  /-- the region the theorems' values are read from: the home's, on the snapshot -/
  values : CacheOK sp fs #[⟨m, w.home.frontier⟩] w.values

/-- **`workerRead`'s accept** is `WorkerFacts`, whatever the heartbeat answered. -/
theorem workerRead_ok {rd : OleanReads ModelIO} {sp : SearchPath} {m : Name} {pace : Pace}
    {t0 jobs : Nat} {fs : FS} {w : WorkerRead} (hrd : OleanReads.Within fs rd sp) {hs hs' : HS}
    (h : (workerRead rd m pace t0 jobs : ModelIO _) fs hs (.ok (.ok w)) hs') :
    WorkerFacts sp fs m jobs w := by
  unfold workerRead at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨x, _, hx, h⟩ := h
  rcases x with e | f
  · simp at h
  have hf : ModelIO.CanGive (readFiles sp m .private) fs (.ok f) :=
    (hrd.files m .private).canGive ⟨_, _, hx⟩
  simp only at h
  cases hh : homeOf m f with
  | error e => simp [hh] at h
  | ok le =>
  obtain ⟨l, expo⟩ := le
  simp only [hh, workerSay, ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
  obtain ⟨_, y, _, hy, h⟩ := h
  rcases y with e | wr
  · simp at h
  simp only [ModelIO.bind_ok, ModelIO.liftIO_iff, exists_eq_left] at h
  obtain ⟨_, h⟩ := h
  cases hds : ownRecords l with
  | error e => simp [hds] at h
  | ok ds =>
  simp only [hds, ModelIO.bind_ok] at h
  obtain ⟨z, _, hz, h⟩ := h
  rcases z with e | r
  · simp at h
  simp only at h
  cases hn : namesNodupGo {} (r.ctx.toList.flatMap declNames) with
  | false => simp [hn] at h
  | true =>
  simp only [hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ModelIO.bind_ok,
    ModelIO.liftIO_iff, exists_eq_left] at h
  obtain ⟨_, h⟩ := h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  refine ⟨⟨f, hf, hh⟩, (workerReads_within hrd m jobs #[]).canGive ⟨_, _, hy⟩, hds,
    (reach_within hrd m _ _ _).canGive ⟨_, _, hz⟩, (namesNodupGo_spec hn).1, rfl, ?_⟩
  -- the values' region: the home's files' private region
  exact cacheOK_files (md := ⟨m, l.frontier⟩) rfl hf

/-! ## The own records accepted from the context -/

/-- The values every job of a worker reads: its home's, on the snapshot. -/
theorem workerFacts_good {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs m jobs w) :
    ∀ md ∈ (#[⟨m, w.home.frontier⟩] : Array ModRef), ∃ f r a,
      ModelIO.CanGive (readFiles sp md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r := by
  intro md hmd
  simp only [List.mem_toArray, List.mem_singleton] at hmd
  subst hmd
  obtain ⟨f, hf, h⟩ := hw.home
  simp only [homeOf] at h
  cases hl : loadView 0 m f with
  | error e => simp [hl] at h
  | ok l =>
  simp only [hl] at h
  cases hc : checkViews m f l with
  | error e => simp [hc] at h
  | ok expo =>
  simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [loadView] at hl
  split at hl
  · rename_i l' hl'
    cases hl
    obtain ⟨r, a, -, -, hreg, -, -, -, -, hgood, -⟩ := loadAt_spec hl'
    exact ⟨f, r, a, hf, hreg, hgood⟩
  · cases hl

/-- **What an accepted worker at `m` establishes**: what it read and checked, and its own
records, with their theorems' values in place (`fillOf` over the home's frontier), accepted one
after another from the context's environment at position `ctx.size`, ending at the own
environment (`ImportOk.accepted`). -/
@[expose] def WorkerAccepted (mode : CheckMode) (maxNatSize : Nat) (sp : SearchPath) (fs : FS) (m : Name) (jobs : Nat) :
    Prop :=
  ∃ w, WorkerFacts sp fs m jobs w ∧
    DeclsRun mode natOpPinSets maxNatSize
      (w.own.toList.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
      (w.reach.ctx.size, mkFEnv (streamEnv w.reach.ctx.toList))
      (w.reach.ctx.size + w.own.size, mkFEnv (streamEnv
        (w.own.toList.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
        (streamEnv w.reach.ctx.toList)))

/-- The check phase and the verdict of an accepted worker: an exit 0 is `WorkerAccepted`. -/
theorem worker_tail {sp : SearchPath} {R : Roots} {m : Name} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace}
    {jobs : Nat} {fs : FS} {w : WorkerRead} (hR : R.Ok fs) (hp : R.bare = sp)
    (hw : WorkerFacts sp fs m jobs w) (tag who : String)
    (alone : Bool) (t0 tIndex tParse : Nat) (J : Jobs (w.reach.ctx ++ w.own)) :
    ∀ v hs hs', (checkOleansG mode maxNatSize pace t0 tIndex tParse jobs R #[⟨m, w.home.frontier⟩] J
        w.reach.ctx.size alone w.values : ModelIO _) fs hs (.ok v) hs' →
      ModelIO.AllOk (verdictG tag w.own.size t0 (w.reach.ctx ++ w.own) v who) fs hs'
        (fun c => c = 0 → WorkerAccepted mode maxNatSize sp fs m jobs) := by
  intro v _ _ hv c _ hc h0
  obtain rfl := verdictG_ok hc h0
  have hgood : ∀ md ∈ (#[⟨m, w.home.frontier⟩] : Array ModRef), ∃ f r a,
      ModelIO.CanGive (readFiles R md.name .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ md.frontier.Good r := fun md hmd => by
    obtain ⟨f, r, a, h1, h2, h3⟩ := workerFacts_good hw md hmd
    exact ⟨f, r, a, readFiles_rev hR (hp ▸ h1), h2, h3⟩
  have hjobs := checkOleansG_jobs hgood (CacheOK.roots hR (by rw [hp]; exact hw.values)) hv
  rw [fillOf_roots hR, hp] at hjobs
  refine ⟨w, hw, ?_⟩
  have hrun := checkDecls_of_jobs_from (mode := mode) (pins := natOpPinSets) (maxNatSize := maxNatSize)
    (ctx := w.reach.ctx.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
    (own := w.own.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
    ?_ ?_
  · simpa [streamEnv_fill] using hrun
  · rw [Array.toList_map, streamEnv_fill]
    exact nodupNames_streamEnv hw.nodup
  · intro k hk hs
    simp only [Array.size_map, Array.size_append] at hk hs
    simp only [← Array.map_append, buildIndex_fill, Array.getElem_map]
    rw [← J.hI]
    have hk' : k < (w.reach.ctx ++ w.own).size := by simpa using hk
    exact (hjobs k hs hk').run hk'

/-- **An accepted worker, in the model**: every outcome of the worker at module `m` over a
snapshot `fs` that is an exit 0 is `WorkerAccepted`, at any `--jobs`, pace and `alone`, whatever
the `liftIO` actions answered, for any reads `rd` that refine the search path's (the search
path's own, `OleanReads.Within.ofPath`, or the one-process mode's tables). -/
theorem checkModuleG_accept {rd : OleanReads ModelIO} {sp : SearchPath} {R : Roots} {m : Name}
    {mode : CheckMode} {maxNatSize : Nat} {pace : Pace} {jobs : Nat} {alone : Bool} {fs : FS}
    (hrd : OleanReads.Within fs rd sp) (hR : R.Ok fs) (hRp : R.bare = sp) {hs hs' : HS}
    (h : (checkModuleG rd R m mode maxNatSize pace jobs alone : ModelIO _) fs hs (.ok 0) hs') :
    WorkerAccepted mode maxNatSize sp fs m jobs := by
  suffices H : ModelIO.AllOk (checkModuleG rd R m mode maxNatSize pace jobs alone) fs hs
      (fun c => c = 0 → WorkerAccepted mode maxNatSize sp fs m jobs) from H 0 hs' h rfl
  simp only [checkModuleG, clockMs, diagLine, ModelIO.allOk_bind, ModelIO.liftIO_iff]
  rintro t0 _ rfl - _ rfl x _ hx
  rcases x with ⟨e, _⟩ | w
  · simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, ModelIO.allOk_pure]
    rintro - _ rfl h0
    exact absurd h0 (CheckError.exitCode_ne_zero _)
  have hw := workerRead_ok hrd hx
  -- with or without the diagnostic lines (a `Unit` step), the clock and the jobs' index, then
  -- the check phase and the verdict
  simp only
  by_cases hh : w.hoisted.size > 0 <;>
    simp only [hh, ↓reduceIte, ModelIO.allOk_bind, ModelIO.liftIO_iff] <;>
    (first | rintro (_ : Unit) _ rfl | skip) <;>
    rintro tIndex _ rfl J _ rfl tParse _ rfl <;>
    by_cases hp : pace.on = true <;>
    simp only [hp, Bool.false_eq_true, ↓reduceIte, ModelIO.allOk_bind, ModelIO.liftIO_iff] <;>
    (first | rintro (_ : Unit) _ rfl | skip) <;>
    exact fun v hs₁ hv => worker_tail hR hRp hw _ _ _ t0 tIndex tParse J v _ hs₁ hv

/-! ## The context -/

/-- **The context of an accepted worker**: every context record `RecordScoped` in the
prefix of the context ending with it (`ImportOk.ordered`) and in the context, every name it reads
stored there, the context `EnvWF`, its names distinct (`ImportOk.nodup`). -/
theorem worker_ctx {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs m jobs w) :
    (∀ k (hk : k < w.reach.ctx.toList.length),
      RecordScoped (streamEnv (w.reach.ctx.toList.take (k + 1))) w.reach.ctx.toList[k]) ∧
    (∀ d ∈ w.reach.ctx.toList, RecordScoped (streamEnv w.reach.ctx.toList) d) ∧
    (∀ d ∈ w.reach.ctx.toList, ∀ y ∈ recordReads d,
      ((streamEnv w.reach.ctx.toList).find? y).isSome = true) ∧
    EnvWF (streamEnv w.reach.ctx.toList) ∧
    ((streamEnv w.reach.ctx.toList).consts.map (·.toConstantVal.name)).Nodup := by
  obtain ⟨_, _, hr⟩ := hw.reach
  obtain ⟨o, a, b, c, -⟩ := reach_ok hr
  exact ⟨o, a, b, c, nodupNames_streamEnv hw.nodup⟩

theorem mem_foldl_append_if {α β : Type} (p : α → Bool) (f : α → Array β) (y : β) :
    ∀ (xs : List α) (acc : Array β),
      y ∈ xs.foldl (fun acc a => if p a then acc else acc ++ f a) acc ↔
        y ∈ acc ∨ ∃ a ∈ xs, p a = false ∧ y ∈ f a
  | [], acc => by simp
  | a :: xs, acc => by
    rw [List.foldl_cons, mem_foldl_append_if p f y xs]
    cases hp : p a <;> simp [hp, or_assoc]

/-- **A certified own operation's pin ground is in the context**: at a worker's accept, every
name of the pin ground of an own constant (`pinGround` over the shipped variants) that a loaded
module holds and that is not an own name is stored in the context, so the operation's install
check finds there whatever of its variants' pins and certificates the loaded modules hold. -/
theorem worker_ground {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs m jobs w) {c : CEntry} (hc : c ∈ w.home.constants)
    (hsk : c.skipped = false) {g : Name} (hg : g ∈ pinGround natOpPinSets c.name)
    (hix : w.reads.index.first.contains g = true) (ho : (ownNames w.home).contains g = false) :
    ((streamEnv w.reach.ctx.toList).find? g).isSome = true := by
  obtain ⟨_, _, hr⟩ := hw.reach
  refine (reach_ok hr).2.2.2.2 g ?_ ho
  show g ∈ ownRoots w.reads.index w.home w.emitted
  unfold ownRoots
  refine Array.mem_append.2 (.inr (Array.mem_filter.2 ⟨?_, hix⟩))
  rw [← Array.foldl_toList]
  exact (mem_foldl_append_if (fun c : CEntry => c.skipped)
    (fun c : CEntry => pinGround natOpPinSets c.name) g _ _).2
    (.inr ⟨c, Array.mem_toList_iff.2 hc, hsk, hg⟩)

/-- Two members of a list whose images, concatenated, are distinct, sharing an element of their
images, are one. -/
theorem nodup_flatMap_inj {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → ∀ {x : β}, x ∈ f a →
      x ∈ f b → a = b
  | [], _, _, _, ha, _, _, _, _ => by simp at ha
  | y :: l, h, a, b, ha, hb, x, hxa, hxb => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    have far : ∀ {c}, c ∈ l → x ∈ f c → x ∈ f y → False := fun hc hxc hxy =>
      h3 x hxy x (List.mem_flatMap.2 ⟨_, hc, hxc⟩) rfl
    rcases List.mem_cons.1 ha with ha₁ | ha₁
    · rcases List.mem_cons.1 hb with hb₁ | hb₁
      · exact ha₁.trans hb₁.symm
      · rw [ha₁] at hxa; exact (far hb₁ hxb hxa).elim
    · rcases List.mem_cons.1 hb with hb₁ | hb₁
      · rw [hb₁] at hxb; exact (far ha₁ hxa hxb).elim
      · exact nodup_flatMap_inj h2 ha₁ hb₁ hxa hxb

/-- **A context name is one record's** (`ImportOk.one_src`, with a module's source a function
of the record storing the name): two context records storing one name are one. -/
theorem worker_one_record {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs m jobs w) {d d' : Declaration} (hd : d ∈ w.reach.ctx.toList)
    (hd' : d' ∈ w.reach.ctx.toList) {n : Name} (hn : n ∈ declNames d) (hn' : n ∈ declNames d') :
    d = d' := by
  exact nodup_flatMap_inj hw.nodup hd hd' hn hn'

/-! ## The own records are the module's -/

/-- The home of an accepted worker: its files, loaded. -/
theorem workerFacts_load {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs m jobs w) :
    ∃ f, ModelIO.CanGive (readFiles sp m .private) fs (.ok f) ∧ loadAt 0 m f = some w.home := by
  obtain ⟨f, hf, h⟩ := hw.home
  simp only [homeOf] at h
  cases hl : loadView 0 m f with
  | error e => simp [hl] at h
  | ok l =>
  simp only [hl] at h
  cases hc : checkViews m f l with
  | error e => simp [hc] at h
  | ok expo =>
  simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [loadView] at hl
  split at hl
  · rename_i l' hl'
    cases hl
    exact ⟨f, hf, hl'⟩
  · cases hl

/-- A constant's entry names it as its skeleton does. -/
theorem lazyEntry_name {r : Region} {i : Nat} {s : CEntryF UInt64 UInt64} {E : CEntryF Name Expr}
    (he : lazyEntry (nameP r) (exprP r) r i s = some E) : nameP r s.name = some E.name := by
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all₀ =>
    have hk : ∃ w all, E.kind = .thm w all := by
      simp only [lazyEntry] at he
      split at he
      rotate_left
      · cases he
      obtain ⟨g, -, he⟩ := bind_some_left he
      obtain ⟨n', -, he⟩ := bind_some_left he
      obtain ⟨l', -, he⟩ := bind_some_left he
      obtain ⟨t', -, he⟩ := bind_some_left he
      obtain ⟨a', -, he⟩ := bind_some_left he
      simp only [pure, Option.some.injEq] at he
      subst he
      exact ⟨_, _, rfl⟩
    obtain ⟨w, all, hk⟩ := hk
    exact (lazyEntry_thm he hk).choose_spec.choose_spec.choose_spec.2.2.2.2.1
  | _ =>
    simp only [lazyEntry] at he
    exact (CEntryF.mapM_parts he).1

/-- **Two skeletons of a private part with one name are one**: its name table names each
constant once (`constNamesOk`). -/
theorem skels_name_inj {r : Region} {a : UInt64} {sk : ModSkel}
    {skels : List (CEntryF UInt64 UInt64)} (hcn : constNamesOk r a = true)
    (hsk : moduleSkel r a = some sk) (hskels : sk.consts.mapM (constSkel r) = some skels)
    {s₁ s₂ : CEntryF UInt64 UInt64} (h₁ : s₁ ∈ skels) (h₂ : s₂ ∈ skels) {n : Name}
    (hn₁ : nameP r s₁.name = some n) (hn₂ : nameP r s₂.name = some n) : s₁ = s₂ := by
  obtain ⟨g, cs, hg, hcs, names, hlen, hnd, hk⟩ := constNamesOk_spec hcn
  have hsc : sk.consts = cs.toList := by
    unfold moduleSkel at hsk
    rw [hg] at hsk
    simp only [Option.bind_eq_bind, Option.bind_some] at hsk
    split at hsk
    · obtain ⟨_, -, hsk⟩ := Option.bind_eq_some_iff.1 hsk
      obtain ⟨_, -, hsk⟩ := Option.bind_eq_some_iff.1 hsk
      obtain ⟨_, -, hsk⟩ := Option.bind_eq_some_iff.1 hsk
      obtain ⟨cs', hcs', hsk⟩ := Option.bind_eq_some_iff.1 hsk
      rw [hcs] at hcs'
      cases hcs'
      cases hsk
      rfl
    · cases hsk
  have hl := mapM_length_opt hskels
  have at_ : ∀ {s}, s ∈ skels → nameP r s.name = some n → ∃ i, ∃ hi : i < names.length,
      names[i] = n ∧ skels[i]? = some s := by
    intro s hs hn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have hic : i < cs.size := by rw [hl, hsc] at hi; simpa using hi
    obtain ⟨sk', h1, h2⟩ := hk i hic
    have hget := mapM_getElem? hskels i
    rw [hsc] at hget
    rw [← Array.getElem?_toList, ← hget, List.getElem?_eq_getElem hi] at h1
    cases h1
    rw [hn] at h2
    have hin : i < names.length := by omega
    rw [List.getElem?_eq_getElem hin] at h2
    exact ⟨i, hin, (Option.some.inj h2).symm, List.getElem?_eq_getElem hi⟩
  obtain ⟨i, hi, hni, hsi⟩ := at_ h₁ hn₁
  obtain ⟨j, hj, hnj, hsj⟩ := at_ h₂ hn₂
  have hij : i = j := List.Nodup.eq_of_getElem_eq hnd hi hj (hni.trans hnj.symm)
  subst hij
  rw [hsi] at hsj
  exact Option.some.inj hsj

/-- **Every theorem of the module's private view is an own record of an accepted worker**,
with its statement, and its reference, on the snapshot, stands for the specification's value
(`ValueAt` over the home's frontier): the own records hold the module's theorems as the
specification reads them off the files (`ViewOf`). -/
theorem worker_thm {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs m jobs w) {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr}
    {all : List Name} (hv : ViewOf sp fs m d) (hc : c ∈ d.constants) (hk : c.kind = .thm v all) :
    ∃ code, Declaration.thmDecl ⟨c.name, c.levelParams, c.type⟩ (.bvar code) ∈ w.own ∧
      ValueAt sp fs #[⟨m, w.home.frontier⟩] code v := by
  obtain ⟨f, hf, hl⟩ := workerFacts_load hw
  obtain ⟨r, a, sk, skels, hreg, hcn, hsk, hskels, -, -, hlazy⟩ := loadAt_spec hl
  obtain ⟨f', hf', hview⟩ := hv
  obtain rfl := readFiles_unique hf hf'
  obtain ⟨sk', hsk', hspec⟩ := view_parts hreg hview
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨loc, hloc, hcs⟩ := mapM_mem_inv hspec (by simpa using hc)
  obtain ⟨s, hs1, hs2⟩ := constSpec_parts hcs
  obtain ⟨s', hs'mem, hs'⟩ := mapM_mem hskels hloc
  rw [hs1] at hs'
  cases hs'
  obtain ⟨e, he, hent⟩ := hlazy.of_skel _ hs'mem
  obtain ⟨hn, hlp, hty, hth⟩ := lazyEntry_of_spec hs2 hent
  obtain ⟨p, g, all', -, hke, hpv, hpg⟩ := hth v all hk
  -- the kept constant of its name in the own constants' merge
  have hes : e.skipped = false := by simp [CEntry.skipped, hke, CKindF.skipped]
  have hecs : e ∈ w.home.constants.toList.filter (!·.skipped) :=
    List.mem_filter.2 ⟨by simpa using he, by simp [hes]⟩
  obtain ⟨hO, hin, hall⟩ := mergedOfList_spec (w.home.constants.toList.filter (!·.skipped))
  have hcont := hall e hecs
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hcont
  obtain ⟨e₁, he₁⟩ := Option.isSome_iff_exists.1 hcont
  have hN := mergedOfList_names (w.home.constants.toList.filter (!·.skipped))
  have hname₁ := hN _ _ he₁
  have he₁c : e₁ ∈ w.home.constants.toList := (List.mem_filter.1 (hin _ _ he₁)).1
  obtain ⟨s₁, hs₁, hent₁⟩ := hlazy.to_skel e₁ he₁c
  have hss : s₁ = s := skels_name_inj hcn hsk hskels hs₁ hs'mem
    (n := e.name) (by rw [lazyEntry_name hent₁, hname₁]) (lazyEntry_name hent)
  subst hss
  rw [hent] at hent₁
  have hee : e₁.toCEntryF = e.toCEntryF := (Option.some.inj hent₁).symm
  have hk₁ : e₁.kind = .thm (valueRef 0 g) all := by
    rw [show e₁.kind = e₁.toCEntryF.kind from rfl, hee]; exact hke
  -- its record
  have hown := hw.emitted
  cases hb : blocksOk (mergedOfList (w.home.constants.toList.filter (!·.skipped))) with
  | error e => simp [ownRecords, hb] at hown
  | ok u =>
  simp only [ownRecords, hb] at hown
  have hmem := declsOf_thm hN hO hown hb ((hO _).2 (by
    rw [Std.HashMap.contains_eq_isSome_getElem?]; exact hcont)) he₁ hk₁
  have hf₁ : e₁.name = c.name ∧ e₁.levelParams = c.levelParams ∧ e₁.type = c.type := by
    refine ⟨?_, ?_, ?_⟩
    · rw [show e₁.name = e₁.toCEntryF.name from rfl, hee]; exact hn
    · rw [show e₁.levelParams = e₁.toCEntryF.levelParams from rfl, hee]; exact hlp
    · rw [show e₁.type = e₁.toCEntryF.type from rfl, hee]; exact hty
  rw [hf₁.1, hf₁.2.1, hf₁.2.2] at hmem
  refine ⟨g * refBase + 0, ?_, ?_⟩
  · rw [hw.own]
    exact Array.mem_toList_iff.1 ((Frontend.hoistNatOpGround_perm _ _).mem_iff.2
      (Array.mem_toList_iff.2 hmem))
  · obtain ⟨hm0, hlg⟩ := refParts (i := 0) (g := g) (by decide)
    refine ⟨⟨m, w.home.frontier⟩, f, r, a, ?_, hf, hreg, ?_⟩
    · rw [hm0]; rfl
    · rw [hlg]
      simpa [exprP, hpg] using hpv

/-! ## The module's local checks, as far as one worker gives them -/

/-- **An accepted worker's part of `ImportOk`**: in any development whose module `i` has the
worker's context records as its `ctx` and its own records, the theorems' values in place, as its
`decls`, and reads each context name from a module that is a function of the record storing it
(`srcOf`; well defined by `worker_one_record`), the context's names are distinct (`nodup`), a
record's names have one source (`one_src`), the own records are accepted from the context
(`accepted`), every context record reads only itself and earlier records (`ordered`), and every
context record is closed in the context, which is well formed.  What
is left of `ImportOk` relates `i` to other modules (`below`, `src_lt`, `presented`, `reads`,
the agreement): the composition's (task #467). -/
theorem worker_local {mode : CheckMode} {maxNatSize : Nat} {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat}
    {w : WorkerRead} (hw : WorkerFacts sp fs m jobs w)
    (hrun : DeclsRun mode natOpPinSets maxNatSize
      (w.own.toList.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
      (w.reach.ctx.size, mkFEnv (streamEnv w.reach.ctx.toList))
      (w.reach.ctx.size + w.own.size, mkFEnv (streamEnv
        (w.own.toList.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
        (streamEnv w.reach.ctx.toList))))
    (dev : Nat → Module) (i : Nat) (hctx : (dev i).ctx = w.reach.ctx.toList)
    (hdecls : (dev i).decls = w.own.toList.map (fillDecl (fillOf sp fs #[⟨m, w.home.frontier⟩])))
    (srcOf : Declaration → Nat) (hsrc : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, (dev i).src n = srcOf d) :
    ((dev i).context.consts.map (·.toConstantVal.name)).Nodup ∧
    (∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, ∀ n' ∈ declNames d, (dev i).src n = (dev i).src n') ∧
    (∃ q, DeclsRun mode natOpPinSets maxNatSize (dev i).decls ((dev i).ctx.length, mkFEnv (dev i).context) q) ∧
    (∀ k (hk : k < (dev i).ctx.length),
      RecordScoped (streamEnv ((dev i).ctx.take (k + 1))) (dev i).ctx[k]) ∧
    (∀ d ∈ (dev i).ctx, RecordScoped (dev i).context d) ∧ EnvWF (dev i).context := by
  obtain ⟨h0, h1, -, h3, h4⟩ := worker_ctx hw
  have hc : (dev i).context = streamEnv w.reach.ctx.toList := by rw [Module.context, hctx]
  refine ⟨by rw [hc]; exact h4, fun d hd n hn n' hn' => by rw [hsrc d hd n hn, hsrc d hd n' hn'],
    ⟨_, by rw [hdecls, hctx, hc, Array.length_toList]; exact hrun⟩,
    fun k hk => by simp only [hctx] at hk ⊢; exact h0 k hk,
    fun d hd => by rw [hc]; exact h1 d (hctx ▸ hd), by rw [hc]; exact h3⟩

end ConLeche.Driver
