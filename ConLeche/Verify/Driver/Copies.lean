module

public import ConLeche.Verify.Driver.Groups
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.Prepare

/-!
# A module's copies in its own environment

What the composition of the workers (task #501) needs about the copies of a name: where a copy
of a module `M`'s part stands in `M`'s own environment, as `M`'s accepted worker builds it
(`ownEnvOf`, the development's own environment of `M`).

* `copy_own` — **a copy's constant**: a copy of a statement kind at any level `M` loads has, in
  `M`'s own environment, a statement-kind constant of the copy's statement, a theorem where the
  copy or the private constant behind it is one.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-! ## A module's own environment -/

/-- **A module's own records**, the theorems' values in place: the development's `decls`. -/
@[expose] noncomputable def ownDeclsOf (sp : SearchPath) (fs : FS) (M : Name) (w : WorkerRead) :
    List Declaration :=
  w.own.toList.map (fillDecl (fillOf sp fs #[⟨M, w.home.frontier⟩]))

/-- **A module's own environment**: its context with its own records installed. -/
@[expose] noncomputable def ownEnvOf (sp : SearchPath) (fs : FS) (M : Name) (w : WorkerRead) : Env :=
  streamEnv (ownDeclsOf sp fs M w) (streamEnv w.reach.ctx.toList)

/-- **The own records accepted from the context** (`worker_local`'s run). -/
@[expose] def OwnRun (mode : CheckMode) (sp : SearchPath) (fs : FS) (M : Name) (w : WorkerRead) :
    Prop :=
  ∃ q, DeclsRun mode natOpPinSets (ownDeclsOf sp fs M w)
    (w.reach.ctx.size, mkFEnv (streamEnv w.reach.ctx.toList)) q

theorem find?_of_nodup {E : Env} (hn : NodupNames E) {ci : ConstantInfo} (h : ci ∈ E.consts) :
    E.find? ci.name = some ci := by
  unfold Env.find?
  unfold NodupNames at hn
  generalize E.consts = l at hn h
  induction l with
  | nil => cases h
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 h with rfl | h'
    · simp
    · have hne : a.name ≠ ci.name := fun he =>
        hn.1 (he ▸ List.mem_map_of_mem h')
      simp only [List.find?_cons]
      rw [show (a.name == ci.name) = false from beq_false_of_ne hne]
      exact ih hn.2 h'

/-- **An accepted module's own environment names each constant once.** -/
theorem ownEnv_nodup {mode : CheckMode} {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat}
    {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w) (hr : OwnRun mode sp fs M w) :
    NodupNames (ownEnvOf sp fs M w) := by
  obtain ⟨q, hq⟩ := hr
  have hc := declsRun_chain mode hq (PushChain.refl _)
  have he := declsRun_env mode hq
  rw [ownEnvOf, show streamEnv w.reach.ctx.toList = (mkFEnv (streamEnv w.reach.ctx.toList)).env
    from rfl, ← he]
  refine hc.2.2.1 ?_
  have := (worker_ctx hw).2.2.2.2
  simpa [NodupNames, ConstantInfo.name] using this

/-- An own record's constant is in the own environment. -/
theorem own_mem_ownEnv {sp : SearchPath} {fs : FS} {M : Name} {w : WorkerRead} {p : Declaration}
    (hp : p ∈ w.own.toList) {ci : ConstantInfo} (hci : ci ∈ declConstants p) :
    ci ∈ (ownEnvOf sp fs M w).consts :=
  (mem_streamEnv_consts _ _).2 (.inl ⟨_, List.mem_map_of_mem hp, by
    rw [declConstants_fillDecl]; exact hci⟩)

/-- An emitted record is an own record. -/
theorem emitted_own {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {p : Declaration} (hp : p ∈ w.emitted) : p ∈ w.own.toList := by
  rw [hw.own]
  exact (Frontend.hoistNatOpGround_perm _ _).mem_iff.2 (Array.mem_toList_iff.2 hp)

/-! ## A copy's constant -/

/-- **A statement-kind entry's record installs its statement** as a statement kind: a theorem
for a theorem. -/
theorem entryDecl_stmt {e : CEntry} {p : Declaration} (hp : entryDecl e = some p)
    (ht : e.kind.tag < 4) (hsk : e.skipped = false) (hq : e.name ≠ quotSoundName)
    (hs : e.name ≠ sorryAxName) :
    ∃ ci ∈ declConstants p, ci.toConstantVal = ⟨e.name, e.levelParams, e.type⟩ ∧
      ci.isStmtKind = true ∧ (e.kind.tag = 2 → ∃ cv, ci = .thmInfo cv) := by
  rcases e with ⟨⟨n, l, t, k⟩, u⟩
  simp only at hq hs
  cases k with
  | ax u' =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    refine ⟨.axiomInfo ⟨n, l, t⟩, ?_, rfl, rfl, fun h => by simp [CKindF.tag] at h⟩
    simp [declConstants, hq, hs]
  | defn v hh sf =>
    have hsf : sf = "safe" := by simpa [CEntry.skipped, CKindF.skipped] using hsk
    subst hsf
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact ⟨_, List.mem_singleton_self _, rfl, rfl, fun h => by simp [CKindF.tag] at h⟩
  | thm v all =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ => ⟨_, rfl⟩⟩
  | opaq v u' =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact ⟨_, List.mem_singleton_self _, rfl, rfl, fun h => by simp [CKindF.tag] at h⟩
  | _ => simp [CKindF.tag] at ht

/-- **A copy's constant in its module's own environment**: a copy of `M`'s part, at a level a
load reads, of a statement kind (an axiom, definition, theorem or opaque constant), not filtered
out, at neither `Quot.sound` nor `sorryAx`, has in `M`'s own environment a statement-kind
constant of the copy's statement.  It is a theorem where the copy is one, or where the private
part's copy of its name is one (what `proofStatus` reads as a proof at an exported axiom). -/
theorem copy_own {mode : CheckMode} {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat}
    {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w) (hrun : OwnRun mode sp fs M w)
    {s : Spot} (hmod : s.part.mod = M) (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server)
    {r : Region} (hr : PartRegion sp fs s.part r) {cv : ConstantVal} {k : CKindF Name Unit}
    (hst : StmtSkel r s.pos.loc cv k) (hsk0 : s.pos.skipped = false) (htag : k.tag < 4)
    (hq : cv.name ≠ quotSoundName) (hsy : cv.name ≠ sorryAxName) :
    ∃ ci, (ownEnvOf sp fs M w).find? cv.name = some ci ∧ ci.toConstantVal = cv ∧
      ci.isStmtKind = true ∧
      ((k.tag = 2 ∨ ∃ q : Spot, CopyAt sp fs q ∧ q.part = ⟨M, .private⟩ ∧
          q.pos.name = s.pos.name ∧ q.pos.tag = 2) → ∃ cv', ci = .thmInfo cv') := by
  obtain ⟨f, r0, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, hN, hO, hb, hem, hown⟩ :=
    home_records hw
  obtain ⟨loc, sP, s1, hloc, hsP, hs1, hn1, hskq, hskP, hbeh, -⟩ :=
    copy_behind hf hreg hsk hload hcv hmod hs hl hr
  have hskp : sP.kind.skipped = false := by rw [hskP, ← hskq, hsk0]
  have hpos : s.pos.name = cv.name := by
    obtain ⟨s', hs', hn', -⟩ := hst
    rw [hs1] at hs'
    cases hs'
    rw [hn1] at hn'
    exact Option.some.inj hn'
  -- the private skeleton behind the copy: its statement, and its kind
  have hP : nameP r0 sP.name = some cv.name ∧ sP.levelParams.mapM (nameP r0) = some cv.levelParams ∧
      exprP r0 sP.type = some cv.type ∧ sP.kind.tag < 4 ∧ (k.tag = 2 → sP.kind.tag = 2) := by
    rcases hbeh with ⟨hsame, -⟩ | hhid
    · obtain ⟨k', ⟨sP', hsP', hn, hl', ht, hkm⟩, htk, -⟩ := hsame cv k hst
      rw [hsP] at hsP'
      cases hsP'
      have hkt : sP.kind.tag = k.tag := by rw [(CKindF.mapM_tag hkm).1, htk]
      exact ⟨hn, hl', ht, by omega, fun h => by omega⟩
    · obtain ⟨⟨u, rfl⟩, hn, hl', ht, htag'⟩ := hhid cv k hst
      exact ⟨hn, hl', ht, by omega, fun h => by simp [CKindF.tag] at h⟩
  obtain ⟨hn, hlp, hty, htP, hthm⟩ := hP
  obtain ⟨E, e₁, hE, he₁, hee⟩ := hown loc sP hloc hsP hskp
  obtain ⟨hn', hl', ht'⟩ := lazyEntry_stmt hE
  rw [hn] at hn'; rw [hlp] at hl'; rw [hty] at ht'
  simp only [Option.some.injEq] at hn' hl' ht'
  obtain ⟨hskE, htagE⟩ := lazyEntry_kind hE
  have hk : e₁.kind = E.kind := by rw [show e₁.kind = e₁.toCEntryF.kind from rfl, hee]
  have hsk₁ : e₁.skipped = false := by simp only [CEntry.skipped, hk, hskE, hskp]
  have ht₁ : e₁.kind.tag < 4 := by rw [hk, htagE]; exact htP
  have hst₁ : (⟨e₁.name, e₁.levelParams, e₁.type⟩ : ConstantVal) = cv := by
    obtain ⟨n, l, t⟩ := cv
    simp only at hn' hl' ht'
    rw [show e₁.name = e₁.toCEntryF.name from rfl, show e₁.levelParams = e₁.toCEntryF.levelParams
      from rfl, show e₁.type = e₁.toCEntryF.type from rfl, hee, hn', hl', ht']
  obtain ⟨p, hp, hpe⟩ := home_entry hN hO hb hem he₁ hsk₁ (by omega)
  obtain ⟨ci, hci, hcv', hks, hth⟩ := entryDecl_stmt hpe ht₁ hsk₁
    (by rw [show e₁.name = cv.name from congrArg ConstantVal.name hst₁]; exact hq)
    (by rw [show e₁.name = cv.name from congrArg ConstantVal.name hst₁]; exact hsy)
  rw [hst₁] at hcv'
  have hmem := own_mem_ownEnv (sp := sp) (fs := fs) (M := M) (emitted_own hw hp) hci
  have hfind := find?_of_nodup (ownEnv_nodup hw hrun) hmem
  rw [show ci.name = cv.name by rw [ConstantInfo.name, hcv']] at hfind
  refine ⟨ci, hfind, hcv', hks, fun hthm' => hth ?_⟩
  rw [hk, htagE]
  rcases hthm' with h2 | ⟨q, hqc, hqp, hqn, hqt⟩
  · exact hthm h2
  · rw [← hqt]
    exact (private_tag hf hreg hsk hskels hcn hqc hqp hloc hsP (by rw [hqn, hpos]; exact hn)).symm

/-! ## An exported copy is behind a private one -/

/-- **The name positions are complete**: every constant of the part's skeleton has a position,
at its location, named as its skeleton names it. -/
theorem namePositionsAt_complete {r : Region} {root : UInt64} {t : NamePositions} {sk : ModSkel}
    (h : namePositionsAt r root = some t) (hsk : moduleSkel r root = some sk) {loc : Nat}
    (hloc : loc ∈ sk.consts) {s : CEntryF UInt64 UInt64} (hs : constSkel r loc = some s)
    {n : Name} (hn : nameP r s.name = some n) :
    ∃ q ∈ t.consts, q.loc = loc ∧ q.name = n := by
  simp only [namePositionsAt] at h
  obtain ⟨sk', hsk', h⟩ := bind_some_left h
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨imps, -, h⟩ := bind_some_left h
  obtain ⟨cs, hcs, h⟩ := bind_some_left h
  split at h
  rotate_left
  · cases h
  simp only [pure, Option.some.injEq] at h
  subst h
  obtain ⟨q, hq, hql⟩ := mapM_mem hcs hloc
  simp only [namePosition, hs, hn, Option.bind_eq_bind, Option.bind_some, pure,
    Option.some.injEq] at hql
  subst hql
  exact ⟨_, by simpa using hq, rfl, rfl⟩

/-- A part's name table on the snapshot is one, where the module's private files read. -/
theorem partNames_unique {sp : SearchPath} {fs : FS} {M : Name} {f : ModFiles}
    (hf : ModelIO.CanGive (readFiles sp M .private) fs (.ok f)) {L : OLeanLevel}
    {t t' : NamePositions} (h : PartNames sp fs ⟨M, L⟩ t) (h' : PartNames sp fs ⟨M, L⟩ t') :
    t = t' := by
  have e1 := readPartNames_of_all hf h
  have e2 := readPartNames_of_all hf h'
  rw [e1] at e2
  exact Option.some.inj e2

/-- **A worker's reads, on the snapshot**: its own private part's table, the header fixpoint of
its header, the loaded parts' tables (`keys` the parts in the load order) under the name index,
and freshness. -/
theorem workerReads_spec {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs') :
    PartNames sp fs ⟨m, .private⟩ wr.own ∧
    ModelIO.CanGive (headerFixpoint (moduleImports sp) wr.own.header.isModule
      wr.own.header.imports) fs (.ok wr.loads) ∧
    (∃ parts : List NamePositions,
      parts.length = ((wr.loads.order.zip wr.loads.flags).toList.map
        fun (n, fl) => (n, fl.level)).length ∧
      (∀ (i : Nat) (t : NamePositions), parts[i]? = some t → ∃ x,
        ((wr.loads.order.zip wr.loads.flags).toList.map fun (n, fl) => (n, fl.level))[i]? = some x ∧
        ModelIO.CanGive (readPartNames sp x) fs (.ok t)) ∧
      wr.index = nameIndexOf parts.toArray) ∧
    freshOk m wr.loads wr.index wr.own = .ok () := by
  simp only [workerReads, ModelIO.bind_ok] at h
  obtain ⟨a, _, ha, h⟩ := h
  rcases a with e | own
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨b, _, hb, h⟩ := h
  rcases b with e | ld
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨c, _, hc, h⟩ := h
  rcases c with e | parts
  · simp at h
  simp only at h
  generalize importsModulesOk _ _ _ _ _ = z at h
  rcases z with e | u
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨d, _, -, h⟩ := h
  rcases d with e | infos
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨d, _, -, h⟩ := h
  rcases d with e | hinfos
  · simp at h
  simp only at h
  generalize (List.forM _ _ : Except CheckError Unit) = z at h
  rcases z with e | u
  · simp at h
  simp only at h
  cases hfr : freshOk m ld (nameIndexOf parts.toArray) own with
  | error e => simp [hfr] at h
  | ok u =>
  simp only [hfr, ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  have hc' : (mapExcept (readPartNames sp) ((ld.order.zip ld.flags).toList.map
      fun (n, fl) => (n, fl.level)) : ModelIO _) fs _ (.ok (.ok parts)) _ := hc
  obtain ⟨hlen, hget⟩ := mapExcept_getElem hc'
  exact ⟨⟨_, _, ha⟩, ⟨_, _, hb⟩, ⟨parts, hlen, hget, rfl⟩, hfr⟩

/-- The private part's name table holds the worker's own table. -/
theorem worker_ownTable {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) : PartNames sp fs ⟨M, .private⟩ w.reads.own := by
  obtain ⟨_, _, h⟩ := hw.reads
  exact (workerReads_spec h).1

/-- **An exported copy is behind a private one**: a copy of `M`'s exported part has a copy of its
name in `M`'s private part. -/
theorem exported_behind {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {s : Spot} (hmod : s.part.mod = M) (hs : CopyAt sp fs s)
    (hl : s.part.level = .exported) :
    ∃ q : Spot, CopyAt sp fs q ∧ q.part = ⟨M, .private⟩ ∧ q.pos.name = s.pos.name := by
  obtain ⟨f, r0, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, -⟩ := home_records hw
  have hr1 : PartRegion sp fs s.part (Region.single f.exported) := by
    obtain ⟨⟨m, L⟩, pos⟩ := s
    simp only at hmod hl
    subst hmod hl
    obtain ⟨_, _, hf'⟩ := hf
    exact ⟨f.upTo .exported, f.exported.moduleDataAddr, (readFiles_of_all .exported hf').canGive,
      rfl⟩
  obtain ⟨loc, sP, s1, hloc, hsP, -, -, -, -, -, hnP⟩ :=
    copy_behind hf hreg hsk hload hcv hmod hs (by rw [hl]; decide) hr1
  have ht := worker_ownTable hw
  have hnt := readPartNames_of_all hf ht
  simp only [ModFiles.upTo, readNamePositions, hreg, Option.bind_eq_bind, Option.bind_some] at hnt
  obtain ⟨q, hq, -, hqn⟩ := namePositionsAt_complete hnt hsk hloc hsP hnP
  exact ⟨⟨⟨M, .private⟩, q⟩, ⟨_, ht, hq⟩, rfl, hqn⟩

/-- **A module's private part holds every name its exported part does.** -/
theorem exported_sub_private {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {te tp : NamePositions}
    (he : PartNames sp fs ⟨M, .exported⟩ te) (hp : PartNames sp fs ⟨M, .private⟩ tp)
    {q : NamePosition} (hq : q ∈ te.consts) : ∃ q' ∈ tp.consts, q'.name = q.name := by
  obtain ⟨q', ⟨t', ht', hq'⟩, hqp, hqn⟩ :=
    exported_behind hw (s := ⟨⟨M, .exported⟩, q⟩) rfl ⟨te, he, hq⟩ rfl
  obtain ⟨f, -, -, -, -, hf, -⟩ := home_records hw
  rw [hqp] at ht'
  rw [partNames_unique hf ht' hp] at hq'
  exact ⟨_, hq', hqn⟩

/-! ## An own statement does not read its own name -/

/-- **What `constsResolveF` asks stored**: every name an expression reads. -/
theorem constsResolveF_readNames {fe : FEnv} :
    ∀ {e : Expr}, e.constsResolveF fe = true → ∀ n ∈ e.readNames, (fe.find? n).isSome = true
  | .bvar _, _, n, h => by simp [Expr.readNames] at h
  | .sort _, _, n, h => by simp [Expr.readNames] at h
  | .lit (.natVal _), he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp_all
  | .lit (.strVal _), he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  | .const m _, he, n, h => by
    simp only [Expr.readNames, List.mem_singleton] at h
    subst h; exact he
  | .fvar _ ty, he, n, h => constsResolveF_readNames (e := ty) he n h
  | .app f a, he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_append] at h
    rcases h with h | h
    · exact constsResolveF_readNames he.1 n h
    · exact constsResolveF_readNames he.2 n h
  | .lam ty b, he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_append] at h
    rcases h with h | h
    · exact constsResolveF_readNames he.1 n h
    · exact constsResolveF_readNames he.2 n h
  | .forallE ty b, he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_append] at h
    rcases h with h | h
    · exact constsResolveF_readNames he.1 n h
    · exact constsResolveF_readNames he.2 n h
  | .letE ty v b, he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_append] at h
    rcases h with (h | h) | h
    · exact constsResolveF_readNames he.1.1 n h
    · exact constsResolveF_readNames he.1.2 n h
    · exact constsResolveF_readNames he.2 n h
  | .proj m _ x, he, n, h => by
    simp only [Expr.constsResolveF, Bool.and_eq_true] at he
    simp only [Expr.readNames, List.mem_cons] at h
    rcases h with rfl | h
    · exact he.1
    · exact constsResolveF_readNames he.2 n h

-- The walk splits at each of the check's guards and carries the rest of the clause into both
-- halves, as `checkConstantValC_fresh`'s.
set_option maxHeartbeats 400000 in
/-- **A checked statement is fresh and resolves.** -/
theorem checkConstantValC_fresh_res (mode : CheckMode) (fe : FEnv)
    (cv : ConstantVal) {a b c : Bool} :
    Yields (checkConstantValC mode fe cv a b c)
      (fun _ => fe.find? cv.name = none ∧ constsResolveFC fe cv.type = true) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.pure ⟨Option.not_isSome_iff_eq_none.mp (by assumption), by simp_all⟩

/-- The statement a record checks with `checkConstantValC`: a definition's, theorem's, opaque
constant's, or an axiom's at no `Quot.sound`. -/
@[expose] def StmtRecord (d : Declaration) (cv : ConstantVal) : Prop :=
  (∃ v h, d = .defnDecl cv v h) ∨ (∃ v, d = .thmDecl cv v) ∨ (∃ v, d = .opaqueDecl cv v) ∨
    (d = .axiomDecl cv ∧ cv.name ≠ quotSoundName)

/-- **An accepted statement record is fresh and its type resolves**, at the step's start. -/
theorem checkDeclStepC_stmt {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {d : Declaration} {cv : ConstantVal} (hd : StmtRecord d cv) :
    Yields (checkDeclStepC mode pins fe d)
      (fun _ => fe.find? cv.name = none ∧ constsResolveFC fe cv.type = true) := by
  unfold checkDeclStepC checkDeclC
  ybind
  refine Yields.bind' (Q := fun _ => fe.find? cv.name = none ∧ constsResolveFC fe cv.type = true)
    ?_ fun _ h => Yields.const h
  unfold checkDeclKindC
  rcases hd with ⟨v, h, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨rfl, hq⟩
  · exact Yields.bind' (checkConstantValC_fresh_res mode fe cv) fun _ h => Yields.const h
  · exact Yields.bind' (checkConstantValC_fresh_res mode fe cv) fun _ h => Yields.const h
  · exact Yields.bind' (checkConstantValC_fresh_res mode fe cv) fun _ h => Yields.const h
  · simp only [hq, ↓reduceIte]
    exact Yields.bind' (checkConstantValC_fresh_res mode fe cv) fun _ h => Yields.const h

/-- **An accepted statement record's type does not read its own name.** -/
theorem declsRun_stmt_fresh {mode : CheckMode} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins ds p q) :
    ∀ d ∈ ds, ∀ cv, StmtRecord d cv → cv.name ∉ cv.type.readNames := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    intro d hd cv hcv
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      obtain ⟨hf, hr⟩ := checkDeclStepC_stmt hcv _ _ _ hC
      rw [constsResolveFC_spec] at hr
      intro hn
      have := constsResolveF_readNames hr _ hn
      rw [hf] at this
      cases this
    · exact ih d hd cv hcv

/-- **An own statement record's type does not read its own name**, at an accepted worker. -/
theorem own_stmt_fresh {mode : CheckMode} {sp : SearchPath} {fs : FS} {M : Name}
    {w : WorkerRead} (hrun : OwnRun mode sp fs M w) {d : Declaration}
    (hd : d ∈ ownDeclsOf sp fs M w) {cv : ConstantVal} (hcv : StmtRecord d cv) :
    cv.name ∉ cv.type.readNames := by
  obtain ⟨q, hq⟩ := hrun
  exact declsRun_stmt_fresh hq d hd cv hcv

end ConLeche.Driver
