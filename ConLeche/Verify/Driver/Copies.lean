module

import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Driver.Provenance
public import ConLeche.Verify.Driver.ReachFrom
public import ConLeche.Verify.Driver.Worker

/-!
# A module's copies in its own environment

What the composition of the workers (task #501) needs about the copies of a name: where a copy
of a module `M`'s part stands in `M`'s own environment, as `M`'s accepted worker builds it
(`ownEnvOf`, the development's own environment of `M`).

* `exported_behind`, `exported_sub_private` — an exported copy has a private copy of its name.
* `own_stmt_fresh` — an own statement record's type does not read its own name (the accepted
  step checks it fresh, its type resolving before it).
* `own_type_stored`, `own_reads_ctx` — what an own record reads is stored: a statement's type's
  names in the own environment, and every read the reach's roots keep in the context.
* `partNames_eq` — a part's name table on the snapshot is one.
* `homeView_index` — a home's view (`HomeView`) is its worker's name index: the home's own
  private part first, then each name's first loaded copy.
* `recordReads_sound`, `recordReads_complete`, `Presents.reads` — `recordReads` is exactly the
  names a record's laws read, so a presentation reads what its record reads, or less.
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

/-! ## An own record's reads are stored -/

/-- A name an environment stores stays stored where constants are prepended. -/
theorem find?_isSome_append {E E' : Env} {new : List ConstantInfo}
    (h : E'.consts = new ++ E.consts) {n : Name} (hn : (E.find? n).isSome = true) :
    (E'.find? n).isSome = true := by
  simp only [Env.find?, List.find?_isSome] at hn ⊢
  obtain ⟨c, hc, he⟩ := hn
  exact ⟨c, by rw [h]; exact List.mem_append_right _ hc, he⟩

/-- **The names an accepted statement record's type reads are stored after the run.** -/
theorem declsRun_stmt_stored {mode : CheckMode} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins ds p q) (hp : p.2 = mkFEnv p.2.env) :
    ∀ d ∈ ds, ∀ cv, StmtRecord d cv → ∀ n ∈ cv.type.readNames, (q.2.env.find? n).isSome = true := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    have hall := declsRun_chain mode (DeclsRun.cons hstep rest) (env := p.2.env) (hp ▸ PushChain.refl _)
    obtain ⟨fe₁, s₁, hq₁, hC⟩ := declStep_ok hstep
    have h₁ : PushChain p.2.env p₁.2 := by
      have := declsRun_chain mode (DeclsRun.cons hstep (DeclsRun.nil p₁)) (env := p.2.env)
        (hp ▸ PushChain.refl _)
      exact this
    intro d hd cv hcv
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨-, hr⟩ := checkDeclStepC_stmt hcv _ _ _ hC
      rw [constsResolveFC_spec] at hr
      intro n hn
      have h0 := constsResolveF_readNames hr n hn
      rw [hp, mkFEnv_find?] at h0
      obtain ⟨new, hnew, -⟩ := hall.2.1
      exact find?_isSome_append hnew h0
    · exact ih h₁.canon d hd cv hcv

/-- **The names an own statement record's type reads are stored** in the own environment. -/
theorem own_type_stored {mode : CheckMode} {sp : SearchPath} {fs : FS} {M : Name}
    {w : WorkerRead} (hrun : OwnRun mode sp fs M w) {d : Declaration}
    (hd : d ∈ ownDeclsOf sp fs M w) {cv : ConstantVal} (hcv : StmtRecord d cv) :
    ∀ n ∈ cv.type.readNames, ((ownEnvOf sp fs M w).find? n).isSome = true := by
  obtain ⟨q, hq⟩ := hrun
  have := declsRun_stmt_stored hq rfl d hd cv hcv
  rw [declsRun_env mode hq] at this
  exact this

/-- A name the context stores is stored in the own environment. -/
theorem ctx_stored_own {sp : SearchPath} {fs : FS} {M : Name} {w : WorkerRead} {n : Name}
    (h : ((streamEnv w.reach.ctx.toList).find? n).isSome = true) :
    ((ownEnvOf sp fs M w).find? n).isSome = true := by
  obtain ⟨d, hd, hn⟩ := streamEnv_find_mem h
  simp only [declNames, List.mem_map] at hn
  obtain ⟨ci, hci, rfl⟩ := hn
  simp only [Env.find?, List.find?_isSome]
  exact ⟨ci, (mem_streamEnv_consts _ _).2 (.inr ((mem_streamEnv_consts _ _).2 (.inl ⟨d, hd, hci⟩))),
    by simp [ConstantInfo.name]⟩

/-- **What an own record reads is stored in the context**, where the reach's roots keep it: no
own name, and loaded or no name of a pinned own constant's fast path (`ownRoots`' filter). -/
theorem own_reads_ctx {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {p : Declaration} (hp : p ∈ w.emitted) {y : Name}
    (hy : y ∈ recordReads p) (ho : (ownNames w.home).contains y = false)
    (hk : (w.reads.index.first.contains y || !(w.home.constants.foldl
      (fun s c => (Modular.pinFootprint c.name).foldl (fun s n => s.insert n) s)
      ({} : Std.HashSet Name)).contains y) = true) :
    ((streamEnv w.reach.ctx.toList).find? y).isSome = true := by
  obtain ⟨_, _, hr⟩ := hw.reach
  refine (reach_ok hr).2.2.2.2 y ?_ ho
  unfold ownRoots
  refine Array.mem_append.2 (.inl (Array.mem_filter.2 ⟨Array.mem_append.2 (.inl ?_), hk⟩))
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Declaration) (acc : Array Name), y ∈ acc ∨ (∃ d ∈ l, y ∈ recordReads d) →
      y ∈ l.foldl (fun acc d => acc ++ recordReads d) acc := by
    intro l
    induction l with
    | nil => intro acc h; simpa using h
    | cons a l ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | ⟨d, hd, hyd⟩
      · exact .inl (Array.mem_append.2 (.inl h))
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact .inl (Array.mem_append.2 (.inr hyd))
        · exact .inr ⟨d, hd, hyd⟩
  exact key _ _ (.inr ⟨p, Array.mem_toList_iff.2 hp, hy⟩)

/-! ## A part's name table on the snapshot is one -/

/-- A module's files read at a location are the snapshot's. -/
theorem readFilesAt_unique {fs : FS} {loc : Located} {m : Name} {L : OLeanLevel}
    {hs₁ hs₁' hs₂ hs₂' : HS} {f₁ f₂ : ModFiles}
    (h₁ : (readFilesAt loc m L : ModelIO _) fs hs₁ (.ok (.ok f₁)) hs₁')
    (h₂ : (readFilesAt loc m L : ModelIO _) fs hs₂ (.ok (.ok f₂)) hs₂') : f₁ = f₂ :=
  (Except.ok.inj (((readFilesAt_isDet loc m L fs).of_ok h₁).ok h₂)).symm

/-- **A part's name table on the snapshot is one.** -/
theorem partNames_eq {sp : SearchPath} {fs : FS} {k : PartKey} {t t' : NamePositions}
    (h : PartNames sp fs k t) (h' : PartNames sp fs k t') : t = t' := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, h'⟩ := h'
  simp only [readPartNames, ModelIO.bind_ok] at h h'
  obtain ⟨y, _, hy, h⟩ := h
  obtain ⟨y', _, hy', h'⟩ := h'
  rcases y with e | loc
  · simp at h
  rcases y' with e | loc'
  · simp at h'
  obtain rfl : loc' = loc := Except.ok.inj ((findModule_ok hy).ok hy')
  simp only [readPartNamesAt, namesOf, ModelIO.bind_ok] at h h'
  obtain ⟨z, _, hz, h⟩ := h
  obtain ⟨z', _, hz', h'⟩ := h'
  rcases z with e | f
  · simp at h
  rcases z' with e | f'
  · simp at h'
  obtain rfl := readFilesAt_unique hz hz'
  cases hn : readNamePositions f k.level with
  | none => simp [hn] at h
  | some ps =>
  simp only [hn, ModelIO.pure_iff, Except.ok.injEq] at h h'
  exact h.1.trans h'.1.symm

/-! ## A home's view is its name index -/

/-- **The first copy of a name in some parts**, in their order. -/
@[expose] def firstIn : List (PartKey × NamePositions) → Name → Option Spot
  | [], _ => none
  | (k, t) :: rest, y =>
    match t.consts.toList.find? (·.name == y) with
    | some q => some ⟨k, q⟩
    | none => firstIn rest y

/-- **The first copy of a name in some parts**, as a copy: the part's position from `i` on and
the name position's in the part. -/
@[expose] def firstCopyIn : List NamePositions → Nat → Name → Option Copy
  | [], _, _ => none
  | t :: ts, i, y =>
    match t.consts.toList.findIdx? (·.name == y) with
    | some k => some ⟨i, k⟩
    | none => firstCopyIn ts (i + 1) y

theorem viewStep_list (k : PartKey) (y : Name) :
    ∀ (l : List NamePosition) (v : Std.HashMap Name Spot),
      (l.foldl (fun (v : Std.HashMap Name Spot) q =>
        if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v)[y]? =
        (v[y]?).or ((l.find? (·.name == y)).map (⟨k, ·⟩))
  | [], v => by simp
  | q :: l, v => by
    simp only [List.foldl_cons, List.find?_cons]
    rw [viewStep_list k y l]
    by_cases hc : v.contains q.name = true
    · simp only [hc, ite_true]
      by_cases hq : (q.name == y) = true
      · have : q.name = y := beq_iff_eq.1 hq
        subst this
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hc
        simp [hs]
      · simp [hq]
    · simp only [hc, Bool.false_eq_true, ite_false, Std.HashMap.getElem?_insert]
      by_cases hq : (q.name == y) = true
      · have : q.name = y := beq_iff_eq.1 hq
        subst this
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        simp only [Option.not_isSome_iff_eq_none] at hc
        simp [hc]
      · simp [hq]

theorem viewStep_get (v : Std.HashMap Name Spot) (k : PartKey) (t : NamePositions) (y : Name) :
    (viewStep v k t)[y]? = (v[y]?).or ((t.consts.toList.find? (·.name == y)).map (⟨k, ·⟩)) := by
  rw [viewStep, ← Array.foldl_toList, viewStep_list]

theorem viewFold_get (y : Name) :
    ∀ (l : List (PartKey × NamePositions)) (v : Std.HashMap Name Spot),
      (l.foldl (fun v kt => viewStep v kt.1 kt.2) v)[y]? = (v[y]?).or (firstIn l y)
  | [], v => by simp [firstIn]
  | (k, t) :: l, v => by
    simp only [List.foldl_cons]
    rw [viewFold_get y l, viewStep_get]
    simp only [firstIn]
    cases v[y]? <;> cases t.consts.toList.find? (·.name == y) <;> simp

/-- The name index's inner fold over one part. -/
theorem nameIndex_inner (i : Nat) (y : Name) :
    ∀ (l : List NamePosition) (first : Std.HashMap Name Copy) (more : Array (Name × Copy)) (k : Nat),
      (l.foldl (fun (acc : Std.HashMap Name Copy × Array (Name × Copy) × Nat) q =>
        let (first, more, k) := acc
        match first[q.name]? with
        | none => (first.insert q.name ⟨i, k⟩, more, k + 1)
        | some _ => (first, more.push (q.name, ⟨i, k⟩), k + 1)) (first, more, k)).1[y]? =
        (first[y]?).or ((l.findIdx? (·.name == y)).map fun j => ⟨i, k + j⟩)
  | [], first, more, k => by simp
  | q :: l, first, more, k => by
    simp only [List.foldl_cons, List.findIdx?_cons]
    cases hf : first[q.name]? with
    | none =>
      simp only []
      rw [nameIndex_inner i y l, Std.HashMap.getElem?_insert]
      by_cases hq : (q.name == y) = true
      · have : q.name = y := beq_iff_eq.1 hq
        subst this
        simp [hf]
      · simp only [hq, Bool.false_eq_true, ite_false, Option.map_map]
        congr 2
        funext j
        simp only [Function.comp, Copy.mk.injEq]
        exact ⟨trivial, by omega⟩
    | some c =>
      simp only []
      rw [nameIndex_inner i y l]
      by_cases hq : (q.name == y) = true
      · have : q.name = y := beq_iff_eq.1 hq
        subst this
        simp [hf]
      · simp only [hq, Bool.false_eq_true, ite_false, Option.map_map]
        congr 2
        funext j
        simp only [Function.comp, Copy.mk.injEq]
        exact ⟨trivial, by omega⟩

/-- The name index's outer fold over the parts. -/
theorem nameIndex_outer (y : Name) :
    ∀ (ps : List NamePositions) (first : Std.HashMap Name Copy) (more : Array (Name × Copy)) (i : Nat),
      (ps.foldl (fun (acc : Std.HashMap Name Copy × Array (Name × Copy) × Nat) p =>
        let (first, more, i) := acc
        let (first, more, _) := p.consts.foldl
          (fun (acc : Std.HashMap Name Copy × Array (Name × Copy) × Nat) q =>
            let (first, more, k) := acc
            match first[q.name]? with
            | none => (first.insert q.name ⟨i, k⟩, more, k + 1)
            | some _ => (first, more.push (q.name, ⟨i, k⟩), k + 1)) (first, more, 0)
        (first, more, i + 1)) (first, more, i)).1[y]? =
        (first[y]?).or (firstCopyIn ps i y)
  | [], first, more, i => by simp [firstCopyIn]
  | p :: ps, first, more, i => by
    simp only [List.foldl_cons]
    rw [nameIndex_outer y ps]
    have hin := nameIndex_inner i y p.consts.toList first more 0
    rw [Array.foldl_toList] at hin
    rw [hin]
    simp only [firstCopyIn, Nat.zero_add]
    cases first[y]? <;> cases p.consts.toList.findIdx? (·.name == y) <;> simp

/-- **The name index's first copy** is the parts' first copy. -/
theorem nameIndexOf_first (ps : List NamePositions) (y : Name) :
    (nameIndexOf ps.toArray).first[y]? = firstCopyIn ps 0 y := by
  have := nameIndex_outer y ps (Std.HashMap.emptyWithCapacity
    (ps.toArray.foldl (fun n p => n + p.consts.size) 0)) #[] 0
  simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.none_or] at this
  rw [← this]
  simp only [nameIndexOf, List.foldl_toArray']
  rfl

theorem find?_eq_findIdx? {α : Type} (p : α → Bool) :
    ∀ l : List α, l.find? p = (l.findIdx? p).bind (l[·]?)
  | [] => rfl
  | a :: l => by
    simp only [List.find?_cons, List.findIdx?_cons]
    cases hp : p a
    · simp only [Bool.false_eq_true, ite_false]
      rw [find?_eq_findIdx? p l]
      cases l.findIdx? p <;> simp
    · simp

theorem findIdx?_spec {α : Type} {p : α → Bool} :
    ∀ {l : List α} {j : Nat}, l.findIdx? p = some j → ∃ a, l[j]? = some a ∧ p a = true
  | [], _, h => by simp at h
  | a :: l, j, h => by
    rw [List.findIdx?_cons] at h
    cases hp : p a
    · simp only [hp, Bool.false_eq_true, ite_false] at h
      obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b, hb, hpb⟩ := findIdx?_spec hj'
      exact ⟨b, by simpa using hb, hpb⟩
    · simp only [hp, ite_true, Option.some.injEq] at h
      subst h
      exact ⟨a, rfl, hp⟩

/-- **The first copy in some parts, by its copy**: the parts' first copy of `y` is the copy the
first-copy search finds, at the part's key. -/
theorem firstIn_zip (y : Name) :
    ∀ (ps : List NamePositions) (ks : List PartKey) (i : Nat), ks.length = ps.length →
      (firstIn (ks.zip ps) y = (firstCopyIn ps i y).bind fun cp =>
        (ks[cp.mod - i]?).bind fun k => (ps[cp.mod - i]?).bind fun t =>
          (t.consts[cp.pos]?).map fun q => ⟨k, q⟩) ∧
      ∀ cp, firstCopyIn ps i y = some cp → i ≤ cp.mod ∧ ∃ t q, ps[cp.mod - i]? = some t ∧
        t.consts[cp.pos]? = some q ∧ q.name = y
  | [], ks, i, h => by
    cases ks with
    | nil => exact ⟨rfl, fun cp h => by simp [firstCopyIn] at h⟩
    | cons _ _ => simp at h
  | t :: ps, ks, i, h => by
    cases ks with
    | nil => simp at h
    | cons k ks =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      obtain ⟨ih1, ih2⟩ := firstIn_zip y ps ks (i + 1) h
      simp only [List.zip_cons_cons, firstIn, firstCopyIn]
      rw [find?_eq_findIdx?]
      cases hj : t.consts.toList.findIdx? (·.name == y) with
      | some j =>
        obtain ⟨q, hq, hqy⟩ := findIdx?_spec hj
        simp only [Option.bind_some, Nat.sub_self, List.getElem?_cons_zero]
        refine ⟨?_, fun cp hcp => ?_⟩
        · simp only [Array.getElem?_toList] at hq
          simp [hq]
        · cases hcp
          refine ⟨Nat.le_refl _, t, q, by simp, by simpa using hq, beq_iff_eq.1 hqy⟩
      | none =>
        simp only [Option.bind_none]
        refine ⟨?_, fun cp hcp => ?_⟩
        · rw [ih1]
          cases hc : firstCopyIn ps (i + 1) y with
          | none => rfl
          | some cp =>
            obtain ⟨hle, -⟩ := ih2 cp hc
            simp only [Option.bind_some]
            have : cp.mod - i = (cp.mod - (i + 1)) + 1 := by omega
            rw [this]
            simp
        · obtain ⟨hle, t', q, ht', hq, hqy⟩ := ih2 cp hcp
          have : cp.mod - i = (cp.mod - (i + 1)) + 1 := by omega
          refine ⟨by omega, t', q, ?_, hq, hqy⟩
          rw [this]; simpa using ht'

/-- Freshness: no name of the own private part is loaded. -/
theorem freshOk_spec {m : Name} {ld : Loads} {ix : NameIndex} {own : NamePositions}
    (h : freshOk m ld ix own = .ok ()) {q : NamePosition} (hq : q ∈ own.consts) :
    ix.first[q.name]? = none := by
  unfold freshOk at h
  cases hf : own.consts.find? (ix.first.contains ·.name) with
  | some q' => simp [hf] at h
  | none =>
    have := Array.find?_eq_none.1 hf q hq
    cases h' : ix.first[q.name]? with
    | none => rfl
    | some c =>
      exfalso; apply this
      rw [Std.HashMap.contains_eq_isSome_getElem?, h']; rfl

/-- **A home's view is its name index** (`viewOf`'s, by the specification, against the worker at
the home on the same snapshot): a name the view holds is the home's own private part's, and then
no loaded module's (freshness), or the view's copy is the home's importer copy, the name
index's first copy at the part its module is loaded at (`importerSpot`'s spot); a name the view
does not hold no loaded module holds.  Header-fixpoint determinism is a hypothesis
(`hdet`, `Loads.lean`'s). -/
theorem homeView_index {sp : SearchPath} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w)
    (hdet : ∀ ld ld', ModelIO.CanGive (headerFixpoint (moduleImports sp)
        w.reads.own.header.isModule w.reads.own.header.imports) fs (.ok ld) →
      ModelIO.CanGive (headerFixpoint (moduleImports sp)
        w.reads.own.header.isModule w.reads.own.header.imports) fs (.ok ld') → ld = ld')
    {v : Std.HashMap Name Spot} (hv : HomeView sp fs M v) (y : Name) :
    (∀ s, v[y]? = some s →
      (s.part = ⟨M, .private⟩ ∧ w.reads.index.first[y]? = none) ∨
      ∃ cp q, w.reads.index.first[y]? = some cp ∧ w.reads.index.at cp = some q ∧
        s = ⟨⟨w.reads.loads.nameAt cp.mod,
          ((w.reads.loads.flags[cp.mod]?).getD default).level⟩, q⟩) ∧
    (v[y]? = none → w.reads.index.first[y]? = none) := by
  obtain ⟨own', ld', ts, hown', hld', hlen, hts, rfl⟩ := hv
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨hown, hld, ⟨parts, hplen, hparts, hix⟩, hfresh⟩ := workerReads_spec hr
  obtain rfl := partNames_eq hown' hown
  obtain rfl := hdet _ _ hld' hld
  generalize hK : ((w.reads.loads.order.zip w.reads.loads.flags).toList.map
    fun (x : Name × LoadFlags) => (⟨x.1, x.2.level⟩ : PartKey)) = K
  have hvk : viewKeys M w.reads.loads = ⟨M, .private⟩ :: K := by rw [← hK]; rfl
  rw [hvk] at hlen hts ⊢
  cases ts with
  | nil => simp at hlen
  | cons t0 ts' =>
  obtain rfl : t0 = w.reads.own := partNames_eq (hts _ _ (by simp)) hown
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
  have hKlen : K.length = parts.length := by rw [hplen, ← hK]; simp
  have hts' : ts' = parts := by
    apply List.ext_getElem (by omega)
    intro i h1 h2
    have hKi : i < K.length := by omega
    have hpt := hts K[i] ts'[i] (List.mem_cons_of_mem _ (List.mem_iff_getElem.2
      ⟨i, by simp; omega, by simp⟩))
    obtain ⟨x, hx, hxr⟩ := hparts i parts[i] (List.getElem?_eq_getElem h2)
    have hxK : x = (K[i].mod, K[i].level) := by
      subst hK
      simp only [List.getElem?_map, List.getElem_map] at hx ⊢
      rw [List.getElem?_eq_getElem (by simpa using hKi)] at hx
      exact (Option.some.inj hx).symm
    subst hxK
    exact partNames_eq hpt hxr
  subst hts'
  rw [viewFold_get, List.zip_cons_cons]
  simp only [Std.HashMap.getElem?_empty, Option.none_or, firstIn]
  rw [hix, nameIndexOf_first]
  rw [find?_eq_findIdx?]
  cases hj : w.reads.own.consts.toList.findIdx? (·.name == y) with
  | some j =>
    obtain ⟨q, hq, hqy⟩ := findIdx?_spec hj
    have hqm : q ∈ w.reads.own.consts := Array.mem_toList_iff.1 (List.mem_of_getElem? hq)
    have hnone := freshOk_spec hfresh hqm
    rw [beq_iff_eq.1 hqy] at hnone
    rw [← nameIndexOf_first, ← hix]
    simp only [Option.bind_some, hq, Option.some.injEq, hnone, reduceCtorEq]
    exact ⟨fun s hs => .inl ⟨by rw [← hs], trivial⟩, fun h => h.elim⟩
  | none =>
    simp only [Option.bind_none]
    obtain ⟨h1, h2⟩ := firstIn_zip y ts' K 0 hKlen
    rw [h1]
    cases hc : firstCopyIn ts' 0 y with
    | none => simp
    | some cp =>
      obtain ⟨-, t, q, ht, hq, -⟩ := h2 cp hc
      simp only [Nat.sub_zero] at ht
      have hKm : cp.mod < K.length := by
        rw [hKlen]; exact (List.getElem?_eq_some_iff.1 ht).1
      obtain ⟨⟨mn, fl⟩, hz, hKe⟩ : ∃ x, (w.reads.loads.order.zip w.reads.loads.flags).toList[cp.mod]? =
          some x ∧ K[cp.mod]? = some ⟨x.1, x.2.level⟩ := by
        subst hK
        simp only [List.length_map] at hKm
        refine ⟨_, List.getElem?_eq_getElem hKm, ?_⟩
        rw [List.getElem?_map, List.getElem?_eq_getElem hKm]
        rfl
      rw [Array.toList_zip, List.getElem?_zip_eq_some] at hz
      obtain ⟨ho, hf⟩ := hz
      simp only [Nat.sub_zero, Option.bind_some, hKe, ht, hq, Option.map_some, Option.some.injEq,
        reduceCtorEq]
      refine ⟨fun s hs => .inr ⟨cp, q, rfl, ?_, ?_⟩, fun h => h.elim⟩
      · simp [NameIndex.at, nameIndexOf, ht, hq]
      · rw [← hs]
        have hn : w.reads.loads.nameAt cp.mod = mn := by
          simp only [Loads.nameAt]; rw [← Array.getElem?_toList, ho]; rfl
        have hfl : (w.reads.loads.flags[cp.mod]?).getD default = fl := by
          rw [← Array.getElem?_toList, hf]; rfl
        rw [hn, hfl]

/-! ## What a record reads, exactly -/

/-- **The memoized walk adds only the expression's names.** -/
theorem needsGo_sound :
    ∀ (e : Expr) (seen : Std.HashSet Expr) (acc : Array Name),
      ∀ n ∈ (needsGo seen acc e).2, n ∈ acc ∨ n ∈ e.needs := by
  intro e
  induction e with
  | bvar i => intro seen acc n hn; exact .inl hn
  | sort u => intro seen acc n hn; exact .inl hn
  | const m us =>
    intro seen acc n hn
    simp only [needsGo, Array.mem_push] at hn
    rcases hn with hn | rfl
    · exact .inl hn
    · exact .inr (by simp [Expr.needs])
  | lit l =>
    intro seen acc n hn
    simp only [needsGo] at hn
    rcases mem_appendList.1 hn with hn | hn
    · exact .inl hn
    · exact .inr (by cases l <;> simpa [Expr.needs] using hn)
  | fvar i ty ih =>
    intro seen acc n hn
    rw [needsGo] at hn
    split at hn
    · exact .inl hn
    · rcases ih seen acc n hn with h | h
      · exact .inl h
      · exact .inr (by simpa [Expr.needs] using h)
  | app f a ihf iha =>
    intro seen acc n hn
    rw [needsGo] at hn
    split at hn
    · exact .inl hn
    · rcases iha _ _ n hn with h | h
      · rcases ihf seen acc n h with h | h
        · exact .inl h
        · exact .inr (by simp [Expr.needs, h])
      · exact .inr (by simp [Expr.needs, h])
  | lam ty b iht ihb =>
    intro seen acc n hn
    rw [needsGo] at hn
    split at hn
    · exact .inl hn
    · rcases ihb _ _ n hn with h | h
      · rcases iht seen acc n h with h | h
        · exact .inl h
        · exact .inr (by simp [Expr.needs, h])
      · exact .inr (by simp [Expr.needs, h])
  | forallE ty b iht ihb =>
    intro seen acc n hn
    rw [needsGo] at hn
    split at hn
    · exact .inl hn
    · rcases ihb _ _ n hn with h | h
      · rcases iht seen acc n h with h | h
        · exact .inl h
        · exact .inr (by simp [Expr.needs, h])
      · exact .inr (by simp [Expr.needs, h])
  | letE ty v b iht ihv ihb =>
    intro seen acc n hn
    rw [needsGo] at hn
    split at hn
    · exact .inl hn
    · rcases ihb _ _ n hn with h | h
      · rcases ihv _ _ n h with h | h
        · rcases iht seen acc n h with h | h
          · exact .inl h
          · exact .inr (by simp [Expr.needs, h])
        · exact .inr (by simp [Expr.needs, h])
      · exact .inr (by simp [Expr.needs, h])
  | proj m i x ih =>
    intro seen acc n hn
    rw [needsGo] at hn
    split at hn
    · exact .inl hn
    · rcases ih _ _ n hn with h | h
      · rcases Array.mem_push.1 h with h | rfl
        · exact .inl h
        · exact .inr (by simp [Expr.needs])
      · exact .inr (by simp [Expr.needs, h])

/-- **The names a constant's laws read** (`ConstCovered`'s, exactly). -/
@[expose] def ConstReads (ci : ConstantInfo) (n : Name) : Prop :=
  n ∈ ci.toConstantVal.type.needs ∨
  (∃ cv v h, ci = .defnInfo cv v h ∧ n ∈ v.needs) ∨
  (∃ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules ∧ ∃ r ∈ rules,
    n ∈ r.rhs.needs ∨ n = r.ctor ∨ ∃ lvls pins, r.fire = .nested lvls pins ∧ ∃ p ∈ pins, n ∈ p.needs) ∨
  (∃ cv caps, ci = .indInfo cv caps ∧ (n ∈ caps.all ∨ (caps.eta = true ∧ n = caps.etaCtor))) ∨
  n ∈ pinFootprint ci.toConstantVal.name

/-- **The names a table reads** (`TableCovered`'s, exactly). -/
@[expose] def TableReads (t : ProjTable) (n : Name) : Prop :=
  n = t.structName ∨ n = t.ctor ∨ ∃ b ∈ t.bodies.toList, n ∈ b.needs

/-- **The names a record reads**: its constants' laws' and its tables'. -/
@[expose] def RecordReads (d : Declaration) (n : Name) : Prop :=
  (∃ ci ∈ declConstants d, ConstReads ci n) ∨ ∃ t ∈ declTables d, TableReads t n

theorem foldl_expr_sound {S : Name → Prop} :
    ∀ (es : List Expr) (x : NeedsSt), (∀ e ∈ es, ∀ n ∈ e.needs, S n) →
      ∀ n ∈ (es.foldl NeedsSt.expr x).2, n ∈ x.2 ∨ S n
  | [], x, _, n, hn => .inl hn
  | e :: es, x, h, n, hn => by
    rcases foldl_expr_sound es (x.expr e) (fun e' he' => h e' (List.mem_cons_of_mem _ he')) n hn
      with h' | h'
    · rcases needsGo_sound e x.1 x.2 n h' with h'' | h''
      · exact .inl h''
      · exact .inr (h e List.mem_cons_self n h'')
    · exact .inr h'

theorem rule_sound (x : NeedsSt) (r : RecRule) :
    ∀ n ∈ (x.rule r).2, n ∈ x.2 ∨ (n ∈ r.rhs.needs ∨ n = r.ctor ∨
      ∃ lvls pins, r.fire = .nested lvls pins ∧ ∃ p ∈ pins, n ∈ p.needs) := by
  intro n hn
  have base : ∀ m ∈ ((x.expr r.rhs).names [r.ctor]).2, m ∈ x.2 ∨ (m ∈ r.rhs.needs ∨ m = r.ctor) := by
    intro m hm
    simp only [NeedsSt.names] at hm
    rcases mem_appendList.1 hm with hm | hm
    · rcases needsGo_sound r.rhs x.1 x.2 m hm with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · exact .inr (.inr (by simpa using hm))
  unfold NeedsSt.rule at hn
  split at hn
  · rename_i lvls pins hf
    rcases foldl_expr_sound (S := fun m => ∃ p ∈ pins, m ∈ p.needs) pins _
      (fun p hp m hm => ⟨p, hp, hm⟩) n hn with h | h
    · rcases base n h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨lvls, pins, hf, h⟩))
  · rcases base n hn with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))

theorem const_sound (x : NeedsSt) (ci : ConstantInfo) :
    ∀ n ∈ (x.const ci).2, n ∈ x.2 ∨ ConstReads ci n := by
  intro n hn
  have hty : ∀ m ∈ (x.expr ci.toConstantVal.type).2, m ∈ x.2 ∨ ConstReads ci m := by
    intro m hm
    rcases needsGo_sound _ x.1 x.2 m hm with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have hfp : ∀ m ∈ pinFootprint ci.toConstantVal.name, ConstReads ci m :=
    fun m hm => .inr (.inr (.inr (.inr hm)))
  unfold NeedsSt.const at hn
  simp only [NeedsSt.names] at hn
  rcases mem_appendList.1 hn with hn | hn
  rotate_left
  · exact .inr (hfp n hn)
  cases ci with
  | defnInfo cv v hh =>
    rcases needsGo_sound v _ _ n hn with h | h
    · exact hty n h
    · exact .inr (.inr (.inl ⟨cv, v, hh, rfl, h⟩))
  | recInfo cv mI rP isK rules =>
    have key : ∀ (rs : List RecRule) (y : NeedsSt), (∀ r ∈ rs, r ∈ rules) →
        ∀ m ∈ (rs.foldl NeedsSt.rule y).2, m ∈ y.2 ∨ ConstReads (.recInfo cv mI rP isK rules) m := by
      intro rs
      induction rs with
      | nil => intro y _ m hm; exact .inl hm
      | cons r rs ih =>
        intro y hr m hm
        rcases ih (y.rule r) (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) m hm with h | h
        · rcases rule_sound y r m h with h | h
          · exact .inl h
          · exact .inr (.inr (.inr (.inl ⟨cv, mI, rP, isK, rules, rfl, r, hr r List.mem_cons_self, h⟩)))
        · exact .inr h
    rcases key rules _ (fun r h => h) n hn with h | h
    · exact hty n h
    · exact .inr h
  | indInfo cv caps =>
    rcases mem_appendList.1 hn with h | h
    · exact hty n h
    · simp only [List.mem_append] at h
      refine .inr (.inr (.inr (.inr (.inl ⟨cv, caps, rfl, ?_⟩))))
      rcases h with h | h
      · exact .inl h
      · split at h
        · rename_i he
          exact .inr ⟨he, by simpa using h⟩
        · simp at h
  | axiomInfo cv => exact hty n hn
  | thmInfo cv => exact hty n hn
  | ctorInfo cv i n' => exact hty n hn

theorem table_sound (x : NeedsSt) (t : ProjTable) :
    ∀ n ∈ (x.table t).2, n ∈ x.2 ∨ TableReads t n := by
  intro n hn
  unfold NeedsSt.table at hn
  rcases foldl_expr_sound (S := fun m => ∃ b ∈ t.bodies.toList, m ∈ b.needs) _ _
    (fun b hb m hm => ⟨b, hb, hm⟩) n hn with h | h
  · simp only [NeedsSt.names] at h
    rcases mem_appendList.1 h with h | h
    · exact .inl h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr h))

/-- **`recordReads` lists only names a record's constants and tables read.** -/
theorem recordReads_sound {d : Declaration} {n : Name} (h : n ∈ recordReads d) :
    RecordReads d n := by
  unfold recordReads at h
  have kc : ∀ (cs : List ConstantInfo) (y : NeedsSt), (∀ c ∈ cs, c ∈ declConstants d) →
      ∀ m ∈ (cs.foldl NeedsSt.const y).2, m ∈ y.2 ∨ RecordReads d m := by
    intro cs
    induction cs with
    | nil => intro y _ m hm; exact .inl hm
    | cons c cs ih =>
      intro y hc m hm
      rcases ih (y.const c) (fun c' h' => hc c' (List.mem_cons_of_mem _ h')) m hm with h | h
      · rcases const_sound y c m h with h | h
        · exact .inl h
        · exact .inr (.inl ⟨c, hc c List.mem_cons_self, h⟩)
      · exact .inr h
  have kt : ∀ (ts : List ProjTable) (y : NeedsSt), (∀ t ∈ ts, t ∈ declTables d) →
      ∀ m ∈ (ts.foldl NeedsSt.table y).2, m ∈ y.2 ∨ RecordReads d m := by
    intro ts
    induction ts with
    | nil => intro y _ m hm; exact .inl hm
    | cons t ts ih =>
      intro y ht m hm
      rcases ih (y.table t) (fun t' h' => ht t' (List.mem_cons_of_mem _ h')) m hm with h | h
      · rcases table_sound y t m h with h | h
        · exact .inl h
        · exact .inr (.inr ⟨t, ht t List.mem_cons_self, h⟩)
      · exact .inr h
  rcases kt _ _ (fun t h => h) n h with h | h
  · rcases kc _ _ (fun c h => h) n h with h | h
    · simp at h
    · exact h
  · exact h

/-- **The names a record reads are in `recordReads`.** -/
theorem recordReads_complete {d : Declaration} {n : Name} (h : RecordReads d n) :
    n ∈ recordReads d := by
  obtain ⟨hc, ht⟩ := recordReads_covers d
  rcases h with ⟨ci, hci, h⟩ | ⟨t, hti, h⟩
  · obtain ⟨c1, c2, c3, c4, c5⟩ := hc ci hci
    rcases h with h | ⟨cv, v, hh, rfl, h⟩ | ⟨cv, mI, rP, isK, rules, rfl, r, hr, h⟩ |
        ⟨cv, caps, rfl, h⟩ | h
    · exact c1 n h
    · exact c2 cv v hh rfl n h
    · obtain ⟨r1, r2, r3⟩ := c3 cv mI rP isK rules rfl r hr
      rcases h with h | rfl | ⟨lvls, pins, hf, p, hp, h⟩
      · exact r1 n h
      · exact r2
      · exact r3 lvls pins hf p hp n h
    · rcases h with h | ⟨he, rfl⟩
      · exact (c4 cv caps rfl).1 n h
      · exact (c4 cv caps rfl).2 he
    · exact c5 n h
  · obtain ⟨t1, t2, t3⟩ := ht t hti
    rcases h with rfl | rfl | ⟨b, hb, h⟩
    · exact t1
    · exact t2
    · exact t3 b hb n h

/-- What an axiom's constant reads, any constant of its statement reads. -/
theorem axiom_constReads {cv : ConstantVal} (hq : cv.name ≠ quotSoundName) {ci : ConstantInfo}
    (hci : ci ∈ declConstants (.axiomDecl cv)) {n : Name} (hr : ConstReads ci n)
    {c : ConstantInfo} (hc : c.toConstantVal = cv) : ConstReads c n := by
  simp only [declConstants, hq, ↓reduceIte] at hci
  split at hci
  · simp at hci
  simp only [List.mem_singleton] at hci
  subst hci
  rcases hr with h | ⟨_, _, _, h, -⟩ | ⟨_, _, _, _, _, h, -⟩ | ⟨_, _, h, -⟩ | h
  · exact .inl (by rw [hc]; exact h)
  · cases h
  · cases h
  · cases h
  · exact .inr (.inr (.inr (.inr (by rw [hc]; exact h))))

/-- **A presentation reads what the record it presents reads**, or less (a statement at no
`Quot.sound`, whose constant is the pinned one). -/
theorem Presents.reads {d p : Declaration} (h : Presents d p)
    (hq : ∀ cv, stmtOf p = .axiomDecl cv → cv.name ≠ quotSoundName ∨ p = .axiomDecl cv)
    {n : Name} (hn : n ∈ recordReads d) : n ∈ recordReads p := by
  apply recordReads_complete
  rcases h with ⟨hperm, htab⟩ | ⟨rfl, -⟩
  · rcases recordReads_sound hn with ⟨ci, hci, hr⟩ | ⟨t, hti, hr⟩
    · exact .inl ⟨ci, hperm.mem_iff.1 hci, hr⟩
    · exact .inr ⟨t, htab ▸ hti, hr⟩
  · have hsound := recordReads_sound hn
    cases p with
    | defnDecl cv v hh =>
      rcases hsound with ⟨ci, hci, hr⟩ | ⟨t, hti, -⟩
      · have hq' := (hq cv rfl).resolve_right (by simp)
        exact .inl ⟨_, List.mem_singleton_self _, axiom_constReads hq' hci hr rfl⟩
      · simp [stmtOf, declTables] at hti
    | thmDecl cv v =>
      rcases hsound with ⟨ci, hci, hr⟩ | ⟨t, hti, -⟩
      · have hq' := (hq cv rfl).resolve_right (by simp)
        exact .inl ⟨_, List.mem_singleton_self _, axiom_constReads hq' hci hr rfl⟩
      · simp [stmtOf, declTables] at hti
    | opaqueDecl cv v =>
      rcases hsound with ⟨ci, hci, hr⟩ | ⟨t, hti, -⟩
      · have hq' := (hq cv rfl).resolve_right (by simp)
        exact .inl ⟨_, List.mem_singleton_self _, axiom_constReads hq' hci hr rfl⟩
      · simp [stmtOf, declTables] at hti
    | axiomDecl cv => exact hsound
    | quotDecl k cv => exact hsound
    | indDecl b nP => exact hsound

end ConLeche.Driver
