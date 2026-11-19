module

public import ConLeche.Verify.Driver.ComposeReads
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Verify.PinRen
import ConLeche.Verify.Frontend.Olean.Group
import ConLeche.Verify.Driver.RouteWorker
import ConLeche.Verify.Frontend.Olean.Emit
import ConLeche.Verify.Frontend.Olean.GroupSame
public import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Driver.Groups
public import ConLeche.Verify.Driver.Copies
import ConLeche.Verify.Driver.Clashes
import ConLeche.Verify.Driver.PropPart

/-!
# The routes: what a module's context stores, and how

At a module of a run (task #501), facts about the records of its context that the routes of the
capture check's pairs (`Routes.lean`) read:

* `ctx_stmt` — a context name whose copy is of a statement kind is stored by its statement,
  read at that copy, of a module of the run;
* `rank_lt` — a name a stored statement's type reads, other than its own, is stored before it;
* `reader_ctx` — a reader of a passed pair stores the name it reads, where the name is loaded at
  it: by the pair's origin (a record's read, an `agreeCheck` partner read, a clash partner read).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

/-! ## Helpers -/

/-- A term's names are stored where it resolves. -/
theorem readNames_stored_of_resolve {E : Env} :
    ∀ {e : Expr}, e.constsResolve E = true → ∀ c ∈ e.readNames, (E.find? c).isSome = true := by
  intro e
  induction e with
  | lit l => cases l <;> intro h c hc <;> simp_all [Expr.readNames, ConLeche.Expr.constsResolve] <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  | _ => intro h c hc; simp_all [Expr.readNames, ConLeche.Expr.constsResolve] <;> grind

/-- **A block installs no statement kind.** -/
theorem blockConstants_not_stmt (p : BlockShape) {ci : ConstantInfo}
    (h : ci ∈ blockConstants p) : ci.isStmtKind = false := by
  unfold blockConstants blockFormers blockCtors at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at h
  have hR : ∀ l : List RecShape, ci ∈ blockRecs p l → ci.isStmtKind = false := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons a l ih =>
      intro h
      rcases List.mem_cons.1 h with rfl | h
      · rfl
      · exact ih h
  rcases h with (⟨x, -, rfl⟩ | ⟨g, -, x, -, rfl⟩) | h
  · rfl
  · rfl
  · exact hR _ h

/-- **A record installing a statement kind installs it alone.** -/
theorem stmt_single {d : Declaration} {ci : ConstantInfo} (h : ci ∈ declConstants d)
    (hk : ci.isStmtKind = true) : declConstants d = [ci] := by
  cases d with
  | indDecl b nP =>
    simp only [declConstants] at h
    split at h
    · rw [blockConstants_not_stmt _ h] at hk; cases hk
    · cases h
  | axiomDecl cv =>
    simp only [declConstants] at h ⊢
    split at h
    · rw [List.mem_singleton.1 h]; simp [*]
    · split at h
      · cases h
      · rw [List.mem_singleton.1 h]; simp [*]
  | _ => simp only [declConstants, List.mem_singleton] at h ⊢; rw [h]

/-- **An accepted step passed the reserved names' check.** -/
theorem checkDeclStepC_basis {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {d : Declaration} :
    Yields (checkDeclStepC mode pins fe d) (fun _ => basisNamesOk d = true) := by
  unfold checkDeclStepC checkDeclC
  yields
  all_goals exact Yields.pure (by assumption)

/-- **Every record of an accepted run passed the reserved names' check.** -/
theorem declsRun_basis {mode : CheckMode} {maxNatSize : Nat} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins maxNatSize none ds p q) : ∀ d ∈ ds, basisNamesOk d = true := by
  induction h with
  | nil => exact fun _ h => nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      exact checkDeclStepC_basis _ _ _ hC
    · exact ih d hd

/-- **A presentation reads what the record it presents reads**, at a record that passed the
reserved names' check. -/
theorem presents_reads {d p : Declaration} (h : Presents d p) (hb : basisNamesOk p = true)
    {n : Name} (hn : n ∈ recordReads d) : n ∈ recordReads p := by
  have hres : quotSoundName ∈ reservedBasisNames := by simp [reservedBasisNames]
  refine Presents.reads h (fun cv hcv => ?_) hn
  cases p with
  | axiomDecl c => exact .inr (by simp only [stmtOf] at hcv; rw [hcv])
  | defnDecl c v hh =>
    simp only [stmtOf, Declaration.axiomDecl.injEq] at hcv
    subst hcv
    refine .inl fun he => ?_
    simp [basisNamesOk, he] at hb
    exact hb hres
  | thmDecl c v =>
    simp only [stmtOf, Declaration.axiomDecl.injEq] at hcv
    subst hcv
    refine .inl fun he => ?_
    simp [basisNamesOk, he] at hb
    exact hb hres
  | opaqueDecl c v =>
    simp only [stmtOf, Declaration.axiomDecl.injEq] at hcv
    subst hcv
    refine .inl fun he => ?_
    simp [basisNamesOk, he] at hb
    exact hb hres
  | quotDecl k c => simp [stmtOf] at hcv
  | indDecl b nP => simp [stmtOf] at hcv

/-- A record's name is stored where the record is. -/
theorem stored_of_record {ds : List Declaration} {d : Declaration} (hd : d ∈ ds) {n : Name}
    (hn : n ∈ declNames d) : ((streamEnv ds).find? n).isSome = true := by
  unfold declNames at hn
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
  simp only [Env.find?, List.find?_isSome]
  exact ⟨ci, (mem_streamEnv_consts _ _).2 (.inl ⟨d, hd, hci⟩), by simp [ConstantInfo.name]⟩

/-- **A statement and kind at a location are one.** -/
theorem stmtSkel_unique {r : Region} {loc : Nat} {cv cv' : ConstantVal} {k k' : CKindF Name Unit}
    (h : StmtSkel r loc cv k) (h' : StmtSkel r loc cv' k') : cv = cv' ∧ k = k' := by
  obtain ⟨s, hs, hn, hl, ht, hk⟩ := h
  obtain ⟨s', hs', hn', hl', ht', hk'⟩ := h'
  rw [hs] at hs'
  cases hs'
  rw [hn] at hn'; rw [hl] at hl'; rw [ht] at ht'; rw [hk] at hk'
  obtain ⟨n, l, t⟩ := cv
  obtain ⟨n', l', t'⟩ := cv'
  simp only [Option.some.injEq] at hn' hl' ht' hk'
  subst hn' hl' ht' hk'
  exact ⟨rfl, rfl⟩

/-- A quotient constant is no definition. -/
theorem quotAt_ne_defn (k : QuotKind) (c cv : ConstantVal) (v : Expr) (hh : ReducibilityHint) :
    quotAt k c ≠ .defnInfo cv v hh := by
  cases k <;> intro h <;> cases h

/-- **A presentation of a definition is the definition.** -/
theorem defn_presents {cv : ConstantVal} {v : Expr} {hh : ReducibilityHint} {p : Declaration}
    (h : Presents (.defnDecl cv v hh) p) : ∃ v' hh', p = .defnDecl cv v' hh' := by
  rcases h with ⟨hperm, -⟩ | ⟨he, -⟩
  · have hm : ConstantInfo.defnInfo cv v hh ∈ declConstants p :=
      hperm.mem_iff.1 (by simp [declConstants])
    cases p with
    | defnDecl c v' h' =>
      simp only [declConstants, List.mem_singleton, ConstantInfo.defnInfo.injEq] at hm
      exact ⟨v', h', by rw [hm.1]⟩
    | thmDecl c v' => simp [declConstants] at hm
    | opaqueDecl c v' => simp [declConstants] at hm
    | axiomDecl c =>
      simp only [declConstants] at hm
      split at hm
      · exact absurd (List.mem_singleton.1 hm).symm (quotAt_ne_defn _ _ _ _ _)
      · split at hm
        · cases hm
        · simp at hm
    | quotDecl k c =>
      simp only [declConstants, List.mem_singleton] at hm
      exact absurd hm.symm (quotAt_ne_defn _ _ _ _ _)
    | indDecl b nP =>
      simp only [declConstants] at hm
      split at hm
      · have := blockConstants_not_stmt _ hm; simp [ConstantInfo.isStmtKind] at this
      · cases hm
  · cases p <;> simp [stmtOf] at he

-- The walk splits at each of the check's guards and carries the clause into both halves, as
-- `checkConstantValC_fresh_res`'s (`Copies.lean`) does, at its limit.
set_option maxHeartbeats 400000 in
/-- **An accepted check of a statement not an axiom's is not at the tolerated axiom's name.** -/
theorem checkConstantValC_sorry {mode : CheckMode} {fe : FEnv} {cv : ConstantVal} {a b : Bool} :
    Yields (checkConstantValC mode fe cv a b false) (fun _ => cv.name ≠ sorryAxName) := by
  unfold checkConstantValC
  yields
  all_goals exact Yields.const (by
    rename_i hs _ _ _ _ _
    intro he
    simp [sorryAxNameAt, he] at hs)

/-- **An accepted definition is not at the tolerated axiom's name.** -/
theorem checkDeclStepC_defn_sorry {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {cv : ConstantVal} {v : Expr} {hh : ReducibilityHint} :
    Yields (checkDeclStepC mode pins fe (.defnDecl cv v hh)) (fun _ => cv.name ≠ sorryAxName) := by
  unfold checkDeclStepC checkDeclC
  ybind
  refine Yields.bind' (Q := fun _ => cv.name ≠ sorryAxName) ?_ fun _ h => Yields.const h
  unfold checkDeclKindC
  exact Yields.bind' checkConstantValC_sorry fun _ h => Yields.const h

theorem declsRun_defn_sorry {mode : CheckMode} {maxNatSize : Nat} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins maxNatSize none ds p q) {cv : ConstantVal} {v : Expr}
    {hh : ReducibilityHint} (hd : .defnDecl cv v hh ∈ ds) : cv.name ≠ sorryAxName := by
  induction h with
  | nil => exact nomatch hd
  | @cons pd ds p p₁ q hstep rest ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      exact checkDeclStepC_defn_sorry _ _ _ hC
    · exact ih hd

/-- **A definition's record, from one constant.** -/
theorem entryDecl_defn {c : CEntry} {d : Declaration} (h : entryDecl c = some d)
    (ht : c.kind.tag = 1) : ∃ v hh, d = .defnDecl ⟨c.name, c.levelParams, c.type⟩ v hh := by
  rcases c with ⟨⟨n, l, t, k⟩, u⟩
  cases k with
  | defn v hh sf =>
    by_cases hsf : sf = "safe"
    · subst hsf
      simp only [entryDecl, Option.some.injEq] at h
      exact ⟨_, _, h.symm⟩
    · simp [entryDecl, hsf] at h
  | _ => simp [CKindF.tag] at ht

/-- **A quotient constant's record, from one constant.** -/
theorem entryDecl_quot {c : CEntry} {d : Declaration} (h : entryDecl c = some d) {q : String}
    (hk : c.kind = .quot q) : ∃ k, d = .quotDecl k ⟨c.name, c.levelParams, c.type⟩ := by
  unfold entryDecl at h
  rw [hk] at h
  simp only at h
  split at h <;> (try (rename_i heq; cases heq)) <;> (try (cases h; exact ⟨_, rfl⟩)) <;> cases h

/-- **A copy's position says its statement's kind**: its tag and its filter. -/
theorem copyAt_kind {sp : Roots} {fs : FS} {s : Spot} {r : Region} {cv : ConstantVal}
    {k : CKindF Name Unit} (hs : CopyAt sp fs s) (hr : PartRegion sp fs s.part r)
    (hst : StmtSkel r s.pos.loc cv k) : s.pos.tag = k.tag ∧ s.pos.skipped = k.skipped := by
  obtain ⟨t, ht, hq⟩ := hs
  obtain ⟨f, a, hf, hreg⟩ := hr
  have hn := partNames_region ht hf
  simp only [readNamePositions, hreg] at hn
  change namePositionsAt r a = some t at hn
  obtain ⟨_, _, _, hall⟩ := namePositionsAt_mem hn
  obtain ⟨_, sk, hsk, -, htg, hskp⟩ := hall _ hq
  obtain ⟨sk', hsk', -, -, -, hkm⟩ := hst
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨h1, h2⟩ := CKindF.mapM_tag hkm
  exact ⟨htg.trans h1, hskp.trans h2⟩

theorem except_mapM_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; cases hy
  | x :: xs, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨a, ha, h⟩ := bind_ok_inv h
    obtain ⟨as, has, h⟩ := bind_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, ha⟩
    · obtain ⟨x', hx', hf⟩ := except_mapM_mem has y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

/-- **A block's record names only its records' constants**, and is an inductive block. -/
theorem declOfF_ind_names {em : Emit} {ts : List Frontend.IndTypeRec}
    {cts : List Frontend.IndCtorRec} {rs : List Frontend.IndRecRec} {d : Declaration}
    (h : Frontend.declOfF em.nm em.lv em.ex (.ind ts cts rs) = .ok (.inl d)) {P : Name → Prop}
    (hts : ∀ t ∈ ts, ∃ c, CvOf em t.cv c ∧ P c.name)
    (hcts : ∀ t ∈ cts, ∃ c, CvOf em t.cv c ∧ P c.name)
    (hrs : ∀ t ∈ rs, ∃ c, CvOf em t.cv c ∧ P c.name) :
    (∃ b nP, d = .indDecl b nP) ∧ ∀ n ∈ declNames d, P n := by
  simp only [Frontend.declOfF, bind, Except.bind, pure, Except.pure] at h
  cases hv : Frontend.validateIndF em.nm em.lv em.ex ts cts rs with
  | error e => simp only [hv] at h; cases h
  | ok x =>
  simp only [hv] at h
  rcases x with x | ⟨c1, nPd⟩
  · simp at h
  simp only at h
  cases hb : Frontend.indBlockOfF em.nm em.lv em.ex ts c1 rs nPd with
  | error e => simp only [hb] at h; cases h
  | ok d' =>
  simp only [hb, Except.ok.injEq, Sum.inl.injEq] at h
  subst h
  obtain ⟨-, -, tyNames, listed, ctorNames, -, -, -, hc1⟩ := validateIndF_inr hv
  have hc1m : ∀ c ∈ c1, c.1 ∈ cts := by
    intro c hc
    rw [hc1] at hc
    simp only [ctorsListed, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨tn, -, c', hc', rfl⟩ := hc
    obtain ⟨n, -, hn⟩ := List.mem_filterMap.1 hc'

    simp only [ctorAt] at hn
    obtain ⟨k, -, hk⟩ := Option.bind_eq_some_iff.1 hn
    have := Array.mem_of_getElem? hk
    simpa using this
  unfold Frontend.indBlockOfF at hb
  obtain ⟨types, htypes, hb⟩ := bind_ok_inv hb
  obtain ⟨ctors, hctors, hb⟩ := bind_ok_inv hb
  obtain ⟨recs, hrecs, hb⟩ := bind_ok_inv hb
  simp only [pure, Except.pure, Except.ok.injEq] at hb
  subst hb
  have hblock : ∀ b ∈ types ++ ctors ++ recs, P b.name := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · obtain ⟨t, ht, hf⟩ := except_mapM_mem htypes b hb
      obtain ⟨cv, hcv, hf⟩ := bind_ok_inv hf
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      obtain ⟨c, hc, hp⟩ := hts t ht
      rw [cvOfF_of hc] at hcv; cases hcv; exact hp
    · obtain ⟨t, ht, hf⟩ := except_mapM_mem hctors b hb
      obtain ⟨cv, hcv, hf⟩ := bind_ok_inv hf
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      obtain ⟨c, hc, hp⟩ := hcts t.1 (hc1m t ht)
      rw [cvOfF_of hc] at hcv; cases hcv; exact hp
    · obtain ⟨t, ht, hf⟩ := except_mapM_mem hrecs b hb
      obtain ⟨rules, -, hf⟩ := bind_ok_inv hf
      obtain ⟨cv, hcv, hf⟩ := bind_ok_inv hf
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      obtain ⟨c, hc, hp⟩ := hrs t ht
      rw [cvOfF_of hc] at hcv; cases hcv; exact hp
  refine ⟨⟨_, _, rfl⟩, fun n hn => ?_⟩
  simp only [declNames, declConstants] at hn
  split at hn
  · rename_i p hp
    obtain ⟨hm, hc, hr⟩ := readBlock_names hp
    have : n ∈ (blockConstants p).map (·.name) := hn
    rw [blockConstants_names] at this
    simp only [List.mem_append, List.mem_map] at this
    rcases this with (⟨ms, hms, rfl⟩ | ⟨c, hc', rfl⟩) | ⟨rc, hrc, rfl⟩
    · obtain ⟨b, hb, hbn⟩ := hm ms hms; rw [← hbn]; exact hblock b hb
    · obtain ⟨b, hb, hbn⟩ := hc c hc'; rw [← hbn]; exact hblock b hb
    · obtain ⟨b, hb, hbn⟩ := hr rc hrc; rw [← hbn]; exact hblock b hb
  · simp at hn

/-- **An accepted quotient record is its slot's pin.** -/
theorem checkDeclStepC_quot {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {k : QuotKind} {cv : ConstantVal} :
    Yields (checkDeclStepC mode pins fe (.quotDecl k cv)) (fun _ => quotPinHit k cv = true) := by
  unfold checkDeclStepC checkDeclC
  ybind
  refine Yields.bind' (Q := fun _ => quotPinHit k cv = true) ?_ fun _ h => Yields.const h
  show Yields (checkQuotRecordC fe k cv) _
  unfold checkQuotRecordC
  yields
  all_goals exact Yields.const (by assumption)

theorem declsRun_quot {mode : CheckMode} {maxNatSize : Nat} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins maxNatSize none ds p q) {k : QuotKind} {cv : ConstantVal}
    (hd : .quotDecl k cv ∈ ds) : quotPinHit k cv = true := by
  induction h with
  | nil => exact nomatch hd
  | @cons pd ds p p₁ q hstep rest ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      exact checkDeclStepC_quot _ _ _ hC
    · exact ih hd

/-- **A pinned quotient record installs its own name.** -/
theorem quotAt_name_of_hit {k : QuotKind} {cv : ConstantVal} (h : quotPinHit k cv = true) :
    (quotAt k cv).name = cv.name := by
  simp only [quotPinHit, Bool.and_eq_true] at h
  have he := ConstantVal.eq_of_beqP h.2
  rw [quotAt, ConLeche.Verify.atLps_name, he]
  rfl

/-- **A module's own names** hold every constant of its private view. -/
theorem ownNames_mem {l : Loaded} {c : CEntry} (hc : c ∈ l.constants) :
    (ownNames l).contains c.name = true := by
  unfold ownNames
  rw [← Array.foldl_toList]
  have key : ∀ (L : List CEntry) (acc : Std.HashSet Name),
      (acc.contains c.name = true ∨ c ∈ L) →
        (L.foldl (fun s c => s.insert c.name) acc).contains c.name = true := by
    intro L
    induction L with
    | nil => intro acc h; simpa using h
    | cons a L ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | h
      · exact .inl (by simp [h])
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl (by simp)
        · exact .inr h
  exact key _ _ (.inr (Array.mem_toList_iff.2 hc))

/-- **A copy of a statement kind, of an accepted module's part, has a position of its name and
of a statement kind in the module's private table.** -/
theorem copy_private_pos {sp : Roots} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {s : Spot} (hmod : s.part.mod = M) (hs : CopyAt sp fs s)
    (hl : s.part.level ≠ .server) {r1 : Region} (hr : PartRegion sp fs s.part r1)
    {cv : ConstantVal} {k : CKindF Name Unit} (hst : StmtSkel r1 s.pos.loc cv k) (hk : k.tag < 4) :
    ∃ q ∈ w.reads.own.consts, q.name = s.pos.name ∧ q.tag < 4 := by
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, -⟩ := home_records hw
  obtain ⟨loc, sP, s1, hloc, hsP, hs1, hn1, hskq, hskP, hbeh, hnP⟩ :=
    copy_behind hf hreg hsk hload hcv hmod hs hl hr
  have htP : sP.kind.tag < 4 := by
    rcases hbeh with ⟨hsame, -⟩ | hhid
    · obtain ⟨k', ⟨sP', hsP', -, -, -, hkm⟩, htk, -⟩ := hsame cv k hst
      rw [hsP] at hsP'
      cases hsP'
      rw [(CKindF.mapM_tag hkm).1, htk]; exact hk
    · obtain ⟨-, -, -, -, htag'⟩ := hhid cv k hst
      omega
  have hT := home_table hf hreg (worker_ownTable hw)
  obtain ⟨q, hq, hql, hqn⟩ := namePositionsAt_complete hT hsk hloc hsP hnP
  obtain ⟨_, _, _, hall⟩ := namePositionsAt_mem hT
  obtain ⟨-, s'', hs'', -, htg, -⟩ := hall q hq
  rw [hql, hsP] at hs''
  cases hs''
  exact ⟨q, hq, hqn, by rw [htg]; exact htP⟩

/-- **A constant of an accepted module's private view has a position of its name and kind** in
the module's private table. -/
theorem home_const_pos {sp : Roots} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {c : CEntry} (hc : c ∈ w.home.constants) :
    ∃ q ∈ w.reads.own.consts, q.name = c.name ∧ q.tag = c.kind.tag := by
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, -⟩ := home_records hw
  have hT := home_table hf hreg (worker_ownTable hw)
  obtain ⟨q, hq, s, hs, hn, htg, -, hle⟩ :=
    Forall₂.mem_right (home_rows hload hreg hT) c (Array.mem_toList_iff.2 hc)
  refine ⟨q, Array.mem_toList_iff.1 hq, ?_, ?_⟩
  · have := (lazyEntry_stmt hle).1
    rw [hn] at this
    exact Option.some.inj this
  · rw [htg, ← (lazyEntry_kind hle).2]

/-- The private table of an accepted module names each position once. -/
theorem own_pos_unique {sp : Roots} {fs : FS} {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {q q' : NamePosition} (hq : q ∈ w.reads.own.consts)
    (hq' : q' ∈ w.reads.own.consts) (hn : q.name = q'.name) : q = q' := by
  obtain ⟨f, r, a, sk, skels, hf, hreg, -⟩ := home_records hw
  have hT := home_table hf hreg (worker_ownTable hw)
  obtain ⟨-, -, hnd, -⟩ := namePositionsAt_mem hT
  exact eq_of_map_nodup hnd (Array.mem_toList_iff.2 hq) (Array.mem_toList_iff.2 hq') hn

/-- **A statement-kind constant's record checks its statement**, at no `Quot.sound`. -/
theorem entryDecl_stmtRecord {e : CEntry} {p : Declaration} (hp : entryDecl e = some p)
    (ht : e.kind.tag < 4) (hq : e.name ≠ quotSoundName) (F : Expr → Expr) :
    StmtRecord (fillDecl F p) ⟨e.name, e.levelParams, e.type⟩ := by
  rcases e with ⟨⟨n, l, t, k⟩, u⟩
  cases k with
  | ax iu =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact .inr (.inr (.inr ⟨rfl, hq⟩))
  | defn v hh sf =>
    by_cases hsf : sf = "safe"
    · subst hsf
      simp only [entryDecl, Option.some.injEq] at hp
      subst hp
      exact .inl ⟨_, _, rfl⟩
    · simp [entryDecl, hsf] at hp
  | thm v all =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact .inr (.inl ⟨_, rfl⟩)
  | opaq v iu =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact .inr (.inr (.inl ⟨_, rfl⟩))
  | _ => simp [CKindF.tag] at ht

/-- **A context name of smaller rank than `y` is stored in the part below `y`.** -/
theorem part_isSome {m : Module} {c y : Name} (hc : (m.context.find? c).isSome = true)
    (hlt : m.rank c < m.rank y) : ((m.part y).find? c).isSome = true := by
  obtain ⟨d, hd, hcd⟩ := streamEnv_find_mem hc
  have hl : m.rank c < m.ctx.length :=
    List.findIdx_lt_length_of_exists ⟨d, hd, by simpa using hcd⟩
  have hp : (declNames m.ctx[m.rank c]).contains c = true := List.findIdx_getElem (w := hl)
  obtain ⟨ci, hci, hn⟩ := List.mem_map.1 (List.contains_iff_mem.1 hp)
  have hk : m.rank c < (m.ctx.take (m.rank y)).length := by
    rw [List.length_take]; omega
  have hmem : m.ctx[m.rank c] ∈ m.ctx.take (m.rank y) := by
    rw [← List.getElem_take (h := hk)]; exact List.getElem_mem hk
  show ((streamEnv (m.ctx.take (m.rank y))).find? c).isSome = true
  simp only [Env.find?, List.find?_isSome]
  exact ⟨ci, (mem_streamEnv_consts _ _).2 (.inl ⟨_, hmem, hci⟩), by simpa [ConstantInfo.name] using hn⟩

/-- **The names of smaller rank than `y`, stored in the context, resolve below `y`.** -/
theorem part_resolve {m : Module} {y : Name} {ty : Expr}
    (h : ∀ c ∈ ty.readNames, m.rank c < m.rank y ∧ (m.context.find? c).isSome = true) :
    ty.constsResolve (m.part y) = true :=
  constsResolve_of_needs fun c hc => by
    rw [needs_eq_readNames] at hc
    exact part_isSome (h c hc).2 (h c hc).1

namespace Run

variable {sp : Roots} {fs : FS} {maxNatSize : Nat} (R : Run sp fs maxNatSize)

/-- **An emitted record of a module of the run passed the reserved names' check.** -/
theorem own_basis {h : Name} (hh : h ∈ R.names) (hx : R.x h = #[]) {p : Declaration} (hp : p ∈ (R.w h).emitted) :
    basisNamesOk p = true := by
  have := declsRun_basis (R.run h hh) _
    (List.mem_map_of_mem (f := fillDecl (fillOf (R.look h) fs #[⟨h, (R.w h).home.frontier⟩]))
      (emitted_own (R.facts₀ hh hx) hp))
  cases p <;> exact this

/-- **A name an own constant's type reads, loaded at the module, is in its context**: the
constant is an own record's or a context record's, and either's reads are stored there. -/
theorem stored_of_own_const {h : Name} (hh : h ∈ R.names) (hx : R.x h = #[]) {ci : ConstantInfo}
    (hci : ci ∈ (ownEnvOf (R.look h) fs h (R.w h)).consts) {y : Name}
    (hy : y ∈ ci.toConstantVal.type.needs)
    (hl : ((R.w h).reads.index.first[y]?).isSome = true) :
    ((R.dev (R.rk h)).context.find? y).isSome = true := by
  have hw := R.facts₀ hh hx
  have hno : (ownNames (R.w h).home).contains y = false := by
    cases hc : (ownNames (R.w h).home).contains y
    · rfl
    · rw [first_none_of_ownNames hw hc] at hl; cases hl
  have hlc : (R.w h).reads.index.first.contains y = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]; exact hl
  rw [R.dev_rk hh]
  rcases (mem_streamEnv_consts _ _).1 hci with ⟨p, hp, hcp⟩ | hc
  · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
    rw [declConstants_fillDecl] at hcp
    have hpe : p0 ∈ (R.w h).emitted.toList := by
      rw [hw.own] at hp0
      exact (Frontend.hoistNatOpGround_perm _ _).mem_iff.1 hp0
    exact own_reads_ctx hw (Array.mem_toList_iff.1 hpe)
      (recordReads_complete (.inl ⟨ci, hcp, .inl hy⟩)) hno (by simp [hlc])
  · obtain ⟨d, hd, hcd⟩ := ((mem_streamEnv_consts _ _).1 hc).resolve_right (by simp [Env.empty])
    exact (worker_ctx hw).2.2.1 d hd y (recordReads_complete (.inl ⟨ci, hcd, .inl hy⟩))

/-- **An emitted record's constant is a constant of its module's merge**, of its name, of a
kind past the statements' where it is no statement. -/
theorem emitted_names {h : Name} (hh : h ∈ R.names) (hx : R.x h = #[]) {p : Declaration} (hp : p ∈ (R.w h).emitted)
    {ci : ConstantInfo} (hci : ci ∈ declConstants p) :
    ∃ c : CEntry, (homeMerged (R.w h)).map[c.name]? = some c ∧ c.name = ci.name ∧
      (ci.isStmtKind = false → 4 ≤ c.kind.tag) := by
  have hw := R.facts₀ hh hx
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, hN, hO, hb, hem, hown⟩ :=
    home_records hw
  have hname : ci.name ∈ declNames p := List.mem_map_of_mem hci
  rcases declsOf_from hN hem hp with ⟨c, hc, hpe⟩ | ⟨ts, cts, rcs, hrf, hdo⟩
  · refine ⟨c, hc, ?_⟩
    rcases hck : c.kind with _ | ⟨v, hh', sf⟩ | ⟨v, all⟩ | ⟨v, iu⟩ | q | _ | _ | _
    all_goals first
      | (simp [entryDecl, hck] at hpe; done)
      | skip
    · -- an axiom
      simp only [entryDecl, hck, Option.some.injEq] at hpe
      subst hpe
      refine ⟨(declNames_stmt (.inl rfl) _ hname).symm, fun hns => ?_⟩
      simp only [declConstants] at hci
      split at hci
      · rw [List.mem_singleton.1 hci] at hns; cases hns
      · split at hci
        · cases hci
        · rw [List.mem_singleton.1 hci] at hns; cases hns
    · -- a definition
      by_cases hsf : sf = "safe"
      · subst hsf
        simp only [entryDecl, hck, Option.some.injEq] at hpe
        subst hpe
        refine ⟨(declNames_stmt (.inr ⟨_, _, rfl⟩) _ hname).symm, fun hns => ?_⟩
        simp only [declConstants, List.mem_singleton] at hci
        rw [hci] at hns; cases hns
      · simp [entryDecl, hck, hsf] at hpe
    · -- a theorem
      simp only [entryDecl, hck, Option.some.injEq] at hpe
      subst hpe
      simp only [declConstants, List.mem_singleton] at hci
      subst hci
      exact ⟨rfl, fun hns => by cases hns⟩
    · -- an opaque constant
      simp only [entryDecl, hck, Option.some.injEq] at hpe
      subst hpe
      simp only [declConstants, List.mem_singleton] at hci
      subst hci
      exact ⟨rfl, fun hns => by cases hns⟩
    · -- a quotient constant: the pin, at its own name
      obtain ⟨kq, rfl⟩ := entryDecl_quot hpe hck
      simp only [declConstants, List.mem_singleton] at hci
      subst hci
      have hhit := declsRun_quot (R.run h hh)
        (List.mem_map.2 ⟨_, emitted_own hw hp, rfl⟩)
      exact ⟨(quotAt_name_of_hit hhit).symm, fun _ => by simp [CKindF.tag]⟩
  · obtain ⟨-, hnames⟩ := declOfF_ind_names hdo
      (P := fun n => ∃ c : CEntry, (homeMerged (R.w h)).map[c.name]? = some c ∧ c.name = n ∧
        4 ≤ c.kind.tag)
      (fun t ht => by
        obtain ⟨c, hst, hcv, htg⟩ := hrf.1 t ht
        exact ⟨c, hcv, c, hst, rfl, by omega⟩)
      (fun t ht => by
        obtain ⟨c, hst, hcv, htg⟩ := hrf.2.1 t ht
        exact ⟨c, hcv, c, hst, rfl, by omega⟩)
      (fun t ht => by
        obtain ⟨c, hst, hcv, htg⟩ := hrf.2.2 t ht
        exact ⟨c, hcv, c, hst, rfl, by omega⟩)
    obtain ⟨c, hc, hcn, ht⟩ := hnames _ hname
    exact ⟨c, hc, hcn, fun _ => ht⟩

/-- **An emitted record's names are its module's own.** -/
theorem emitted_ownNames {h : Name} (hh : h ∈ R.names) (hx : R.x h = #[]) {p : Declaration}
    (hp : p ∈ (R.w h).emitted) {n : Name} (hn : n ∈ declNames p) :
    (ownNames (R.w h).home).contains n = true := by
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
  obtain ⟨c, hc, hcn, -⟩ := R.emitted_names hh hx hp hci
  have := (mergedOfList_spec _).2.1 _ _ hc
  rw [show ci.toConstantVal.name = c.name from hcn.symm]
  exact ownNames_mem (Array.mem_toList_iff.1 (List.mem_filter.1 this).1)

/-- **A name an own environment stores, loaded at the module, is in its context**: an own
record's names are the module's own, which no load holds. -/
theorem stored_of_own_find {h : Name} (hh : h ∈ R.names) (hx : R.x h = #[]) {y : Name}
    (hy : ((ownEnvOf (R.look h) fs h (R.w h)).find? y).isSome = true)
    (hl : ((R.w h).reads.index.first[y]?).isSome = true) :
    ((R.dev (R.rk h)).context.find? y).isSome = true := by
  have hw := R.facts₀ hh hx
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hy
  have hn := Env.find?_name hci
  rw [R.dev_rk hh]
  rcases (mem_streamEnv_consts _ _).1 (Env.find?_mem hci) with ⟨p, hp, hcp⟩ | hc
  · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
    rw [declConstants_fillDecl] at hcp
    have hpe : p0 ∈ (R.w h).emitted.toList := by
      rw [hw.own] at hp0
      exact (Frontend.hoistNatOpGround_perm _ _).mem_iff.1 hp0
    have := R.emitted_ownNames hh hx (Array.mem_toList_iff.1 hpe) (List.mem_map_of_mem (f := fun c : ConstantInfo => c.toConstantVal.name) hcp)
    rw [show ci.toConstantVal.name = y from hn] at this
    rw [first_none_of_ownNames hw this] at hl
    cases hl
  · obtain ⟨d, hd, hcd⟩ := ((mem_streamEnv_consts _ _).1 hc).resolve_right (by simp [Env.empty])
    rw [← hn]
    exact stored_of_record hd (List.mem_map_of_mem hcd)

/-- **The context's copy of a name**: a copy of that name on the snapshot, at a level a load
reads. -/
theorem copyOf_facts {M : Name} (hM : M ∈ R.names) {y : Name} {s : Spot}
    (hs : copyOf (R.envOf M) (R.cap M).1 y = some s) :
    CopyAt (R.look M) fs s ∧ s.part.level ≠ .server ∧ s.pos.name = y := by
  obtain ⟨_, _, hrd⟩ := (R.facts M hM).reads
  obtain ⟨hparts, hindex⟩ := workerReads_index hrd
  have he : EnvOk (R.look M) fs (R.envOf M) := ⟨rfl, hparts, hindex⟩
  obtain ⟨-, -, -, -, -, hloc, -⟩ := R.cap_facts hM
  unfold copyOf at hs
  split at hs
  · rename_i i s' hi
    cases hs
    obtain ⟨a, b⟩ := importerSpot_copy he hi
    refine ⟨a, b, ?_⟩
    obtain ⟨-, hfirst, -⟩ := workerIndex_copies hrd
    unfold importerSpot at hi
    obtain ⟨cp, hcp, hi⟩ := bind_some_left hi
    obtain ⟨q, hq, hi⟩ := bind_some_left hi
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨-, rfl⟩ := hi
    obtain ⟨q', hq', hn⟩ := hfirst y cp hcp
    have hq2 : (R.w M).reads.index.at cp = some q := hq
    rw [hq2] at hq'; cases hq'; exact hn
  · obtain ⟨-, hlv, hcp, -, hn⟩ := hloc y s hs
    exact ⟨hcp, by rw [hlv]; decide, hn⟩

/-- **A context name whose copy is of a statement kind is stored by its statement**, read at that
copy: its constant is a statement kind of the copy's statement, the copy is on the snapshot, at a
level a load reads, not unsafe or partial, of a module of the run, and the name is not the
tolerated axiom's. -/
theorem ctx_stmt {M : Name} (hM : M ∈ R.names) {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) {s : Spot}
    (hs : copyOf (R.envOf M) (R.cap M).1 y = some s) {r : Region} {cv : ConstantVal}
    {k : CKindF Name Unit} (hr : PartRegion (R.look M) fs s.part r) (hst : StmtSkel r s.pos.loc cv k)
    (hk : k.tag < 4) :
    ∃ ci, (R.dev (R.rk M)).context.find? y = some ci ∧ ci.toConstantVal = cv ∧
      ci.isStmtKind = true ∧ CopyAt (R.look M) fs s ∧ s.part.level ≠ .server ∧
      s.pos.skipped = false ∧ cv.name = y ∧ y ≠ sorryAxName ∧ s.part.mod ∈ R.names ∧
      R.x s.part.mod = #[] := by
  have hw := R.facts M hM
  obtain ⟨k0, d, hm, hk0, hh, hyd⟩ := R.ctx_record hM hy
  obtain ⟨-, hrec, -⟩ := R.cap_facts hM
  obtain ⟨⟨x, hx, s', hs', hmod', hra⟩, hall, -⟩ := hrec k0 d hm hk0 hh
  obtain ⟨s'', hs'', hmod⟩ := hall y hyd
  rw [hs] at hs''
  cases hs''
  obtain ⟨hhm, -, hxm⟩ := R.home_rank hM hh
  have hwm := R.facts₀ hhm hxm
  have hrun : OwnRun .verified maxNatSize (R.look hm) fs hm (R.w hm) := ⟨_, R.run hm hhm⟩
  obtain ⟨f, r0, a, sk, skels, hf, -⟩ := home_records hwm
  have hf' : ModelIO.CanGive (readFiles (R.look hm) s.part.mod .private) fs (.ok f) := by
    rw [hmod]; exact hf
  obtain ⟨hcp, hlv, hnm⟩ := R.copyOf_facts hM hs
  have hcpH := R.copy_own' (R.trims M) hhm hmod hcp
  have hrH := R.region_own (R.trims M) hhm hmod hr
  have hdm : d ∈ (R.w M).reach.ctx.toList :=
    Array.mem_toList_iff.2 (Array.mem_of_getElem? hk0)
  have hfind : ∀ ci ∈ declConstants d, (R.dev (R.rk M)).context.find? ci.name = some ci := by
    intro ci hci
    rw [R.dev_rk hM]
    exact find?_of_nodup (nodupNames_streamEnv hw.nodup)
      ((mem_streamEnv_consts _ _).2 (.inl ⟨d, hdm, hci⟩))
  have hcvn : cv.name = s.pos.name := copyAt_stmt_name hcp hr hst
  have hcvy : cv.name = y := hcvn.trans hnm
  have hpr : ∃ p ∈ (R.w hm).emitted, Presents d p := by
    have := hra.recordFrom; rw [hmod'] at this
    exact recordFrom_presents (R.from_own (R.trims M) hhm this) hwm
  have hres : quotSoundName ∈ reservedBasisNames := by simp [reservedBasisNames]
  have hsq : sorryAxName ≠ quotSoundName := by decide
  cases hra with
  | @stmt x1 s1 r1 cv1 k1 hs1 hl1 hr1 hst1 hsk1 hg hq hd1 hred =>
    have hxy : x = y := (declNames_stmt (.inl rfl) x hx).trans (declNames_stmt (.inl rfl) y hyd).symm
    subst x
    rw [hs] at hs'
    cases hs'
    obtain ⟨h1, h2⟩ := stmtSkel_unique (partRegion_unique hf' (R.region_own (R.trims M) hhm hmod hr1) hrH ▸ hst1) hst
    subst cv1 k1
    have hsy : cv.name ≠ sorryAxName := by
      intro he
      simp [declNames, declConstants, he, hsq] at hyd
    by_cases hqs : cv.name = quotSoundName
    · -- `Quot.sound`: the pinned constant, the copy's statement where its home accepted it
      have hyq : y = (quotAt .sound cv).name := by
        simpa [declNames, declConstants, hqs, ConstantInfo.name] using hyd
      obtain ⟨p, hp, hpres⟩ := hpr
      have hqmem : quotAt .sound cv ∈ declConstants p := by
        rcases hpres with ⟨hperm, -⟩ | ⟨he, -⟩
        · exact hperm.mem_iff.1 (by simp [declConstants, hqs])
        · have hb := R.own_basis hhm hxm hp
          cases p with
          | axiomDecl c =>
            simp only [stmtOf, Declaration.axiomDecl.injEq] at he
            subst he; simp [declConstants, hqs]
          | defnDecl c v hh =>
            simp only [stmtOf, Declaration.axiomDecl.injEq] at he
            subst he; simp [basisNamesOk, hqs] at hb; exact absurd hres hb
          | thmDecl c v =>
            simp only [stmtOf, Declaration.axiomDecl.injEq] at he
            subst he; simp [basisNamesOk, hqs] at hb; exact absurd hres hb
          | opaqueDecl c v =>
            simp only [stmtOf, Declaration.axiomDecl.injEq] at he
            subst he; simp [basisNamesOk, hqs] at hb; exact absurd hres hb
          | quotDecl k c => simp [stmtOf] at he
          | indDecl b nP => simp [stmtOf] at he
      have hfO := find?_of_nodup (ownEnv_nodup hwm hrun)
        (own_mem_ownEnv (sp := R.look hm) (fs := fs) (M := hm) (emitted_own hwm hp) hqmem)
      obtain ⟨ci', hci', hcv', hks', -⟩ := copy_own hwm hrun hmod hcpH hlv hrH hst hsk1 hk hsy
      rw [← hyq, ← hcvy, hci'] at hfO
      cases hfO
      refine ⟨quotAt .sound cv, ?_, hcv', hks', hcp, hlv, hsk1, hcvy, hcvy ▸ hsy, hmod ▸ hhm, hmod ▸ hxm⟩
      have := hfind (quotAt .sound cv) (by simp [declConstants, hqs])
      rwa [← hyq] at this
    · refine ⟨.axiomInfo cv, ?_, rfl, rfl, hcp, hlv, hsk1, hcvy, hcvy ▸ hsy, hmod ▸ hhm, hmod ▸ hxm⟩
      have := hfind (.axiomInfo cv) (by simp [declConstants, hqs, hsy])
      rwa [show (ConstantInfo.axiomInfo cv).name = y from hcvy] at this
  | @entry s1 r1 r₀ e d1 cv1 k1 hs1 hl1 hr1 he hr₀ hst₀ hk1 hsk1 hd1 =>
    have hf'' : ModelIO.CanGive (readFiles (R.look hm) s'.part.mod .private) fs (.ok f) := by
      rw [hmod']; exact hf
    rw [partRegion_unique hf'' (R.region_own (R.trims M) hhm hmod' hr1)
      (R.region_own (R.trims M) hhm hmod' hr₀)] at he
    have htag : (CEntry.ofF e).kind.tag = 1 := by
      rw [show (CEntry.ofF e).kind = e.kind from rfl, (StmtSkel.entry hst₀ he).2, hk1]
    obtain ⟨v, hh', rfl⟩ := entryDecl_defn (recordOfEntry_eq hd1) htag
    have hxy : x = y := (declNames_stmt (.inr ⟨_, _, rfl⟩) x hx).trans
      (declNames_stmt (.inr ⟨_, _, rfl⟩) y hyd).symm
    subst x
    rw [hs] at hs'
    cases hs'
    obtain ⟨h1, h2⟩ := stmtSkel_unique (partRegion_unique hf' (R.region_own (R.trims M) hhm hmod hr₀) hrH ▸ hst₀) hst
    subst cv1 k1
    have hecv : (⟨(CEntry.ofF e).name, (CEntry.ofF e).levelParams, (CEntry.ofF e).type⟩ :
        ConstantVal) = cv := (StmtSkel.entry hst₀ he).1
    rw [hecv] at hpr hfind hyd
    obtain ⟨p, hp, hpres⟩ := hpr
    obtain ⟨v', hh'', rfl⟩ := defn_presents hpres
    have hsy : cv.name ≠ sorryAxName := declsRun_defn_sorry (R.run hm hhm)
      (List.mem_map.2 ⟨_, emitted_own hwm hp, rfl⟩)
    refine ⟨.defnInfo cv v hh', ?_, rfl, rfl, hcp, hlv, hsk1, hcvy, hcvy ▸ hsy, hmod ▸ hhm, hmod ▸ hxm⟩
    have := hfind (.defnInfo cv v hh') (by simp [declConstants])
    rwa [show (ConstantInfo.defnInfo cv v hh').name = y from hcvy] at this
  | @quot s1 r1 cv1 q d1 hs1 hl1 hr1 hst1 hd1 =>
    obtain ⟨kq, rfl⟩ := entryDecl_quot (recordOfEntry_eq hd1) rfl
    have hxy : x = y := by
      simp only [declNames, declConstants, List.map_cons, List.map_nil, List.mem_singleton] at hx hyd
      rw [hx, hyd]
    subst x
    rw [hs] at hs'
    cases hs'
    obtain ⟨-, rfl⟩ := stmtSkel_unique (partRegion_unique hf' (R.region_own (R.trims M) hhm hmod hr1) hrH ▸ hst1) hst
    simp [CKindF.tag] at hk
  | group hg =>
    -- a group read from the home's private part: its names are no statement's there
    obtain ⟨t, q, tE, np, ni, nn, all, cs, ir, iu, irf, mqs, cqs, tys, rest, t', rb, r₁, r₂, r₃, r₄,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hg
    obtain ⟨tys', ctors', recs', ts, cts, rcs, -, hdo, g1, g2, g3⟩ := groupRecord_res hd
    obtain ⟨⟨b, nP, rfl⟩, -⟩ := declOfF_ind_names hdo (P := fun _ => True)
      (fun t ht => by obtain ⟨c, -, hc⟩ := Forall₂.mem_left g1 t ht; exact ⟨c, hc.1, trivial⟩)
      (fun t ht => by obtain ⟨c, -, hc⟩ := Forall₂.mem_left g2 t ht; exact ⟨c, hc.1, trivial⟩)
      (fun t ht => by obtain ⟨c, -, hc⟩ := Forall₂.mem_left g3 t ht; exact ⟨c, hc.1, trivial⟩)
    obtain ⟨ci, hci, hcin⟩ := List.mem_map.1 hyd
    have hns : ci.isStmtKind = false := by
      simp only [declConstants] at hci
      split at hci
      · exact blockConstants_not_stmt _ hci
      · cases hci
    obtain ⟨p, hp, hpres⟩ := hpr
    have hcp' : ci ∈ declConstants p := by
      rcases hpres with ⟨hperm, -⟩ | ⟨he, -⟩
      · exact hperm.mem_iff.1 hci
      · cases p <;> simp only [stmtOf] at he <;>
          first | (cases he; done) | (rw [← he]; exact hci)
    obtain ⟨c, hc, hcn, htc⟩ := R.emitted_names hhm hxm hp hcp'
    have hcm := (mergedOfList_spec _).2.1 _ _ hc
    obtain ⟨q₁, hq₁, hq₁n, hq₁t⟩ :=
      home_const_pos hwm (Array.mem_toList_iff.1 (List.mem_filter.1 hcm).1)
    obtain ⟨q₂, hq₂, hq₂n, hq₂t⟩ := copy_private_pos hwm hmod hcpH hlv hrH hst hk
    have := own_pos_unique hwm hq₁ hq₂ (by rw [hq₁n, hq₂n, hnm, hcn]; exact hcin)
    subst this
    have := htc hns
    omega

/-- **A name a stored statement's type reads, other than its own, is stored before it.** -/
theorem rank_lt {M : Name} (hM : M ∈ R.names) {y : Name} {ci : ConstantInfo}
    (hci : (R.dev (R.rk M)).context.find? y = some ci) (hk : ci.isStmtKind = true) {c : Name}
    (hc : c ∈ ci.toConstantVal.type.readNames) (hne : c ≠ y) :
    (R.dev (R.rk M)).rank c < (R.dev (R.rk M)).rank y ∧
      ((R.dev (R.rk M)).context.find? c).isSome = true := by
  have hw := R.facts M hM
  rw [R.dev_rk hM] at hci ⊢
  change (streamEnv (R.w M).reach.ctx.toList).find? y = some ci at hci
  show (R.w M).reach.ctx.toList.findIdx _ < (R.w M).reach.ctx.toList.findIdx _ ∧
    ((streamEnv (R.w M).reach.ctx.toList).find? c).isSome = true
  generalize hL : (R.w M).reach.ctx.toList = L at hci
  have hnd : (L.flatMap declNames).Nodup := hL ▸ hw.nodup
  have hord := (worker_ctx hw).1
  rw [hL] at hord
  have hmem := Env.find?_mem hci
  have hyn : ci.name = y := Env.find?_name hci
  obtain ⟨d, hd, hcd⟩ := ((mem_streamEnv_consts L Env.empty).1 hmem).resolve_right
    (by simp [Env.empty])
  obtain ⟨k, hkL, rfl⟩ := List.getElem_of_mem hd
  have hone := stmt_single hcd hk
  have hdn : declNames L[k] = [y] := by
    simp only [declNames, hone, List.map_cons, List.map_nil]
    rw [← hyn]; rfl
  -- the first record storing a name is the one record storing it
  have first : ∀ (j : Nat) (hj : j < L.length) (n : Name), n ∈ declNames L[j] →
      L.findIdx (fun d => (declNames d).contains n) = j := by
    intro j hj n hn
    have hp : (fun d => (declNames d).contains n) L[j] = true := by simpa using hn
    have hle : L.findIdx (fun d => (declNames d).contains n) ≤ j := by
      refine Nat.le_of_not_lt fun hlt => ?_
      exact absurd hp (by simpa using List.not_of_lt_findIdx hlt)
    have hlt' : L.findIdx (fun d => (declNames d).contains n) < L.length := by omega
    have hpi := List.findIdx_getElem (w := hlt')
    refine Classical.byContradiction fun hne => ?_
    exact nodup_flatMap_pos hnd hlt' hj hne (by simpa using hpi) hn
  have hres := ((hord k hkL).1 ci (by rw [hone]; exact List.mem_singleton_self _)).1
  obtain ⟨ci', hci'⟩ := Option.isSome_iff_exists.1 (readNames_stored_of_resolve hres c hc)
  have hcn : ci'.name = c := Env.find?_name hci'
  obtain ⟨j, hj, hjk, hcj⟩ := prefix_record (Env.find?_mem hci')
  have hcj' : c ∈ declNames L[j] := by
    rw [← hcn]; exact List.mem_map_of_mem hcj
  have hjne : j ≠ k := by
    rintro rfl
    rw [hdn, List.mem_singleton] at hcj'
    exact hne hcj'
  refine ⟨?_, ?_⟩
  · rw [first j hj c hcj', first k hkL y (by rw [hdn]; exact List.mem_singleton_self _)]
    omega
  · simp only [Env.find?, List.find?_isSome]
    exact ⟨ci', mem_prefix_consts (Env.find?_mem hci'), by simp [← hcn, ConstantInfo.name]⟩

/-- **A reader stores the name it reads, where the name is loaded at it**: by the pair's origin,
a read of one of its own records, the statement of one of its copies an `agreeCheck` compared, or
of one of its copies of a clash's name. -/
theorem reader_ctx {M : Name} (hM : M ∈ R.names) {h y : Name} (hP : (h, y) ∈ (R.cap M).2.2)
    (hl : ((R.w h).reads.index.first[y]?).isSome = true) :
    ((R.dev (R.rk h)).context.find? y).isSome = true := by
  obtain ⟨-, hrec, -, -, -, -, hreach⟩ := R.cap_facts hM
  obtain ⟨hR, horig⟩ := hreach _ hP
  have hhN : h ∈ R.names := (R.reached_rank hM hR).1
  have hxN : R.x h = #[] := (R.reached_rank hM hR).2.2
  have hwh := R.facts₀ hhN hxN
  have hno : (ownNames (R.w h).home).contains y = false := by
    cases hc : (ownNames (R.w h).home).contains y
    · rfl
    · rw [first_none_of_ownNames hwh hc] at hl; cases hl
  have hlc : (R.w h).reads.index.first.contains y = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]; exact hl
  rcases horig with ⟨k, d, hd, hh, hy⟩ | ⟨h', v, y', s₂, hv, hs₂, hmod2, hsk2, rg, cv₂, k₂, hrg, hst,
      htag, hyn⟩ | ⟨k, d, hd, n, hn, cs, hcs, kc, hkc, hz1, hz2⟩
  · -- a record of home `h` reads `y`: its presentation of an own record of `h` does
    obtain ⟨⟨x, -, s, -, hmod, hra⟩, -⟩ := hrec k d h hd hh
    have hrf := hra.recordFrom
    rw [hmod] at hrf
    obtain ⟨p, hp, hpr⟩ := recordFrom_presents (R.from_own (R.trims M) hhN hrf) hwh
    rw [R.dev_rk hhN]
    exact own_reads_ctx hwh hp (presents_reads hpr (R.own_basis hhN hxN hp) hy) hno (by simp [hlc])
  · -- an `agreeCheck` partner read: a name of the statement of a copy of `h`
    obtain ⟨hcp, hlv, -⟩ := homeView_copy hv hs₂
    have hcpH := R.copy_own' (R.trims M) hhN hmod2.symm hcp
    have hrgH := R.region_own (R.trims M) hhN hmod2.symm hrg
    have hyn' : y ∈ cv₂.type.needs := by
      rcases needsGo_sound _ _ _ _ hyn with h0 | h0
      · simp at h0
      · exact h0
    by_cases hsy : cv₂.name = sorryAxName
    · -- the tolerated axiom: its home checked its statement, which no context record reads
      obtain ⟨e₁, p, hp, hpe, -, ht₁, hcv, -⟩ := copy_entry hwh hmod2.symm hcpH hlv hrgH hst hsk2 htag
      have hq : e₁.name ≠ quotSoundName := by
        rw [show e₁.name = cv₂.name from congrArg ConstantVal.name hcv, hsy]; decide
      have hrec := entryDecl_stmtRecord hpe ht₁ hq (fillOf (R.look h) fs #[⟨h, (R.w h).home.frontier⟩])
      rw [hcv] at hrec
      have hst' := own_type_stored ⟨_, R.run h hhN⟩
        (List.mem_map.2 ⟨_, emitted_own hwh hp, rfl⟩) hrec y
        (by rw [← needs_eq_readNames]; exact hyn')
      exact R.stored_of_own_find hhN hxN hst' hl
    · obtain ⟨ci, hfind, hcv, -, -, -⟩ := copy_own hwh ⟨_, R.run h hhN⟩ hmod2.symm hcpH hlv hrgH hst
        hsk2 htag hsy
      exact R.stored_of_own_const hhN hxN (Env.find?_mem hfind) (by rw [hcv]; exact hyn') hl
  · -- a clash partner read: a copy, at `h`, of a clash's name the context stores
    obtain ⟨_, _, hrd⟩ := (R.facts M hM).reads
    obtain ⟨cl, hcl, hcln, cp, kd, he, hk1⟩ := clashCopiesOf_spec hcs (k := kc.1) (cv := kc.2)
      (Array.mem_toList_iff.2 hkc)
    obtain ⟨q, hq, hcpq, ⟨rg, hrg, hstq⟩, hqn, hcvn⟩ := workerClash_stmt hrd hcl he
    have hmodq : (spotOf (R.w M).reads cp q).part.mod = h := by
      show (R.w M).reads.loads.nameAt cp.mod = h
      rw [← hk1]; exact hz1.symm
    obtain ⟨hgm, hwg⟩ : ∃ f, ModelIO.CanGive (readFiles (R.look h) (spotOf (R.w M).reads cp q).part.mod
        .private) fs (.ok f) := by
      obtain ⟨f, -, -, -, -, hf, -⟩ := home_records hwh
      exact ⟨f, by rw [hmodq]; exact hf⟩
    -- the context's copy of the clash's name: the index's first copy
    have hdn : d ∈ (R.w M).reach.ctx.toList := Array.mem_toList_iff.2 (Array.mem_of_getElem? hd)
    have hyn : ((R.dev (R.rk M)).context.find? n).isSome = true := by
      rw [R.dev_rk hM]; exact stored_of_record hdn hn
    obtain ⟨-, hfirst, hmore, hall, -, hcopy⟩ := workerIndex_copies hrd
    obtain ⟨cp₀, hf₀⟩ : ∃ cp₀, (R.w M).reads.index.first[n]? = some cp₀ := by
      rcases hall cp q hq with h1 | h1
      · rw [hqn, hcln] at h1; exact ⟨_, h1⟩
      · obtain ⟨-, cp₀, hf, -⟩ := hmore _ _ h1
        rw [hqn, hcln] at hf; exact ⟨_, hf⟩
    obtain ⟨q₀, hq₀, hq₀n⟩ := hfirst n cp₀ hf₀
    have hs₀ : copyOf (R.envOf M) (R.cap M).1 n = some (spotOf (R.w M).reads cp₀ q₀) := by
      unfold copyOf
      have : importerSpot (R.envOf M) n = some (cp₀.mod, spotOf (R.w M).reads cp₀ q₀) := by
        unfold importerSpot
        have e1 : (R.envOf M).wr.index.first[n]? = some cp₀ := hf₀
        have e2 : (R.envOf M).wr.index.at cp₀ = some q₀ := hq₀
        simp only [e1, e2, Option.bind_eq_bind, Option.bind_some, pure]
        rfl
      rw [this]
    -- its kind: one of a clash with the copy at `cp`
    obtain ⟨cl', hcl', -, ⟨cv', kd', he'⟩, cv₀, kd₀, he₀⟩ : ∃ cl' ∈ (R.w M).reads.clashes.toList,
        cl'.name = n ∧ (∃ cv kd, (cp, cv, kd) ∈ cl'.copies.toList) ∧
          ∃ cv kd, (cp₀, cv, kd) ∈ cl'.copies.toList := by
      by_cases hc : cp = cp₀
      · subst hc
        exact ⟨cl, hcl, hcln, ⟨_, _, he⟩, _, _, he⟩
      · exact workerClash_complete hrd hc hq hq₀ (hqn.trans hcln) hq₀n
    obtain ⟨q', hq', -, ⟨rg', hrg', hstq'⟩, -⟩ := workerClash_stmt hrd hcl' he'
    rw [hq] at hq'; cases hq'
    obtain ⟨rfl, rfl⟩ := stmtSkel_unique hstq (partRegion_unique hwg (R.region_own (R.trims M) hhN hmodq hrg')
      (R.region_own (R.trims M) hhN hmodq hrg) ▸ hstq')
    obtain ⟨q₀', hq₀', hcp₀, ⟨rg₀, hrg₀, hst₀⟩, -⟩ := workerClash_stmt hrd hcl' he₀
    rw [hq₀] at hq₀'; cases hq₀'
    obtain ⟨-, ht₀⟩ := workerClash_kinds hrd hcl' he₀ he₀
    obtain ⟨hsk, ht⟩ := workerClash_kinds hrd hcl' he' he₀
    obtain ⟨-, -, -, -, -, -, hsk₀, -, hnsy, -, -⟩ :=
      R.ctx_stmt hM hyn hs₀ hrg₀ hst₀ (by rcases ht₀ with h0 | h0 <;> rw [h0] <;> decide)
    have hskq : (spotOf (R.w M).reads cp q).pos.skipped = false := by
      rw [(copyAt_kind hcpq hrg hstq).2]
      change kd.skipped = false
      rw [show kd.skipped = kd₀.skipped from hsk, ← (copyAt_kind hcp₀ hrg₀ hst₀).2]
      exact hsk₀
    obtain ⟨ci, hfind, hcv, -, -, -⟩ := copy_own hwh ⟨_, R.run h hhN⟩ hmodq (R.copy_own' (R.trims M) hhN hmodq hcpq)
      (spotOf_level _ _ _) (R.region_own (R.trims M) hhN hmodq hrg) hstq hskq (by rcases ht with h0 | h0 <;> rw [h0] <;> decide)
      (by rw [hcvn, hcln]; exact hnsy)
    have hyn' : y ∈ kc.2.type.needs := by
      rcases needsGo_sound _ _ _ _ hz2 with h0 | h0
      · simp at h0
      · exact h0
    exact R.stored_of_own_const hhN hxN (Env.find?_mem hfind) (by rw [hcv]; exact hyn') hl

/-- **The names a context statement's type reads are passed as reads of its home**, the module
of its copy, which is of smaller rank. -/
theorem ctx_reads {M : Name} (hM : M ∈ R.names) {y : Name} {ci : ConstantInfo}
    (hci : (R.dev (R.rk M)).context.find? y = some ci) {s : Spot}
    (hs : copyOf (R.envOf M) (R.cap M).1 y = some s) :
    s.part.mod ∈ R.names ∧ R.rk s.part.mod < R.rk M ∧
      ∀ c ∈ ci.toConstantVal.type.readNames, R.Pr M (R.rk s.part.mod) c := by
  have hw := R.facts M hM
  have hci' := hci
  rw [R.dev_rk hM] at hci'
  obtain ⟨d, hd, hcd⟩ := ((mem_streamEnv_consts _ Env.empty).1 (Env.find?_mem hci')).resolve_right
    (by simp [Env.empty])
  obtain ⟨k, hm, hk, hh⟩ := worker_home hw hd
  obtain ⟨-, hrec, -⟩ := R.cap_facts hM
  obtain ⟨-, hall, hreads, -⟩ := hrec k d hm hk hh
  have hyd : y ∈ declNames d := by
    rw [← Env.find?_name hci]; exact List.mem_map_of_mem hcd
  obtain ⟨s', hs', hmod⟩ := hall y hyd
  rw [hs] at hs'
  cases hs'
  obtain ⟨hhm, hlt, -⟩ := R.home_rank hM hh
  refine ⟨hmod ▸ hhm, hmod ▸ hlt, fun c hc => ⟨_, rfl, ?_⟩⟩
  rw [hmod]
  exact hreads c (recordReads_complete (.inl ⟨ci, hcd, .inl (by rw [needs_eq_readNames]; exact hc)⟩))

end Run

end ConLeche.Driver.Compose
