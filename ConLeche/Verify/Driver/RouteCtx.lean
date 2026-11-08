module

public import ConLeche.Verify.Driver.ComposeReads
public import ConLeche.Verify.Driver.RouteWorker
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Frontend.Prepare

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
  simp only [List.mem_append, List.mem_map] at h
  have hR : ∀ l : List RecShape, ci ∈ blockRecs p l → ci.isStmtKind = false := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons a l ih =>
      intro h
      rcases List.mem_cons.1 h with rfl | h
      · rfl
      · exact ih h
  rcases h with (⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | h
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
theorem declsRun_basis {mode : CheckMode} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins ds p q) : ∀ d ∈ ds, basisNamesOk d = true := by
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

namespace Run

variable {sp : SearchPath} {fs : FS} (R : Run sp fs)

/-- **An emitted record of a module of the run passed the reserved names' check.** -/
theorem own_basis {h : Name} (hh : h ∈ R.names) {p : Declaration} (hp : p ∈ (R.w h).emitted) :
    basisNamesOk p = true := by
  have := declsRun_basis (R.run h hh) _
    (List.mem_map_of_mem (f := fillDecl (fillOf sp fs #[⟨h, (R.w h).home.frontier⟩]))
      (emitted_own (R.facts h hh) hp))
  cases p <;> exact this

/-- **A name an own constant's type reads, loaded at the module, is in its context**: the
constant is an own record's or a context record's, and either's reads are stored there. -/
theorem stored_of_own_const {h : Name} (hh : h ∈ R.names) {ci : ConstantInfo}
    (hci : ci ∈ (ownEnvOf sp fs h (R.w h)).consts) {y : Name}
    (hy : y ∈ ci.toConstantVal.type.needs)
    (hl : ((R.w h).reads.index.first[y]?).isSome = true) :
    ((R.dev (R.rk h)).context.find? y).isSome = true := by
  have hw := R.facts h hh
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

/-- **A context name whose copy is of a statement kind is stored by its statement**, read at that
copy: its constant is a statement kind of the copy's statement, the copy is on the snapshot, at a
level a load reads, not unsafe or partial, of a module of the run, and the name is not the
tolerated axiom's. -/
theorem ctx_stmt {M : Name} (hM : M ∈ R.names) {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) {s : Spot}
    (hs : copyOf (R.envOf M) (R.cap M).1 y = some s) {r : Region} {cv : ConstantVal}
    {k : CKindF Name Unit} (hr : PartRegion sp fs s.part r) (hst : StmtSkel r s.pos.loc cv k)
    (hk : k.tag < 4) :
    ∃ ci, (R.dev (R.rk M)).context.find? y = some ci ∧ ci.toConstantVal = cv ∧
      ci.isStmtKind = true ∧ CopyAt sp fs s ∧ s.part.level ≠ .server ∧
      s.pos.skipped = false ∧ cv.name = y ∧ y ≠ sorryAxName ∧ s.part.mod ∈ R.names := by
  sorry

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
  have hwh := R.facts h hhN
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
    obtain ⟨p, hp, hpr⟩ := recordFrom_presents hrf hwh
    rw [R.dev_rk hhN]
    exact own_reads_ctx hwh hp (presents_reads hpr (R.own_basis hhN hp) hy) hno (by simp [hlc])
  · -- an `agreeCheck` partner read: a name of the statement of a copy of `h`
    obtain ⟨hcp, hlv, -⟩ := homeView_copy hv hs₂
    have hyn' : y ∈ cv₂.type.needs := by
      rcases needsGo_sound _ _ _ _ hyn with h0 | h0
      · simp at h0
      · exact h0
    by_cases hsy : cv₂.name = sorryAxName
    · sorry
    · obtain ⟨ci, hfind, hcv, -, -, -⟩ := copy_own' hwh ⟨_, R.run h hhN⟩ hmod2.symm hcp hlv hrg hst
        hsk2 htag hsy
      exact R.stored_of_own_const hhN (Env.find?_mem hfind) (by rw [hcv]; exact hyn') hl
  · sorry

end Run

end ConLeche.Driver.Compose
