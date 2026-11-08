module

public import ConLeche.Verify.Driver.ComposeReads
public import ConLeche.Verify.Driver.RouteWorker
import ConLeche.Verify.Driver.Reach

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

namespace Run

variable {sp : SearchPath} {fs : FS} (R : Run sp fs)

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
  sorry

end Run

end ConLeche.Driver.Compose
