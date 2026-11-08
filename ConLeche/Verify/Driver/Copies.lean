module

public import ConLeche.Verify.Driver.Groups
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.DeclPushes
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
  obtain ⟨loc, sP, s1, hloc, hsP, hs1, hn1, hskq, hskP, hbeh⟩ :=
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

end ConLeche.Driver
