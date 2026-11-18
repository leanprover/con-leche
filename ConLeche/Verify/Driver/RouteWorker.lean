module

public import ConLeche.Verify.Driver.Copies
public import ConLeche.Verify.Driver.Clashes
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Driver.Compose
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Reads
public import ConLeche.Verify.Frontend.Olean.Emit

/-!
# The routes' facts about one worker

What the routes of the composition (task #501, `Routes.lean`) need of one accepted worker,
model-free:

* `readNames_needsGo` — the reach's memoized walk lists every name an expression reads;
* `first_none_of_ownNames` — no name of a module's private view is loaded (freshness);
* `first_of_at` — a copy the name index records makes its name loaded;
* `homeView_copy`, `spotOf_level` — a view's copy, and a loaded copy, is a copy on the snapshot
  at a level a load reads;
* `workerClash_kinds` — a clash's copies are theorems or axioms, all unsafe or none (Lean's
  merge rule, `subsumesF`);
* `copy_own` — **a copy's constant**: a copy of a statement kind at any level its module `M`
  loads has, in `M`'s own environment, a statement-kind constant of the copy's statement (at
  `Quot.sound` the pin, which is the copy's statement where its home accepted it), a theorem where
  the copy or the private constant behind it is one; the statement's type does not read its own
  name.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-- `Expr.needs` is `Expr.readNames`. -/
theorem needs_eq_readNames (e : Expr) : e.needs = e.readNames := by
  induction e with
  | lit l => cases l <;> rfl
  | fvar _ _ ih => simp only [Expr.needs, Expr.readNames, ih]
  | app f a ihf iha => simp only [Expr.needs, Expr.readNames, ihf, iha]
  | lam t b iht ihb => simp only [Expr.needs, Expr.readNames, iht, ihb]
  | forallE t b iht ihb => simp only [Expr.needs, Expr.readNames, iht, ihb]
  | letE t v b iht ihv ihb => simp only [Expr.needs, Expr.readNames, iht, ihv, ihb]
  | proj s i e ih => simp only [Expr.needs, Expr.readNames, ih]
  | _ => rfl

/-- **The memoized walk from nothing lists every name an expression reads.** -/
theorem readNames_needsGo {e : Expr} {n : Name} (h : n ∈ e.readNames) :
    n ∈ (needsGo {} #[] e).2 := by
  have hi : NeedsInv (({} : Std.HashSet Expr), (#[] : Array Name)) := fun e he => by simp at he
  exact (needsGo_spec e {} #[] hi).2.2 n (by rw [needs_eq_readNames]; exact h)

variable {sp : SearchPath} {fs : FS}

theorem ownNames_foldl (n : Name) : ∀ (l : List CEntry) (s : Std.HashSet Name),
    (l.foldl (fun s c => s.insert c.name) s).contains n = true →
      s.contains n = true ∨ ∃ c ∈ l, c.name = n
  | [], _, h => .inl h
  | c :: l, s, h => by
    rcases ownNames_foldl n l _ h with h' | ⟨c', hc', he⟩
    · rw [Std.HashSet.contains_insert] at h'
      rcases Bool.or_eq_true_iff.1 h' with h' | h'
      · exact .inr ⟨c, List.mem_cons_self, beq_iff_eq.1 h'⟩
      · exact .inl h'
    · exact .inr ⟨c', List.mem_cons_of_mem _ hc', he⟩

/-- A name of a module's private view is one of its loaded constants'. -/
theorem mem_ownNames {l : Loaded} {n : Name} (h : (ownNames l).contains n = true) :
    ∃ c ∈ l.constants.toList, c.name = n := by
  unfold ownNames at h
  rw [← Array.foldl_toList] at h
  rcases ownNames_foldl n _ _ h with h | h
  · simp at h
  · exact h

/-- **No name of a module's private view is loaded** (the worker's freshness). -/
theorem first_none_of_ownNames {M : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs M jobs w) {n : Name} (hn : (ownNames w.home).contains n = true) :
    w.reads.index.first[n]? = none := by
  obtain ⟨c, hc, rfl⟩ := mem_ownNames hn
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, hskels, -, -, hload, -⟩ := home_records hw
  obtain ⟨r', a', sk', skels', hreg', -, hsk', hskels', -, -, hlazy⟩ := loadAt_spec hload
  rw [hreg] at hreg'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg')
  rw [hsk] at hsk'
  cases hsk'
  rw [hskels] at hskels'
  cases hskels'
  obtain ⟨s, hs, hent⟩ := hlazy.to_skel c hc
  obtain ⟨loc, hloc, hls⟩ := mapM_mem_inv hskels hs
  have hnt := readPartNames_of_all hf (worker_ownTable hw)
  simp only [ModFiles.upTo, readNamePositions, hreg, Option.bind_eq_bind, Option.bind_some] at hnt
  obtain ⟨q, hq, -, hqn⟩ := namePositionsAt_complete hnt hsk hloc hls (lazyEntry_name hent)
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨own, -, -, -, -, hown, hfresh, -⟩ := workerReads_loads hr
  rw [hown] at hq
  have h := hfresh q hq
  rw [Std.HashMap.contains_eq_isSome_getElem?, hqn] at h
  exact Option.not_isSome_iff_eq_none.1 (by simpa using h)

/-- **A copy the name index records makes its name loaded.** -/
theorem first_of_at {M : Name} {jobs : Nat} {w : WorkerRead} {x : Array ImportRec}
    (hw : WorkerFacts sp fs M jobs w x)
    {cp : Copy} {q : NamePosition} (hq : w.reads.index.at cp = some q) :
    (w.reads.index.first[q.name]?).isSome = true := by
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨-, -, hmore, hall, -, -⟩ := workerIndex_copies hr
  rcases hall cp q hq with h | h
  · rw [h]; rfl
  · obtain ⟨-, cp₀, hf, -⟩ := hmore _ _ h
    rw [hf]; rfl

/-- **A loaded copy is at a level a load reads.** -/
theorem spotOf_level (wr : WorkerReads) (cp : Copy) (q : NamePosition) :
    (spotOf wr cp q).part.level ≠ .server := by
  simp only [spotOf, LoadFlags.level]
  split <;> decide

/-- The first copy of a name in some parts is of that name. -/
theorem firstIn_name {y : Name} : ∀ (l : List (PartKey × NamePositions)) {s : Spot},
    firstIn l y = some s → s.pos.name = y
  | [], _, h => by simp [firstIn] at h
  | (k, t) :: l, s, h => by
    simp only [firstIn] at h
    split at h
    · rename_i q hq
      cases h
      have := List.find?_some hq
      exact beq_iff_eq.1 this
    · exact firstIn_name l h

/-- A view's part is at a level a load reads. -/
theorem viewKeys_level {h : Name} {ld : Loads} {k : PartKey} (hk : k ∈ viewKeys h ld) :
    k.level ≠ .server := by
  unfold viewKeys at hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact (by decide : OLeanLevel.private ≠ .server)
  · obtain ⟨⟨m, fl⟩, -, rfl⟩ := List.mem_map.1 hk
    simp only [LoadFlags.level]
    split <;> decide

/-- **A view's copy of `y`** is a copy on the snapshot, of `y`, at a level a load reads. -/
theorem homeView_copy {h y : Name} {v : Std.HashMap Name Spot} {s : Spot}
    (hv : HomeView sp fs h v) (hs : v[y]? = some s) :
    CopyAt sp fs s ∧ s.part.level ≠ .server ∧ s.pos.name = y := by
  obtain ⟨-, ld, ts, -, -, -, hparts, rfl⟩ := hv
  obtain ⟨-, t, hkt, hq⟩ := Compose.homeView_part hs
  refine ⟨⟨t, hparts _ _ hkt, hq⟩, viewKeys_level (List.of_mem_zip hkt).1, ?_⟩
  rw [viewFold_get] at hs
  simp only [Std.HashMap.getElem?_empty, Option.none_or] at hs
  exact firstIn_name _ hs

/-- Lean's merge rule passes theorems and axioms only, both unsafe or neither. -/
theorem subsumesF_kinds {E E' : Type} {headTy : Name → Option Expr} {cv₁ : ConstantVal}
    {k₁ : CKindF Name E} {cv₂ : ConstantVal} {k₂ : CKindF Name E'}
    (h : subsumesF headTy cv₁ k₁ cv₂ k₂ = true) :
    k₁.skipped = k₂.skipped ∧ (k₁.tag = 0 ∨ k₁.tag = 2) ∧ (k₂.tag = 0 ∨ k₂.tag = 2) := by
  simp only [subsumesF, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases k₁ <;> cases k₂ <;> simp_all [CKindF.skipped, CKindF.tag]

/-- The clash rule's fold over at least one more copy: every copy has the kept one's filter, and
is a theorem or an axiom. -/
theorem clashKinds_fold {X : Type} (kd : X → CKindF Name Unit) {g : X → X → Except CheckError X}
    (hg : ∀ a b r, g a b = .ok r → (kd a).skipped = (kd b).skipped ∧
      ((kd a).tag = 0 ∨ (kd a).tag = 2) ∧ ((kd b).tag = 0 ∨ (kd b).tag = 2) ∧ (r = a ∨ r = b)) :
    ∀ (rest : List X) (kept r : X), rest ≠ [] → rest.foldlM g kept = .ok r →
      ∀ x ∈ kept :: rest, (kd x).skipped = (kd kept).skipped ∧ ((kd x).tag = 0 ∨ (kd x).tag = 2)
  | [], _, _, hne, _ => absurd rfl hne
  | b :: rest, kept, r, _, h => by
    simp only [List.foldlM_cons] at h
    cases hb : g kept b with
    | error e => rw [hb] at h; cases h
    | ok r' =>
      rw [hb] at h
      obtain ⟨hs, hk, hbt, hr'⟩ := hg kept b r' hb
      have hr's : (kd r').skipped = (kd kept).skipped := by
        rcases hr' with rfl | rfl
        · rfl
        · exact hs.symm
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨rfl, hk⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hs.symm, hbt⟩
      cases rest with
      | nil => simp at hx
      | cons c rest =>
        obtain ⟨h1, h2⟩ := clashKinds_fold kd hg (c :: rest) r' r (by simp) h x
          (List.mem_cons_of_mem _ hx)
        exact ⟨h1.trans hr's, h2⟩

/-- `clashCopies`' fold lists two copies or more per name. -/
theorem ccStep_size (first : Std.HashMap Name Copy) :
    ∀ (l : List (Name × Copy)) (m : Std.HashMap Name (Array Copy)),
      (∀ (n : Name) (a : Array Copy), m[n]? = some a → 2 ≤ a.size) →
      ∀ (n : Name) (a : Array Copy), (l.foldl (ccStep first) m)[n]? = some a → 2 ≤ a.size
  | [], _, hm => hm
  | (n', c) :: l, m, hm => ccStep_size first l _ fun (n : Name) (a : Array Copy) h => by
    simp only [ccStep, Std.HashMap.getElem?_alter] at h
    split at h
    · cases hm' : m[n']? with
      | none => rw [hm'] at h; cases h; simp
      | some a₀ =>
        rw [hm'] at h
        cases h
        have := hm n' a₀ hm'
        simp only [Array.size_push]
        omega
    · exact hm n a h

theorem length_filterMap_all {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    rw [List.filterMap_cons, hy, List.length_cons, List.length_cons,
      length_filterMap_all fun z hz => h z (List.mem_cons_of_mem _ hz)]

/-- **A clash lists two copies or more.** -/
theorem workerClash_two {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {x : Array ImportRec} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs x : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {cl : Clash} (hcl : cl ∈ wr.clashes.toList) : 2 ≤ cl.copies.toList.length := by
  obtain ⟨-, ⟨infos, hinf, hcls⟩, -⟩ := workerReads_open h
  obtain ⟨-, hcomp⟩ := readInfos_ok hinf
  rw [hcls, Array.toList_map] at hcl
  obtain ⟨⟨n, a⟩, ha, rfl⟩ := List.mem_map.1 hcl
  have h2 : 2 ≤ a.size := by
    have ha' := Array.mem_toList_iff.1 ha
    rw [clashCopies_eq, Std.HashMap.mem_toArray_iff_getElem?_eq_some, ← Array.foldl_toList] at ha'
    exact ccStep_size _ _ {} (fun n a h => by simp at h) n a ha'
  simp only [Array.toList_filterMap]
  rw [length_filterMap_all fun c hc => by
    have hreq : c ∈ ((clashCopies wr.index).flatMap (·.2)).toList := by
      simp only [Array.toList_flatMap, List.mem_flatMap]
      exact ⟨(n, a), ha, hc⟩
    simpa using hcomp c hreq]
  simpa using h2

/-- **A clash's copies are theorems or axioms, all unsafe or none**: Lean's merge rule
(`subsumesF`) passed on it. -/
theorem workerClash_kinds {m : Name} {jobs : Nat} {x : Array ImportRec} {wr : WorkerReads} {hs hs' : HS}
    (h : (workerReads (.ofPath sp) m jobs x : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {cl : Clash} (hcl : cl ∈ wr.clashes.toList) {e₁ e₂ : Copy × ConstantVal × CKindF Name Unit}
    (h₁ : e₁ ∈ cl.copies.toList) (h₂ : e₂ ∈ cl.copies.toList) :
    e₁.2.2.skipped = e₂.2.2.skipped ∧ (e₁.2.2.tag = 0 ∨ e₁.2.2.tag = 2) := by
  have h2 := workerClash_two h hcl
  obtain ⟨-, -, headTy, hfm⟩ := workerReads_open h
  have hok := forM_ok_all hfm cl hcl
  simp only [clashOk] at hok
  generalize hcs : cl.copies.toList = l at hok h₁ h₂ h2
  rcases l with _ | ⟨k, rest⟩
  · simp at h₁
  simp only at hok
  generalize hr : List.foldlM (m := Except CheckError) _ k rest = res at hok
  rcases res with e | r
  · cases hok
  have hall := clashKinds_fold (fun x : Copy × ConstantVal × CKindF Name Unit => x.2.2)
    (fun a b r hab => by
      obtain ⟨_, cv₂, k₂⟩ := a
      obtain ⟨_, cv₁, k₁⟩ := b
      simp only at hab ⊢
      split at hab
      · rename_i h1
        obtain ⟨hs, ht₁, ht₂⟩ := subsumesF_kinds h1
        exact ⟨hs.symm, ht₂, ht₁, .inr (Except.ok.inj hab).symm⟩
      · split at hab
        · rename_i h1
          obtain ⟨hs, ht₂, ht₁⟩ := subsumesF_kinds h1
          exact ⟨hs, ht₂, ht₁, .inl (Except.ok.inj hab).symm⟩
        · cases hab) rest k r (by rintro rfl; simp at h2) hr
  obtain ⟨a1, a2⟩ := hall e₁ h₁
  obtain ⟨b1, -⟩ := hall e₂ h₂
  exact ⟨a1.trans b1.symm, a2⟩

/-- **The own entry behind a copy**: a copy of `M`'s part, at a level a load reads, of a statement
kind, not filtered out, stands for a constant of the home's merge, of the copy's statement, kept
and of a statement kind, whose record is emitted; a theorem where the copy or the private constant
behind it is one. -/
theorem copy_entry {M : Name} {jobs : Nat} {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w)
    {s : Spot} (hmod : s.part.mod = M) (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server)
    {r : Region} (hr : PartRegion sp fs s.part r) {cv : ConstantVal} {k : CKindF Name Unit}
    (hst : StmtSkel r s.pos.loc cv k) (hsk0 : s.pos.skipped = false) (htag : k.tag < 4) :
    ∃ (e₁ : CEntry) (p : Declaration), p ∈ w.emitted ∧ entryDecl e₁ = some p ∧
      e₁.skipped = false ∧ e₁.kind.tag < 4 ∧
      (⟨e₁.name, e₁.levelParams, e₁.type⟩ : ConstantVal) = cv ∧
      ((k.tag = 2 ∨ ∃ q : Spot, CopyAt sp fs q ∧ q.part = ⟨M, .private⟩ ∧
          q.pos.name = s.pos.name ∧ q.pos.tag = 2) → e₁.kind.tag = 2) := by
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
  refine ⟨e₁, p, hp, hpe, hsk₁, ht₁, hst₁, fun hthm' => ?_⟩
  rw [hk, htagE]
  rcases hthm' with h2 | ⟨q, hqc, hqp, hqn, hqt⟩
  · exact hthm h2
  · rw [← hqt]
    exact (private_tag hf hreg hsk hskels hcn hqc hqp hloc hsP (by rw [hqn, hpos]; exact hn)).symm

/-- **A statement-kind entry's record**: a statement record installing its statement as a
statement kind (a theorem for a theorem), or `Quot.sound`'s axiom. -/
theorem entryDecl_stmt {e : CEntry} {p : Declaration} {cv : ConstantVal}
    (hcv : (⟨e.name, e.levelParams, e.type⟩ : ConstantVal) = cv) (hp : entryDecl e = some p)
    (ht : e.kind.tag < 4) (hsk : e.skipped = false) (hs : cv.name ≠ sorryAxName) :
    (StmtRecord p cv ∧ ∃ ci ∈ declConstants p, ci.toConstantVal = cv ∧ ci.isStmtKind = true ∧
      (e.kind.tag = 2 → ∃ cv', ci = .thmInfo cv')) ∨
    (p = .axiomDecl cv ∧ cv.name = quotSoundName ∧ e.kind.tag = 0) := by
  subst hcv
  rcases e with ⟨⟨n, l, t, k⟩, u⟩
  simp only at hs ⊢
  cases k with
  | ax u' =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    by_cases hq : n = quotSoundName
    · exact .inr ⟨rfl, hq, rfl⟩
    · refine .inl ⟨.inr (.inr (.inr ⟨rfl, hq⟩)), .axiomInfo ⟨n, l, t⟩, ?_, rfl, rfl,
        fun h => by simp [CKindF.tag] at h⟩
      simp [declConstants, hq, hs]
  | defn v hh sf =>
    have hsf : sf = "safe" := by simpa [CEntry.skipped, CKindF.skipped] using hsk
    subst hsf
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact .inl ⟨.inl ⟨_, _, rfl⟩, _, List.mem_singleton_self _, rfl, rfl,
      fun h => by simp [CKindF.tag] at h⟩
  | thm v all =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact .inl ⟨.inr (.inl ⟨_, rfl⟩), _, List.mem_singleton_self _, rfl, rfl, fun _ => ⟨_, rfl⟩⟩
  | opaq v u' =>
    simp only [entryDecl, Option.some.injEq] at hp
    subst hp
    exact .inl ⟨.inr (.inr (.inl ⟨_, rfl⟩)), _, List.mem_singleton_self _, rfl, rfl,
      fun h => by simp [CKindF.tag] at h⟩
  | _ => simp [CKindF.tag] at ht

theorem stmtRecord_fill (F : Expr → Expr) {d : Declaration} {cv : ConstantVal}
    (h : StmtRecord d cv) : StmtRecord (fillDecl F d) cv := by
  rcases h with ⟨v, hh, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨rfl, hq⟩
  · exact .inl ⟨v, hh, rfl⟩
  · exact .inr (.inl ⟨F v, rfl⟩)
  · exact .inr (.inr (.inl ⟨v, rfl⟩))
  · exact .inr (.inr (.inr ⟨rfl, hq⟩))

/-- An accepted quotient record is its pin. -/
theorem checkQuotRecordC_hit (fe : FEnv) (k : QuotKind) (cv : ConstantVal) :
    Yields (checkQuotRecordC fe k cv) (fun _ => quotPinHit k cv = true) := by
  by_cases h : quotPinHit k cv = true
  · exact Yields.const h
  · unfold checkQuotRecordC
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact Yields.ofThrowBind

/-- **An accepted `Quot.sound` axiom is its pin.** -/
theorem checkDeclStepC_quot {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {cv : ConstantVal} (hq : cv.name = quotSoundName) :
    Yields (checkDeclStepC mode pins fe (.axiomDecl cv)) (fun _ => quotPinHit .sound cv = true) := by
  unfold checkDeclStepC checkDeclC
  ybind
  refine Yields.bind' (Q := fun _ => quotPinHit .sound cv = true) ?_ fun _ h => Yields.const h
  unfold checkDeclKindC
  simp only [hq, ↓reduceIte]
  exact checkQuotRecordC_hit _ _ _

theorem declsRun_quot_hit {mode : CheckMode} {maxNatSize : Nat} {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv} (h : DeclsRun mode pins maxNatSize ds p q) :
    ∀ cv, Declaration.axiomDecl cv ∈ ds → cv.name = quotSoundName → quotPinHit .sound cv = true := by
  induction h with
  | nil => exact fun _ h _ => nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    intro cv hd hq
    rcases List.mem_cons.mp hd with he | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      rw [← he] at hC
      exact checkDeclStepC_quot hq _ _ _ hC
    · exact ih cv hd hq

/-- `Quot.sound`'s pin installs the record's statement. -/
theorem quotAt_sound {cv : ConstantVal} (h : quotPinHit .sound cv = true) :
    quotAt .sound cv = .axiomInfo cv ∧
      cv.type = (quotPin .sound).toConstantVal.type.instantiateLevelParams
        (quotPin .sound).toConstantVal.levelParams (cv.levelParams.map .param) := by
  simp only [quotPinHit, Bool.and_eq_true] at h
  have he := ConstantVal.eq_of_beqP h.2
  refine ⟨?_, by rw [he]; rfl⟩
  conv => rhs; rw [he]
  rfl

theorem readNames_instantiateLevelParams (ks : List Name) (us : List Level) (e : Expr) :
    (e.instantiateLevelParams ks us).readNames = e.readNames := by
  induction e with
  | lit l => rfl
  | fvar _ _ ih => simp only [Expr.instantiateLevelParams, Expr.readNames, ih]
  | app f a ihf iha => simp only [Expr.instantiateLevelParams, Expr.readNames, ihf, iha]
  | lam t b iht ihb => simp only [Expr.instantiateLevelParams, Expr.readNames, iht, ihb]
  | forallE t b iht ihb => simp only [Expr.instantiateLevelParams, Expr.readNames, iht, ihb]
  | letE t v b iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, Expr.readNames, iht, ihv, ihb]
  | proj s i e ih => simp only [Expr.instantiateLevelParams, Expr.readNames, ih]
  | _ => rfl

/-- **A copy's constant in its module's own environment**: a copy of `M`'s part, at a level a
load reads, of a statement kind, not filtered out, at no `sorryAx`, has in `M`'s own environment
a statement-kind constant of the copy's statement, a theorem where the copy or the private
constant behind it is one; and the statement's type does not read its own name. -/
theorem copy_own {mode : CheckMode} {maxNatSize : Nat} {M : Name} {jobs : Nat}
    {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w) (hrun : OwnRun mode maxNatSize sp fs M w)
    {s : Spot} (hmod : s.part.mod = M) (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server)
    {r : Region} (hr : PartRegion sp fs s.part r) {cv : ConstantVal} {k : CKindF Name Unit}
    (hst : StmtSkel r s.pos.loc cv k) (hsk0 : s.pos.skipped = false) (htag : k.tag < 4)
    (hsy : cv.name ≠ sorryAxName) :
    ∃ ci, (ownEnvOf sp fs M w).find? cv.name = some ci ∧ ci.toConstantVal = cv ∧
      ci.isStmtKind = true ∧
      ((k.tag = 2 ∨ ∃ q : Spot, CopyAt sp fs q ∧ q.part = ⟨M, .private⟩ ∧
          q.pos.name = s.pos.name ∧ q.pos.tag = 2) → ∃ cv', ci = .thmInfo cv') ∧
      cv.name ∉ cv.type.readNames := by
  obtain ⟨e₁, p, hp, hpe, hsk₁, ht₁, hst₁, hthm⟩ := copy_entry hw hmod hs hl hr hst hsk0 htag
  have hpo := emitted_own hw hp
  have hpd : fillDecl (fillOf sp fs #[⟨M, w.home.frontier⟩]) p ∈ ownDeclsOf sp fs M w :=
    List.mem_map_of_mem hpo
  rcases entryDecl_stmt hst₁ hpe ht₁ hsk₁ hsy with ⟨hrec, ci, hci, hcv, hks, hth⟩ |
    ⟨rfl, hq, htag0⟩
  · have hfind := find?_of_nodup (ownEnv_nodup hw hrun) (own_mem_ownEnv (sp := sp) (fs := fs)
      (M := M) hpo hci)
    rw [show ci.name = cv.name by rw [ConstantInfo.name, hcv]] at hfind
    exact ⟨ci, hfind, hcv, hks, fun h => hth (hthm h),
      own_stmt_fresh hrun hpd (stmtRecord_fill _ hrec)⟩
  · obtain ⟨hq', hrun'⟩ := hrun
    have hhit := declsRun_quot_hit hrun' cv hpd hq
    obtain ⟨hat, hty⟩ := quotAt_sound hhit
    have hci : ConstantInfo.axiomInfo cv ∈ declConstants (.axiomDecl cv) := by
      simp [declConstants, hq, hat]
    have hfind := find?_of_nodup (ownEnv_nodup hw ⟨hq', hrun'⟩) (own_mem_ownEnv (sp := sp)
      (fs := fs) (M := M) hpo hci)
    refine ⟨.axiomInfo cv, hfind, rfl, rfl, fun h => absurd (hthm h) (by omega), ?_⟩
    rw [hty, readNames_instantiateLevelParams, hq]
    decide

end ConLeche.Driver
