module

public import ConLeche.Verify.Driver.ReachFrom
public import ConLeche.Verify.Driver.Worker
import ConLeche.Verify.Frontend.Olean.Present
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Lazy
public import ConLeche.Verify.Frontend.Olean.Emit
import ConLeche.Verify.Frontend.Olean.Group

/-!
# A context record presents its source's own record

Task #448 (#467's stage 2, "provenance").  Where the reach read a context record of a
worker at `M` (`RecordFrom`, `ConLeche/Verify/Driver/ReachFrom.lean`) from a module `h`, and the
worker at `h` accepted on the same snapshot (the trust assumption for several runs), the record
is a presentation (`Presents`) of one of `h`'s own records as `h`'s worker emitted them.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-! ## A module's files, read at every level -/

/-- **A part's name table, from a home's files**: determined, the table of the view the part
reads. -/
theorem readPartNames_of_all {sp : SearchPath} {m : Name} {fs : FS} {f : ModFiles}
    {level : OLeanLevel} {t : NamePositions}
    (hf : (readFiles sp m .private : ModelIO _) fs (.ok (.ok f)))
    (h : (readPartNames sp (m, level) : ModelIO _) fs (.ok (.ok t))) :
    readNamePositions (f.upTo level) level = some t := by
  obtain ⟨loc, -, -, hfm, -⟩ := readFiles_ok hf
  have hall := readFiles_of_all level hf
  simp only [readFiles] at hall
  rw [ModelIO.bind_det hfm] at hall
  simp only [readPartNames, ModelIO.bind_ok] at h
  obtain ⟨y, hy, h⟩ := h
  rw [hfm] at hy
  simp only [ModelIO.answer_ok, Option.some.injEq] at hy
  subst hy
  simp only [readPartNamesAt, ModelIO.bind_ok] at h
  obtain ⟨z, hz, h⟩ := h
  simp only at hall
  rw [hall] at hz
  simp only [ModelIO.answer_ok, Option.some.injEq] at hz
  subst hz
  simp only at h
  cases hr : readNamePositions (f.upTo level) level with
  | none => simp [hr] at h
  | some ps =>
    simp only [hr, ModelIO.pure_iff, Except.ok.injEq] at h
    rw [h]

/-- **A part's files, from a home's**: determined. -/
theorem partFiles_of_all {sp : SearchPath} {m : Name} {fs : FS} {f f' : ModFiles}
    {level : OLeanLevel}
    (hf : (readFiles sp m .private : ModelIO _) fs (.ok (.ok f)))
    (h : (readFiles sp m level : ModelIO _) fs (.ok (.ok f'))) : f' = f.upTo level := by
  have hall := readFiles_of_all level hf
  rw [hall] at h
  exact (by simpa using h : f.upTo level = f').symm

/-- **The name positions of a part**: each at a constant of the part's skeleton, its name, kind
tag and filter the skeleton's; the names distinct. -/
theorem namePositionsAt_mem {r : Region} {root : UInt64} {t : NamePositions}
    (h : namePositionsAt r root = some t) :
    ∃ sk, moduleSkel r root = some sk ∧ (t.consts.toList.map (·.name)).Nodup ∧
      ∀ q ∈ t.consts, q.loc ∈ sk.consts ∧ ∃ s, constSkel r q.loc = some s ∧
        nameP r s.name = some q.name ∧ q.tag = s.kind.tag ∧ q.skipped = s.kind.skipped := by
  simp only [namePositionsAt] at h
  obtain ⟨sk, hsk, h⟩ := bind_some_left h
  obtain ⟨imps, -, h⟩ := bind_some_left h
  obtain ⟨cs, hcs, h⟩ := bind_some_left h
  split at h
  rotate_left
  · cases h
  rename_i hd
  simp only [pure, Option.some.injEq] at h
  subst h
  refine ⟨sk, hsk, ?_, fun q hq => ?_⟩
  · have := (distinctGo_iff _ _).1 (by simpa using hd)
    simpa using this.1
  · have hq' : q ∈ cs := by simpa using hq
    obtain ⟨l, hl, hql⟩ := mapM_mem_inv hcs hq'
    simp only [namePosition] at hql
    obtain ⟨s, hs, hql⟩ := bind_some_left hql
    obtain ⟨n, hn, hql⟩ := bind_some_left hql
    simp only [pure, Option.some.injEq] at hql
    subst hql
    exact ⟨hl, s, hs, hn, rfl, rfl⟩

/-! ## The home's own records -/

/-- **A constant of the merge, no part of a block and not filtered out, is emitted**: among the
roots, its record (`entryDecl`) is among the declarations. -/
theorem declsOf_entry {mg : Merged} {rs : Array Name} {ds : Array Declaration} {n : Name}
    {c : CEntry} (hN : ∀ (n : Name) (c : CEntry), mg.map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ mg.order ↔ mg.map.contains n = true)
    (hd : declsOf (emitAll mg rs) = .ok ds) (hb : blocksOk mg = .ok ())
    (hrs : n ∈ rs) (hc : mg.map[n]? = some c) (hsk : c.skipped = false) (ht : c.kind.tag < 5) :
    ∃ p, entryDecl c = some p ∧ p ∈ ds := by
  obtain ⟨h1, h2⟩ := emitAll_spec hN rs
  obtain ⟨r, hr, hdc⟩ := emitAll_covers (blocksOk_good hb hO) hN hO rs (h2 n hrs c hc hsk) hc hsk
  have hR := rec_of_declares hc (h1 r hr) hdc
  obtain ⟨d, hd1, hd2⟩ := (declsOf_spec hd).1 r hr
  have hsk' : c.kind.skipped = false := hsk
  refine ⟨d, ?_, hd2⟩
  cases r with
  | ind ts cs rs' =>
    simp only at hR
    omega
  | ax cv u =>
    obtain ⟨h3, h4⟩ := hR
    rw [h4] at hsk'
    simp only [CKindF.skipped] at hsk'
    subst hsk'
    simp only [declOfF, cvOfF_of h3, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
    subst hd1
    simp [entryDecl, h4]
  | defn cv i h s =>
    obtain ⟨h3, v, h4, h5⟩ := hR
    rw [h5] at hsk'
    have hs : s = "safe" := by simpa [CKindF.skipped] using hsk'
    subst hs
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Sum.inl.injEq] at hd1
    subst hd1
    simp only [entryDecl, h5]
    cases h <;> rfl
  | thm cv i =>
    obtain ⟨h3, v, all, h4, h5⟩ := hR
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Sum.inl.injEq] at hd1
    subst hd1
    simp [entryDecl, h5]
  | opaq cv i u =>
    obtain ⟨h3, v, h4, h5⟩ := hR
    rw [h5] at hsk'
    simp only [CKindF.skipped] at hsk'
    subst hsk'
    have hex : (emitAll mg rs).ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
    subst hd1
    simp [entryDecl, h5]
  | quot cv q =>
    obtain ⟨h3, h4⟩ := hR
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd1
    split at hd1
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd1
         subst hd1
         simp [entryDecl, h4])
      | (cases hd1; done)

theorem lazyEntry_kind {nm : UInt64 → Option Name} {ex : UInt64 → Option Expr} {r : Region}
    {i : Nat} {s : CEntryF UInt64 UInt64} {E : CEntryF Name Expr}
    (h : lazyEntry nm ex r i s = some E) :
    E.kind.skipped = s.kind.skipped ∧ E.kind.tag = s.kind.tag := by
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all =>
    simp only [lazyEntry] at h
    split at h
    rotate_left
    · cases h
    obtain ⟨_, -, h⟩ := bind_some_left h
    obtain ⟨_, -, h⟩ := bind_some_left h
    obtain ⟨_, -, h⟩ := bind_some_left h
    obtain ⟨_, -, h⟩ := bind_some_left h
    obtain ⟨_, -, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | _ =>
    simp only [lazyEntry] at h
    obtain ⟨-, -, -, h1, h2⟩ := CEntryF.mapM_parts h
    exact ⟨h2.symm, h1.symm⟩

theorem entryDecl_congr {a b : CEntry} (h : a.toCEntryF = b.toCEntryF) : entryDecl a = entryDecl b := by
  obtain ⟨a, ua⟩ := a
  obtain ⟨b, ub⟩ := b
  simp only at h
  subst h
  rfl

/-- The home's own constants as the worker merges them (`ownRecords`). -/
@[expose] def homeMerged (w : WorkerRead) : Merged :=
  mergedOfList (w.home.constants.toList.filter (!·.skipped))

/-- **The home's files and its own records**: the home's private view (its region, skeleton,
the check of its views), the merge of its own constants and their emission, and for every
skeleton of its private part not filtered out, the constant the load read there, which the
merge holds under its name. -/
theorem home_records {sp : SearchPath} {fs : FS} {h : Name} {jobs : Nat} {w : WorkerRead}
    (hw : WorkerFacts sp fs h jobs w) :
    ∃ f r a sk skels, (readFiles sp h .private : ModelIO _) fs (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) ∧ moduleSkel r a = some sk ∧
      sk.consts.mapM (constSkel r) = some skels ∧ constNamesOk r a = true ∧
      checkViews h f w.home = .ok w.expo ∧
      (∀ (n : Name) (c : CEntry), (homeMerged w).map[n]? = some c → c.name = n) ∧
      (∀ n, n ∈ (homeMerged w).order ↔ (homeMerged w).map.contains n = true) ∧
      blocksOk (homeMerged w) = .ok () ∧
      declsOf (emitAll (homeMerged w) (homeMerged w).order) = .ok w.emitted ∧
      ∀ loc s, loc ∈ sk.consts → constSkel r loc = some s → s.kind.skipped = false →
        ∃ E e₁, lazyEntry (nameP r) (exprP r) r 0 s = some E ∧
          (homeMerged w).map[E.name]? = some e₁ ∧ e₁.toCEntryF = E := by
  have hh := hw.home
  simp only [readHome, OleanReads.ofPath, ModelIO.bind_ok] at hh
  obtain ⟨x, hx, hh⟩ := hh
  rcases x with e | f
  · simp at hh
  simp only at hh
  cases hl : loadView 0 h f with
  | error e => simp [hl] at hh
  | ok l =>
  simp only [hl] at hh
  cases hc : checkViews h f l with
  | error e => simp [hc] at hh
  | ok expo =>
  simp only [hc, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  have hload : loadAt 0 h f = some w.home := by
    simp only [loadView] at hl
    split at hl
    · cases hl; assumption
    · cases hl
  obtain ⟨r, a, sk, skels, hreg, hcn, hsk, hskels, -, -, hlazy⟩ := loadAt_spec hload
  obtain ⟨hO, hin, hall⟩ := mergedOfList_spec (w.home.constants.toList.filter (!·.skipped))
  have hN := mergedOfList_names (w.home.constants.toList.filter (!·.skipped))
  have hown := hw.emitted
  cases hb : blocksOk (mergedOfList (w.home.constants.toList.filter (!·.skipped))) with
  | error e => simp [ownRecords, hb] at hown
  | ok u =>
  simp only [ownRecords, hb] at hown
  refine ⟨f, r, a, sk, skels, hx, hreg, hsk, hskels, hcn, hc, hN, hO, hb, hown,
    fun loc s hloc hs hskp => ?_⟩
  obtain ⟨s', hs'mem, hs'⟩ := mapM_mem hskels hloc
  rw [hs] at hs'
  cases hs'
  obtain ⟨e, he, hent⟩ := hlazy.of_skel _ hs'mem
  have hes : e.skipped = false := by
    have := (lazyEntry_kind hent).1
    simpa [CEntry.skipped, this] using hskp
  have hecs : e ∈ w.home.constants.toList.filter (!·.skipped) :=
    List.mem_filter.2 ⟨by simpa using he, by simp [hes]⟩
  have hcont := hall e hecs
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hcont
  obtain ⟨e₁, he₁⟩ := Option.isSome_iff_exists.1 hcont
  have hname₁ := hN _ _ he₁
  have he₁c : e₁ ∈ w.home.constants.toList := (List.mem_filter.1 (hin _ _ he₁)).1
  obtain ⟨s₁, hs₁, hent₁⟩ := hlazy.to_skel e₁ he₁c
  have hss : s₁ = s := skels_name_inj hcn hsk hskels hs₁ hs'mem
    (n := e.name) (by rw [lazyEntry_name hent₁, hname₁]) (lazyEntry_name hent)
  subst hss
  rw [hent] at hent₁
  exact ⟨e.toCEntryF, e₁, hent, he₁, (Option.some.inj hent₁).symm⟩

/-- **A constant of the home's merge, no part of a block, has its record among the emitted
ones.** -/
theorem home_entry {w : WorkerRead}
    (hN : ∀ (n : Name) (c : CEntry), (homeMerged w).map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ (homeMerged w).order ↔ (homeMerged w).map.contains n = true)
    (hb : blocksOk (homeMerged w) = .ok ())
    (hem : declsOf (emitAll (homeMerged w) (homeMerged w).order) = .ok w.emitted)
    {n : Name} {c : CEntry} (hc : (homeMerged w).map[n]? = some c) (hsk : c.skipped = false)
    (ht : c.kind.tag < 5) : ∃ p ∈ w.emitted, entryDecl c = some p := by
  obtain ⟨p, hp, hpm⟩ := declsOf_entry hN hO hem hb ((hO _).2 (by
    rw [Std.HashMap.contains_eq_isSome_getElem?, hc]; rfl)) hc hsk ht
  exact ⟨p, hpm, hp⟩

/-- **No constant of the home's merge is a recursor of no block.** -/
theorem home_recur {w : WorkerRead}
    (hO : ∀ n, n ∈ (homeMerged w).order ↔ (homeMerged w).map.contains n = true)
    (hb : blocksOk (homeMerged w) = .ok ())
    {n : Name} {c : CEntry} (hc : (homeMerged w).map[n]? = some c) :
    ∀ np ni nmo nmi rules k iu, c.kind ≠ .recur [] np ni nmo nmi rules k iu := by
  intro np ni nmo nmi rules k iu hk
  have hn : n ∈ (homeMerged w).order.toList := Array.mem_toList_iff.2 ((hO n).2 (by
    rw [Std.HashMap.contains_eq_isSome_getElem?, hc]; rfl))
  have := forM_ok hb n hn
  simp [blockStep, hc, hk] at this

theorem lazyEntry_stmt {nm : UInt64 → Option Name} {ex : UInt64 → Option Expr} {r : Region}
    {i : Nat} {s : CEntryF UInt64 UInt64} {E : CEntryF Name Expr}
    (h : lazyEntry nm ex r i s = some E) :
    nm s.name = some E.name ∧ s.levelParams.mapM nm = some E.levelParams ∧
      ex s.type = some E.type := by
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all =>
    simp only [lazyEntry] at h
    split at h
    rotate_left
    · cases h
    obtain ⟨_, -, h⟩ := bind_some_left h
    obtain ⟨n, hn, h⟩ := bind_some_left h
    obtain ⟨l, hl, h⟩ := bind_some_left h
    obtain ⟨t, ht, h⟩ := bind_some_left h
    obtain ⟨_, -, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact ⟨hn, hl, ht⟩
  | _ =>
    simp only [lazyEntry] at h
    obtain ⟨h1, h2, h3, -, -⟩ := CEntryF.mapM_parts h
    exact ⟨h1, h2, h3⟩

theorem reduce_ne_quot {n : Name} (h : reduceOpNames.contains n = true) :
    n ≠ quotSoundName ∧ n ≠ sorryAxName := by
  simp only [reduceOpNames, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

/-- **A statement presents the home's own record at its skeleton**: a statement read off a
skeleton of the home's private part that is an axiom, a definition, a theorem or an opaque
constant, not filtered out, at a compiler-trust name only an axiom or an opaque constant. -/
theorem stmt_presents {w : WorkerRead} {r : Region} {sk : ModSkel}
    (hN : ∀ (n : Name) (c : CEntry), (homeMerged w).map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ (homeMerged w).order ↔ (homeMerged w).map.contains n = true)
    (hb : blocksOk (homeMerged w) = .ok ())
    (hem : declsOf (emitAll (homeMerged w) (homeMerged w).order) = .ok w.emitted)
    (hown : ∀ loc s, loc ∈ sk.consts → constSkel r loc = some s → s.kind.skipped = false →
        ∃ E e₁, lazyEntry (nameP r) (exprP r) r 0 s = some E ∧
          (homeMerged w).map[E.name]? = some e₁ ∧ e₁.toCEntryF = E)
    {loc : Nat} {s : CEntryF UInt64 UInt64} {cv : ConstantVal}
    (hloc : loc ∈ sk.consts) (hs : constSkel r loc = some s) (hskp : s.kind.skipped = false)
    (hn : nameP r s.name = some cv.name) (hl : s.levelParams.mapM (nameP r) = some cv.levelParams)
    (hty : exprP r s.type = some cv.type) (htag : s.kind.tag < 4)
    (hred : reduceOpNames.contains cv.name = true → s.kind.tag = 0 ∨ s.kind.tag = 3) :
    ∃ p ∈ w.emitted, Presents (.axiomDecl cv) p := by
  obtain ⟨E, e₁, hE, he₁, hee⟩ := hown loc s hloc hs hskp
  obtain ⟨hn', hl', ht'⟩ := lazyEntry_stmt hE
  rw [hn] at hn'; rw [hl] at hl'; rw [hty] at ht'
  simp only [Option.some.injEq] at hn' hl' ht'
  obtain ⟨hsk', htag'⟩ := lazyEntry_kind hE
  have hst : (⟨e₁.name, e₁.levelParams, e₁.type⟩ : ConstantVal) = cv := by
    obtain ⟨n, l, t⟩ := cv
    simp only at hn' hl' ht'
    rw [show e₁.name = e₁.toCEntryF.name from rfl, show e₁.levelParams = e₁.toCEntryF.levelParams
      from rfl, show e₁.type = e₁.toCEntryF.type from rfl, hee, hn', hl', ht']
  have hk : e₁.kind = E.kind := by rw [show e₁.kind = e₁.toCEntryF.kind from rfl, hee]
  have hsk₁ : e₁.skipped = false := by simp only [CEntry.skipped, hk, hsk', hskp]
  have ht₁ : e₁.kind.tag < 5 := by rw [hk, htag']; omega
  obtain ⟨p, hp, hpe⟩ := home_entry hN hO hb hem he₁ hsk₁ ht₁
  refine ⟨p, hp, ?_⟩
  have hred' : reduceOpNames.contains cv.name = true → e₁.kind.tag = 0 ∨ e₁.kind.tag = 3 := by
    rw [hk, htag']; exact hred
  revert hpe hred' ht₁ hsk₁
  rcases e₁ with ⟨⟨n₁, l₁, t₁, k₁⟩, u₁⟩
  simp only at hst hk
  subst hst
  intro hsk₁ ht₁ hpe hred'
  cases k₁ with
  | ax u =>
    simp only [entryDecl, Option.some.injEq] at hpe
    subst hpe
    exact .inl ⟨List.Perm.refl _, rfl⟩
  | defn v hh sf =>
    have hsf : sf = "safe" := by simpa [CEntry.skipped, CKindF.skipped] using hsk₁
    subst hsf
    simp only [entryDecl, Option.some.injEq] at hpe
    subst hpe
    refine .inr ⟨rfl, ?_⟩
    simp only [declConstants, List.map_cons, List.map_nil, List.mem_singleton]
    rintro n rfl hr
    have := hred' (List.contains_iff_mem.2 hr)
    simp [CKindF.tag] at this
  | thm v all =>
    simp only [entryDecl, Option.some.injEq] at hpe
    subst hpe
    refine .inr ⟨rfl, ?_⟩
    simp only [declConstants, List.map_cons, List.map_nil, List.mem_singleton]
    rintro n rfl hr
    have := hred' (List.contains_iff_mem.2 hr)
    simp [CKindF.tag] at this
  | opaq v u =>
    simp only [entryDecl, Option.some.injEq] at hpe
    subst hpe
    by_cases hr : reduceOpNames.contains n₁ = true
    · obtain ⟨h1, h2⟩ := reduce_ne_quot hr
      exact .inl ⟨by simp [declConstants, h1, h2], rfl⟩
    · refine .inr ⟨rfl, ?_⟩
      simp only [declConstants, List.map_cons, List.map_nil, List.mem_singleton]
      rintro n rfl hr'
      exact hr (List.contains_iff_mem.2 hr')
  | _ =>
    rw [← hk] at htag'
    have h4 := htag'.symm ▸ htag
    simp [CKindF.tag] at h4 ht₁

/-- **A constant's record, through the builder, is `entryDecl`'s.** -/
theorem declOfF_recOf {em : Emit} {c : CEntry} {r : DeclRec} {d : Declaration}
    (hR : RecOf em c r) (hd : declOfF em.nm em.lv em.ex r = .ok (.inl d)) :
    entryDecl c = some d := by
  cases r with
  | ind ts cs rs' => exact hR.elim
  | ax cv u =>
    obtain ⟨h3, h4⟩ := hR
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd
    cases u with
    | true => simp [pure, Except.pure] at hd
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
        Sum.inl.injEq] at hd
      subst hd
      simp [entryDecl, h4]
  | defn cv i h s =>
    obtain ⟨h3, v, h4, h5⟩ := hR
    have hex : em.ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd
    by_cases hsafe : s = "safe"
    · subst hsafe
      simp only [hex, pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd
      subst hd
      simp only [entryDecl, h5]
      cases h <;> rfl
    · split at hd
      · exact absurd rfl hsafe
      · simp [pure, Except.pure] at hd
  | thm cv i =>
    obtain ⟨h3, v, all, h4, h5⟩ := hR
    have hex : em.ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Sum.inl.injEq] at hd
    subst hd
    simp [entryDecl, h5]
  | opaq cv i u =>
    obtain ⟨h3, v, h4, h5⟩ := hR
    have hex : em.ex i = .ok v := by simp [Emit.ex, h4, pure, Except.pure]
    simp only [declOfF, cvOfF_of h3, hex, bind, Except.bind] at hd
    cases u with
    | true => simp [pure, Except.pure] at hd
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
        Sum.inl.injEq] at hd
      subst hd
      simp [entryDecl, h5]
  | quot cv q =>
    obtain ⟨h3, h4⟩ := hR
    simp only [declOfF, cvOfF_of h3, bind, Except.bind] at hd
    split at hd
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at hd
         subst hd
         simp [entryDecl, h4])
      | (cases hd; done)

/-- **One constant's record** (`recordOfEntry`) is `entryDecl`'s. -/
theorem recordOfEntry_eq {e : CEntryF Name Expr} {d : Declaration} (h : recordOfEntry e = .ok d) :
    entryDecl (CEntry.ofF e) = some d := by
  unfold recordOfEntry at h
  split at h
  · cases h
  rename_i ds hds
  split at h
  · rename_i d' hl
    cases h
    have hd : d ∈ ds := by
      rw [← Array.mem_toList_iff, hl]; exact List.mem_singleton_self _
    obtain ⟨r, hr, hdr⟩ := (declsOf_spec hds).2 d hd
    rcases (Emit.one_spec {} (CEntry.ofF e)).2.2.1 r hr with h0 | hR
    · simp at h0
    · exact declOfF_recOf hR hdr
  · cases h

/-- A constant that is no theorem: its lazy read is its whole read. -/
theorem lazyEntry_entryAt {r : Region} {i loc : Nat} {s : CEntryF UInt64 UInt64}
    {E e : CEntryF Name Expr} (hs : constSkel r loc = some s)
    (hE : lazyEntry (nameP r) (exprP r) r i s = some E) (he : entryAt r loc = some e)
    (ht : e.kind.tag ≠ 2) : E = e := by
  rw [entryAt_eq] at he
  obtain ⟨s', hs', hm⟩ := constSpec_parts he
  rw [hs] at hs'
  cases hs'
  rcases s with ⟨name, lps, type, kind⟩
  cases kind with
  | thm p all =>
    have := (CEntryF.mapM_parts hm).2.2.2.1
    simp [CKindF.tag] at this
    exact absurd this.symm ht
  | _ =>
    simp only [lazyEntry] at hE
    rw [hm] at hE
    exact (Option.some.inj hE).symm

theorem Presents.refl (d : Declaration) : Presents d d := .inl ⟨List.Perm.refl _, rfl⟩

/-- **A whole constant presents the home's own record at its skeleton**: the constant the
load read there, no part of a block, through the builder. -/
theorem whole_presents {w : WorkerRead} {r : Region} {sk : ModSkel}
    (hN : ∀ (n : Name) (c : CEntry), (homeMerged w).map[n]? = some c → c.name = n)
    (hO : ∀ n, n ∈ (homeMerged w).order ↔ (homeMerged w).map.contains n = true)
    (hb : blocksOk (homeMerged w) = .ok ())
    (hem : declsOf (emitAll (homeMerged w) (homeMerged w).order) = .ok w.emitted)
    (hown : ∀ loc s, loc ∈ sk.consts → constSkel r loc = some s → s.kind.skipped = false →
        ∃ E e₁, lazyEntry (nameP r) (exprP r) r 0 s = some E ∧
          (homeMerged w).map[E.name]? = some e₁ ∧ e₁.toCEntryF = E)
    {loc : Nat} {s : CEntryF UInt64 UInt64} {e : CEntryF Name Expr} {d : Declaration}
    (hloc : loc ∈ sk.consts) (hs : constSkel r loc = some s) (hskp : s.kind.skipped = false)
    (hE : ∀ E, lazyEntry (nameP r) (exprP r) r 0 s = some E → E = e) (ht : e.kind.tag < 5)
    (hd : recordOfEntry e = .ok d) :
    ∃ p ∈ w.emitted, Presents d p := by
  obtain ⟨E, e₁, hE', he₁, hee⟩ := hown loc s hloc hs hskp
  obtain rfl := hE E hE'
  have hk : e₁.kind = E.kind := by rw [show e₁.kind = e₁.toCEntryF.kind from rfl, hee]
  have hsk₁ : e₁.skipped = false := by
    simp only [CEntry.skipped, hk, (lazyEntry_kind hE').1, hskp]
  obtain ⟨p, hp, hpe⟩ := home_entry hN hO hb hem he₁ hsk₁ (by rw [hk]; exact ht)
  refine ⟨p, hp, ?_⟩
  have h1 := recordOfEntry_eq hd
  rw [← entryDecl_congr (a := e₁) (b := CEntry.ofF E) (by simp [CEntry.ofF, hee]), hpe] at h1
  cases h1
  exact Presents.refl _

/-! ## The home's check of its exported part -/

/-- A loop in `Except` whose every step yields, and says `P` of its element where it does,
says `P` of every element where it ends in a value. -/
theorem forIn_ok_all {ε α σ : Type} (P : α → Prop) {f : α → σ → Except ε (ForInStep σ)}
    (hf : ∀ x s r, f x s = .ok r → P x ∧ ∃ s', r = .yield s') :
    ∀ (xs : List α) (init : σ) (res : σ), forIn xs init f = .ok res → ∀ x ∈ xs, P x
  | [], _, _, _ => by simp
  | x :: xs, init, res, h => by
    simp only [List.forIn_cons] at h
    cases hx : f x init with
    | error e => simp [hx, bind, Except.bind] at h
    | ok r =>
      obtain ⟨hp, s', rfl⟩ := hf x init _ hx
      simp only [hx, bind, Except.bind] at h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hp
      · exact forIn_ok_all P hf xs s' res h y hy

/-- The private constant a hidden exported one stands for, by kind. -/
@[expose] def hiddenKind (ke kp : CKindF UInt64 UInt64) : Bool :=
  match ke, kp with
  | .ax u, .defn _ _ s => u == (s != "safe")
  | .ax u, .thm .. => !u
  | .ax u, .opaq _ u' => u == u'
  | _, _ => false

/-- **What `expoOfParts` checks of one exported constant** at `c`: the private part points at
it, or the private constant of its name (the `i`-th, at `loc`) is it with its value hidden
(by its skeleton's pointers) or refined by it (decoded, `expoOf`). -/
@[expose] def ExpoAt (r : Region) (skP : ModSkel) (cs : Array (CEntryF Name Expr)) (c : Nat) :
    Prop :=
  c ∈ skP.consts ∨
  ∃ (se sp : CEntryF UInt64 UInt64) (en : Name) (i loc : Nat),
    constSkel r c = some se ∧ nameP r se.name = some en ∧ (∃ hi : i < cs.size, cs[i].name = en) ∧
    skP.consts[i]? = some loc ∧ constSkel r loc = some sp ∧
    ((hiddenKind se.kind sp.kind = true ∧ se.type = sp.type ∧ se.levelParams = sp.levelParams) ∨
     ∃ e pc x, entryAt r c = some e ∧ expoOf pc e = some x ∧
       ((∃ v all, cs[i]!.kind = .thm v all) → entryAt r loc = some pc) ∧
       ((∀ v all, cs[i]!.kind ≠ .thm v all) → pc = cs[i]!))

theorem privIdx_spec (cs : Array (CEntryF Name Expr)) {en : Name} {i : Nat}
    (h : (cs.size.fold (fun i _ (acc : Std.HashMap Name Nat) => acc.insert cs[i].name i) ∅)[en]? =
      some i) : ∃ hi : i < cs.size, cs[i].name = en := by
  suffices H : ∀ n (hn : n ≤ cs.size) (en : Name) (i : Nat),
      (n.fold (fun j hj (acc : Std.HashMap Name Nat) => acc.insert cs[j].name j) ∅)[en]? = some i →
        ∃ hi : i < cs.size, cs[i].name = en from H _ (Nat.le_refl _) en i h
  intro n
  induction n with
  | zero => intro _ en i h; simp at h
  | succ n ih =>
    intro hn en i h
    rw [Nat.fold_succ] at h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i he
      cases h
      exact ⟨by omega, eq_of_beq he⟩
    · exact ih (by omega) en i h

theorem privLoc_spec (l : List Nat) {c i : Nat}
    (h : (l.foldl (fun (x : Std.HashMap Nat Nat × Nat) c => (x.1.insert c x.2, x.2 + 1))
      (∅, 0)).1[c]? = some i) : c ∈ l := by
  suffices H : ∀ (l : List Nat) (m : Std.HashMap Nat Nat) (k : Nat),
      (l.foldl (fun (x : Std.HashMap Nat Nat × Nat) c => (x.1.insert c x.2, x.2 + 1)) (m, k)).1[c]? =
        some i → m[c]?.isSome ∨ c ∈ l from by
    rcases H l ∅ 0 h with h' | h'
    · simp at h'
    · exact h'
  intro l
  induction l with
  | nil =>
    intro m k h
    simp only [List.foldl_nil] at h
    exact .inl (by simp [h])
  | cons x l ih =>
    intro m k h
    simp only [List.foldl_cons] at h
    rcases ih _ _ h with h' | h'
    · rw [Std.HashMap.getElem?_insert] at h'
      split at h'
      · rename_i he; exact .inr (eq_of_beq he ▸ List.mem_cons_self)
      · exact .inl h'
    · exact .inr (List.mem_cons_of_mem _ h')

/-- **The home's check of its exported part**, constant by constant. -/
theorem expoOfParts_ok {r : Region} {pa ea : UInt64} {cs : Array (CEntryF Name Expr)}
    {expo : Array Expo} (h : expoOfParts r pa ea cs = .ok expo) :
    ∃ skP skE, moduleSkel r pa = some skP ∧ moduleSkel r ea = some skE ∧
      ∀ c ∈ skE.consts, ExpoAt r skP cs c := by
  unfold expoOfParts at h
  cases hP : moduleSkel r pa with
  | none => simp [hP] at h
  | some skP =>
  cases hE : moduleSkel r ea with
  | none => simp [hP, hE] at h
  | some skE =>
  simp only [hP, hE] at h
  refine ⟨skP, skE, rfl, rfl, ?_⟩
  generalize hl : (forIn skE.consts (Array.map (fun _ => Expo.absent) cs) _ :
    Except String (Array Expo)) = x at h
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok res =>
  refine forIn_ok_all (ExpoAt r skP cs) ?_ skE.consts _ res hl
  intro c st rr hrr
  split at hrr
  · rename_i i hi
    simp only [pure, Except.pure, Except.ok.injEq] at hrr
    subst hrr
    exact ⟨.inl (privLoc_spec _ hi), _, rfl⟩
  · split at hrr
    rotate_left
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrr
    rename_i se hse
    split at hrr
    rotate_left
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrr
    rename_i en hen
    split at hrr
    rotate_left
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrr
    rename_i i hi
    split at hrr
    rotate_left
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrr
    rename_i sp hsp
    obtain ⟨loc, hloc, hsp'⟩ := Option.bind_eq_some_iff.1 hsp
    have hloc' : skP.consts[i]? = some loc := by simpa using hloc
    have base : ((hiddenKind se.kind sp.kind = true ∧ se.type = sp.type ∧
        se.levelParams = sp.levelParams) ∨
        ∃ e pc x, entryAt r c = some e ∧ expoOf pc e = some x ∧
          ((∃ v all, cs[i]!.kind = .thm v all) → entryAt r loc = some pc) ∧
          ((∀ v all, cs[i]!.kind ≠ .thm v all) → pc = cs[i]!)) → ExpoAt r skP cs c :=
      fun hX => .inr ⟨se, sp, en, i, loc, hse, hen, privIdx_spec cs hi, hloc', hsp', hX⟩
    split at hrr <;> split at hrr
    all_goals first
      | (rename_i hk1 hk2 hcond
         have hrr' : ForInStep.yield (st.set! i Expo.hidden) = rr := Except.ok.inj hrr
         subst hrr'
         simp only [Bool.and_eq_true, beq_iff_eq] at hcond
         refine ⟨base (.inl ⟨?_, hcond.2.1, hcond.2.2⟩), _, rfl⟩
         rw [hk1, hk2]
         simp [hiddenKind, hcond.1])
      | (rename_i hcond
         simp at hcond
         done)
      | (split at hrr
         rotate_left
         · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrr
         rename_i e he
         split at hrr
         · rename_i v all hk
           split at hrr
           rotate_left
           · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hrr
           rename_i pc hpc
           simp only [bind, Except.bind, pure, Except.pure] at hrr
           split at hrr
           · rename_i x hx
             simp only [Except.ok.injEq] at hrr
             subst hrr
             refine ⟨base (.inr ⟨e, pc, x, he, hx, fun _ => ?_, fun h' => absurd hk (h' v all)⟩), _, rfl⟩
             obtain ⟨l', hl', hpc'⟩ := Option.bind_eq_some_iff.1 hpc
             have : l' = loc := by
               have h1 : skP.consts[i]? = some l' := by simpa using hl'
               rw [hloc'] at h1; exact (Option.some.inj h1).symm
             subst this
             exact hpc'
           · simp [throw, throwThe, MonadExceptOf.throw] at hrr
         · rename_i hk
           simp only [bind, Except.bind, pure, Except.pure] at hrr
           split at hrr
           · rename_i x hx
             simp only [Except.ok.injEq] at hrr
             subst hrr
             exact ⟨base (.inr ⟨e, cs[i]!, x, he, hx, fun ⟨v, all, h'⟩ => absurd h' (hk v all),
               fun _ => rfl⟩), _, rfl⟩
           · simp [throw, throwThe, MonadExceptOf.throw] at hrr)

end ConLeche.Driver
