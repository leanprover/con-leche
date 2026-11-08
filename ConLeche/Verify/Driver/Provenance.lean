module

public import ConLeche.Verify.Driver.ReachFrom
public import ConLeche.Verify.Driver.Worker
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Lazy
public import ConLeche.Verify.Frontend.Olean.Emit
public import ConLeche.Verify.Frontend.Olean.Prefix
import ConLeche.Verify.Frontend.Olean.Group

/-!
# A context record presents its source's own record

Task #448 (#467's stage 2, "provenance").  Where the reach read a context record of a
worker at `M` (`RecordFrom`, `ConLeche/Verify/Driver/ReachFrom.lean`) from a module `h`, and the
worker at `h` accepted on the same snapshot (the trust assumption for several runs), the record
is a presentation (`Presents`) of one of `h`'s own records as `h`'s worker emitted them: here
for every record but an inductive group (`recordFrom_presents_nongroup`); the group and the
assembled statements are `ConLeche/Verify/Driver/Groups.lean`'s.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend ConLeche.Frontend.Olean ConLeche.Cached

/-! ## A module's files, read at every level -/

/-- **A part's name table, from a home's files**: determined, the table of the view the part
reads. -/
theorem readPartNames_of_all {sp : SearchPath} {m : Name} {fs : FS} {f : ModFiles}
    {level : OLeanLevel} {t : NamePositions}
    (hf : ModelIO.CanGive (readFiles sp m .private) fs (.ok f))
    (h : ModelIO.CanGive (readPartNames sp (m, level)) fs (.ok t)) :
    readNamePositions (f.upTo level) level = some t := by
  obtain ⟨_, _, hf⟩ := hf
  obtain ⟨hs₀, _, h⟩ := h
  have hall := readFiles_of_all level hf
  simp only [readPartNames, ModelIO.bind_ok] at h
  obtain ⟨y, hs₁, hy, h⟩ := h
  rcases y with e | loc
  · simp at h
  simp only [readPartNamesAt, ModelIO.bind_ok] at h
  obtain ⟨z, hs₂, hz, h⟩ := h
  have hz' : (readFiles sp m level : ModelIO _) fs hs₀ (.ok z) hs₂ := by
    simp only [readFiles, ModelIO.bind_ok]
    exact ⟨.ok loc, hs₁, hy, hz⟩
  obtain rfl := hall.ok hz'
  simp only at h
  cases hr : readNamePositions (f.upTo level) level with
  | none => simp [hr] at h
  | some ps =>
    simp only [hr, ModelIO.pure_iff, Except.ok.injEq] at h
    rw [h.1]

/-- **A part's files, from a home's**: determined. -/
theorem partFiles_of_all {sp : SearchPath} {m : Name} {fs : FS} {f f' : ModFiles}
    {level : OLeanLevel}
    (hf : ModelIO.CanGive (readFiles sp m .private) fs (.ok f))
    (h : ModelIO.CanGive (readFiles sp m level) fs (.ok f')) : f' = f.upTo level := by
  obtain ⟨_, _, hf⟩ := hf
  have := (readFiles_of_all level hf).eq h
  simpa using this

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

/-! ## The worker's name index is the snapshot's -/

theorem mapExcept_getElem {α β ε : Type} {f : α → ModelIO (Except ε β)} {fs : FS} :
    ∀ {xs : List α} {ys : List β} {hs hs' : HS}, (mapExcept f xs : ModelIO _) fs hs (.ok (.ok ys)) hs' →
      ys.length = xs.length ∧ ∀ (i : Nat) (y : β), ys[i]? = some y →
        ∃ x, xs[i]? = some x ∧ ModelIO.CanGive (f x) fs (.ok y)
  | [], ys, _, _, h => by
    simp only [mapExcept, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    cases h
    simp
  | x :: xs, ys, _, _, h => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨a, _, ha, h⟩ := h
    rcases a with e | b
    · simp at h
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨c, _, hc, h⟩ := h
      rcases c with e | bs
      · simp at h
      · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
        obtain ⟨h, -⟩ := h
        cases h
        obtain ⟨h1, h2⟩ := mapExcept_getElem hc
        refine ⟨by simp [h1], fun i y hy => ?_⟩
        cases i with
        | zero => simp at hy; subst hy; exact ⟨x, rfl, _, _, ha⟩
        | succ i => exact h2 i y (by simpa using hy)

theorem loadsIndex_spec (order : List Name) {m : Name} {i : Nat}
    (h : (order.foldl (fun (acc : Std.HashMap Name Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
      ({}, 0)).1[m]? = some i) : order[i]? = some m := by
  suffices H : ∀ (l : List Name) (acc : Std.HashMap Name Nat) (k : Nat),
      (∀ n j, acc[n]? = some j → order[j]? = some n) → (∀ j (hj : j < l.length), order[k + j]? = some l[j]) →
      ∀ n j, (l.foldl (fun (acc : Std.HashMap Name Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
        (acc, k)).1[n]? = some j → order[j]? = some n from
    H order ∅ 0 (fun n j h => by rw [Std.HashMap.getElem?_empty] at h; cases h)
      (fun j hj => by rw [Nat.zero_add]; exact List.getElem?_eq_getElem hj) m i h
  intro l
  induction l with
  | nil => intro acc k h1 _; exact h1
  | cons x l ih =>
    intro acc k h1 h2
    simp only [List.foldl_cons]
    refine ih _ (k + 1) (fun n j hn => ?_) (fun j hj => ?_)
    · rw [Std.HashMap.getElem?_insert] at hn
      split at hn
      · rename_i he
        cases hn
        have := h2 0 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero] at this
        rw [this, eq_of_beq he]
      · exact h1 n j hn
    · have := h2 (j + 1) (by simp; omega)
      rw [show k + 1 + j = k + (j + 1) by omega, this]
      simp

/-- **The worker's name index and load order are the snapshot's**: each loaded part's table is
its module's at its level, and the order names each module where the index says. -/
theorem workerReads_index {sp : SearchPath} {fs : FS} {m : Name} {jobs : Nat} {wr : WorkerReads}
    {hs hs' : HS} (h : (workerReads (.ofPath sp) m jobs : ModelIO _) fs hs (.ok (.ok wr)) hs') :
    (∀ i t, wr.index.parts[i]? = some t →
      PartNames sp fs ⟨wr.loads.nameAt i, ((wr.loads.flags[i]?).getD default).level⟩ t) ∧
    (∀ n i, wr.loads.index[n]? = some i → wr.loads.nameAt i = n) := by
  simp only [workerReads, ModelIO.bind_ok] at h
  obtain ⟨a, _, -, h⟩ := h
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
  generalize freshOk _ _ _ _ = z at h
  rcases z with e | u
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  -- the load order and its index
  have hidx : ∀ n i, ld.index[n]? = some i → ld.nameAt i = n := by
    intro n i hi
    simp only [headerFixpoint, OleanReads.ofPath, ModelIO.bind_ok] at hb
    obtain ⟨st, _, -, hb⟩ := hb
    rcases st with e | st
    · simp at hb
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hb
    obtain ⟨hb, -⟩ := hb
    subst hb
    simp only [Loads.nameAt]
    rw [← Array.foldl_toList] at hi
    rw [← Array.getElem?_toList, loadsIndex_spec st.order.toList hi]
    rfl
  refine ⟨fun i t ht => ?_, hidx⟩
  simp only [nameIndexOf] at ht
  have hc' : (mapExcept (readPartNames sp) ((ld.order.zip ld.flags).toList.map
      fun (n, fl) => (n, fl.level)) : ModelIO _) fs _ (.ok (.ok parts)) _ := hc
  obtain ⟨-, hget⟩ := mapExcept_getElem hc'
  obtain ⟨x, hx, hxr⟩ := hget i t (by simpa using ht)
  simp only [List.getElem?_map, Array.toList_zip] at hx
  obtain ⟨⟨n, fl⟩, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  rw [List.getElem?_zip_eq_some] at hz
  obtain ⟨h1, h2⟩ := hz
  have hn : ld.nameAt i = n := by
    simp only [Loads.nameAt]; rw [← Array.getElem?_toList, h1]; rfl
  have hf : ((ld.flags[i]?).getD default) = fl := by
    rw [← Array.getElem?_toList, h2]; rfl
  simp only
  rw [hn, hf]
  exact hxr
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
    ∃ f r a sk skels, ModelIO.CanGive (readFiles sp h .private) fs (.ok f) ∧
      f.viewRegion .private = some (r, a) ∧ moduleSkel r a = some sk ∧
      sk.consts.mapM (constSkel r) = some skels ∧ constNamesOk r a = true ∧
      checkViews h f w.home = .ok w.expo ∧ loadAt 0 h f = some w.home ∧
      (∀ (n : Name) (c : CEntry), (homeMerged w).map[n]? = some c → c.name = n) ∧
      (∀ n, n ∈ (homeMerged w).order ↔ (homeMerged w).map.contains n = true) ∧
      blocksOk (homeMerged w) = .ok () ∧
      declsOf (emitAll (homeMerged w) (homeMerged w).order) = .ok w.emitted ∧
      ∀ loc s, loc ∈ sk.consts → constSkel r loc = some s → s.kind.skipped = false →
        ∃ E e₁, lazyEntry (nameP r) (exprP r) r 0 s = some E ∧
          (homeMerged w).map[E.name]? = some e₁ ∧ e₁.toCEntryF = E := by
  obtain ⟨hs, _, hh⟩ := hw.home
  simp only [readHome, OleanReads.ofPath, ModelIO.bind_ok] at hh
  obtain ⟨x, hs₁, hx, hh⟩ := hh
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
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hh
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
  refine ⟨f, r, a, sk, skels, ⟨hs, hs₁, hx⟩, hreg, hsk, hskels, hcn, hc, hload, hN, hO, hb, hown,
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

/-- **The home's check of its views reached its exported part's.** -/
theorem checkViews_expo {m : Name} {f : ModFiles} {l : Loaded} {expo : Array Expo}
    (h : checkViews m f l = .ok expo)
    (hm : f.isModule = true) {sv p : Part} (hs : f.server = some sv) (hp : f.private = some p) :
    ∃ r, Region.ofParts #[f.exported, sv, p] = .ok r ∧
      expoOfParts r p.moduleDataAddr f.exported.moduleDataAddr (l.constants.map (·.toCEntryF)) =
        .ok expo := by
  unfold checkViews at h
  simp only [hs, hp, hm, ite_true] at h
  cases hr : Region.ofParts #[f.exported, sv, p] with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
  refine ⟨r, rfl, ?_⟩
  simp only [hr, bind, Except.bind] at h
  generalize (forIn [("server", sv.moduleDataAddr), ("private", p.moduleDataAddr)] PUnit.unit _ :
    Except CheckError PUnit) = x at h
  cases x with
  | error e => simp at h
  | ok u =>
  simp only at h
  split at h
  · generalize (forIn [("exported", f.exported.moduleDataAddr), ("server", sv.moduleDataAddr)]
      PUnit.unit _ : Except CheckError PUnit) = y at h
    cases y with
    | error e => simp at h
    | ok u =>
    simp only at h
    split at h
    · rename_i e1 a h1 h2
      simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [h1, h]
    · simp at h
    · simp at h
  · simp at h

theorem mapM_some_eq {α : Type} : ∀ l : List α, l.mapM some = some l
  | [] => rfl
  | x :: l => by simp [List.mapM_cons, mapM_some_eq l, bind, Option.bind, pure]

theorem listMapM_isSome {α β γ : Type} {f : α → Option β} {g : α → Option γ} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome → (g x).isSome) → (l.mapM f).isSome → (l.mapM g).isSome
  | [], _, _ => rfl
  | x :: l, hfg, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h ⊢
    cases hf : f x with
    | none => simp [hf] at h
    | some b =>
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hfg x List.mem_cons_self (by simp [hf]))
      rw [hc]
      simp only [hf] at h
      cases hl : List.mapM f l with
      | none => simp [hl] at h
      | some w =>
        obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1
          (listMapM_isSome (fun y hy => hfg y (List.mem_cons_of_mem _ hy)) (by simp [hl]))
        simp [hw', pure]

/-- **A kind's names, from a decoded one**: they read, to a kind of the same constructor, a
quotient constant's the same. -/
theorem kind_names {r : Region} {s : CEntryF UInt64 UInt64} {e : CEntryF Name Expr}
    (h : s.mapM (nameP r) (exprP r) = some e) :
    ∃ k', s.kind.mapM (nameP r) (fun _ => some ()) = some k' ∧ k'.tag = e.kind.tag ∧
      ∀ q, e.kind = .quot q → k' = .quot q := by
  simp only [CEntryF.mapM] at h
  obtain ⟨_, -, h⟩ := bind_some_left h
  obtain ⟨_, -, h⟩ := bind_some_left h
  obtain ⟨_, -, h⟩ := bind_some_left h
  obtain ⟨k, hk, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  simp only
  cases hs : s.kind with
  | ax u => rw [hs] at hk; cases hk; exact ⟨.ax u, rfl, rfl, fun q h => by cases h⟩
  | defn v hh sf =>
    rw [hs] at hk
    obtain ⟨_, -, hk⟩ := bind_some_left hk
    cases hk
    exact ⟨.defn () hh sf, rfl, rfl, fun q h => by cases h⟩
  | thm v all =>
    rw [hs] at hk
    obtain ⟨_, -, hk⟩ := bind_some_left hk
    obtain ⟨as, ha, hk⟩ := bind_some_left hk
    cases hk
    exact ⟨.thm () as, by simp [CKindF.mapM, ha, bind, Option.bind, pure], rfl,
      fun q h => by cases h⟩
  | opaq v u =>
    rw [hs] at hk
    obtain ⟨_, -, hk⟩ := bind_some_left hk
    cases hk
    exact ⟨.opaq () u, rfl, rfl, fun q h => by cases h⟩
  | quot q =>
    rw [hs] at hk; cases hk
    exact ⟨.quot q, rfl, rfl, fun q' h => by cases h; rfl⟩
  | induct np ni all cs nn ir iu irf =>
    rw [hs] at hk
    obtain ⟨as, ha, hk⟩ := bind_some_left hk
    obtain ⟨cs', hc, hk⟩ := bind_some_left hk
    cases hk
    exact ⟨.induct np ni as cs' nn ir iu irf,
      by simp [CKindF.mapM, ha, hc, bind, Option.bind, pure], rfl, fun q h => by cases h⟩
  | ctor ind cidx np nf iu =>
    rw [hs] at hk
    obtain ⟨i', hi, hk⟩ := bind_some_left hk
    cases hk
    exact ⟨.ctor i' cidx np nf iu, by simp [CKindF.mapM, hi, bind, Option.bind, pure], rfl,
      fun q h => by cases h⟩
  | recur all np ni nmo nmi rules kk iu =>
    rw [hs] at hk
    obtain ⟨as, ha, hk⟩ := bind_some_left hk
    obtain ⟨rs, hr, hk⟩ := bind_some_left hk
    cases hk
    have hsome : (rules.mapM fun (x : UInt64 × Nat × UInt64) => do
        let c ← nameP r x.1
        let e ← (fun _ => some ()) x.2.2
        pure (c, x.2.1, e)).isSome := by
      refine listMapM_isSome (fun x _ hx => ?_) (Option.isSome_iff_exists.2 ⟨_, hr⟩)
      simp only [bind, Option.bind] at hx ⊢
      cases hn : nameP r x.1 with
      | none => simp [hn] at hx
      | some c => simp [pure]
    obtain ⟨rs', hrs'⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨.recur as np ni nmo nmi rs' kk iu, ?_, rfl, fun q h => by cases h⟩
    simp only [CKindF.mapM, ha, bind, Option.bind]
    simp only [bind, Option.bind] at hrs'
    rw [hrs']
    rfl

/-- **A statement read in a region's first bytes reads the same in the region.** -/
theorem StmtSkel.sub {P R : Region} {n : Nat} (hs : Region.Sub P R n) {c : Nat} (hc : P.Good c)
    {cv : ConstantVal} {k : CKindF Name Unit} (h : StmtSkel P c cv k) : StmtSkel R c cv k := by
  obtain ⟨s, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨g1, g2⟩ := constSkel_ok h1
  have hn : nameP R s.name = some cv.name := by
    rw [hs.nameP_sub (g1 _ (by simp [CEntryF.names]))]; exact h2
  have hl : s.levelParams.mapM (nameP R) = some cv.levelParams := by
    rw [listMapM_congr _ fun x hx => hs.nameP_sub (g1 x (by simp [CEntryF.names, hx]))]; exact h3
  refine ⟨s, by rw [hs.constSkel_sub hc]; exact h1, hn, hl, ?_, ?_⟩
  · rw [hs.exprP_sub (g2 _ (by simp [CEntryF.exprs]))]; exact h4
  · have hE := CEntryF.mapM_congr (fn := nameP R) (fn' := nameP P)
      (fe := fun _ : UInt64 => (some () : Option Unit)) (fe' := fun _ => some ()) s
      (fun v hv => hs.nameP_sub (g1 v hv)) (fun _ _ => rfl)
    simp only [CEntryF.mapM, hn, h2, hl, h3, bind, Option.bind, h5] at hE
    cases hk : s.kind.mapM (nameP R) (fun _ => some ()) with
    | none => simp [hk] at hE
    | some k' =>
      simp only [hk, pure, Option.some.injEq, CEntryF.mk.injEq] at hE
      rw [hE.2.2.2]

/-- **How a copy's skeleton stands for the home's private constant behind it**: the same (its
statement and kind constructor read alike, a quotient constant's kind the same, and the whole
constant where it decodes), or its value hidden (an axiom of the statement the private
skeleton reads, a definition, theorem or opaque constant). -/
@[expose] def Behind (r1 : Region) (c : Nat) (r : Region) (loc : Nat) (sP : CEntryF UInt64 UInt64) :
    Prop :=
  ((∀ cv k, StmtSkel r1 c cv k → ∃ k', StmtSkel r loc cv k' ∧ k'.tag = k.tag ∧
      ∀ q, k = .quot q → k' = .quot q) ∧
    ∀ e, entryAt r1 c = some e → entryAt r loc = some e) ∨
  (∀ cv k, StmtSkel r1 c cv k → (∃ u, k = .ax u) ∧ nameP r sP.name = some cv.name ∧
    sP.levelParams.mapM (nameP r) = some cv.levelParams ∧ exprP r sP.type = some cv.type ∧
    (sP.kind.tag = 1 ∨ sP.kind.tag = 2 ∨ sP.kind.tag = 3))

theorem Behind.refl (r : Region) (c : Nat) (sP : CEntryF UInt64 UInt64) : Behind r c r c sP :=
  .inl ⟨fun _ k h => ⟨k, h, rfl, fun _ h => h⟩, fun _ h => h⟩

theorem hintsEq_eq {a b : HintsRec} (h : hintsEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [hintsEq]

theorem rulesEq_eq : ∀ {a b : List (Name × Nat × Expr)}, rulesEq a b = true → a = b
  | [], [], _ => rfl
  | (x, y, z) :: xs, (x', y', z') :: ys, h => by
    simp only [rulesEq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
    rw [rulesEq_eq h]
  | [], _ :: _, h => by simp [rulesEq] at h
  | _ :: _, [], h => by simp [rulesEq] at h

/-- **`entrySame` is equality.** -/
theorem entrySame_eq {a b : CEntryF Name Expr} (h : entrySame a b = true) : a = b := by
  obtain ⟨n, l, t, k⟩ := a
  obtain ⟨n', l', t', k'⟩ := b
  simp only [entrySame, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
  congr 1
  cases k <;> cases k' <;> simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
  all_goals first
    | (obtain ⟨⟨h1, h2⟩, h3⟩ := h; rw [h1, hintsEq_eq h2, h3])
    | (rcases h with ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩, hh⟩
       rw [ha, hb, hc, hd, he, rulesEq_eq hf, hg, hh])
    | simp_all

/-- `expoOf`'s verdict on two decoded constants: the same, or the second an axiom of the
first's statement, the first a definition, theorem or opaque constant, filtered alike. -/
theorem expoOf_cases {pc e : CEntryF Name Expr} {x : Expo} (h : expoOf pc e = some x) :
    pc = e ∨ (pc.stmt = e.stmt ∧ ∃ u, e.kind = .ax u ∧ pc.kind.skipped = u ∧
      (pc.kind.tag = 1 ∨ pc.kind.tag = 2 ∨ pc.kind.tag = 3)) := by
  unfold expoOf at h
  split at h
  · rename_i hs
    exact .inl (entrySame_eq hs)
  · split at h
    · rename_i hst
      simp only [Bool.and_eq_true, beq_iff_eq] at hst
      obtain ⟨⟨hn, hl⟩, ht⟩ := hst
      have hst' : pc.stmt = e.stmt := by simp [CEntryF.stmt, hn, hl, ht]
      right
      refine ⟨hst', ?_⟩
      split at h
      · rename_i v hh sf u hk1 hk2
        split at h
        · rename_i hu
          exact ⟨u, hk2, by simp [hk1, CKindF.skipped]; exact (beq_iff_eq.1 hu).symm,
            by simp [hk1, CKindF.tag]⟩
        · cases h
      · rename_i v all u hk1 hk2
        split at h
        · rename_i hu
          exact ⟨u, hk2, by simp [hk1, CKindF.skipped]; simpa using hu, by simp [hk1, CKindF.tag]⟩
        · cases h
      · rename_i v u' u hk1 hk2
        split at h
        · rename_i hu
          exact ⟨u, hk2, by simp [hk1, CKindF.skipped]; exact (beq_iff_eq.1 hu).symm,
            by simp [hk1, CKindF.tag]⟩
        · cases h
      · cases h
    · cases h

/-- **The home's private constant behind a copy** of one of its names, at a level a load reads
(`.exported` or `.private`): a skeleton of the home's private part, filtered as the copy is, that
the copy's stands for (`Behind`), by the home's check of its views where the copy is exported. -/
theorem copy_behind {sp : SearchPath} {fs : FS} {h : Name} {f : ModFiles} {r : Region}
    {a : UInt64} {sk : ModSkel} {l : Loaded} {expo : Array Expo}
    (hf : ModelIO.CanGive (readFiles sp h .private) fs (.ok f))
    (hreg : f.viewRegion .private = some (r, a)) (hsk : moduleSkel r a = some sk)
    (hload : loadAt 0 h f = some l) (hcv : checkViews h f l = .ok expo)
    {s : Spot} (hmod : s.part.mod = h) (hs : CopyAt sp fs s) (hl : s.part.level ≠ .server)
    {r1 : Region} (hr1 : PartRegion sp fs s.part r1) :
    ∃ loc sP s1, loc ∈ sk.consts ∧ constSkel r loc = some sP ∧
      constSkel r1 s.pos.loc = some s1 ∧ nameP r1 s1.name = some s.pos.name ∧
      s.pos.skipped = s1.kind.skipped ∧ sP.kind.skipped = s1.kind.skipped ∧
      Behind r1 s.pos.loc r loc sP ∧ nameP r sP.name = some s.pos.name := by
  obtain ⟨⟨m, L⟩, q⟩ := s
  simp only at hmod
  subst hmod
  obtain ⟨t, ht, hq⟩ := hs
  have hnt := readPartNames_of_all hf ht
  obtain ⟨f1, a1, hf1, hreg1⟩ := hr1
  have hf1' := partFiles_of_all hf hf1
  subst hf1'
  simp only at hl hreg1 hnt ⊢
  cases L with
  | server => exact absurd rfl hl
  | «private» =>
    simp only [ModFiles.upTo] at hreg1 hnt
    rw [hreg] at hreg1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg1)
    simp only [readNamePositions, hreg, Option.bind_eq_bind, Option.bind_some] at hnt
    obtain ⟨sk', hsk', -, hall⟩ := namePositionsAt_mem hnt
    rw [hsk] at hsk'
    cases hsk'
    obtain ⟨hloc, s1, hs1, hn1, -, hsk1⟩ := hall q hq
    exact ⟨q.loc, s1, s1, hloc, hs1, hs1, hn1, hsk1, rfl, Behind.refl _ _ _, hn1⟩
  | exported =>
    simp only [ModFiles.upTo, ModFiles.viewRegion, Option.some.injEq, Prod.mk.injEq] at hreg1
    obtain ⟨rfl, rfl⟩ := hreg1
    simp only [readNamePositions, ModFiles.upTo, ModFiles.viewRegion, Option.bind_eq_bind,
      Option.bind_some] at hnt
    obtain ⟨skE, hskE, -, hall⟩ := namePositionsAt_mem hnt
    obtain ⟨hloc, s1, hs1, hn1, -, hsk1⟩ := hall q hq
    cases hm : f.isModule with
    | false =>
      have hreg' : f.viewRegion .private =
          some (Region.single f.exported, f.exported.moduleDataAddr) := by
        simp [ModFiles.viewRegion, hm]
      rw [hreg] at hreg'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg')
      rw [hsk] at hskE
      cases hskE
      exact ⟨q.loc, s1, s1, hloc, hs1, hs1, hn1, hsk1, rfl, Behind.refl _ _ _, hn1⟩
    | true =>
      obtain ⟨_, _, hf'⟩ := hf
      obtain ⟨loc0, b, ex, -, -, -, hex, hpriv, -⟩ := readFiles_ok hf'
      have hm' : ModFiles.isModule { exported := ex } = true := by rw [← hex]; exact hm
      obtain ⟨bs, bp, sv, p, -, -, -, -, hfeq⟩ := hpriv rfl hm'
      subst hfeq
      simp only at hm hskE hs1 hn1 ⊢
      obtain ⟨r3, hr3, hexpo⟩ := checkViews_expo hcv hm rfl rfl
      have hreg3 : (ModFiles.viewRegion ⟨ex, some sv, some p⟩ .private) = some (r3, p.moduleDataAddr) := by
        simp [ModFiles.viewRegion, hm, hr3, Except.toOption, bind, Option.bind, pure]
      rw [hreg] at hreg3
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg3)
      obtain ⟨hrshape, ho1, ho2⟩ := ofParts_three hr3
      have hsub : Region.Sub (Region.single ex) r ex.bytes.size := by
        rw [hrshape]
        exact Region.Sub.trans (Region.Sub.single_two ex sv ho1) (Region.Sub.two_three ex sv p ho1 ho2)
          (by simp)
      obtain ⟨skP, skE', hskP, hskE', hexpoAt⟩ := expoOfParts_ok hexpo
      rw [hsk] at hskP
      cases hskP
      have hlocE : ∃ g, (Region.single ex).loc ex.moduleDataAddr = some g := by
        unfold moduleSkel at hskE
        obtain ⟨g, hg, -⟩ := bind_some_left hskE
        exact ⟨g, hg⟩
      obtain ⟨g, hg⟩ := hlocE
      rw [hsub.moduleSkel_sub hg, hskE] at hskE'
      cases hskE'
      have hgood := (hsub.moduleSkel_ok hskE).1 q.loc hloc
      have hs1r : constSkel r q.loc = some s1 := by rw [hsub.constSkel_sub hgood]; exact hs1
      have hentry : ∀ e, entryAt (Region.single ex) q.loc = some e → entryAt r q.loc = some e := by
        intro e he
        rw [entryAt_eq] at he ⊢
        rw [hsub.constSpec_sub hgood]
        exact he
      have hstmt : ∀ cv k, StmtSkel (Region.single ex) q.loc cv k → StmtSkel r q.loc cv k :=
        fun cv k h => h.sub hsub hgood
      have hn1r : nameP r s1.name = some q.name := by
        obtain ⟨g1, -⟩ := constSkel_ok hs1
        rw [hsub.nameP_sub (g1 _ (by simp [CEntryF.names]))]; exact hn1
      rcases hexpoAt q.loc hloc with hin | ⟨se, sp, en, i, loc, hse, hen, ⟨hi, hcsi⟩, hloci, hsp, alt⟩
      · exact ⟨q.loc, s1, s1, hin, hs1r, hs1, hn1, hsk1, rfl,
          .inl ⟨fun cv k h => ⟨k, hstmt cv k h, rfl, fun _ h => h⟩, hentry⟩, hn1r⟩
      rw [hs1r] at hse
      cases hse
      have hen' : en = q.name := by rw [hn1r] at hen; exact (Option.some.inj hen).symm
      -- the private constant at `loc`, as the load read it
      obtain ⟨r', a', sk', skels', hreg', hsk', hskels', hlen, hal⟩ := loadAt_aligned hload
      rw [hreg] at hreg'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg')
      rw [hsk] at hsk'
      cases hsk'
      have hlocm : loc ∈ sk.consts := List.mem_of_getElem? hloci
      have hil : i < skels'.length := by
        have := mapM_length_opt hskels'
        have := (List.getElem?_eq_some_iff.1 hloci).1
        omega
      have hski : skels'[i] = sp := by
        have h1 := mapM_getElem? hskels' i
        rw [hloci, Option.bind_some, hsp, List.getElem?_eq_getElem hil] at h1
        exact Option.some.inj h1
      have hcs : (l.constants.map (·.toCEntryF))[i]'(by simpa using hi) =
          (l.constants[i]'(by simpa using hi)).toCEntryF := by simp
      have hlz : lazyEntry (nameP r) (exprP r) r 0 sp = some (l.constants[i]'(hlen ▸ hil)).toCEntryF := by
        rw [← hski]; exact hal i hil
      have hspn : nameP r sp.name = some en := by
        rw [(lazyEntry_stmt hlz).1, ← hcsi, hcs]
      have hspq : nameP r sp.name = some q.name := hen' ▸ hspn
      -- the statement of a copy, as the private part reads it at `q.loc`
      have hst1 : ∀ cv k, StmtSkel (Region.single ex) q.loc cv k →
          nameP r s1.name = some cv.name ∧ s1.levelParams.mapM (nameP r) = some cv.levelParams ∧
          exprP r s1.type = some cv.type ∧ s1.kind.mapM (nameP r) (fun _ => some ()) = some k := by
        intro cv k h
        obtain ⟨s', hs', h1, h2, h3, h4⟩ := hstmt cv k h
        rw [hs1r] at hs'
        cases hs'
        exact ⟨h1, h2, h3, h4⟩
      rcases alt with ⟨hk, hty, hlps⟩ | ⟨e, pc, x, he, hx, hthm, hnthm⟩
      · refine ⟨loc, sp, s1, hlocm, hsp, hs1, hn1, hsk1, ?_, .inr fun cv k h => ?_, hspq⟩
        · unfold hiddenKind at hk
          split at hk <;> rename_i hk1 hk2 <;> simp only [hk1, hk2, CKindF.skipped] at hk ⊢
          all_goals first
            | (cases hk; done)
            | exact (beq_iff_eq.1 hk).symm
            | (simp only [Bool.not_eq_true'] at hk; exact hk.symm)
        · obtain ⟨h1, h2, h3, h4⟩ := hst1 cv k h
          rw [hen] at h1
          cases h1
          refine ⟨?_, hspn, hlps ▸ h2, hty ▸ h3, ?_⟩
          · unfold hiddenKind at hk
            split at hk <;> rename_i hk1 hk2
            all_goals first
              | (rw [hk1] at h4; simp only [CKindF.mapM, pure, Option.some.injEq] at h4
                 exact ⟨_, h4.symm⟩)
              | cases hk
          · unfold hiddenKind at hk
            split at hk <;> rename_i hk1 hk2 <;> simp [hk2, CKindF.tag] at hk ⊢
      · -- the private constant decoded at `loc`
        have hpc : entryAt r loc = some pc := by
          by_cases ht : ∃ v all, (l.constants.map CEntry.toCEntryF)[i]!.kind = CKindF.thm v all
          · exact hthm ht
          · have hpc' := hnthm (fun v all h' => ht ⟨v, all, h'⟩)
            subst hpc'
            have hbang : (l.constants.map CEntry.toCEntryF)[i]! =
                (l.constants[i]'(hlen ▸ hil)).toCEntryF := by
              rw [getElem!_pos _ _ (by simpa using hi)]; simp
            rw [hbang] at ht ⊢
            have htag := (lazyEntry_kind hlz).2
            rw [entryAt_eq]
            simp only [constSpec, hsp, Option.bind_eq_bind, Option.bind_some]
            revert hlz htag
            rcases sp with ⟨sn, sl, st, sk0⟩
            cases sk0 with
            | thm v all =>
              intro _ htag
              exfalso
              apply ht
              cases hk : (l.constants[i]'(hlen ▸ hil)).kind <;> rw [hk] at htag <;>
                simp [CKindF.tag] at htag
              exact ⟨_, _, rfl⟩
            | _ => intro hlz _; simp only [lazyEntry] at hlz; exact hlz
        have hmP : sp.mapM (nameP r) (exprP r) = some pc := by
          rw [entryAt_eq] at hpc
          obtain ⟨s'', hs'', hm''⟩ := constSpec_parts hpc
          rw [hsp] at hs''
          cases hs''
          exact hm''
        have hm1 : s1.mapM (nameP r) (exprP r) = some e := by
          rw [entryAt_eq] at he
          obtain ⟨s'', hs'', hm''⟩ := constSpec_parts he
          rw [hs1r] at hs''
          cases hs''
          exact hm''
        have he1 : entryAt (Region.single ex) q.loc = some e := by
          rw [entryAt_eq, ← hsub.constSpec_sub hgood, ← entryAt_eq]; exact he
        obtain ⟨hn1', hl1', ht1', htag1, hsk1'⟩ := CEntryF.mapM_parts hmP
        obtain ⟨hnE, hlE, htE, htagE, hskE'⟩ := CEntryF.mapM_parts hm1
        -- a copy's statement is its decoded constant's
        have hcvE : ∀ cv k, StmtSkel (Region.single ex) q.loc cv k → cv = e.stmt ∧
            s1.kind.mapM (nameP r) (fun _ => some ()) = some k := by
          intro cv k h
          obtain ⟨h1, h2, h3, h4⟩ := hst1 cv k h
          refine ⟨?_, h4⟩
          rw [hnE] at h1; rw [hlE] at h2; rw [htE] at h3
          obtain ⟨n, l', t'⟩ := cv
          simp only [Option.some.injEq] at h1 h2 h3
          simp [CEntryF.stmt, h1, h2, h3]
        rcases expoOf_cases hx with rfl | ⟨hst, u, heu, hpu, hpt⟩
        · refine ⟨loc, sp, s1, hlocm, hsp, hs1, hn1, hsk1, by rw [hsk1', hskE'], .inl ⟨?_, ?_⟩, hspq⟩
          · intro cv k h
            obtain ⟨hcv, hk1⟩ := hcvE cv k h
            obtain ⟨k', hk', htk', hq'⟩ := kind_names hmP
            obtain ⟨k'', hk'', htk'', hq''⟩ := kind_names hm1
            rw [hk1] at hk''
            cases hk''
            refine ⟨k', ⟨sp, hsp, ?_, ?_, ?_, hk'⟩, by rw [htk', ← htk''], fun q0 hq0 => ?_⟩
            · rw [hn1', hcv]; rfl
            · rw [hl1', hcv]; rfl
            · rw [ht1', hcv]; rfl
            · subst hq0
              have h4 : pc.kind.tag = 4 := by rw [← htk'']; rfl
              cases hpk : pc.kind with
              | quot q1 =>
                have := hq'' q1 hpk
                cases this
                exact hq' _ hpk
              | _ => rw [hpk] at h4; simp [CKindF.tag] at h4
          · intro e' he'
            rw [he1] at he'
            cases he'
            exact hpc
        · refine ⟨loc, sp, s1, hlocm, hsp, hs1, hn1, hsk1, ?_, .inr fun cv k h => ?_, hspq⟩
          · rw [hsk1', hskE', heu, hpu]; rfl
          · obtain ⟨hcv, hk1⟩ := hcvE cv k h
            refine ⟨?_, ?_, ?_, ?_, by rw [htag1]; exact hpt⟩
            · have h0 : k.tag = 0 := by
                rw [← (CKindF.mapM_tag hk1).1, htagE, heu]; rfl
              cases k <;> simp_all [CKindF.tag]
            · rw [hn1', hcv, ← hst]; rfl
            · rw [hl1', hcv, ← hst]; rfl
            · rw [ht1', hcv, ← hst]; rfl

/-! ## A record presents its source's own record -/

/-- A part's region on the snapshot is one. -/
theorem partRegion_unique {sp : SearchPath} {fs : FS} {h : Name} {f : ModFiles}
    (hf : ModelIO.CanGive (readFiles sp h .private) fs (.ok f)) {L : OLeanLevel} {r r' : Region}
    (h1 : PartRegion sp fs ⟨h, L⟩ r) (h2 : PartRegion sp fs ⟨h, L⟩ r') : r = r' := by
  obtain ⟨f1, a1, hf1, hr1⟩ := h1
  obtain ⟨f2, a2, hf2, hr2⟩ := h2
  have e1 := partFiles_of_all hf hf1
  have e2 := partFiles_of_all hf hf2
  subst e1; subst e2
  rw [hr1] at hr2
  exact (Prod.mk.inj (Option.some.inj hr2)).1

/-- **A private copy's kind is that of the private skeleton of its name.** -/
theorem private_tag {sp : SearchPath} {fs : FS} {h : Name} {f : ModFiles} {r : Region} {a : UInt64}
    {sk : ModSkel} {skels : List (CEntryF UInt64 UInt64)}
    (hf : ModelIO.CanGive (readFiles sp h .private) fs (.ok f))
    (hreg : f.viewRegion .private = some (r, a)) (hsk : moduleSkel r a = some sk)
    (hskels : sk.consts.mapM (constSkel r) = some skels) (hcn : constNamesOk r a = true)
    {q : Spot} (hq : CopyAt sp fs q) (hqp : q.part = ⟨h, .private⟩)
    {loc : Nat} {sP : CEntryF UInt64 UInt64} (hloc : loc ∈ sk.consts)
    (hsP : constSkel r loc = some sP) (hn : nameP r sP.name = some q.pos.name) :
    q.pos.tag = sP.kind.tag := by
  obtain ⟨⟨m, L⟩, pos⟩ := q
  simp only [PartKey.mk.injEq] at hqp
  obtain ⟨rfl, rfl⟩ := hqp
  obtain ⟨t, ht, hpos⟩ := hq
  have hnt := readPartNames_of_all hf ht
  simp only [ModFiles.upTo, readNamePositions, hreg, Option.bind_eq_bind, Option.bind_some] at hnt
  obtain ⟨sk', hsk', -, hall⟩ := namePositionsAt_mem hnt
  rw [hsk] at hsk'
  cases hsk'
  obtain ⟨hl', sq, hsq, hnq, htq, -⟩ := hall pos hpos
  obtain ⟨sP', hm1, h1⟩ := mapM_mem hskels hloc
  obtain ⟨sq', hm2, h2⟩ := mapM_mem hskels hl'
  rw [hsP] at h1; rw [hsq] at h2
  cases h1; cases h2
  rw [skels_name_inj hcn hsk hskels hm2 hm1 hnq hn] at htq
  exact htq

/-- A quotient constant's skeleton, as the load reads it. -/
theorem lazyEntry_quot {r : Region} {loc : Nat} {s : CEntryF UInt64 UInt64} {cv : ConstantVal}
    {q : String} {E : CEntryF Name Expr} (hs : constSkel r loc = some s)
    (hst : StmtSkel r loc cv (.quot q)) (hE : lazyEntry (nameP r) (exprP r) r 0 s = some E) :
    E = ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ := by
  obtain ⟨s', hs', hn, hl, ht, hk⟩ := hst
  rw [hs] at hs'
  cases hs'
  rcases s with ⟨sn, sl, st, sk0⟩
  cases sk0 with
  | quot q' =>
    simp only [CKindF.mapM, pure, Option.some.injEq, CKindF.quot.injEq] at hk
    subst hk
    simp only [lazyEntry, CEntryF.mapM, CKindF.mapM] at hE
    simp only at hn hl ht
    simp [hn, hl, ht, bind, Option.bind, pure] at hE
    rw [← hE]
  | _ =>
    have := (CKindF.mapM_tag hk).1
    simp [CKindF.tag] at this

theorem groupOfKind_tag {x : Name} {k : CKindF Name Unit} (hg : groupOfKind x k = none)
    (hq : k.tag ≠ 4) : k.tag < 4 := by
  cases k <;> simp_all [groupOfKind, CKindF.tag]

/-- **The statement, whole-constant and quotient cases.** -/
theorem recordFrom_presents_nongroup {sp : SearchPath} {fs : FS} {h : Name}
    {jobs : Nat} {w : WorkerRead} (hw : WorkerFacts sp fs h jobs w) :
    (∀ {x : Name} {s : Spot} {r : Region} {cv : ConstantVal} {k : CKindF Name Unit},
      s.part.mod = h → CopyAt sp fs s → s.part.level ≠ .server → PartRegion sp fs s.part r →
      StmtSkel r s.pos.loc cv k → s.pos.skipped = false → groupOfKind x k = none → k.tag ≠ 4 →
      (reduceOpNames.contains cv.name = true → ∃ q : Spot, CopyAt sp fs q ∧
        q.part = ⟨s.part.mod, .private⟩ ∧ q.pos.name = s.pos.name ∧
        (q.pos.tag = 0 ∨ q.pos.tag = 3)) →
      ∃ p ∈ w.emitted, Presents (.axiomDecl cv) p) ∧
    (∀ {s : Spot} {r r₀ : Region} {e : CEntryF Name Expr} {d : Declaration} {cv : ConstantVal}
      {k : CKindF Name Unit}, s.part.mod = h → CopyAt sp fs s → s.part.level ≠ .server →
      PartRegion sp fs s.part r → entryAt r s.pos.loc = some e → PartRegion sp fs s.part r₀ →
      StmtSkel r₀ s.pos.loc cv k → k.tag = 1 → s.pos.skipped = false → recordOfEntry e = .ok d →
      ∃ p ∈ w.emitted, Presents d p) ∧
    (∀ {s : Spot} {r : Region} {cv : ConstantVal} {q : String} {d : Declaration},
      s.part.mod = h → CopyAt sp fs s → s.part.level ≠ .server → PartRegion sp fs s.part r →
      StmtSkel r s.pos.loc cv (.quot q) →
      recordOfEntry ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ = .ok d →
      ∃ p ∈ w.emitted, Presents d p) := by
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, hskels, hcn, hcv, hload, hN, hO, hb, hem, hown⟩ :=
    home_records hw
  refine ⟨fun {x s r1 cv k} hmod hs hl hr hst hsk0 hg hq hred => ?_,
    fun {s r1 r₀ e d cv k} hmod hs hl hr he hr₀ hst hk1 hsk0 hd => ?_,
    fun {s r1 cv q d} hmod hs hl hr hst hd => ?_⟩
  · obtain ⟨loc, sP, s1, hloc, hsP, hs1, hn1, hskq, hskP, hbeh, -⟩ :=
      copy_behind hf hreg hsk hload hcv hmod hs hl hr
    have hskp : sP.kind.skipped = false := by rw [hskP, ← hskq, hsk0]
    have hpos : s.pos.name = cv.name := by
      obtain ⟨s', hs', hn', -⟩ := hst
      rw [hs1] at hs'
      cases hs'
      rw [hn1] at hn'
      exact Option.some.inj hn'
    have hred' : ∀ {sP' : CEntryF UInt64 UInt64}, constSkel r loc = some sP' →
        nameP r sP'.name = some cv.name → reduceOpNames.contains cv.name = true →
        sP'.kind.tag = 0 ∨ sP'.kind.tag = 3 := by
      intro sP' hsP' hn' hr'
      obtain ⟨q', hq', hqp, hqn, hqt⟩ := hred hr'
      rw [hmod] at hqp
      have := private_tag hf hreg hsk hskels hcn hq' hqp hloc hsP' (by rw [hqn, hpos]; exact hn')
      rw [← this]; exact hqt
    rcases hbeh with ⟨hsame, -⟩ | hhid
    · obtain ⟨k', ⟨sP', hsP', hn, hl', ht, hkm⟩, htk, -⟩ := hsame cv k hst
      rw [hsP] at hsP'
      cases hsP'
      have htag : sP.kind.tag < 4 := by
        rw [(CKindF.mapM_tag hkm).1, htk]; exact groupOfKind_tag hg hq
      exact stmt_presents hN hO hb hem hown hloc hsP hskp hn hl' ht htag (hred' hsP hn)
    · obtain ⟨-, hn, hl', ht, htag⟩ := hhid cv k hst
      exact stmt_presents hN hO hb hem hown hloc hsP hskp hn hl' ht (by omega) (hred' hsP hn)
  · obtain ⟨rfl⟩ : r₀ = r1 := by
      rw [← hmod] at hf
      exact partRegion_unique hf hr₀ hr
    obtain ⟨loc, sP, s1, hloc, hsP, hs1, hn1, hskq, hskP, hbeh, -⟩ :=
      copy_behind hf hreg hsk hload hcv hmod hs hl hr
    have hskp : sP.kind.skipped = false := by rw [hskP, ← hskq, hsk0]
    have het : e.kind.tag = 1 := by rw [(StmtSkel.entry hst he).2, hk1]
    rcases hbeh with ⟨-, hent⟩ | hhid
    · exact whole_presents hN hO hb hem hown hloc hsP hskp
        (fun E hE => lazyEntry_entryAt hsP hE (hent e he) (by omega)) (by omega) hd
    · obtain ⟨⟨u, rfl⟩, -⟩ := hhid cv k hst
      simp [CKindF.tag] at hk1
  · obtain ⟨loc, sP, s1, hloc, hsP, hs1, hn1, hskq, hskP, hbeh, -⟩ :=
      copy_behind hf hreg hsk hload hcv hmod hs hl hr
    rcases hbeh with ⟨hsame, -⟩ | hhid
    · obtain ⟨k', hk', -, hq'⟩ := hsame cv _ hst
      obtain rfl := hq' q rfl
      have hskp : sP.kind.skipped = false := by
        obtain ⟨s', hs', -, -, -, hkm⟩ := hk'
        rw [hsP] at hs'
        cases hs'
        cases hk0 : sP.kind <;> rw [hk0] at hkm <;>
          first | rfl | (have := (CKindF.mapM_tag hkm).1; simp [CKindF.tag] at this)
      exact whole_presents hN hO hb hem hown hloc hsP hskp (fun E hE => lazyEntry_quot hsP hk' hE)
        (by simp [CKindF.tag]) hd
    · obtain ⟨⟨u, hu⟩, -⟩ := hhid cv _ hst
      cases hu

end ConLeche.Driver
