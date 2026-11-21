module

public import ConLeche.Verify.Driver.ComposeReads
import ConLeche.Verify.Driver.RouteCtx
import ConLeche.Verify.Driver.RoutePub
import ConLeche.Verify.Driver.RouteWorker
public import ConLeche.Verify.Driver.Copies
public import ConLeche.Verify.Driver.Clashes
import ConLeche.Verify.Driver.PropPart
import ConLeche.Verify.Driver.Graph

/-!
# The routes of the capture check's pairs, and the local checks of a run

At a module `M` of a run (task #501), every pair `(h, y)` the capture check passed whose context
copy is not the reader `h`'s own has a `Route` (`Run.route`), read off the branch of
`captureOne` that passed it:

* **the public-import route**: the copy is of a module `M1` of `h`'s public-import closure that
  exports `y`; `M1` is loaded at `h`, so `h`'s copy of `y` agrees with `M1`'s: one module, or two
  copies of a clash at `h`, proofs of one statement whose names `h`'s clash partner reads passed
  (`agree_loaded`);
* **the view route**: the copy agrees with `h`'s view's first copy `s₂` (`AgreeOk`): one module
  (`h` reads `y` from it), or two proofs of one statement, `s₂` a constant of its module's own
  environment, its statement's names passed as reads of that module (`proofAt_of`).

With them `ImportOk.reads` holds at every module (`reads_of_routes`), and so `LocalOk`
(`Run.localOk`).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

/-- **The reach's table lists every copy of a clash**, under the clash's name. -/
theorem clashCopiesOf_complete {sp : Roots} {fs : FS} {m : Name} {jobs : Nat} {x : Array ImportRec}
    {wr : WorkerReads} {hs hs' : HS}
    (h : (workerReads (.ofPath sp) m jobs x : ModelIO _) fs hs (.ok (.ok wr)) hs')
    {cl : Clash} (hcl : cl ∈ wr.clashes.toList) {e : Copy × ConstantVal × CKindF Name Unit}
    (he : e ∈ cl.copies.toList) :
    ∃ cs, (clashCopiesOf wr)[cl.name]? = some cs ∧ (wr.loads.nameAt e.1.mod, e.2.1) ∈ cs.toList := by
  obtain ⟨-, ⟨infos, -, hcls⟩, -⟩ := workerReads_open h
  obtain ⟨-, -, hmore, -, -, -⟩ := workerIndex_copies h
  obtain ⟨c1, -⟩ := clashCopies_spec (ix := wr.index) fun n c hm => by
    obtain ⟨-, cp₀, hf, -⟩ := hmore n c hm
    rw [hf]; rfl
  let g : Copy × ConstantVal × CKindF Name Unit → Name × ConstantVal :=
    fun x => (wr.loads.nameAt x.1.mod, x.2.1)
  let ins : Std.HashMap Name (Array (Name × ConstantVal)) → Clash →
      Std.HashMap Name (Array (Name × ConstantVal)) := fun m cl => m.insert cl.name (cl.copies.map g)
  have hkeep : ∀ (l : List Clash) (m : Std.HashMap Name (Array (Name × ConstantVal))),
      (∀ c ∈ l, c.name ≠ cl.name) → (l.foldl ins m)[cl.name]? = m[cl.name]? := by
    intro l
    induction l with
    | nil => intro m _; rfl
    | cons a l ih =>
      intro m hl
      rw [List.foldl_cons, ih _ (fun c hc => hl c (List.mem_cons_of_mem _ hc))]
      simp only [ins, Std.HashMap.getElem?_insert]
      have hne : a.name ≠ cl.name := hl a List.mem_cons_self
      simp [hne]
  have hlast : ∀ (l : List Clash) (m : Std.HashMap Name (Array (Name × ConstantVal))),
      (∃ c ∈ l, c.name = cl.name) →
      ∃ c ∈ l, c.name = cl.name ∧ (l.foldl ins m)[cl.name]? = some (c.copies.map g) := by
    intro l
    induction l with
    | nil => intro m ⟨c, hc, _⟩; cases hc
    | cons a l ih =>
      intro m hex
      by_cases hl : ∃ c ∈ l, c.name = cl.name
      · obtain ⟨c, hc, hn, he⟩ := ih (ins m a) hl
        exact ⟨c, List.mem_cons_of_mem _ hc, hn, by rw [List.foldl_cons]; exact he⟩
      · have ha : a.name = cl.name := by
          obtain ⟨c, hc, hn⟩ := hex
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hn
          · exact absurd ⟨c, hc, hn⟩ hl
        refine ⟨a, List.mem_cons_self, ha, ?_⟩
        rw [List.foldl_cons, hkeep l _ (fun c hc hn => hl ⟨c, hc, hn⟩)]
        simp [ins, ha]
  obtain ⟨c, hc, hcn, hcs⟩ := hlast wr.clashes.toList {} ⟨cl, hcl, rfl⟩
  refine ⟨c.copies.map g, by
    show (wr.clashes.foldl ins {})[cl.name]? = _
    rw [← Array.foldl_toList]; exact hcs, ?_⟩
  rw [hcls, Array.toList_map] at hcl hc
  obtain ⟨⟨n, a⟩, ha, rfl⟩ := List.mem_map.1 hcl
  obtain ⟨⟨n', a'⟩, ha', rfl⟩ := List.mem_map.1 hc
  simp only at hcn
  subst hcn
  simp only [Array.toList_filterMap, List.mem_filterMap] at he
  obtain ⟨d, hd, hdv⟩ := he
  have hd' : d ∈ a'.toList :=
    (c1 n' a' (Array.mem_toList_iff.1 ha') d).2 ((c1 n' a (Array.mem_toList_iff.1 ha) d).1 hd)
  rw [Array.toList_map]
  refine List.mem_map.2 ⟨e, ?_, rfl⟩
  simp only [Array.toList_filterMap, List.mem_filterMap]
  exact ⟨d, hd', hdv⟩

/-- One statement is one `ConstantVal`. -/
theorem SameStmt.eq {a b : ConstantVal} (h : SameStmt a b) : a = b := by
  obtain ⟨n, l, t⟩ := a
  obtain ⟨n', l', t'⟩ := b
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- A recorded copy is of a loaded module. -/
theorem at_mod_lt {wr : WorkerReads} (hsize : wr.index.parts.size = wr.loads.order.size)
    {cp : Copy} {q : NamePosition} (h : wr.index.at cp = some q) : cp.mod < wr.loads.order.size := by
  unfold NameIndex.at at h
  obtain ⟨t, ht, -⟩ := Option.bind_eq_some_iff.1 h
  rw [← hsize]
  exact (Array.getElem?_eq_some_iff.1 ht).1

namespace Run

variable {sp : Roots} {fs : FS} {maxNatSize : Nat} (R : Run sp fs maxNatSize)

/-- The own records' run is an `OwnRun`. -/
theorem ownRun {M : Name} (hM : M ∈ R.names) :
    OwnRun .verified maxNatSize (R.look M) fs M (R.w M) :=
  ⟨_, R.run M hM⟩

/-- **A copy whose proof status is `.yes` is a theorem of its module's own environment**, of the
copy's statement. -/
theorem thm_of_status {a : Roots} (ha : a.Trims sp) {y T : Name} (hT : T ∈ R.names)
    (hxT : R.x T = #[])
    {s : Spot} (hmod : s.part.mod = T) (hs : CopyAt a fs s) (hl : s.part.level ≠ .server)
    {r : Region} {cv : ConstantVal} {k : CKindF Name Unit} (hr : PartRegion a fs s.part r)
    (hst : StmtSkel r s.pos.loc cv k) (hsk : s.pos.skipped = false) (hy : cv.name = y)
    (hsy : y ≠ sorryAxName) (hp : StatusOk a fs s k .yes) :
    (R.dev (R.rk T)).own.find? y = some (.thmInfo cv) := by
  have htag := hp.1 (fun h => nomatch h)
  obtain ⟨ci, hci, hcv, -, hthm, -⟩ := copy_own (R.facts₀ hT hxT) (R.ownRun hT) hmod
    (R.copy_own' ha hT hmod hs) hl (R.region_own ha hT hmod hr) hst hsk
    htag (by rw [hy]; exact hsy)
  obtain ⟨cv', rfl⟩ := hthm (by
    rcases hp.2.1 rfl with h2 | ⟨h0, -, q, hq, hqp, hqn, hqt⟩
    · exact .inl h2
    · exact .inr ⟨q, R.copy_own' ha hT (by rw [hqp, hmod]) hq, by rw [hqp, hmod], hqn, hqt⟩)
  obtain rfl : cv' = cv := hcv
  rw [R.dev_rk hT, ← hy]
  exact hci

/-- **A recorded inference holds over the part below its name.** -/
theorem prop_of_pending {M : Name} (hM : M ∈ R.names) {w : String} {y : Name} {cv : ConstantVal}
    (hmem : (w, y, cv) ∈ (R.cap M).2.1) :
    TypeIsProp .verified ((R.dev (R.rk M)).part y) cv.type := by
  obtain ⟨-, -, -, -, hfl, -⟩ := R.cap_facts hM
  have hw := worker_ctx (R.facts M hM)
  exact (typeIsProp_part (m := R.dev (R.rk M))
    (by rw [R.dev_rk hM]; exact hw.1) (by rw [R.dev_rk hM]; exact hw.2.2.2.1)
    (by rw [R.dev_rk hM]; exact hfl) hmem).2

/-- **The importer's copy at a module is its index's first copy.** -/
theorem copyOf_first {h y : Name} {cp : Copy} {q : NamePosition}
    (hf : (R.w h).reads.index.first[y]? = some cp) (hq : (R.w h).reads.index.at cp = some q) :
    copyOf (R.envOf h) (R.cap h).1 y = some (spotOf (R.w h).reads cp q) := by
  simp [copyOf, importerSpot, envOf, hf, hq, spotOf]

/-- **A loaded copy at a module agrees with the one the module reads**: one module, or two
copies of a clash, proofs of one statement whose names the module's clash partner reads passed. -/
theorem agree_loaded {h : Name} (hh : h ∈ R.names) (ih : R.AgreeAll h) {y : Name}
    (hy : ((R.dev (R.rk h)).context.find? y).isSome = true) {cp : Copy} {q : NamePosition}
    (hq : (R.w h).reads.index.at cp = some q) (hqn : q.name = y) :
    Agree R.dev (R.rk h) (R.rk ((R.w h).reads.loads.nameAt cp.mod)) y := by
  have hw := R.facts h hh
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨-, hfirst, -, -, -, -⟩ := workerIndex_copies hr
  obtain ⟨-, -, -, -, hsize, -⟩ := workerReads_loads hr
  obtain ⟨s₀, hs₀, hsrc⟩ := R.src_copy hh hy
  obtain ⟨cp₀, hf⟩ := Option.isSome_iff_exists.1 (hqn ▸ first_of_at hw hq)
  obtain ⟨q₀, hq₀, hn₀⟩ := hfirst y cp₀ hf
  obtain rfl : s₀ = spotOf (R.w h).reads cp₀ q₀ :=
    Option.some.inj (hs₀.symm.trans (R.copyOf_first hf hq₀))
  by_cases hm : (R.w h).reads.loads.nameAt cp₀.mod = (R.w h).reads.loads.nameAt cp.mod
  · exact .same (by rw [hsrc]; simp only [spotOf]; rw [hm])
  have hne : cp₀ ≠ cp := fun e => hm (by rw [e])
  obtain ⟨cl, hcl, hcln, ⟨cv₀, kd₀, he₀⟩, cv, kd, he⟩ :=
    workerClash_complete hr hne hq₀ hq hn₀ hqn
  obtain ⟨q₀', hq₀', hc₀, ⟨rg₀, hr₀, hst₀⟩, -, -⟩ := workerClash_stmt hr hcl he₀
  obtain ⟨q', hq', hc, ⟨rg, hrg, hst⟩, -, hcvn⟩ := workerClash_stmt hr hcl he
  rw [hq₀] at hq₀'; cases hq₀'
  rw [hq] at hq'; cases hq'
  obtain ⟨hsk01, htag0⟩ := workerClash_kinds hr hcl he₀ he
  obtain ⟨-, htag⟩ := workerClash_kinds hr hcl he he₀
  have ht0 : kd₀.tag < 4 := by rcases htag0 with h | h <;> simp only at h <;> omega
  have ht : kd.tag < 4 := by rcases htag with h | h <;> simp only at h <;> omega
  obtain ⟨ci, hci, hcicv, hcik, -, -, hsk₀, -, hsy, hM0, -⟩ := R.ctx_stmt hh hy hs₀ hr₀ hst₀ ht0
  have hsame : cv₀ = cv := SameStmt.eq (workerClash_same hr hcl he₀ he)
  subst hsame
  have hskip : (spotOf (R.w h).reads cp q).pos.skipped = false := by
    rw [(copyAt_kind hc hrg hst).2, ← (show kd₀.skipped = kd.skipped from hsk01),
      ← (copyAt_kind hc₀ hr₀ hst₀).2, hsk₀]
  have hT := (R.reached_rank hh (.loaded (at_mod_lt hsize hq))).1
  have hxT := (R.reached_rank hh (.loaded (at_mod_lt hsize hq))).2.2
  have hcvy : cv₀.name = y := hcvn.trans hcln
  obtain ⟨ci', hci', hcv', hk', -, hfresh⟩ := copy_own (R.facts₀ hT hxT) (R.ownRun hT) rfl
    (R.copy_own' (R.trims h) hT rfl hc)
    (spotOf_level _ _ _) (R.region_own (R.trims h) hT rfl hrg) hst hskip ht (by rw [hcvy]; exact hsy)
  rw [hcvy] at hci'
  replace hci' : (R.dev (R.rk ((R.w h).reads.loads.nameAt cp.mod))).own.find? y = some ci' := by
    rw [R.dev_rk hT]; exact hci'
  have hcne : ∀ c ∈ ci.toConstantVal.type.readNames, c ≠ y := fun c hc e =>
    hfresh (by rw [hcvy, ← e]; simpa [hcicv] using hc)
  -- every clash copy's statement's names, read as its module reads them
  have hnames : ∀ x ∈ cl.copies.toList, ∀ c ∈ ci.toConstantVal.type.readNames,
      Agree R.dev (R.rk h) (R.rk ((R.w h).reads.loads.nameAt x.1.mod)) c := by
    intro x hx c hc
    obtain ⟨-, hctx⟩ := R.rank_lt hh hci hcik hc (hcne c hc)
    refine ih (_, c) ?_ hctx
    obtain ⟨k, d, hm', hk, hhm, hyd⟩ := R.ctx_record hh hy
    obtain ⟨-, hrec, -⟩ := R.cap_facts hh
    obtain ⟨cs, hcs, hmem⟩ := clashCopiesOf_complete hr hcl hx
    rw [hcln] at hcs
    have hxs : x.2.1 = cv₀ := SameStmt.eq (workerClash_same hr hcl hx he)
    exact (hrec k d hm' hk hhm).2.2.2 y hyd cs hcs _ (Array.mem_toList_iff.1 hmem) c
      (readNames_needsGo (by rw [hxs, ← hcicv]; exact hc))
  have hres : ci.toConstantVal.type.constsResolve ((R.dev (R.rk h)).part y) = true :=
    part_resolve fun c hc => R.rank_lt hh hci hcik hc (hcne c hc)
  obtain ⟨-, -, -, hclash, -⟩ := R.cap_facts hh
  rcases (hclash cl (Array.mem_toList_iff.1 hcl)).2 ⟨_, Array.mem_toList_iff.1 he, by rw [hq]; rfl⟩
    with ⟨x, hx, qx, hqx, hyes⟩ | ⟨w, cv', hpend, x', hx', rfl⟩
  · -- a theorem copy, of a loaded module of smaller rank: no inference
    have hx' := Array.mem_toList_iff.2 hx
    obtain ⟨qx', hqx', hcx, ⟨rgx, hrgx, hstx⟩, -, hcvnx⟩ := workerClash_stmt hr hcl hx'
    rw [hqx] at hqx'; cases hqx'
    obtain ⟨hskx, -⟩ := workerClash_kinds hr hcl he₀ hx'
    have hskipx : (spotOf (R.w h).reads x.1 qx).pos.skipped = false := by
      rw [(copyAt_kind hcx hrgx hstx).2, ← (show kd₀.skipped = x.2.2.skipped from hskx),
        ← (copyAt_kind hc₀ hr₀ hst₀).2, hsk₀]
    obtain ⟨hU, hUlt, hxU⟩ := R.reached_rank hh (.loaded (at_mod_lt hsize hqx))
    have hxs : x.2.1 = cv₀ := SameStmt.eq (workerClash_same hr hcl hx' he)
    have hthm := R.thm_of_status (R.trims h) hU hxU rfl hcx (spotOf_level _ _ _) hrgx hstx hskipx
      (hcvnx.trans hcln) hsy hyes
    exact .thm hci hci' (hcv'.trans hcicv.symm) hcik hk' (hnames _ he) hres hUlt hthm
      (by rw [hxs, hcicv]) (hnames _ hx')
  · -- no copy is a theorem: the statement, inferred over the part below the name
    have hxs : x'.2.1 = cv₀ := SameStmt.eq (workerClash_same hr hcl (Array.mem_toList_iff.2 hx') he)
    exact .proof hci hci' (hcv'.trans hcicv.symm) hcik hk' (hnames _ he) hres
      (by rw [hcicv, ← hxs]; exact R.prop_of_pending hh (hcln ▸ hpend))

/-- **Two proofs of one statement, the view's copy a constant of its module**: the view route's
proof pair at module `M` (`AgreeOk`'s second arm), the view's copy `s₂` of module `T`. -/
theorem proofAt_of {M : Name} (hM : M ∈ R.names) {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) {s₁ : Spot}
    (hs₁ : copyOf (R.envOf M) (R.cap M).1 y = some s₁) {T : Name} (hT : T ∈ R.names)
    (hxT : R.x T = #[]) (hTM : R.rk T < R.rk M) {s₂ : Spot}
    (hmod₂ : s₂.part.mod = T) (hc₂ : CopyAt (R.look M) fs s₂) (hl₂ : s₂.part.level ≠ .server)
    {r₁ : Region} {cv₁ : ConstantVal} {k₁ : CKindF Name Unit} {r₂ : Region} {cv₂ : ConstantVal}
    {k₂ : CKindF Name Unit} {p₁ p₂ : ProofStatus}
    (hr₁ : PartRegion (R.look M) fs s₁.part r₁) (hst₁ : StmtSkel r₁ s₁.pos.loc cv₁ k₁)
    (hr₂ : PartRegion (R.look M) fs s₂.part r₂) (hst₂ : StmtSkel r₂ s₂.pos.loc cv₂ k₂)
    (hsk₂ : s₂.pos.skipped = false) (hlp : cv₁.levelParams = cv₂.levelParams)
    (hty : cv₁.type = cv₂.type) (hs1 : StatusOk (R.look M) fs s₁ k₁ p₁)
    (hs2 : StatusOk (R.look M) fs s₂ k₂ p₂)
    (hn1 : p₁ ≠ .no) (hn2 : p₂ ≠ .no)
    (hpart : ∀ c ∈ (needsGo {} #[] cv₂.type).2, (s₂.part.mod, c) ∈ (R.cap M).2.2)
    (hpend : p₁ = .yes ∨ p₂ = .yes ∨ ∃ w, (w, y, cv₁) ∈ (R.cap M).2.1)
    (hname₂ : cv₂.name = y) :
    ProofAt R.dev (R.rk M) (R.Pr M) (R.rk T) y := by
  obtain ⟨ci, hci, hcicv, hcik, hc₁, hl₁, hsk₁, hcv1y, hsy, hM1, hxM1⟩ :=
    R.ctx_stmt hM hy hs₁ hr₁ hst₁ (hs1.1 hn1)
  obtain rfl : cv₂ = cv₁ := SameStmt.eq ⟨hname₂.trans hcv1y.symm, hty.symm, hlp.symm⟩
  obtain ⟨ci', hci', hcv', hk', -, hfresh⟩ := copy_own (R.facts₀ hT hxT) (R.ownRun hT) hmod₂
    (R.copy_own' (R.trims M) hT hmod₂ hc₂) hl₂ (R.region_own (R.trims M) hT hmod₂ hr₂) hst₂ hsk₂ (hs2.1 hn2) (by rw [hcv1y]; exact hsy)
  rw [hcv1y] at hci'
  have hname : ∀ c ∈ ci.toConstantVal.type.readNames, (R.dev (R.rk M)).rank c < (R.dev (R.rk M)).rank y ∧
      ((R.dev (R.rk M)).context.find? c).isSome = true := fun c hc => by
    have hc' : c ∈ cv₂.type.readNames := by rw [← hcicv]; exact hc
    exact R.rank_lt hM hci hcik hc fun e => hfresh (by rw [hcv1y, ← e]; exact hc')
  refine ⟨ci, ci', hci, by rw [R.dev_rk hT]; exact hci', hcv'.trans hcicv.symm, hcik, hk',
    fun c hc => ⟨⟨T, rfl, hmod₂ ▸ hpart c (readNames_needsGo (by rw [← hcicv]; exact hc))⟩,
      hname c hc⟩, part_resolve hname, ?_⟩
  rcases hpend with h2 | h2 | ⟨w, hw⟩
  · -- the context's copy is a theorem of its module, whose names are its record's reads
    obtain ⟨-, hlt, hrd⟩ := R.ctx_reads hM hci hs₁
    exact .inr ⟨_, cv₂, hlt, R.thm_of_status (R.trims M) hM1 hxM1 rfl hc₁ hl₁ hr₁ hst₁ hsk₁ hcv1y hsy (h2 ▸ hs1),
      hcicv.symm, fun c hc => ⟨hrd c hc, hname c hc⟩⟩
  · -- the view's copy is a theorem of its module
    exact .inr ⟨_, cv₂, hTM, R.thm_of_status (R.trims M) hT hxT hmod₂ hc₂ hl₂ hr₂ hst₂ hsk₂
      (hname₂) hsy (h2 ▸ hs2), hcicv.symm, fun c hc => ⟨⟨T, rfl,
        hmod₂ ▸ hpart c (readNames_needsGo (by rw [← hcicv]; exact hc))⟩, hname c hc⟩⟩
  · -- neither: the statement, inferred over the part below the name
    exact .inl (by rw [hcicv]; exact R.prop_of_pending hM hw)

/-- **The route of a passed pair whose copy is not its reader's** (see the module docstring). -/
theorem route {M : Name} (hM : M ∈ R.names)
    (ih : ∀ M' ∈ R.names, R.rk M' < R.rk M → R.AgreeAll M') {h y : Name}
    (hP : (h, y) ∈ (R.cap M).2.2) (hy : ((R.dev (R.rk M)).context.find? y).isSome = true)
    {s₁ : Spot} (hs₁ : copyOf (R.envOf M) (R.cap M).1 y = some s₁) (hne : s₁.part.mod ≠ h) :
    Route R.dev (R.rk M) (R.Pr M) (R.rk h) y := by
  obtain ⟨hhn, hhr, hxh, s, hs, hsrc, hb⟩ := R.passed_open hM hP hy
  have hss : s₁ = s := Option.some.inj (hs₁.symm.trans hs)
  subst hss
  have hwh := R.facts₀ hhn hxh
  rcases hb with heq | hpub | ⟨v, s₂, hv, hv2, hag⟩
  · exact absurd heq hne
  · obtain ⟨-, hlt, cp, q, hq, hqn, hcpm⟩ := R.pub_loaded hM hhn hpub hne
    have hctx := R.reader_ctx hM hP (hqn ▸ first_of_at hwh hq)
    have hag := R.agree_loaded hhn (ih h hhn hhr) hctx hq hqn
    rw [hcpm] at hag
    exact ⟨R.rk s₁.part.mod, .inr ⟨hctx, hlt, hag⟩, .inl hsrc.symm⟩
  obtain ⟨hc₂, hl₂, hnm₂⟩ := homeView_copy hv hv2
  have hidx := (homeView_index (R.trims M) (R.trims h) hwh (fun _ _ a b => headerFixpoint_unique a b) hv y).1 s₂ hv2
  obtain ⟨_, _, hr⟩ := hwh.reads
  obtain ⟨-, -, -, -, hsize, -⟩ := workerReads_loads hr
  -- an importer copy at the reader: a module of smaller rank, read from where the reader stores it
  have himp : ∀ cp q, (R.w h).reads.index.first[y]? = some cp →
      (R.w h).reads.index.at cp = some q → s₂ = spotOf (R.w h).reads cp q →
      s₂.part.mod ∈ R.names ∧ R.rk s₂.part.mod < R.rk h ∧ R.x s₂.part.mod = #[] ∧
        ((R.dev (R.rk h)).context.find? y).isSome = true ∧
        Agree R.dev (R.rk h) (R.rk s₂.part.mod) y := by
    intro cp q hf hq he
    subst he
    obtain ⟨hT, hlt, hxT⟩ := R.reached_rank hhn (.loaded (at_mod_lt hsize hq))
    have hctx := R.reader_ctx hM hP (by rw [hf]; rfl)
    obtain ⟨s', hs', hsrc'⟩ := R.src_copy hhn hctx
    obtain rfl := Option.some.inj (hs'.symm.trans (R.copyOf_first hf hq))
    exact ⟨hT, hlt, hxT, hctx, .same hsrc'.symm⟩
  rcases hag with hmod | ⟨r₁, cv₁, k₁, r₂, cv₂, k₂, p₁, p₂, hr₁, hst₁, hr₂, hst₂, hsk₂, hlp, hty,
    hs1, hs2, hn1, hn2, hpart, hpend⟩
  · rcases hidx with ⟨hpriv, -⟩ | ⟨cp, q, hf, hq, he⟩
    · exact absurd (hmod.trans (by rw [hpriv])) hne
    · obtain ⟨-, hlt, -, hctx, hagr⟩ := himp cp q hf hq he
      exact ⟨R.rk s₂.part.mod, .inr ⟨hctx, hlt, hagr⟩, .inl (by rw [hsrc, hmod])⟩
  · have hname₂ : cv₂.name = y := (copyAt_stmt_name hc₂ hr₂ hst₂).trans hnm₂
    rcases hidx with ⟨hpriv, -⟩ | ⟨cp, q, hf, hq, he⟩
    · have hmod₂ : s₂.part.mod = h := by rw [hpriv]
      exact ⟨R.rk h, .inl rfl, .inr (R.proofAt_of hM hy hs₁ hhn hxh hhr hmod₂ hc₂ hl₂ hr₁ hst₁ hr₂
        hst₂ hsk₂ hlp hty hs1 hs2 hn1 hn2 hpart hpend hname₂)⟩
    · obtain ⟨hT, hlt, hxT, hctx, hagr⟩ := himp cp q hf hq he
      exact ⟨R.rk s₂.part.mod, .inr ⟨hctx, hlt, hagr⟩, .inr (R.proofAt_of hM hy hs₁ hT hxT
        (Nat.lt_trans hlt hhr) rfl hc₂ hl₂ hr₁ hst₁ hr₂ hst₂ hsk₂ hlp hty hs1 hs2 hn1 hn2 hpart
        hpend hname₂)⟩

/-- **`ImportOk.reads` at every module of the run.** -/
theorem reads_ok : ∀ M ∈ R.names, ∀ d ∈ R.ctx M, ∀ n ∈ declNames d,
    RecordScoped (readsAlike R.dev (R.rk M) ((R.dev (R.rk M)).src n)) d :=
  R.reads_of_routes fun _ hM ih _ _ hP hy _ hs₁ hne => R.route hM ih hP hy hs₁ hne

/-- **The local checks at every module of the development of an accepted run.** -/
theorem localOk (j : Nat) : LocalOk .verified natOpPinSets maxNatSize R.dev j :=
  R.localOk_of (fun _ hM _ _ hh => R.home_rank hM hh) R.reads_ok j

end Run

/-- **Every module of the headers' closure is a node of a closure closed under imports.** -/
theorem hdrClosure_mem {sp : Roots} {fs : FS} {roots : List Name} {C : List Graph.Node}
    (good : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2))
    (hroots : ∀ r ∈ roots, r ∈ C.map (·.1)) (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1))
    {m : Name} (h : Frontend.Olean.HdrClosure sp fs roots m) : m ∈ C.map (·.1) := by
  induction h with
  | root hr => exact hroots _ hr
  | @step a is i _ ha hi ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ih
    obtain rfl := moduleImports_canGive_unique (good e he) ha
    exact edges e he i hi

end ConLeche.Driver.Compose
