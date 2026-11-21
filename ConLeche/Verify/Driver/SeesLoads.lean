module

public import ConLeche.Verify.Driver.Routes
public import ConLeche.OleanInput
import ConLeche.Verify.Driver.LoadsAll
import ConLeche.Verify.Driver.RouteCtx
import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Driver.Copies
import ConLeche.Verify.Driver.Clashes
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.OleanInput
import ConLeche.Verify.PinRen
import ConLeche.Verify.Cached.Fill

/-!
# What a module sees, in its worker's index (task #618)

A module `M` of an accepted run sees a name `n` as `m'`'s (`Sees`, `ConLeche/OleanInput.lean`)
when its header loads a part of `m'` that holds a constant named `n`.  Every such name is a copy
in `M`'s worker's name index, of the module `m'` (`Run.sees_copy`):

* the header fixpoint loads every module `LoadsAt` derives, whole where some derivation loads it
  whole (`loadsAt_fixpoint`, `ConLeche/Verify/Driver/LoadsAll.lean`);
* a constant of a part has a name position of that part's name table (`readNamePositions_of_view`),
  and a constant of the exported part has the name of one of the private part
  (`exported_sub_private`, the home's check of its views), so the part the fixpoint loads holds it;
* a constant's name is its stored constant's: a quotient constant's is its pin's, which an
  accepted module's own record of it has (`entry_name`: the private constant behind it, by the
  home's check of its views, is an own record, and its check asks it pinned).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : Roots} {fs : FS}

/-- **What a header with imports added loads, at a part** (task #619): `LoadsAt` over a module's
own imports followed by `x`, the private part where some derivation loads it whole, the exported
part where one loads it.  It holds wherever `Loads` does (`loads_toX`), which also asks
an exported part not loaded whole. -/
@[expose] def LoadsX (sp : Roots) (fs : FS) (x : Array ImportRec) (m m' : Name) (p : OLeanLevel) :
    Prop :=
  ∃ d, ViewOf sp fs m d ∧
    match p with
    | .private => LoadsAt sp fs (!d.isModule) (d.imports ++ x) m' true
    | .exported => LoadsAt sp fs (!d.isModule) (d.imports ++ x) m' false
    | .server => False

/-- **What a header with imports added sees** (`Sees` over `LoadsX`). -/
@[expose] def SeesX (sp : Roots) (fs : FS) (x : Array ImportRec) (m n m' : Name) : Prop :=
  ∃ p c, LoadsX sp fs x m m' p ∧ InModulePart sp fs m' p c ∧ c.name = n

/-- What a header loads, it loads with imports added. -/
theorem loadsAt_append {sp : Roots} {fs : FS} {g : Bool} {imps : Array ImportRec} (x : Array ImportRec)
    {m : Name} {b : Bool} (h : LoadsAt sp fs g imps m b) : LoadsAt sp fs g (imps ++ x) m b := by
  induction h with
  | root hi => exact .root (Array.mem_append_left _ hi)
  | step _ hv hi hx ih => exact .step ih hv hi hx

theorem loads_toX {sp : Roots} {fs : FS} (x : Array ImportRec) {m m' : Name} {p : OLeanLevel}
    (h : Loads sp fs m m' p) : LoadsX sp fs x m m' p := by
  obtain ⟨d, hv, hl⟩ := h
  refine ⟨d, hv, ?_⟩
  cases p with
  | «private» => exact loadsAt_append x hl
  | exported => exact loadsAt_append x hl.1
  | server => exact hl.elim

/-- **What a header sees, it sees with imports added.** -/
theorem sees_toX {sp : Roots} {fs : FS} (x : Array ImportRec) {m n m' : Name}
    (h : Sees sp fs m n m') : SeesX sp fs x m n m' := by
  obtain ⟨p, c, hL, hc, hn⟩ := h
  exact ⟨p, c, loads_toX x hL, hc, hn⟩

/-- **A part's name table, from its files**: the table of the view the files hold. -/
theorem partNames_of_files {sp : Roots} {fs : FS} {m : Name} {p : OLeanLevel} {f : ModFiles}
    {t : NamePositions} (hf : ModelIO.CanGive (readFiles sp m p) fs (.ok f))
    (ht : readNamePositions f p = some t) : PartNames sp fs ⟨m, p⟩ t := by
  obtain ⟨hs, hs', h⟩ := hf
  simp only [readFiles, ModelIO.bind_ok] at h
  obtain ⟨y, hs₁, hy, h⟩ := h
  rcases y with e | loc
  · simp at h
  refine ⟨hs, hs', ?_⟩
  simp only [readPartNames, ModelIO.bind_ok]
  refine ⟨.ok loc, hs₁, hy, ?_⟩
  simp only [readPartNamesAt, ModelIO.bind_ok]
  refine ⟨.ok f, hs', h, ?_⟩
  simp [namesOf, ht]

/-- **A decoded view's constant, at its position**: a position of the view's name table holds
its name, and the view's region holds the constant there. -/
theorem view_entry_pos {f : ModFiles} {p : OLeanLevel} {d : ModDecoded}
    (hd : decodeModuleSpec f p = some d) {e : CEntryF Name Expr} (he : e ∈ d.constants) :
    ∃ t q r a, readNamePositions f p = some t ∧ q ∈ t.consts ∧ q.name = e.name ∧
      f.viewRegion p = some (r, a) ∧ entryAt r q.loc = some e := by
  rw [← parseView_eq_spec] at hd
  obtain ⟨t, ht, -, hnames, -, -⟩ := readNamePositions_of_view hd
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem he
  have hlen : t.consts.size = d.constants.size := by
    have := congrArg List.length hnames
    simpa using this
  have hit : i < t.consts.size := by omega
  have hnm : t.consts[i].name = d.constants[i].name := by
    have := congrArg (·[i]?) hnames
    simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hit,
      Array.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at this
    exact this
  have hre := readEntry_of_view hd ht (Array.getElem?_eq_getElem hit)
  rw [Array.getElem?_eq_getElem hi] at hre
  simp only [readEntry] at hre
  obtain ⟨⟨r, a⟩, hreg, hre⟩ := bind_some_left hre
  exact ⟨t, t.consts[i], r, a, ht, Array.getElem_mem hit, hnm, hreg, hre⟩

/-- **The statement and kind of a constant a region holds**, off its skeleton. -/
theorem stmtSkel_of_entry {r : Region} {loc : Nat} {e : CEntryF Name Expr}
    (h : entryAt r loc = some e) :
    ∃ k, StmtSkel r loc e.cv k ∧ ∀ q, e.kind = .quot q → k = .quot q := by
  rw [entryAt_eq] at h
  obtain ⟨s, hs, hm⟩ := constSpec_parts h
  obtain ⟨hn, hl, ht, -, -⟩ := CEntryF.mapM_parts hm
  obtain ⟨k', hk', -, hq⟩ := kind_names hm
  exact ⟨k', ⟨s, hs, hn, hl, ht, hk'⟩, hq⟩

namespace Run

variable (R : Run sp fs)

/-- **A quotient constant of a part of a module of the run is at its pin's name**: the private
constant behind it is an own record, which the module's check asks pinned. -/
theorem quot_name (hl : ∀ M, R.look M = sp) {M : Name} (hx : R.x M = #[])
    (hM : M ∈ R.names) {p : OLeanLevel} {t : NamePositions} (ht : PartNames sp fs ⟨M, p⟩ t)
    {q : NamePosition} (hq : q ∈ t.consts) (hp : p ≠ .server) {f : ModFiles} {r1 : Region}
    {a1 : UInt64} (hf : ModelIO.CanGive (readFiles sp M p) fs (.ok f))
    (hreg : f.viewRegion p = some (r1, a1)) {e : CEntryF Name Expr}
    (he : entryAt r1 q.loc = some e) {qs : String} (hk : e.kind = .quot qs)
    {dq : Declaration} (hdq : declOfEntry e = some dq) :
    ∀ c ∈ dq.constants, c.name = e.name := by
  have hw := R.facts₀ hM hx
  rw [hl M] at hw
  obtain ⟨f0, r, a, sk, skels, hf0, hreg0, hsk, -, -, hcv, hload, hN, hO, hb, hem, hall⟩ :=
    home_records hw
  have hr1 : PartRegion sp fs ⟨M, p⟩ r1 := ⟨f, a1, hf, hreg⟩
  obtain ⟨loc, sP, s1, hloc, hsP, -, -, -, -, hbeh, -⟩ :=
    copy_behind hf0 hreg0 hsk hload hcv (s := ⟨⟨M, p⟩, q⟩) rfl ⟨t, ht, hq⟩ hp hr1
  obtain ⟨k1, hst1, hkq⟩ := stmtSkel_of_entry he
  have hk1 : k1 = .quot qs := hkq qs hk
  subst hk1
  -- the private skeleton behind it: the same statement, a quotient constant of the same kind
  have hstP : StmtSkel r loc e.cv (.quot qs) := by
    rcases hbeh with ⟨hsame, -⟩ | hhid
    · obtain ⟨k', hst', -, hkq'⟩ := hsame e.cv _ hst1
      rw [hkq' qs rfl] at hst'
      exact hst'
    · obtain ⟨⟨u, hu⟩, -⟩ := hhid e.cv _ hst1
      cases hu
  obtain ⟨sP', hsP', -, -, -, hkm⟩ := id hstP
  rw [hsP] at hsP'
  cases hsP'
  have hskp : sP.kind.skipped = false := by
    have := (CKindF.mapM_tag hkm).2
    rw [this]; rfl
  obtain ⟨E, e₁, hE, he₁, he₁E⟩ := hall loc sP hloc hsP hskp
  have hEe : E = e := by
    rw [lazyEntry_quot hsP hstP hE]
    rcases e with ⟨n, l, ty, k⟩
    simp only at hk
    subst hk
    rfl
  subst hEe
  have hsk1 : e₁.skipped = false := by
    simp only [CEntry.skipped]; rw [show e₁.kind = E.kind from by rw [← he₁E]]; rw [hk]; rfl
  have htag : e₁.kind.tag < 5 := by rw [show e₁.kind = E.kind from by rw [← he₁E], hk]; simp [CKindF.tag]
  obtain ⟨p', hp', hpe⟩ := home_entry hN hO hb hem he₁ hsk1 htag
  rw [entryDecl_safe hsk1, he₁E, hdq] at hpe
  obtain rfl := Option.some.inj hpe
  -- the own record is checked pinned
  have hown := emitted_own hw hp'
  have hrun := R.run M hM
  rw [hl M] at hrun
  obtain ⟨kq, hkq2⟩ : ∃ kq, dq = .quotDecl kq E.cv := by
    have := entryDecl_quot (c := e₁) (by rw [entryDecl_safe hsk1, he₁E]; exact hdq)
      (q := qs) (by rw [show e₁.kind = E.kind from by rw [← he₁E], hk])
    obtain ⟨kq, h⟩ := this
    refine ⟨kq, h.trans ?_⟩
    rw [show (⟨e₁.name, e₁.levelParams, e₁.type⟩ : ConstantVal) = E.cv from by
      rw [← he₁E]; rfl]
  subst hkq2
  have hmem : Declaration.quotDecl kq E.cv ∈
      ownDecls sp fs M (R.w M) :=
    List.mem_map.2 ⟨_, hown, rfl⟩
  have hhit := hrun.quot hmem
  intro c hc
  simp only [Declaration.constants, List.mem_singleton] at hc
  subst hc
  exact quotAt_name_of_hit hhit

/-- A constant of a stored constant that is no quotient constant has its name. -/
theorem entryConstants_name {e : CEntryF Name Expr} (hq : ∀ qs, e.kind ≠ .quot qs)
    {c : ConstantInfo} (hc : c ∈ entryConstants e) : c.name = e.name := by
  unfold entryConstants at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc; rfl
  · simp only [List.mem_singleton] at hc; subst hc; rfl
  · simp only [List.mem_singleton] at hc; subst hc; rfl
  · cases hd : declOfEntry e with
    | none => simp [hd] at hc
    | some d =>
      simp only [hd, Option.map_some, Option.getD_some] at hc
      unfold declOfEntry at hd
      split at hd
      all_goals (try (rename_i hk; exact absurd hk (hq _)))
      all_goals cases hd
      all_goals simp only [Declaration.constants] at hc
      all_goals (try split at hc)
      all_goals (try split at hc)
      all_goals first
        | (simp at hc; done)
        | (simp only [List.mem_singleton] at hc; subst hc; rfl)
        | (simp only [List.mem_singleton] at hc; subst hc
           rw [quotAt, ConLeche.Verify.atLps_name]
           rename_i h1
           exact (show (quotPin .sound).name = quotSoundName by decide).trans h1.symm)

/-- **A constant of a part of a module of the run has its stored constant's name.** -/
theorem entry_name (hl : ∀ M, R.look M = sp) {M : Name} (hx : R.x M = #[])
    (hM : M ∈ R.names) {p : OLeanLevel} {t : NamePositions} (ht : PartNames sp fs ⟨M, p⟩ t)
    {q : NamePosition} (hq : q ∈ t.consts) (hp : p ≠ .server) {f : ModFiles} {r1 : Region}
    {a1 : UInt64} (hf : ModelIO.CanGive (readFiles sp M p) fs (.ok f))
    (hreg : f.viewRegion p = some (r1, a1)) {e : CEntryF Name Expr}
    (he : entryAt r1 q.loc = some e) {c : ConstantInfo} (hc : c ∈ entryConstants e) :
    c.name = e.name := by
  by_cases hk : ∃ qs, e.kind = .quot qs
  · obtain ⟨qs, hk⟩ := hk
    have hlow : e.kind.tag < 5 := by rw [hk]; simp [CKindF.tag]
    rw [entryRecords_low hlow] at hc
    cases hdq : declOfEntry e with
    | none => rw [hdq] at hc; cases hc
    | some dq =>
      rw [hdq] at hc
      exact R.quot_name hl hx hM ht hq hp hf hreg he hk hdq c hc
  · exact entryConstants_name (fun qs h => hk ⟨qs, h⟩) hc

/-- **The part a module sees is a loaded part**: the module at some position of its worker's load
order, at the part seen, or the private part where the exported one is seen. -/
theorem sees_at (hl : ∀ M, R.look M = sp) {M m' : Name}
    (hM : M ∈ R.names) {p : OLeanLevel} (h : LoadsX sp fs (R.x M) M m' p) :
    p ≠ .server ∧ ∃ k : Nat, (R.w M).reads.loads.order[k]? = some m' ∧
      (((((R.w M).reads.loads.flags[k]?).getD default).level = p) ∨
        (p = .exported ∧ (((R.w M).reads.loads.flags[k]?).getD default).level = .private)) := by
  obtain ⟨d, hv, hlp⟩ := h
  have hw := R.facts M hM
  rw [hl M] at hw
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨own, hown, hld, -, -, -, -, -⟩ := workerReads_loads hr
  rw [NamePositions.withImports_imports, NamePositions.withImports_isModule] at hld
  obtain ⟨fM, hfM, hdM⟩ := hv
  obtain ⟨ps, hps, hhead, -⟩ := readNamePositions_of_view ((parseView_eq_spec _ _).trans hdM)
  have hown' := readPartNames_of_all hfM hown
  simp only [ModFiles.upTo] at hown'
  rw [hps] at hown'
  obtain rfl := Option.some.inj hown'
  rw [hhead] at hld
  have hlev : ∀ fl : LoadFlags, fl.level = .private ∨ fl.level = .exported := by
    intro fl; unfold LoadFlags.level; split <;> simp
  cases p with
  | «private» =>
    obtain ⟨k, hk, ha⟩ := loadsAt_fixpoint hld hlp
    refine ⟨by decide, k, hk, .inl ?_⟩
    unfold LoadFlags.level; rw [ha rfl]; rfl
  | exported =>
    obtain ⟨k, hk, -⟩ := loadsAt_fixpoint hld hlp
    refine ⟨by decide, k, hk, ?_⟩
    rcases hlev (((R.w M).reads.loads.flags[k]?).getD default) with h' | h'
    · exact .inr ⟨rfl, h'⟩
    · exact .inl h'
  | server => exact hlp.elim

/-- **A module a module loads is a module of the run of smaller rank**, with no import added. -/
theorem loads_rank {M : Name} (hM : M ∈ R.names) {k : Nat} {m' : Name}
    (hk : (R.w M).reads.loads.order[k]? = some m') :
    m' ∈ R.names ∧ R.rk m' < R.rk M ∧ R.x m' = #[] := by
  obtain ⟨_, _, hr⟩ := (R.facts M hM).reads
  obtain ⟨own, hown, hld, -⟩ := workerReads_loads hr
  exact R.fixpoint_rank (R.trims M) hM hown hld (Array.mem_of_getElem? hk)

/-- **A name a module sees is a copy of its worker's index**, of the module it sees it from. -/
theorem sees_copy (hl : ∀ M, R.look M = sp) {M : Name}
    (hM : M ∈ R.names) {n m' : Name} (h : SeesX sp fs (R.x M) M n m') :
    ∃ cp q, (R.w M).reads.index.at cp = some q ∧ q.name = n ∧
      (R.w M).reads.loads.nameAt cp.mod = m' := by
  obtain ⟨p, c, hL, ⟨f, dp, e, hf, hdp, he, hce⟩, rfl⟩ := h
  obtain ⟨hps, k, hk, hlevel⟩ := R.sees_at hl hM hL
  have hw := R.facts M hM
  rw [hl M] at hw
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨own, hown, hld, -, hsize, -, -, -⟩ := workerReads_loads hr
  obtain ⟨hm'R, -, hxm'⟩ := R.loads_rank hM hk
  have hw' := R.facts₀ hm'R hxm'
  rw [hl m'] at hw'
  have hkl : k < (R.w M).reads.index.parts.size := by
    rw [hsize]; exact (Array.getElem?_eq_some_iff.1 hk).1
  obtain ⟨hidx, -⟩ := workerReads_index hr
  have hpart := hidx k _ (Array.getElem?_eq_getElem hkl)
  have hnk : (R.w M).reads.loads.nameAt k = m' := by
    simp only [HeaderLoads.nameAt, hk, Option.getD_some]
  rw [hnk] at hpart
  -- the constant's position in the part it is in
  obtain ⟨tp, q, r1, a1, htp, hq, hqn, hreg1, hent⟩ := view_entry_pos hdp he
  have hpn : PartNames sp fs ⟨m', p⟩ tp := partNames_of_files hf htp
  have hcn : c.name = e.name := R.entry_name hl hxm' hm'R hpn hq hps hf hreg1 hent hce
  -- its name in the loaded part
  obtain ⟨q', hq', hq'n⟩ : ∃ q' ∈ (R.w M).reads.index.parts[k].consts, q'.name = e.name := by
    rcases hlevel with hL' | ⟨rfl, hL'⟩
    · rw [hL'] at hpart
      have := partNames_region hpart (k := ⟨m', p⟩) hf
      rw [htp] at this
      obtain rfl := Option.some.inj this
      exact ⟨q, hq, hqn⟩
    · rw [hL'] at hpart
      obtain ⟨q', hq', hn'⟩ := exported_sub_private hw' hpn hpart hq
      exact ⟨q', hq', hn'.trans hqn⟩
  obtain ⟨hcop, -⟩ := workerIndex_copies hr
  obtain ⟨cp, hcm, hat⟩ := hcop k _ q' (Array.getElem?_eq_getElem hkl) hq'
  exact ⟨cp, q', hat, hq'n.trans hcn.symm, by rw [hcm, hnk]⟩

/-- **A module a module sees is a module of the run of smaller rank**, with no import added. -/
theorem sees_rank (hl : ∀ M, R.look M = sp) {M : Name}
    (hM : M ∈ R.names) {n m' : Name} (h : SeesX sp fs (R.x M) M n m') :
    m' ∈ R.names ∧ R.rk m' < R.rk M ∧ R.x m' = #[] := by
  obtain ⟨p, c, hL, -, -⟩ := h
  obtain ⟨-, k, hk, -⟩ := R.sees_at hl hM hL
  exact R.loads_rank hM hk

end Run

end ConLeche.Driver.Compose
