module

public import ConLeche.Verify.Driver.Routes
public import ConLeche.OleanInput
public import ConLeche.Verify.IsModelRecords
import ConLeche.Verify.OleanInput
import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Frontend.Olean.GroupSame
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Prefix
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.PinRen

/-!
# A module's constants are its worker's own records (task #618)

Every constant of a module's private part (`moduleConstants`) is stored by a record of its
worker's own records (`Run.own_covers`, `StoredAs`): the worker's merge of its home's constants
holds each under its name, and the emission covers it (`covered_of_merged`, as the merged read's
`readOleansAt_covers`).  A constant of any part of a module of the run is stored in the module's
own environment under its name (`Run.part_own`): a constant of the exported or the server part
has the name of a private one (`part_behind`, the home's check of its views).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : Roots} {fs : FS} {maxNatSize : Nat}

/-! ## The constants of a stored constant, by name -/

/-- The quotient package's `Quot.sound` is named `Quot.sound`. -/
theorem quotAt_sound_name (cv : ConstantVal) : (quotAt .sound cv).name = quotSoundName := by
  rw [quotAt, ConLeche.Verify.atLps_name]
  decide

/-- **A stored constant with constants is kept, and no hole.** -/
theorem entryConstants_safe {x : CEntryF Name Expr} {c : ConstantInfo} (h : c ∈ entryConstants x) :
    x.kind.skipped = false ∧ ¬(x.kind.tag = 0 ∧ x.name = sorryAxName) := by
  rcases x with ⟨n, l, t, k⟩
  cases k with
  | ax u =>
    cases u
    · refine ⟨rfl, fun ⟨_, hn⟩ => ?_⟩
      simp only at hn
      subst hn
      simp [entryConstants, declOfEntry, Declaration.constants, CEntryF.cv,
        show sorryAxName ≠ quotSoundName by decide] at h
    · simp [entryConstants, declOfEntry] at h
  | defn v hh s =>
    by_cases hs : s = "safe"
    · subst hs; exact ⟨rfl, by simp [CKindF.tag]⟩
    · simp [entryConstants, declOfEntry, hs] at h
  | opaq v u => cases u <;> simp_all [entryConstants, declOfEntry, CKindF.skipped, CKindF.tag]
  | induct _ _ _ _ _ _ u _ => cases u <;> simp_all [entryConstants, declOfEntry, CKindF.skipped, CKindF.tag]
  | ctor _ _ _ _ u => cases u <;> simp_all [entryConstants, declOfEntry, CKindF.skipped, CKindF.tag]
  | recur _ _ _ _ _ _ _ u => cases u <;> simp_all [entryConstants, declOfEntry, CKindF.skipped, CKindF.tag]
  | thm => exact ⟨rfl, by simp [CKindF.tag]⟩
  | quot => exact ⟨rfl, by simp [CKindF.tag]⟩

/-- **Outside the quotient package, a stored constant's constants have its name.** -/
theorem entryConstants_name {x : CEntryF Name Expr} {c : ConstantInfo} (h : c ∈ entryConstants x)
    (ht : x.kind.tag ≠ 4) : c.name = x.name := by
  rcases x with ⟨n, l, t, k⟩
  cases k with
  | ax u =>
    cases u
    · simp only [entryConstants, declOfEntry, Option.map_some, Option.getD_some,
        Declaration.constants, CEntryF.cv] at h
      split at h
      · rename_i hq
        rw [List.mem_singleton] at h
        subst h
        rw [quotAt_sound_name]; exact hq.symm
      · split at h
        · cases h
        · rw [List.mem_singleton] at h; subst h; rfl
    · simp [entryConstants, declOfEntry] at h
  | defn v hh s =>
    by_cases hs : s = "safe"
    · subst hs
      simp only [entryConstants, declOfEntry, Option.map_some, Option.getD_some,
        Declaration.constants, CEntryF.cv] at h
      split at h <;> (rw [List.mem_singleton] at h; subst h; rfl)
    · simp [entryConstants, declOfEntry, hs] at h
  | opaq v u =>
    cases u
    · simp only [entryConstants, declOfEntry, Option.map_some, Option.getD_some,
        Declaration.constants, CEntryF.cv, List.mem_singleton] at h
      subst h; rfl
    · simp [entryConstants, declOfEntry] at h
  | thm v all =>
    simp only [entryConstants, declOfEntry, Option.map_some, Option.getD_some,
      Declaration.constants, CEntryF.cv, List.mem_singleton] at h
    subst h; rfl
  | quot q => simp [CKindF.tag] at ht
  | induct _ _ _ _ _ _ u _ =>
    cases u
    · simp only [entryConstants, List.mem_singleton] at h; subst h; rfl
    · simp [entryConstants, declOfEntry] at h
  | ctor _ _ _ _ u =>
    cases u
    · simp only [entryConstants, List.mem_singleton] at h; subst h; rfl
    · simp [entryConstants, declOfEntry] at h
  | recur _ _ _ _ _ _ _ u =>
    cases u
    · simp only [entryConstants, List.mem_singleton] at h; subst h; rfl
    · simp [entryConstants, declOfEntry] at h

/-- **A kept stored constant outside the quotient package, and no hole, has a constant of its
name.** -/
theorem entryConstants_exists {x : CEntryF Name Expr} (hs : x.kind.skipped = false)
    (ht : x.kind.tag ≠ 4) (hsy : ¬(x.kind.tag = 0 ∧ x.name = sorryAxName)) :
    ∃ c ∈ entryConstants x, c.name = x.name := by
  suffices hne : entryConstants x ≠ [] by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨c, hc, entryConstants_name hc ht⟩
  rcases x with ⟨n, l, t, k⟩
  cases k with
  | ax u =>
    simp only [CKindF.skipped] at hs
    subst hs
    have hn : n ≠ sorryAxName := fun h => hsy ⟨rfl, h⟩
    simp only [entryConstants, declOfEntry, Option.map_some, Option.getD_some,
      Declaration.constants, CEntryF.cv]
    split <;> simp_all
  | defn v hh s =>
    simp only [CKindF.skipped, bne_eq_false_iff_eq] at hs
    subst hs
    simp only [entryConstants, declOfEntry, Option.map_some, Option.getD_some,
      Declaration.constants]
    split <;> simp
  | opaq v u =>
    simp only [CKindF.skipped] at hs; subst hs
    simp [entryConstants, declOfEntry, Declaration.constants]
  | thm => simp [entryConstants, declOfEntry, Declaration.constants]
  | quot => simp [CKindF.tag] at ht
  | induct _ _ _ _ _ _ u _ => simp only [CKindF.skipped] at hs; subst hs; simp [entryConstants]
  | ctor _ _ _ _ u => simp only [CKindF.skipped] at hs; subst hs; simp [entryConstants]
  | recur _ _ _ _ _ _ _ u => simp only [CKindF.skipped] at hs; subst hs; simp [entryConstants]

/-- Two quotient constants of one kind and statement have the same constants. -/
theorem entryConstants_quot {x y : CEntryF Name Expr} {q : String} (hx : x.kind = .quot q)
    (hy : y.kind = .quot q) (hcv : x.cv = y.cv) : entryConstants x = entryConstants y := by
  rcases x with ⟨n, l, t, k⟩
  rcases y with ⟨n', l', t', k'⟩
  simp only at hx hy
  subst hx hy
  simp only [CEntryF.cv, ConstantVal.mk.injEq] at hcv
  obtain ⟨rfl, rfl, rfl⟩ := hcv
  rfl

/-! ## The merge's coverage -/

/-- **A constant of a merged stored constant is covered by the emission** (the merged read's
argument, `readOleansAt_covers`). -/
private theorem covered_of_merged {mg : Merged} {ds : Array Declaration} (F : MergeFacts mg ds)
    {c : CEntryF Name Expr} {e' : CEntry} (he : mg.map[c.name]? = some e')
    (hst : EntryStands e' c) {r : ConstantInfo} (hrc : r ∈ entryConstants c) : CoveredBy ds r := by
  by_cases ht : c.kind.tag < 5
  · exact covers_entry F he hst ht hrc
  · have hec : e'.toCEntryF = c := by
      rcases hst with hec | ⟨-, -, hc2⟩
      · exact hec
      · exfalso; apply ht
        rcases hc2 with hc2 | hc2 <;> rw [hc2] <;> decide
    subst hec
    obtain ⟨d', hd', c', hc', hst'⟩ := covers_block F he (by omega) hrc
    exact ⟨d', hd', fun _ => ⟨c', hc', hst'⟩⟩

/-- **The home's merge is a merge of its emission.** -/
private theorem homeMergeFacts {M : Name} {jobs : Nat} {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w) :
    MergeFacts (homeMerged w) w.emitted := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hN, hO, hb, hem, -⟩ := home_records hw
  have hnd : (homeMerged w).order.toList.Nodup := by
    obtain ⟨hoR, -⟩ := mergedOfList_firsts (w.home.constants.toList.filter (!·.skipped)) {} []
      (by simp) (by simp)
    have hoR' : (homeMerged w).order.toList =
        (firstsGo [] (w.home.constants.toList.filter (!·.skipped))).map (·.name) := hoR
    rw [hoR']
    exact firstsGo_nodup _ [] (by simp)
  exact ⟨hN, hO, hnd, hb, hem⟩

/-- **A kept constant of a module's private view has its merged copy** in its worker's home's
merge, standing for it. -/
private theorem home_view_entry {M : Name} {jobs : Nat} {w : WorkerRead} (hw : WorkerFacts sp fs M jobs w)
    {d : ModDecoded} (hv : ViewOf sp fs M d) {e : CEntryF Name Expr} (he : e ∈ d.constants)
    (hsk : e.kind.skipped = false) :
    ∃ e', (homeMerged w).map[e.name]? = some e' ∧ EntryStands e' e := by
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk0, hskels, -, -, -, -, -, -, -, hown⟩ :=
    home_records hw
  obtain ⟨f', hf', hview⟩ := hv
  obtain rfl := readFiles_unique hf hf'
  obtain ⟨sk', hsk', hspec⟩ := view_parts hreg hview
  rw [hsk0] at hsk'
  cases hsk'
  obtain ⟨loc, hloc, hcs⟩ := mapM_mem_inv hspec (by simpa using he)
  obtain ⟨s, hs1, hs2⟩ := constSpec_parts hcs
  have hss : s.kind.skipped = false := by rw [(CEntryF.mapM_parts hs2).2.2.2.2]; exact hsk
  obtain ⟨E, e₁, hE, he₁, hee⟩ := hown loc s hloc hs1 hss
  obtain ⟨hn, hlp, hty, -⟩ := lazyEntry_of_spec hs2 hE
  rw [hn] at he₁
  refine ⟨e₁, he₁, ?_⟩
  by_cases h2 : e.kind.tag = 2
  · refine .inr ⟨?_, ?_, .inl h2⟩
    · simp only [CEntryF.cv]; rw [hee, hn, hlp, hty]
    · rw [show e₁.kind = e₁.toCEntryF.kind from rfl, hee, (lazyEntry_kind hE).2,
        (CEntryF.mapM_parts hs2).2.2.2.1, h2]
  · exact .inl (hee.trans (lazyEntry_eq_of_spec hs2 hE h2))

/-! ## The private constant behind a part's constant -/

/-- **The private constant behind a constant of any part** of a home: a skeleton of the home's
private part, filtered alike, that it stands for (`Behind`), of its name. -/
private theorem part_behind {h : Name} {f : ModFiles} {r : Region} {a : UInt64} {sk : ModSkel} {l : Loaded}
    {expo : Array Expo} (hf : ModelIO.CanGive (readFiles sp h .private) fs (.ok f))
    (hreg : f.viewRegion .private = some (r, a)) (hsk : moduleSkel r a = some sk)
    (hload : loadAt 0 h f = some l) (hcv : checkViews h f l = .ok expo) {L : OLeanLevel}
    {r1 : Region} {a1 : UInt64} (hreg1 : (f.upTo L).viewRegion L = some (r1, a1)) {skE : ModSkel}
    (hskE : moduleSkel r1 a1 = some skE) {loc1 : Nat} (hloc : loc1 ∈ skE.consts)
    {s1 : CEntryF UInt64 UInt64} (hs1 : constSkel r1 loc1 = some s1) {n : Name}
    (hn1 : nameP r1 s1.name = some n) :
    ∃ loc sP, loc ∈ sk.consts ∧ constSkel r loc = some sP ∧ sP.kind.skipped = s1.kind.skipped ∧
      Behind r1 loc1 r loc sP ∧ nameP r sP.name = some n := by
  -- where the part's region is the private one
  have hrefl : r1 = r → a1 = a → ∃ loc sP, loc ∈ sk.consts ∧ constSkel r loc = some sP ∧
      sP.kind.skipped = s1.kind.skipped ∧ Behind r1 loc1 r loc sP ∧ nameP r sP.name = some n := by
    rintro rfl rfl
    rw [hsk] at hskE
    cases hskE
    exact ⟨loc1, s1, hloc, hs1, rfl, Behind.refl _ _ _, hn1⟩
  obtain ⟨_, _, hf'⟩ := hf
  obtain ⟨loc0, b, ex, -, -, -, hex, hpriv, hclassic⟩ := readFiles_ok hf'
  cases hm : ModFiles.isModule { exported := ex } with
  | false =>
    obtain ⟨-, -, rfl⟩ := hclassic rfl hm
    have hreg' : ModFiles.viewRegion { exported := ex } .private =
        some (Region.single ex, ex.moduleDataAddr) := by simp [ModFiles.viewRegion, hm]
    rw [hreg] at hreg'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg')
    cases L <;> simp [ModFiles.upTo, ModFiles.viewRegion, hm] at hreg1 <;>
      exact hrefl hreg1.1.symm hreg1.2.symm
  | true =>
    obtain ⟨bs, bp, sv, p, -, -, -, -, rfl⟩ := hpriv rfl hm
    have hm' : ModFiles.isModule ⟨ex, some sv, some p⟩ = true := hm
    obtain ⟨r3, hr3, hexpo⟩ := checkViews_expo hcv hm' rfl rfl
    obtain ⟨r3', ex', hr3', hexpoS⟩ := checkViews_server hcv hm' rfl rfl
    rw [hr3] at hr3'
    obtain rfl := Except.ok.inj hr3'
    have hreg3 : (ModFiles.viewRegion ⟨ex, some sv, some p⟩ .private) =
        some (r3, p.moduleDataAddr) := by
      simp [ModFiles.viewRegion, hm', hr3, Except.toOption, bind, Option.bind, pure]
    rw [hreg] at hreg3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg3)
    obtain ⟨hrshape, ho1, ho2⟩ := ofParts_three hr3
    cases L with
    | «private» =>
      simp only [ModFiles.upTo] at hreg1
      rw [hreg] at hreg1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg1)
      exact hrefl rfl rfl
    | exported =>
      simp only [ModFiles.upTo, ModFiles.viewRegion, Option.some.injEq, Prod.mk.injEq] at hreg1
      obtain ⟨rfl, rfl⟩ := hreg1
      have hsub : Region.Sub (Region.single ex) r ex.bytes.size := by
        rw [hrshape]
        exact Region.Sub.trans (Region.Sub.single_two ex sv ho1)
          (Region.Sub.two_three ex sv p ho1 ho2) (by simp)
      exact behind_sub hsub hreg hsk hload hexpo hskE hloc hs1 hn1
    | server =>
      have hm2 : ModFiles.isModule { exported := ex, server := some sv } = true := hm
      cases hr2 : Region.ofParts #[ex, sv] with
      | error e =>
        simp [ModFiles.upTo, ModFiles.viewRegion, hm2, hr2, Except.toOption, bind,
          Option.bind] at hreg1
      | ok r2 =>
      have hreg2 : (ModFiles.upTo ⟨ex, some sv, some p⟩ .server).viewRegion .server =
          some (r2, sv.moduleDataAddr) := by
        simp [ModFiles.upTo, ModFiles.viewRegion, hm2, hr2, Except.toOption, bind, Option.bind,
          pure]
      rw [hreg1] at hreg2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hreg2)
      obtain ⟨hr2shape, -⟩ := ofParts_two hr2
      have hsub : Region.Sub r1 r (ex.bytes ++ sv.bytes).size := by
        rw [hrshape, hr2shape]
        exact Region.Sub.two_three ex sv p ho1 ho2
      exact behind_sub hsub hreg hsk hload hexpoS hskE hloc hs1 hn1

namespace Run

variable (R : Run sp fs maxNatSize)

/-- **What the emission covers is stored by an own record**: the emitted records are the own
records (the hoist moves them), each passing the reserved names' check in the own run. -/
private theorem covered_own {M : Name} (hM : M ∈ R.names) (hx : R.x M = #[]) {c : ConstantInfo}
    (hcov : CoveredBy (R.w M).emitted c) :
    ∃ c' ∈ constantsOf (R.dev (R.rk M)).decls, StoredAs c' c := by
  obtain ⟨d, hd, hd'⟩ := hcov
  have hw := R.facts₀ hM hx
  have hown : d ∈ (R.w M).own.toList := by
    rw [hw.own]
    simp only [recsOf, Array.isEmpty_empty, ↓reduceIte]
    exact (Frontend.hoistNatOpGround_perm _ _).mem_iff.2 (Array.mem_toList_iff.2 hd)
  let F := fillOf (R.look M) fs #[⟨M, (R.w M).home.frontier⟩]
  have hmem : fillDecl F d ∈ ownDecls (R.look M) fs M (R.w M) := List.mem_map_of_mem hown
  have hbn : basisNamesOk (fillDecl F d) = basisNamesOk d := by cases d <;> rfl
  have hrec : (fillDecl F d).constants = d.constants := by cases d <;> rfl
  obtain ⟨c', hc', hst⟩ := hd' (hbn ▸ declsRun_basisNamesOk (R.run M hM) _ hmem)
  refine ⟨c', ?_, hst⟩
  rw [R.dev_rk hM]
  exact mem_constantsOf.2 ⟨_, hmem, hrec ▸ hc'⟩

/-- **A constant of an own record is stored in the module's own environment**, under its name. -/
theorem stored_name {M : Name} (hM : M ∈ R.names) {c : ConstantInfo}
    (hc : c ∈ constantsOf (R.dev (R.rk M)).decls) :
    ((R.dev (R.rk M)).own.find? c.name).isSome = true := by
  obtain ⟨d, hd, hcd⟩ := mem_constantsOf.1 hc
  have hd' : d ∈ ownDecls (R.look M) fs M (R.w M) := by
    rw [R.dev_rk hM] at hd; exact hd
  obtain ⟨ci, hci, hst⟩ := records_stored (declsRun_blockRead (R.run M hM) d hd') c hcd
  have hn : ci.name = c.name := by
    show ci.toConstantVal.name = c.toConstantVal.name
    rw [hst.1]
  rw [← hn]
  exact own_of_decl hd (List.mem_map_of_mem hci)

/-- **A module's constants are stored by its own records.** -/
theorem own_covers {M : Name} (hM : M ∈ R.names) (hx : R.x M = #[]) {c : ConstantInfo}
    (hc : moduleConstants (R.look M) fs M c) :
    ∃ c' ∈ constantsOf (R.dev (R.rk M)).decls, StoredAs c' c := by
  obtain ⟨f, d, e, hf, hd, he, hc⟩ := hc
  have hw := R.facts₀ hM hx
  obtain ⟨e', he', hst⟩ := home_view_entry hw ⟨f, hf, hd⟩ he (entryConstants_safe hc).1
  exact R.covered_own hM hx (covered_of_merged (homeMergeFacts hw) he' hst hc)

/-- **A constant of a part of a module of the run is stored in its own environment.** -/
theorem part_own {M : Name} (hM : M ∈ R.names) (hx : R.x M = #[]) {p : OLeanLevel}
    {c : ConstantInfo} (hc : InModulePart (R.look M) fs M p c) :
    ((R.dev (R.rk M)).own.find? c.name).isSome = true := by
  have hw := R.facts₀ hM hx
  obtain ⟨f', d, e, hf', hd, he, hc⟩ := hc
  obtain ⟨hsafe, hsy⟩ := entryConstants_safe hc
  obtain ⟨f, r, a, sk, skels, hf, hreg, hsk, -, -, hcv, hload, -, -, -, -, hown⟩ :=
    home_records hw
  have F := homeMergeFacts hw
  -- the part's constant at its location
  obtain rfl := partFiles_of_all hf hf'
  rw [← parseView_eq_spec] at hd
  obtain ⟨r1, a1, hv, hp, -⟩ := parseView_some hd
  obtain ⟨-, skE, hskE, -, hcs, -⟩ := parseAt_some hp
  obtain ⟨loc1, hloc1, hc1⟩ := mapM_mem_inv hcs (by simpa using he)
  obtain ⟨s1, hs1, hm1⟩ := constSpec_parts hc1
  obtain ⟨hn1, hl1, ht1, htag1, hsk1⟩ := CEntryF.mapM_parts hm1
  -- the private constant behind it, in the merge
  obtain ⟨loc, sP, hloc, hsP, hskP, hbeh, hnP⟩ :=
    part_behind hf hreg hsk hload hcv hv hskE hloc1 hs1 hn1
  have hsP0 : sP.kind.skipped = false := by rw [hskP, hsk1, hsafe]
  obtain ⟨E, e₁, hE, he₁, hee⟩ := hown loc sP hloc hsP hsP0
  obtain ⟨hnE, hlE, htE⟩ := lazyEntry_stmt hE
  obtain ⟨hskE', htagE⟩ := lazyEntry_kind hE
  have hEn : E.name = e.name := by rw [hnP] at hnE; exact (Option.some.inj hnE).symm
  have hst₁ : EntryStands e₁ E := .inl hee
  rw [← hee] at he₁
  have hmerged : (homeMerged (R.w M)).map[E.name]? = some e₁ := by
    rw [show E.name = e₁.toCEntryF.name by rw [hee]]; exact he₁
  -- a constant of `E` of `c`'s name
  have key : ∃ cp ∈ entryConstants E, cp.name = c.name := by
    obtain ⟨k, hk, hkt, hkq⟩ := kind_names hm1
    have hst : StmtSkel r1 loc1 e.stmt k := ⟨s1, hs1, hn1, hl1, ht1, hk⟩
    by_cases h4 : e.kind.tag = 4
    · cases hq : e.kind with
      | quot q =>
        rcases hbeh with ⟨hsame, -⟩ | hhid
        · obtain ⟨k', hk', -, hq'⟩ := hsame _ _ hst
          rw [hq' q (hkq q hq)] at hk'
          have hEq := lazyEntry_quot hsP hk' hE
          refine ⟨c, ?_, rfl⟩
          rw [entryConstants_quot (y := e) (q := q) (by rw [hEq]) hq (by rw [hEq]; rfl)]
          exact hc
        · obtain ⟨⟨u, hu⟩, -⟩ := hhid _ _ hst
          rw [hkq q hq] at hu; cases hu
      | _ => rw [hq] at h4; simp [CKindF.tag] at h4
    · have hcn : c.name = e.name := entryConstants_name hc h4
      have hEtag : E.kind.tag ≠ 4 ∧ ¬(E.kind.tag = 0 ∧ E.name = sorryAxName) := by
        rcases hbeh with ⟨hsame, -⟩ | hhid
        · obtain ⟨k', ⟨sP', hsP', -, -, -, hk'⟩, htk, -⟩ := hsame _ _ hst
          rw [hsP] at hsP'
          cases hsP'
          have : E.kind.tag = e.kind.tag := by
            rw [htagE, (CKindF.mapM_tag hk').1, htk, hkt]
          rw [this, hEn]; exact ⟨h4, hsy⟩
        · obtain ⟨-, -, -, -, ht3⟩ := hhid _ _ hst
          rw [htagE]
          exact ⟨by omega, fun h => by omega⟩
      obtain ⟨cp, hcp, hcpn⟩ := entryConstants_exists (by rw [hskE', hsP0]) hEtag.1 hEtag.2
      exact ⟨cp, hcp, by rw [hcpn, hEn, hcn]⟩
  obtain ⟨cp, hcp, hcpn⟩ := key
  obtain ⟨c', hc', hst'⟩ := R.covered_own hM hx (covered_of_merged F hmerged hst₁ hcp)
  have hn : c'.name = cp.name := by
    show c'.toConstantVal.name = cp.toConstantVal.name
    rw [hst'.1]
  rw [← hcpn, ← hn]
  exact R.stored_name hM hc'

end Run

end ConLeche.Driver.Compose
