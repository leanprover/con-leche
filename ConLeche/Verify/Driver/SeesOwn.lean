module

public import ConLeche.Verify.Driver.Routes
public import ConLeche.OleanInput
public import ConLeche.Verify.IsModelRecords
import ConLeche.Verify.Cached.IotaReadC
import ConLeche.Verify.Inductives.IotaRead
import ConLeche.Verify.OleanInput
import ConLeche.Verify.Driver.Provenance
import ConLeche.Verify.Frontend.Olean.GroupSame
import ConLeche.Verify.Frontend.Olean.Lazy
import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Prefix
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.PinRen
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Driver.Reach

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
private theorem homeMergeFacts {M : Name} {jobs : Nat} {w : WorkerRead} {x : Array ImportRec} (hw : WorkerFacts sp fs M jobs w x) :
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
private theorem home_view_entry {M : Name} {jobs : Nat} {w : WorkerRead} {x : Array ImportRec} (hw : WorkerFacts sp fs M jobs w x)
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

/-! ## A compared challenge's copies (task #619) -/

/-- A hole's or a theorem's record holds the axiom or the theorem of its statement, at a name
other than the quotient's axiom's and the placeholder's. -/
theorem copyStmt?_constants {d : Declaration} {cv : ConstantVal} (h : copyStmt? d = some cv)
    (hq : cv.name ≠ quotSoundName) (hs : cv.name ≠ sorryAxName) :
    ∀ c ∈ d.constants, c = .axiomInfo cv ∨ c = .thmInfo cv := by
  intro c hc
  cases d with
  | axiomDecl cv' =>
    simp only [copyStmt?, Option.some.injEq] at h; subst h
    simp only [Declaration.constants, hq, hs, ↓reduceIte, List.mem_singleton] at hc
    exact .inl hc
  | defnDecl cv' v hint =>
    simp only [copyStmt?] at h
    split at h
    · rename_i hm
      cases h
      have hu : usesSorry v = true := by rw [usesSorry, ← Expr.mentionsAnyConstC_spec]; exact hm
      simp only [Declaration.constants, hu, ↓reduceIte, List.mem_singleton] at hc
      exact .inl hc
    · cases h
  | thmDecl cv' v =>
    simp only [copyStmt?, Option.some.injEq] at h; subst h
    simp only [Declaration.constants, List.mem_singleton] at hc
    exact .inr hc
  | opaqueDecl cv' v =>
    simp only [copyStmt?, Option.some.injEq] at h; subst h
    simp only [Declaration.constants, List.mem_singleton] at hc
    exact .inl hc
  | quotDecl k cv' => simp [copyStmt?] at h
  | indDecl b n => simp [copyStmt?] at h

/-- A definition no hole: its record holds the definition. -/
theorem copyStmt?_defn {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (h : copyStmt? (.defnDecl cv v hint) = none) :
    (Declaration.defnDecl cv v hint).constants = [.defnInfo cv v hint] := by
  simp only [copyStmt?] at h
  split at h
  · cases h
  · rename_i hm
    have hu : usesSorry v = false := by
      rw [usesSorry, ← Expr.mentionsAnyConstC_spec]; simpa using hm
    simp [Declaration.constants, hu]

/-- A block the reader reads (`blockReadB`) is `BlockRead`. -/
theorem blockRead_of_B {block : List ConstantInfo} {nP : Nat}
    (h : blockReadB (.indDecl block nP) = true) : BlockRead nP block := by
  simp only [blockReadB] at h
  split at h
  · cases h
  · rename_i p hp
    simp only [Bool.and_eq_true] at h
    refine ⟨p, hp, (namesNodupGo_spec h.1).1, fun cvTs cs rs hs => ?_⟩
    have h2 := h.2
    rw [hs] at h2
    exact beq_iff_eq.1 h2

/-- **A copy statement, the stored one's up to level names**: the same, or the stored one
renamed. -/
theorem sameCv_cases {cv : ConstantVal} {ci : ConstantInfo}
    (h : Cached.sameCvUpToLevels cv ci.toConstantVal = true) :
    cv = ci.toConstantVal ∨
      (ci.toConstantVal.levelParams.Nodup ∧ cv.levelParams.Nodup ∧
        ci.toConstantVal.levelParams.length = cv.levelParams.length ∧
        cv = ⟨ci.toConstantVal.name, cv.levelParams,
          ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
            (cv.levelParams.map Level.param)⟩) := by
  unfold Cached.sameCvUpToLevels at h
  split at h
  · exact .inl (ConstantVal.eq_of_beqP h)
  · simp only [Bool.and_eq_true, Cached.levelsRenaming, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hl, hn1⟩, hn2⟩, he⟩ := h
    refine .inr ⟨hn2, hn1, hl.symm, ?_⟩
    rw [← ConstantVal.eq_of_beqP he]
    simp [ConstantVal.atLpsC, Expr.instLevelParams_spec]

/-- **An accepted copy**, case by case (`copyCheck`). -/
theorem copyCheck_ok {m : Name} {ld : HeaderLoads} {ix : NameIndex} {r : Reach}
    {owner : Std.HashMap Name Nat} {d : Declaration} (h : copyCheck m ld ix r owner d = .ok ()) :
    recKey d ≠ quotSoundName ∧ recKey d ≠ sorryAxName ∧ basisNamesOk d = true ∧
    ∃ k, owner[recKey d]? = some k ∧
      ((∃ cv ci, copyStmt? d = some cv ∧ ci ∈ declConstants (r.ctx.getD k default) ∧
          ci.toConstantVal.name = recKey d ∧ Cached.sameCvUpToLevels cv ci.toConstantVal = true) ∨
       (∃ cv v hint ci, d = .defnDecl cv v hint ∧ copyStmt? d = none ∧
          ci ∈ declConstants (r.ctx.getD k default) ∧ ci.toConstantVal.name = recKey d ∧
          sameDefUpToLevels (.defnInfo cv v hint) ci = true) ∨
       (copyRecEq d (r.ctx.getD k default) = true ∧ blockReadB d = true ∧
          copyReadsB owner r d = true)) := by
  unfold copyCheck at h
  simp only at h
  split at h
  · cases h
  rename_i hqs
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hqs
  split at h
  · cases h
  rename_i hb
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hb
  refine ⟨hqs.1, hqs.2, by simpa using hb, ?_⟩
  split at h
  · cases h
  rename_i k hk
  refine ⟨k, hk, ?_⟩
  have hfind : ∀ ci, (declConstants (r.ctx.getD k default)).find?
      (·.toConstantVal.name == recKey d) = some ci →
      ci ∈ declConstants (r.ctx.getD k default) ∧ ci.toConstantVal.name = recKey d :=
    fun ci hci => ⟨List.mem_of_find?_eq_some hci, by simpa using List.find?_some hci⟩
  split at h
  · rename_i cv ci hcs hci
    split at h
    · rename_i hsame
      obtain ⟨hm, hn⟩ := hfind ci hci
      exact .inl ⟨cv, ci, hcs, hm, hn, hsame⟩
    · cases h
  · rename_i cv v hint ci hcs hci
    split at h
    · rename_i hsame
      obtain ⟨hm, hn⟩ := hfind ci hci
      exact .inr (.inl ⟨cv, v, hint, ci, rfl, hcs, hm, hn, hsame⟩)
    · cases h
  · split at h
    · rename_i hb2
      simp only [Bool.and_eq_true] at hb2
      exact .inr (.inr ⟨hb2.1.1, hb2.1.2, hb2.2⟩)
    · cases h
  · cases h
  · cases h

/-- A `forM` over `Except` that succeeds succeeds on each element. -/
theorem forM_except_ok {α ε : Type} {f : α → Except ε Unit} :
    ∀ {l : List α}, l.forM f = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, a, ha => by simp at ha
  | b :: l, h, a, ha => by
    simp only [List.forM] at h
    cases hb : f b with
    | error e => rw [hb] at h; cases h
    | ok u =>
      rw [hb] at h
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hb
      · exact forM_except_ok h a ha

/-- A copy's name, by its statement. -/
theorem recKey_of_copyStmt {d : Declaration} {cv : ConstantVal} (h : copyStmt? d = some cv) :
    recKey d = cv.name := by
  cases d with
  | axiomDecl cv' => cases h; rfl
  | defnDecl cv' v hint =>
    simp only [copyStmt?] at h
    split at h
    · cases h; rfl
    · cases h
  | thmDecl cv' v => cases h; rfl
  | opaqueDecl cv' v => cases h; rfl
  | quotDecl k cv' => cases h
  | indDecl b n => cases h

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
    simp only [recsOf]
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

/-- **A module's constants, stored**, at any imports added (task #619): by an own record, or, at a
compared challenge, by the context's constant its copy is (`copyCheck`), the same constant or one
of its statement at other level-parameter names (`RenamedAs`). -/
theorem own_covers_x {M : Name} (hM : M ∈ R.names) {c : ConstantInfo}
    (hc : moduleConstants (R.look M) fs M c) :
    (∃ c' ∈ constantsOf (R.dev (R.rk M)).decls, StoredAs c' c) ∨
    ∃ ci, ci ∈ (streamEnv (R.w M).reach.ctx.toList).consts ∧ ci.name = c.name ∧
      ((StoredAs ci c ∧ ∃ f : Name → Option ConstantInfo,
          (∀ n c', f n = some c' → c' ∈ (streamEnv (R.w M).reach.ctx.toList).consts ∧
            c'.name = n) ∧
          ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules → RecReads f ci) ∨
        RenamedAs ci c) := by
  obtain ⟨f, d0, e, hf, hd0, he, hc⟩ := hc
  have hw := R.facts M hM
  obtain ⟨e', he', hst⟩ := home_view_entry hw ⟨f, hf, hd0⟩ he (entryConstants_safe hc).1
  obtain ⟨d, hd, hd'⟩ := covered_of_merged (homeMergeFacts hw) he' hst hc
  by_cases hown : d ∈ ownRecs (R.x M) (R.w M).reads.index (R.w M).emitted
  · left
    have hown' : d ∈ (R.w M).own.toList := by
      rw [hw.own]
      simp only [recsOf]
      exact (Frontend.hoistNatOpGround_perm _ _).mem_iff.2 (Array.mem_toList_iff.2 hown)
    let F := fillOf (R.look M) fs #[⟨M, (R.w M).home.frontier⟩]
    have hmem : fillDecl F d ∈ ownDecls (R.look M) fs M (R.w M) := List.mem_map_of_mem hown'
    have hbn : basisNamesOk (fillDecl F d) = basisNamesOk d := by cases d <;> rfl
    have hrec : (fillDecl F d).constants = d.constants := by cases d <;> rfl
    obtain ⟨c', hc', hst⟩ := hd' (hbn ▸ declsRun_basisNamesOk (R.run M hM) _ hmem)
    refine ⟨c', ?_, hst⟩
    rw [R.dev_rk hM]
    exact mem_constantsOf.2 ⟨_, hmem, hrec ▸ hc'⟩
  · right
    have hxe : (R.x M).isEmpty = false := by
      cases hxe : (R.x M).isEmpty
      · rfl
      · exact absurd (by simp [ownRecs, hxe, hd]) hown
    have hcopy : d ∈ (copyRecs (R.x M) (R.w M).reads.index (R.w M).emitted).toList := by
      simp only [ownRecs, hxe, Bool.false_eq_true, ↓reduceIte, Array.mem_filter, hd, true_and,
        Bool.not_eq_true'] at hown
      simp only [copyRecs, hxe, Bool.false_eq_true, ↓reduceIte, Array.toList_filter,
        List.mem_filter, Array.mem_toList_iff, hd, true_and]
      simpa using hown
    have hcc := forM_except_ok hw.copies d hcopy
    obtain ⟨hq, hs, hb, k, hk, hcase⟩ := copyCheck_ok hcc
    obtain ⟨c', hc', hst'⟩ := hd' hb
    obtain ⟨hlt, -⟩ := ownerMap_spec hk
    have hectx : (R.w M).reach.ctx.getD k default ∈ (R.w M).reach.ctx.toList := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    have hin : ∀ ci, ci ∈ declConstants ((R.w M).reach.ctx.getD k default) →
        ci ∈ (streamEnv (R.w M).reach.ctx.toList).consts := fun ci hci =>
      (mem_streamEnv_consts _ _).2 (.inl ⟨_, hectx, hci⟩)
    have hcv : c.toConstantVal = c'.toConstantVal := hst'.1.symm
    rcases hcase with ⟨cv, ci, hcs, hci, hcin, hsame⟩ | ⟨cv, v, hint, ci, rfl, hcs, hci, hcin,
      hsame⟩ | ⟨heq, hbr⟩
    · -- a hole or a theorem: by its statement
      have hkey := recKey_of_copyStmt hcs
      have hc'k := copyStmt?_constants hcs (hkey ▸ hq) (hkey ▸ hs) c' hc'
      have hcc' : c.toConstantVal = cv := by rcases hc'k with rfl | rfl <;> exact hcv
      -- `c` is no definition, recursor or constructor (`c'` is none)
      have hnd : ∀ cv₁ v₁ h₁, c ≠ .defnInfo cv₁ v₁ h₁ := by
        intro cv₁ v₁ h₁ hc1
        have := hst'.2.1 cv₁ v₁ h₁ hc1
        rcases hc'k with rfl | rfl <;> rw [hc1] at this <;> cases this
      have hnr : ∀ cv₁ mI rP isK rules, c ≠ .recInfo cv₁ mI rP isK rules := by
        intro cv₁ mI rP isK rules hc1
        obtain ⟨_, _, h1, -⟩ := hst'.2.2.1 cv₁ mI rP isK rules hc1
        rcases hc'k with rfl | rfl <;> cases h1
      have hnc : ∀ cvj cnP nF T, c ≠ .ctorInfo cvj cnP nF T := by
        intro cvj cnP nF T hc1
        obtain ⟨_, _, h1⟩ := hst'.2.2.2 cvj cnP nF T hc1
        rcases hc'k with rfl | rfl <;> cases h1
      have hname : ci.name = c.name := by
        show ci.toConstantVal.name = c.toConstantVal.name
        rw [hcin, hkey, hcc']
      refine ⟨ci, hin ci hci, hname, ?_⟩
      rcases sameCv_cases hsame with heq | ⟨hn1, hn2, hlen, heq⟩
      · exact .inl ⟨⟨heq ▸ hcc'.symm, fun a b h e => absurd e (hnd a b h),
          fun a b c d e f => absurd f (hnr a b c d e), fun a b c d e => absurd e (hnc a b c d)⟩,
          fun _ => none, fun _ _ h => by simp at h, fun a b c d e f => absurd f (hnr a b c d e)⟩
      · refine .inr ⟨hn1, hcc' ▸ hn2, hcc' ▸ hlen, hname.symm, ?_,
          fun a b h e => absurd e (hnd a b h), hnr, hnc⟩
        rw [hcc']
        exact congrArg ConstantVal.type heq
    · -- a definition: the loaded one, renamed or not
      rw [copyStmt?_defn hcs, List.mem_singleton] at hc'
      subst hc'
      have hname : ci.name = c.name := by
        show ci.toConstantVal.name = c.toConstantVal.name
        rw [hcin, hcv]; rfl
      refine ⟨ci, hin ci hci, hname, ?_⟩
      unfold sameDefUpToLevels at hsame
      simp only at hsame
      split at hsame
      · refine .inl ⟨(ConstantInfo.eq_of_beqP hsame).symm ▸ hst', fun _ => none,
          fun _ _ h => by simp at h, fun cv₁ mI rP isK rules hc1 => ?_⟩
        obtain ⟨_, _, h1, -⟩ := hst'.2.2.1 cv₁ mI rP isK rules hc1
        cases h1
      · simp only [Bool.and_eq_true, Cached.levelsRenaming, beq_iff_eq, decide_eq_true_eq] at hsame
        obtain ⟨⟨⟨hl, hn1⟩, hn2⟩, he⟩ := hsame
        have he' := ConstantInfo.eq_of_beqP he
        cases ci with
        | defnInfo cv' v' h' =>
          simp only [ConstantInfo.atLpsC, ConstantInfo.defnInfo.injEq] at he'
          obtain ⟨hcv', hv', rfl⟩ := he'
          have hcvc : c.toConstantVal = cv := hcv
          refine .inr ⟨hn2, hcvc ▸ hn1, hcvc ▸ hl.symm, hname.symm, ?_, ?_, ?_, ?_⟩
          · rw [hcvc, ← hcv']
            simp [ConstantVal.atLpsC, Expr.instLevelParams_spec]
            rfl
          · intro cv₁ v₁ h₁ hc1
            have := hst'.2.1 cv₁ v₁ h₁ hc1
            rw [hc1] at this
            cases this
            refine ⟨cv', v', rfl, ?_⟩
            rw [← hv', Expr.instLevelParams_spec, hcv]
          · intro cv₁ mI rP isK rules hc1
            obtain ⟨_, _, h1, -⟩ := hst'.2.2.1 cv₁ mI rP isK rules hc1
            cases h1
          · intro cvj cnP nF T hc1
            obtain ⟨_, _, h1⟩ := hst'.2.2.2 cvj cnP nF T hc1
            cases h1
        | _ => simp [ConstantInfo.atLpsC] at he'
    · -- an inductive block: the context's record itself
      cases d with
      | indDecl block nP =>
        cases hE : (R.w M).reach.ctx.getD k default with
        | indDecl block' nP' =>
          rw [hE] at heq hin
          simp only [copyRecEq, Bool.and_eq_true, beq_iff_eq] at heq
          obtain ⟨rfl, hbl⟩ := heq
          obtain rfl := eq_of_listBeqBy (fun a b h => ConstantInfo.eq_of_beqP h) hbl
          obtain ⟨ci, hci, hst⟩ := records_stored (fun b n h => by
            cases h; exact blockRead_of_B hbr.1) c' hc'
          have hst2 := hst.trans hst'
          -- the context's constants, read through the owner map
          have hsound : ∀ n c'', ctxConst (ownerMap (R.w M).reach.ctx) (R.w M).reach n = some c'' →
              c'' ∈ (streamEnv (R.w M).reach.ctx.toList).consts ∧ c''.name = n := by
            intro n c'' h
            unfold ctxConst at h
            split at h
            · next j hj =>
              obtain ⟨hlt', -⟩ := ownerMap_spec hj
              have hm : (R.w M).reach.ctx.getD j default ∈ (R.w M).reach.ctx.toList := by
                simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt']
              have h2 := List.find?_some h
              simp only [beq_iff_eq] at h2
              exact ⟨(mem_streamEnv_consts _ _).2 (.inl ⟨_, hm, List.mem_of_find?_eq_some h⟩), h2⟩
            · exact nomatch h
          refine ⟨ci, hin ci hci, ?_, .inl ⟨hst2, _, hsound, fun cv₁ mI rP isK rules hc1 => ?_⟩⟩
          · show ci.toConstantVal.name = c.toConstantVal.name
            rw [hst2.1]
          · obtain ⟨_, _, hci1, -⟩ := hst2.2.2.1 cv₁ mI rP isK rules hc1
            have hcr := hbr.2
            cases hp : readBlock nP block with
            | error e => simp [copyReadsB, hp] at hcr
            | ok p =>
              simp only [copyReadsB, hp] at hcr
              cases hb : Cached.blockReadsOkC (ctxConst (ownerMap (R.w M).reach.ctx) (R.w M).reach)
                p with
              | error e => simp [hb] at hcr
              | ok u =>
                have hmemB : ci ∈ blockConstants p := by
                  simpa [declConstants, hp] using hci
                rw [Cached.blockReadsOkC_eq] at hb
                cases u
                exact blockReadsOk_reads hb ci (Cached.blockConstants_rec hmemB hci1)
        | _ => rw [hE] at heq; simp [copyRecEq] at heq
      | _ => simp [copyRecEq] at heq

end Run

end ConLeche.Driver.Compose
