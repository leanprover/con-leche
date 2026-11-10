module

public import ConLeche.Verify.Driver.ComposeReads
import ConLeche.Verify.Driver.Clashes
import ConLeche.Verify.Driver.Copies
import ConLeche.Verify.Driver.Provenance

/-!
# The routes: the public-import route

At a module `M` of a run (task #501), a read of `y` by a record of home `h` that passed by the
public-import route (`PubRoute`): the context's copy is of a module `M1` of `h`'s public-import
closure that exports `y`.  Then `M1` is a module of the run of smaller rank than `h`, loaded at
`h`, and `h`'s name index holds a copy of `y` at it (`pub_loaded`).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

/-- **A public path between two modules starts with an exported import of the first.** -/
theorem _root_.ConLeche.Driver.PubReach.first {sp : SearchPath} {fs : FS} {a b : Name}
    (h : PubReach sp fs a b) (hne : a ≠ b) :
    ∃ is i0, ModelIO.CanGive (moduleImports sp a) fs (.ok is) ∧ i0 ∈ is ∧
      i0.isExported = true ∧ PubReach sp fs i0.module b := by
  induction h with
  | refl => exact absurd rfl hne
  | @step b' is i _ hc hi he ih =>
    by_cases hab : a = b'
    · subst hab
      exact ⟨is, i, hc, hi, he, .refl⟩
    · obtain ⟨is0, i0, h1, h2, h3, h4⟩ := ih hab
      exact ⟨is0, i0, h1, h2, h3, .step h4 hc hi he⟩

namespace Run

variable {sp : SearchPath} {fs : FS} {maxNatSize : Nat} (R : Run sp fs maxNatSize)

/-- **The importer's copy of a name is a copy of it on the snapshot.** -/
theorem importerSpot_copyAt {M : Name} (hM : M ∈ R.names) {y : Name} {i : Nat} {s : Spot}
    (h : importerSpot (R.envOf M) y = some (i, s)) : CopyAt sp fs s ∧ s.pos.name = y := by
  obtain ⟨_, _, hrd⟩ := (R.facts M hM).reads
  obtain ⟨-, hfirst, -, -, -, hcopy⟩ := workerIndex_copies hrd
  unfold importerSpot at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cp, hcp, q, hq, h⟩ := h
  cases h
  unfold envOf at hcp hq ⊢
  obtain ⟨q', hq', hn⟩ := hfirst y cp hcp
  rw [hq] at hq'
  cases hq'
  exact ⟨hcopy cp q hq, hn⟩

/-- **The public-import route's module is loaded at the reader**, of smaller rank, with a copy of
the name in the reader's name index. -/
theorem pub_loaded {M : Name} (hM : M ∈ R.names) {h y : Name} (hh : h ∈ R.names) {s₁ : Spot}
    (hpub : PubRoute sp fs (R.envOf M) h y s₁) (hne : s₁.part.mod ≠ h) :
    s₁.part.mod ∈ R.names ∧ R.rk s₁.part.mod < R.rk h ∧
      ∃ cp q, (R.w h).reads.index.at cp = some q ∧ q.name = y ∧
        (R.w h).reads.loads.nameAt cp.mod = s₁.part.mod := by
  -- the public path, at `M`'s load order
  have hwM := R.facts M hM
  obtain ⟨_, _, hrdM⟩ := hwM.reads
  obtain ⟨_, _, hldM, hpubM, hsizeM, -⟩ := workerReads_loads hrdM
  obtain ⟨i, hi, hsp, hix, hp, hexp⟩ := hpub
  unfold envOf at hix hp
  have hp' : (((pubClosures (R.w M).reads.loads)[hi]?).map (·.has i)).getD false = true := by
    rw [← hpubM]; exact hp
  obtain ⟨a, b, ha, hb, hab⟩ := pubClosures_pubReach hldM hp'
  obtain ⟨-, -, -, -, hixM⟩ := headerFixpoint_sound hldM
  have ha' : a = h := by
    rw [hixM h hi hix] at ha; exact (Option.some.inj ha).symm
  subst ha'
  obtain ⟨-, hmod⟩ := importerSpot_loaded hsizeM hsp
  have hb' : s₁.part.mod = b := by
    rw [hmod]; show ((R.w M).reads.loads.order[i]?).getD _ = b; rw [hb]; rfl
  rw [hb'] at hne hexp ⊢
  -- the name, in the exported part of its module
  have hy : ∃ te, PartNames sp fs ⟨b, .exported⟩ te ∧ ∃ q ∈ te.consts, q.name = y := by
    rcases hexp with hl | hex
    · obtain ⟨⟨te, hte, hmem⟩, hn⟩ := R.importerSpot_copyAt hM hsp
      have hpart : s₁.part = ⟨b, .exported⟩ := by
        rw [← hb', ← hl]
      rw [hpart] at hte
      exact ⟨te, hte, _, hmem, hn⟩
    · exact hex
  obtain ⟨te, hte, q, hq, hqn⟩ := hy
  -- the module, loaded at `h`
  have hwh := R.facts a hh
  obtain ⟨_, _, hrdh⟩ := hwh.reads
  obtain ⟨own, hown, hldh, _, hsizeh, -⟩ := workerReads_loads hrdh
  obtain ⟨is, i0, his, hi0, -, hi0b⟩ := hab.first (Ne.symm hne)
  obtain rfl := moduleImports_canGive_unique his (R.rootImports hh hown)
  have hmem := headerFixpoint_complete hldh hi0 hi0b
  have hrank := R.fixpoint_rank hh hown hldh hmem
  refine ⟨hrank.1, hrank.2, ?_⟩
  obtain ⟨j, hj, hjb⟩ := Array.getElem_of_mem hmem
  have hjb' : (R.w a).reads.loads.nameAt j = b := by
    unfold Loads.nameAt; rw [Array.getElem?_eq_getElem hj, hjb]; rfl
  have hjp : j < (R.w a).reads.index.parts.size := by rw [hsizeh]; exact hj
  obtain ⟨hparts, -⟩ := workerReads_index hrdh
  have ht := hparts j _ (Array.getElem?_eq_getElem hjp)
  rw [hjb'] at ht
  obtain ⟨hcopies, -⟩ := workerIndex_copies hrdh
  -- the loaded part holds a copy of the name
  have hin : ∃ q' ∈ (R.w a).reads.index.parts[j].consts, q'.name = y := by
    unfold LoadFlags.level at ht
    split at ht
    · obtain ⟨q', hq', hn⟩ := exported_sub_private (R.facts b hrank.1) hte ht hq
      exact ⟨q', hq', hn.trans hqn⟩
    · rw [partNames_eq ht hte]; exact ⟨q, hq, hqn⟩
  obtain ⟨q', hq', hn⟩ := hin
  obtain ⟨cp, hcpm, hcp⟩ := hcopies j _ q' (Array.getElem?_eq_getElem hjp) hq'
  exact ⟨cp, q', hcp, hn, by rw [hcpm]; exact hjb'⟩

end Run

end ConLeche.Driver.Compose
