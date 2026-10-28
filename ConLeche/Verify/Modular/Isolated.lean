module

public import ConLeche.Verify.Modular.IsoRun
public import ConLeche.Verify.Modular.Ghost
import ConLeche.Verify.Modular.Mask
import ConLeche.Verify.Modular.IsoCtx
import ConLeche.Verify.Modular.Local

public section

/-!
# An isolated run's checks are the local checks (task #374)

In isolated mode (`--modular=isolated`) everything around module `M` is
a function of `M`'s own records and the units it reads (`mask slot lv`:
the interfaces of the modules it loads, the private records of those it
loads privately): its context (`isoCtx`), the install and check of its
records from it, the check of its unit (`unitOk` at `isoUView`, the
context's lookup and the loaded interfaces) and its local checks
(`localOkIso`: its levels, and the copies of a name that meet in its
context have one qualified name).  `IsoRunOk` is what such a run
establishes, module by module, about the published units.

The local checks follow through the store run's theorems at the store
of the units (`ghostStore`, `ConLeche/Verify/Modular/Ghost.lean`), which
exists in the proof only:

* `unitOk_congr` — a unit's check reads its context only through the
  lookup and the interfaces of the modules the lookup answers with; so
  the isolated check is the store's (`unitOk_ghost`);
* `keysOk_oneKey` — the isolated duplicates' check gives the store's;
* `IsoRunOk.storeOk` — an isolated run is an isolated install over the
  store of its units (`IsoStoreOk`), hence (`IsoStoreOk.localOk`)
* **`IsoRunOk.localOk`** — every module of the development it stands for
  (`isoRunDev`: contexts built from the units, own environments over
  them) passes the local checks, the hypothesis of the modular capstones.
-/

namespace ConLeche.Cached.Mod

open ConLeche ConLeche.Modular

variable {mode : CheckMode}

/-! ## A unit's check reads the lookup and the loaded interfaces -/

/-- **Two views of a context that answer alike**: the same lookup, and the
same interface for every module the lookup answers with. -/
structure UAgree (U₁ U₂ : UView) : Prop where
  look : U₁.look = U₂.look
  iface : ∀ d h' j' c, U₁.look d = some (h', j', c) → U₁.iface h' = U₂.iface h'

/-- Two own indices that a unit's check reads alike. -/
structure FeAgree (fe₁ fe₂ : FEnv) : Prop where
  idx : fe₁.idx = fe₂.idx
  vb : fe₁.visibleBelow = fe₂.visibleBelow
  env : fe₁.env = fe₂.env

theorem target_congr {U₁ U₂ : UView} {fe₁ fe₂ : FEnv} (hU : UAgree U₁ U₂) (hf : FeAgree fe₁ fe₂)
    (h : Nat) (d : Name) : target h fe₁ U₁ d = target h fe₂ U₂ d := by
  unfold target; rw [hf.idx, hf.vb, hU.look]

/-- A target of another module is the lookup's. -/
theorem target_look {U : UView} {fe : FEnv} {h : Nat} {d : Name} {h' j' : Nat}
    (ht : target h fe U d = some (h', j')) (hne : h' ≠ h) : ∃ c, U.look d = some (h', j', c) := by
  unfold target at ht
  split at ht
  · split at ht
    · cases ht; exact absurd rfl hne
    · cases ht
  · cases hl : U.look d with
    | none => rw [hl] at ht; cases ht
    | some x =>
      obtain ⟨a, b, c⟩ := x
      rw [hl] at ht
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact ⟨c, rfl⟩

section congr
variable {U₁ U₂ : UView} {fe₁ fe₂ : FEnv} (hU : UAgree U₁ U₂) (hf : FeAgree fe₁ fe₂)
include hU hf

theorem read2Ok_congr (h : Nat) (d : Name) : read2Ok U₁ h fe₁ d = read2Ok U₂ h fe₂ d := by
  unfold read2Ok; rw [target_congr hU hf]

theorem full2Ok_congr (h : Nat) (s : ModSlot) (w : Want) (d : Name) :
    full2Ok U₁ h fe₁ s w d = full2Ok U₂ h fe₂ s w d := by
  unfold full2Ok; rw [target_congr hU hf, hU.look]

theorem read1Ok_congr (h : Nat) (s : ModSlot) (G : Array (Nat × UInt8)) (d : Name) :
    read1Ok U₁ h fe₁ s G d = read1Ok U₂ h fe₂ s G d := by
  unfold read1Ok
  rw [← target_congr hU hf]
  cases ht : target h fe₁ U₁ d with
  | none => rfl
  | some p =>
    obtain ⟨h', j'⟩ := p
    simp only
    split
    · rfl
    · rename_i hne
      obtain ⟨c, hc⟩ := target_look ht (fun e => hne (beq_iff_eq.mpr e))
      unfold UView.needAt UView.gateAt
      rw [hU.iface d h' j' c hc]

theorem full1Ok_congr (h : Nat) (s : ModSlot) (G : Array (Nat × UInt8)) (w : Want) (d : Name) :
    full1Ok U₁ h fe₁ s G w d = full1Ok U₂ h fe₂ s G w d := by
  unfold full1Ok
  rw [← target_congr hU hf]
  cases ht : target h fe₁ U₁ d with
  | none => rfl
  | some p =>
    obtain ⟨h', j'⟩ := p
    simp only
    split
    · rfl
    · rename_i hne
      obtain ⟨c, hc⟩ := target_look ht (fun e => hne (beq_iff_eq.mpr e))
      unfold UView.storedAt UView.fullGateAt
      rw [← hU.look, hU.iface d h' j' c hc]

theorem readsOk_congr (h : Nat) (s : ModSlot) (lvl2 : Bool) (G : Array (Nat × UInt8))
    (r : ReadSet) : readsOk U₁ h fe₁ s lvl2 G r = readsOk U₂ h fe₂ s lvl2 G r := by
  unfold readsOk
  simp only [read2Ok_congr hU hf, read1Ok_congr hU hf, full2Ok_congr hU hf, full1Ok_congr hU hf]

/-- **A unit's check reads its context only through the lookup and the
interfaces of the modules it answers with.** -/
theorem unitOk_congr (hfind : ∀ n, findIn fe₁ U₁ n = findIn fe₂ U₂ n) (h : Nat)
    (fl : Name → Bool) (s : ModSlot) (r : Reads) :
    unitOk U₁ h fe₁ fl s r = unitOk U₂ h fe₂ fl s r := by
  have hfind' : findIn fe₁ U₁ = findIn fe₂ U₂ := funext hfind
  unfold unitOk shapeOk
  rw [hf.env, hfind']
  simp only [readsOk_congr hU hf]

end congr

/-! ## At the store of the units -/

/-- The data of an isolated run's modules over the store of its units:
every module's own constants over that store's lookup (`ownView`). -/
@[expose] def ghostData (slots : Array (Thunk ModSlot)) (M : Array ModData) : Array ModData :=
  Array.ofFn fun k : Fin M.size => { M[k] with fe := ownView M[k].fe.env ((ghostStore slots).mb k) }

theorem ghostData_size (slots : Array (Thunk ModSlot)) (M : Array ModData) :
    (ghostData slots M).size = M.size := Array.size_ofFn

theorem ghostData_get (slots : Array (Thunk ModSlot)) (M : Array ModData) {i : Nat}
    (hi : i < (ghostData slots M).size) :
    (ghostData slots M)[i] =
      { M[i]'(ghostData_size slots M ▸ hi) with
        fe := ownView (M[i]'(ghostData_size slots M ▸ hi)).fe.env ((ghostStore slots).mb i) } :=
  Array.getElem_ofFn ..

/-- **The isolated view of a context answers as the store's view**, when
the store's name index lists every unit constant. -/
theorem uagree_store {S : Store} (hI : IdxOk S) (i : Nat) :
    UAgree (isoUView (mask S.slot (S.lvl i)) (S.lvl i)) (S.uview i) := by
  have hpick : (S.mb i).pick? = isoLook S.slot (S.lvl i) := by
    funext n
    rw [pick?_iso hI]
    rfl
  refine ⟨?_, fun d h' j' c hc => ?_⟩
  · show isoLook (mask S.slot _) _ = (S.mb i).pick?
    rw [isoLook_mask, hpick]
  · show (mask S.slot _ h').exp = (S.slot h').exp
    have hc' : isoLook (mask S.slot (S.lvl i)) (S.lvl i) d = some (h', j', c) := hc
    rw [isoLook_mask] at hc'
    obtain ⟨e, he, rfl, -, -, -⟩ := isoLook_entry hc'
    rcases entry_lvl he with h1 | h2
    · rw [mask_one h1]
    · rw [mask_two h2]

theorem feAgree_ownView (own : Env) (mb : MBase) : FeAgree (mkFEnv own) (ownView own mb) :=
  ⟨rfl, rfl, rfl⟩

/-- **The isolated check of a unit is the store's check of it**, when the
store's name index lists every unit constant. -/
theorem unitOk_store {S : Store} (hI : IdxOk S) (i : Nat) (own : Env)
    (fl : Name → Bool) (s : ModSlot) (r : Reads) :
    unitOk (isoUView (mask S.slot (S.lvl i)) (S.lvl i)) i (mkFEnv own) fl s r =
      unitOk (S.uview i) i (ownView own (S.mb i)) fl s r := by
  have hU := uagree_store hI i
  refine unitOk_congr hU (feAgree_ownView _ _) (fun n => ?_) i fl s r
  -- the own index, then the context: the same lookups
  have hown : (ownView own (S.mb i)).find? n = (own.find? n).or ((S.mb i).find? n) := by
    have hc : CanonB (ownView own (S.mb i)) { mb := some (S.mb i) } := rfl
    rw [hc.find? n]; rfl
  unfold findIn
  rw [mkFEnv_find?, hown]
  cases ho : own.find? n with
  | some c => rfl
  | none =>
    simp only [Option.none_or]
    rw [hU.look]
    simp only [Store.uview_look]
    unfold MBase.find?
    cases (S.mb i).pick? n with
    | none => rfl
    | some x => obtain ⟨_, _, _⟩ := x; rfl

/-- **The isolated duplicates' check gives the store's**: every copy of a
name a module sees has the qualified name of the first. -/
theorem keysOk_oneKey (S : Store) (i : Nat) (h : keysOk S.slot (S.lvl i) = true) (n : Name) :
    oneKey S i n = true := by
  unfold keysOk at h
  rw [List.all_eq_true] at h
  -- every visible alternate has the qualified name of the first presentation
  have hk : ∀ x ∈ (S.mb i).alts n, ∀ c, (S.mb i).at? x.1 x.2 = some c → c.name = n →
      ∃ h₀ j₀ c₀, isoLook S.slot (S.lvl i) n = some (h₀, j₀, c₀) ∧
        S.keyAt x.1 x.2 n = S.keyAt h₀ j₀ n := by
    intro x _ c hat hcn
    have he := entry_of_at? hat
    have := h _ he
    simp only at this
    rw [hcn] at this
    cases hl : isoLook S.slot (S.lvl i) n with
    | none => rw [hl] at this; cases this
    | some y =>
      obtain ⟨h₀, j₀, c₀⟩ := y
      rw [hl] at this
      exact ⟨h₀, j₀, c₀, rfl, beq_iff_eq.mp this⟩
  unfold oneKey
  simp only
  split
  · rfl
  · rename_i h₀ j₀ rest hv
    have hmem : ∀ x ∈ (h₀, j₀) :: rest, ∃ h₁ j₁ c₁,
        isoLook S.slot (S.lvl i) n = some (h₁, j₁, c₁) ∧ S.keyAt x.1 x.2 n = S.keyAt h₁ j₁ n := by
      intro x hx
      rw [← hv, List.mem_filter] at hx
      obtain ⟨hxa, hxv⟩ := hx
      cases hat : (S.mb i).at? x.1 x.2 with
      | none => rw [hat] at hxv; cases hxv
      | some c =>
        rw [hat] at hxv
        exact hk _ hxa c hat (beq_iff_eq.mp hxv)
    rw [List.all_eq_true]
    intro x hx
    rw [beq_iff_eq]
    obtain ⟨h₁, j₁, c₁, hl, hx'⟩ := hmem x (List.mem_cons_of_mem _ hx)
    obtain ⟨h₂, j₂, c₂, hl', hy'⟩ := hmem (h₀, j₀) List.mem_cons_self
    rw [hl] at hl'
    simp only [Option.some.injEq, Prod.mk.injEq] at hl'
    obtain ⟨rfl, rfl, -⟩ := hl'
    rw [hx', hy']

/-! ## What an isolated run establishes -/

/-- **What an isolated modular run establishes**, about the published
units `slots` and the modules' data `M`: per module `i` (its levels `lv`
those its unit records), its records installed from the canonical index
of its context built from the units it reads (`mask`), every record
checked there, its proofs attested there, its own constants over that
context those its data holds; its data's index the canonical index of
its own constants; its unit checked against them and its context
(`isoUView`); its local checks (`localOkIso`).  Beside these, the
coverage: one unit per module, published as the module's data, its
constants the install's, imports earlier, levels over the run's modules. -/
structure IsoRunOk (mode : CheckMode) (slots : Array (Thunk ModSlot)) (M : Array ModData) :
    Prop where
  sizes : slots.size = M.size
  below : ∀ i (h : i < M.size), ∀ b ∈ M[i].imports, b < i
  lvls : ∀ i (h : i < M.size), M[i].unit.prv.lvl.size = M.size
  slot : ∀ i (h : i < M.size), slotOf slots i = M[i].unit
  priv : ∀ i (h : i < M.size), M[i].unit.prv.priv = M[i].fe.env.consts.reverse.toArray
  own : ∀ i (h : i < M.size), M[i].fe = mkFEnv M[i].fe.env
  iso : ∀ i (h : i < M.size), ∃ n feI pendI,
    InstallRun mode natOpPinSets M[i].ds.toList
      (0, mkFEnv (isoCtx (mask (slotOf slots) M[i].unit.prv.lvl) M[i].unit.prv.lvl), #[])
      (n, feI, pendI) ∧
    (∀ pc ∈ pendI.toList, ∃ s, checkPending mode feI pc {} = .ok ((), s)) ∧
    ProofsAttested mode M[i].flags.contains feI pendI ∧
    feI.env = Env.over M[i].fe.env (isoCtx (mask (slotOf slots) M[i].unit.prv.lvl) M[i].unit.prv.lvl)
  unit : ∀ i (h : i < M.size),
    unitOk (isoUView (mask (slotOf slots) M[i].unit.prv.lvl) M[i].unit.prv.lvl) i M[i].fe
      M[i].flags.contains M[i].unit M[i].reads = true
  locals : ∀ i (h : i < M.size),
    localOkIso i (mask (slotOf slots) M[i].unit.prv.lvl) M[i].unit.prv.lvl = true

/-- **An isolated run is an isolated install over the store of its
units.** -/
theorem IsoRunOk.storeOk {slots : Array (Thunk ModSlot)} {M : Array ModData}
    (h : IsoRunOk mode slots M) : IsoStoreOk mode (ghostStore slots) (ghostData slots M) := by
  have hsz := ghostData_size slots M
  have hget : ∀ {i : Nat} (hi : i < (ghostData slots M).size), _ := fun {i} hi =>
    ghostData_get slots M (i := i) hi
  have hS : (ghostStore slots).slots.size = M.size := h.sizes
  -- module `i`'s levels in the store are its unit's
  have hlv : ∀ i (hi : i < M.size), (ghostStore slots).lvl i = M[i].unit.prv.lvl := by
    intro i hi
    rw [ghostStore_lvl (h.sizes ▸ hi), h.slot i hi]
  have hslot : (ghostStore slots).slot = slotOf slots := rfl
  refine { slots := by rw [hsz]; exact hS, lvls := fun i hi => ?_, below := fun i hi => ?_,
           idx := ghostStore_idxOk slots, iso := fun i hi => ?_, view := fun i hi => ?_,
           slot := fun i hi => ?_, priv := fun i hi => ?_, ulvl := fun i hi => ?_,
           unit := fun i hi => ?_, locals := fun i hi => ?_, dups := ghostStore_dupsOk slots }
  · rw [hsz] at hi ⊢; rw [hlv i hi]; exact h.lvls i hi
  · rw [hget]; exact h.below i _
  · have hi' : i < M.size := hsz ▸ hi
    rw [hget, hslot, hlv i hi', ← isoCtx_mask]
    exact h.iso i hi'
  · rw [hget]; rfl
  · rw [hget]; exact h.slot i _
  · rw [hget]; exact h.priv i _
  · rw [hget, hlv i (hsz ▸ hi)]
  · have hi' : i < M.size := hsz ▸ hi
    rw [hget]
    show unitOk ((ghostStore slots).uview i) i (ownView M[i].fe.env ((ghostStore slots).mb i))
      M[i].flags.contains M[i].unit M[i].reads = true
    rw [← unitOk_store (ghostStore_idxOk slots) i, hlv i hi', ← h.own i hi']
    exact h.unit i hi'
  · have hi' : i < M.size := hsz ▸ hi
    have hl := h.locals i hi'
    unfold localOkIso at hl
    rw [Bool.and_eq_true, levelsOk_mask, keysOk_mask] at hl
    unfold localOk
    rw [Bool.and_eq_true, hslot, hlv i hi', Array.all_eq_true]
    refine ⟨hl.1, fun k _ => keysOk_oneKey _ i ?_ _⟩
    rw [hslot, hlv i hi']
    exact hl.2

/-- **The development an isolated run stands for**: every module's
context built from the units it reads, its own environment its constants
over it; its sources, proofs, qualified names and interface read off its
unit and the units it reads (at the store of the units). -/
@[expose] def isoRunDev (slots : Array (Thunk ModSlot)) (M : Array ModData) : Nat → Module :=
  isoDevOf (ghostStore slots) (ghostData slots M)

/-- **Every module of an isolated run passes its local checks**: the
hypothesis of the modular capstones (`ConLeche.modular_model_exists`,
`ConLeche.modular_no_False`). -/
theorem IsoRunOk.localOk {slots : Array (Thunk ModSlot)} {M : Array ModData}
    (h : IsoRunOk mode slots M) (i : Nat) : LocalOk mode natOpPinSets (isoRunDev slots M) i :=
  h.storeOk.localOk i

/-! ## A store run is an isolated run -/

/-- A store run's data with every module's own index in place of its
view (what an isolated run keeps). -/
@[expose] def ownData (M : Array ModData) : Array ModData :=
  M.map fun d => { d with fe := mkFEnv d.fe.env }

/-- **The store run's duplicates' check gives the isolated one.** -/
theorem RunOk.keysOk_iso {S : Store} {M : Array ModData} (hR : RunOk mode S M) {i : Nat}
    (hi : i < M.size) : keysOk S.slot (S.lvl i) = true := by
  unfold keysOk
  rw [List.all_eq_true]
  intro e he
  have hat := at?_of_entry he
  have hx : (e.h, e.j) ∈ S.alts e.ci.name := hR.idx.mem_alts hat
  have hsome := pickIn_isSome (mb := S.mb i) (l := (S.mb i).alts e.ci.name)
    (by rw [Store.alts_mb]; exact hx) hat rfl
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨h₀, j₀, c₀⟩ := p
  have hp' : (S.mb i).pick? e.ci.name = some (h₀, j₀, c₀) := hp
  have hl : isoLook S.slot (S.lvl i) e.ci.name = some (h₀, j₀, c₀) := by
    rw [← hp']
    unfold isoLook
    rw [pick?_iso hR.idx]
  rw [hl]
  simp only [beq_iff_eq]
  exact hR.key_pick hi hp' hx hat rfl

/-- **A store run is an isolated run** of the same units: the store mode
is the isolated mode with every module's context read through one shared
name index (proved here: the index answers as the units). -/
theorem RunOk.isoRunOk {S : Store} {M : Array ModData} (hR : RunOk mode S M) :
    IsoRunOk mode S.slots (ownData M) := by
  have hI := hR.isoStoreOk
  have hsz : (ownData M).size = M.size := Array.size_map ..
  have hget : ∀ i (hi : i < (ownData M).size),
      (ownData M)[i] = { M[i]'(hsz ▸ hi) with fe := mkFEnv (M[i]'(hsz ▸ hi)).fe.env } :=
    fun i hi => Array.getElem_map ..
  have hslot : slotOf S.slots = S.slot := rfl
  refine { sizes := by rw [hsz]; exact hR.slots, below := fun i hi => ?_, lvls := fun i hi => ?_,
           slot := fun i hi => ?_, priv := fun i hi => ?_, own := fun i hi => ?_,
           iso := fun i hi => ?_, unit := fun i hi => ?_, locals := fun i hi => ?_ }
  · rw [hget]; exact hR.below i (hsz ▸ hi)
  · rw [hget]; simp only; rw [hR.ulvl i (hsz ▸ hi), hsz]; exact hR.lvls i (hsz ▸ hi)
  · rw [hget, hslot]; exact hR.slot i (hsz ▸ hi)
  · rw [hget]; exact hR.priv i (hsz ▸ hi)
  · rw [hget]; rfl
  · have hi' : i < M.size := hsz ▸ hi
    rw [hget]
    simp only
    rw [hR.ulvl i hi', hslot, isoCtx_mask]
    obtain ⟨n, feI, pendI, hrun, hchk, hprf, henv⟩ := hI.iso i hi'
    exact ⟨n, feI, pendI, hrun, hchk, hprf, henv⟩
  · have hi' : i < M.size := hsz ▸ hi
    rw [hget]
    simp only
    rw [hR.ulvl i hi', hslot, unitOk_store hR.idx i, ← hI.view i hi']
    exact hR.unit i hi'
  · have hi' : i < M.size := hsz ▸ hi
    rw [hget]
    simp only
    rw [hR.ulvl i hi', hslot]
    unfold localOkIso
    rw [levelsOk_mask, keysOk_mask, hR.keysOk_iso hi', Bool.and_true]
    exact localOk_levels (hR.locals i hi')

end ConLeche.Cached.Mod
