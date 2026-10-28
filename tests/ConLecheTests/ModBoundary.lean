module

public import ConLeche.Verify.Modular.View
public import ConLeche.Verify.Modular.Mask
public import ConLeche.Driver.Modular
import ConLeche.Verify.Modular.Local

public section

/-!
# The boundary between a unit's two halves (task #370)

A module that loads module `h` at the exported level reads `h`'s
interface (`exp`) and never its private record (`prv`), which only an
`import all` importer reads.  This file makes the boundary a theorem:
empty the private record of every module a viewer does not load at the
private level (`maskPrv`) and every lookup of its view answers the same
(`at?`, `pick?`, `find?`, `findTable?`), so the view is a twin of the
masked one (`Twin`: every install step and record check runs alike,
`installDeclStep_twin`, `checkPending_congr`); and a constant's
key, for a constant the exported part presents, reads the
interface alone (`keyOfSlot_maskPrv`).  A read of `prv` added on an
exported-level path breaks one of these.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- The store as a viewer with levels `b.lvl` would see it if every
module it does not load at the private level had no private record. -/
def maskPrv (b : MBase) : MBase :=
  { b with slots := b.slots.mapIdx fun h t =>
      if lvlAt b.lvl h == 2 then t else Thunk.pure { t.get with prv := {} } }

theorem maskPrv_lvl (b : MBase) : (maskPrv b).lvl = b.lvl := by rfl

theorem maskPrv_size (b : MBase) : (maskPrv b).slots.size = b.slots.size := by
  simp [maskPrv]

theorem maskPrv_gateOk (b : MBase) (g : Array (Nat × UInt8)) :
    (maskPrv b).gateOk g = b.gateOk g := by rfl

theorem maskPrv_exp (b : MBase) {h : Nat} (hh : h < (maskPrv b).slots.size) :
    ((maskPrv b).slots[h]).get.exp = (b.slots[h]'(by rwa [maskPrv_size] at hh)).get.exp := by
  simp only [maskPrv, Array.getElem_mapIdx]
  split <;> rfl

theorem maskPrv_get2 (b : MBase) {h : Nat} (hh : h < (maskPrv b).slots.size)
    (hl : h < b.lvl.size) (h2 : (b.lvl[h] == 2) = true) :
    ((maskPrv b).slots[h]).get = (b.slots[h]'(by rwa [maskPrv_size] at hh)).get := by
  simp only [maskPrv, Array.getElem_mapIdx, lvlAt, hl, ↓reduceDIte, h2, ↓reduceIte]

theorem ite_mask_exp (c : Prop) [Decidable c] (t : Thunk ModSlot) :
    (if c then t else Thunk.pure { t.get with prv := {} }).get.exp = t.get.exp := by
  split <;> rfl

theorem maskPrv_at? (b : MBase) (h j : Nat) : (maskPrv b).at? h j = b.at? h j := by
  obtain ⟨idx, slots, lvl⟩ := b
  unfold MBase.at?
  simp only [maskPrv, Array.size_mapIdx, MBase.gateOk]
  split
  · rename_i hl
    split
    · rename_i h2
      split
      · rename_i hs
        simp only [Array.getElem_mapIdx, lvlAt, hl, ↓reduceDIte, h2, ↓reduceIte]
      · rfl
    · split
      · split
        · rename_i hs
          simp only [Array.getElem_mapIdx, ite_mask_exp]
        · rfl
      · rfl
  · rfl

theorem maskPrv_alts (b : MBase) (n : Name) : (maskPrv b).alts n = b.alts n := by
  unfold MBase.alts maskPrv; rfl

theorem maskPrv_pickIn (b : MBase) (n : Name) :
    ∀ l, (maskPrv b).pickIn n l = b.pickIn n l
  | [] => rfl
  | (h, j) :: rest => by
    unfold MBase.pickIn
    rw [maskPrv_at?, maskPrv_pickIn b n rest]

theorem maskPrv_pick? (b : MBase) (n : Name) : (maskPrv b).pick? n = b.pick? n := by
  unfold MBase.pick?
  rw [maskPrv_alts, maskPrv_pickIn]

theorem maskPrv_find? (b : MBase) (n : Name) : (maskPrv b).find? n = b.find? n := by
  unfold MBase.find?
  rw [maskPrv_pick?]

theorem maskPrv_findTable? (b : MBase) (T : Name) :
    (maskPrv b).findTable? T = b.findTable? T := by
  unfold MBase.findTable?
  rw [maskPrv_pick?, maskPrv_lvl]
  split
  · rename_i h j cv caps _
    by_cases hs : h < b.slots.size
    · have hs' : h < (maskPrv b).slots.size := by rw [maskPrv_size]; exact hs
      simp only [hs, hs', ↓reduceDIte]
      by_cases hl : h < b.lvl.size
      · by_cases h2 : (b.lvl[h] == 2) = true
        · simp only [hl, ↓reduceDIte, h2, ↓reduceIte, maskPrv_get2 b hs' hl h2]
        · simp only [hl, ↓reduceDIte, h2, Bool.false_eq_true, ↓reduceIte, maskPrv_exp b hs']
      · simp only [hl, ↓reduceDIte]
    · have hs' : ¬ h < (maskPrv b).slots.size := by rw [maskPrv_size]; exact hs
      simp only [hs, hs', ↓reduceDIte]
  · rfl

/-- **A view is the twin of its masked view**: the module's install and
checks at it never read a private record it does not load. -/
theorem view_twin_maskPrv (b : MBase) : Twin (viewOf b) (viewOf (maskPrv b)) := by
  refine ⟨?_, ?_, (canonB_viewOf b).idxBelow, (canonB_viewOf (maskPrv b)).idxBelow⟩
  · funext n
    unfold viewOf FEnv.find? FBase.find?
    simp [maskPrv_find?]
  · funext T
    unfold viewOf FEnv.rawTable? FBase.findTable?
    simp [maskPrv_findTable?]

/-- **A presented constant's key reads the interface alone.** -/
theorem keyOfSlot_maskPrv (s : ModSlot) (h j : Nat)
    (hp : ((s.exp.at1[j]?).join).isSome = true) :
    keyOfSlot s h j = keyOfSlot { s with prv := {} } h j := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hp
  unfold keyOfSlot
  simp only [hci]

/-! ## An isolated module reads what Lean loads for it (task #374)

Module `M` with levels `lv` (Lean's `importModulesCore` for `M`: `1` a
module loaded at the exported level, `2` one loaded with `import all`, `0`
one not loaded) reads its imports' units only through `mask s lv`: the
interface of a module loaded at level 1 or 2, the private record of one
loaded at level 2, nothing of any other.  Two families of units that agree
there (`LoadedAgree`) give every isolated computation around `M` the same
result — its context's one-pass build (index, lookup, duplicates), the
check of its records, its unit (the driver's `unitOf`) and that unit's
check, its local checks.  This holds by construction (each takes the
masked units); the theorems below pin it, and `isoCtx_mask` and the other
lemmas of `ConLeche/Verify/Modular/Mask.lean` that masking changes
nothing. -/

/-- **An isolated module's computations read only the units Lean loads
for it**, and of those loaded at the exported level only the interface. -/
theorem isolated_boundary {lv : ByteArray} {s s' : Nat → ModSlot} (h : LoadedAgree lv s s') :
    isoBuild (mask s lv) lv = isoBuild (mask s' lv) lv ∧
    (∀ mode pins ds, checkModuleIsolated mode pins (mask s lv) lv ds =
      checkModuleIsolated mode pins (mask s' lv) lv ds) ∧
    (∀ m fe fl u r, unitOk (isoUView (mask s lv) lv) m fe fl u r =
      unitOk (isoUView (mask s' lv) lv) m fe fl u r) ∧
    (∀ m, localOkIso m (mask s lv) lv = localOkIso m (mask s' lv) lv) := by
  rw [mask_agree h]
  exact ⟨rfl, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ => rfl⟩

/-- **The unit an isolated module computes reads only what Lean loads for
it**: the driver's `unitOf` over two agreeing families. -/
theorem unitOf_boundary {lv : ByteArray} {s s' : Nat → ModSlot} (h : LoadedAgree lv s s')
    (g : Array Driver.Modular.ModIn) (fl : Std.HashSet Name) (k : Nat) (fe : FEnv) :
    Driver.Modular.unitOf g (isoUView (mask s lv) lv) fl k lv fe =
      Driver.Modular.unitOf g (isoUView (mask s' lv) lv) fl k lv fe := by
  rw [mask_agree h]

/-- **Masking changes nothing**: the context, its lookup, the records'
check and the local checks from the masked units are those from all the
units. -/
theorem isolated_mask (s : Nat → ModSlot) (lv : ByteArray) :
    isoCtx (mask s lv) lv = isoCtx s lv ∧ isoLook (mask s lv) lv = isoLook s lv ∧
    (∀ mode pins ds, checkModuleIsolated mode pins (mask s lv) lv ds =
      checkModuleIsolated mode pins s lv ds) ∧
    (∀ m, localOkIso m (mask s lv) lv = localOkIso m s lv) :=
  ⟨isoCtx_mask s lv, isoLook_mask s lv, fun mode pins ds => checkModuleIsolated_mask mode pins s lv ds,
    fun m => localOkIso_mask m s lv⟩

/--
info: 'ConLeche.Cached.Mod.isolated_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isolated_boundary

end ConLeche.Cached.Mod
