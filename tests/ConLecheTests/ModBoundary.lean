module

public import ConLeche.Verify.Modular.View
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
qualified name, for a constant the exported part presents, reads the
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

/-- **A presented constant's qualified name reads the interface alone.** -/
theorem keyOfSlot_maskPrv (s : ModSlot) (h j : Nat) (n : Name)
    (hp : ((s.exp.at1[j]?).join).isSome = true) :
    keyOfSlot s h j n = keyOfSlot { s with prv := {} } h j n := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hp
  unfold keyOfSlot
  simp only [hci]

end ConLeche.Cached.Mod
