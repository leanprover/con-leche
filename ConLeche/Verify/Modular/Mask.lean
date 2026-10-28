module

public import ConLeche.Cached.ModIso
import ConLeche.Verify.Modular.IsoCtx

public section

/-!
# What an isolated module reads (task #374)

Everything the isolated mode computes around module `M` — its context,
its context's lookup, the check of its records, the check of its unit
and its local checks — takes `M`'s imports' units as `mask slot lv`
(`ConLeche/Cached/ModIso.lean`): the whole unit of a module `M` loads
privately (`import all`), the interface alone of one it loads at the
exported level, nothing of any other.  This file proves that the mask
changes none of them: each is the same function of the masked units as
of all the units (`isoEntries_mask`, `isoCtx_mask`, `isoLook_mask`,
`keysOk_mask`, `levelsOk_mask`, `checkModuleIsolated_mask`).  So the
isolated mode reads exactly what Lean's own import reads for `M` (its
loaded modules' interfaces, the private parts only under `import all`),
and the proofs may speak of the units themselves.

`LoadedAgree lv s s'` says that two families of units agree on what a
module with levels `lv` may read; the masks of such families are equal
(`mask_agree`), so every isolated computation around the module gives
the same result on both (`ConLecheTests/ModBoundary.lean` pins the
statement).
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- **Two families of units agree on what a module with levels `lv` may
read**: the interface of every module it loads (at level 1 or 2), and the
private record of every module it loads at the private level (2). -/
@[expose] def LoadedAgree (lv : ByteArray) (s s' : Nat → ModSlot) : Prop :=
  ∀ h, (lvlAt lv h = 1 ∨ lvlAt lv h = 2) →
    (s h).exp = (s' h).exp ∧ (lvlAt lv h = 2 → (s h).prv = (s' h).prv)

theorem mask_two {s : Nat → ModSlot} {lv : ByteArray} {h : Nat} (h2 : lvlAt lv h = 2) :
    mask s lv h = s h := by
  unfold mask; simp [h2]

theorem mask_one {s : Nat → ModSlot} {lv : ByteArray} {h : Nat} (h1 : lvlAt lv h = 1) :
    mask s lv h = { exp := (s h).exp } := by
  unfold mask; simp [h1]

theorem mask_other {s : Nat → ModSlot} {lv : ByteArray} {h : Nat} (h1 : lvlAt lv h ≠ 1)
    (h2 : lvlAt lv h ≠ 2) : mask s lv h = {} := by
  unfold mask; simp [h1, h2]

/-- **The masks of agreeing families are equal.** -/
theorem mask_agree {lv : ByteArray} {s s' : Nat → ModSlot} (h : LoadedAgree lv s s') :
    mask s lv = mask s' lv := by
  funext x
  by_cases h2 : lvlAt lv x = 2
  · obtain ⟨he, hp⟩ := h x (.inr h2)
    rw [mask_two h2, mask_two h2]
    have hp := hp h2
    cases hs : s x; cases hs' : s' x
    rw [hs, hs'] at he hp
    simp_all
  · by_cases h1 : lvlAt lv x = 1
    · rw [mask_one h1, mask_one h1, (h x (.inl h1)).1]
    · rw [mask_other h1 h2, mask_other h1 h2]

/-- A family agrees with its mask. -/
theorem mask_loadedAgree (s : Nat → ModSlot) (lv : ByteArray) : LoadedAgree lv (mask s lv) s := by
  intro x hx
  rcases hx with h1 | h2
  · rw [mask_one h1]; exact ⟨rfl, fun h2 => by rw [h1] at h2; cases h2⟩
  · rw [mask_two h2]; exact ⟨rfl, fun _ => rfl⟩

/-! ## The presentations -/

/-- A level that is neither 1 nor 2 presents nothing. -/
theorem presentAt_other {lv : ByteArray} {s : ModSlot} {l : UInt8} (h1 : l ≠ 1) (h2 : l ≠ 2)
    (j : Nat) : presentAt lv s l j = none := by
  unfold presentAt
  simp [h1, h2]

/-- **A module presents the same constants from its masked unit.** -/
theorem entriesOf_mask (s : Nat → ModSlot) (lv : ByteArray) (h : Nat) :
    entriesOf lv h (mask s lv) = entriesOf lv h s := by
  rw [entriesOf_eq, entriesOf_eq]
  by_cases h2 : lvlAt lv h = 2
  · rw [mask_two h2]
  · by_cases h1 : lvlAt lv h = 1
    · rw [mask_one h1, h1]
      rfl
    · rw [mask_other h1 h2]
      rw [List.filterMap_eq_nil_iff.mpr (fun j _ => by rw [presentAt_other h1 h2]; rfl)]
      rw [List.filterMap_eq_nil_iff.mpr (fun j _ => by rw [presentAt_other h1 h2]; rfl)]

theorem isoEntries_mask (s : Nat → ModSlot) (lv : ByteArray) :
    isoEntries (mask s lv) lv = isoEntries s lv := by
  unfold isoEntries
  congr 1
  funext h
  exact entriesOf_mask s lv h

/-- **The context from the masked units is the context.** -/
theorem isoCtx_mask (s : Nat → ModSlot) (lv : ByteArray) : isoCtx (mask s lv) lv = isoCtx s lv := by
  unfold isoCtx
  rw [isoEntries_mask]

theorem isoIndex_mask (s : Nat → ModSlot) (lv : ByteArray) :
    isoIndex (mask s lv) lv = isoIndex s lv := by
  unfold isoIndex
  rw [isoCtx_mask]

/-- **The context's lookup from the masked units is the context's lookup.** -/
theorem isoLook_mask (s : Nat → ModSlot) (lv : ByteArray) : isoLook (mask s lv) lv = isoLook s lv := by
  funext n
  unfold isoLook
  rw [isoEntries_mask]

/-- **The isolated check of a module from the masked units is its isolated
check.** -/
theorem checkModuleIsolated_mask (mode : CheckMode) (pins : List NatOpPinSet)
    (s : Nat → ModSlot) (lv : ByteArray) (ds : Array Declaration) :
    checkModuleIsolated mode pins (mask s lv) lv ds = checkModuleIsolated mode pins s lv ds := by
  unfold checkModuleIsolated
  rw [isoIndex_mask]

/-! ## Keys and the local checks -/

/-- A presented constant's level is 1 or 2. -/
theorem entry_lvl {s : Nat → ModSlot} {lv : ByteArray} {e : IsoEntry} (he : e ∈ isoEntries s lv) :
    lvlAt lv e.h = 1 ∨ lvlAt lv e.h = 2 := by
  obtain ⟨-, -, hp, -⟩ := mem_isoEntries.mp he
  by_cases h2 : lvlAt lv e.h = 2
  · exact .inr h2
  · by_cases h1 : lvlAt lv e.h = 1
    · exact .inl h1
    · rw [presentAt_other h1 h2] at hp; cases hp

/-- **A presented constant's key reads what the mask keeps.** -/
theorem keyOfSlot_mask {s : Nat → ModSlot} {lv : ByteArray} {e : IsoEntry}
    (he : e ∈ isoEntries s lv) :
    keyOfSlot (mask s lv e.h) e.h e.j = keyOfSlot (s e.h) e.h e.j := by
  rcases entry_lvl he with h1 | h2
  · rw [mask_one h1]
    obtain ⟨-, -, hp, -⟩ := mem_isoEntries.mp he
    rw [h1] at hp
    rcases (presentAt_some hp).2 with ⟨h2, -⟩ | ⟨-, ci, hci, -⟩
    · cases h2
    · unfold keyOfSlot
      simp only [hci]
  · rw [mask_two h2]

/-- The context's lookup answers with one of its entries. -/
theorem isoLook_entry {s : Nat → ModSlot} {lv : ByteArray} {n : Name} {h j : Nat}
    {c : ConstantInfo} (hl : isoLook s lv n = some (h, j, c)) :
    ∃ e ∈ isoEntries s lv, e.h = h ∧ e.j = j ∧ e.ci = c ∧ c.name = n := by
  unfold isoLook at hl
  cases hf : (isoEntries s lv).find? (·.ci.name == n) with
  | none => rw [hf] at hl; cases hl
  | some e =>
    rw [hf] at hl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨e, List.mem_of_find?_eq_some hf, rfl, rfl, rfl,
      beq_iff_eq.mp (by simpa using List.find?_some hf)⟩

theorem all_congr' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **The duplicates' check from the masked units is the check.** -/
theorem keysOk_mask (s : Nat → ModSlot) (lv : ByteArray) : keysOk (mask s lv) lv = keysOk s lv := by
  unfold keysOk
  rw [isoEntries_mask, isoLook_mask]
  refine all_congr' fun e he => ?_
  cases hl : isoLook s lv e.ci.name with
  | none => rfl
  | some x =>
    obtain ⟨h₀, j₀, c⟩ := x
    obtain ⟨e₀, he₀, rfl, rfl, -, -⟩ := isoLook_entry hl
    simp only
    rw [keyOfSlot_mask he, keyOfSlot_mask he₀]

theorem u8_zero_of {x : UInt8} (h : x ≤ 2) (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  have a := UInt8.le_iff_toNat_le.mp h
  have b : x.toNat ≠ 1 := fun e => h1 (UInt8.toNat_inj.mp (by simpa using e))
  have c : x.toNat ≠ 2 := fun e => h2 (UInt8.toNat_inj.mp (by simpa using e))
  simp at a
  exact UInt8.toNat_inj.mp (by simp; omega)

/-- **The levels' check from the masked units is the check.** -/
theorem levelsOk_mask (m : Nat) (s : Nat → ModSlot) (lv : ByteArray) :
    levelsOk m lv (mask s lv) = levelsOk m lv s := by
  unfold levelsOk
  congr 1
  funext h
  simp only
  by_cases h2 : lvlAt lv h = 2
  · rw [mask_two h2]
  · by_cases h1 : lvlAt lv h = 1
    · rw [mask_one h1]; simp [h1]
    · by_cases hle : lvlAt lv h ≤ 2
      · simp [u8_zero_of hle h1 h2]
      · simp [hle]

theorem localOkIso_mask (m : Nat) (s : Nat → ModSlot) (lv : ByteArray) :
    localOkIso m (mask s lv) lv = localOkIso m s lv := by
  unfold localOkIso
  rw [levelsOk_mask, keysOk_mask]

end ConLeche.Cached.Mod
