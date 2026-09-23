module

public import ConLeche.Model.BasisLfp
public import ConLeche.Model.Annot.BlockLfpMono

public section

/-!
# The pinned basis clauses in HOLE form (lane POSPROOF)

Production-data instances of the interface `ReadsHoles`
(`Model/Annot/BlockLfpMono.lean`) at the clauses the basis installs
record (`Model/BasisLfp.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.SetModel

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The field-free clauses in HOLE form (lane POSPROOF)

`ReadsHoles` (`Annot/BlockLfpMono.lean`) is the link HOLE2's clause must
carry: the fit relation IS the hole reading of the stored constructors.
The zero- and one-constructor field-free clauses above already have it
(no field, no result index; the index set is the unit set).  The pinned
`Nat`'s does NOT: its fit (`natFits`) asks `m ∈ ω` beside the hole
`m ∈ S`, a condition no field reading states — HOLE2 restates it (the
operator `{∅} ∪ {vsucc m ∣ m ∈ S}` has the same least fixed point `ω`). -/

/-- The hole reading of a one-member, unparameterized, unindexed block
with `n` field-free constructors. -/
@[expose] def holes0 (n : Nat) : HoleReading V where
  nctors := fun _ => n
  frame := fun _ ρp _ => ρp
  fields := fun _ _ _ => []
  resIdx := fun _ _ _ => []

theorem spineFit_nil_iff {ρ : Nat → V} {fs : List V} : SpineFit ρ [] fs ↔ fs = [] := by
  cases fs <;> simp [SpineFit]

/-- **`PUnit`'s recorded clause reads its constructor with holes.** -/
theorem punitLfp_readsHoles {nm : Name} {w : (Name → Nat) → Nat} :
    ReadsHoles (punitLfp (V := V) nm w) (holes0 1) := by
  intro ψ ρp _ X _ c _ t ht j fs
  have ht' : t ∈ˢ (unitSet : V) := by rw [← lfp0_idx ψ ρp c]; exact ht
  have ht := mem_unitSet_iff.mp ht'
  subst ht
  show (j = 0 ∧ fs = []) ↔ (j < 1 ∧ SpineFit ρp [] fs ∧ tupW 0 [] = pt)
  rw [spineFit_nil_iff, tupW_zero]
  exact ⟨fun ⟨hj, hf⟩ => ⟨by omega, hf, rfl⟩, fun ⟨hj, hf, _⟩ => ⟨by omega, hf⟩⟩

/-- **`Empty`'s and `False`'s recorded clauses read their (no)
constructors with holes.** -/
theorem emptyLfp_readsHoles {nm : Name} {w : Nat} :
    ReadsHoles (emptyLfp (V := V) nm w) (holes0 0) := by
  intro ψ ρp _ X _ c _ t _ j fs
  show False ↔ (j < 0 ∧ _)
  exact ⟨False.elim, fun h => absurd h.1 (Nat.not_lt_zero j)⟩

end ConLeche.Model
