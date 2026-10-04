module

public import ConLeche.Model.Annot.BlockLfp
import ConLeche.SetModel.HoleClose

public section

/-!
# The lfp clause with HOLES: the container case of the carrier's growth

The clause (`BlockLfp.lean`) carries the hole reading of the stored
constructors and its fibre in hole form (`LfpClause.fibre_holes`).  The
operator's monotonicity is the fit's accessibility's (`LfpClause.mono`,
tasks #326/#327); this module keeps the one growth fact the recursor's
frames read:

* **The container case** (`LfpClause.carrier_le_on_group'`): a stored
  container's reached group-mates, read at two parameter frames, grow
  as soon as the hole fit at the larger carrier on the group does
  (`lfpTuple_le_on`).  No premise "C is monotone in its parameter"
  (charter item 4): the comparison is of THIS instantiation's two
  frames, and the only container facts used are its clause's closure
  and monotonicity in its own holes (both derived: `LfpClause.closed`,
  `LfpClause.mono`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The container case -/

namespace LfpClause

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}

open Classical in
/-- **The carrier below on a group, with the index sets agreeing on `G` only**:
the frame's key checks the index telescopes of the
REACHED group-mates alone (`nestInstType`'s N2), so only they are known
to have the same index sets at the two parameter frames.  The bound is
taken at the tuple that is the larger carrier on `G` and the smaller one
elsewhere, which lies in the smaller frame's tuple space. -/
theorem carrier_le_on_group' (h : LfpClause acval D) {ψ : Name → Nat} {ρp ρp' : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (hs' : Sat V (D.params ψ).reverse ρp')
    (G : Nat → Prop) (hidx : ∀ g, g < D.N → G g → D.idx ψ ρp g = D.idx ψ ρp' g)
    (hwalk : ∀ g, g < D.N → G g → ∀ t, t ∈ˢ D.idx ψ ρp g → ∀ j fs,
      D.HFits ψ ρp (fun x => if G x then D.carrier ψ ρp' x else D.carrier ψ ρp x) t g j fs →
      D.HFits ψ ρp' (D.carrier ψ ρp') t g j fs) :
    ∀ g, g < D.N → G g → FamLe (D.idx ψ ρp g) (D.carrier ψ ρp g) (D.carrier ψ ρp' g) := by
  have hmono := h.mono hs
  have hcl := h.closed hs
  let B : Nat → V := fun x => if G x then D.carrier ψ ρp' x else D.carrier ψ ρp x
  have hB : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) B := by
    intro m hm
    by_cases hGm : G m
    · simp only [B, ite_eq_left hGm, hidx m hm hGm]; exact lfpTuple_mem _ _ _ _ m hm
    · simp only [B, ite_eq_right hGm]; exact lfpTuple_mem _ _ _ _ m hm
  have hle := lfpTuple_le_on hcl hmono G hB fun g hg hG t ht x hx => ?_
  · intro g hg hG
    have := hle g hg hG
    simp only [B, ite_eq_left hG] at this
    exact this
  · change x ∈ˢ app (D.Φ ψ ρp (fun x => if G x then B x else D.carrier ψ ρp x) g) t at hx
    have hZeq : (fun x => if G x then B x else D.carrier ψ ρp x)
        = fun x => if G x then D.carrier ψ ρp' x else D.carrier ψ ρp x := by
      funext x; by_cases hx : G x <;> simp [B, hx]
    rw [hZeq] at hx
    have hZ : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp)
        (fun x => if G x then D.carrier ψ ρp' x else D.carrier ψ ρp x) := hB
    obtain ⟨j, fs, hf, rfl⟩ := (h.fibre_holes hs hZ hg ht x).mp hx
    have hf' := hwalk g hg hG t ht j fs hf
    simp only [B, ite_eq_left hG]
    rw [← h.carrier_eq hs' hg]
    exact (h.fibre_holes hs' (lfpTuple_mem _ _ _ _) hg (by rw [← hidx g hg hG]; exact ht) _).mpr
      ⟨j, fs, hf', rfl⟩

end LfpClause

end ConLeche.Model
