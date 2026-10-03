module

public import ConLeche.Model.Annot.BlockLfp
public import ConLeche.Semantics.Inductives.HoleMono
import ConLeche.SetModel.HoleClose

public section

/-!
# The lfp clause with HOLES: what positivity needs from it

Charter item 2: "every stored `I p⃗` is the least fixed point of its
right-hand-side operator: the interpretation of its constructor types
with holes at the block's members … Monotonicity is DERIVED FROM
POSITIVITY".  The clause (`BlockLfp.lean`) carries the hole reading of
the stored constructors (`LfpDatum.fields`/`resIdx`, the hole frame
`LfpDatum.frame`), and its fibre in hole form (`LfpClause.fibre_holes`:
the fibre is the injections of the spines fitting those readings at the
hole frame).  This module proves, against it, the facts
positivity must deliver:

* **Positivity of a constructor** along a frame relation (`CtorPos`)
  and the hole fit's growth along it (`LfpDatum.hfits_mono`).
* **The consumer** (`monoTuple_of_holes`): the operator is monotone
  as soon as every field reading is `MonoOn` the hole order
  — which is what the run of `nestPos` on the field delivers.  The
  install reads it at the constructors' stage (`BlockCtorsStage.holeFun`);
  the recorded clause records only the fit's growth (`fitsMono`) and
  derives the operator's monotonicity from it (`LfpClause.mono`, task
  #326).
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

/-! ## The interface

The hole reading itself — the fields with holes (`LfpDatum.fields`), the
result index readings (`resIdx`), the hole frame (`LfpDatum.frame`), the
hole fit (`HFits`) — is part of the datum and the clause
(`Annot/BlockLfp.lean`).  What positivity adds
is the relation along which a constructor is positive. -/

namespace LfpDatum

variable (D : LfpDatum V)

/-- **Positivity of a constructor along a frame relation**: every field
positive under its predecessors, every result index hole-free below
them. -/
@[expose] def CtorPos (R : FrameRel V) (ψ : Name → Nat) (c j : Nat) : Prop :=
  TeleMonoOn R (D.fields ψ c j) ∧
    ∀ e ∈ D.resIdx ψ c j, ConstOn (R.underTele (D.fields ψ c j)) e

variable {D}

/-- **The hole fit grows along a frame relation** at which the
constructor is positive. -/
theorem hfits_mono {R : FrameRel V} {ψ : Name → Nat} {c j : Nat} (hpos : D.CtorPos R ψ c j)
    {ρp ρp' X X' : Nat → V} (hR : R (D.frame ψ ρp X) (D.frame ψ ρp' X')) {t : V} {fs : List V}
    (h : D.HFits ψ ρp X t c j fs) : D.HFits ψ ρp' X' t c j fs := by
  obtain ⟨hj, hsp, hres⟩ := h
  refine ⟨hj, spineFit_mono _ hpos.1 hR hsp, fun l hl => ?_⟩
  obtain ⟨e, he, heq⟩ := hres l hl
  refine ⟨e, he, ?_⟩
  rw [← heq]
  exact (hpos.2 e (List.mem_of_getElem? he) _ _ (FrameRel.underTele_consList _ fs hR hsp)).symm

end LfpDatum

/-! ## The consumer: the operator is monotone, from the field readings -/

/-- **The block's operator is monotone**, DERIVED: from the fibre law,
the clause's link to the hole reading, and positivity of every constructor along the hole order `R`
(the frames of two ordered tuples are `R`-related).  The positivity
premise is what `nestPos`'s run on each field delivers. -/
theorem monoTuple_of_holes {D : LfpDatum V}
    {ψ : Name → Nat} {ρp : Nat → V}
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs)
    (R : FrameRel V)
    (hR : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X →
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y → TupleLe D.N (D.idx ψ ρp) X Y →
      R (D.frame ψ ρp X) (D.frame ψ ρp Y))
    (hpos : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.CtorPos R ψ c j) :
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) := by
  intro X Y hX hY hXY
  refine tupleLe_of_fibre (hfib X hX) (hfib Y hY) fun c hc t ht j fs hf => ?_
  exact LfpDatum.hfits_mono (hpos c hc j hf.1) (hR X Y hX hY hXY) hf

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
    · simp only [B, if_pos hGm, hidx m hm hGm]; exact lfpTuple_mem _ _ _ _ m hm
    · simp only [B, if_neg hGm]; exact lfpTuple_mem _ _ _ _ m hm
  have hle := lfpTuple_le_on hcl hmono G hB fun g hg hG t ht x hx => ?_
  · intro g hg hG
    have := hle g hg hG
    simp only [B, if_pos hG] at this
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
    simp only [B, if_pos hG]
    rw [← h.carrier_eq hs' hg]
    exact (h.fibre_holes hs' (lfpTuple_mem _ _ _ _) hg (by rw [← hidx g hg hG]; exact ht) _).mpr
      ⟨j, fs, hf', rfl⟩

end LfpClause


end ConLeche.Model
