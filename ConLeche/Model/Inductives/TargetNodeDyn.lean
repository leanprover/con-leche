module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Inductives.TargetNodeList

public section

/-!
# The node presentation's DYNAMIC part: the generic piece

`TgtNodeDyn` (`TargetNodeList.lean`) asks, at every node of the list, the
kit's `trans`: a spine fitting at an ADMISSIBLE frame of the node, at a
hole tuple below the node's true carrier, fits at the true frame and
carrier.  At a derived node (a container instantiation) this is the
frame's monotonicity in its key's parameters — `FrameMono`, the
positivity derivation's conclusion at the frame — along a hole relation
from the admissible valuation of the node's frame stack to the TRUE one.
This module supplies the generic piece:

* `trans_of_frameConcl` — `trans` from `FrameMono`'s conclusion (at the
  group tuple `grpTuple`) when the group is the container's WHOLE
  recorded block and the block has no instance components (`LfpCover.wid`):
  the clause's `fitsMono` along `Y ≤ carrier`, then the fit's dependence
  on the members only (`LfpDatum.hfits_congr_members`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps grpNews)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `trans` from the frame's conclusion -/

section Trans

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V} {ψ : Name → Nat}

/-- **`trans` at a derived node from `FrameMono`'s conclusion**: the frame's
group covers every member (`hall`) and the operator is as wide as its
members (`hwid`); the admissible frame `ρs` reads the true frame `ρt`'s
index sets.  A spine fitting at `ρs` and a tuple `Y` below the true
carrier fits at `ρs` and the true carrier (`fitsMono`), hence at `ρs` and
the group tuple (they agree on the members), hence — the frame's
conclusion — at the true frame and carrier. -/
theorem trans_of_frameConcl (hcl : LfpClause acval D) (hwid : D.N = D.k)
    {grp : List (Name × Expr)} (hall : ∀ c, c < D.k → InGrp D grp c) {ρs ρt : Nat → V}
    (hconcl : ∀ g, InGrp D grp g → ∀ t j fs,
      D.HFits ψ ρs (grpTuple D ψ grp ρs ρt) t g j fs → D.HFits ψ ρt (D.carrier ψ ρt) t g j fs)
    (hsat : Sat V (D.params ψ).reverse ρs) (hidx : ∀ c, c < D.N → D.idx ψ ρs c = D.idx ψ ρt c)
    {Y : Nat → V}
    (hY : InTupleSpace (D.w ψ) D.N (D.idx ψ ρt) Y)
    (hle : TupleLe D.N (D.idx ψ ρt) Y (D.carrier ψ ρt)) {t : V} {c j : Nat} {fs : List V}
    (hc : c < D.N) (hf : D.HFits ψ ρs Y t c j fs) : D.HFits ψ ρt (D.carrier ψ ρt) t c j fs := by
  have hC : InTupleSpace (D.w ψ) D.N (D.idx ψ ρs) (D.carrier ψ ρt) := fun m hm => by
    rw [hidx m hm]; exact lfpTuple_mem _ _ _ _ m hm
  have hY' : InTupleSpace (D.w ψ) D.N (D.idx ψ ρs) Y := fun m hm => by
    rw [hidx m hm]; exact hY m hm
  have hle' : TupleLe D.N (D.idx ψ ρs) Y (D.carrier ψ ρt) := fun m hm => by
    rw [hidx m hm]; exact hle m hm
  have h1 := hcl.fitsMono ψ ρs hsat Y _ hY' hC hle' c hc t j fs hf
  have hck : c < D.k := hwid ▸ hc
  refine hconcl c (hall c hck) t j fs ((LfpDatum.hfits_congr_members fun m hm => ?_).mp h1)
  unfold grpTuple
  rw [if_pos (hall m hm)]

end Trans

end ConLeche.Model
