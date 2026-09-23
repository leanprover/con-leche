module

public import ConLeche.SetModel.UnionRec
@[expose] public section

/-!
# Regime SQ: the class kit is the squash kit (task #315)

DESIGN "DESIGN DOCUMENT 2, v2" §3.4.  At `¬allProp ∧ w = 0` the guard
leaves a lone, non-nested block with at most one constructor under the
subsingleton criterion.  Every value of the carrier is then the point
(`mkZero`), so the major carries no information and the recursion runs
on the INDEX: the constructor's fields are a FUNCTION of its index
values (`srcVals`, the subsingleton criterion), and the predecessors
of an index tuple are the recursive calls' index tuples (`sqPred`),
accessible by the block's own lfp induction.

`BlockRecKitI`'s arm covers SQ unchanged: `famCand`/`famCand_hCand`
are stated over a `UnionRecKitC`, and the squash kit is one — only its
`pred` and its `acc` differ from regime WF's.  The kit's pieces are
`FixSquashI`'s (`isOfW`/`tupW`, `srcVals`, `sqSpine`, `sqPred`, the
accessibility argument).  The motive is read off the recursor's TYPE
(`RecFamData.hconcl`), and the step is the RESIDUE read at the source
spine: the lone minor is a prefix variable of the residue's own frame,
which is why the check never looks inside the `nP…rP-1` stretch.

This file adds the one SQ-specific projection the Model tier reads:
a tagged index's INDEX part.
-/

namespace ConLeche.Semantics

open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The tagged index's index part

`WfRec.lean` reads a tagged index's VALUE (`tagVal`, the payload the
∈-order is taken on).  Regime SQ reads its INDEX instead: at `w = 0`
the payload is the point and the index is what the recursion runs
on. -/

/-- The INDEX of a tagged recursion index `tagged c i x = ⟨c, i, x⟩`. -/
noncomputable def tagIdx (u : V) : V := sfst (ssnd u)

@[simp] theorem tagIdx_tagged (c : Nat) (i x : V) : tagIdx (tagged c i x) = i := by
  unfold tagIdx tagged
  rw [ssnd_kpair, sfst_kpair]

end ConLeche.Semantics
