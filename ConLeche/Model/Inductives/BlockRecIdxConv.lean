module

public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Annot.BitInst

public section

/-!
# The recursor's INDEX binders ARE the member's index telescope — at the model

Stage (b'') (`targetIdxDoms`, `Kernel/Inductives/RecCheck.lean`)
compares each recursor's index binder domains, binder by
binder, with the eliminated member's index telescope opened at the
recursor's own numbering (`openPisParamsIdx`).  This file is that
check's model side: the CONVERSE of the recursor type's index clause
(`blockRecIdxFit_run` is the forward one), which is what the kit
regimes' `hconclTy` needs — a carrier element's index values fit the
MEMBER's telescope, and the recursor's conclusion is licensed only at a
fit of the RECURSOR's binder data.

Two pieces (the pass's inversion is the family record's `idxDoms`,
`Verify/Inductives/RecStage.lean`):

* `defeqDom_agree_at` — ONE position of a binder-by-binder `isDefEq`,
  read at a context that is NOT an opening of either compared type.
  §35's certified hop (`prefixDoms_agree`) reads at the first
  opening's own context; here the two telescopes live at different
  numberings, so the context is built from the recursor's prefix and
  the member's (lifted) indices, and both subjects are correlated with
  it through `ctxOk_of_openers_congr`;
* `blockRecIdxConv_run` — the converse at the run, by induction on the
  index position; the parameter positions are §35's hop
  (`prefixDoms_agree` at the parameter comparison stage (b) makes).

**The frame.**  A `DefEqClaim` concludes at the frames satisfying the
context it was run under and nowhere else, and the context here is the
recursor's rule PREFIX followed by the member's indices.  So the
converse is stated at a prefix that FITS the recursor's prefix domains
— which is exactly what every consumer has in hand (the kit's class
index set is guarded by that fit, `blockRecIs_fits`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 3. Small list and frame helpers -/

section Helpers

omit [SetTheory V] in
/-- A `liftDomsK` entry is the entry lifted at its own cutoff. -/
theorem liftDomsK_getD (K : Nat) :
    ∀ (k : Nat) (Ds : List AnnotTerm) (l : Nat), l < Ds.length →
      (liftDomsK K k Ds).getD l default = (Ds.getD l default).liftN K (k + l)
  | _, [], _, h => absurd h (Nat.not_lt_zero _)
  | k, D :: Ds, 0, _ => by simp [liftDomsK]
  | k, D :: Ds, l + 1, h => by
    show (liftDomsK K (k + 1) Ds).getD l default = _
    rw [liftDomsK_getD K (k + 1) Ds l (by simpa using h)]
    simp only [List.getD_cons_succ]
    rw [show k + 1 + l = k + (l + 1) from by omega]

end Helpers

end ConLeche.Model
