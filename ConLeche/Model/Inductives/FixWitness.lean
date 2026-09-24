module

public import ConLeche.Model.Inductives.FixChains
public section

/-!
# The recursive flags against `recAt`

What survives of the fixpoint route's slot witness (the closure witness
is now the hole operator's, `Model/Annot/LfpHoleWitness.lean`): a
position is recursive exactly where the kinds' recursive flag is set.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

omit [SetTheory V] in
theorem recAt_iff_rsOf {nP i : Nat} {ks : List RecFieldKind} (hi : i < ks.length) :
    recAt nP ks (nP + i) ↔ (rsOf ks).getD i false = true := by
  rw [rsOf_getD_iff hi]
  unfold recAt
  rw [Nat.add_sub_cancel_left]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_add_right _ _, h⟩⟩

end ConLeche.Model
