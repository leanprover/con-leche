module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.Level
import ConLeche.Verify.Inductives.BlockRecInv

public section

/-!
# The recursor stage's READINGS (task #315, milestone M5, the Model half)

What `blockRecStaged_of`'s two open premises
(`Model/Inductives/BlockStageRec.lean`) are made of: the recursors'
stored types read to a Π-tower whose binder data is the semantics
tier's `rds`, the rule's prefix binders read to the SAME data (G2), and
the stored right-hand side's body reads to the residue at the `ih`
openers' values (O-1).

**D-d first**, because it is one line and the whole family's level
arithmetic rests on it: `checkBlockRecElimAgree` compares the sorts the
kernel's own sort check gave the recursors' CONCLUSIONS, and
`blockRecElimAgree_inv` (`Verify/Inductives/BlockRecInv.lean`) exposes
that comparison as `Level.isEquiv`.  The model does not consume
`isEquiv`; it consumes `Level.eval` at a ground assignment, which is
what `Level.isEquiv_sound` turns it into.  With that, a family has ONE
elimination level — `M5m`'s `OneElimLevel` at the family's single `ℓ`.
-/

namespace ConLeche.Model

open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

/-! ## D-d, at the valuation -/

/-- **One elimination level per family, at a ground assignment.**
`blockRecElimAgree_inv` gives the check's own verdict
(`Level.isEquiv`); this is the form the model reads — every recursor's
conclusion sort EVALUATES to the first one's at every `ψ`, so the
Σ'-chain has one level and the candidate one tower bit. -/
theorem blockRecElimAgree_eval {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) : ∀ u ∈ us, u.eval ψ = (us.headD .zero).eval ψ :=
  fun u hu => Level.isEquiv_sound (ConLeche.blockRecElimAgree_inv h u hu) ψ

/-- The same, between any two of the family's conclusions. -/
theorem blockRecElimAgree_eval_pair {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) {u v : Level} (hu : u ∈ us) (hv : v ∈ us) :
    u.eval ψ = v.eval ψ :=
  (blockRecElimAgree_eval h ψ u hu).trans (blockRecElimAgree_eval h ψ v hv).symm

/-- **The zeroness bit is the family's**, which is exactly the shape
`OneElimLevel` (`Semantics/Tower/BlockRecKitI.lean`) asks for once the
recursors' conclusions' sorts are the readings' binder numerals: at
the family's single `ℓ := (us.headD .zero).eval ψ`, a conclusion sort
is zero iff `ℓ` is. -/
theorem blockRecElimAgree_zero_iff {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) {u : Level} (hu : u ∈ us) :
    ((us.headD .zero).eval ψ = 0 ↔ u.eval ψ = 0) := by
  rw [blockRecElimAgree_eval h ψ u hu]

end ConLeche.Model
