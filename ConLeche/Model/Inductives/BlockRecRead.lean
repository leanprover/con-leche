module

import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Level
public import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.BasisEmpty
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
open ConLeche.Semantics (AnnotTerm)
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

/-! ## The finding, and its RESOLUTION in the kernel

`denoteMeta` does not respect `Expr.resetMeta`: `resetMeta` forces
every binder's datum to `⟨.never⟩`, whose bit is `1`, while a datum
that holds at `φ` reads `0`, and `interp` is not bit-blind —
`lamR`/`piR` take the bit.  So two `resetMeta`-equal expressions can
denote differently, which `not_denoteMeta_resetMeta_invariant` below
witnesses.

`blockIhCall?` (`Kernel/Inductives/BlockRec.lean`) used to recognise a
guarded recursive call up to exactly that relation, and its
comparison is the ONLY tie between the stored right-hand side's call
node and the spine the ι law is stated at — so a reading could not be
transported across it.  **The kernel comparison was strengthened**
(lane K2): the node and the generated spine are now compared EXACTLY,
binder data included (`e != expected`), and `blockIhCall?_spine`
(`Verify/Inductives/BlockRecInv.lean`) exports `e = expected` — so
the field's ANNOTATED index expressions in the call node are the
constructor's stored ones, syntactically.  The whole arena battery and
the whole e2e suite are unchanged by the strengthening (measured at
the k = 1 probe, with a negative control showing the comparison is
what those fixtures' rules pass).

The witness stays as the record of WHY the comparison is exact. -/
theorem not_denoteMeta_resetMeta_invariant :
    ∃ (e₁ e₂ : Expr) (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
      (φ : Name → Nat) (d : Nat),
      Expr.resetMeta e₁ = Expr.resetMeta e₂ ∧
      denoteMeta acval env φ d e₁ ≠ denoteMeta acval env φ d e₂ := by
  refine ⟨.lam (.sort .zero) (.sort .zero) ⟨ConLeche.PropWhen.never⟩,
    .lam (.sort .zero) (.sort .zero) ⟨ConLeche.PropWhen.ifAllZero []⟩,
    (fun _ _ => .prf), ⟨[]⟩, (fun _ => 0), 0, rfl, ?_⟩
  have e1 : ∀ pw : ConLeche.PropWhen,
      denoteMeta (fun _ _ => AnnotTerm.prf) (⟨[]⟩ : Env) (fun _ => 0) 0
          (Expr.lam (.sort .zero) (.sort .zero) ⟨pw⟩)
        = some (.lam (pwBit (fun _ => 0) pw) (.sort 0) (.sort 0)) := by
    intro pw
    rw [denoteMeta]
    simp [denoteMeta_sort, Expr.instantiate1, Level.eval]
  rw [e1, e1, pwBit_never, pwBit_ifAllZero_nil]
  simp

end ConLeche.Model
