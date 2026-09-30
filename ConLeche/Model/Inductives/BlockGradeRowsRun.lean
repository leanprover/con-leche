module

import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.BlockLfpHoles
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.FixKit
import ConLeche.Verify.Inductives.RecStage

public section

/-!
# Grading the ι rule's constructor readings

Transports of `WellDenotedV` across the rule's lifts (the rule prefix's
non-parameter binders, the `K` chain binders of `chainFrame K a ρ`), and
the gradedness of the constructor's index readings (`blockCtorEs_wdV`)
and of the fired constructor application (`blockRuleMkAV_wdV`), both off
the constructor's stored type (`okTy`, `mem_type`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-! ## 1. Transports and the constructor's two graded readings -/

section CtorReadings

/-- **The chain lift, graded**: a form lifted past the `K` chain binders
at the frame's own depth is graded at the chain frame exactly when it
is at the base frame. -/
theorem wellDenotedV_liftN_chainFrame {K : Nat} {a ρ : Nat → V} (ws : List V)
    (e : AnnotTerm) :
    WellDenotedV V (consList ws (chainFrame K a ρ)) (e.liftN K ws.length)
      ↔ WellDenotedV V (consList ws ρ) e := by
  rw [WellDenotedV_liftN, chainFrame,
    shiftE_consList_ih (locals := ws) (ihvals := (List.range K).map a) rfl (by simp)]

end CtorReadings

end ConLeche.Model
