--#export reAndRecMustReject

/- End-to-end fixture (task #632), a must-reject control of `rec_eta`
   (lean4's `tests/elab/12520_2.lean`, `@And.rec = g`): `And.rec` with no
   argument, against a free `g`.  Where the expansion fires (`And`'s
   rescue), the reduct `intro t.1 t.2` still differs from `g … t`; it
   terminates.

   official (lean4 with #15374): 1.  con-leche: 1. -/

import Lean
open Lean Elab Command Meta

/-- `rfl_unchecked n : ∀ xs, a = b` adds the theorem `n` with the proof
`fun xs => Eq.refl a`, kernel check skipped. -/
elab "rfl_unchecked " n:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let val ← forallTelescope ty fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "expected an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let decl : Declaration := .thmDecl
      { name := n.getId, levelParams := [], type := ty, value := val }
    withOptions (debug.skipKernelTC.set · true) <| addDecl decl

rfl_unchecked reAndRecMustReject :
  ∀ (g : {a b : Prop} → {motive : a ∧ b → Sort 1} →
      ((left : a) → (right : b) → motive (And.intro left right)) → (t : a ∧ b) → motive t),
    @And.rec.{1} = @g
