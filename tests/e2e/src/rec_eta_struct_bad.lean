--#export reProdSwapMustReject

/- End-to-end fixture (task #632), a must-reject control of `rec_eta`:
   `Prod.rec` is η-expanded and ι-reduced at a fresh pair `p` to
   `a (p.2, p.1)`, which is not `a p`.

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

rfl_unchecked reProdSwapMustReject : ∀ (a : Bool × Bool → Bool),
  @Prod.rec Bool Bool (fun _ => Bool) (fun b c => a (c, b)) = a
