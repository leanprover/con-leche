--#export pi_bool

/- End-to-end fixture (task #515), a negative control of
   `unitlike_wide`: a ∀ whose codomain is not unit-like (`Nat → Bool`)
   is not unit-like, even with a unit-like domain.

   official (lean4 master): 1.  con-leche: 1. -/

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

rfl_unchecked pi_bool : ∀ (p q : Unit → Bool), p = q
