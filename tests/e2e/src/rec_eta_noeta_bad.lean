--#export reNoEtaMustReject

/- End-to-end fixture (task #632), a must-reject control of `rec_eta`:
   the recursor of a family with two constructors (neither K nor η) is not
   η-expanded (official's gate), and at a fresh major its ι step could not
   fire anyway: `Two.rec (f .a) (f .b)` is not `f` definitionally.

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

inductive Two where
  | a
  | b

rfl_unchecked reNoEtaMustReject : ∀ (f : Two → Bool),
  @Two.rec (fun _ => Bool) (f Two.a) (f Two.b) = f
