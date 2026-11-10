--#export etaExplicitMustReject

/- End-to-end fixture (task #515), the negative control of
   `eta_partial_ctor` (lean4's `tests/elab/12520_1.lean`): an arbitrary
   `f : Bool → Box` is not `Box.mk`: the expansion compares `(f x).val`
   with `x`, which differ.

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

structure EtaAdmissionBox where
  val : Bool

rfl_unchecked etaExplicitMustReject : ∀ (f : Bool → EtaAdmissionBox), f = EtaAdmissionBox.mk
