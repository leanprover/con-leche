--#export foo_nat

/- End-to-end fixture (task #515), the negative control of
   `unitlike_wide` (lean4's `tests/elab/2258.lean`): `Foo Nat Nat` is
   not unit-like (its field `foo : Nat` is neither a proposition nor
   unit-like), so `p = q := Eq.refl p` is not a definitional equality.

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

structure Foo (A B : Type) where
  foo : B
  bar : Unit
  baz : True
  barf : A = B

rfl_unchecked foo_nat : ∀ (p q : Foo Nat Nat), p = q
