--#export pc_val pc_val_lam pc_two pc_unit

/- End-to-end fixture (task #515): η for a partially applied structure
   constructor (official's `try_eta_struct_core` since lean4#15373),
   ported from lean4's `tests/elab/12520_1.lean`.  When the constructor
   side lacks arguments, the two sides' types are compared and both are
   applied to fresh variables up to the full application, which is then
   compared field by field with the other side's projections.

   * `pc_val`: `T.mk (x True.intro).val =?= x` at `True → T`: the
     expansion compares `(x h).1` with `(x True.intro).val` (proof
     irrelevance on the argument) and `(x h).2` with `h`.
   * `pc_val_lam`: the same against `fun h => x h` (η first).
   * `pc_two`: two missing fields, `Q.mk =?= f` at `True → True → Q`
     (both fields proofs).
   * `pc_unit`: with the wider unit-like η (lean4#15372): the missing
     field has the unit-like type `Bar`, and the expansion compares
     `(f x).w` with `(f ⟨trivial⟩).w` (arguments at `Bar`) and `(f x).u`
     with `x`.

   official (lean4 master): 0.  con-leche: 0. -/

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

structure T where
  val : Bool
  proof : True

structure Q where
  p1 : True
  p2 : True

structure Bar where
  bar : True

structure W where
  w : Bool
  u : Bar

rfl_unchecked pc_val : ∀ (x : True → T), T.mk (x True.intro).val = x
rfl_unchecked pc_val_lam : ∀ (x : True → T), T.mk (x True.intro).val = (fun h => x h)
rfl_unchecked pc_two : ∀ (f : True → True → Q), Q.mk = f
rfl_unchecked pc_unit : ∀ (f : Bar → W), W.mk (f ⟨trivial⟩).w = f
