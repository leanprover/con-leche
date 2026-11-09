--#export par_unit par_unit_poly par_unit_pi nest_par_unit nest_par_unit_dep

/- End-to-end fixture (task #515, review round 2): the unit-like test at
   fieldless structures with parameters, alone and inside a unit-like
   structure.  Official's `is_unit_like` has one path for every
   non-recursive structure: the constructor's fields after the
   parameters, each a proposition or unit-like — for a fieldless one,
   none.  con-leche reads the constructor and the field count off the
   structure's projection table, which a fieldless structure has too.

   * `par_unit`: `E Nat`, a fieldless structure with a parameter.
   * `par_unit_poly`: `EU.{u} α`, universe-polymorphic, a parameter.
   * `par_unit_pi`: `Nat → E Bool`, a ∀ ending in one.
   * `nest_par_unit`: `W Nat`, whose fields are `E α`, `EU α` and a
     proposition — unit-like through two fieldless structures with
     parameters.
   * `nest_par_unit_dep`: `WD Nat`, a later field's type mentions an
     earlier fieldless one (`h : e = e`).

   The v4.29.1 elaborator does not know the wider rule, so the
   statements are added with the kernel check skipped and the proof
   `Eq.refl p`.

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
      { name := n.getId, levelParams := (collectLevelParams {} ty).params.toList,
        type := ty, value := val }
    withOptions (debug.skipKernelTC.set · true) <| addDecl decl

structure E (α : Type) : Type

universe u

structure EU (α : Type u) : Type u

structure W (α : Type) : Type where
  e : E α
  eu : EU α
  t : True

structure WD (α : Type) : Type where
  e : E α
  h : e = e

rfl_unchecked par_unit : ∀ (p q : E Nat), p = q
rfl_unchecked par_unit_poly : ∀ (α : Type u) (p q : EU.{u} α), p = q
rfl_unchecked par_unit_pi : ∀ (p q : Nat → E Bool), p = q
rfl_unchecked nest_par_unit : ∀ (p q : W Nat), p = q
rfl_unchecked nest_par_unit_dep : ∀ (p q : WD Nat), p = q
