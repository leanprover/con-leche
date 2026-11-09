--#export foo_unit bar_true pi_unit pi_unit_lam nest_unit dep_field_unit pi_field_unit struct_pi_unit

/- End-to-end fixture (task #515): the wider unit-like η of the official
   kernel since lean4#15372 (`is_unit_like`), ported from lean4's
   `tests/elab/2258.lean`.  A type is unit-like when its head normal
   form is a ∀ whose codomain is unit-like, or a non-recursive
   structure every field of whose constructor, at the instance's
   parameters, is a proposition or itself unit-like; any two
   inhabitants of a unit-like type are definitionally equal.

   * `foo_unit`: `Foo Nat Unit`, fields `B := Unit`, `Unit`, `True`,
     `Nat = Unit` — unit-like only at this instance (`Foo Nat Nat` is
     not: `unitlike_wide_foo_nat_bad`).
   * `bar_true`: a structure whose one field is a proposition.
   * `pi_unit`: `id (α → id Unit)`, a ∀ with a unit-like codomain
     behind a definition.
   * `pi_unit_lam`: a λ against a variable at a unit-like ∀ (η first).
   * `nest_unit`: unit-likeness through a structure field of a
     unit-like structure type (`Foo Nat (Foo Nat Unit)`).
   * `dep_field_unit`: a later field's type mentions an earlier field
     (`Dep`: `n : Unit`, `p : n = n`).
   * `pi_field_unit`: a field of ∀ type with a unit-like codomain.
   * `struct_pi_unit`: a ∀ ending in a unit-like structure.

   The v4.29.1 elaborator does not know the rule, so the statements are
   added with the kernel check skipped and the proof `Eq.refl p`.

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

structure Foo (A B : Type) where
  foo : B
  bar : Unit
  baz : True
  barf : A = B

structure Bar : Type where
  bar : True

structure Dep where
  n : Unit
  p : n = n

structure PiField where
  f : Nat → Unit
  g : (n : Nat) → Fin (n + 1) → Bar

rfl_unchecked foo_unit : ∀ (p q : Foo Nat Unit), p = q
rfl_unchecked bar_true : ∀ (p q : Bar), p = q
rfl_unchecked pi_unit : ∀ (α : Type) (p q : id (α → id Unit)), p = q
rfl_unchecked pi_unit_lam : ∀ (α : Type) (q q' : α → Bar), (fun x => q x) = q'
rfl_unchecked nest_unit : ∀ (p q : Foo Unit (Foo Unit Unit)), p = q
rfl_unchecked dep_field_unit : ∀ (p q : Dep), p = q
rfl_unchecked pi_field_unit : ∀ (p q : PiField), p = q
rfl_unchecked struct_pi_unit : ∀ (p q : Nat → Nat → Foo Bool Bool → Dep), p = q
