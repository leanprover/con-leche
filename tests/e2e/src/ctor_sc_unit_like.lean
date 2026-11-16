--#export t t2
/- End-to-end fixture (task #592): the constructor shortcut skips a
   unit-like type.  `U.mk` and `V.v` are closed constructor applications of
   types with one constructor and no fields; the other sides are stuck
   opaque constants, equal by unit-like η.  Official accepts; con-leche
   accepts (the target verdict). -/
import Lean

open Lean Elab Command Term Meta in
/-- `refl_thm n : l = r` adds the theorem `n : l = r := Eq.refl l` as it
stands, without the elaborator deciding the equation. -/
elab "refl_thm " n:ident " : " eq:term : command => liftTermElabM do
  let ty ← elabType eq
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let some (α, l, _) := ty.eq? | throwError "refl_thm: expected an equation"
  let u ← instantiateLevelMVars (← getLevel α)
  addDecl (.thmDecl { name := n.getId, levelParams := [], type := ty,
                      value := mkApp2 (mkConst ``Eq.refl [u]) α l })

structure U where

inductive V where
  | v

opaque u : U := ⟨⟩
opaque w : V := .v

refl_thm t : U.mk = u
refl_thm t2 : w = V.v
