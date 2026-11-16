--#export t t2
/- End-to-end fixture (task #592): the constructor shortcut skips a
   structure.  `S.mk ax.x ax.y` is a closed, fully applied constructor
   application, and the other side, the opaque constant `ax`, is stuck;
   structure η equates them.  `t2` has the constructor application on the
   left.  Official accepts; con-leche accepts (the target verdict). -/
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

structure S where
  x : Nat
  y : Bool

opaque ax : S := ⟨1, true⟩

refl_thm t : S.mk ax.x ax.y = ax
refl_thm t2 : ax = S.mk ax.x ax.y
