--#export t t2
/- End-to-end fixture (task #592): the constructor shortcut's own branch.
   The left sides head-normalise to the right side's constructor, and the
   comparison continues on the normal form (`t`: the right side is the
   constructor application; `t2`: the left side is).  Official accepts;
   con-leche accepts (the target verdict). -/
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

refl_thm t : List.map (· + 1) [1, 2, 3] = [2, 3, 4]
refl_thm t2 : [2, 3, 4] = List.map (· + 1) [1, 2, 3]
