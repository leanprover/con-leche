--#export t
/- End-to-end fixture (task #592): `decide (2 + 2 = 5)` head-normalises to
   `false`, another constructor than `true`: the constructor shortcut
   answers `false` at once.  Official rejects (`debug.skipKernelTC` keeps
   the elaborator's kernel off it); con-leche rejects (the target
   verdict). -/
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

set_option debug.skipKernelTC true
refl_thm t : decide (2 + 2 = 5) = true
