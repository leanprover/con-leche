--#export t t2 t3 t4
/- End-to-end fixture (task #592): the constructor shortcut skips `Nat`,
   whose constructor applications meet literals (`Nat.succ 999` against
   `1000`, `Nat.zero` against `0`) and the offset forms.  Official accepts;
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

refl_thm t : Nat.succ (Nat.succ Nat.zero) = 2
refl_thm t2 : (1000 : Nat) = Nat.succ 999
refl_thm t3 : Nat.zero = 0
refl_thm t4 : Nat.succ (1000 * 1000) = 1000001
