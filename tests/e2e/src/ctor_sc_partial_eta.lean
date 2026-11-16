--#export t t2
/- End-to-end fixture (task #592): a constructor applied to fewer than its
   parameters and fields is no target of the constructor shortcut.
   `@List.cons Nat 1` is a function, equal to its η-expansion
   `fun l => List.cons 1 l` by λ-η; the expansion's head normal form is a
   λ-expression, not a constructor application.  (The count probe of task
   #592 found this pair on `init-full`.)  `t2` has the sides swapped.
   Official accepts; con-leche accepts (the target verdict). -/
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

refl_thm t : (List.cons 1 : List Nat → List Nat) = fun l => List.cons 1 l
refl_thm t2 : (fun l => List.cons 1 l : List Nat → List Nat) = List.cons 1
