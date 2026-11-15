--#export t t2
/- End-to-end fixture (task #592): the constructor shortcut skips a family
   in `Prop`.  `P.a` and `P.b` are different constructors, and proof
   irrelevance equates them; a shortcut that read the two heads would answer
   `false`.  `t2` is the same at a family declared in `Sort u` and used at
   `u := 0` (`IndCaps.neverZero` is false there, so it is skipped too).
   Official accepts (the elaborator's kernel checks both); con-leche
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

inductive P : Prop where
  | a
  | b

-- `inductive Q : Sort u | a | b`, which the elaborator refuses (its sort
-- may be `Prop`) and the kernel takes
open Lean in
run_cmd Elab.Command.liftCoreM (addDecl (.inductDecl [`u] 0
  [{ name := `Q, type := .sort (.param `u),
     ctors := [{ name := `Q.a, type := .const `Q [.param `u] },
               { name := `Q.b, type := .const `Q [.param `u] }] }] false))

refl_thm t : (P.a : P) = P.b
refl_thm t2 : (Q.a : Q.{0}) = Q.b
