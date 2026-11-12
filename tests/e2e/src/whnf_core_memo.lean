--#export whnfCoreMemo
/- Task #572 (found in task #451): the `whnfCore` memo is looked up at
every step of a reduction chain, as in the official kernel.

  S   := (fun x => Bool.rec (motive := fun _ => Bool) false true x) true
  lhs := Bool.rec (motive := fun _ => Bool) S S S

The type check of `whnfCoreMemo : lhs = true := Eq.refl lhs` puts `lhs`
through `whnf` (the full mode).  Its ι step normalizes the major `S` (a β
step, then one ι step), which stores `S`'s answer, and continues with the
minor premise, the same `S`, which the memo answers.  The official kernel
takes two `Bool.rec` steps; con-leche took three before task #572 (its
loop looked the memo up only at its entry).  `whnf_core_memo_cheap` is
the same through the cheap mode.  Both terms are built by `addDecl`, so no
elaboration reduces them first.

official: 0.  con-leche: 0. -/
import Lean
open Lean

run_meta do
  let motive := mkLambda `_ .default (mkConst ``Bool) (mkConst ``Bool)
  let recB (f t m : Expr) := mkApp4 (mkConst ``Bool.rec [1]) motive f t m
  let S := mkApp (mkLambda `x .default (mkConst ``Bool)
    (recB (mkConst ``false) (mkConst ``true) (.bvar 0))) (mkConst ``true)
  let lhs := recB S S S
  let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
  let value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) lhs
  addDecl (.thmDecl { name := `whnfCoreMemo, levelParams := [], type, value })
