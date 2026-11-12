--#export whnfCoreMemoCheap
/- Task #572 (found in task #451): `whnf_core_memo` through the cheap
mode of `whnfCore` (definitional equality's `cheap_proj`).

  S   := (fun x => Bool.rec (motive := fun _ => Bool) false true x) true
  lhs := Bool.rec (motive := fun _ => Bool) S S S

The type check of `whnfCoreMemoCheap : lhs = true := Eq.refl true`
compares `true =?= lhs` and puts `lhs` through the cheap `whnfCore`.  Its
ι step normalizes the major `S` by `whnf` (the full mode, in both modes),
which stores `S`'s answer, and continues with the minor premise `S` in
the cheap mode.  The official kernel reads its one memo in both modes
and takes two `Bool.rec` steps.  con-leche's cheap mode reads a memo of
its own, which the full mode fills with the chains the two modes reduce
alike; `S`'s chain (a β step and an ι step) is one, so con-leche takes
two steps too (three before task #572).

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
  let value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  addDecl (.thmDecl { name := `whnfCoreMemoCheap, levelParams := [], type, value })
