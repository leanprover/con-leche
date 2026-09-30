--#export T.rec

/- RESTRICT b02, the GOOD half: `T.{u}` with its would-be occurrence at
   OTHER universe levels pointed at the unrelated `BPin.{v}`, used at
   `BPin.{0}`.  The forged twin `restrict_b02_m2prime_direct_bad`
   (`scripts/mk_restrict_bad.py`) repoints `BPin` to `T` inside `T`'s
   block, keeping the levels, giving `mk : T.{0} → T.{u}` — the member at
   other levels as the field itself (the half of M2′ official shares).
   Official (Lean v4.29.1, handed to the kernel by `addDecl`; the
   elaborator cannot write `T.{0}` for the type being defined) REJECTS
   it: "(kernel) arg #1 of 'T.mk' contains a non valid occurrence of the
   datatypes being declared" (`is_valid_ind_app` compares the constant
   WITH its levels, inductive.cpp:341). -/

import Lean

inductive BPin.{w} : Sort (max 1 w) where
  | pin : BPin
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let ctorTy := Expr.forallE `a (.const `BPin [.zero]) (.const `T [u]) .default
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := ctorTy }] }] false
