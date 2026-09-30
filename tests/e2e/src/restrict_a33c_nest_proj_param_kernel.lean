--#export T.rec T.rec_1
/- RESTRICT a33c (kernel-level, `addDecl`; the ELABORATOR overflows on this
   block): `C (p : Nat × Type) | mk : Prod.snd p → C p`, `T | mk : C (1, T) → T`.
   The container's field needs δ (`Prod.snd`) and proj reduction to reach the
   member. -/
import Lean

open Lean in
/-- register the kernel-generated auxiliary recursors `T.rec_i` on the Lean side
    (the `inductive` elaborator's `addAuxRecs`, `Elab/MutualInductive.lean`) -/
def registerAuxRecs (T : Name) : CoreM Unit := do
  let mut i := 1
  while true do
    let auxRecName := T ++ `rec |>.appendIndexAfter i
    let env ← getEnv
    let some const := env.toKernelEnv.find? auxRecName | break
    let res ← env.addConstAsync auxRecName .recursor
    res.commitConst res.asyncEnv (info? := const)
    res.commitCheckEnv res.asyncEnv
    setEnv res.mainEnv
    i := i + 1
inductive C (p : Nat × Type) : Type where
  | mk : Prod.snd p → C p
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let pair := mkApp4 (.const `Prod.mk [.zero, .succ .zero]) (.const `Nat []) (.sort (.succ .zero)) (.lit (.natVal 1)) (.const `T [])
  let ctorTy := Expr.forallE `a (mkApp (.const `C []) pair) (.const `T []) .default
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
  IO.println s!"kernel contains T.rec_1: {(Lean.Kernel.Environment.find? (← getEnv).toKernelEnv `T.rec_1).isSome}"
