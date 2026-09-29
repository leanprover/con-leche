--#export T.rec
/- T (α : Type) | mk : List ((fun y => T y) α) → T α
   UNIFCHK (2026-09-29): a member uniform only after β, inside a container
   key.  Official 1; ours 1 (M3 before lane UNIFCHK, `nestUniform` since).
   TARGET 1. -/
import Lean
open Lean in
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

open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let T : Expr := .const `T []
  let dom := mkApp (.const `List [.zero]) (mkApp (Expr.lam `y (.sort 1) (mkApp T (.bvar 0)) .default) (.bvar 0))
  let ctorTy := Expr.forallE `α (.sort 1) (Expr.forallE `a dom (mkApp T (.bvar 1)) .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default, ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
