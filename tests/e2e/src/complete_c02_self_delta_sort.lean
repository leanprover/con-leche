--#export T.rec T.rec_1
/- COMPLETE c02 (kernel-level): the BLOCK's own type behind δ: `T : MyType`,
   `MyType := Type`, nested through List. -/
import Lean
def MyType : Type 1 := Type
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
  let lstT := mkApp (.const `List [.zero]) T
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .const `MyType [], ctors := [
      { name := `T.leaf, type := T },
      { name := `T.mk, type := .forallE `a lstT T .default }] }] false
  registerAuxRecs `T
