--#export T.rec
/- COMPLETE c03d_pi_depth_1030 (kernel-level): T | leaf | mk : (flat) (Nat → … → T) → T with 1030 Π binders. -/
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
  let d := (List.range 1030).foldl (fun acc _ => Expr.forallE `n (.const `Nat []) acc .default) T
  let dom := d
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1, ctors := [
      { name := `T.leaf, type := T },
      { name := `T.mk, type := .forallE `a dom T .default }] }] false
  registerAuxRecs `T
