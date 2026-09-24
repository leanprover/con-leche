--#export T.rec
/- COMPLETE c05b (kernel-level): List^30 (Nat → … (1000 binders) → T): container descents and
   Π bodies share the per-field positivity fuel (1024); 30 aux types only for official. -/
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
set_option maxRecDepth 100000
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let T : Expr := .const `T []
  let d := (List.range 1000).foldl (fun acc _ => Expr.forallE `n (.const `Nat []) acc .default) T
  let d := (List.range 30).foldl (fun acc _ => mkApp (.const `List [.zero]) acc) d
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1, ctors := [
      { name := `T.leaf, type := T },
      { name := `T.mk, type := .forallE `a d T .default }] }] false
  registerAuxRecs `T
