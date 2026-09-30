--#export T.rec T.rec_1
/- COMPLETE m3 (kernel-level): a member under a PROJECTION inside a
   CONTAINER PARAMETER: `T : Type | mk : List ((T, Nat).1) → T` (a raw
   `.proj Prod 0`).  Official (v4.29.1, v4.33.0, v4.34.0 — probed) ACCEPTS:
   `check_uniform_ind_occs` descends into the projection, the auxiliary
   type's field reduces to `T` (`is_valid_ind_app`).  Ours: the walk's M3
   check (`Expr.holesApplied`, `nestMemberCtor`) descends into the
   projection as official's `for_each` does.  Today 0, target 0,
   official 0.  Rejected twins: `complete_m3_proj_unapplied`,
   `complete_m3_proj_phantom`. -/
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
  let pr := mkApp4 (.const `Prod.mk [.succ .zero, .succ .zero]) (.sort 1) (.sort 1) T
    (.const `Nat [])
  let dom := mkApp (.const `List [.zero]) (.proj `Prod 0 pr)
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1, ctors := [
      { name := `T.mk, type := .forallE `a dom T .default }] }] false
  registerAuxRecs `T
