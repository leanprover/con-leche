--#export T.rec T.rec_1
/- M3PROJ (kernel-level, adversarial twin of `complete_m3_proj_param`): a
   member UNAPPLIED under a PROJECTION in a container's parameter:
   `T (α : Type) : Type | mk : List ((T, α).1 α) → T α` (a raw
   `.proj Prod 0`; `T` bare inside the pair, applied to `α` only after
   the projection).  Official v4.34.0 REJECTS (`check_uniform_ind_occs`
   descends into the projection and finds `T` with no argument).  Ours:
   the walk's M3 (`Expr.holesApplied`) descends into the projection as
   official does and rejects the bare hole. -/
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
  let a : Expr := .bvar 0
  let pr := mkApp4 (.const `Prod.mk [.succ .zero, .succ .zero])
    (.forallE `x (.sort 1) (.sort 1) .default) (.sort 1) T a
  let dom := mkApp (.const `List [.zero]) (mkApp (.proj `Prod 0 pr) a)
  let ctorTy := Expr.forallE `α (.sort 1)
    (Expr.forallE `a dom (mkApp T (.bvar 1)) .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default,
       ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
