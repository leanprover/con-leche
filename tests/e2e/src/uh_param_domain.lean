--#export T.rec
/- T (α : Type) | mk : (α : (fun _ => Type) (T Nat)) → T α  (the ctor's param domain)
   UNIFCHK (2026-09-29): a member in the constructor's PARAMETER domain.
   Official v4.33.1+ rejects (every occurrence at offset < nparams);
   ≤ v4.33.0 accepts.  Ours: 0 before lane UNIFCHK (the walk never reads the
   parameter domains), 1 since (`nestUniform`).  TARGET 1. -/
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
  let pdom := mkApp (Expr.lam `y (.sort 1) (.sort 1) .default) (mkApp T (.const `Nat []))
  let ctorTy := Expr.forallE `α pdom (mkApp T (.bvar 0)) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default, ctors := [{ name := `T.mk, type := ctorTy }] }] false
