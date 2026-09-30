--#export T.rec T.rec_1
/- L9FIX C2 (kernel-level, `addDecl`): C1 with a phantom container that
   HAS a constructor: `R (α : Prop) : Type | mk : R α`,
   `T : Type | mk : R T → T`.  The field's domain `R T` is ILL-TYPED.
   Official: v4.29.0–v4.32.1 ACCEPT; v4.32.2+ REJECT ("application type
   mismatch", `inductive.cpp:1223–1231`).  Here the instantiated container
   constructor `R.mk T`, typed at the frame, already fails.  Target:
   reject (1). -/
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
inductive R (α : Prop) : Type | mk : R α
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let ctorTy := Expr.forallE `a (mkApp (.const `R []) (.const `T [])) (.const `T []) .default
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1, ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
