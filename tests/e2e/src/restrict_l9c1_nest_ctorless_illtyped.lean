--#export T.rec T.rec_1
/- RESTRICT L9 C1 (kernel-level, `addDecl`): the L9 escape WITHOUT a member at
   other levels, through a CONSTRUCTOR-LESS container:
   `R0 (α : Prop) : Type` (no constructor), `T : Type | mk : R0 T → T`.
   The field's domain `R0 T` is ILL-TYPED (`T : Type`, `R0` wants a
   `Prop`).  Official: v4.29.0–v4.32.1 ACCEPT (the parameter never reaches
   the auxiliary type); v4.32.2+ REJECT ("application type mismatch",
   `inductive.cpp:1223–1231` type-checks the replaced nested applications
   `I Ds`); v4.33.1's `check_uniform_ind_occs` does not apply (`T` is
   applied uniformly).  No constructor of `R0` is typed at the frame, so
   only the container-application check rejects it.  Target: reject (1). -/
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
inductive R0 (α : Prop) : Type
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let ctorTy := Expr.forallE `a (mkApp (.const `R0 []) (.const `T [])) (.const `T []) .default
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1, ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
