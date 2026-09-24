--#export T.rec T.rec_1
/- RESTRICT a28 (kernel-level, `addDecl`): the member at other levels inside a
   PHANTOM container's parameter: `P (α : Type) | mk : P α`,
   `T.{u} : Type | mk : P T.{0} → T.{u}`.  Official's aux constructor
   `_nested.P_1.mk : _nested.P_1` never sees `T.{0}`; accepted up to
   v4.33.0, rejected from v4.33.1 (`check_uniform_ind_occs`: "invalid
   occurrence of datatype 'T' being declared").  Ours: M2′, a reject. -/
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
inductive P (α : Type) : Type where
  | mk : P α
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let dom := mkApp (Expr.const `P []) (.const `T [.zero])
  let ctorTy := Expr.forallE `a dom (.const `T [u]) .default
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
#print T.rec
#print T.rec_1
