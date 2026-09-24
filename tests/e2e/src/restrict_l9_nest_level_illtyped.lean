--#export T.rec T.rec_1
/- LEVELBUG-O L9 (kernel-level, `addDecl`): a member at OTHER levels as a
   nested container's parameter, where the container's sort is its
   parameter's: `Q.{w} (α : Sort w) : Sort w | mk : Q α` (phantom),
   `T.{u} : Sort u | mk : Q.{u} T.{0} → T.{u}`.  The field's domain
   `Q.{u} T.{0}` is ILL-TYPED for u ≠ 0 (`T.{0} : Prop`, `Q.{u}` wants
   `Sort u`).  Official: v4.29.0–v4.32.1 ACCEPT (the parameter never
   reaches the auxiliary type, so it escapes type checking); v4.32.2–
   v4.33.0 REJECT ("application type mismatch", `inductive.cpp` v4.33.0
   :1223–1231 type-checks the replaced nested applications `I Ds`);
   v4.33.1+ REJECT earlier ("invalid occurrence of datatype 'T' being
   declared", `check_uniform_ind_occs`: `T.{0}` is not at the block's
   levels).  Exported by the pinned v4.29.1.  Target: reject (1). -/
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
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let w := Level.param `w
  addDecl <| Declaration.inductDecl [`w] 1
    [{ name := `Q, type := .forallE `a (.sort w) (.sort w) .default,
       ctors := [{ name := `Q.mk, type := .forallE `a (.sort w) (mkApp (.const `Q [w]) (.bvar 0)) .default }] }] false
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let dom := mkApp (Expr.const `Q [u]) (.const `T [.zero])
  let ctorTy := Expr.forallE `a dom (.const `T [u]) .default
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort u, ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
