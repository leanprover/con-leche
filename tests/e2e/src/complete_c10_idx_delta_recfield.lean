--#export T.rec T.rec_1
/- COMPLETE c10: a container whose index telescope is behind δ
   (`C (α) : Idx`, `Idx := Nat → Type`) with a RECURSIVE field
   (`step : (n : Nat) → C α n → C α (n+1)`), nested: T | leaf | mk : C T 0 → T.
   Official: the aux type's index count is whnf-based (1); the frame hole's
   occurrence `C α n` has 1 param + 1 index. -/
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
def Idx : Type 1 := Nat → Type
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let ty := Expr.forallE `α (.sort 1) (.const `Idx []) .default
  let C := Expr.const `C []
  let natE := Expr.const `Nat []
  -- base : (α : Type) → α → C α 0
  let baseTy := Expr.forallE `α (.sort 1) (.forallE `a (.bvar 0)
      (mkApp2 C (.bvar 1) (.lit (.natVal 0))) .default) .default
  -- step : (α : Type) → (n : Nat) → C α n → C α (Nat.succ n)
  let stepTy := Expr.forallE `α (.sort 1) (.forallE `n natE
      (.forallE `c (mkApp2 C (.bvar 1) (.bvar 0))
        (mkApp2 C (.bvar 2) (mkApp (.const `Nat.succ []) (.bvar 1))) .default) .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `C, type := ty, ctors := [{ name := `C.base, type := baseTy },
        { name := `C.step, type := stepTy }] }] false
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let T : Expr := .const `T []
  addDecl <| Declaration.inductDecl [] 0
    [{ name := `T, type := .sort 1, ctors := [
      { name := `T.leaf, type := T },
      { name := `T.mk, type := .forallE `a (mkApp2 (.const `C []) T (.lit (.natVal 0))) T .default }] }] false
  registerAuxRecs `T
