--#export T.rec
/- T (α : Type) | mk : (let x : Type := T Nat; Nat) → T α
   UNIFCHK (2026-09-29), ACCEPTED SUPERSET (reported, not ruled): a
   NON-uniform occurrence `T Nat` only in the value of a `let` its body
   never uses.  Official v4.33.1+ rejects; ≤ v4.33.0 accepts.  Ours 0: the
   stored constructor type is the ζ reduct (see `uh_let_erase_type`).
   TARGET 1 (official) if a reject-only check on the declared type is ever
   wanted. -/
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
  -- (let x : Type := T Nat; Nat), the value unused
  let dom := Expr.letE `x (.sort 1) (mkApp T (.const `Nat [])) (.const `Nat []) false
  let ctorTy := Expr.forallE `α (.sort 1) (Expr.forallE `a dom (mkApp T (.bvar 1)) .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default, ctors := [{ name := `T.mk, type := ctorTy }] }] false
