--#export T.rec
/- T (α : Type) | mk : (let x : (fun _ => Type) (T Nat) := Nat; x) → T α
   UNIFCHK (2026-09-29), ACCEPTED SUPERSET (reported, not ruled): a
   NON-uniform occurrence `T Nat` only in a `let`'s TYPE.  Official v4.33.1+
   rejects (`check_uniform_ind_occs` walks `let` types); ≤ v4.33.0 accepts.
   Ours 0: the uniform-occurrence check (`nestUniform`) reads the STORED
   constructor type, and the annotation pass inlines `let`s (the ζ
   reduct), so the occurrence is gone.  Sound (the model reads the stored
   type).  TARGET 1 (official) if a reject-only check on the declared type
   is ever wanted. -/
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
  -- (let x : (fun _ => Type) (T Nat) := Nat; x)
  let letTy := mkApp (Expr.lam `y (.sort 1) (.sort 1) .default) (mkApp T (.const `Nat []))
  let dom := Expr.letE `x letTy (.const `Nat []) (.bvar 0) false
  let ctorTy := Expr.forallE `α (.sort 1) (Expr.forallE `a dom (mkApp T (.bvar 1)) .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default, ctors := [{ name := `T.mk, type := ctorTy }] }] false
