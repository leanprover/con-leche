--#export T.rec T.rec_1
/- RESTRICT a29 (kernel-level, `addDecl`): a member UNAPPLIED inside a
   PHANTOM container's parameter: `Wrap (F : Type → Type) | mk : Nat → Wrap F`,
   `T (α : Type) : Type | mk : Wrap T → T α`.  Official's aux constructor
   `Wrap_1.mk : Nat → Wrap_1` never sees `T`; accepted up to v4.33.0,
   rejected from v4.33.1 (`check_uniform_ind_occs`: "invalid occurrence of
   datatype 'T' being declared: it must be applied to the parameters and
   universe levels of the mutual declaration").  Ours: M3 on the walk's
   normal form (`Expr.holesApplied`), a reject — the walk
   never reads the phantom parameter, and the model needs every
   hole applied to the parameters (M3). -/
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
structure Wrap (F : Type → Type) : Type where
  n : Nat
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let dom := mkApp (Expr.const `Wrap []) (.const `T [])
  let ctorTy := Expr.forallE `α (.sort 1)
    (Expr.forallE `a dom (mkApp (.const `T []) (.bvar 1)) .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default,
       ctors := [{ name := `T.mk, type := ctorTy }] }] false
  registerAuxRecs `T
#print T.rec
#print T.rec_1
