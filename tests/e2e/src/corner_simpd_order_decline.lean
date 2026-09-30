--#export T.rec T.rec_1
/- SIMPD ORDER (lane SIMPD, the member block is the positivity check's
   ROOT frame): a block with TWO independent faults —
   * `T.mk : Wrap T → T α`: the member UNAPPLIED in a PHANTOM container
     parameter (`restrict_a29`): M3, one of the root frame's own lines
     (`nestRootLines`), a reject (official v4.33.1+: 1);
   * `T.deep : G 2000 (T α) → T α`, `G (n+1) β := Nat → G n β`: the walk
     reads 2000 `Π` binders manufactured by reduction, beyond the
     constructor's input-derived fuel (`whnfWalkFuel`, depth + 1024) —
     our resource limit, a decline (official accepts it).
   The root frame walks EVERY constructor before its own lines run, so
   the decline comes first: exit 2.  Official 1; before lane SIMPD (the
   member constructors' M3 ran right after each one's walk) 1.  An
   order-only move on a two-fault stream (ruling 2026-09-29). -/
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
def G : Nat → Type → Type
  | 0, β => β
  | n + 1, β => Nat → G n β
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let tα := mkApp (.const `T []) (.bvar 1)
  let mkTy := Expr.forallE `α (.sort 1)
    (Expr.forallE `a (mkApp (.const `Wrap []) (.const `T [])) tα .default) .default
  let deepTy := Expr.forallE `α (.sort 1)
    (Expr.forallE `a (mkApp2 (.const `G []) (mkNatLit 2000) (mkApp (.const `T []) (.bvar 0)))
      tα .default) .default
  addDecl <| Declaration.inductDecl [] 1
    [{ name := `T, type := .forallE `α (.sort 1) (.sort 1) .default,
       ctors := [{ name := `T.mk, type := mkTy }, { name := `T.deep, type := deepTy }] }] false
  registerAuxRecs `T
#print T.rec
#print T.rec_1
