--#export S2.rec
/- RESTRICT a34b (kernel-level, `addDecl`): `S2 (α : Sort u) : Sort u | mk : α → S2 α`.
   The ELABORATOR rejects ("resulting universe may be Prop"), the KERNEL accepts
   (`check_constructors`: `is_geq(u, u)`; `elim_only_at_universe_zero`: the
   field is not in the result, so `S2.rec` eliminates into `Prop` only). -/
import Lean
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let ty := Expr.forallE `α (.sort u) (.sort u) .default
  let ctorTy := Expr.forallE `α (.sort u) (.forallE `a (.bvar 0) (mkApp (.const `S2 [u]) (.bvar 1)) .default) .default
  addDecl <| Declaration.inductDecl [`u] 1
    [{ name := `S2, type := ty, ctors := [{ name := `S2.mk, type := ctorTy }] }] false
#print S2.rec
