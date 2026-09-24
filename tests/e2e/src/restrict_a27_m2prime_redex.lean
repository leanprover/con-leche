--#export T.rec
/- RESTRICT a27 (kernel-level, `addDecl`): the member at OTHER universe levels
   inside a redex whnf drops: `T.{u} : Type | mk : (fun (_ : Type) => Nat) T.{0} → T.{u}`.
   The elaborator cannot write `T.{0}` for the type being defined; official
   ≤ v4.33.0 accepts (`check_positivity` whnf's to `Nat`; no nested
   occurrence), v4.33.1+ rejects (`check_uniform_ind_occs`: "invalid
   occurrence of datatype 'T' being declared").  Ours: M2′
   `nestNoMemberConst` rejects after the walk (lane L9FIX; a decline before). -/
import Lean
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let dom := mkApp (Expr.lam `x (.sort (.succ .zero)) (.const `Nat []) .default) (.const `T [.zero])
  let ctorTy := Expr.forallE `a dom (.const `T [u]) .default
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := ctorTy }] }] false
#print T
#print T.rec
