--#export T.rec
/- L9FIX adversarial M2′ probe A1 (kernel-level, `addDecl`): the member at
   levels DEFINITIONALLY but not structurally the block's, in a redex whnf
   drops: `T.{u} : Type | mk : (fun (_ : Type) => Nat) T.{max u u} → T.{u}`.
   Official ≤ v4.33.0 ACCEPTS (the walk never reads it); v4.33.1+ REJECTS
   (`check_uniform_ind_occs` compares the levels STRUCTURALLY:
   "invalid occurrence of datatype 'T' being declared").  Ours: M2′
   compares structurally too, a reject.  Target: reject (1). -/
import Lean
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let dom := mkApp (Expr.lam `x (.sort (.succ .zero)) (.const `Nat []) .default) (.const `T [.max u u])
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := .forallE `a dom (.const `T [u]) .default }] }] false
