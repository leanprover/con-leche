--#export T.rec
/- L9FIX control for M2′ (kernel-level, `addDecl`): A1 at the block's OWN
   levels, `T.{u} : Type | mk : (fun (_ : Type) => Nat) T.{u} → T.{u}`.
   Official accepts on every toolchain (v4.29.1, v4.33.0, v4.34.0: the
   occurrence is at the declaration's levels with its (zero) parameters).
   Ours: the member is abstracted to its hole, M2′ silent.  Target: accept
   (0). -/
import Lean
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  -- member at the block's levels but a DIFFERENT level-list spelling of the same param: T.{u} inside, block [u] — control (must accept)
  let dom := mkApp (Expr.lam `x (.sort (.succ .zero)) (.const `Nat []) .default) (.const `T [u])
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := .forallE `a dom (.const `T [u]) .default }] }] false
