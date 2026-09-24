--#export T.rec
/- RESTRICT a27 (kernel-level, `addDecl`): the member at OTHER universe levels
   inside a redex whnf drops: `T.{u} : Type | mk : (fun (_ : Type) => Nat) T.{0} → T.{u}`.
   The elaborator cannot write `T.{0}` for the type being defined; the kernel
   accepts (`check_positivity` whnf's to `Nat`; no nested occurrence).
   Ours: M2′ `nestNoMemberConst` declines before the walk. -/
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
