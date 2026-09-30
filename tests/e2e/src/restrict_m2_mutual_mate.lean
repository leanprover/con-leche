--#export T.rec S.rec
/- L9FIX adversarial M2′ probe A4 (kernel-level, `addDecl`): a MUTUAL
   member at other levels in a redex whnf drops: `T.{u}, S.{u} : Type`,
   `T.mk : (fun (_ : Type) => Nat) S.{0} → T.{u}`, `S.mk : S.{u}`.
   Official ≤ v4.33.0 ACCEPTS; v4.33.1+ REJECTS (`check_uniform_ind_occs`
   checks every member name: "invalid occurrence of datatype 'S' being
   declared").  Ours: M2′ (every member name), a reject.  Target: reject
   (1). -/
import Lean
open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let u := Level.param `u
  let dom := mkApp (Expr.lam `x (.sort (.succ .zero)) (.const `Nat []) .default) (.const `S [.zero])
  addDecl <| Declaration.inductDecl [`u] 0
    [{ name := `T, type := .sort (.succ .zero), ctors := [{ name := `T.mk, type := .forallE `a dom (.const `T [u]) .default }] },
     { name := `S, type := .sort (.succ .zero), ctors := [{ name := `S.mk, type := .const `S [u] }] }] false
