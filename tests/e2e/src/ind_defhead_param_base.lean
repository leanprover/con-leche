--#export K.rec Two
/- The base of `ind_defhead_param_bad` (scripts/mk_defhead_param_fixture.py): that stream stores `K`
   at `Two`, the definition of the telescope below, which holds `K`'s parameters.  Official rejects
   that: `elim_nested_inductive` reads a block's parameters off member 0's type with a syntactic
   `is_pi` (`get_params`, `inductive.cpp`), "incorrect number of parameters"; the run is
   `mk_official` below.  This base, with the telescope written out, it accepts. -/
import Lean
open Lean Elab Command

def Two : Type 1 := (n : Nat) → Fin (n + 1) → Type → Type

inductive K : (n : Nat) → Fin (n + 1) → Type → Type where
  | mk (n : Nat) (i : Fin (n + 1)) (A : Type) (a : A) : K n i A

elab "mk_official" : command => do
  let K' := mkConst `K'
  let finTy := mkApp (mkConst ``Fin) (mkApp2 (mkConst ``Nat.add) (.bvar 0) (mkNatLit 1))
  let ctorTy : Expr :=
    .forallE `n (mkConst ``Nat)
      (.forallE `i finTy
        (.forallE `A (mkSort 1)
          (.forallE `a (.bvar 0) (mkApp3 K' (.bvar 3) (.bvar 2) (.bvar 1)) .default)
          .default) .default) .default
  let d : Declaration := .inductDecl [] 3
    [{ name := `K', type := mkConst `Two, ctors := [{ name := `K'.mk, type := ctorTy }] }] false
  try
    liftCoreM <| addDecl d
    throwError "official accepted a block with its parameters behind a definition"
  catch e =>
    logInfo m!"official: {e.toMessageData}"
mk_official
