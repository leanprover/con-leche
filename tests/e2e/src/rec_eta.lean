--#export re_k_lam re_k_lam_full re_k re_k_symm re_punit re_prod_lam re_prod re_prod_symm re_prod_nested

/- End-to-end fixture (task #632): η for a partially applied recursor
   (official's `eta_expand_iota_reduce_recursor` since lean4#15374),
   ported from lean4's `tests/elab/12520_2.lean`, and the arena
   renovation tests `etaRecStruct` and `etaRuleK`.  A recursor of a K
   family, or of an η family, applied to fewer arguments than its major
   needs is η-expanded along its type and ι-reduced with the stuck-major
   rescues (K, structure η) on the fresh major; the other side is compared
   with the resulting λ.

   * `re_k_lam`, `re_k_lam_full`: `Eq.rec … (a rfl) _` against `fun h => a h`
     (function η first; the recursor side then reduces by the K rescue).
   * `re_k` (the arena's `etaRuleK`), `re_k_symm`: against `a` itself,
     both orientations: the K recursor η-expanded.
   * `re_punit`: `PUnit.rec (a ())` against `a : Unit → Bool`: a
     fieldless η family.
   * `re_prod_lam`: `Prod.rec (fun b c => a (b, c))` against `fun b => a b`.
   * `re_prod` (the arena's `etaRecStruct`), `re_prod_symm`: against `a`.
   * `re_prod_nested`: the same under a binder, against `g x`.

   official (lean4 with #15374): 0.  con-leche before task #632: 1
   (`re_k`, `re_k_symm`, `re_punit`, `re_prod`, `re_prod_symm`,
   `re_prod_nested`); now 0. -/

import Lean
open Lean Elab Command Meta

/-- `rfl_unchecked n : ∀ xs, a = b` adds the theorem `n` with the proof
`fun xs => Eq.refl a`, kernel check skipped. -/
elab "rfl_unchecked " n:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let val ← forallTelescope ty fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "expected an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let decl : Declaration := .thmDecl
      { name := n.getId, levelParams := [], type := ty, value := val }
    withOptions (debug.skipKernelTC.set · true) <| addDecl decl

rfl_unchecked re_k_lam : ∀ (a : true = true → Bool),
  @Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) _ = fun h => a h
rfl_unchecked re_k_lam_full : ∀ (a : true = true → Bool),
  (fun h => a h) = a
rfl_unchecked re_k : ∀ (a : true = true → Bool),
  @Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) true = a
rfl_unchecked re_k_symm : ∀ (a : true = true → Bool),
  a = @Eq.rec Bool true (fun _ _ => Bool) (a (Eq.refl true)) true
rfl_unchecked re_punit : ∀ (a : Unit → Bool),
  @PUnit.rec (fun _ => Bool) (a ()) = a
rfl_unchecked re_prod_lam : ∀ (a : Bool × Bool → Bool),
  @Prod.rec Bool Bool (fun _ => Bool) (fun b c => a (b, c)) = fun b => a b
rfl_unchecked re_prod : ∀ (a : Bool × Bool → Bool),
  @Prod.rec Bool Bool (fun _ => Bool) (fun b c => a (b, c)) = a
rfl_unchecked re_prod_symm : ∀ (a : Bool × Bool → Bool),
  a = @Prod.rec Bool Bool (fun _ => Bool) (fun b c => a (b, c))
rfl_unchecked re_prod_nested : ∀ (g : Nat → Bool × Bool → Bool),
  (fun x => @Prod.rec Bool Bool (fun _ => Bool) (fun b c => g x (b, c))) = g
