module

import ConLeche.Kernel.TypeChecker
public import ConLeche.Verify.Knot
public import ConLeche.Verify.Shift

public section

/-!
# Abstraction and the open/close roundtrip

Inference opens a binder, infers the body, and re-closes the body's
type with `abstract1`.  The lemmas here make that roundtrip exact:

* `fvarConsistent d ty e`: every reachable `fvar d` leaf is exactly
  `fvar d n ty` — true of any opened body;
* `abstract1_instantiate1`: closing then re-opening is the identity,
  given consistency and no loose bound variables;
* scoping and loose-bvar bookkeeping for `abstract1`/`instantiate1`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

open Expr

/-- Every reachable `fvar` leaf with index `d` is exactly `fvar d ty`. -/
@[expose] def Expr.fvarConsistent (d : Nat) (ty : Expr) : Expr → Prop
  | .fvar idx ty' => idx = d → ty' = ty
  | .app f a => fvarConsistent d ty f ∧ fvarConsistent d ty a
  | .lam t b | .forallE t b => fvarConsistent d ty t ∧ fvarConsistent d ty b
  | .letE t v b => fvarConsistent d ty t ∧ fvarConsistent d ty v ∧ fvarConsistent d ty b
  | .proj _ _ e => fvarConsistent d ty e
  | _ => True

/-- Closing then re-opening a binder body is the identity. -/
theorem abstract1_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), fvarConsistent d ty e → e.looseBVarsBounded k = true →
      (e.abstract1 d k).instantiate1 (.fvar d ty) k = e := by
  intro e
  induction e <;> intro k hc hb <;>
    simp_all [Expr.fvarConsistent, Expr.looseBVarsBounded, Expr.abstract1, Expr.instantiate1]
  case bvar i =>
    have h1 : ¬ (i = k) := by omega
    have h2 : ¬ (i > k) := by omega
    simp [h1, h2]
  case fvar idx ty' ih =>
    by_cases hidx : idx = d
    · obtain rfl := hc hidx
      simp [hidx, Expr.instantiate1]
    · simp [hidx, Expr.instantiate1]

/-- Abstracting away the top variable lowers the scope bound. -/
theorem WScoped.abstract1 {d : Nat} :
    ∀ {e : Expr} (k : Nat), WScoped (d + 1) e → WScoped d (e.abstract1 d k) := by
  intro e
  induction e <;> intro k hw <;>
    simp_all [Expr.abstract1, WScoped]
  case fvar idx ty' ih =>
    by_cases hidx : idx = d
    · simp [hidx, WScoped]
    · simp only [hidx, ite_false, WScoped]
      exact ⟨by omega, hw.2⟩

/-- Opening lowers the loose-bvar bound by one. -/
theorem looseBVarsBounded_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).looseBVarsBounded k = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, Expr.looseBVarsBounded]
  case bvar i =>
    split
    · simp [Expr.looseBVarsBounded]
    · split <;> simp [Expr.looseBVarsBounded] <;> omega

/-- Abstracting raises the loose-bvar bound by one. -/
theorem looseBVarsBounded_abstract1 {d : Nat} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.abstract1 d k).looseBVarsBounded (k + 1) = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.abstract1, Expr.looseBVarsBounded]
  case bvar i => omega
  case fvar idx ty' ih =>
    split <;> simp [Expr.looseBVarsBounded] <;> omega

end ConLeche
