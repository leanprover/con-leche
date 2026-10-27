/-
A stream that declares its OWN `Std.Tactic.BVDecide` names (task #368):
`unsat_of_verifyBVExpr_eq_true` applied to a native-named axiom, but the
closure is not the checker's pinned one, so the gate does not accept,
the argument is inferred, and the stub's use declines.  Today's verdict:
decline (2); target: decline.
-/
--#export fake

namespace Std.Tactic.BVDecide
def BVLogicalExpr : Type := Nat
def BVLogicalExpr.Unsat (_e : BVLogicalExpr) : Prop := True
namespace Reflect
def verifyBVExpr (_e : BVLogicalExpr) (_c : Nat) : Bool := true
theorem unsat_of_verifyBVExpr_eq_true (e : BVLogicalExpr) (c : Nat)
    (_h : verifyBVExpr e c = true) : e.Unsat := True.intro
end Reflect
end Std.Tactic.BVDecide

axiom fake._native.bv_decide.ax_1_1 :
  Std.Tactic.BVDecide.Reflect.verifyBVExpr (0 : Nat) 0 = true

theorem fake : Std.Tactic.BVDecide.BVLogicalExpr.Unsat (0 : Nat) :=
  Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true _ _ fake._native.bv_decide.ax_1_1
