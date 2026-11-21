-- Task #607: CmpBndC with other binder names: accepted (an `Expr` holds no binder name).
prelude
import Init.Prelude
def g : Nat → Nat := fun y => y
theorem gt (z : Nat) : Eq (g z) z := rfl
