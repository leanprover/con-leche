-- Task #607: a definition and a hole, compared with a solution whose binders are named otherwise.
prelude
import Init.Prelude
def g : Nat → Nat := fun x => x
theorem gt (x : Nat) : Eq (g x) x := sorry
