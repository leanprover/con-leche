-- Task #607: an axiom of the challenge module is a hole.
prelude
import Init.Prelude
axiom ax : Eq (Nat.succ Nat.zero) (Nat.succ Nat.zero)
