-- Task #607: CmpAxC's axiom, as an axiom of the solution: the solution's check declines it,
-- as it declines every axiom but the standard ones.
prelude
import Init.Prelude
axiom ax : Eq (Nat.succ Nat.zero) (Nat.succ Nat.zero)
