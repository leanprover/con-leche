module
prelude

/- Task #397: a certified `Nat` operation's name holds its certified
   definition or nothing (the literal fast path reads the name only).
   This module declares `Nat` as Lean's `Init.Prelude` does and
   `Nat.div` as an AXIOM of the pin's type: rejected in every mode
   (`natPinnedName`, `checkDecl`); Lean accepts the module. -/

public section

set_option genCtorIdx false in
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

axiom Nat.div : Nat → Nat → Nat

end
