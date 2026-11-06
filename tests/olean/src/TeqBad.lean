module
-- Guards task #464: with TeqQ2's files as TeqX's, two theorems `teq` of two statements are
-- loaded together: rejected (as Lean's import does).
import TeqP1
import TeqX
theorem teqBad : (1 : Nat) + 1 = 2 := teq
