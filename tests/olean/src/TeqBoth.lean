module
-- Guards task #464: TeqP1 and TeqP2 loaded together, two proofs of one statement under one
-- name: merged by Lean's rule, accepted.
import TeqP1
import TeqP2
theorem teqB : (1 : Nat) + 1 = 2 := teq
