module
-- Guards task #415: M loads TeqH and TeqP2.  The statement of teqN's
-- exported equation lemma means P1's teq, which M does not load; M holds
-- P2's teq, a proof of the same statement, so the copy H means and the one
-- M holds are one constant: accepted (Lean accepts M).
import TeqH
import TeqP2
theorem teqM : teqN = 0 := teqN_zero
