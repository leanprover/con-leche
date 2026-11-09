module
-- Guards task #415: M loads TeqH and TeqQ2, whose teq states something
-- else than the teq H's equation lemma means (P1's): two constants under
-- one name meet in M's completed view, rejected (Lean accepts M: its
-- import rule never loads P1).
import TeqH
import TeqQ2
theorem teqDM : teqN = 0 := teqN_zero
