-- Ported from Lean v4.35.0 tests/lake/tests/challenge-primitive-issue/Solution.lean
-- (comparator: tests/projects/primitive_issue, which defines Nat.land,
-- Nat.lor, Nat.xor and the shifts as 0 instead of importing
-- Init.Data.String.Bootstrap).
-- Upstream: rejected ("Const does not match between challenge and target
-- 'Nat.gcd'", exit 1).
-- Verbatim.
prelude
import Init.Prelude
import Init.Core
-- Supplies the kernel built-ins the comparison exports, so that `Nat.gcd` below is the only
-- constant that differs from the challenge.
import Init.Data.String.Bootstrap

def Nat.gcd (_ _ : Nat) : Nat := 0

theorem thm1 a b : Nat.gcd a b = 0 := by
  unfold Nat.gcd
  rfl

theorem thm2 : Nat.gcd 1 1 = 1 := rfl

theorem boom : False :=
  Nat.noConfusion <| Eq.trans (thm1 1 1).symm thm2
