-- Ported from Lean v4.35.0 tests/lake/tests/challenge-primitive-issue/Challenge.lean
-- (comparator: tests/projects/primitive_issue).
-- Adapted: `prelude` + `import Init.Data.Nat.Gcd` (the home of the
-- challenge context's `Nat.gcd`) instead of all of Init.
prelude
import Init.Data.Nat.Gcd

theorem boom : False := sorry
