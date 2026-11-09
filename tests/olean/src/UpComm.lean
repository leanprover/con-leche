-- Ported from Lean v4.35.0 tests/lake/tests/challenge-simple-match/Challenge.lean
-- (comparator: tests/projects/simple_match).  The same challenge is the
-- Challenge.lean of challenge-simple-mismatch, -simple-axiom-issue,
-- -simple-kind-mismatch, check-paranoid and the sandbox/config tests.
-- Adapted: `prelude` + `import Init.Data.Nat.Basic` instead of all of
-- Init (the gate checks the closure on every run).
prelude
import Init.Data.Nat.Basic

theorem comm (n m : Nat) : n + m = m + n := by
  sorry
