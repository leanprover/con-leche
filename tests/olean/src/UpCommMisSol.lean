-- Ported from Lean v4.35.0 tests/lake/tests/challenge-simple-mismatch/Solution.lean
-- (comparator: tests/projects/simple_mismatch).
-- Upstream: rejected ("Challenge and solution constant kind don't match:
-- 'comm'", exit 1).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

axiom comm (n m : Nat) : m + m = m + m
