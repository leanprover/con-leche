-- Ported from Lean v4.35.0 tests/lake/tests/challenge-simple-match/Solution.lean
-- (comparator: tests/projects/simple_match); also the Solution.lean of
-- check-paranoid, check-audit, check-from-export and the sandbox tests.
-- Upstream: accepted ("Your solution is okay!", exit 0).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`; `grind` replaced
-- by the lemma it finds (`grind` needs all of Init).
prelude
import Init.Data.Nat.Basic

theorem comm (n m : Nat) : n + m = m + n :=
  Nat.add_comm n m
