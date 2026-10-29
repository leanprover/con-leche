-- Ported from Lean v4.35.0 tests/lake/tests/challenge-simple-axiom-issue/Solution.lean
-- (comparator: tests/projects/simple_axiom_issue); challenge-simple-kind-mismatch's
-- Solution.lean is the same file.
-- Upstream: rejected ("Illegal axiom detected: 'helper'", exit 1).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`; `universe u` added
-- (implicit in a file that imports Init).
prelude
import Init.Data.Nat.Basic

universe u

axiom helper {α : Sort u} : α

theorem comm (n m : Nat) : n + m = m + n := by
  exact helper
