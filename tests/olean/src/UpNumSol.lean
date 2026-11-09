-- Ported from Lean v4.35.0 tests/lake/tests/challenge-numeric-namespace/Solution.lean
-- (comparator: tests/projects/numeric_namespace).
-- Upstream: accepted ("Your solution is okay!", exit 0).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

namespace «123»
theorem foo : 1 + 1 = 2 := by
  rfl
end «123»
