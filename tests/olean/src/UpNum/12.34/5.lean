-- Ported from Lean v4.35.0 tests/lake/tests/challenge-numeric-namespace/Challenge/12.34/5.lean
-- (comparator: tests/projects/numeric_namespace): the challenge module
-- `Challenge.«12.34».«5»`, here `UpNum.«12.34».«5»`.
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

namespace «123»
theorem foo : 1 + 1 = 2 := by
  sorry
end «123»
