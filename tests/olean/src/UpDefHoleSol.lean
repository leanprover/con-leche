-- Ported from Lean v4.35.0 tests/lake/tests/challenge-def-hole/Solution.lean
-- (comparator: tests/projects/def_hole).
-- Upstream: accepted ("Your solution is okay!", exit 0).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

def n : Nat := 17

theorem foo : n + 17 = 34 := rfl
