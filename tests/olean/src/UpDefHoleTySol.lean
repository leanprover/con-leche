-- Ported from Lean v4.35.0 tests/lake/tests/challenge-def-hole-type-mismatch/Solution.lean
-- (comparator: tests/projects/def_hole_type_mismatch).
-- Upstream: rejected ("Const does not match between challenge and target
-- 'n'", exit 1).
-- Adapted: `prelude` + `import Init.Data.Int.Basic`.
prelude
import Init.Data.Int.Basic

-- Solution's hole has a different type; should be rejected even though the
-- theorem body is `sorry`.
def n : Int := 17

theorem foo : 17 + 17 = 34 := sorry
