-- Ported from Lean v4.35.0 tests/lake/tests/challenge-def-hole-type-mismatch/Challenge.lean
-- (comparator: tests/projects/def_hole_type_mismatch).
-- Adapted: `prelude` + `import Init.Data.Int.Basic`.
prelude
import Init.Data.Int.Basic

def n : Nat := sorry

theorem foo : 17 + 17 = 34 := sorry
