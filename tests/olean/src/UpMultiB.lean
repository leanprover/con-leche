-- Ported from Lean v4.35.0 tests/lake/tests/check-multi/B.lean.
-- Upstream: accepted (exit 0).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

theorem b_thm : 2 + 2 = 4 := rfl
