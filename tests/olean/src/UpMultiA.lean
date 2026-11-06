-- Ported from Lean v4.35.0 tests/lake/tests/check-multi/A.lean (`lake check`
-- with two roots).  Upstream: accepted (exit 0).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

theorem a_thm : 1 + 1 = 2 := rfl
