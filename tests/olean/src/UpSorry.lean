-- Ported from Lean v4.35.0 tests/lake/tests/check-sorry/Solution.lean;
-- check-from-export's Bad.lean is the same file.
-- Upstream: rejected ("Axiom 'sorryAx' is not permitted", exit 1).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

theorem bad : False := sorry
