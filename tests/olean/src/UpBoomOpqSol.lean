-- Ported from Lean v4.35.0 tests/lake/tests/challenge-opaque-value/Solution.lean
-- (comparator: tests/projects/opaque_value).
-- Upstream: rejected ("Illegal axiom detected: 'f'", exit 1).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

axiom f : False
opaque v : False := f
theorem boom : False := v
