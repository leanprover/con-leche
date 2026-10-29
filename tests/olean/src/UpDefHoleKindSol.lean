-- Ported from Lean v4.35.0 tests/lake/tests/challenge-def-hole-kind-mismatch/Solution.lean
-- (comparator: tests/projects/def_hole_kind_mismatch).
-- Upstream: rejected ("Solution constant is not a definition: 'n'", exit 1).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

-- Solution tries to satisfy the hole with an axiom rather than a def.
-- Should be rejected because the kind does not match.
axiom n : Nat

theorem foo : n + 17 = 34 := sorry
