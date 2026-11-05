-- Ported from Lean v4.35.0 tests/lake/tests/challenge-def-hole/Challenge.lean
-- (comparator: tests/projects/def_hole); also the Challenge.lean of
-- challenge-def-hole-axiom-issue and -def-hole-kind-mismatch.  Upstream
-- config: theorem_names [foo], definition_names [n] (con-leche: every
-- sorry of a challenge is a hole).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

def n : Nat := sorry

theorem foo : n + 17 = 34 := sorry
