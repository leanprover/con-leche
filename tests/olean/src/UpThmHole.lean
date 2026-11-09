-- Ported from comparator tests/projects/theorem_hole_issue/Challenge.lean
-- (not in Lean v4.35.0's tests).
-- Adapted: `prelude` + `import Init.Classical`.
prelude
import Init.Classical

theorem hex : ∃ x : Nat, x = 0 := sorry

-- Not a hole itself, but its *value* mentions the theorem hole `hex`, so the transitive
-- walk in `Compare.loop` reaches `hex` a second time.
noncomputable def w : Nat := Classical.choose hex

theorem hw : w = 0 := sorry
