-- Ported from comparator tests/projects/theorem_hole_issue/Solution.lean.
-- Upstream: accepted (exit 0).
-- Adapted: `prelude` + `import Init.Classical`.
prelude
import Init.Classical

theorem hex : ∃ x : Nat, x = 0 := ⟨0, rfl⟩

noncomputable def w : Nat := Classical.choose hex

theorem hw : w = 0 := Classical.choose_spec hex
