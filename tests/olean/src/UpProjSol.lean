-- Ported from comparator tests/projects/proj_trick/Solution.lean.
-- Upstream: rejected (exit 1).
-- Adapted as UpProj (no `import Lean`, `S.a` for `pr%`).
prelude
import Init.Data.Nat.Basic

/-- Same name, never compared: now uninhabited. -/
structure S : Type where
  a : Nat
  h : False

def T : Type := S

theorem tgt : ∀ (s : T), S.a s = (0 : Nat) := by
  intro s
  exact (S.h s).elim
