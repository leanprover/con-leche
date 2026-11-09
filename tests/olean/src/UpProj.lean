-- Ported from comparator tests/projects/proj_trick/Challenge.lean (not in
-- Lean v4.35.0's tests).  Upstream config: theorem_names [tgt],
-- definition_names [T], permitted_axioms [].
-- Adapted: `prelude` + `import Init.Data.Nat.Basic` instead of `import
-- Lean`, and the projection function `S.a` where upstream's `pr%`
-- elaborator writes a raw `Expr.proj S 0` (which needs `import Lean`).
-- The trick targets a comparison that follows only the constants a hole
-- mentions (a raw projection mentions none); con-leche compares every
-- constant of the challenge, `S` among them, whatever mentions it.  The
-- verbatim pair was run once (task #384): rejected the same way.
prelude
import Init.Data.Nat.Basic

/-- The structure the statement is really about. -/
structure S : Type where
  a : Nat

/-- The definition hole: the solver supplies the carrier. -/
def T : Type := S

theorem tgt : ∀ (s : T), S.a s = (0 : Nat) := sorry
