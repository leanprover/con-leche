-- Ported from Lean v4.35.0 tests/lake/tests/challenge-olean-issue/Solution.lean
-- (comparator: tests/projects/olean_issue); check-audit-reject's
-- Solution.lean is the same file.
-- Upstream: rejected ("Lean default kernel rejected the solution", exit 1;
-- check-audit-reject: exit 1).
-- Verbatim (it needs `import Lean` for `run_elab`).
import Lean

open Lean

unsafe def badNatUnsafe : Nat := unsafeCast (-4294967296 : Int)

@[implemented_by badNatUnsafe] opaque badNatVal : Nat

run_elab
  addDecl <| .defnDecl {
    name        := .str .anonymous "badNat"
    levelParams := []
    type        := .const ``Nat []
    value       := .lit <| .natVal badNatVal
    hints       := .opaque
    safety      := .safe
  }

theorem boom : False := by
  have truly_marvelous_0 : ¬badNat ≤ 9223372036854775807 := by decide
  have truly_marvelous_1 : ¬9223372036854775807 < badNat := by decide
  omega
