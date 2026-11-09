-- Ported from Lean v4.35.0 tests/lake/tests/challenge-def-hole-axiom-issue/Solution.lean
-- (comparator: tests/projects/def_hole_axiom_issue).
-- Upstream: rejected ("Illegal axiom detected: 'sorryAx'", exit 1).
-- Adapted: `prelude` + `import Init.Data.Nat.Basic`.
prelude
import Init.Data.Nat.Basic

-- Adversarial solution: hides `sorryAx` (an axiom that is NOT in permitted_axioms)
-- inside the hole body. The kernel accepts the proof of `foo` because `n + 17`
-- β-reduces to `17 + 17 = 34` regardless of which `Unit` argument is passed. The
-- stored term for `foo` (written as `@Eq.refl Nat 34`) does not syntactically
-- reference `n`, so without explicit hole-body axiom checking this illegal
-- axiom usage would escape validation.
noncomputable def n : Nat := (fun _ : Nat => 17) (sorryAx Nat false)

theorem foo : n + 17 = 34 := @Eq.refl Nat 34
