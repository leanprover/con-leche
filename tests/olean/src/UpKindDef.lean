-- con-leche's own, after Lean v4.35.0 tests/lake/tests/challenge-def-hole-kind-mismatch:
-- a definition hole alone, so that a solution of the wrong kind meets no
-- other failure first (upstream's solution there is an axiom, which
-- con-leche declines before any comparison).
prelude
import Init.Data.Nat.Basic

def n : Nat := sorry
