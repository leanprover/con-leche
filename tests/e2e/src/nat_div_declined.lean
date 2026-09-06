/- End-to-end test: WF-recursive Nat operations on literals (div,
   mod, gcd, bit ops) have no verified fast path; reducing them
   natively is unsupported, and unary/delta grinding on big literals
   would build huge terms — the checker must positively decline. -/

--#export t

theorem t : Eq (Nat.div 36893488147419103232 2) 18446744073709551616 :=
  Eq.refl 18446744073709551616
