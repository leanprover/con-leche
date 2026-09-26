/- End-to-end test: WF-recursive Nat operations on literals (div,
   mod) on big literals: unary/delta grinding would build huge terms.
   The slice carries everything the pinned `Nat.div` install needs, so
   the operation certifies and the literal reduces on the fast path:
   accepted (exit 0).  (The name is historical: the fixture was written
   when this declined.) -/

--#export t

theorem t : Eq (Nat.div 36893488147419103232 2) 18446744073709551616 :=
  Eq.refl 18446744073709551616
