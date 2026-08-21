/- End-to-end test: `opaque` declarations — a theorem check without
   the is-a-proposition requirement; the constant is stored
   non-unfoldable.  `useIt` checks that the opaque constant types as a
   stuck head. -/

--#export mystery useIt

opaque mystery : Nat → Nat := fun n => n

def useIt : Nat := mystery (Nat.succ Nat.zero)
