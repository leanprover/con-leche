module
-- (task #421 cont. 25) reads LdvB.casesOn, whose value reads LdvB.rec.  With
-- LdvA's import of LdvQ made private (tests/lazy.sh), LdvA's block degrades
-- in its completed exported view: LdvB.rec is a type-only constant of M's
-- context.
import LdvA
theorem ldvM (x : LdvB) :
    LdvB.casesOn (motive := fun _ => Nat) x (fun _ => 0) =
      LdvB.casesOn (motive := fun _ => Nat) x (fun _ => 0) := rfl
