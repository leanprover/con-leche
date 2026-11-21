module
-- (task #421) reads LdgB.casesOn, whose value reads LdgB.rec.  With
-- LdgA's import of LdgQ made private (tests/lazy.sh), LdgA's block is
-- installed at its completed exported view (#421 cont. 25): LdgB.rec is
-- presented, ldgT (which its constructor's statement reads) is a need of
-- LdgA's interface and a type-only constant of M's context.  The lazy
-- closure takes such a block as degraded (a superset of what it locates);
-- tests/lazy.sh pins the type-only constants.
import LdgA
theorem ldgM (x : LdgB) :
    LdgB.casesOn (motive := fun _ => Nat) x (fun _ => 0) =
      LdgB.casesOn (motive := fun _ => Nat) x (fun _ => 0) := rfl
