module
-- Guards task #502 (the reader's copy of a name unsafe): H reads GbG's S and S.rec in the
-- statement of an exported theorem, and holds an unsafe axiom `u` in its private part.  The
-- gate drops S.rec from GbG's exported part (as for GbH) and renames `u` to S.rec.
public import GbG
public theorem hz : (∀ _ : S, True) → @S.rec (fun _ => Nat) (fun x => x) = @S.rec (fun _ => Nat) (fun x => x) :=
  fun _ => rfl
private unsafe axiom u : Nat
