module
-- Guards task #501: a definition named S.rec, and an exposed value reading it.
public def S.rec : Nat := 5
@[expose] public def w : Nat := S.rec + 0
