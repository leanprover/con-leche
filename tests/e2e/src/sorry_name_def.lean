prelude
-- A definition at `sorryAx`'s name, in a file without Lean's `Init`.  Lean accepts it; con-leche
-- reserves the name to the tolerated axiom (whose record installs nothing), as it reserves the
-- certified operations' and the compiler-trust names, and rejects the declaration (exit 1), a
-- reject Lean does not make.  Target verdict: 1.
inductive T : Prop
  | intro
def sorryAx : T := T.intro
