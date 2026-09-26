module

public import ConLeche.Term.Syntax
public import ConLeche.Term.Subst
public import ConLeche.Term.Const

@[expose] public section

/-!
# The erased term language (task #74)

`Term` is the term language the whole semantics tier is written in.
It has a base directory of its own rather than one consumer's, since
`Semantics/*`, `SetModel/*`, `Verify/Denote/*` and `Model/*` all read
it.

The three modules: `Syntax` carries `Term`/`BConst`/`mkAppN`,
`Subst` carries `liftN`/`inst` with their `rfl` laws, and
`Const`'s basis constants are read by `Semantics/BasisType`,
`SetModel/Value` and — `emptyT` — by `Model/Capstone`.
-/
