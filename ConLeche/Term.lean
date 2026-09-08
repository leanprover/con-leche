import ConLeche.Term.Syntax
import ConLeche.Term.Subst
import ConLeche.Term.Const

/-!
# The erased term language (task #74; cut down and relocated at #209)

`Term` is the term language the whole semantics tier is written in.
It used to live at `ConLeche/TT/*` under `namespace ConLeche.TT`, as the
syntax half of a *declarative type theory* whose judgment and model
sat above it; those are gone (tasks #190 and #209) and the syntax is
not theirs, so it moved here — a base directory of its own rather than
one consumer's, since `Semantics/*`, `SetModel/*`, `Verify/Denote/*`
and `Model/*` all read it.

The three modules: `Syntax` carries `Term`/`BConst`/`mkAppN`,
`Subst` carries `liftN`/`inst`/`arrow` with their `rfl` laws, and
`Const`'s basis constants are read by `Semantics/BasisType`,
`SetModel/Value` and — `emptyT` — by `Model/CapstoneP`.

What the *declarative* lane above them added is gone.
`TT/Semantics/{Value,Interp,ConstOk,Soundness}` — its own model and
its soundness theorem, 1 202 lines — were deleted at task #190:
nothing outside the four modules ever imported them, and the P tier's
`interp`/`bval` (`ConLeche/Semantics/*`) are its own, not these.
`TT/Judgment` — the `HasType` relation, which lost its last reader
with them — went at task #209, together with the premise-type formers
`natStepT`/`quotInvT` and their four substitution lemmas in
`Verify/Denote/SubstAlgebra`, which nothing outside those rules ever
mentioned — and that module went the same way at task #221, its whole
lift/instantiate algebra unread (resolvable in git history).  The two lane records went with them; what of them is
still live is DESIGN.md's "House practices" section.
-/
