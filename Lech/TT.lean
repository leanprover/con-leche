import Lech.TT.Syntax
import Lech.TT.Subst
import Lech.TT.Const

/-!
# The erased term language (task #74, cut down at #190 and #209)

The three modules left here are **consumed**, which is why they are
here: `VExpr`/`BConst`/`mkAppN` (`Syntax`) and `liftN`/`inst`/`arrow`
with their laws (`Subst`) are the syntax the whole `Semantics/*`–
`SetP/*` tower is written in; `Const`'s basis constants are read by
`Semantics/BasisType`, `SetModel/Value` and — `emptyT` — by
`SetP/CapstoneP`.

What the *declarative* lane above them added is gone.
`TT/Semantics/{Value,Interp,ConstOk,Soundness}` — its own model and
its soundness theorem, 1 202 lines — were deleted at task #190:
nothing outside the four modules ever imported them, and the P tier's
`interp2`/`bval2` (`Lech/Semantics/*`) are its own, not these.
`TT/Judgment` — the `HasType` relation, which lost its last reader
with them — went at task #209, together with the premise-type formers
`natStepT`/`quotInvT` and their four substitution lemmas in
`Verify/Denote/SubstAlgebra`, which nothing outside those rules ever
mentioned.
-/
