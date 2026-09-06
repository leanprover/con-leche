import Lech.TT.Syntax
import Lech.TT.Subst
import Lech.TT.Const
import Lech.TT.Judgment

/-!
# The declarative type-theory layer (task #74)

See `Lech/TT/DESIGN.md`.  The four modules left here are **consumed**,
which is why they are here: `VExpr`/`BConst`/`mkAppN` (`Syntax`) and
`liftN`/`inst`/`arrow` with their laws (`Subst`) are the syntax the
whole `Semantics/*`–`SetP/*` tower is written in; `Const`'s basis
constants are read by `Semantics/BasisType`, `SetModel/Value` and —
`emptyT` — by `SetP/CapstoneP`; `Judgment` survives on `natStepT` and
`quotInvT`, which `Verify/Denote/SubstAlgebra` uses.

`TT/Semantics/{Value,Interp,ConstOk,Soundness}` — the declarative
lane's own model and its soundness theorem, 1 202 lines — were deleted
at task #190: nothing outside the four ever imported them, and the
P tier's `interp2`/`bval2` (`Lech/Semantics/*`) are its own, not
these.  `Judgment`'s `HasType` relation lost its last reader with
them and is now itself unread; see DESIGN's task #190 section.
-/
