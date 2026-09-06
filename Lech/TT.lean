import Lech.TT.Syntax
import Lech.TT.Subst
import Lech.TT.Const
import Lech.TT.Judgment
import Lech.TT.Semantics.Value
import Lech.TT.Semantics.Interp
import Lech.TT.Semantics.ConstOk
import Lech.TT.Semantics.Soundness

/-!
# The declarative type-theory layer (task #74)

See `Lech/TT/DESIGN.md`.  Nothing in the checker imports this yet:
the layer is additive, and the bridge (denotation of a real `Env` +
`Expr` into `VExpr`) is future work.
-/
