import Setlec.TT.Syntax
import Setlec.TT.Subst
import Setlec.TT.Const
import Setlec.TT.Judgment
import Setlec.TT.Examples
import Setlec.TT.Semantics.Value
import Setlec.TT.Semantics.Interp
import Setlec.TT.Semantics.ConstOk
import Setlec.TT.Semantics.Soundness
import Setlec.TT.Semantics.Consistency

/-!
# The declarative type-theory layer (task #74)

See `Setlec/TT/DESIGN.md`.  Nothing in the checker imports this yet:
the layer is additive, and the bridge (denotation of a real `Env` +
`Expr` into `VExpr`) is future work.
-/
