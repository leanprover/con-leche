import Setlec.TTVerify.Denote
import Setlec.TTVerify.Inversion
import Setlec.TTVerify.EnvTT
import Setlec.TTVerify.Claims
import Setlec.TTVerify.Extend
import Setlec.TTVerify.Consistency

/-!
# The TTVerify bridge (task #119)

Verification of the checker against the *declarative type theory* of
`Setlec/TT/*` rather than directly against the set model: a denotation
from a real `Env` + `Expr` into `VExpr` (`Setlec/TTVerify/Denote.lean`),
an environment invariant transposed from `EnvModel`
(`Setlec/TTVerify/EnvTT.lean`), and the acceptance theorem
(`Setlec/TTVerify/Consistency.lean`).

Layering: this hierarchy may import `Setlec/TT/*`, `Setlec/Kernel/*`
and `Setlec/Verify/*`.  The checker never imports it, and
`Setlec/TT/*` stays checker-free — every adaptation lives here.

Both verification paths coexist: nothing in `Setlec/Model/*` is
replaced or weakened by this one.
-/
