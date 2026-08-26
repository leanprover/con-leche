import Setlec.TTVerify.VClosed
import Setlec.TTVerify.InstSimp
import Setlec.TTVerify.Weaken
import Setlec.TTVerify.Denote
import Setlec.TTVerify.Shift
import Setlec.TTVerify.Inst
import Setlec.TTVerify.Tele
import Setlec.TTVerify.Certs
import Setlec.TTVerify.Iota
import Setlec.TTVerify.Inversion
import Setlec.TTVerify.Typable
import Setlec.TTVerify.EnvTT
import Setlec.TTVerify.Claims
import Setlec.TTVerify.WhnfCore
import Setlec.TTVerify.WhnfCoreStep
import Setlec.TTVerify.NatOpsStep
import Setlec.TTVerify.InferStep
import Setlec.TTVerify.StrLitStep
import Setlec.TTVerify.ProjStep
import Setlec.TTVerify.Extend
import Setlec.TTVerify.Consistency
import Setlec.TTVerify.HasTypeSubst

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
