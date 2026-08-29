import Setlec.Verify.Denote.VClosed
import Setlec.Verify.Denote.InstSimp
import Setlec.Verify.Denote.Weaken
import Setlec.Verify.Denote
import Setlec.Verify.Denote.Shift
import Setlec.Verify.Denote.Inst
import Setlec.Verify.Denote.Tele
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
import Setlec.TTVerify.DefEqStep
import Setlec.TTVerify.IotaStep
import Setlec.TTVerify.ProofIrrelStep
import Setlec.TTVerify.StuckStep
import Setlec.TTVerify.EtaCertStep
import Setlec.TTVerify.StuckIrrelStep
import Setlec.TTVerify.StructEtaCertStep
import Setlec.TTVerify.PairEtaStep
import Setlec.TTVerify.LitCtorStep
import Setlec.TTVerify.MajorStep
import Setlec.TTVerify.Extend
import Setlec.TTVerify.Consistency
import Setlec.Verify.Denote.HasTypeSubst
import Setlec.TTVerify.DeclStep
import Setlec.TTVerify.DeclValue
import Setlec.TTVerify.DeclThm
import Setlec.TTVerify.DeclOpaque
import Setlec.TTVerify.DeclDefn
import Setlec.TTVerify.ReducePin
import Setlec.TTVerify.DeclAxiom
import Setlec.TTVerify.OfReduceKey
import Setlec.TTVerify.SubstConst
import Setlec.TTVerify.StdAxiomKey
import Setlec.TTVerify.NatOpPin
import Setlec.TTVerify.DivModPin
import Setlec.TTVerify.DeclBasis
import Setlec.Verify.Denote.Rename
import Setlec.Verify.Denote.TeleOpen
import Setlec.TTVerify.DeclInd
import Setlec.TTVerify.IndBottom
import Setlec.TTVerify.IndBottomStages
import Setlec.TTVerify.IndBottomPlain
import Setlec.TTVerify.IndBottomNested
import Setlec.TTVerify.IndBottomProj
import Setlec.TTVerify.EnvSwap
import Setlec.TTVerify.DeclIndMember
import Setlec.TTVerify.DeclIndRecs
import Setlec.TTVerify.DeclIndProj
import Setlec.TTVerify.DeclIndDecl
import Setlec.TTVerify.DeclFamilies
import Setlec.TTVerify.Main

/-!
# The TTVerify bridge (task #119)

Verification of the checker against the *declarative type theory* of
`Setlec/TT/*` rather than directly against the set model: a denotation
from a real `Env` + `Expr` into `VExpr` (`Setlec/Verify/Denote.lean`),
an environment invariant transposed from `EnvModel`
(`Setlec/TTVerify/EnvTT.lean`), and the acceptance theorem
(`Setlec/TTVerify/Consistency.lean`).

Layering: this hierarchy may import `Setlec/TT/*`, `Setlec/Kernel/*`
and `Setlec/Verify/*`.  The checker never imports it, and
`Setlec/TT/*` stays checker-free — every adaptation lives here.

Both verification paths coexist: nothing in `Setlec/SetR/*` is
replaced or weakened by this one.
-/
