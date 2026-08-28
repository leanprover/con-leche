import Setlec.SetR.Rel
import Setlec.SetR.AnnotOkV
import Setlec.SetR.Sound.Motives
import Setlec.SetR.Sound.Struct
import Setlec.SetR.Sound.Irrel
import Setlec.SetR.Sound.Rigidity
import Setlec.SetR.Sound.Stuck
import Setlec.SetR.Sound.Proj
import Setlec.SetR.Sound.Lit
import Setlec.SetR.Sound.NatOps
import Setlec.SetR.Sound.NatOpsWf
import Setlec.SetR.Sound.Iota
import Setlec.SetR.Sound.Main
import Setlec.SetR.Weaken
import Setlec.SetR.CtxOkR
import Setlec.SetR.Decl
import Setlec.SetR.EnvS
import Setlec.SetR.Install.Cons
import Setlec.SetR.Install.Value
import Setlec.SetR.Install.ValueKinds
import Setlec.SetR.Install.Axiom
import Setlec.SetR.Install.ReducePin
import Setlec.SetR.Install.IndBottomS
import Setlec.SetR.Install.IndFrameS
import Setlec.SetR.Examples
import Setlec.SetR.Bridge.Env
import Setlec.SetR.Bridge.Claims
import Setlec.SetR.Bridge.WhnfCore
import Setlec.SetR.Bridge.Infer
import Setlec.SetR.Bridge.DefEq
import Setlec.SetR.Bridge.ReduceNat
import Setlec.SetR.Bridge.Step
import Setlec.SetR.Bridge.InferStruct
import Setlec.SetR.Bridge.Spine
import Setlec.SetR.Bridge.Irrel
import Setlec.SetR.Bridge.Certs
import Setlec.SetR.Bridge.StuckIrrel
import Setlec.SetR.Bridge.Eta
import Setlec.SetR.Bridge.StrLitR
import Setlec.SetR.Bridge.Stuck
import Setlec.SetR.Bridge.EtaCerts
import Setlec.SetR.Bridge.DefEqClosed

/-!
# `Setlec.SetR` — umbrella for the task-#148 relation family

See `Setlec/SetR/DESIGN.md` for the campaign section,
`Setlec/SetR/Rel.lean` for the family itself and
`Setlec/SetR/Bridge/*.lean` for the checker-to-derivation bridge.
-/
