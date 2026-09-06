import Lech.SetP.Claims2P
import Lech.SetP.Direct.DirectIntroP
import Lech.SetP.Claims2PIO
import Lech.SetP.IOLicenseP
import Lech.SetP.OkPTransport
import Lech.SetP.CtxOkPKit
import Lech.SetP.Step2.InferP
import Lech.SetP.Step2.InferIOP
import Lech.SetP.Step2.WhnfP
import Lech.SetP.Step2.GateP
import Lech.SetP.Step2.DefEqP
import Lech.SetP.Annot.EnvS2Core
import Lech.SetP.Annot.EnvS2P
import Lech.SetP.Step2.IrrelP
import Lech.SetP.Step2.IrrelFastP
import Lech.SetP.Step2.StuckP
import Lech.SetP.Step2.ReadsP
import Lech.SetP.Step2.ReadsIOP
import Lech.SetP.Step2.AcceptedP
import Lech.SetP.Step2.NatP
import Lech.SetP.Step2.CapsRowsP
import Lech.SetP.Step2.TiersP
import Lech.SetP.InstallP
import Lech.SetP.NatEqsP
import Lech.SetP.NatSemP
import Lech.SetP.CapsP
import Lech.SetP.DivModP
import Lech.SetP.NatWfP
import Lech.SetP.NatStepP
import Lech.SetP.DivModCertP
import Lech.SetP.CapstoneP
import Lech.SetP.AxiomBitsP
import Lech.SetP.BasisConsP
import Lech.SetP.BitAgree
import Lech.SetP.BasisTypeOk
import Lech.SetP.EqTowerP
import Lech.SetP.BasisStepP
import Lech.SetP.BasisEmptyP
import Lech.SetP.BasisFalseP
import Lech.SetP.LevelsP
import Lech.SetP.BasisBlocksP
import Lech.SetP.BasisQuotP
import Lech.SetP.BasisEqP
import Lech.SetP.IndConsP
import Lech.SetP.IndMemberP
import Lech.SetP.IndCapsP
import Lech.SetP.IndMembersP
import Lech.SetP.IndTeleP
import Lech.SetP.IndUnitLawP
import Lech.SetP.IndEtaLawP
import Lech.SetP.IndFrameP
import Lech.SetP.IndProjCapsP
import Lech.SetP.IndProjEtaP
import Lech.SetP.IndRunsP
import Lech.SetP.IndSubstP
import Lech.SetP.IndStageKitP
import Lech.SetP.IndCrossP
import Lech.SetP.IndZipFieldP
import Lech.SetP.IndRenameP
import Lech.SetP.IndGradeP
import Lech.SetP.IndDomGradeP
import Lech.SetP.IndPrefixGradeP
import Lech.SetP.IndParamGradeP
import Lech.SetP.IndFieldGradeP
import Lech.SetP.IndPlainParamP
import Lech.SetP.IndZipperP
import Lech.SetP.IndPointKitP
import Lech.SetP.IndPointP
import Lech.SetP.IndTowerReadP
import Lech.SetP.IndReductP
import Lech.SetP.IndLamTowerP
import Lech.SetP.IndAnnotKitP
import Lech.SetP.IndAnnotMemP
import Lech.SetP.IndFireP
import Lech.SetP.IndTransportP
import Lech.SetP.IndOpenRevP
import Lech.SetP.IndPinGradeP
import Lech.SetP.IndBottomPlainP
import Lech.SetP.IndOpenerGradeP
import Lech.SetP.IndNestedParamP
import Lech.SetP.IndBottomNestedP
import Lech.SetP.IndPinRowP
import Lech.SetP.IndProjKitP
import Lech.SetP.IndBottomProjP
import Lech.SetP.IotaRulePlainP
import Lech.SetP.IotaRuleNestedP
import Lech.SetP.SwapP
import Lech.SetP.IndRecsP
import Lech.SetP.ProjRenameP
import Lech.SetP.ProjConsP
import Lech.SetP.ProjInstallP
import Lech.SetP.DeclIndP
import Lech.SetP.IndPinProbeP
import Lech.SetP.AxiomPinP
import Lech.SetP.HarvestP
import Lech.SetP.FoldP
import Lech.SetP.Annot.Bit
import Lech.SetP.Annot.BitLemmas
import Lech.SetP.Annot.BitShift
import Lech.SetP.Annot.BitInst
import Lech.SetP.Annot.BitClosed
import Lech.SetP.Annot.BitInstall
import Lech.SetP.Annot.BitExtend
import Lech.SetP.Annot.ValidV
import Lech.SetP.Annot.ValidVSpine
import Lech.SetP.Step2.BitLevels
-- P modules the old `Lech/SetR.lean` umbrella covered only transitively;
-- named here so `lake build LechP` roots the whole lane.
import Lech.SetP.Annot.BitRename
import Lech.SetP.AxiomMemP
import Lech.SetP.AxiomReduceP
import Lech.SetP.ErasePwInv
import Lech.SetP.RecRulesPCons
import Lech.SetP.ReduceOpsP
import Lech.SetP.Step2.IotaKitP
import Lech.SetP.Step2.IotaRowsP
import Lech.SetP.Step2.MajorP
import Lech.SetP.Step2.ProjRowsP
import Lech.SetP.Step2.StrLitP

/-!
# `Lech.SetP` — the graded-model lane (task #161, S2)

THE SEPARATION's second subtree.  `Lech.SetR.*` is the collapsed
model (`EnvS`, `Sound/*`, `Install/*`, the 2U/`denote2` tier, the
`R`/`R2` capstones); **this** tree is the graded model — the `AnnotOk2`
bit carriers (`Annot/Bit*`, `Annot/ValidV*`), `EnvS2Core`/`EnvS2P`, the
per-rule `…P` quarters and rows, the basis/inductive/projection install
`…P` families, the fold `FoldP` and the capstone `CapstoneP`.  Both
stand on `Lech.SetBase.*` and neither may import the other.

The shipped driver's P letter lives with the driver it is about
(`no_proof_of_Empty_SPCD_P`, `Lech/Verify/Cached/MainC.lean`); `MainP`
— the interned drivers' P capstone family — went with those drivers at
task #172.

**Only the file paths and module names moved** (`Lech.SetR.Interp2.X`
→ `Lech.SetP.X`, `Lech.SetR.Annot.X` → `Lech.SetP.Annot.X`).  The
Lean *namespaces* (`Lech.SetR.Interp2`, `Lech.SetR.Annot`) are
unchanged, so every frozen statement keeps its name verbatim and no
consumer outside the `import` lines was touched — the statement-freeze
discipline (task #161).  The namespaces are renamed, if ever, by a
separate batch that is allowed to touch declaration names.

The boundary is enforced by `tests/layering.sh` (inside `tests/arena.sh`):
after this move the gate classifies **by path alone** — `Lech/SetP/*`
is P, `Lech/SetBase/*` is base, `Lech/SetR/*` is R — and the
lane-closure computation S1 needed is gone.  Since **S8 the whitelist is
EMPTY**: this tree reaches no `Lech/SetR/*` module at all, and the
gate reads `0 P->R edges (whitelist EMPTY); 0 R->P`.
-/
