import ConLeche.SetP.Claims2P
import ConLeche.SetP.Direct.DirectIntroP
import ConLeche.SetP.Claims2PIO
import ConLeche.SetP.IOLicenseP
import ConLeche.SetP.OkPTransport
import ConLeche.SetP.CtxOkPKit
import ConLeche.SetP.Step2.InferP
import ConLeche.SetP.Step2.InferIOP
import ConLeche.SetP.Step2.WhnfP
import ConLeche.SetP.Step2.GateP
import ConLeche.SetP.Step2.DefEqP
import ConLeche.SetP.Annot.EnvS2Core
import ConLeche.SetP.Annot.EnvS2P
import ConLeche.SetP.Step2.IrrelP
import ConLeche.SetP.Step2.IrrelFastP
import ConLeche.SetP.Step2.StuckP
import ConLeche.SetP.Step2.ReadsP
import ConLeche.SetP.Step2.ReadsIOP
import ConLeche.SetP.Step2.AcceptedP
import ConLeche.SetP.Step2.NatP
import ConLeche.SetP.Step2.CapsRowsP
import ConLeche.SetP.Step2.TiersP
import ConLeche.SetP.InstallP
import ConLeche.SetP.NatEqsP
import ConLeche.SetP.NatSemP
import ConLeche.SetP.CapsP
import ConLeche.SetP.DivModP
import ConLeche.SetP.NatWfP
import ConLeche.SetP.NatStepP
import ConLeche.SetP.DivModCertP
import ConLeche.SetP.CapstoneP
import ConLeche.SetP.AxiomBitsP
import ConLeche.SetP.BasisConsP
import ConLeche.SetP.BitAgree
import ConLeche.SetP.BasisTypeOk
import ConLeche.SetP.EqTowerP
import ConLeche.SetP.BasisStepP
import ConLeche.SetP.BasisEmptyP
import ConLeche.SetP.BasisFalseP
import ConLeche.SetP.LevelsP
import ConLeche.SetP.BasisBlocksP
import ConLeche.SetP.BasisQuotP
import ConLeche.SetP.BasisEqP
import ConLeche.SetP.IndConsP
import ConLeche.SetP.IndMemberP
import ConLeche.SetP.IndCapsP
import ConLeche.SetP.IndMembersP
import ConLeche.SetP.IndTeleP
import ConLeche.SetP.IndUnitLawP
import ConLeche.SetP.IndEtaLawP
import ConLeche.SetP.IndFrameP
import ConLeche.SetP.IndProjCapsP
import ConLeche.SetP.IndProjEtaP
import ConLeche.SetP.IndRunsP
import ConLeche.SetP.IndSubstP
import ConLeche.SetP.IndStageKitP
import ConLeche.SetP.IndCrossP
import ConLeche.SetP.IndZipFieldP
import ConLeche.SetP.IndRenameP
import ConLeche.SetP.IndGradeP
import ConLeche.SetP.IndDomGradeP
import ConLeche.SetP.IndPrefixGradeP
import ConLeche.SetP.IndParamGradeP
import ConLeche.SetP.IndFieldGradeP
import ConLeche.SetP.IndPlainParamP
import ConLeche.SetP.IndZipperP
import ConLeche.SetP.IndPointKitP
import ConLeche.SetP.IndPointP
import ConLeche.SetP.IndTowerReadP
import ConLeche.SetP.IndReductP
import ConLeche.SetP.IndLamTowerP
import ConLeche.SetP.IndAnnotKitP
import ConLeche.SetP.IndAnnotMemP
import ConLeche.SetP.IndFireP
import ConLeche.SetP.IndTransportP
import ConLeche.SetP.IndOpenRevP
import ConLeche.SetP.IndPinGradeP
import ConLeche.SetP.IndBottomPlainP
import ConLeche.SetP.IndOpenerGradeP
import ConLeche.SetP.IndNestedParamP
import ConLeche.SetP.IndBottomNestedP
import ConLeche.SetP.IndPinRowP
import ConLeche.SetP.IndProjKitP
import ConLeche.SetP.IndBottomProjP
import ConLeche.SetP.IotaRulePlainP
import ConLeche.SetP.IotaRuleNestedP
import ConLeche.SetP.SwapP
import ConLeche.SetP.IndRecsP
import ConLeche.SetP.ProjRenameP
import ConLeche.SetP.ProjConsP
import ConLeche.SetP.ProjInstallP
import ConLeche.SetP.DeclIndP
import ConLeche.SetP.IndPinProbeP
import ConLeche.SetP.AxiomPinP
import ConLeche.SetP.HarvestP
import ConLeche.SetP.FoldP
import ConLeche.SetP.Annot.Bit
import ConLeche.SetP.Annot.BitLemmas
import ConLeche.SetP.Annot.BitShift
import ConLeche.SetP.Annot.BitInst
import ConLeche.SetP.Annot.BitClosed
import ConLeche.SetP.Annot.BitInstall
import ConLeche.SetP.Annot.BitExtend
import ConLeche.SetP.Annot.ValidV
import ConLeche.SetP.Annot.ValidVSpine
import ConLeche.SetP.Step2.BitLevels
-- P modules the old `ConLeche/SetR.lean` umbrella covered only transitively;
-- named here so `lake build ConLecheP` roots the whole lane.
import ConLeche.SetP.Annot.BitRename
import ConLeche.SetP.AxiomMemP
import ConLeche.SetP.AxiomReduceP
import ConLeche.SetP.ErasePwInv
import ConLeche.SetP.RecRulesPCons
import ConLeche.SetP.ReduceOpsP
import ConLeche.SetP.Step2.IotaKitP
import ConLeche.SetP.Step2.IotaRowsP
import ConLeche.SetP.Step2.MajorP
import ConLeche.SetP.Step2.ProjRowsP
import ConLeche.SetP.Step2.StrLitP

/-!
# `ConLeche.SetP` — the graded-model lane (task #161, S2)

THE SEPARATION's second subtree.  `ConLeche.SetR.*` is the collapsed
model (`EnvS`, `Sound/*`, `Install/*`, the 2U/`denote2` tier, the
`R`/`R2` capstones); **this** tree is the graded model — the `AnnotOk2`
bit carriers (`Annot/Bit*`, `Annot/ValidV*`), `EnvS2Core`/`EnvS2P`, the
per-rule `…P` quarters and rows, the basis/inductive/projection install
`…P` families, the fold `FoldP` and the capstone `CapstoneP`.  Both
stand on `ConLeche.SetBase.*` and neither may import the other.

The shipped driver's P letter lives with the driver it is about
(`no_proof_of_Empty_SPCD_P`, `ConLeche/Verify/Cached/MainC.lean`); `MainP`
— the interned drivers' P capstone family — went with those drivers at
task #172.

**Only the file paths and module names moved** (`ConLeche.SetR.Interp2.X`
→ `ConLeche.SetP.X`, `ConLeche.SetR.Annot.X` → `ConLeche.SetP.Annot.X`).  The
Lean *namespaces* (`ConLeche.SetR.Interp2`, `ConLeche.SetR.Annot`) are
unchanged, so every frozen statement keeps its name verbatim and no
consumer outside the `import` lines was touched — the statement-freeze
discipline (task #161).  The namespaces are renamed, if ever, by a
separate batch that is allowed to touch declaration names.

The boundary is enforced by `tests/layering.sh` (inside `tests/arena.sh`):
after this move the gate classifies **by path alone** — `ConLeche/SetP/*`
is P, `ConLeche/SetBase/*` is base, `ConLeche/SetR/*` is R — and the
lane-closure computation S1 needed is gone.  Since **S8 the whitelist is
EMPTY**: this tree reaches no `ConLeche/SetR/*` module at all, and the
gate reads `0 P->R edges (whitelist EMPTY); 0 R->P`.
-/
