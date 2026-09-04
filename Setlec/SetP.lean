import Setlec.SetP.Claims2P
import Setlec.SetP.DirectIntroP
import Setlec.SetP.Claims2PIO
import Setlec.SetP.IOLicenseP
import Setlec.SetP.OkPTransport
import Setlec.SetP.CtxOkPKit
import Setlec.SetP.Step2.InferP
import Setlec.SetP.Step2.InferIOP
import Setlec.SetP.Step2.WhnfP
import Setlec.SetP.Step2.GateP
import Setlec.SetP.Step2.DefEqP
import Setlec.SetP.Step2.AssemblyP
import Setlec.SetP.Annot.EnvS2Core
import Setlec.SetP.Annot.EnvS2P
import Setlec.SetP.Step2.IrrelP
import Setlec.SetP.Step2.StuckP
import Setlec.SetP.Step2.ReadsP
import Setlec.SetP.Step2.ReadsIOP
import Setlec.SetP.Step2.AcceptedP
import Setlec.SetP.Step2.NatP
import Setlec.SetP.Step2.CapsRowsP
import Setlec.SetP.Step2.TiersP
import Setlec.SetP.InstallP
import Setlec.SetP.NatEqsP
import Setlec.SetP.NatSemP
import Setlec.SetP.CapsP
import Setlec.SetP.DivModP
import Setlec.SetP.NatWfP
import Setlec.SetP.NatStepP
import Setlec.SetP.DivModCertP
import Setlec.SetP.CapstoneP
import Setlec.SetP.AxiomBitsP
import Setlec.SetP.BasisConsP
import Setlec.SetP.BitAgree
import Setlec.SetP.BasisTypeOk
import Setlec.SetP.EqTowerP
import Setlec.SetP.BasisStepP
import Setlec.SetP.BasisEmptyP
import Setlec.SetP.LevelsP
import Setlec.SetP.BasisBlocksP
import Setlec.SetP.BasisQuotP
import Setlec.SetP.BasisEqP
import Setlec.SetP.BasisPSigmaP
import Setlec.SetP.IndConsP
import Setlec.SetP.IndMemberP
import Setlec.SetP.IndCapsP
import Setlec.SetP.IndMembersP
import Setlec.SetP.IndTeleP
import Setlec.SetP.IndUnitLawP
import Setlec.SetP.IndEtaLawP
import Setlec.SetP.IndFrameP
import Setlec.SetP.IndProjCapsP
import Setlec.SetP.IndProjEtaP
import Setlec.SetP.IndRunsP
import Setlec.SetP.IndSubstP
import Setlec.SetP.IndStageKitP
import Setlec.SetP.IndCrossP
import Setlec.SetP.IndZipFieldP
import Setlec.SetP.IndRenameP
import Setlec.SetP.IndGradeP
import Setlec.SetP.IndDomGradeP
import Setlec.SetP.IndPrefixGradeP
import Setlec.SetP.IndParamGradeP
import Setlec.SetP.IndFieldGradeP
import Setlec.SetP.IndPlainParamP
import Setlec.SetP.IndZipperP
import Setlec.SetP.IndPointKitP
import Setlec.SetP.IndPointP
import Setlec.SetP.IndTowerReadP
import Setlec.SetP.IndReductP
import Setlec.SetP.IndLamTowerP
import Setlec.SetP.IndAnnotKitP
import Setlec.SetP.IndAnnotMemP
import Setlec.SetP.IndFireP
import Setlec.SetP.IndTransportP
import Setlec.SetP.IndOpenRevP
import Setlec.SetP.IndPinGradeP
import Setlec.SetP.IndBottomPlainP
import Setlec.SetP.IndOpenerGradeP
import Setlec.SetP.IndNestedParamP
import Setlec.SetP.IndBottomNestedP
import Setlec.SetP.Annot.BitReads
import Setlec.SetP.IndPinRowP
import Setlec.SetP.IndProjKitP
import Setlec.SetP.IndBottomProjP
import Setlec.SetP.IotaRulePlainP
import Setlec.SetP.IotaRuleNestedP
import Setlec.SetP.SwapP
import Setlec.SetP.IndRecsP
import Setlec.SetP.ProjRenameP
import Setlec.SetP.ProjConsP
import Setlec.SetP.ProjInstallP
import Setlec.SetP.DeclIndP
import Setlec.SetP.IndPinProbeP
import Setlec.SetP.AxiomPinP
import Setlec.SetP.HarvestP
import Setlec.SetP.FoldP
import Setlec.SetP.MainP
import Setlec.SetP.Annot.Bit
import Setlec.SetP.Annot.BitLemmas
import Setlec.SetP.Annot.BitShift
import Setlec.SetP.Annot.BitInst
import Setlec.SetP.Annot.BitClosed
import Setlec.SetP.Annot.BitInstall
import Setlec.SetP.Annot.BitExtend
import Setlec.SetP.Annot.ValidV
import Setlec.SetP.Annot.ValidVSpine
import Setlec.SetP.Step2.BitLevels
-- P modules the old `Setlec/SetR.lean` umbrella covered only transitively;
-- named here so `lake build SetlecP` roots the whole lane.
import Setlec.SetP.Annot.BitRename
import Setlec.SetP.AxiomMemP
import Setlec.SetP.AxiomReduceP
import Setlec.SetP.ErasePwInv
import Setlec.SetP.RecRulesPCons
import Setlec.SetP.ReduceOpsP
import Setlec.SetP.Step2.IotaKitP
import Setlec.SetP.Step2.IotaRowsP
import Setlec.SetP.Step2.MajorP
import Setlec.SetP.Step2.ProjPinsP
import Setlec.SetP.Step2.ProjRowsP
import Setlec.SetP.Step2.StrLitP

/-!
# `Setlec.SetP` — the graded-model lane (task #161, S2)

THE SEPARATION's second subtree.  `Setlec.SetR.*` is the collapsed
model (`EnvS`, `Sound/*`, `Install/*`, the 2U/`denote2` tier, the
`R`/`R2` capstones); **this** tree is the graded model — the `AnnotOk2`
bit carriers (`Annot/Bit*`, `Annot/ValidV*`), `EnvS2Core`/`EnvS2P`, the
per-rule `…P` quarters and rows, the basis/inductive/projection install
`…P` families, the fold `FoldP`, the capstone `CapstoneP` and — since
S8 — `MainP`, the shipped drivers' capstone family
(`no_proof_of_Empty_SP_P` and its cached/shared siblings).  Both stand
on `Setlec.SetBase.*` and neither may import the other.

**Only the file paths and module names moved** (`Setlec.SetR.Interp2.X`
→ `Setlec.SetP.X`, `Setlec.SetR.Annot.X` → `Setlec.SetP.Annot.X`).  The
Lean *namespaces* (`Setlec.SetR.Interp2`, `Setlec.SetR.Annot`) are
unchanged, so every frozen statement keeps its name verbatim and no
consumer outside the `import` lines was touched — the statement-freeze
discipline (task #161).  The namespaces are renamed, if ever, by a
separate batch that is allowed to touch declaration names.

The boundary is enforced by `tests/layering.sh` (inside `tests/arena.sh`):
after this move the gate classifies **by path alone** — `Setlec/SetP/*`
is P, `Setlec/SetBase/*` is base, `Setlec/SetR/*` is R — and the
lane-closure computation S1 needed is gone.  Since **S8 the whitelist is
EMPTY**: this tree reaches no `Setlec/SetR/*` module at all, and the
gate reads `0 P->R edges (whitelist EMPTY); 0 R->P`.
-/
