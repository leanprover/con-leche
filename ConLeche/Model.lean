import ConLeche.Model.Claims
import ConLeche.Model.Inductives.StructIntro
import ConLeche.Model.ClaimsIO
import ConLeche.Model.IOLicense
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Steps.Infer
import ConLeche.Model.Steps.InferIO
import ConLeche.Model.Steps.Whnf
import ConLeche.Model.Steps.Gate
import ConLeche.Model.Steps.DefEq
import ConLeche.Model.Annot.EnvModel
import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Steps.Irrel
import ConLeche.Model.Steps.IrrelFast
import ConLeche.Model.Steps.Stuck
import ConLeche.Model.Steps.Reads
import ConLeche.Model.Steps.ReadsIO
import ConLeche.Model.Steps.Accepted
import ConLeche.Model.Steps.Nat
import ConLeche.Model.Steps.CapsRows
import ConLeche.Model.Steps.Tiers
import ConLeche.Model.Install
import ConLeche.Model.NatEqs
import ConLeche.Model.NatSem
import ConLeche.Model.Caps
import ConLeche.Model.DivMod
import ConLeche.Model.NatWf
import ConLeche.Model.NatStep
import ConLeche.Model.DivModCert
import ConLeche.Model.Capstone
import ConLeche.Model.AxiomBits
import ConLeche.Model.BasisCons
import ConLeche.Model.BitAgree
import ConLeche.Model.BasisTypeOk
import ConLeche.Model.EqTower
import ConLeche.Model.BasisStep
import ConLeche.Model.BasisEmpty
import ConLeche.Model.BasisFalse
import ConLeche.Model.Levels
import ConLeche.Model.BasisBlocks
import ConLeche.Model.BasisQuot
import ConLeche.Model.BasisEq
import ConLeche.Model.IndCons
import ConLeche.Model.IndMember
import ConLeche.Model.IndCaps
import ConLeche.Model.IndMembers
import ConLeche.Model.IndTele
import ConLeche.Model.IndUnitLaw
import ConLeche.Model.IndEtaLaw
import ConLeche.Model.IndFrame
import ConLeche.Model.IndProjCaps
import ConLeche.Model.IndProjEta
import ConLeche.Model.IndRuns
import ConLeche.Model.IndSubst
import ConLeche.Model.IndStageKit
import ConLeche.Model.IndCross
import ConLeche.Model.IndZipField
import ConLeche.Model.IndRename
import ConLeche.Model.IndGrade
import ConLeche.Model.IndDomGrade
import ConLeche.Model.IndPrefixGrade
import ConLeche.Model.IndParamGrade
import ConLeche.Model.IndFieldGrade
import ConLeche.Model.IndPlainParam
import ConLeche.Model.IndZipper
import ConLeche.Model.IndPointKit
import ConLeche.Model.IndPoint
import ConLeche.Model.IndTowerRead
import ConLeche.Model.IndReduct
import ConLeche.Model.IndLamTower
import ConLeche.Model.IndAnnotKit
import ConLeche.Model.IndAnnotMem
import ConLeche.Model.IndFire
import ConLeche.Model.IndTransport
import ConLeche.Model.IndOpenRev
import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndBottomPlain
import ConLeche.Model.IndOpenerGrade
import ConLeche.Model.IndNestedParam
import ConLeche.Model.IndBottomNested
import ConLeche.Model.IndPinRow
import ConLeche.Model.IndProjKit
import ConLeche.Model.IndBottomProj
import ConLeche.Model.IotaRulePlain
import ConLeche.Model.IotaRuleNested
import ConLeche.Model.Swap
import ConLeche.Model.IndRecs
import ConLeche.Model.ProjRename
import ConLeche.Model.ProjCons
import ConLeche.Model.ProjInstall
import ConLeche.Model.DeclInd
import ConLeche.Model.IndPinProbe
import ConLeche.Model.AxiomPin
import ConLeche.Model.Harvest
import ConLeche.Model.Fold
import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitShift
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitInstall
import ConLeche.Model.Annot.BitExtend
import ConLeche.Model.Annot.Valid
import ConLeche.Model.Annot.ValidSpine
import ConLeche.Model.Steps.BitLevels
-- P modules the old `ConLeche/SetR.lean` umbrella covered only transitively;
-- named here so `lake build ConLecheModel` roots the whole lane.
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.AxiomMem
import ConLeche.Model.AxiomReduce
import ConLeche.Model.ErasePwInv
import ConLeche.Model.RecRulesCons
import ConLeche.Model.ReduceOps
import ConLeche.Model.Steps.IotaKit
import ConLeche.Model.Steps.IotaRows
import ConLeche.Model.Steps.Major
import ConLeche.Model.Steps.ProjRows
import ConLeche.Model.Steps.StrLit

/-!
# `ConLeche.Model` — the graded-model lane (task #161, S2)

THE SEPARATION's second subtree.  `ConLeche.SetR.*` is the collapsed
model (`EnvS`, `Sound/*`, `Install/*`, the 2U/`denoteAnnot` tier, the
`R`/`R2` capstones); **this** tree is the graded model — the `WellDenoted`
bit carriers (`Annot/Bit*`, `Annot/ValidV*`), `EnvModel`/`EnvModelM`, the
per-rule `…P` quarters and rows, the basis/inductive/projection install
`…P` families, the fold `FoldP` and the capstone `CapstoneP`.  Both
stand on `ConLeche.SetBase.*` and neither may import the other.

The shipped driver's P letter lives with the driver it is about
(`no_proof_of_Empty_cached`, `ConLeche/Verify/Cached/MainC.lean`); `MainP`
— the interned drivers' P capstone family — went with those drivers at
task #172.

**Only the file paths and module names moved** (`ConLeche.SetR.Interp.X`
→ `ConLeche.Model.X`, `ConLeche.SetR.Annot.X` → `ConLeche.Model.Annot.X`).  The
Lean *namespaces* (`ConLeche.SetR.Interp`, `ConLeche.SetR.Annot`) are
unchanged, so every frozen statement keeps its name verbatim and no
consumer outside the `import` lines was touched — the statement-freeze
discipline (task #161).  The namespaces are renamed, if ever, by a
separate batch that is allowed to touch declaration names.

The boundary is enforced by `tests/layering.sh` (inside `tests/arena.sh`):
after this move the gate classifies **by path alone** — `ConLeche/Model/*`
is P, `ConLeche/SetBase/*` is base, `ConLeche/SetR/*` is R — and the
lane-closure computation S1 needed is gone.  Since **S8 the whitelist is
EMPTY**: this tree reaches no `ConLeche/SetR/*` module at all, and the
gate reads `0 P->R edges (whitelist EMPTY); 0 R->P`.
-/
