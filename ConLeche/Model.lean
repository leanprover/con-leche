module

public import ConLeche.Model.Claims
public import ConLeche.Model.Inductives.StructIntro
public import ConLeche.Model.ClaimsIO
public import ConLeche.Model.IOLicense
public import ConLeche.Model.WellDenotedTransport
public import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Steps.Infer
public import ConLeche.Model.Steps.InferIO
public import ConLeche.Model.Steps.Whnf
public import ConLeche.Model.Steps.Gate
public import ConLeche.Model.Steps.DefEq
public import ConLeche.Model.Annot.EnvModel
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Steps.Irrel
public import ConLeche.Model.Steps.IrrelFast
public import ConLeche.Model.Steps.Stuck
public import ConLeche.Model.Steps.Reads
public import ConLeche.Model.Steps.ReadsIO
public import ConLeche.Model.Steps.Accepted
public import ConLeche.Model.Steps.Nat
public import ConLeche.Model.Steps.CapsRows
public import ConLeche.Model.Steps.Tiers
public import ConLeche.Model.Install
public import ConLeche.Model.NatEqs
public import ConLeche.Model.NatSem
public import ConLeche.Model.Caps
public import ConLeche.Model.DivMod
public import ConLeche.Model.NatWf
public import ConLeche.Model.NatStep
public import ConLeche.Model.DivModCert
public import ConLeche.Model.Capstone
public import ConLeche.Model.AxiomBits
public import ConLeche.Model.BasisCons
public import ConLeche.Model.BitAgree
public import ConLeche.Model.BasisTypeOk
public import ConLeche.Model.EqTower
public import ConLeche.Model.BasisStep
public import ConLeche.Model.BasisEmpty
public import ConLeche.Model.BasisFalse
public import ConLeche.Model.Levels
public import ConLeche.Model.BasisBlocks
public import ConLeche.Model.BasisQuot
public import ConLeche.Model.BasisEq
public import ConLeche.Model.IndCons
public import ConLeche.Model.IndMember
public import ConLeche.Model.IndCaps
public import ConLeche.Model.IndMembers
public import ConLeche.Model.IndTele
public import ConLeche.Model.IndUnitLaw
public import ConLeche.Model.IndEtaLaw
public import ConLeche.Model.IndFrame
public import ConLeche.Model.IndProjCaps
public import ConLeche.Model.IndProjEta
public import ConLeche.Model.IndRuns
public import ConLeche.Model.IndSubst
public import ConLeche.Model.IndStageKit
public import ConLeche.Model.IndCross
public import ConLeche.Model.IndZipField
public import ConLeche.Model.IndRename
public import ConLeche.Model.IndGrade
public import ConLeche.Model.IndDomGrade
public import ConLeche.Model.IndPrefixGrade
public import ConLeche.Model.IndParamGrade
public import ConLeche.Model.IndFieldGrade
public import ConLeche.Model.IndPlainParam
public import ConLeche.Model.IndZipper
public import ConLeche.Model.IndPointKit
public import ConLeche.Model.IndPoint
public import ConLeche.Model.IndTowerRead
public import ConLeche.Model.IndReduct
public import ConLeche.Model.IndLamTower
public import ConLeche.Model.IndAnnotKit
public import ConLeche.Model.IndAnnotMem
public import ConLeche.Model.IndFire
public import ConLeche.Model.IndTransport
public import ConLeche.Model.IndOpenRev
public import ConLeche.Model.IndPinGrade
public import ConLeche.Model.IndBottomPlain
public import ConLeche.Model.IndOpenerGrade
public import ConLeche.Model.IndNestedParam
public import ConLeche.Model.IndBottomNested
public import ConLeche.Model.IndPinRow
public import ConLeche.Model.IndProjKit
public import ConLeche.Model.IndBottomProj
public import ConLeche.Model.IotaRulePlain
public import ConLeche.Model.IotaRuleNested
public import ConLeche.Model.Swap
public import ConLeche.Model.IndRecs
public import ConLeche.Model.ProjRename
public import ConLeche.Model.ProjCons
public import ConLeche.Model.ProjInstall
public import ConLeche.Model.DeclInd
public import ConLeche.Model.IndPinProbe
public import ConLeche.Model.AxiomPin
public import ConLeche.Model.Harvest
public import ConLeche.Model.Fold
public import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Annot.BitShift
public import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.Annot.BitClosed
public import ConLeche.Model.Annot.BitInstall
public import ConLeche.Model.Annot.BitExtend
public import ConLeche.Model.Annot.Valid
public import ConLeche.Model.Annot.ValidSpine
public import ConLeche.Model.Steps.BitLevels
-- P modules the old `ConLeche/SetR.lean` umbrella covered only transitively;
-- named here so `lake build ConLecheModel` roots the whole lane.
public import ConLeche.Model.Annot.BitRename
public import ConLeche.Model.AxiomMem
public import ConLeche.Model.AxiomReduce
public import ConLeche.Model.ErasePwInv
public import ConLeche.Model.RecRulesCons
public import ConLeche.Model.ReduceOps
public import ConLeche.Model.Steps.IotaKit
public import ConLeche.Model.Steps.IotaRows
public import ConLeche.Model.Steps.Major
public import ConLeche.Model.Steps.ProjRows
public import ConLeche.Model.Steps.StrLit

@[expose] public section

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
