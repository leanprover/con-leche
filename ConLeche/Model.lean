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
public import ConLeche.Model.StepAgree
public import ConLeche.Model.Fold
public import ConLeche.Model.Inductives.BlockRepOne
public import ConLeche.Model.Inductives.BlockRecCand
public import ConLeche.Model.Inductives.BlockRec
public import ConLeche.Model.Inductives.BlockRecFrames
public import ConLeche.Model.Inductives.BlockRecKit
public import ConLeche.Model.Inductives.BlockRecTyped
public import ConLeche.Model.Inductives.BlockRecEq
public import ConLeche.Model.Inductives.BlockRecWD
public import ConLeche.Model.Inductives.BlockRecLeaf
public import ConLeche.Model.Inductives.BlockRecValid
public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Inductives.MutualCtorShape
public import ConLeche.Model.Inductives.MutualData
public import ConLeche.Model.Inductives.MutualShadow
public import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Model.Inductives.MutualLeafBelow
public import ConLeche.Model.Inductives.MutualStageFormer
public import ConLeche.Model.Inductives.MutualFormersKit
public import ConLeche.Model.Inductives.MutualIdxUniv
public import ConLeche.Model.Inductives.MutualStageCtor
public import ConLeche.Model.Inductives.MutualCore
public import ConLeche.Model.Inductives.MutualNorm
public import ConLeche.Model.Inductives.CaseWitness
public import ConLeche.Model.Inductives.TupleLfp
public import ConLeche.Model.Inductives.BlockRepMutual
public import ConLeche.Model.Inductives.BlockComposed
public import ConLeche.Model.Inductives.NestedFit
public import ConLeche.Model.Inductives.NestedAux
public import ConLeche.Model.Inductives.NestedEntryParam
public import ConLeche.Model.Inductives.NestedPremise
public import ConLeche.Model.Inductives.ContainerCross
public import ConLeche.Model.Inductives.BasisBlocksZero
public import ConLeche.Model.Inductives.BasisBlocksUnit
public import ConLeche.Model.Inductives.BasisBlocksNat
public import ConLeche.Model.Inductives.BasisBlocksEq
public import ConLeche.Model.Inductives.BasisBlocksStep
public import ConLeche.Model.Inductives.BasisBlocksTag
public import ConLeche.Model.Inductives.EnvModelBStages
public import ConLeche.Model.Inductives.BasisBlocksFold
public import ConLeche.Model.Inductives.NestedCore
public import ConLeche.Model.Inductives.DeclNestedCore
public import ConLeche.Model.Inductives.NestedRecsStage
public import ConLeche.Model.Inductives.NestedRecRead
public import ConLeche.Model.Inductives.NestedRecTypes
public import ConLeche.Model.Inductives.NestedRecScratch
public import ConLeche.Model.Inductives.NestedRecFibre
public import ConLeche.Model.Inductives.NestedRecWalk
public import ConLeche.Model.Inductives.NestedRecCtor
public import ConLeche.Model.Inductives.NestedRecFrames
public import ConLeche.Model.Inductives.NestedRecFrames2
public import ConLeche.Model.Inductives.NestedRecEqs
public import ConLeche.Model.Inductives.NestedRecsStore
public import ConLeche.Model.Inductives.NestedRecsSwap
public import ConLeche.Model.Inductives.NestedRecRule
public import ConLeche.Model.Inductives.NestedStoreRun
public import ConLeche.Model.Inductives.NestedChain
public import ConLeche.Model.Inductives.NestedRec
public import ConLeche.Model.Inductives.NestedRecCand
public import ConLeche.Model.Inductives.NestedRecTyped
public import ConLeche.Model.Inductives.NestedPinLaws
public import ConLeche.Model.Inductives.NestedPinLeafAll
public import ConLeche.Model.Inductives.NestedRewriteRead
public import ConLeche.Model.Inductives.NestedStageCtor
public import ConLeche.Model.Inductives.NestedTables
public import ConLeche.Model.Inductives.NestedLoop
public import ConLeche.Model.Inductives.NestedPins
public import ConLeche.Model.Inductives.NestedCopyIdx
public import ConLeche.Model.Inductives.NestedCopyRead
public import ConLeche.Model.Inductives.NestedOwnPinsRead
public import ConLeche.Model.Inductives.NestedCopyInst
public import ConLeche.Model.Inductives.NestedInstMap
public import ConLeche.Model.Inductives.NestedTransfer
public import ConLeche.Model.Inductives.NestedCtorRead
public import ConLeche.Model.Inductives.NestedCtorOpened
public import ConLeche.Model.Inductives.NestedCtorRefl
public import ConLeche.Model.Inductives.NestedReadLaw
public import ConLeche.Model.Inductives.MutualRecData
public import ConLeche.Model.Inductives.MutualRecRead
public import ConLeche.Model.Inductives.MutualRuleRead
public import ConLeche.Model.Inductives.MutualRecs
public import ConLeche.Model.Inductives.MutualRecsProvision
public import ConLeche.Model.Inductives.MutualRecsStage
public import ConLeche.Model.Inductives.BlockRecBridge
public import ConLeche.Model.Inductives.BlockRepCross
public import ConLeche.Model.Inductives.MutualRecsSwap
public import ConLeche.Model.Inductives.MutualRecsLaw
public import ConLeche.Model.Inductives.MutualRecsStore
public import ConLeche.Model.Inductives.BlockTableMember
public import ConLeche.Model.Inductives.BlockTableOf
public import ConLeche.Model.Inductives.BlockStageTable
public import ConLeche.Model.Inductives.BlockStageTables
public import ConLeche.Model.Inductives.MutualNoProj
public import ConLeche.Model.Inductives.MutualTables
public import ConLeche.Model.Inductives.NestedSlotRead
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
