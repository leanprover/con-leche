#!/usr/bin/env python3
"""Phase 3's plan: which import edges may stop being `public`.

TWO constraints, both of them about the PUBLIC closure — a private import
gives the importer the imported module's public interface and nothing more:

  coverage   for every constant a module mentions ANYWHERE (proof terms
             included), some DIRECT import of it must carry that constant
             publicly.  This is what the first attempt missed: demoting an
             edge three tiers down breaks a module that never mentions it.
  publicness a module's import must be PUBLIC when the module's own public
             interface (scripts/pub-iface.lean) needs something that import
             carries.

Everything starts public; an edge is demoted only when neither constraint
breaks anywhere.  The build is the confirmation, not the search.

TWO MODES.

    scripts/pub-import-plan.py            the PLAN: run the fixpoint from the
                                          all-public tree and write
                                          $PUBPLAN_DIR/plan.json for
                                          scripts/pub-import-apply.py.
    scripts/pub-import-plan.py --check    the GATE (task #235): start from the
                                          tree's ACTUAL `public import` set
                                          and report every edge that is
                                          individually demotable.  Exit 1 if
                                          any is — the tree is then not at a
                                          local minimum.

The gate deliberately does NOT compare against a freshly computed plan: the
fixpoint is greedy, so its result depends on the order it tries edges in, and
a plan edge that is plain here and public there is not a finding.  "No public
import can be demoted on its own" is order-independent.

Inputs (regenerate with `tests/shake.sh`, which is this script's caller in the
standard battery):

    $PUBPLAN_DIR/census.tsv   lake env lean --run scripts/dead-census.lean <mods>
    $PUBPLAN_DIR/pub.tsv      lake env lean --run scripts/pub-iface.lean   <mods>

`$PUBPLAN_DIR` defaults to `_tmp/m3`.
"""
import re, subprocess, json, collections, os, sys

CHECK = '--check' in sys.argv[1:]
DIR   = os.environ.get('PUBPLAN_DIR', '_tmp/m3')

# THE PER-FILE FALLBACK (task #231 phase 3, kept by task #235).  The model is
# a filter on candidate demotions, never a claim, and two files' re-exports
# are reached by DOT-NOTATION, which no census row and no source-identifier
# scan can attribute to a module: `RecCtorsStored.cons` in Model/Install and
# a lemma of the Denote tier in Semantics/IndRecsCore.  Demoting these builds
# a tree whose `rfl`s stop closing, so they stay public and the gate must not
# ask for them again.
FALLBACK = {
    # lane GENREC: the generated stage's run records name the stage's
    # kernel data (`classStreamRecs`, `ClassKey`, …) and the target check's
    # major record (`TargetMajorRun`) in their PUBLIC statements; each
    # MEASURED by demoting it alone (unknown identifier `classStreamRecs`,
    # `GenRecRun.lean:74`; unknown identifier `TargetMajorRun`, `:103`).
    ('ConLeche.Verify.Inductives.GenRecRun', 'ConLeche.Kernel.Inductives.GenRec'),
    ('ConLeche.Verify.Inductives.GenRecRun', 'ConLeche.Verify.Inductives.RecCheckRun'),
    # sub-lane GENREC-D: the generated stage's cached simulation states its
    # lemmas over the stage's kernel data (`ClassSlot`, `classReadSlots`, …)
    # and the cached kit's (`WScoped`, `CState`, `TargetMajScoped`, `SimG`
    # through `TargetRecC`'s re-exports); each MEASURED by demoting it alone
    # (unknown identifier `ClassSlot`, `GenRecC.lean:52`; unknown identifier
    # `WScoped`, `:69`).
    ('ConLeche.Verify.Cached.GenRecC', 'ConLeche.Kernel.Inductives.GenRec'),
    ('ConLeche.Verify.Cached.GenRecC', 'ConLeche.Verify.Cached.TargetRecC'),
    # sub-lane GENREC-A: `GenRecStage`'s public statements name the run
    # record, the stage record, the generator's scoping and its syntax
    # predicates; each MEASURED by demoting it alone (unknown identifier
    # `GenRecRun`, `GenRecStage.lean:329`; `RecTyGen`, `:378`;
    # `ClassGenScoped`, `:221`; unknown constant `ConLeche.Expr.Plain`, `:77`).
    ('ConLeche.Model.Inductives.GenRecStage', 'ConLeche.Verify.Inductives.GenRecRun'),
    ('ConLeche.Model.Inductives.GenRecStage', 'ConLeche.Verify.Inductives.RecStage'),
    ('ConLeche.Model.Inductives.GenRecStage', 'ConLeche.Verify.Inductives.ClassGenScope'),
    ('ConLeche.Model.Inductives.GenRecStage', 'ConLeche.Verify.Inductives.ClassGenAnnot'),
    # lane LIBMERGE (the block library merged into fewer modules): four
    # re-exports the model calls demotable, each MEASURED by demoting it
    # alone.  `BlockRecTower`'s public statements name `dnegSpace`,
    # `choiceV`, `piR`, `AnnotTerm`, `interp` through `TowerKit`
    # (`Unknown identifier dnegSpace`, `BlockRecTower.lean:64`);
    # `StructEntryKit`'s namespace block opens `SetTheory` and its public
    # statements name `fvsD`/`tfvD`/`projArgsD`, reached through
    # `StructRecKit` and its `DirectGen` re-export (`Unknown identifier
    # SetTheory`, `StructEntryKit.lean:57`; `ConLeche.fvsD`, `:1152`);
    # `DeclBlock`'s `DeclNative` re-export carries `spineFit_take` to
    # `BlockRecData` (`Unknown identifier spineFit_take`,
    # `BlockRecData.lean:1898`).
    ('ConLeche.Semantics.Tower.BlockRecTower', 'ConLeche.Semantics.Tower.TowerKit'),
    ('ConLeche.Model.Inductives.StructEntryKit', 'ConLeche.Model.Inductives.StructRecKit'),
    ('ConLeche.Model.Inductives.StructRecKit', 'ConLeche.Verify.Inductives.DirectGen'),
    ('ConLeche.Model.Inductives.DeclBlock', 'ConLeche.Model.Inductives.DeclNative'),
    # lane DNEWB: `FixTeleBound` lost its `FixNoBVar` import (deleted whole)
    # and now reaches `SetTheory` (its public `variable [SetTheory V]`)
    # through `StructEntryFree`; MEASURED by demoting it alone (unknown
    # identifier `SetTheory`, `FixTeleBound.lean:37`).
    ('ConLeche.Model.Inductives.FixKit', 'ConLeche.Model.Inductives.StructEntryKit'),
    # lane PARKFIX: moving the parked completeness modules to
    # `ConLeche/Complete/` changed the census's IMPORT ORDER (the module list
    # is alphabetical), and with it which module a lazily realised auxiliary
    # constant (`….eq_1` and the like) is attributed to — `Verify/Subst`'s
    # rows became `Verify/PropRead`'s — so the model stopped seeing these two
    # re-exports.  Each MEASURED by demoting it alone: `BlockCallCerts`
    # (unknown identifier `SetTheory`, `BlockCallCerts.lean:29`),
    # `StructBits` (unknown `ConLeche.whnf_sort`/`inferTypeCore_forallE_eq`,
    # `BlockRecPreRun.lean:2330–2363`).
    ('ConLeche.Model.Inductives.BlockCallCerts', 'ConLeche.Model.Inductives.BlockRep'),
    ('ConLeche.Model.Inductives.StructFrameKit', 'ConLeche.Verify.BinderLoop'),
    # lane DELMOD s2: `StructRecSpine`'s `IndPinGrade` re-export is what the
    # struct/fix proofs downstream reach `IndPinGrade`/`IndReduct` through;
    # MEASURED by demoting it alone (unknown identifier: `wellDenotedV_instSeq`
    # at `StructBodyFrames.lean:295` and `FixEntryLaw.lean:261`, then
    # `denoteMeta_mkAppN_of` at `BlockRecTyShapeRun.lean:242`).
    ('ConLeche.Model.Inductives.StructRecKit', 'ConLeche.Model.IndPinGrade'),
    # lane RPTIE: two re-exports the model calls demotable, each MEASURED by
    # demoting it alone.  `NestScope`'s public statements name `TargetMajor`
    # and `targetSeeds` (`mem_targetSeeds`, `targetSeeds_mem`; unknown
    # identifier `TargetMajor`, `NestScope.lean:517`) from `RecCheck`;
    # `StructFrameKit`'s name `PiTeleAV` (`StructFrameKit.lean:762`) from
    # `IndTowerRead` — the census now attributes it elsewhere.
    ('ConLeche.Verify.Inductives.NestScope', 'ConLeche.Kernel.Inductives.RecCheck'),
    ('ConLeche.Model.Inductives.StructFrameKit', 'ConLeche.Model.IndTowerRead'),
    # lane SEEDDEFEQ M2: `ClassMatchRun`'s public statements reach
    # `Expr.replaceFVars` by dot-notation (`targetCanonParams`' unfolding,
    # `:85`) through `RecCheck`, and `Expr.ErasedEq` (`:35`) through
    # `Subst`; MEASURED by demoting each alone.
    ('ConLeche.Verify.Inductives.ClassMatchRun', 'ConLeche.Kernel.Inductives.RecCheck'),
    ('ConLeche.Verify.Inductives.ClassMatchRun', 'ConLeche.Verify.Subst'),
    # lane NESTIND session 28 (the calls' kit, landed with its consumer):
    # six re-exports the model calls demotable, each MEASURED by demoting it
    # alone.  `TargetCallEntry` loses `Expr.ErasedEqL` (`:40`, via
    # `TargetNodeRb`) and `TargetCallRun` (`:55`, `RecCheckRun`);
    # `TargetCallRead` loses `AnnotTerm.substAV` (`:46`, `BitSubstFvars`),
    # `holeP` (`:202`, `NestPosMono`), `LocList` (`:77`, `TargetNodeRead`);
    # `NestCallRun` loses `FEnv` (`:42`, `RecCheckRun`).
    ('ConLeche.Model.Inductives.TargetCallEntry', 'ConLeche.Model.Inductives.TargetNodeRb'),
    ('ConLeche.Model.Inductives.TargetCallEntry', 'ConLeche.Verify.Inductives.RecCheckRun'),
    ('ConLeche.Model.Inductives.TargetCallRead', 'ConLeche.Model.Annot.BitSubstFvars'),
    ('ConLeche.Model.Inductives.TargetCallRead', 'ConLeche.Model.Inductives.NestPosMono'),
    ('ConLeche.Model.Inductives.TargetCallRead', 'ConLeche.Model.Inductives.TargetNodeRead'),
    ('ConLeche.Verify.Inductives.NestCallRun', 'ConLeche.Verify.Inductives.RecCheckRun'),
    # lane RP-ANNOT: `TargetCallGen` gained private imports (the move kit),
    # which changed the census's attribution; the model then calls its two
    # re-exports demotable.  Each MEASURED by demoting it alone: without
    # `TargetNodeRead`, `variable [SetTheory V]` fails (unknown identifier
    # `SetTheory`, `TargetCallGen.lean:59`); without `RecCheckRun`, the
    # statements' `TargetCallRun` (unknown identifier, `:381`).
    ('ConLeche.Model.Inductives.TargetCallGen', 'ConLeche.Model.Inductives.TargetNodeRead'),
    ('ConLeche.Model.Inductives.TargetCallGen', 'ConLeche.Verify.Inductives.RecCheckRun'),
    # lane NESTIND s23: `TargetNodeSem`'s public statements name `NodesSem`/
    # `NodeSemAt` (PosDerivNodes) and `BlockData`/`BlockNamesOk`/
    # `BlockHoleCtxFacts` (TargetNodeCover's re-exports); MEASURED by
    # demoting each (unknown identifier, `TargetNodeSem.lean:124` and `:47`).
    ('ConLeche.Model.Inductives.TargetNodeSem', 'ConLeche.Model.Inductives.PosDerivNodes'),
    ('ConLeche.Model.Inductives.TargetNodeSem', 'ConLeche.Model.Inductives.TargetNodeCover'),
    # lane NESTIND s23: `TargetNodeDynOf`'s public statements name `trueVal`
    # (TargetNodeAdm) and `NestedNodeDynOwed` (TargetNodeSem); MEASURED by
    # demoting each (unknown identifier, `TargetNodeDynOf.lean:75` and `:926`).
    ('ConLeche.Model.Inductives.TargetNodeDynOf', 'ConLeche.Model.Inductives.TargetNodeAdm'),
    ('ConLeche.Model.Inductives.TargetNodeDynOf', 'ConLeche.Model.Inductives.TargetNodeSem'),
    # lane COMPLETE-2/3: the completeness theorem's public statements name
    # `MemberCtorD` (PosDeriv); MEASURED by demoting it (unknown
    # identifier, `Complete/PosDerivComplete.lean:57`).
    ('ConLeche.Complete.PosDerivComplete', 'ConLeche.Verify.Inductives.PosDeriv'),
    # lane POSDERIV: the positivity inversion's public statements name
    # `NestCtxOk` (NestScope) and `BlockParts.nestCtx`/`checkBlockPositivity`
    # (PositivityInv); MEASURED by demoting each (unknown identifier,
    # `PosDerivInv.lean:161` and `:930`).
    ('ConLeche.Verify.Inductives.PosDerivInv', 'ConLeche.Verify.Inductives.NestScope'),
    ('ConLeche.Verify.Inductives.PosDerivInv', 'ConLeche.Verify.Inductives.PositivityInv'),
    # lane POSDERIV s2: `storedFieldShapes_of_walk`'s public statement names
    # `MemberCtorD`/`PosTree`; MEASURED by demoting it (unknown
    # identifier, `StoredShapes.lean:1049`).
    ('ConLeche.Model.Inductives.StoredShapes', 'ConLeche.Verify.Inductives.PosDeriv'),
    # lane FLATACC: after the flat (W) witness went (LfpHoleWitness,
    # TupleContainer, Container, BlockHoleFlat deleted) the model stopped
    # attributing these eight re-exports; each MEASURED by demoting it alone
    # (`nonempty_shapes`, `AxiomPin.lean:304`; `interp_sort_mem`,
    # `TowerCons.lean:161`, for both Claims→Skeleton and Skeleton→Univ;
    # `capsOk_cons_proj`, `ProjCons.lean:210`; `essOfR_fixCtorDataList_getD`,
    # `BlockStageCtors.lean:257`; `fixFibre_zero_elim`, `FixZeroField.lean:97`;
    # `erasePwNames_forallE_invS`, `AxiomMem.lean:151`; `CtxOk.nil`,
    # `BlockRecRead.lean:176`).
    ('ConLeche.Model.AxiomMem', 'ConLeche.Verify.StdAxiomPin'),
    ('ConLeche.Model.Claims', 'ConLeche.Semantics.Skeleton'),
    ('ConLeche.Model.IndProjEta', 'ConLeche.Model.IndProjCaps'),
    ('ConLeche.Model.ReduceOps', 'ConLeche.Model.ErasePwInv'),
    ('ConLeche.Model.Tiers', 'ConLeche.Model.CtxOkKit'),
    ('ConLeche.Semantics.Skeleton', 'ConLeche.Semantics.Univ'),
    # lane NESTIND session 9: `TargetClassCall`'s public statements name
    # `replF` (`TargetCallKit`), `TgtOutCls` (`TargetClass`), `TgtDsOk`
    # (`TargetFrame`) and `tgtMajor` (`TargetIhData`'s re-exports); each
    # MEASURED by demoting it alone (`Unknown identifier replF`, `:70`;
    # `TgtOutCls`, `:667`; `TgtDsOk`, `:233`; `tgtMajor`, `:133`).
    # `TargetCallCore`'s `tgtCall_coreFitG` names `TgtDsOk` (`Unknown
    # identifier TgtDsOk`, `TargetCallCore.lean:190`).
    ('ConLeche.Model.Inductives.TargetClassCall', 'ConLeche.Model.Inductives.TargetCallKit'),
    ('ConLeche.Model.Inductives.TargetClassCall', 'ConLeche.Model.Inductives.TargetClass'),
    ('ConLeche.Model.Inductives.TargetClassCall', 'ConLeche.Model.Inductives.TargetFrame'),
    ('ConLeche.Model.Inductives.TargetClassCall', 'ConLeche.Model.Inductives.TargetIhData'),
    ('ConLeche.Model.Inductives.TargetCallCore', 'ConLeche.Model.Inductives.TargetFrame'),
    # lane NESTIND session 14: `BlockStageRec`'s public statements name the
    # generic cons `consBlockRecsR` and `RecRulesShape` (`BlockWF`); MEASURED
    # by demoting it alone (`Unknown identifier consBlockRecsR`,
    # `BlockStageRec.lean:254`).
    ('ConLeche.Model.Inductives.BlockStageRec', 'ConLeche.Verify.Inductives.BlockWF'),
    # lane NESTIND session 7: `TargetOutCerts`' public statements name
    # `TgtDsOk` (`TargetFrame`) and `tgtRP`/`TgtOutCls`/`RecStageG` (through
    # `TargetOutGrade`'s re-exports); each MEASURED by demoting it alone
    # (`Unknown identifier TgtDsOk`, `TargetOutCerts.lean:80`; `Unknown
    # identifier tgtRP`, `:83`).
    ('ConLeche.Model.Inductives.TargetOutCerts', 'ConLeche.Model.Inductives.TargetFrame'),
    ('ConLeche.Model.Inductives.TargetOutCerts', 'ConLeche.Model.Inductives.TargetOutGrade'),
    # lane NESTKERN session 2: `TargetRecC`'s statement at :1001 names
    # `TargetTyEntry` (`RecCheckRun`); MEASURED by demoting it alone
    # (`Unknown identifier TargetTyEntry`, `TargetRecC.lean:1001`).
    ('ConLeche.Verify.Cached.TargetRecC', 'ConLeche.Verify.Inductives.RecCheckRun'),
    # lane NESTKERN: `checkBlockRecT_run`'s public statement names the
    # kernel's `checkBlockRecT` (`BlockTail`); MEASURED by demoting it alone
    # (`Unknown identifier checkBlockRecT`, `RecCheckRun.lean:873`).
    ('ConLeche.Verify.Inductives.RecCheckRun', 'ConLeche.Kernel.Inductives.BlockTail'),
    # lane L2: `TargetAuxFire`'s public statements name the kernel's
    # `auxRuleFire`/`FEnv`/`RecShape` and the Verify tier's
    # `Expr.instSeq`; each MEASURED by demoting it alone (`Unknown
    # identifier FEnv`, `:49`; `Unknown constant ConLeche.Expr.instSeq`,
    # `:165`).  Nothing imports the module yet (L6's consumer).
    ('ConLeche.Verify.Inductives.TargetAuxFire', 'ConLeche.Kernel.Inductives.RecCheck'),
    ('ConLeche.Verify.Inductives.TargetAuxFire', 'ConLeche.Verify.Subst'),
    # lane HOLE2 session 3: `BlockHoleGrade`'s public statements name
    # `BlockHoleCtxFacts`/`BlockNamesOk` (through `BlockPosRun`) and
    # `BlockHoleFacts` (`BlockLfpHoles`); each MEASURED by demoting it alone
    # (`Unknown identifier BlockNamesOk`/`BlockHoleCtxFacts`, `:104`;
    # `Unknown identifier BlockHoleFacts`, `:433`).
    ('ConLeche.Model.Inductives.BlockHoleGrade', 'ConLeche.Model.Inductives.BlockPosRun'),
    ('ConLeche.Model.Inductives.BlockHoleGrade', 'ConLeche.Model.Inductives.BlockLfpHoles'),
    # lane CONTSEM session 2: `Expr.substFvars`/`frameCrest_eq` are stated
    # over the kernel's `instPisWith`/`nestAbstract`/`NestCtx` and `Expr`;
    # MEASURED by demoting it alone (`Unknown identifier Expr`,
    # `SubstFvars.lean:25`).
    ('ConLeche.Verify.SubstFvars', 'ConLeche.Kernel.Inductives.Positivity'),
    # lane RECLIB session 3: the target check's scoping lemmas state
    # `EnvWF`, `WScoped`, `Rules.Infer` and the kernel's `targetAbs`/
    # `targetWhnfPis` in PUBLIC statements; each MEASURED by demoting it
    # alone (`Unknown identifier EnvWF`/`Rules.Grade`/`WScoped`/...).
    ('ConLeche.Verify.Inductives.RecCheckScope', 'ConLeche.Verify.EnvWF'),
    ('ConLeche.Verify.Inductives.RecCheckScope', 'ConLeche.Rules.Rel'),
    ('ConLeche.Verify.Inductives.RecCheckScope', 'ConLeche.Verify.Shift'),
    ('ConLeche.Verify.Inductives.RecCheckScope', 'ConLeche.Kernel.Inductives.RecCheck'),
    # `TargetIhSlot`'s `variable [SetTheory V]` binder resolves through
    # `TargetRecRead` (`Unknown identifier SetTheory`, `:47`), measured.
    ('ConLeche.Model.Inductives.TargetIhSlot', 'ConLeche.Model.Inductives.TargetRecRead'),
    # lane RECLIB session 5: the same `variable [SetTheory V]` binder
    # class, MEASURED by demoting each alone (`Unknown identifier
    # SetTheory`, `TargetCallCore.lean:67`, `TargetCallKit.lean:41`).
    ('ConLeche.Model.Inductives.TargetCallCore', 'ConLeche.Model.Inductives.TargetIhData'),
    ('ConLeche.Model.Inductives.TargetCallKit', 'ConLeche.Model.Inductives.TargetRecRead'),
    # lane GENREC-PORT: the generator's syntax modules, each MEASURED by
    # demoting it alone.  `ClassGenScope`'s `@[expose] def ScB` names
    # `WScoped` (`Unknown identifier WScoped`, `ClassGenScope.lean:57`);
    # `ClassGenAnnot`'s statements name `closeTelescope` (`:166`) and
    # `Expr.ErasedEq` (`:46`); `ClassGenMinorSyn`'s `Expr.ErasedEq` (`:204`).
    ('ConLeche.Verify.Inductives.ClassGenScope', 'ConLeche.Verify.Shift'),
    ('ConLeche.Verify.Inductives.ClassGenAnnot', 'ConLeche.Kernel.Inductives.Positivity'),
    ('ConLeche.Verify.Inductives.ClassGenAnnot', 'ConLeche.Verify.Subst'),
    ('ConLeche.Verify.Inductives.ClassGenMinorSyn', 'ConLeche.Verify.Subst'),
    # lane HOLE2 (the positivity walk's cached simulation): three
    # re-exports the model calls demotable, each MEASURED by demoting it
    # alone.  `NestPosC`'s public simulation theorems are stated over
    # `sharedOpsC` (`CheckerC`; `Unknown identifier sharedOpsC`, `:401`),
    # `fueledOpsM` (`BridgeDecl`; `:402`) and `SimC`/`CSOK`/`CState`
    # (`SimC`; `:115`), which the model does not attribute.
    ('ConLeche.Verify.Cached.NestPosC', 'ConLeche.Cached.CheckerC'),
    ('ConLeche.Verify.Cached.NestPosC', 'ConLeche.Verify.BridgeDecl'),
    ('ConLeche.Verify.Cached.NestPosC', 'ConLeche.Verify.Cached.SimC'),
    # lane RECLIB session 5 (HOLE2's files, after HOLE2 closed): nine
    # more, each MEASURED by demoting it alone.  WHY the model calls them
    # demotable: at the tree as it stands it already reports `('pub', M)`
    # imprecision for all four modules (`BlockPosRun`, `NestPosC`,
    # `NestScope`, `PositivityInv`), and the token is per MODULE, so the
    # rebased baseline masks every further demotion there.  Measured
    # failures: `NestScope` without `Positivity` loses `NestCtx`
    # (`:121`), without `Shift` loses `WScoped` (`:27`); `NestPosC`
    # without `NestScope` loses `NestCtxOk` (`:47`); `PositivityInv`
    # without `BlockInstall` loses `BlockParts`/`Expr` (`:26`);
    # `BlockPosRun` without `BlockLfpTup` loses `LfpDatum.CtorPos`
    # (`:185`), without `BlockHoleRead` `Expr.ErasedEqL` (`:114`),
    # without `BlockStageCtors` `BlockNamesOk` (`:165`), without
    # `NestPosMono` `PiPosThen` (`:77`), without `PositivityInv`
    # `BlockParts.nestCtx` (`:172`).  (Its sixth, `Model.Rules.Inputs`,
    # WAS demotable and is demoted.)
    # lane CONTSEM session 4: `ContN2`'s `keyFrame_eq_substE` states
    # `substTau` (`BitSubstFvars`); MEASURED by demoting it alone
    # (`Unknown identifier substTau`, `ContN2.lean:295`).
    ('ConLeche.Model.Inductives.ContN2', 'ConLeche.Model.Annot.BitSubstFvars'),
    # lane NESTIND session 3: `RecCheckRun`'s public statements
    # (`TargetMajorRun fe …`, `TargetTyEntry`) name `FEnv`/`BlockShape`/
    # `ConstantVal`/`Expr`, all through `BlockTail`; MEASURED by demoting it
    # alone (`Unknown identifier FEnv`, `RecCheckRun.lean:66`).
    ('ConLeche.Verify.Inductives.NestScope', 'ConLeche.Kernel.Inductives.Positivity'),
    ('ConLeche.Verify.Inductives.NestScope', 'ConLeche.Verify.Shift'),
    ('ConLeche.Verify.Cached.NestPosC', 'ConLeche.Verify.Inductives.NestScope'),
    ('ConLeche.Verify.Inductives.PositivityInv', 'ConLeche.Kernel.Inductives.BlockInstall'),
    ('ConLeche.Model.Inductives.BlockPosRun', 'ConLeche.Model.Annot.BlockLfpTup'),
    ('ConLeche.Model.Inductives.BlockPosRun', 'ConLeche.Model.Inductives.BlockHoleRead'),
    ('ConLeche.Model.Inductives.BlockPosRun', 'ConLeche.Model.Inductives.BlockStageCtors'),
    ('ConLeche.Model.Inductives.BlockPosRun', 'ConLeche.Model.Inductives.NestPosMono'),
    ('ConLeche.Model.Inductives.BlockPosRun', 'ConLeche.Verify.Inductives.PositivityInv'),
    # task #315 (lane INVERT, the recursor stage's run records): the
    # re-exports the model calls demotable once the positional peels
    # went, each MEASURED by demoting it alone.  `BlockRecRun`'s records
    # are stated over the kernel's stage functions (`Unknown identifier
    # CheckMode`, `:63`); `BlockRecTyShapeRun`'s public statements name `blockRecRdsAV`
    # (`:138`, through `BlockRecMem`), `FieldReadAt` (`:842`, through
    # `BlockRecRule`) and `BlockData` (`:92`, through `BlockRecTyping`);
    # `StructRows` -> `Capstone` is how `BlockRecData` reaches
    # `Rules.RulesInputs.ofSem` (`BlockRecData.lean:3540`, the
    # dot-notation blind class).
    ('ConLeche.Verify.Inductives.BlockRecRun',
     'ConLeche.Kernel.Inductives.BlockInstall'),
    # task #315 (lane RECLIB, the target check's run records): the same
    # class as `BlockRecRun`'s — the records are stated over the kernel's
    # stage functions (`Unknown identifier BlockShape`, `:65`), MEASURED
    # by demoting it alone.
    ('ConLeche.Verify.Inductives.RecCheckRun',
     'ConLeche.Kernel.Inductives.RecCheck'),
    ('ConLeche.Model.Inductives.BlockRecTyShapeRun',
     'ConLeche.Model.Inductives.BlockRecMem'),
    ('ConLeche.Model.Inductives.BlockRecTyShapeRun',
     'ConLeche.Model.Inductives.BlockRecRule'),
    ('ConLeche.Model.Inductives.BlockRecTyShapeRun',
     'ConLeche.Model.Inductives.BlockRecTyping'),
    ('ConLeche.Model.Inductives.StructFrameKit',
     'ConLeche.Model.Capstone'),
    # task #315 (lane GRAPH1, the graph producer): MEASURED by demoting
    # it alone — `BlockRecPreRun`'s own public `@[expose] def
    # BlockRecSplitAt` names `prefOf`/`idxOf`/`majOf` (`Unknown
    # identifier prefOf`, `BlockRecPreRun.lean:280`), which the model
    # does not attribute to an exposed body.
    ('ConLeche.Model.Inductives.BlockRecPreRun',
     'ConLeche.Semantics.Tower.BlockRecTower'),
    # task #315 (lane D-OLD, the old one-member route's dead code
    # deleted): three re-exports the model calls demotable, each MEASURED
    # by demoting it alone.  `StructStageTable.lean`'s `variable` binder
    # gets `[SetTheory V]` through `StructBodyFrames` (`Unknown identifier
    # SetTheory`, `:41`).  `DeclSum` -> `StructStageTable` and
    # `FixAssemblyKit` -> `FixCtorsLoop` are the chain by which the Block
    # route's files see `Model.DomsBelow.getD_below`, a name that
    # `Semantics.DomsBelow.getD_below` shadows once the chain breaks
    # (`BlockRuleGrading.lean:1419`, `BlockKitIhRun.lean:518`: an
    # application type mismatch, the dot-notation blind class).
    ('ConLeche.Model.Inductives.SumKit',
     'ConLeche.Model.Inductives.StructEntryKit'),
    # task #315 (lane RM55, regime IND's rows): `BlockIndRuleRun.lean`'s one
    # remaining `public import` is where its `variable` binder gets
    # `[SetTheory V]` and its public statements get `blockRuleCaAV`.
    # MEASURED: demoting it alone fails the build with `Unknown identifier
    # SetTheory` (`:62`).
    ('ConLeche.Model.Inductives.BlockIndRuleRun',
     'ConLeche.Model.Inductives.BlockRuleCaRun'),
    # task #315 (lane FLOOR, the shake-gate follow-up): `BlockDeclRun`'s
    # two `public import`s, each MEASURED by demoting it alone.  Without
    # `BlockRuleRun` the file's `variable` binder loses `[SetTheory V]`
    # and its public statements `BlockNamesOk`/`blockRecEqs`/`blockRecAcv`
    # (`Unknown identifier SetTheory`, `:48`); without `BlockRecTyShapeRun`
    # its public statements lose `BlockMembersRun` (`:118`).
    ('ConLeche.Model.Inductives.BlockDeclRun',
     'ConLeche.Model.Inductives.BlockRuleRun'),
    ('ConLeche.Model.Inductives.BlockDeclRun',
     'ConLeche.Model.Inductives.BlockRecTyShapeRun'),
    # task #315 (lane ETA1, the k-ary η-closure): `DeclBlockEta.lean`'s two
    # re-exports are named by its PUBLIC statements (`BlockShape`,
    # `consBlockInds`, … through `DeclBlock`; `ExtEta`, `EtaFamiliesClosed`
    # through `EnvGuards`), yet the model reports each individually
    # demotable.  MEASURED, each alone: demoting `DeclBlock` fails with
    # `Unknown identifier BlockShape` (`:53`), demoting `EnvGuards` with
    # `Unknown identifier ExtEta` (`:294`).
    ('ConLeche.Semantics.Inductives.DeclBlockEta',
     'ConLeche.Semantics.Inductives.DeclBlock'),
    ('ConLeche.Semantics.Inductives.DeclBlockEta',
     'ConLeche.Verify.EnvGuards'),
    # task #315 (lane RM52, the level-parameter kit): `BlockRuleParams.lean`
    # re-exports `Model/Inductives/BlockRuleRun.lean` because its `variable`
    # binder gets `[SetTheory V]` through that line and its public statements
    # name `blockRuleIhsRunAV`/`BlockCtorDataI`/`FvarList` (the census sees
    # none of a variable binder's class).  MEASURED: demoting it alone fails
    # the build with `Unknown identifier SetTheory` (`:39`); making
    # `BitLevels` public instead leaves `Unknown identifier FvarList` and
    # `EnvModelM`, the compiler naming `BlockRecRule` back.
    ('ConLeche.Model.Inductives.BlockRuleParams',
     'ConLeche.Model.Inductives.BlockRuleRun'),
    # task #315 (M5, the per-pair rule obligation): `BlockRuleFit.lean`
    # re-exports `Model/Inductives/BlockRecPreRun.lean` because
    # `BlockRecSplitAt` is named by THREE of its public statements, and
    # because that line is where the file's `variable` binder gets
    # `[SetTheory V]` (a class in a variable binder stores no census row —
    # the `BlockStageRec`/`EnvModelM` case below).  MEASURED: demoting it
    # fails the build with `Unknown identifier SetTheory`, and adding
    # `public import ...BlockRecData` instead leaves three `Unknown
    # identifier BlockRecSplitAt` with the compiler naming the line back.
    ('ConLeche.Model.Inductives.BlockRuleFit',
     'ConLeche.Model.Inductives.BlockRecPreRun'),
    # task #315 (M5, the pre-run file, session 22): `BlockRecPreRun.lean`'s
    # four re-exports, each MEASURED by demoting it alone and watching the
    # build fail — the #290 blind class four times over, a plain import
    # being invisible to a PUBLIC statement.  They became demotion
    # candidates for the first time when the file grew §40.7/§40.8 (the
    # census row grew by 56 constants), which is the greedy fixpoint's
    # order-dependence again, one entry below the `BlockRuleFit` one.
    #   BlockRecTyping  — `BlockRecTyShape`, named by `blockIndRegime_run`
    #                     and its satellites (`Unknown identifier
    #                     BlockRecTyShape` at `:5300`);
    #   BlockRecSqI     — `tagIdx` (`:4386`);
    #   BlockRecWfI     — `WfRecKit`/`wfData`, the WF regime's kit
    #                     (`:398`, `:410`);
    #   BlockRecData    — `blockRecTyAV`, which nearly every public
    #                     statement of the file names (`:521`).
    ('ConLeche.Model.Inductives.BlockRecPreRun',
     'ConLeche.Model.Inductives.BlockRecTyping'),
    ('ConLeche.Model.Inductives.BlockRecPreRun',
     'ConLeche.Semantics.Tower.BlockRecSqI'),
    ('ConLeche.Model.Inductives.BlockRecPreRun',
     'ConLeche.Semantics.Tower.BlockRecWfI'),
    ('ConLeche.Model.Inductives.BlockRecPreRun',
     'ConLeche.Model.Inductives.BlockRecData'),
    # task #315 (M5, same session): the entry above is a NEW public edge,
    # and the plan's fixpoint is greedy and order-dependent, so it made
    # `FixAssemblyKit -> FixWitness` look demotable for the first time —
    # a second public path to `FixWitness`'s content now exists.  It is
    # not demotable: MEASURED, demoting it fails the build with
    # `Unknown identifier recAt_iff_rsOf`, which
    # `Model/Inductives/BlockRecPreRun.lean` names in a public statement
    # and reaches only through this re-export.
    ('ConLeche.Model.Inductives.FixKit',
     'ConLeche.Model.Inductives.FixWitness'),
    ('ConLeche.Model.Install',        'ConLeche.Model.Annot.BitExtend'),
    ('ConLeche.Model.Install',        'ConLeche.Semantics.ConstsBound'),
    ('ConLeche.Model.Install',        'ConLeche.Verify.Extend.Sibs'),
    ('ConLeche.Semantics.IndRecsCore','ConLeche.Verify.Denote.EnvExt'),
    ('ConLeche.Semantics.IndRecsCore','ConLeche.Verify.Denote.Levels'),
    # task #315: `BlockTablesStage EXTENDS BlockCtorsStage`, and a
    # structure's PARENT is reached by the generated `toBlockCtorsStage`
    # projection, which no census row attributes to the parent's module;
    # demoting it makes the `extends` clause say `sorryAx is not a
    # structure`.
    ('ConLeche.Model.Inductives.BlockStageTables',
     'ConLeche.Model.Inductives.BlockStageCtors'),
    # task #315 (M5, the recursor stage's Model half): three re-exports of
    # `Model/Inductives/BlockStageRec.lean` that the model drops and the
    # compiler asks back, MEASURED one at a time — `EnvModelM` carries the
    # `[SetTheory V]` the file's `variable` binder needs (a class in a
    # variable binder stores no census row), `BitConsCross` carries
    # `acvalWith` and `NoProjEnv`, and `IndBlockFacts` carries `SwapShList`
    # / `SwapNResS`.  Demoting any one of them fails the build with an
    # `Unknown identifier` at the corresponding name.
    ('ConLeche.Model.Inductives.BlockStageRec',
     'ConLeche.Model.Annot.EnvModelM'),
    ('ConLeche.Model.Inductives.BlockStageRec',
     'ConLeche.Model.Annot.BitConsCross'),
    ('ConLeche.Model.Inductives.BlockStageRec',
     'ConLeche.Semantics.IndBlockFacts'),
    # task #315 (M5, O-1's file): `Model/Inductives/BlockRecRule.lean`
    # re-exports `Model/Inductives/FixRecRead.lean` for `EnvModel`,
    # `FieldReadAt`, `ihTeleAtR`, `ihIdxAtM` and `teleVarsAV`, all of which
    # `denoteMeta_blockIhSpinePis` states.  MEASURED (again at D-NEW):
    # demoting the line alone fails the build with `Unknown identifier
    # ConstsBound`.
    ('ConLeche.Model.Inductives.BlockRecRule',
     'ConLeche.Model.Inductives.FixRecRead'),
    # task #315 (M5, O-1's file, session 5): the same file re-exports
    # `Semantics/Tower/BlockRecTower.lean` for `prefVarsAV`, which the
    # STATEMENT of `prefVars_shift` names.  The census attributes the
    # definition to the module that DEFINES it, but the edge is reached
    # here through the generic reading battery's re-export chain, so the
    # model's candidate demotion is wrong.  MEASURED: demoting the line
    # fails the build with `Unknown identifier prefVarsAV`.
    ('ConLeche.Model.Inductives.BlockRecRule',
     'ConLeche.Semantics.Tower.BlockRecTower'),
    # task #315 (M5, the leaf's membership): `Model/Inductives/BlockRecMem.lean`
    # re-exports `Model/Annot/EnvModelM.lean` for the kernel types its public
    # statements name through the file's `variable` binder (`CheckMode`,
    # `Env`, `ConstantVal`, `BlockShape`, `RecShape`) and
    # `Semantics/Tower/BlockRecTower.lean` for `blockRecAV`/`BlockRecPre`, which
    # appear only in HYPOTHESIS binders of `hmem_of_pre`/`hrd_of_pre` and are
    # attributed to no census row.  MEASURED one at a time: demoting either
    # line fails the build with `Unknown identifier` at exactly those names.
    ('ConLeche.Model.Inductives.BlockRecMem',
     'ConLeche.Model.Annot.EnvModelM'),
    ('ConLeche.Model.Inductives.BlockRecMem',
     'ConLeche.Semantics.Tower.BlockRecTower'),
    # task #253: `PushChain` is an exposed `def … : Prop` whose BODY names
    # `NodupNames` (EnvBound); the model reads statements, not exposed
    # bodies, and the compiler wants the re-export.
    ('ConLeche.Verify.Cached.PushChain','ConLeche.Verify.EnvBound'),
    # task #285: `BasisGen` declares the `#annotate_basis` COMMAND, and
    # `TrustAxioms` invokes it through `BasisA`'s re-export.  A command
    # elaborator is registered, not named, so no census row attributes it —
    # demoting the line makes `TrustAxioms` fail to parse (`unexpected
    # token '#'`), which is task #235's third blind class seen from the
    # other side.  (The fixpoint is order-dependent: this edge became a
    # demotion candidate only when #285 changed the graph around it.)
    ('ConLeche.Kernel.BasisA','ConLeche.Kernel.BasisGen'),
    # task #290: every statement of `Verify/Frontend/Local.lean` is over
    # Naive's `NRes`, `isDigit`, `isWs`; the model calls the edge demotable
    # (the private `import Scan.Equiv` covers the constants), but a private
    # import is invisible to a public statement — the build says
    # `unknown identifier NRes`.
    ('ConLeche.Verify.Frontend.Local','ConLeche.Frontend.Scan.Naive'),
    # task #305 closing: `FixRecRead`'s public signatures resolve
    # `SetTheory`, `AnnotTerm`, `denoteMeta`, `EnvModel` and `openFvars`
    # only through `FixRecReadDefs`'s re-export; the model calls the edge
    # demotable once the file's two new plain imports (`Annot/BitInst`,
    # `Annot/BitRename`, needed after `Model/Steps/*`'s re-exports went)
    # cover the constants, but a plain import is invisible to a public
    # statement (the #290 class) — the build says so for every substitute
    # tried.
    ('ConLeche.Model.Inductives.FixRecRead','ConLeche.Model.Inductives.FixKit'),
    # task #315 M3: `FixTeleBound`'s public statement resolves `SetTheory`
    # (the `open SetTheory` of its namespace block) only through
    # `FixChains`'s re-export; the model calls the edge demotable once the
    # file's other imports cover the constants, but a bare `open` needs the
    # NAMESPACE to exist in the public view — the build says
    # `unknown identifier SetTheory` (#223 §6's first blind class).
    ('ConLeche.Model.Inductives.FixKit','ConLeche.Model.Inductives.FixChains'),
    # task #315 M3: `BlockStageFormer`'s public statements resolve
    # `SetTheory` (its namespace block's bare `open`), `AnnotTerm`,
    # `WellDenotedV` and `Sat` only through `BlockLeafOk`'s re-export; the
    # model calls the edge demotable once the file's two plain imports
    # (`FixStageFormer`, `Verify/Inductives/BlockWF`, both PROOF-only)
    # cover the constants, but a plain import is invisible to a public
    # statement.  Demoting it makes the build say `unknown identifier
    # SetTheory` at the `open`, and adding the `public import
    # ConLeche.SetTheory.Core` lean's own note suggests only moves the
    # failure on to `AnnotTerm`/`WellDenotedV`/`Sat` — both blind classes
    # (#223 §6's first and the #290 one) in one line.
    ('ConLeche.Model.Inductives.BlockStageFormer','ConLeche.Model.Inductives.BlockLeafOk'),
    # task #315 (lane RECLIB session 6, the import gate after the old
    # recursor-stage proofs went): `FixRecRead.lean`'s public statement
    # `denoteMeta_shiftFromN` names `Expr.shiftFromN`, reached only
    # through the `Verify/Inductives/FixRec` re-export.  MEASURED:
    # demoting it alone fails the build with `Unknown constant
    # ConLeche.Expr.shiftFromN` (`:53`).
    ('ConLeche.Model.Inductives.FixRecRead','ConLeche.Verify.Inductives.DirectGen'),
    # lane HOLE2 session 5 (the gate after the slot machinery went): five
    # more, each MEASURED by demoting it alone.  Downstream reaches
    # through three of them (`consList_eq_chainFrame`,
    # `BlockDeclRun.lean:617`; `frameIdx_eq_reverse_map`,
    # `BlockStageCtors.lean:347`; `mkPisAV_below_of`,
    # `BlockRecData.lean:356`); `StoredShapes` states `NoBVar` (it held
    # `LfpHoleWitness`'s slot definitions after lane FLATACC deleted that file)
    # and `FixTeleBound`'s `variable [SetTheory V]` binder resolves
    # through `FixNoBVar` (`:36`).
    ('ConLeche.Model.Inductives.BlockRecGraph','ConLeche.Model.Inductives.BlockRecPreHpre'),
    ('ConLeche.Model.Inductives.FixKit','ConLeche.Semantics.Tower.FixTower'),
    ('ConLeche.Model.Inductives.StoredShapes','ConLeche.Semantics.NoBVar'),
    ('ConLeche.Model.Inductives.FixKit','ConLeche.Model.Inductives.FixNoBVar'),
    # lane HOLE2 stage E2 (the gate after the proof refactor): ten more,
    # each MEASURED by demoting it alone.  The file's own public statements
    # name the re-export: `NoBVar` (`HoleSubst.lean:403`), `Expr.nestOcc`
    # (`NestPosOut.lean:45`), `Expr.ErasedEq` (`:45`), `EnvWF` (`:254`),
    # `paramBvarsAt`/`BlockCtorDataI` (`StoredShapes.lean:784`), `holeP`
    # (`:348`), `HoleIn` (`:419`), the `AnnotTerm`/`denoteMeta` of
    # `BlockHoleRead.lean:350`; downstream reaches through the other two
    # (`mkAppN_wellDenotedV_of_pt`, `BlockRecData.lean:3549`; a `rw` over
    # `nestHoles` stops matching at `BlockHoleGrade.lean:322`).
    ('ConLeche.Model.Inductives.HoleSubst','ConLeche.Semantics.NoBVar'),
    ('ConLeche.Model.Inductives.NestPosOut','ConLeche.Kernel.Inductives.Positivity'),
    ('ConLeche.Model.Inductives.NestPosOut','ConLeche.Verify.Subst'),
    ('ConLeche.Model.Inductives.NestPosOut','ConLeche.Verify.EnvWF'),
    ('ConLeche.Model.Inductives.StoredShapes','ConLeche.Model.Inductives.BlockData'),
    ('ConLeche.Model.Inductives.StoredShapes','ConLeche.Model.Inductives.NestPosMono'),
    ('ConLeche.Model.Inductives.StoredShapes','ConLeche.Model.Inductives.NestPosOut'),
    ('ConLeche.Model.Inductives.BlockHoleRead','ConLeche.Model.Annot.Bit'),
    # lane ALPHA1: after the positivity files' imports narrowed, the model
    # calls six more edges demotable; each MEASURED by demoting it alone,
    # all coverage failures one tier down: `IndFieldGrade` without
    # `IndParamGrade`'s `IndDomGrade` loses `instPisAt_length` (`:117`),
    # without its `IndRuns` `defEqListOk_getD` (`:272`); `IndZipper`
    # without `IndPlainParam`'s `IndFieldGrade` loses `fieldGradeFire`
    # (`:289`), without its `IndPrefixGrade` `prefixGradeFire` (`:258`);
    # `BlockHoleRead` without `FixRec` loses `Expr.ErasedEq` (`:70`);
    # `StructBodyFrames` without `StructRecSpine`'s `IndProjKit` loses
    # `wellDenotedV_instSeq` (`:295`).
    ('ConLeche.Model.IndParamGrade', 'ConLeche.Model.IndDomGrade'),
    ('ConLeche.Model.IndParamGrade', 'ConLeche.Model.IndRuns'),
    ('ConLeche.Model.IndPlainParam', 'ConLeche.Model.IndFieldGrade'),
    ('ConLeche.Model.IndPlainParam', 'ConLeche.Model.IndPrefixGrade'),
    ('ConLeche.Model.Inductives.BlockHoleRead', 'ConLeche.Verify.Inductives.DirectGen'),
    ('ConLeche.Model.Inductives.StructRecKit', 'ConLeche.Model.IndProjKit'),
    # lane RECREST s2: `tgtRecPinsOk`'s public statement names both
    # `blockRecAcv` (BlockRecAssembly) and `RecRulePinsOk` (BlockRecLaw);
    # MEASURED by demoting each alone (unknown identifier,
    # `NestedRecPins.lean:182` and `:185`).
    ('ConLeche.Model.Inductives.NestedRecPins', 'ConLeche.Model.Inductives.BlockRecAssembly'),
    ('ConLeche.Model.Inductives.NestedRecPins', 'ConLeche.Model.Inductives.BlockRecLaw'),
}

files=[f for f in subprocess.check_output(['git','ls-files','*.lean']).decode().split()
       if not f.startswith(('tests/e2e/src/','tests/trust-surface/','_probe/','bridge/','scripts/'))]
mod=lambda f: f[:-5].replace('/','.')
fileof={mod(f):f for f in files}
UMBRELLA={'ConLeche.lean','ConLeche/Term.lean','ConLeche/SetModel.lean','ConLeche/Semantics.lean',
          'ConLeche/Model.lean','ConLeche/Verify/Cached.lean','ConLeche/Verify/Denote.lean',
          'ConLeche/Kernel/Basis.lean','ConLeche/Complete.lean'}
# frozen: the umbrellas exist to re-export, the classic roots have no `public`
# keyword, `tests/*` and the PinGen generator are outside the census roots.
CLASSIC={'tests/ProofDeps.lean','PinDump.lean'}
FROZEN_PREFIX=('tests/','ConLeche/PinGen/','ConLeche/Challenge.lean','ConLeche/PinGen.lean')
EXT=('Std','Lean','Init')

def imports(f):
    out=[]
    for i,l in enumerate(open(f).read().split('\n')):
        m=re.match(r'^(public\s+)?(meta\s+)?import\s+(all\s+)?([A-Za-z0-9_.]+)\s*$', l)
        if m and not m.group(3):
            out.append((i, bool(m.group(1)), bool(m.group(2)), m.group(4)))
    return out

mods=sorted(fileof)
idx={m:i for i,m in enumerate(mods)}
bit={m:1<<i for m,i in idx.items()}

# --- the graph: every non-meta, non-external import edge
D={m:[] for m in mods}
for m in mods:
    for _,_,ismeta,t in imports(fileof[m]):
        if ismeta or t.startswith(EXT): continue
        if t in idx: D[m].append(t)

# --- reach: every module whose constants this module mentions at all
declmod={}
deps=collections.defaultdict(set)
for line in open(DIR+'/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<3: continue
    declmod[p[0]]=p[1]
for line in open(DIR+'/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<4: continue
    for c in p[3].split():
        dm=declmod.get(c)
        if dm and dm in idx and dm!=p[1]: deps[p[1]].add(dm)
reach={m: 0 for m in mods}
for m,s in deps.items():
    if m in idx: reach[m]=sum(bit[x] for x in s if x in idx)

# --- opens: a bare `open N` needs N to EXIST in this module's view, which
# means some module in its cover must declare a constant under that prefix.
# (DESIGN #223 records this as the criterion `shake` misses.)
nsmods=collections.defaultdict(set)
for n,dm in declmod.items():
    parts=n.split('.')
    for k in range(1,len(parts)):
        nsmods['.'.join(parts[:k])].add(dm)
opens={}
for m in mods:
    src=open(fileof[m]).read()
    ns=set()
    for mm in re.finditer(r'^\s*open\s+([^\n]*)', src, re.M):
        seg=mm.group(1).split('--')[0]
        seg=re.sub(r'\(.*?\)','',seg)
        for tok in seg.replace(' in','').split():
            if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', tok) and tok not in ('in','scoped'):
                ns.add(tok)
    opens[m]=[sum(bit[x] for x in nsmods.get(n,()) if x in idx) for n in sorted(ns)]
    opens[m]=[b for b in opens[m] if b]

# --- source identifiers: a lemma named in a TACTIC argument (`simp [f]`,
# `exact h`, …) need not appear in the resulting proof term, so the census
# does not see it.  Add every identifier the source mentions whose name has a
# unique declaring module.  This can only keep MORE imports public, never
# fewer — soundness over aggressiveness.
sufmods=collections.defaultdict(set)
for n,dm in declmod.items():
    if dm not in idx: continue
    parts=n.split('.')
    for k in range(len(parts)):
        sufmods['.'.join(parts[k:])].add(dm)
srcneed={}
for m in mods:
    src=open(fileof[m]).read()
    acc=0
    for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.'!?]*", src)):
        ms=sufmods.get(tok)
        if ms and len(ms)==1:
            d=next(iter(ms))
            if d!=m: acc |= bit[d]
    srcneed[m]=acc

need={m:0 for m in mods}
for line in open(DIR+'/pub.tsv'):
    if '\t' not in line: continue
    m,rest=line.rstrip('\n').split('\t',1)
    if m in idx: need[m]=sum(bit[x] for x in rest.split() if x in idx)

# --- topological order
order=[]; seen=set()
def visit(m, st=()):
    if m in seen or m in st: return
    for t in D[m]: visit(t, st+(m,))
    seen.add(m); order.append(m)
for m in mods: visit(m)

# A module can only depend on what it imports.  The census walks the FINAL
# environment and adds `@[csimp]`/`@[implemented_by]` edges, which an attribute
# in a LATER module can create — those are not import edges and show up as
# impossible backwards dependencies (`Kernel/ExprOps` "needing" `Verify/Level`).
# Restrict both sets to each module's real transitive import closure.
allcl={}
for m in order:
    acc=bit[m]
    for t in D[m]: acc |= allcl.get(t, bit.get(t,0))
    allcl[m]=acc
for m in mods:
    reach[m] = (reach[m] | srcneed[m]) & allcl[m]
    need[m]  &= allcl[m]

P={m:set(D[m]) for m in mods}                    # public imports; start: all

def closures():
    cl={}
    for m in order:
        acc=bit[m]
        for t in P[m]:
            acc |= cl.get(t, bit.get(t,0))
        cl[m]=acc
    return cl

_OKBASE=set()

def violations(cl):
    """Every constraint the configuration `P` breaks, as a set of tokens."""
    out=set()
    for m in mods:
        cov=bit[m]
        pubcov=0
        for t in D[m]:
            cov |= cl[t]
            if t in P[m]: pubcov |= cl[t]
        if reach[m] & ~cov: out.add(('cover', m))
        if need[m] & ~pubcov: out.add(('pub', m))
        for j,b in enumerate(opens[m]):
            if not (b & cov): out.add(('open', m, j))
    return out

def ok(cl):
    return violations(cl) <= _OKBASE

# The STARTING tree is correct by construction — it is the tree that builds —
# so anything the model reports there is the MODEL's imprecision (an `open`
# picked out of a docstring line; a match auxiliary the census attributes to
# the module that first generated it).  Record those and require only that
# nothing gets worse — the model is a filter on candidate demotions, never a
# claim.
def _rebase(label):
    global _OKBASE
    _OKBASE=set()
    b=violations(closures())
    if b: print(f'model imprecision at {label} (ignored):', sorted(b))
    _OKBASE=b

_rebase('baseline')

frozen={m for m in mods
        if fileof[m] in UMBRELLA or fileof[m] in CLASSIC
        or fileof[m].startswith(FROZEN_PREFIX)}
# every module we are allowed to narrow MUST be covered by the census, or its
# dependency set is silently empty and the fixpoint will happily strip it bare
# (that is what an incomplete root list did on the first run: the whole
# `Frontend/*` cone had no rows and lost every re-export).
seen_mods={l.split('\t')[1] for l in open(DIR+'/census.tsv') if '\t' in l}
missing=[m for m in mods if m not in frozen and m not in seen_mods]
assert not missing, f'census does not cover: {missing[:6]} ({len(missing)} modules)'
tot=sum(len(D[m]) for m in mods)

if CHECK:
    # The tree as it stands: an edge is public iff its line says `public`.
    for m in mods:
        pubs=set()
        for _,ispub,ismeta,t in imports(fileof[m]):
            if ismeta or t.startswith(EXT) or t not in idx: continue
            if ispub: pubs.add(t)
        P[m]=pubs & set(D[m])
    _rebase('the tree as it stands')
    bad=[]
    for m in mods:
        if m in frozen: continue
        for t in sorted(P[m]):
            if (m,t) in FALLBACK: continue
            P[m].discard(t)
            if ok(closures()): bad.append((m,t))
            P[m].add(t)
    pub=sum(len(P[m]) for m in mods)
    if bad:
        print(f'DEMOTABLE `public import` ({len(bad)}) — `public import X` is for a '
              're-export something else\'s PUBLIC statement needs:')
        for m,t in bad: print(f'  {fileof[m]}: public import {t}')
        raise SystemExit(1)
    print(f'pub-imports: {pub} of {tot} in-tree edges public, none demotable '
          f'({len(FALLBACK)} dot-notation fallbacks)')
    raise SystemExit(0)

changed=True
while changed:
    changed=False
    for m in reversed(order):                    # importers first
        if m in frozen: continue
        for t in sorted(P[m]):
            P[m].discard(t)
            if ok(closures()):
                changed=True
            else:
                P[m].add(t)
pub=sum(len(P[m]) for m in mods)
print(f'{pub} of {tot} in-tree import edges must stay public  ->  {tot-pub} narrow')
json.dump({m:sorted(P[m]) for m in mods}, open(DIR+'/plan.json','w'))
