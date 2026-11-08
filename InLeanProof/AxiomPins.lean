module

public import InLeanProof.Ops
public import InLeanProof.Statement
public import InLeanProof.Sim
public import InLeanProof.FVar
public import InLeanProof.Range
public import InLeanProof.KnotI
public import InLeanProof.StateOpsI
public import InLeanProof.WalksDefeq
public import InLeanProof.WalksWhnf
public import InLeanProof.WalksIota
public import InLeanProof.WalksWhnfLoop
public import InLeanProof.WalksInfer
public import InLeanProof.KnotAssembly
public import InLeanProof.SquarePilot
public import InLeanProof.IotaViews
public import InLeanProof.LeafGuardI
public import InLeanProof.WalksIotaRec
public import InLeanProof.WalksInferBody
public import InLeanProof.BodiesI
public import InLeanProof.EnvPresI
public import InLeanProof.EnvBodiesPres
public import InLeanProof.QuotPres
public import InLeanProof.IndPres
public import InLeanProof.StepPres
public import InLeanProof.IndMembers
public import InLeanProof.IndBasis
public import InLeanProof.PassEnv
public import InLeanProof.PassCtors
public import InLeanProof.BlockPresR
public import InLeanProof.PassNest
public import InLeanProof.DeclStep
public import InLeanProof.DeclPins
public import InLeanProof.ProjGuardI
public import InLeanProof.PassUniform
public import InLeanProof.PassNestKey
public import InLeanProof.PassClasses
public import InLeanProof.PassTail
public import InLeanProof.PassRecs
public import InLeanProof.PassRecs2
public import InLeanProof.PassRecs3
public import InLeanProof.PassRecs4
public import InLeanProof.PassRecs5
public import InLeanProof.PassRecs6
public import InLeanProof.PassRecs7

/-!
# The axiom pins of the InLean proof tier (task #451, lane G)

Exactly which axioms the tier's theorems may use: the standard three and, where
a walk's cutoff reads a cached field, the stop-gap axioms of
`InLeanProof/MkDataAxioms.lean`.  A drift is a build error.  The two proofs
that read no cached field pin the standard axioms alone.
-/

/-- info: 'InLeanProof.mapOff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.mapOff_spec

/--
info: 'InLeanProof.no_false_of_addDeclSound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.no_false_of_addDeclSound

/--
info: 'InLeanProof.Expr.fieldsOk' depends on axioms: [propext,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.Expr.fieldsOk

/--
info: 'InLeanProof.toExpr_liftLooseBVars' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_liftLooseBVars

/--
info: 'InLeanProof.toExpr_instantiate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_instantiate

/-- info: 'InLeanProof.memoEI_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.memoEI_ok

/-- info: 'InLeanProof.memoBI_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.memoBI_ok

/-- info: 'InLeanProof.ensureSortI_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ensureSortI_ok

/-- info: 'InLeanProof.toExpr_of_clEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.toExpr_of_clEq

/-- info: 'InLeanProof.data_eraseK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.data_eraseK

/-- info: 'InLeanProof.mkFVarM_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.mkFVarM_ok

/-- info: 'InLeanProof.FVTableOK.trans_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.FVTableOK.trans_inj

/-- info: 'InLeanProof.clEq_iff_TransS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.clEq_iff_TransS

/-- info: 'InLeanProof.erase_eq_of_toExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.erase_eq_of_toExpr

/-- info: 'InLeanProof.clHash_of_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.clHash_of_erase

/-- info: 'InLeanProof.RangeOk_instantiate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.RangeOk_instantiate

/-- info: 'InLeanProof.RangeOk_abstractDepthsFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.RangeOk_abstractDepthsFrom

/--
info: 'InLeanProof.RangeOk_instantiateLevelParams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.RangeOk_instantiateLevelParams

/-- info: 'InLeanProof.FVarTable.trans_depthOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.FVarTable.trans_depthOK

/-- info: 'InLeanProof.RangeOk_of_inRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.RangeOk_of_inRange

/-- info: 'InLeanProof.anyNode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.anyNode_spec

/-- info: 'InLeanProof.toExpr_getAppFnT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.toExpr_getAppFnT

/-- info: 'InLeanProof.toExpr_getAppArgsT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.toExpr_getAppArgsT

/-- info: 'InLeanProof.getAppNumArgsT_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.getAppNumArgsT_eq

/-- info: 'InLeanProof.depthS_subst_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.depthS_subst_le

/--
info: 'InLeanProof.toExpr_instantiate1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_instantiate1

/--
info: 'InLeanProof.toExpr_instantiateRev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_instantiateRev

/--
info: 'InLeanProof.toExpr_abstractDepthsFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_abstractDepthsFrom

/--
info: 'InLeanProof.toExpr_instantiateLevelParams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_instantiateLevelParams

/--
info: 'InLeanProof.toExpr_hasLooseBVar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_hasLooseBVar

/--
info: 'InLeanProof.looseBVarRange_toExpr' depends on axioms: [propext,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.looseBVarRange_toExpr

/--
info: 'InLeanProof.hasFVar_toExpr' depends on axioms: [propext,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.hasFVar_toExpr

/--
info: 'InLeanProof.instLevelParamsChecked_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instLevelParamsChecked_ok

/-- info: 'InLeanProof.ensureSortI_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ensureSortI_spec

/--
info: 'InLeanProof.whnfCoreStepI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfCoreStepI_spec

/-- info: 'InLeanProof.ssimI_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ssimI_zero

/-- info: 'InLeanProof.ensureSortI_by_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ensureSortI_by_square

/--
info: 'InLeanProof.TrS_inst1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.TrS_inst1

/-! ## The state operations' triples (lane P2-whnf, `InLeanProof/StateOpsI.lean`) -/

/--
info: 'InLeanProof.tripleI_iff_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.tripleI_iff_run

/--
info: 'InLeanProof.inst1M_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inst1M_specI

/--
info: 'InLeanProof.instListRevM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instListRevM_specI

/--
info: 'InLeanProof.abstractRangeM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.abstractRangeM_specI

/--
info: 'InLeanProof.instLevelParamsM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instLevelParamsM_specI

/--
info: 'InLeanProof.liftFueled_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.liftFueled_specI

/--
info: 'InLeanProof.CSOKI.of_tabLe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.CSOKI.of_tabLe

/--
info: 'InLeanProof.mkFVarM_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mkFVarM_specI

/--
info: 'InLeanProof.instListM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instListM_specI

/--
info: 'InLeanProof.constTyAtM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.constTyAtM_specI

/--
info: 'InLeanProof.constValAtM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.constValAtM_specI

/--
info: 'InLeanProof.ruleRhsAtM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ruleRhsAtM_specI

/--
info: 'InLeanProof.leqCore_trL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.leqCore_trL

/--
info: 'InLeanProof.isEquivLM_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.isEquivLM_specI

/--
info: 'InLeanProof.isEquivListLM_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.isEquivListLM_specI

/-! ## The body walks, part 1 (lane P2-whnf, `InLeanProof/WalksWhnf.lean`) -/

/--
info: 'InLeanProof.defeqArgI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defeqArgI_spec

/--
info: 'InLeanProof.defEqListI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defEqListI_spec

/--
info: 'InLeanProof.litToCtorIfNatI_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.litToCtorIfNatI_specI

/--
info: 'InLeanProof.projLitToCtorI_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.projLitToCtorI_specI

/--
info: 'InLeanProof.litMajorToCtorI_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.litMajorToCtorI_specI

/--
info: 'InLeanProof.defeqSpineI_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defeqSpineI_specI

/-! The last `DiscC1` twins (the same file): the cache reads and the bulk
instantiation use the stop-gap axioms through `StateOpsI`. -/

/--
info: 'InLeanProof.unfoldDefinitionI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.unfoldDefinitionI_specI

/--
info: 'InLeanProof.iotaCertsFullIAux_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.iotaCertsFullIAux_specI

/--
info: 'InLeanProof.iotaCertsFullI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.iotaCertsFullI_specI

/--
info: 'InLeanProof.reduceNatI_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.reduceNatI_specI

/-! ## The body walks, part 2 (lane P2-whnf, `InLeanProof/WalksIota.lean`): interning and
instantiation read cached fields, hence the stop-gap axioms. -/

/--
info: 'InLeanProof.formerSortLoopI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.formerSortLoopI_specI

/--
info: 'InLeanProof.formerNeverZeroI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.formerNeverZeroI_specI

/--
info: 'InLeanProof.iotaCase3I_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.iotaCase3I_specI

/--
info: 'InLeanProof.iotaIndexOkI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.iotaIndexOkI_specI

/-! ## The body walks, part 3 (lane P2-whnf, `InLeanProof/WalksWhnfLoop.lean`) -/

/--
info: 'InLeanProof.whnfLoopI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfLoopI_specI

/--
info: 'InLeanProof.whnfBodyI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfBodyI_specI

/--
info: 'InLeanProof.betaPeelI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.betaPeelI_specI

/--
info: 'InLeanProof.whnfCoreLoopI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfCoreLoopI_specI

/--
info: 'InLeanProof.whnfCoreBodyI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfCoreBodyI_specI

/--
info: 'InLeanProof.whnfAppI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfAppI_specI

/--
info: 'InLeanProof.reduceProjCoreI_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.reduceProjCoreI_specI

/-! ## The body walks, part 4 (lane P2-whnf, phase 4: `InLeanProof/IotaViews.lean`,
`LeafGuardI.lean`, `WalksIotaRec.lean`): the ι step -/

/-- info: 'InLeanProof.isCtorAppC_TrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.isCtorAppC_TrS

/-- info: 'InLeanProof.towerSlotsAllF_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.towerSlotsAllF_V

/-- info: 'InLeanProof.andRescueSlotsF_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.andRescueSlotsF_V

/--
info: 'InLeanProof.substLevelTreesM_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.substLevelTreesM_specI

/--
info: 'InLeanProof.pinArgsI_TrS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.pinArgsI_TrS

/--
info: 'InLeanProof.wscopedBC_of_WScoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.wscopedBC_of_WScoped

/--
info: 'InLeanProof.closedBV_of_lbb' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.closedBV_of_lbb

/--
info: 'InLeanProof.leafGuardSpecI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.leafGuardSpecI

/--
info: 'InLeanProof.majorToCtorI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.majorToCtorI_specI

/--
info: 'InLeanProof.prepareMajorI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.prepareMajorI_specI

/--
info: 'InLeanProof.iotaCertIL_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.iotaCertIL_specI

/--
info: 'InLeanProof.iotaRecI_specI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.iotaRecI_specI

/--
info: 'InLeanProof.whnfAppI_specI_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfAppI_specI_of

/-! ### Lane P2-defeq (`InLeanProof/WalksDefeq.lean`) -/

/--
info: 'InLeanProof.boolTrueShortcutI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.boolTrueShortcutI_spec

/--
info: 'InLeanProof.proofIrrelI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.proofIrrelI_spec

/--
info: 'InLeanProof.propIrrelI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.propIrrelI_spec

/--
info: 'InLeanProof.etaCertI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.etaCertI_spec

/--
info: 'InLeanProof.structUnitCertI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.structUnitCertI_spec

/--
info: 'InLeanProof.structEtaCertWithI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.structEtaCertWithI_spec

/--
info: 'InLeanProof.structEtaCertI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.structEtaCertI_spec

/--
info: 'InLeanProof.stuckIrrelI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.stuckIrrelI_spec

/--
info: 'InLeanProof.defeqLamsInnerI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defeqLamsInnerI_spec

/--
info: 'InLeanProof.lamsStepL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.lamsStepL_spec

/--
info: 'InLeanProof.lamsSpecI_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.lamsSpecI_all

/--
info: 'InLeanProof.quickDefEqI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.quickDefEqI_spec

/--
info: 'InLeanProof.defeqOffsetI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defeqOffsetI_spec

/--
info: 'InLeanProof.tryUnfoldProjAppI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.tryUnfoldProjAppI_spec

/--
info: 'InLeanProof.deltaQuickI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.deltaQuickI_spec

/--
info: 'InLeanProof.lazyDeltaStepI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.lazyDeltaStepI_spec

/--
info: 'InLeanProof.ldrStepL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ldrStepL_spec

/--
info: 'InLeanProof.ldrNatBL_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ldrNatBL_spec

/--
info: 'InLeanProof.ldrNatAL_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ldrNatAL_spec

/--
info: 'InLeanProof.ldrOffL_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ldrOffL_spec

/--
info: 'InLeanProof.lazySpecI_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.lazySpecI_all

/--
info: 'InLeanProof.lazyProjSpecI_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.lazyProjSpecI_all

/--
info: 'InLeanProof.defeqProjPairI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.defeqProjPairI_spec

/--
info: 'InLeanProof.defeqStuckI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.defeqStuckI_spec

/--
info: 'InLeanProof.bodyTailL_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.bodyTailL_spec

/--
info: 'InLeanProof.bodyLazyL_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.bodyLazyL_spec

/--
info: 'InLeanProof.bodyQ2L_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.bodyQ2L_spec

/--
info: 'InLeanProof.bodyPIL_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.bodyPIL_spec

/--
info: 'InLeanProof.bodyQ1L_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.bodyQ1L_spec

/--
info: 'InLeanProof.defeqBodyI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.defeqBodyI_spec

/--
info: 'InLeanProof.clBeq_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.clBeq_TrS

/--
info: 'InLeanProof.lamPairI_some' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.lamPairI_some

/--
info: 'InLeanProof.lamPairI_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.lamPairI_none

/--
info: 'InLeanProof.natPredI_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.natPredI_TrS

/--
info: 'InLeanProof.sameConstHeads_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.sameConstHeads_TrS

/--
info: 'InLeanProof.strLit_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.strLit_TrS

/--
info: 'InLeanProof.fvarDepth_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.fvarDepth_TrS

/--
info: 'InLeanProof.structUnitCert_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.structUnitCert_eq

/--
info: 'InLeanProof.structEtaCertWith_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.structEtaCertWith_eq

/--
info: 'InLeanProof.inferLamsOutI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferLamsOutI_spec

/--
info: 'InLeanProof.inferLamsLeafI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferLamsLeafI_spec

/--
info: 'InLeanProof.inferLamsI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferLamsI_spec

/--
info: 'InLeanProof.inferPisOut_trL' does not depend on any axioms
-/
#guard_msgs in
#print axioms InLeanProof.inferPisOut_trL

/--
info: 'InLeanProof.inferPisLeafI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferPisLeafI_spec

/--
info: 'InLeanProof.inferPisI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferPisI_spec

/--
info: 'InLeanProof.inferSpinePiI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferSpinePiI_spec

/--
info: 'InLeanProof.inferSpineWhnfI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferSpineWhnfI_spec

/--
info: 'InLeanProof.inferSpineI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferSpineI_spec

/--
info: 'InLeanProof.inferSpineIOWhnfI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferSpineIOWhnfI_spec

/--
info: 'InLeanProof.inferSpineIOI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferSpineIOI_spec

/--
info: 'InLeanProof.zeroWhereZero_trL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.zeroWhereZero_trL

/--
info: 'InLeanProof.checkGuardRowsI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkGuardRowsI_spec

/--
info: 'InLeanProof.stripTop_of_TrS_lam_binderOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.stripTop_of_TrS_lam_binderOf

/--
info: 'InLeanProof.stripTop_of_TrS_forallE_binderOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.stripTop_of_TrS_forallE_binderOf

/--
info: 'InLeanProof.mkFVarM_tys' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mkFVarM_tys

/--
info: 'InLeanProof.memoEI_infer_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.memoEI_infer_specI

/--
info: 'InLeanProof.memoEI_whnfCore_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.memoEI_whnfCore_specI

/--
info: 'InLeanProof.memoEI_whnf_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.memoEI_whnf_specI

/--
info: 'InLeanProof.memoEI_inferIO_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.memoEI_inferIO_specI

/--
info: 'InLeanProof.memoBI_defeq_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.memoBI_defeq_specI

/--
info: 'InLeanProof.defeqE_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defeqE_specI

/--
info: 'InLeanProof.CSOKI.enterEager' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.CSOKI.enterEager

/--
info: 'InLeanProof.CSOKI.leaveEager' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.CSOKI.leaveEager

/--
info: 'InLeanProof.ssimI_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ssimI_succ

/--
info: 'InLeanProof.ssimI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ssimI

/--
info: 'InLeanProof.closure_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.closure_spec

/--
info: 'InLeanProof.closure_contains_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.closure_contains_iff

/--
info: 'InLeanProof.leafGuard_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.leafGuard_value

/--
info: 'InLeanProof.okLv_inferPisOutI' depends on axioms: [propext, Quot.sound, InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.okLv_inferPisOutI

/--
info: 'InLeanProof.okLv_succ_of_fits' depends on axioms: [propext, Quot.sound, InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.okLv_succ_of_fits

/--
info: 'InLeanProof.okLv_imax_of_fits' depends on axioms: [propext, Quot.sound, InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.okLv_imax_of_fits

/--
info: 'InLeanProof.Pure.runs_inferLams_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.Pure.runs_inferLams_tail

/--
info: 'InLeanProof.Pure.runs_inferPis_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.Pure.runs_inferPis_tail

/--
info: 'InLeanProof.Pure.closed_lamTail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.Pure.closed_lamTail

/--
info: 'InLeanProof.leavesBounded_TrS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.leavesBounded_TrS

/--
info: 'InLeanProof.inferLamsI_tail_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferLamsI_tail_spec

/--
info: 'InLeanProof.inferPisI_tail_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferPisI_tail_spec

/--
info: 'InLeanProof.ensureSortIOI_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ensureSortIOI_spec

/--
info: 'InLeanProof.fvarTypeM_specI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.fvarTypeM_specI

/--
info: 'InLeanProof.typeAtI_TrS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.typeAtI_TrS

/--
info: 'InLeanProof.inferBodyI_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferBodyI_leaf

/--
info: 'InLeanProof.inferBodyI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferBodyI_spec

/--
info: 'InLeanProof.inferBodyIOI_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.inferBodyIOI_spec

/--
info: 'InLeanProof.bodiesI_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.bodiesI_of

/--
info: 'InLeanProof.ssimI_of_env' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ssimI_of_env

-- Lane P3a (O4): the six environment hypotheses from `EnvPresI`, and its preservation.

/--
info: 'InLeanProof.envRelI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envRelI_of

/--
info: 'InLeanProof.envDomI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envDomI_of

/--
info: 'InLeanProof.envDefnI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envDefnI_of

/--
info: 'InLeanProof.envViewI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envViewI_of

/--
info: 'InLeanProof.envRecI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envRecI_of

/--
info: 'InLeanProof.defeqEnvI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.defeqEnvI_of

/--
info: 'InLeanProof.envHyps_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envHyps_of

/--
info: 'InLeanProof.presI_push' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_push

/--
info: 'InLeanProof.presI_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_one

/--
info: 'InLeanProof.presI_axiom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_axiom

/--
info: 'InLeanProof.presI_defn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_defn

/--
info: 'InLeanProof.presI_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_thm

/--
info: 'InLeanProof.presI_opaque' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_opaque

/--
info: 'InLeanProof.presI_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_empty

-- Lane P3b: `EnvBodiesI` from the relation, the quotient group.

/--
info: 'InLeanProof.envProjI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envProjI_of

/--
info: 'InLeanProof.envBodiesI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envBodiesI_of

/--
info: 'InLeanProof.ssimI_of_pres' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ssimI_of_pres

/--
info: 'InLeanProof.envWF_of_modelOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.envWF_of_modelOk

/--
info: 'InLeanProof.emvarS_instantiateLevelParams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.emvarS_instantiateLevelParams

/--
info: 'InLeanProof.presI_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_congr

/--
info: 'InLeanProof.checkQuotC_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkQuotC_ok

/--
info: 'InLeanProof.quotGroupPres' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.quotGroupPres

/--
info: 'InLeanProof.find_foldl_addConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.find_foldl_addConst

/--
info: 'InLeanProof.presI_group' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_group

/--
info: 'InLeanProof.toCaps_capsOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.toCaps_capsOf

/--
info: 'InLeanProof.ctorsStored_of_pres' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ctorsStored_of_pres

/--
info: 'InLeanProof.inRange_of_projBodiesInRange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.inRange_of_projBodiesInRange

/--
info: 'InLeanProof.projBodiesInRange_of_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.projBodiesInRange_of_none

/--
info: 'InLeanProof.findProj_foldl_old' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.findProj_foldl_old

/--
info: 'InLeanProof.projBodiesInRange_group' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.projBodiesInRange_group

/--
info: 'InLeanProof.projBodiesInRange_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.projBodiesInRange_one

/--
info: 'InLeanProof.mem_storedBlock' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mem_storedBlock

/--
info: 'InLeanProof.storedBlock_all' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.storedBlock_all

/--
info: 'InLeanProof.checkInductiveC_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkInductiveC_ok

/--
info: 'InLeanProof.projBodiesInRange_ind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.projBodiesInRange_ind

/--
info: 'InLeanProof.storedBlock_of_checkInductiveC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.storedBlock_of_checkInductiveC

/--
info: 'InLeanProof.checkAxiomC_quotSound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkAxiomC_quotSound

/--
info: 'InLeanProof.presI_quotSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.presI_quotSound

/--
info: 'InLeanProof.checkShapelessS_run_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkShapelessS_run_ne

/--
info: 'InLeanProof.checkIndDeclC_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkIndDeclC_ok

/--
info: 'InLeanProof.toBlock_names' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.toBlock_names

/--
info: 'InLeanProof.basisNameHit_toBlock' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.basisNameHit_toBlock

/-! ## O7: the inductive job (lane O7) -/

/-- info: 'InLeanProof.toBlock_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.toBlock_eq

/-- info: 'InLeanProof.blockSplit_tr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.blockSplit_tr

/-- info: 'InLeanProof.blockShape?_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockShape?_tr

/-- info: 'InLeanProof.indParamsOk_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.indParamsOk_tr

/-- info: 'InLeanProof.basisNameHit_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.basisNameHit_tr

/-- info: 'InLeanProof.flushI_csoki' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.flushI_csoki

/-- info: 'InLeanProof.opsSimI_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.opsSimI_of

/--
info: 'InLeanProof.JobEnvI.ops' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.JobEnvI.ops

/--
info: 'InLeanProof.genEntriesAgree_noSt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.genEntriesAgree_noSt

/--
info: 'InLeanProof.checkShapelessS_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkShapelessS_not_ok

/--
info: 'InLeanProof.checkIndDeclC_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.checkIndDeclC_sim

/-- info: 'InLeanProof.blockIsRec_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockIsRec_tr

/--
info: 'InLeanProof.reduceMembersSimI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.reduceMembersSimI_of

/-- info: 'InLeanProof.blockShape?_memberOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockShape?_memberOk

/-- info: 'InLeanProof.blockKSSimI_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockKSSimI_of

/--
info: 'InLeanProof.reduceMemberSimI_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.reduceMemberSimI_of

/--
info: 'InLeanProof.blockKSSimI_of_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.blockKSSimI_of_stages

/--
info: 'InLeanProof.passTailSimI_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.passTailSimI_of

/--
info: 'InLeanProof.checkIndDeclC_sim_stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkIndDeclC_sim_stages

/--
info: 'InLeanProof.CIRange_of_constInRange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.CIRange_of_constInRange

/-! ## O7, continued: the reduct and the pinned blocks -/

/--
info: 'InLeanProof.whnfTelescopeI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.whnfTelescopeI_run

/--
info: 'InLeanProof.closeTelescope_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.closeTelescope_tr

/-- info: 'InLeanProof.reducedFormer_emvar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.reducedFormer_emvar

/--
info: 'InLeanProof.reducedFormerSimI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.reducedFormerSimI

/-- info: 'InLeanProof.toBlock_CIOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.toBlock_CIOk

/-- info: 'InLeanProof.pins_tr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.pins_tr

/-- info: 'InLeanProof.pins_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.pins_ok

/--
info: 'InLeanProof.pinAgrees_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.pinAgrees_tr

/--
info: 'InLeanProof.pinCopyOk_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.pinCopyOk_tr

/--
info: 'InLeanProof.listBeqBy_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.listBeqBy_tr

/-- info: 'InLeanProof.pinLinkOk_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.pinLinkOk_tr

/-- info: 'InLeanProof.blockLinksOk_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockLinksOk_tr

/--
info: 'InLeanProof.checkIndDeclC_sim_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkIndDeclC_sim_rest

/-- info: 'InLeanProof.FEnv.find?_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.FEnv.find?_congr

/-- info: 'InLeanProof.capsOf_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.capsOf_congr

/-- info: 'InLeanProof.sees_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.sees_safe

/-- info: 'InLeanProof.FEnv_find_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.FEnv_find_none

/-- info: 'InLeanProof.fresh_of_checkInductiveC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.fresh_of_checkInductiveC

/-- info: 'InLeanProof.sees_of_checkInductiveC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.sees_of_checkInductiveC

/-- info: 'InLeanProof.quot_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.quot_safe

/--
info: 'InLeanProof.openPisAtFvarsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.openPisAtFvarsI_run

/-- info: 'InLeanProof.checkBlockTeleFI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkBlockTeleFI_run

/-- info: 'InLeanProof.checkBlockDomsAtFI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkBlockDomsAtFI_run

/--
info: 'InLeanProof.checkBlockAgreeFI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkBlockAgreeFI_run

/--
info: 'InLeanProof.checkBlockIndsFI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkBlockIndsFI_run

/-- info: 'InLeanProof.presI_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.presI_mark

/-- info: 'InLeanProof.presI_marked_former' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.presI_marked_former

/-- info: 'InLeanProof.presI_consBlockIndsF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.presI_consBlockIndsF

/-- info: 'InLeanProof.presI_formers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.presI_formers

/-- info: 'InLeanProof.blockShape?_members' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockShape?_members

/-- info: 'InLeanProof.checkBlockIndsF_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkBlockIndsF_fresh

/-- info: 'InLeanProof.MarkedExt.findProj?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.MarkedExt.findProj?

/-- info: 'InLeanProof.markedExt_consBlockIndsF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.markedExt_consBlockIndsF

/-- info: 'InLeanProof.jobEnvI_formers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.jobEnvI_formers

/-- info: 'InLeanProof.openPisAtFvars_resolve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.openPisAtFvars_resolve

/-- info: 'InLeanProof.constsResolveF_noSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.constsResolveF_noSt

/-- info: 'InLeanProof.TrS_of_clEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.TrS_of_clEq

/-- info: 'InLeanProof.structCtorResidOk_TrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.structCtorResidOk_TrS

/-- info: 'InLeanProof.checkStructDomsAtFI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkStructDomsAtFI_run

/-- info: 'InLeanProof.checkStructFieldSortsIFI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkStructFieldSortsIFI_run

/--
info: 'InLeanProof.checkSumCtorFI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkSumCtorFI_run

/--
info: 'InLeanProof.checkBlockCtorsFI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkBlockCtorsFI_run

/-! Lane P3r: `BlockPresObl`'s recognised branch (`BlockPresR.lean`). -/

/--
info: 'InLeanProof.toExpr_instantiate1L' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.toExpr_instantiate1L

/--
info: 'InLeanProof.projBodyAt_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.projBodyAt_tr

/-- info: 'InLeanProof.hasPis_iff_structProjBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.hasPis_iff_structProjBodies

/-- info: 'InLeanProof.genEntriesAgree_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.genEntriesAgree_facts

/-- info: 'InLeanProof.checkBlockKS_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkBlockKS_cover

/-- info: 'InLeanProof.blockShape?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockShape?_spec

/--
info: 'InLeanProof.dropVars_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.dropVars_tr

/--
info: 'InLeanProof.recFire_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.recFire_tr

/-- info: 'InLeanProof.recogCtx_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.recogCtx_of

/--
info: 'InLeanProof.RecogCtx.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.RecogCtx.entry

/--
info: 'InLeanProof.RecogCtx.table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.RecogCtx.table

/--
info: 'InLeanProof.blockPresOblP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.blockPresOblP

/--
info: 'InLeanProof.indGroupPresBP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.indGroupPresBP

/-- info: 'InLeanProof.toDecl_recognised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.toDecl_recognised

/-- info: 'InLeanProof.fieldsOkB_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.fieldsOkB_mono

/-- info: 'InLeanProof.projStepsOk_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.projStepsOk_mono

/-- info: 'InLeanProof.projStepsAll_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.projStepsAll_of_ok

/-- info: 'InLeanProof.projStepsAllOk_of_checkInductiveC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.projStepsAllOk_of_checkInductiveC

/--
info: 'InLeanProof.instPisWithI_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instPisWithI_tr

/-- info: 'InLeanProof.cNestHoles_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.cNestHoles_eq

/--
info: 'InLeanProof.nestHolesLoopI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestHolesLoopI_run

/--
info: 'InLeanProof.nestHolesI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestHolesI_run

/-- info: 'InLeanProof.trShape_formers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.trShape_formers

/--
info: 'InLeanProof.blockNestCtxI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.blockNestCtxI_run

/-- info: 'InLeanProof.anySpec_nestOcc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.anySpec_nestOcc

/-- info: 'InLeanProof.nestOccI_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.nestOccI_tr

/-- info: 'InLeanProof.piDomsOccI_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.piDomsOccI_tr

/-- info: 'InLeanProof.TrS_not_fvar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.TrS_not_fvar

/-- info: 'InLeanProof.TrS_stripTop_fvar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.TrS_stripTop_fvar

/-- info: 'InLeanProof.phAppI_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.phAppI_tr

/-- info: 'InLeanProof.replaceApps_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.replaceApps_eq

/-- info: 'InLeanProof.raF_hole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.raF_hole

/-- info: 'InLeanProof.replaceAppsI_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.replaceAppsI_tr

/-- info: 'InLeanProof.trShape_nP' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.trShape_nP

/-! ## Lane O6: the declaration step for the non-inductive kinds -/

/-- info: 'InLeanProof.crNF_of_infer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.crNF_of_infer

/-- info: 'InLeanProof.constsResolve_of_infer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.constsResolve_of_infer

/-- info: 'InLeanProof.okC_of_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.okC_of_flags

/-- info: 'InLeanProof.collect_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.collect_complete

/-- info: 'InLeanProof.levelParams_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.levelParams_complete

/--
info: 'InLeanProof.allLevelParamsDefined_of_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.allLevelParamsDefined_of_guard

/--
info: 'InLeanProof.checkTermWF_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkTermWF_ok

/-- info: 'InLeanProof.litShapeOk_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.litShapeOk_tr

/-- info: 'InLeanProof.natOpName_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.natOpName_tr

/--
info: 'InLeanProof.checkConstantValC_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkConstantValC_sim

/--
info: 'InLeanProof.checkConstantValFSimI' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkConstantValFSimI

/--
info: 'InLeanProof.checkValueC_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkValueC_sim

/--
info: 'InLeanProof.checkThmC_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkThmC_sim

/--
info: 'InLeanProof.checkDefnC_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkDefnC_sim

/--
info: 'InLeanProof.checkOpaqueC_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkOpaqueC_sim

/--
info: 'InLeanProof.checkAxiomC_quotSound_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkAxiomC_quotSound_sim

/--
info: 'InLeanProof.checkAxiomC_sorry_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkAxiomC_sorry_sim

/-- info: 'InLeanProof.checkQuotC_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkQuotC_sim

/-- info: 'InLeanProof.quotFold_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.quotFold_ok

/--
info: 'InLeanProof.checkDeclKindC_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkDeclKindC_sim

/--
info: 'InLeanProof.checkDecl_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkDecl_sim

/--
info: 'InLeanProof.checkDeclKindC_sim_cert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkDeclKindC_sim_cert

/-! ## Lane O6: the pinned families -/

/-- info: 'InLeanProof.matchesPin_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.matchesPin_tr

/-- info: 'InLeanProof.pinFoundInd_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.pinFoundInd_tr

/-- info: 'InLeanProof.pinFoundCtor_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.pinFoundCtor_tr

/-- info: 'InLeanProof.pinFoundRec_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.pinFoundRec_tr

/-- info: 'InLeanProof.stdAxiomOk_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.stdAxiomOk_tr

/-- info: 'InLeanProof.trustCompilerOk_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.trustCompilerOk_tr

/-- info: 'InLeanProof.reduceElemOk_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.reduceElemOk_tr

/-- info: 'InLeanProof.reduceStoredOk_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.reduceStoredOk_tr

/-- info: 'InLeanProof.ofReduceAxOk_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ofReduceAxOk_tr

/--
info: 'InLeanProof.checkAxiomC_pinned_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkAxiomC_pinned_sim

/--
info: 'InLeanProof.checkReducePin_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkReducePin_sim

/--
info: 'InLeanProof.checkOpaqueC_reduce_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkOpaqueC_reduce_sim

/-- info: 'InLeanProof.checkDecl_sim_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkDecl_sim_of

/--
info: 'InLeanProof.checkDeclKindC_sim_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkDeclKindC_sim_full

/--
info: 'InLeanProof.checkDecl_sim_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkDecl_sim_full

/--
info: 'InLeanProof.pinListOk_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.pinListOk_tr

/--
info: 'InLeanProof.basisNamesOk_ind_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.basisNamesOk_ind_tr

/-- info: 'InLeanProof.checkDecl_of_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.checkDecl_of_kind

/-- info: 'InLeanProof.basisNamesOk_toDecl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.basisNamesOk_toDecl

/--
info: 'InLeanProof.projGuardSpecI_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.projGuardSpecI_of

/--
info: 'InLeanProof.projGuardRowsGoI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.projGuardRowsGoI_run

/-- info: 'InLeanProof.LvFits_zero_of_RangeOk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.LvFits_zero_of_RangeOk

/-- info: 'InLeanProof.maxDepthS_params' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.maxDepthS_params

/-- info: 'InLeanProof.params_okLv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.params_okLv

/-- info: 'InLeanProof.params_trL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.params_trL

/--
info: 'InLeanProof.instLvlParamsI_params_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instLvlParamsI_params_tr

/--
info: 'InLeanProof.instPisWithI_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.instPisWithI_map

/-- info: 'InLeanProof.mapM_mkFVarM_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.mapM_mkFVarM_run

/-- info: 'InLeanProof.map_trL_beq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.map_trL_beq

/-- info: 'InLeanProof.nestCanonSub_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.nestCanonSub_rel

/--
info: 'InLeanProof.nestCanonCrestI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestCanonCrestI_run

/-- info: 'InLeanProof.hiAt_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.hiAt_rel

/--
info: 'InLeanProof.nestRootCanonI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestRootCanonI_run

/--
info: 'InLeanProof.nestUniformOkI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestUniformOkI_run

/-- info: 'InLeanProof.forIn_unit_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.forIn_unit_run

/--
info: 'InLeanProof.nestUniformI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestUniformI_run

/-- info: 'InLeanProof.CVRel.eq_trCV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.CVRel.eq_trCV

/-- info: 'InLeanProof.indView_trCV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.indView_trCV

/-- info: 'InLeanProof.indView_none_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.indView_none_tr

/-- info: 'InLeanProof.familyTelescopeI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.familyTelescopeI_run

/--
info: 'InLeanProof.checkSpineAtI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkSpineAtI_run

/--
info: 'InLeanProof.familyKeyCheckI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.familyKeyCheckI_run

/-- info: 'InLeanProof.piBinders_TrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.piBinders_TrS

/-- info: 'InLeanProof.sortOf_TrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.sortOf_TrS

/-- info: 'InLeanProof.runs4_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.runs4_bind

/--
info: 'InLeanProof.nestInstTypeI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestInstTypeI_run

/-! ## Lane O7-classes (`PassClasses.lean`, `PassTail.lean`) -/

/-- info: 'InLeanProof.OkSlot.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.OkSlot.mono

/-- info: 'InLeanProof.trSlot_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.trSlot_mono

/-- info: 'InLeanProof.classOfMotiveVar_tr' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.classOfMotiveVar_tr

/-- info: 'InLeanProof.OkS_piResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.OkS_piResult

/-- info: 'InLeanProof.headDepth_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.headDepth_tr

/-- info: 'InLeanProof.constHead_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.constHead_tr

/-- info: 'InLeanProof.getLast?_TrSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.getLast?_TrSL

/-- info: 'InLeanProof.okS_getLast?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.okS_getLast?

/-- info: 'InLeanProof.forIn_acc_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.forIn_acc_run

/-- info: 'InLeanProof.foldl_filterMap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.foldl_filterMap

/-- info: 'InLeanProof.forIn_early_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.forIn_early_run

/--
info: 'InLeanProof.forIn_filterMap_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.forIn_filterMap_run

/--
info: 'InLeanProof.classReadMinorI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classReadMinorI_run

/--
info: 'InLeanProof.classReadSlotsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classReadSlotsI_run

/-- info: 'InLeanProof.cMotPos_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.cMotPos_tr

/-- info: 'InLeanProof.mapM_map_option' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.mapM_map_option

/--
info: 'InLeanProof.classReadI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classReadI_run

/-- info: 'InLeanProof.cReplaceFVars_noFvar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.cReplaceFVars_noFvar

/-- info: 'InLeanProof.replaceFVars_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.replaceFVars_eq

/--
info: 'InLeanProof.rfF_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.rfF_tr

/-- info: 'InLeanProof.rfF_none_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.rfF_none_tr

/--
info: 'InLeanProof.mapSpec_rfF_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.mapSpec_rfF_tr

/--
info: 'InLeanProof.replaceFVarsI_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.replaceFVarsI_tr

/-- info: 'InLeanProof.fvSubRel_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.fvSubRel_getElem?

/--
info: 'InLeanProof.targetCanonParamsI_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetCanonParamsI_tr

/-- info: 'InLeanProof.bvarBound_TrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.bvarBound_TrS

/--
info: 'InLeanProof.hasLooseBVars_TrS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.hasLooseBVars_TrS

/-- info: 'InLeanProof.fvbFold_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.fvbFold_le

/-- info: 'InLeanProof.fvbFold_ge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.fvbFold_ge

/-- info: 'InLeanProof.fvarRange_TrS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.fvarRange_TrS_le

/--
info: 'InLeanProof.fvarB_le_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.fvarB_le_tr

/--
info: 'InLeanProof.rangeGuard_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.rangeGuard_tr

/-- info: 'InLeanProof.runs_mapM_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.runs_mapM_loop

/-- info: 'InLeanProof.runs_mapM' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.runs_mapM

/-- info: 'InLeanProof.classes_trCR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.classes_trCR

/-- info: 'InLeanProof.okSlot_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.okSlot_classes

/-- info: 'InLeanProof.classNPcOf_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.classNPcOf_tr

/--
info: 'InLeanProof.classKeyOfI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classKeyOfI_run

/--
info: 'InLeanProof.mapM_classKeyOfI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.mapM_classKeyOfI_run

/-- info: 'InLeanProof.nestCtorEntry_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.nestCtorEntry_tr

/-- info: 'InLeanProof.ctorEntry_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ctorEntry_tr

/-- info: 'InLeanProof.targetCtorsOf_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetCtorsOf_tr

/-- info: 'InLeanProof.runs3_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.runs3_bind

/--
info: 'InLeanProof.targetOutsideInstI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetOutsideInstI_run

/-- info: 'InLeanProof.OkTM.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.OkTM.mono

/-- info: 'InLeanProof.toName_quotName' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.toName_quotName

/-- info: 'InLeanProof.trShape_members' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.trShape_members

/-- info: 'InLeanProof.runs5_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.runs5_bind

/-- info: 'InLeanProof.any_nestOcc_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.any_nestOcc_tr

/--
info: 'InLeanProof.targetMajorOfI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetMajorOfI_run

/-- info: 'InLeanProof.targetPinTysI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetPinTysI_run

/-- info: 'InLeanProof.mkFEnv_find?_fun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.mkFEnv_find?_fun

/-- info: 'InLeanProof.lbb_of_bvarB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.lbb_of_bvarB

/--
info: 'InLeanProof.targetMajorPinsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetMajorPinsI_run

/-- info: 'InLeanProof.TrS_mkAppL_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.TrS_mkAppL_const

/-- info: 'InLeanProof.getAppArgs_mkAppN'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.getAppArgs_mkAppN'

/-- info: 'InLeanProof.getAppArgs_mkAppN_const' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.getAppArgs_mkAppN_const

/--
info: 'InLeanProof.classMajorsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classMajorsI_run

/-- info: 'InLeanProof.canon_wscoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.canon_wscoped

/-- info: 'InLeanProof.trShape_k' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.trShape_k

/--
info: 'InLeanProof.filter_member_trTM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.filter_member_trTM

/--
info: 'InLeanProof.checkBlockClassesI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkBlockClassesI_run

/--
info: 'InLeanProof.fvSubRel_nestKeyMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.fvSubRel_nestKeyMap

/--
info: 'InLeanProof.nestSeedOfI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.nestSeedOfI_run

/--
info: 'InLeanProof.classSeedsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classSeedsI_run

/--
info: 'InLeanProof.checkBlockIdxSortsFI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.checkBlockIdxSortsFI_run

/-- info: 'InLeanProof.recKExpected_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.recKExpected_tr

/-- info: 'InLeanProof.streamKCheckI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.streamKCheckI_run

/-! ## Lane O7-classes, continued (`PassRecs.lean`) -/

/-- info: 'InLeanProof.occF_le_fvarRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.occF_le_fvarRange

/--
info: 'InLeanProof.fvarB_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.fvarB_tr

/-- info: 'InLeanProof.targetAbs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetAbs_eq

/-- info: 'InLeanProof.targetAbsI_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetAbsI_tr

/-- info: 'InLeanProof.isEquivList_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.isEquivList_tr

/-! ## Lane O7-recursors (`PassRecs2.lean`) -/

/-- info: 'InLeanProof.isDefEq_self_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.isDefEq_self_runs

/--
info: 'InLeanProof.tpdGuard_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.tpdGuard_tr

/--
info: 'InLeanProof.targetParamsDefEqI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetParamsDefEqI_run

/-- info: 'InLeanProof.getD_TrSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.getD_TrSL

/-- info: 'InLeanProof.targetHolesI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetHolesI_run

/-- info: 'InLeanProof.targetAbs_lbb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetAbs_lbb

/-- info: 'InLeanProof.map_param_trL' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.map_param_trL

/--
info: 'InLeanProof.targetClassMatchI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetClassMatchI_run

/-- info: 'InLeanProof.OkNf.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.OkNf.mono

/-- info: 'InLeanProof.map_trNf_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.map_trNf_mono

/-- info: 'InLeanProof.ctorsAny_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.ctorsAny_tr

/--
info: 'InLeanProof.targetMajorNfsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetMajorNfsI_run

/-- info: 'InLeanProof.OkTMN.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.OkTMN.mono

/-- info: 'InLeanProof.map_trTM_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.map_trTM_mono

/--
info: 'InLeanProof.classesNfsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classesNfsI_run

/-- info: 'InLeanProof.blockRecLpsOk_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockRecLpsOk_tr

/-- info: 'InLeanProof.reservedRecName_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.reservedRecName_tr

/-- info: 'InLeanProof.blockRecNamesUnreserved_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockRecNamesUnreserved_tr

/-- info: 'InLeanProof.nameSet_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.nameSet_tr

/-- info: 'InLeanProof.blockRecNameSetOk_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.blockRecNameSetOk_tr

/-- info: 'InLeanProof.filter_own_tr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.filter_own_tr

/-- info: 'InLeanProof.filter_aux_tr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.filter_aux_tr

/-- info: 'InLeanProof.trShape_recs' does not depend on any axioms -/
#guard_msgs in
#print axioms InLeanProof.trShape_recs

/-- info: 'InLeanProof.names_trRec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.names_trRec

/-- info: 'InLeanProof.names_trCtorParts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.names_trCtorParts

/-- info: 'InLeanProof.wantAux_tr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InLeanProof.wantAux_tr

/-- info: 'InLeanProof.trShape_n0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.trShape_n0

/-- info: 'InLeanProof.targetRecPinsI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.targetRecPinsI_run

/-- info: 'InLeanProof.classStreamRecsI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.classStreamRecsI_run

/-- info: 'InLeanProof.hits_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.hits_tr

/-- info: 'InLeanProof.classMinorSlotI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.classMinorSlotI_run

/-- info: 'InLeanProof.classFieldsOfI_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InLeanProof.classFieldsOfI_run

/--
info: 'InLeanProof.classFormerTyI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classFormerTyI_run

/--
info: 'InLeanProof.targetPiDomsWith_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetPiDomsWith_tr

/-! ## Lane O7-recursors, round 2 (`PassRecs3.lean`) -/

/--
info: 'InLeanProof.EraseMapOk.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.EraseMapOk.mono

/--
info: 'InLeanProof.efF_nonfvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.efF_nonfvar

/--
info: 'InLeanProof.mapSpec_efF_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mapSpec_efF_tr

/--
info: 'InLeanProof.eraseFVarTys_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.eraseFVarTys_eq

/--
info: 'InLeanProof.efLoop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.efLoop_run

/--
info: 'InLeanProof.eraseFVarTysI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.eraseFVarTysI_run

/--
info: 'InLeanProof.mapM_eraseFVarTysI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.mapM_eraseFVarTysI_run

/--
info: 'InLeanProof.stripPis_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.stripPis_TrS

/--
info: 'InLeanProof.getAppNumArgsT_TrS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.getAppNumArgsT_TrS

/--
info: 'InLeanProof.targetK53I_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetK53I_run

/--
info: 'InLeanProof.piDomAt_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.piDomAt_tr

/--
info: 'InLeanProof.classNodesAgreeI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classNodesAgreeI_run

/--
info: 'InLeanProof.unwrapOr_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.unwrapOr_run

/--
info: 'InLeanProof.trTM_default' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.trTM_default

/--
info: 'InLeanProof.getD_map_trTM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.getD_map_trTM

/--
info: 'InLeanProof.getD_of_all' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.getD_of_all

/--
info: 'InLeanProof.okTMN_default' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.okTMN_default

/--
info: 'InLeanProof.classLeafAt_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classLeafAt_tr

/--
info: 'InLeanProof.FvsOk.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.FvsOk.mono

/--
info: 'InLeanProof.FvsOk.okSL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.FvsOk.okSL

/--
info: 'InLeanProof.FvsOk.lbb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.FvsOk.lbb

/--
info: 'InLeanProof.classFieldsAgreeI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classFieldsAgreeI_run

/--
info: 'InLeanProof.targetCtorAtI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.targetCtorAtI_run

/--
info: 'InLeanProof.classFieldsOf_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classFieldsOf_length

/--
info: 'InLeanProof.OkCC.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.OkCC.mono

/--
info: 'InLeanProof.ClassOk.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ClassOk.mono

/--
info: 'InLeanProof.classOk_default' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classOk_default

/--
info: 'InLeanProof.filter_ctor_trNf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.filter_ctor_trNf

/--
info: 'InLeanProof.classCtorOfI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classCtorOfI_run

/--
info: 'InLeanProof.map_trCC_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.map_trCC_mono

/--
info: 'InLeanProof.okTMN_all_of_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.okTMN_all_of_getD

/--
info: 'InLeanProof.classCtorsOfI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classCtorsOfI_run

/--
info: 'InLeanProof.classesCtorsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classesCtorsI_run

/--
info: 'InLeanProof.optT_bind_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.optT_bind_run

/--
info: 'InLeanProof.optT_pure_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.optT_pure_run

/--
info: 'InLeanProof.liftOpt_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.liftOpt_run

/--
info: 'InLeanProof.liftM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.liftM_run

/--
info: 'InLeanProof.lbb_instPisWith' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.lbb_instPisWith

/--
info: 'InLeanProof.fvsOk_of_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.fvsOk_of_open

/--
info: 'InLeanProof.majorI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.majorI_run

/--
info: 'InLeanProof.ihPartsI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ihPartsI_run

/--
info: 'InLeanProof.mapM_binder_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mapM_binder_run

/--
info: 'InLeanProof.motiveTyI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.motiveTyI_run

/-! ## Lane O7-recursors, round 3 (`PassRecs4.lean`) -/

/--
info: 'InLeanProof.emvarS_closeTelescope' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.emvarS_closeTelescope

/--
info: 'InLeanProof.emvarS_closeLams' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.emvarS_closeLams

/--
info: 'InLeanProof.closeLams_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.closeLams_tr

/--
info: 'InLeanProof.TrSL_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.TrSL_getD

/--
info: 'InLeanProof.okS_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.okS_getD

/--
info: 'InLeanProof.lbb_targetPiDomsWith' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.lbb_targetPiDomsWith

/--
info: 'InLeanProof.motiveSlot_trSlot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.motiveSlot_trSlot

/--
info: 'InLeanProof.slotVarI_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.slotVarI_run

/--
info: 'InLeanProof.motVarI_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.motVarI_run

/--
info: 'InLeanProof.mapM_optT_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mapM_optT_run

/--
info: 'InLeanProof.getD_map_trCF' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.getD_map_trCF

/--
info: 'InLeanProof.getD_filterMap_range_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.getD_filterMap_range_lt

/--
info: 'InLeanProof.minorIhStepOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.minorIhStepOk

/--
info: 'InLeanProof.minorTyI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.minorTyI_run

/--
info: 'InLeanProof.CGOk.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.CGOk.mono

/--
info: 'InLeanProof.getD_map_trSlot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.getD_map_trSlot

/--
info: 'InLeanProof.getD_map_trCCs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.getD_map_trCCs

/--
info: 'InLeanProof.find?_trCC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.find?_trCC

/--
info: 'InLeanProof.closed_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.closed_getD

/--
info: 'InLeanProof.prefixSlotStepOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.prefixSlotStepOk

/--
info: 'InLeanProof.prefixBindersI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.prefixBindersI_run

/--
info: 'InLeanProof.major_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.major_closed

/--
info: 'InLeanProof.classGenRecTyI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classGenRecTyI_run

/--
info: 'InLeanProof.filterMapM_optT_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.filterMapM_optT_run

/--
info: 'InLeanProof.pvarsI_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.pvarsI_run

/--
info: 'InLeanProof.find?_slot_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.find?_slot_tr

/--
info: 'InLeanProof.ruleIhStepOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.ruleIhStepOk

/--
info: 'InLeanProof.emvarS_mkAppN_args' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.emvarS_mkAppN_args

/--
info: 'InLeanProof.classGenRuleI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classGenRuleI_run

/--
info: 'InLeanProof.withAnnotations_noFVar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.withAnnotations_noFVar

/--
info: 'InLeanProof.allLevelParamsDefined_noFVar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.allLevelParamsDefined_noFVar

/--
info: 'InLeanProof.constsResolveF_state' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.constsResolveF_state

/--
info: 'InLeanProof.classConstOk_emvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classConstOk_emvar

/--
info: 'InLeanProof.classConstOkI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classConstOkI_run

/--
info: 'InLeanProof.classRecTyCheckI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTyCheckI_run

/--
info: 'InLeanProof.classRecTyCheck_emvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTyCheck_emvar

/--
info: 'InLeanProof.classRecTyOkI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTyOkI_run

/--
info: 'InLeanProof.GenCls.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.GenCls.mono

/--
info: 'InLeanProof.classRecTysOkI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTysOkI_run

/--
info: 'InLeanProof.ucPick_compound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.ucPick_compound

/--
info: 'InLeanProof.ucDedup_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ucDedup_spec

/--
info: 'InLeanProof.usedConstants_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.usedConstants_complete

/--
info: 'InLeanProof.find_isSome_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.find_isSome_tr

/--
info: 'InLeanProof.constsResolve_of_test' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.constsResolve_of_test

/--
info: 'InLeanProof.constsResolveF_tr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.constsResolveF_tr

/--
info: 'InLeanProof.stripLams_tr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.stripLams_tr

/--
info: 'InLeanProof.allM_true' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.allM_true

/--
info: 'InLeanProof.classRuleCheck_emvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRuleCheck_emvar

/--
info: 'InLeanProof.classRuleCheckI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classRuleCheckI_run

/--
info: 'InLeanProof.RuleCtorOk.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.RuleCtorOk.mono

/--
info: 'InLeanProof.all_okLv_param' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.all_okLv_param

/--
info: 'InLeanProof.classRulesOkI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classRulesOkI_run

/--
info: 'InLeanProof.TrSL_of_okC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.TrSL_of_okC

/--
info: 'InLeanProof.getD_ctors_mem' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.getD_ctors_mem

/--
info: 'InLeanProof.classRecsRulesOkI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classRecsRulesOkI_run

/--
info: 'InLeanProof.classGenRecTy_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classGenRecTy_shape

/--
info: 'InLeanProof.classRecTyOk_pre_emvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTyOk_pre_emvar

/--
info: 'InLeanProof.classRecTysOk_pre_emvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTysOk_pre_emvar

/--
info: 'InLeanProof.recs_ne_nil_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.recs_ne_nil_of_pins

/--
info: 'InLeanProof.presI_push_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_push_plain

/--
info: 'InLeanProof.tableFields_notInd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.tableFields_notInd

/--
info: 'InLeanProof.find_push_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.find_push_self

/--
info: 'InLeanProof.push_env_find' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.push_env_find

/--
info: 'InLeanProof.jobEnvI_push_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.jobEnvI_push_plain

/--
info: 'InLeanProof.pushDelta_one' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.pushDelta_one

/--
info: 'InLeanProof.presI_consSumCtorsF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_consSumCtorsF

/--
info: 'InLeanProof.presI_consBlockCtorsF_go' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_consBlockCtorsF_go

/--
info: 'InLeanProof.trShape_memberCtors' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.trShape_memberCtors

/--
info: 'InLeanProof.jobEnvI_ctors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.jobEnvI_ctors

/--
info: 'InLeanProof.trShape_majorIdxAt' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.trShape_majorIdxAt

/--
info: 'InLeanProof.trShape_rulePrefixAt' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.trShape_rulePrefixAt

/--
info: 'InLeanProof.entryRelI_recEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.entryRelI_recEntry

/--
info: 'InLeanProof.presI_consBlockRecsBareF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.presI_consBlockRecsBareF

/--
info: 'InLeanProof.zip_fst_sublist' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.zip_fst_sublist

/--
info: 'InLeanProof.jobEnvI_ruleEnv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.jobEnvI_ruleEnv

/--
info: 'InLeanProof.isNeverZero_tr' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.isNeverZero_tr

/--
info: 'InLeanProof.numCtorsOf_tr' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.numCtorsOf_tr

/--
info: 'InLeanProof.blockLargeElimAllowed_tr' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.blockLargeElimAllowed_tr

/--
info: 'InLeanProof.structElimLevel_tr' does not depend on any axioms
-/
#guard_msgs in
#print axioms InLeanProof.structElimLevel_tr

/--
info: 'InLeanProof.any_member_trTM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.any_member_trTM

/--
info: 'InLeanProof.minors_trCR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.minors_trCR

/--
info: 'InLeanProof.ctorsSum_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.ctorsSum_tr

/--
info: 'InLeanProof.classRecOf_tr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRecOf_tr

/--
info: 'InLeanProof.classFormerTy_lbb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classFormerTy_lbb

/--
info: 'InLeanProof.classFormerTysI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.classFormerTysI_run

/--
info: 'InLeanProof.targetMajorNfs_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.targetMajorNfs_sub

/--
info: 'InLeanProof.classesNfs_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classesNfs_sub

/--
info: 'InLeanProof.classConstOk_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classConstOk_fresh

/--
info: 'InLeanProof.classRecTyOk_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTyOk_facts

/--
info: 'InLeanProof.classRecTysOk_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.classRecTysOk_facts

/--
info: 'InLeanProof.targetRecPins_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.targetRecPins_nodup

/--
info: 'InLeanProof.CtorLbb.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.CtorLbb.mono

/--
info: 'InLeanProof.str_rec_ne_sorryAx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.str_rec_ne_sorryAx

/--
info: 'InLeanProof.str_recI_ne_sorryAx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.str_recI_ne_sorryAx

/--
info: 'InLeanProof.targetRecPins_not_sorryAx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.targetRecPins_not_sorryAx

/--
info: 'InLeanProof.genCVs_okC' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms InLeanProof.genCVs_okC

/--
info: 'InLeanProof.mem_nfs_nil' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.mem_nfs_nil

/--
info: 'InLeanProof.okSL_of_okC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.okSL_of_okC

/--
info: 'InLeanProof.genRecCheckI_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 InLeanProof.Expr.mkAppData_fields,
 InLeanProof.Expr.mkData_eq,
 InLeanProof.Level.mkData_eq]
-/
#guard_msgs in
#print axioms InLeanProof.genRecCheckI_run
