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
info: 'InLeanProof.indGroupPresB_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms InLeanProof.indGroupPresB_of

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
