module

public import InLeanProof.Ops
public import InLeanProof.Statement
public import InLeanProof.Sim
public import InLeanProof.FVar
public import InLeanProof.Range
public import InLeanProof.KnotI
public import InLeanProof.StateOpsI
public import InLeanProof.WalksWhnf
public import InLeanProof.SquarePilot

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
