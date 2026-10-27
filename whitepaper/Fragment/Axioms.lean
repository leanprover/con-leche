module

public import Fragment.Consistency
public import Fragment.Modular
public import Fragment.Install
public import Fragment.Access
public import Fragment.UniformBeta
public import Fragment.ValueReading
public import Fragment.Probe
public import Fragment.EtaIota
public import Fragment.IOWitness

public section

/-!
# The axiom pin

The fragment's theorems use exactly Lean's three standard axioms and
nothing else — in particular no `sorryAx` and no axiom of the
fragment's own: the library `SetLib` and the level oracle
`LevelOracle` are *class parameters* of every theorem, not axioms.
`whitepaper/fragment-gate.sh` builds this file; a change in the list
is a build error here.
-/

/--
info: 'Fragment.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.soundness

/--
info: 'Fragment.closed_infer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.closed_infer

/--
info: 'Fragment.install_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_def

/--
info: 'Fragment.install_ind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_ind

/--
info: 'Fragment.accepted_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.accepted_model

/--
info: 'Fragment.no_empty_inductive_inhabitant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.no_empty_inductive_inhabitant

/--
info: 'Fragment.no_empty_prop_inhabitant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.no_empty_prop_inhabitant

/--
info: 'Fragment.Red.iotaNested_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaNested_sound

/--
info: 'Fragment.IndSpec.famOp_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.famOp_mono

/--
info: 'Fragment.IndSpec.famOp_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.famOp_acc

/--
info: 'Fragment.IndSpec.Fam_psK_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.Fam_psK_mono

/--
info: 'Fragment.IndSpec.Fam_psK_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.Fam_psK_acc

/--
info: 'Fragment.IndSpec.contClause_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.contClause_of

/--
info: 'Fragment.lfpP_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lfpP_acc

/--
info: 'Fragment.IndSpec.classLaws_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.classLaws_of

/--
info: 'Fragment.IndSpec.RecGraphN_fun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.RecGraphN_fun

/--
info: 'Fragment.IndSpec.RecGraphN_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.RecGraphN_total

/--
info: 'Fragment.IndSpec.recSemN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.recSemN_eq

/--
info: 'Fragment.IndSpec.rec1Sem_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec1Sem_eq

/--
info: 'Fragment.IndSpec.rec_rule_lawN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_lawN

/--
info: 'Fragment.IndSpec.rec_rule_law1N' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_law1N

/--
info: 'Fragment.install_nest' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_nest

/--
info: 'Fragment.install_ind_any' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_ind_any

/--
info: 'Fragment.AccIter.closed_of_acc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.AccIter.closed_of_acc

/--
info: 'Fragment.lfpFamSet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lfpFamSet_eq

/--
info: 'Fragment.lfpFamSet_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lfpFamSet_induction

/--
info: 'Fragment.badEnv_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.badEnv_no_model

/--
info: 'Fragment.Red.beta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.beta_sound

/--
info: 'Fragment.major_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.major_eq

/--
info: 'Fragment.Red.iota_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iota_core

/--
info: 'Fragment.teleFit_of_ne_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.teleFit_of_ne_pt

/--
info: 'Fragment.Red.iota_core_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iota_core_sem

/--
info: 'Fragment.Red.iota_core_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iota_core_strict

/--
info: 'Fragment.Red.strict_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.strict_dom

/--
info: 'Fragment.Red.iotaStrict_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaStrict_sound

/--
info: 'Fragment.Red.iotaNestedStrict_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaNestedStrict_sound

/--
info: 'Fragment.IndSpec.indFib_of_readers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.indFib_of_readers

/--
info: 'Fragment.IndSpec.Reader.fib_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.Reader.fib_app

/--
info: 'Fragment.IndSpec.strict_adm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.strict_adm

/--
info: 'Fragment.Red.iota_core_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iota_core_slot

/--
info: 'Fragment.Red.slot_of_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.slot_of_law

/--
info: 'Fragment.Red.dom_fib' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.dom_fib

/--
info: 'Fragment.Red.app_fib' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.app_fib

/--
info: 'Fragment.Red.iotaSlot_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaSlot_sound

/--
info: 'Fragment.Red.iotaNestedSlot_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaNestedSlot_sound

/--
info: 'Fragment.IndSpec.Reader.app_famSetF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.Reader.app_famSetF

/--
info: 'Fragment.DefEq.lam_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.lam_sound

/--
info: 'Fragment.DefEq.eta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.eta_sound

/--
info: 'Fragment.DefEq.pi_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.pi_sound

/--
info: 'Fragment.lam_congr_untyped_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lam_congr_untyped_unsound

/--
info: 'Fragment.SetLib.lamV_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.SetLib.lamV_mem

/--
info: 'Fragment.SetLib.lamV_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.SetLib.lamV_eta

/--
info: 'Fragment.SetLib.piV_mem_typeU' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.SetLib.piV_mem_typeU

/--
info: 'Fragment.piV_empty_not_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.piV_empty_not_strict

/--
info: 'Fragment.IndSpec.adm_Fam_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.adm_Fam_of

/--
info: 'Fragment.IndSpec.class_reading' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.class_reading

/--
info: 'Fragment.DefEq.lamProp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.lamProp_sound

/--
info: 'Fragment.DefEq.lamConst_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.lamConst_sound

/--
info: 'Fragment.DefEq.appIn_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.appIn_sound

/--
info: 'Fragment.DefEqIn.lam_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEqIn.lam_sound

/--
info: 'Fragment.DefEqIn.eta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEqIn.eta_sound

/--
info: 'Fragment.lam_congr_sorts_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lam_congr_sorts_unsound

/--
info: 'Fragment.mixed_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.mixed_lam

/--
info: 'Fragment.piV_const_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.piV_const_one

/--
info: 'Fragment.DefEq.etaProp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.etaProp_sound

/--
info: 'Fragment.DefEqLams.inner_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEqLams.inner_sound

/--
info: 'Fragment.DefEqLams.outer_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEqLams.outer_sound

/--
info: 'Fragment.DefEq.lams_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.DefEq.lams_sound

/--
info: 'Fragment.defeqLams_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.defeqLams_sound

/--
info: 'Fragment.Red.iotaK_core_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaK_core_sem

/--
info: 'Fragment.Red.iotaEta_core_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaEta_core_sem

/--
info: 'Fragment.Red.iotaEta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaEta_sound

/--
info: 'Fragment.etaLaw_vals' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.etaLaw_vals

/--
info: 'Fragment.Red.projCtor_core_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.projCtor_core_sem

/--
info: 'Fragment.projPt_of_fieldSort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.projPt_of_fieldSort

/--
info: 'Fragment.recRuleLawK_of_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.recRuleLawK_of_eta

/--
info: 'Fragment.iotaEta_noFields' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Fragment.iotaEta_noFields

/--
info: 'Fragment.plainIota_literal_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.plainIota_literal_witness

/--
info: 'Fragment.etaIota_reduced_major_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.etaIota_reduced_major_witness

/--
info: 'Fragment.eq_pt_of_mem_sortZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.eq_pt_of_mem_sortZero

/--
info: 'Fragment.ctorApp_eq_pt_of_sortZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.ctorApp_eq_pt_of_sortZero

/--
info: 'Fragment.Red.iota_core_prop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iota_core_prop

/--
info: 'Fragment.Red.iotaProp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaProp_sound

/--
info: 'Fragment.inferIO_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.inferIO_sound

/--
info: 'Fragment.eq_pt_of_IORel_prop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.eq_pt_of_IORel_prop

/--
info: 'Fragment.proofIrrelIO_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.proofIrrelIO_sound

/--
info: 'Fragment.IORel_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IORel_neutral

/--
info: 'Fragment.etaIO_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.etaIO_sound

/--
info: 'Fragment.lam_congr_io_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.lam_congr_io_unsound

/--
info: 'Fragment.eta_body_io_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.eta_body_io_unsound

/--
info: 'Fragment.eta_lam_io_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.eta_lam_io_unsound

/--
info: 'Fragment.io_type_value_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.io_type_value_collision

/--
info: 'Fragment.interp_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.interp_zeta

/--
info: 'Fragment.Red.zeta_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.zeta_sound

/--
info: 'Fragment.Infer.letE_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Infer.letE_sound

/--
info: 'Fragment.Infer.letE_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Infer.letE_sat

/--
info: 'Fragment.InferIO.letE_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.InferIO.letE_sound

/--
info: 'Fragment.Red.iotaK_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Red.iotaK_sound

/--
info: 'Fragment.IndSpec.rec_rule_lawK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_lawK

/--
info: 'Fragment.IndSpec.rec_rule_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_slot

/--
info: 'Fragment.IndSpec.rec_rule_slotN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_slotN

/--
info: 'Fragment.IndSpec.rec_rule_slot1N' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.IndSpec.rec_rule_slot1N

/--
info: 'Fragment.Infer.mono' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Fragment.Infer.mono

/--
info: 'Fragment.Checks.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Checks.mono

/--
info: 'Fragment.install_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.install_thm

/--
info: 'Fragment.Checks.joined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Checks.joined

/--
info: 'Fragment.local_checks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.local_checks

/--
info: 'Fragment.local_accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.local_accepted

/--
info: 'Fragment.local_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.local_model

/--
info: 'Fragment.local_no_empty_prop_inhabitant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.local_no_empty_prop_inhabitant
