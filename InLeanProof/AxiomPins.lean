module

public import InLeanProof.Ops
public import InLeanProof.Statement

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
