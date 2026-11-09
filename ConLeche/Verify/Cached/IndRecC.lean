module

public import ConLeche.Cached.CheckerC
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# The cached recursor stage is the specification's (task #498)

The parts of `genRecCheckC` (`ConLeche/Cached/IndRec.lean`) mirror
those of `genRecCheck` (`ConLeche/Kernel/Inductives/GenRec.lean`) at the
cached driver's shared operations: the same steps, each cached walk
equal to the plain one it replaces (`IndWalksC.lean`, `OpsC.lean`,
`GuardsC.lean`, `openPisAtFvarsC_eq`), each core call the shared
operation it unfolds to.  So each relation is an equation, proved twin
by twin bottom up; the stage itself (which flushes and runs the rules at
an overlay) is simulated by a triple that enters through them
(`genRecCheckS_spec`, `GenRecC.lean`).
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The generator -/

theorem targetCtorAtC_eq (M : TargetMajor) (c : ConstantVal) :
    targetCtorAtC M c = targetCtorAt M c := by
  unfold targetCtorAtC targetCtorAt
  cases M.member <;> simp only [Expr.instLevelParams_spec]

theorem ClassGen.majorC_eq (g : ClassGen) (c d : Nat) : g.majorC c d = g.major c d := by
  simp only [ClassGen.majorC, ClassGen.major, Expr.instPisWithC_eq, openPisAtFvarsC_eq]

theorem ClassGen.motiveTyC_eq (g : ClassGen) (c d : Nat) : g.motiveTyC c d = g.motiveTy c d := by
  simp only [ClassGen.motiveTyC, ClassGen.motiveTy, ClassGen.majorC_eq, Expr.closeTelescopeC_eq]

theorem ClassGen.ihPartsC_eq (g : ClassGen) (t tele : Nat) (w : Expr) (d : Nat) :
    g.ihPartsC t tele w d = g.ihParts t tele w d := by
  simp only [ClassGen.ihPartsC, ClassGen.ihParts, openPisAtFvarsC_eq, Expr.getAppArgsC_spec]

theorem ClassGen.minorTyC_eq (g : ClassGen) (c : Nat) (x : ClassCtor) (d : Nat) :
    g.minorTyC c x d = g.minorTy c x d := by
  simp only [ClassGen.minorTyC, ClassGen.minorTy, openPisAtFvarsC_eq, Expr.targetPiDomsWithC_eq,
    ClassGen.ihPartsC_eq, Expr.closeTelescopeC_eq, Expr.getAppArgsC_spec]
  rfl

theorem ClassGen.prefixBindersC_eq (g : ClassGen) : g.prefixBindersC = g.prefixBinders := by
  simp only [ClassGen.prefixBindersC, ClassGen.prefixBinders, ClassGen.motiveTyC_eq,
    ClassGen.minorTyC_eq]
  rfl

theorem classGenRecTyC_eq (g : ClassGen) (c : Nat) : classGenRecTyC g c = classGenRecTy g c := by
  simp only [classGenRecTyC, classGenRecTy, ClassGen.majorC_eq, Expr.closeTelescopeC_eq]

theorem classGenRuleC_eq (g : ClassGen) (recOf : Nat → Option Name) (rlvls : List Level)
    (c : Nat) (x : ClassCtor) : classGenRuleC g recOf rlvls c x = classGenRule g recOf rlvls c x := by
  simp only [classGenRuleC, classGenRule, openPisAtFvarsC_eq, Expr.targetPiDomsWithC_eq,
    ClassGen.ihPartsC_eq, Expr.closeLamsC_eq]
  rfl

/-! ## The class match -/

theorem targetCanonParamsC_eq (pfvs : List Expr) (e : Expr) :
    targetCanonParamsC pfvs e = targetCanonParams pfvs e := by
  simp only [targetCanonParamsC, targetCanonParams, Expr.replaceFVarsC_spec]

theorem eraseFVarTysC_eq : eraseFVarTysC = Expr.eraseFVarTys := by
  funext e
  simp only [eraseFVarTysC, Expr.eraseFVarTys, Expr.replaceFVarsC_spec]

theorem targetParamsDefEqC_eq (mode : CheckMode) (fe : FEnv) (d : Nat) (names : List Name)
    (lvls : List Level) (holes : List Expr) (pfvs : List Expr) :
    ∀ as bs : List Expr, targetParamsDefEqC mode fe d names lvls holes pfvs as bs
      = targetParamsDefEq (sharedOpsC mode fe) fe.env d (targetAbs names lvls holes) pfvs as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp only [targetParamsDefEqC, targetParamsDefEq, Expr.targetAbsC_spec,
      targetCanonParamsC_eq, targetParamsDefEqC_eq mode fe d names lvls holes pfvs as bs]
    rfl

theorem targetClassMatchC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape)
    (formerTys pfvs : List Expr) (us : List Level) (ds : List Expr) (lvls : List Level)
    (eds : List Expr) :
    targetClassMatchC mode fe p formerTys pfvs us ds lvls eds
      = targetClassMatch (sharedOpsC mode fe) fe.env p formerTys pfvs us ds lvls eds := by
  simp only [targetClassMatchC, targetClassMatch, targetParamsDefEqC_eq]

theorem targetMajorNfsC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape)
    (formerTys pfvs : List Expr) (us : List Level) (ds : List Expr)
    (ctors : List (ConstantVal × Nat)) :
    ∀ tbl : List NestCtorNf, targetMajorNfsC mode fe p formerTys pfvs us ds ctors tbl
      = targetMajorNfs (sharedOpsC mode fe) fe.env p formerTys pfvs us ds ctors tbl
  | [] => rfl
  | e :: es => by
    simp only [targetMajorNfsC, targetMajorNfs, targetClassMatchC_eq,
      targetMajorNfsC_eq mode fe p formerTys pfvs us ds ctors es]

theorem targetK53C_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (majDom f : Expr) :
    targetK53C mode fe p formerTys Mc tele majDom f
      = targetK53 (sharedOpsC mode fe) fe.env p formerTys Mc tele majDom f := by
  simp only [targetK53C, targetK53, eraseFVarTysC_eq, Expr.getAppArgsC_spec, Expr.nestOccC_spec,
    targetClassMatchC_eq]
  rfl

/-! ## The classes' constructors -/

theorem classFieldsOfC_eq (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) :
    ∀ (i : Nat) (fs : List Expr), classFieldsOfC p ctor ihs i fs = classFieldsOf p ctor ihs i fs
  | _, [] => rfl
  | i, f :: fs => by
    simp only [classFieldsOfC, classFieldsOf, Expr.nestOccC_spec, classFieldsOfC_eq p ctor ihs]
    rfl

theorem classNodesAgreeC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape)
    (formerTys : List Expr) (Mc : TargetMajor) (tele : List Expr) (leaf : Expr)
    (fvs : List Expr) (i : Nat) (ctor : Name) :
    ∀ E : List NestCtorNf, classNodesAgreeC mode fe p formerTys Mc tele leaf fvs i ctor E
      = classNodesAgree (sharedOpsC mode fe) fe.env p formerTys Mc tele leaf fvs i ctor E
  | [] => rfl
  | e :: es => by
    simp only [classNodesAgreeC, classNodesAgree, Expr.targetPiDomsWithC_eq, targetK53C_eq,
      classNodesAgreeC_eq mode fe p formerTys Mc tele leaf fvs i ctor es]
    rfl

theorem classFieldsAgreeC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape)
    (formerTys : List Expr) (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name)
    (E : List NestCtorNf) :
    ∀ (i : Nat) (ks : List ClassField), classFieldsAgreeC mode fe p formerTys Ms fvs ctor E i ks
      = classFieldsAgree (sharedOpsC mode fe) fe.env p formerTys Ms fvs ctor E i ks
  | _, [] => rfl
  | i, .ordinary :: ks => by
    simp only [classFieldsAgreeC, classFieldsAgree,
      classFieldsAgreeC_eq mode fe p formerTys Ms fvs ctor E (i + 1) ks]
  | i, .recursive t tele :: ks => by
    simp only [classFieldsAgreeC, classFieldsAgree, classNodesAgreeC_eq,
      classFieldsAgreeC_eq mode fe p formerTys Ms fvs ctor E (i + 1) ks]

theorem classCtorOfC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (ctor : ConstantVal × Nat) :
    classCtorOfC mode fe p formerTys rd Ms c ctor
      = classCtorOf (sharedOpsC mode fe) fe.env p formerTys rd Ms c ctor := by
  simp only [classCtorOfC, classCtorOf, openPisAtFvarsC_eq, classFieldsOfC_eq,
    classFieldsAgreeC_eq, targetCtorAtC_eq, Expr.instPisWithC_eq]

theorem classCtorsOfC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) :
    ∀ cs : List (ConstantVal × Nat), classCtorsOfC mode fe p formerTys rd Ms c cs
      = classCtorsOf (sharedOpsC mode fe) fe.env p formerTys rd Ms c cs
  | [] => rfl
  | ctor :: cs => by
    simp only [classCtorsOfC, classCtorsOf, classCtorOfC_eq,
      classCtorsOfC_eq mode fe p formerTys rd Ms c cs]

theorem classesCtorsC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) :
    ∀ (c : Nat) (rest : List TargetMajor), classesCtorsC mode fe p formerTys rd Ms c rest
      = classesCtors (sharedOpsC mode fe) fe.env p formerTys rd Ms c rest
  | _, [] => rfl
  | c, M :: rest => by
    simp only [classesCtorsC, classesCtors, classCtorsOfC_eq,
      classesCtorsC_eq mode fe p formerTys rd Ms (c + 1) rest]

theorem classesNfsC_eq (mode : CheckMode) (fe : FEnv) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) :
    ∀ Ms : List TargetMajor, classesNfsC mode fe p formerTys tbl Ms
      = classesNfs (sharedOpsC mode fe) fe.env p formerTys tbl Ms
  | [] => rfl
  | M :: Ms => by
    simp only [classesNfsC, classesNfs, targetMajorNfsC_eq, classesNfsC_eq mode fe p formerTys tbl Ms]

theorem classFormerTyC_eq (mode : CheckMode) (fe : FEnv) (formers : List ConstantVal) :
    classFormerTyC mode fe formers = classFormerTy (sharedOpsC mode fe) fe formers := by
  funext M
  simp only [classFormerTyC, classFormerTy, familyTelescopeC_eq, Expr.instLevelParams_spec]
  rfl

/-! ## The generated types and rules, checked -/

theorem unresolvedConstsErrorLC_true (where_ : String) (e : Expr) :
    unresolvedConstsErrorLC true where_ e = unresolvedConstsError where_ e := by
  simp only [unresolvedConstsErrorLC, unresolvedConstsError, Expr.mentionsAnyConstC_spec,
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]

theorem classConstOkC_eq (mode : CheckMode) (fe : FEnv) (cv : ConstantVal) :
    classConstOkC mode fe cv = classConstOk (sharedOpsC mode fe) fe cv := by
  simp only [classConstOkC, classConstOk, Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec,
    unresolvedConstsErrorLC_true]
  rfl

theorem classRecTyCheckC_eq (mode : CheckMode) (fe : FEnv) (cvRi cvG : ConstantVal) :
    classRecTyCheckC mode fe cvRi cvG = classRecTyCheck (sharedOpsC mode fe) fe cvRi cvG := by
  simp only [classRecTyCheckC, classRecTyCheck, classConstOkC_eq]
  rfl

theorem classRecTyOkC_eq (mode : CheckMode) (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) :
    classRecTyOkC mode fe g k rc cvRi c = classRecTyOk (sharedOpsC mode fe) fe g k rc cvRi c := by
  simp only [classRecTyOkC, classRecTyOk, classGenRecTyC_eq, classRecTyCheckC_eq]

theorem classRecTysOkC_eq (mode : CheckMode) (fe : FEnv) (g : ClassGen) (k : Nat) :
    ∀ (rcs : List RecShape) (cvs : List ConstantVal) (cs : List Nat),
      classRecTysOkC mode fe g k rcs cvs cs = classRecTysOk (sharedOpsC mode fe) fe g k rcs cvs cs
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    simp only [classRecTysOkC, classRecTysOk, classRecTyOkC_eq, classRecTysOkC_eq mode fe g k rcs]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl

theorem classRuleCheckC_eq (mode : CheckMode) (feT feR : FEnv) (cvR : ConstantVal) (n : Nat)
    (gen : Expr) :
    classRuleCheckC mode feT feR cvR n gen
      = classRuleCheck (sharedOpsRuleR mode feR) feT feR cvR n gen := by
  simp only [classRuleCheckC, classRuleCheck, Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec,
    unresolvedConstsErrorLC_true, sharedOpsRuleR, sharedOpsC, opE, bind_assoc, pure_bind]

theorem classRulesOkC_eq (mode : CheckMode) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (cvR : ConstantVal) (c : Nat) :
    ∀ xs : List ClassCtor, classRulesOkC mode feT feR g recOf cvR c xs
      = classRulesOk (sharedOpsRuleR mode feR) feT feR g recOf cvR c xs
  | [] => rfl
  | x :: xs => by
    simp only [classRulesOkC, classRulesOk, classRuleOk, classGenRuleC_eq, classRuleCheckC_eq,
      classRulesOkC_eq mode feT feR g recOf cvR c xs, bind_assoc, pure_bind]

theorem classRecsRulesOkC_eq (mode : CheckMode) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) :
    ∀ (cvs : List ConstantVal) (cs : List Nat), classRecsRulesOkC mode feT feR g recOf cvs cs
      = classRecsRulesOk (sharedOpsRuleR mode feR) feT feR g recOf cvs cs
  | cvG :: cvs, c :: cs => by
    simp only [classRecsRulesOkC, classRecsRulesOk, classRulesOkC_eq,
      classRecsRulesOkC_eq mode feT feR g recOf cvs cs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem classStreamRecsC_eq (mode : CheckMode) (fe : FEnv) :
    ∀ rcs : List RecShape, classStreamRecsC mode fe rcs = classStreamRecs (sharedOpsC mode fe) fe rcs
  | [] => rfl
  | rc :: rcs => by
    simp only [classStreamRecsC, classStreamRecs, checkConstantValC_eq,
      classStreamRecsC_eq mode fe rcs]

end ConLeche.Cached
