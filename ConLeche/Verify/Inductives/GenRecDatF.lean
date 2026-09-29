module

public import ConLeche.Verify.BridgeDecl
public import ConLeche.Kernel.Inductives.GenRec

public section

/-!
# The generated recursor stage at fuel `F`

`genRecCheck_datF`: the stage as the pure install runs it
(`ShadowOps.ofOps` at the fueled family `fueledOpsM`), read at fuel `F`,
IS the stage at the pure operations at fuel `F` (`ShadowOps.fueled`) —
the generated stage's twin of `targetRecCheck_datF` (`BridgeDecl.lean`),
one lemma per stage function of `Kernel/Inductives/GenRec.lean`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

theorem classMinorSlot_datF (rd : ClassRead) (c : Nat) (C : Name) (F : Nat) :
    (classMinorSlot (m := FueledM) rd c C).val F = classMinorSlot (m := CheckM) rd c C := by
  unfold classMinorSlot
  dsimp only
  split <;> rfl

theorem classFieldsOf_datF (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) (F : Nat) :
    ∀ (i : Nat) (fs : List Expr),
      (classFieldsOf (m := FueledM) p ctor ihs i fs).val F =
        classFieldsOf (m := CheckM) p ctor ihs i fs
  | _, [] => rfl
  | i, f :: fs => by
    unfold classFieldsOf
    dsimp only
    split <;>
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      classFieldsOf_datF p ctor ihs F (i + 1) fs] <;> rfl

theorem classNodesAgree_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List (Expr × BinderMeta)) (leaf : Expr) (fvs : List Expr)
    (i : Nat) (ctor : Name) (F : Nat) :
    ∀ (es : List NestCtorNf),
      (classNodesAgree (fueledOpsM mode) env p formerTys Mc tele leaf fvs i ctor es).val F =
        classNodesAgree (fueledOps mode F) env p formerTys Mc tele leaf fvs i ctor es
  | [] => rfl
  | e :: es => by
    unfold classNodesAgree
    split
    · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        targetK53_datF, classNodesAgree_datF env p formerTys Mc tele leaf fvs i ctor F es]
    · rfl

theorem classFieldsAgree_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) (F : Nat) :
    ∀ (i : Nat) (ks : List ClassField),
      (classFieldsAgree (fueledOpsM mode) env p formerTys Ms fvs ctor E i ks).val F =
        classFieldsAgree (fueledOps mode F) env p formerTys Ms fvs ctor E i ks
  | _, [] => rfl
  | i, .ordinary :: ks => by
    unfold classFieldsAgree
    exact classFieldsAgree_datF env p formerTys Ms fvs ctor E F (i + 1) ks
  | i, .recursive t tele :: ks => by
    unfold classFieldsAgree
    simp only [FueledM.atF_bind, unwrapOr_atF, classNodesAgree_datF,
      classFieldsAgree_datF env p formerTys Ms fvs ctor E F (i + 1) ks]

theorem classCtorOf_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (c : Nat) (cA : ConstantVal × Nat) (F : Nat) :
    (classCtorOf (fueledOpsM mode) env p formerTys rd Ms c cA).val F =
      classCtorOf (fueledOps mode F) env p formerTys rd Ms c cA := by
  unfold classCtorOf
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classMinorSlot_datF,
    classFieldsOf_datF, classFieldsAgree_datF]

theorem classCtorsOf_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (c : Nat) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)),
      (classCtorsOf (fueledOpsM mode) env p formerTys rd Ms c cs).val F =
        classCtorsOf (fueledOps mode F) env p formerTys rd Ms c cs
  | [] => rfl
  | cA :: cs => by
    unfold classCtorsOf
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtorOf_datF,
      classCtorsOf_datF env p formerTys rd Ms c F cs]

theorem classesCtors_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (F : Nat) :
    ∀ (c : Nat) (l : List TargetMajor),
      (classesCtors (fueledOpsM mode) env p formerTys rd Ms c l).val F =
        classesCtors (fueledOps mode F) env p formerTys rd Ms c l
  | _, [] => rfl
  | c, M :: rest => by
    unfold classesCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtorsOf_datF,
      classesCtors_datF env p formerTys rd Ms F (c + 1) rest]

theorem classMajors_datF (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs : List Expr) (F : Nat) :
    ∀ (keys : List ClassKey),
      (classMajors (fueledOpsM mode) fe p ctorsAs pfvs keys).val F =
        classMajors (fueledOps mode F) fe p ctorsAs pfvs keys
  | [] => rfl
  | key :: keys => by
    unfold classMajors
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetMajorOf_datF, targetMajorPins_datF,
      classMajors_datF fe p ctorsAs pfvs F keys]

theorem classesNfs_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) (F : Nat) :
    ∀ (Ms : List TargetMajor),
      (classesNfs (fueledOpsM mode) env p formerTys tbl Ms).val F =
        classesNfs (fueledOps mode F) env p formerTys tbl Ms
  | [] => rfl
  | M :: Ms => by
    unfold classesNfs
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetMajorNfs_datF,
      classesNfs_datF env p formerTys tbl F Ms]

theorem classFormerTy_datF (fe : FEnv) (cvTas : List ConstantVal) (M : TargetMajor) (F : Nat) :
    (classFormerTy (m := FueledM) fe cvTas M).val F = classFormerTy (m := CheckM) fe cvTas M := by
  unfold classFormerTy
  repeat' split
  all_goals rfl

theorem mapMLoop_atF {α β : Type} (f : α → FueledM β) (F : Nat) :
    ∀ (l : List α) (bs : List β),
      (List.mapM.loop f l bs).val F = List.mapM.loop (fun a => (f a).val F) l bs
  | [], _ => rfl
  | a :: l, bs => by
    simp only [List.mapM.loop, FueledM.atF_bind, mapMLoop_atF f F l]

theorem mapM_atF {α β : Type} (f : α → FueledM β) (F : Nat) (l : List α) :
    (l.mapM f).val F = l.mapM (fun a => (f a).val F) :=
  mapMLoop_atF f F l []

theorem classFormerTys_datF (fe : FEnv) (cvTas : List ConstantVal) (F : Nat)
    (Ms : List TargetMajor) :
    (Ms.mapM (classFormerTy (m := FueledM) fe cvTas)).val F =
      Ms.mapM (classFormerTy (m := CheckM) fe cvTas) := by
  rw [mapM_atF]
  simp only [classFormerTy_datF]

theorem classRecTyOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) (F : Nat) :
    (classRecTyOk (fueledOpsM mode) fe g k rc cvRi c).val F =
      classRecTyOk (fueledOps mode F) fe g k rc cvRi c := by
  unfold classRecTyOk
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, checkConstantValF_datF, fueledOpsM_isDefEq_atF]

theorem classRecTysOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (F : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cls : List Nat),
      (classRecTysOk (fueledOpsM mode) fe g k recs cvs cls).val F =
        classRecTysOk (fueledOps mode F) fe g k recs cvs cls
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    unfold classRecTysOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRecTyOk_datF,
      classRecTysOk_datF fe g k F rcs cvs cs]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl

theorem classRuleOk_datF (feT feR : FEnv) (cvR : ConstantVal) (pw : PropWhen) (n : Nat)
    (gen : Expr) (F : Nat) :
    (classRuleOk (fueledOpsM mode) .plain feT feR cvR pw n gen).val F =
      classRuleOk (fueledOps mode F) .plain feT feR cvR pw n gen := by
  unfold classRuleOk
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, fueledOpsM_annotate_atF, fueledOpsM_inferType_atF]

theorem classRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (pw : PropWhen) (c : Nat) (F : Nat) :
    ∀ (xs : List ClassCtor),
      (classRulesOk (fueledOpsM mode) .plain feT feR g recOf cvR pw c xs).val F =
        classRulesOk (fueledOps mode F) .plain feT feR g recOf cvR pw c xs
  | [] => rfl
  | x :: xs => by
    unfold classRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classRuleOk_datF,
      classRulesOk_datF feT feR g recOf cvR pw c F xs]

theorem classRecsRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (pw : PropWhen) (F : Nat) :
    ∀ (cvs : List ConstantVal) (cs : List Nat),
      (classRecsRulesOk (fueledOpsM mode) .plain feT feR g recOf pw cvs cs).val F =
        classRecsRulesOk (fueledOps mode F) .plain feT feR g recOf pw cvs cs
  | cvG :: cvs, c :: cs => by
    unfold classRecsRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRulesOk_datF,
      classRecsRulesOk_datF feT feR g recOf pw F cvs cs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem classStreamRecs_datF (fe : FEnv) (F : Nat) :
    ∀ (recs : List RecShape),
      (classStreamRecs (fueledOpsM mode) fe recs).val F = classStreamRecs (fueledOps mode F) fe recs
  | [] => rfl
  | rc :: rcs => by
    unfold classStreamRecs
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkConstantValF_datF,
      classStreamRecs_datF fe F rcs]

/-- **The generated recursor stage at fuel `F`**: the pure install's run
(`ShadowOps.ofOps` at the fueled family) is the model's fueled run. -/
theorem genRecCheck_datF (fe₁ : FEnv) (env₁ : Env) (fe : FEnv) (p : BlockShape)
    (nestedBit : Bool) (pos : NestState) (cvTas : List ConstantVal)
    (block : List ConstantInfo) (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (genRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe₁ env₁ fe p nestedBit pos cvTas block
        ctorsAs).val F =
      genRecCheck (ShadowOps.fueled mode F) fe₁ env₁ fe p nestedBit pos cvTas block ctorsAs := by
  unfold genRecCheck
  simp only [ShadowOps.ofOps, ShadowOps.fueled, FueledM.atF_bind, FueledM.atF_pure,
    FueledM.atF_throw, FueledM.atF_ite, unwrapOr_atF, targetRecPins_datF, classStreamRecs_datF,
    classMajors_datF, blockNestCtx_datF, nestSeeds_datF, classesNfs_datF, classesCtors_datF,
    classFormerTys_datF, classRecTysOk_datF, classRecsRulesOk_datF]

end ConLeche
