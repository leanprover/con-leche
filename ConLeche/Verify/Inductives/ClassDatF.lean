module

public import ConLeche.Verify.BridgeDecl
public import ConLeche.Verify.Inductives.ClassInv

public section

/-!
# The class check at fuel `F` (the fueled bridge)

The `atF` battery of `Verify/BridgeDecl.lean`, extended to the class
checker (`ConLeche/Kernel/Inductives/ClassCheck.lean`): the pure
install's run of `classRecCheck` at the fueled family
(`ShadowOps.ofOps (fueledOpsM mode)`) read at fuel `F` IS the run at the
fueled operations `ShadowOps.fueled mode F` (`classRecCheck_datF`), which
`ClassInv.lean` inverts.  The class check catches no error (the verified
monads do not support `tryCatch`), so every stage commutes with reading
at `F`.
-/


namespace ConLeche

variable {mode : CheckMode}

/-! ## Generic: `mapM` and `for` loops at fuel `F` -/

theorem mapM_loop_atF {α β : Type} (f : α → FueledM β) (F : Nat) :
    ∀ (l : List α) (acc : List β),
      (List.mapM.loop f l acc).val F = List.mapM.loop (fun a => (f a).val F) l acc
  | [], acc => rfl
  | a :: l, acc => by
    simp only [List.mapM.loop, FueledM.atF_bind]
    congr 1
    funext b
    exact mapM_loop_atF f F l (b :: acc)

theorem mapM_atF {α β : Type} (f : α → FueledM β) (F : Nat) (l : List α) :
    (l.mapM f).val F = l.mapM (fun a => (f a).val F) :=
  mapM_loop_atF f F l []

theorem forIn_atF {α σ : Type} (f : α → σ → FueledM (ForInStep σ)) (F : Nat) :
    ∀ (l : List α) (init : σ),
      (forIn l init f).val F = forIn l init (fun a s => (f a s).val F)
  | [], init => rfl
  | a :: l, init => by
    rw [List.forIn_cons, List.forIn_cons, FueledM.atF_bind]
    congr 1
    funext r
    cases r with
    | done b => rfl
    | yield b => exact forIn_atF f F l b

/-! ## The `atF` walk over do-blocks with join points

A do-block's guard (`unless c do throw e`) before more statements
elaborates to a JOIN POINT `have jp := k; if c then jp () else throw e >>=
jp`; `simp`'s ζ-reduction copies `k` into both branches, exponentially in
the number of guards.  The walk instead hoists the `have`s into the
context (`extract_lets`), closes every failure branch without entering
its join point (`throw_bind_atF`), and unfolds a join point only where it
is called (`zetaDelta`). -/

theorem throw_bind_atF {α β : Type} {e : CheckError} {f : α → FueledM β} {f' : α → CheckM β}
    {F : Nat} : ((throw e : FueledM α) >>= f).val F = ((throw e : CheckM α) >>= f') := rfl

theorem discard_atF {α : Type} (x : FueledM α) (F : Nat) :
    (discard x : FueledM Unit).val F = discard (x.val F) := by
  show (x >>= fun _ => pure ()).val F = _
  rw [FueledM.atF_bind]
  cases x.val F <;> rfl

theorem bind_congr' {α β : Type} {x y : CheckM α} {f g : α → CheckM β} (h1 : x = y)
    (h2 : ∀ a, f a = g a) : x >>= f = y >>= g := by
  subst h1; congr 1; funext a; exact h2 a

theorem mapM_congr' {α β : Type} {f g : α → CheckM β} (h : ∀ a, f a = g a) (l : List α) :
    l.mapM f = l.mapM g := by
  have : f = g := funext h
  subst this; rfl

/-- The walk (see above), with extra rewrites. -/
macro "datF_x" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat' (first
    | with_reducible rfl
    | exact throw_bind_atF
    | extract_lets
    | ((rw [FueledM.atF_bind]; congr 1 <;> try (with_reducible rfl)) <;> try funext _)
    | (with_reducible refine bind_congr' ?_ (fun _ => ?_))
    | (with_reducible refine mapM_congr' (fun _ => ?_) _)
    | (simp (config := { zeta := false }) only [FueledM.atF_pure, FueledM.atF_throw,
        FueledM.atF_ite, unwrapOr_atF, liftFueled_atF, fueledOpsM_annotate_atF,
        fueledOpsM_inferType_atF, fueledOpsM_isDefEq_atF, fueledOpsM_ensureSort_atF,
        fueledOpsM_whnf_atF, discard_atF, $ls,*])
    | split
    | (rw [forIn_atF]; congr 1; funext _ _)
    | (simp (config := { zetaDelta := true, zeta := false }) only [])))

/-! ## Check 1 -/

theorem classInfo_datF (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (a : Nat) (key : ClassKey) (F : Nat) :
    (classInfo (fueledOpsM mode) env ctx holes ctorsAs a key).val F =
      classInfo (fueledOps mode F) env ctx holes ctorsAs a key := by
  unfold classInfo
  datF_x [mapM_atF, nestInstType_datF]

theorem classInfos_datF (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    ∀ (a : Nat) (ks : List ClassKey),
      (classInfos (fueledOpsM mode) env ctx holes ctorsAs a ks).val F =
        classInfos (fueledOps mode F) env ctx holes ctorsAs a ks
  | _, [] => rfl
  | a, k :: ks => by
    unfold classInfos
    datF_x [classInfo_datF, classInfos_datF env ctx holes ctorsAs F _ ks]

theorem classKeysCyclic_datF (env : Env) (cls : List ClassInfo) (dsF : Nat → List Expr)
    (hi F : Nat) :
    ∀ (cs : List Nat),
      (classKeysCyclic (fueledOpsM mode) env cls dsF hi cs).val F =
        classKeysCyclic (fueledOps mode F) env cls dsF hi cs
  | [] => rfl
  | c :: cs => by
    unfold classKeysCyclic
    datF_x [classKeysCyclic_datF env cls dsF hi F cs]

/-! ## The defeq tier -/

theorem classParamsDefEq_datF (env : Env) (d F : Nat) :
    ∀ (as bs : List Expr),
      (classParamsDefEq (fueledOpsM mode) env d as bs).val F =
        classParamsDefEq (fueledOps mode F) env d as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold classParamsDefEq
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, fueledOpsM_inferType_atF,
      fueledOpsM_isDefEq_atF, classParamsDefEq_datF env d F as bs]

theorem classAliases_datF (env : Env) (hi : Nat) (cls : List ClassInfo) (F : Nat) :
    ∀ (es : List Expr),
      (classAliases (fueledOpsM mode) env hi cls es).val F =
        classAliases (fueledOps mode F) env hi cls es
  | [] => rfl
  | e :: es => by
    unfold classAliases
    datF_x [classAliases_datF env hi cls F es, classParamsDefEq_datF]

theorem classSamePairs_datF (env : Env) (hi : Nat) (cls : List ClassInfo) (F : Nat) :
    (classSamePairs (fueledOpsM mode) env hi cls).val F =
      classSamePairs (fueledOps mode F) env hi cls := by
  unfold classSamePairs
  datF_x [classParamsDefEq_datF]

/-! ## Checks 3 and 4 -/

theorem classPos_datF (env : Env) (ctx : NestCtx) (cls : List ClassInfo) (hi F : Nat) :
    ∀ (fuel dep kb : Nat) (e : Expr),
      (classPos (fueledOpsM mode) env ctx cls hi fuel dep kb e).val F =
        classPos (fueledOps mode F) env ctx cls hi fuel dep kb e
  | 0, _, _, _ => rfl
  | fuel + 1, dep, kb, e => by
    unfold classPos
    datF_x [classPos_datF env ctx cls hi F fuel]

theorem classFields_datF (env : Env) (ctx : NestCtx) (cls : List ClassInfo) (hi fuel F : Nat)
    (base : Nat) :
    ∀ (nF j : Nat) (cur : Expr),
      (classFields (fun d e => classPos (fueledOpsM mode) env ctx cls hi fuel d 0 e) base nF j cur).val F
        = classFields (fun d e => classPos (fueledOps mode F) env ctx cls hi fuel d 0 e) base nF j cur
  | 0, _, _ => rfl
  | nF + 1, j, cur => by
    unfold classFields
    split
    · simp only [FueledM.atF_bind, FueledM.atF_pure, classPos_datF,
        classFields_datF env ctx cls hi fuel F base nF]
    · rfl

theorem classCtor_datF (env : Env) (ctx : NestCtx) (holes : List Expr) (cls : List ClassInfo)
    (hi : Nat) (c : ClassInfo) (cv : ConstantVal) (nF : Nat) (crest : Expr) (F : Nat) :
    (classCtor (fueledOpsM mode) env ctx holes cls hi c cv nF crest).val F =
      classCtor (fueledOps mode F) env ctx holes cls hi c cv nF crest := by
  unfold classCtor
  datF_x [classFields_datF, checkStructFieldSortsI_datF, nestNoMemberConst_datF]

theorem classCtors_datF (env : Env) (ctx : NestCtx) (holes : List Expr) (cls : List ClassInfo)
    (hi : Nat) (c : ClassInfo) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (crests : List Expr),
      (classCtors (fueledOpsM mode) env ctx holes cls hi c cs crests).val F =
        classCtors (fueledOps mode F) env ctx holes cls hi c cs crests
  | (cv, nF) :: cs, crest :: crests => by
    unfold classCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtor_datF,
      classCtors_datF env ctx holes cls hi c F cs crests]
  | [], _ => by unfold classCtors; rfl
  | _ :: _, [] => by unfold classCtors; rfl

theorem classAllCtors_datF (env : Env) (ctx : NestCtx) (holes : List Expr) (cls : List ClassInfo)
    (hi F : Nat) :
    ∀ (cs : List ClassInfo) (crests : List (List Expr)),
      (classAllCtors (fueledOpsM mode) env ctx holes cls hi cs crests).val F =
        classAllCtors (fueledOps mode F) env ctx holes cls hi cs crests
  | c :: cs, cr :: crs => by
    unfold classAllCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtors_datF,
      classAllCtors_datF env ctx holes cls hi F cs crs]
  | [], _ => by unfold classAllCtors; rfl
  | _ :: _, [] => by unfold classAllCtors; rfl

/-! ## Checks 5 and 6 -/

theorem classMinorSlot_datF (rd : ClassRead) (c : Nat) (C : Name) (F : Nat) :
    (classMinorSlot (m := FueledM) rd c C).val F = classMinorSlot (m := CheckM) rd c C := by
  unfold classMinorSlot
  datF_x [unwrapOr_atF]

theorem classIhsAgree_datF (sameIdx : Nat → Nat → Bool) (ctor : Name) (ihs : List (Nat × Nat))
    (F : Nat) :
    ∀ (i : Nat) (ks : List ClassField),
      (classIhsAgree (m := FueledM) sameIdx ctor ihs i ks).val F =
        classIhsAgree (m := CheckM) sameIdx ctor ihs i ks
  | _, [] => rfl
  | i, k :: ks => by
    unfold classIhsAgree
    datF_x [classIhsAgree_datF sameIdx ctor ihs F (i + 1) ks]

theorem classCrest_datF (ctx : NestCtx) (holes : List Expr) (cls : List ClassInfo) (c : ClassInfo)
    (cv : ConstantVal) (F : Nat) :
    (classCrest (m := FueledM) ctx holes cls c cv).val F = classCrest (m := CheckM) ctx holes cls c cv := by
  unfold classCrest
  datF_x [unwrapOr_atF]

theorem classRuleOk_datF (feT feR : FEnv) (cvR : ConstantVal) (pw : PropWhen) (n : Nat)
    (rhs gen : Expr) (F : Nat) :
    (classRuleOk (fueledOpsM mode) .plain feT feR cvR pw n rhs gen).val F =
      classRuleOk (fueledOps mode F) .plain feT feR cvR pw n rhs gen := by
  unfold classRuleOk
  datF_x [unwrapOr_atF]

theorem classRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (pw : PropWhen) (c F : Nat) :
    ∀ (xs : List ClassCtor) (rhss : List Expr),
      (classRulesOk (fueledOpsM mode) .plain feT feR g recOf cvR pw c xs rhss).val F =
        classRulesOk (fueledOps mode F) .plain feT feR g recOf cvR pw c xs rhss
  | x :: xs, rhs :: rhss => by
    unfold classRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classRuleOk_datF,
      classRulesOk_datF feT feR g recOf cvR pw c F xs rhss]
  | [], _ => by unfold classRulesOk; rfl
  | _ :: _, [] => by unfold classRulesOk; rfl

theorem classRecTyOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (rules : List RecRule) (c F : Nat) :
    (classRecTyOk (fueledOpsM mode) fe g k rc rules c).val F =
      classRecTyOk (fueledOps mode F) fe g k rc rules c := by
  unfold classRecTyOk
  datF_x [checkConstantValF_datF, targetRulePins_datF]

theorem classRecTysOk_datF (fe : FEnv) (g : ClassGen) (k F : Nat) :
    ∀ (rcs : List RecShape) (rss : List (List RecRule)) (cs : List Nat),
      (classRecTysOk (fueledOpsM mode) fe g k rcs rss cs).val F =
        classRecTysOk (fueledOps mode F) fe g k rcs rss cs
  | rc :: rcs, rs :: rss, c :: cs => by
    unfold classRecTysOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRecTyOk_datF,
      classRecTysOk_datF fe g k F rcs rss cs]
  | [], _, _ => by unfold classRecTysOk; rfl
  | _ :: _, [], _ => by unfold classRecTysOk; rfl
  | _ :: _, _ :: _, [] => by unfold classRecTysOk; rfl

theorem classRecsRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (pw : PropWhen) (F : Nat) :
    ∀ (rcs : List RecShape) (cvs : List ConstantVal) (cs : List Nat),
      (classRecsRulesOk (fueledOpsM mode) .plain feT feR g recOf pw rcs cvs cs).val F =
        classRecsRulesOk (fueledOps mode F) .plain feT feR g recOf pw rcs cvs cs
  | rc :: rcs, cv :: cvs, c :: cs => by
    unfold classRecsRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRulesOk_datF,
      classRecsRulesOk_datF feT feR g recOf pw F rcs cvs cs]
  | [], _, _ => by unfold classRecsRulesOk; rfl
  | _ :: _, [], _ => by unfold classRecsRulesOk; rfl
  | _ :: _, _ :: _, [] => by unfold classRecsRulesOk; rfl

/-! ## The whole check -/

/-- **The class check at fuel `F`**: the pure install's run
(`ShadowOps.ofOps` at the fueled family) is the model's fueled run. -/
theorem classRecCheck_datF (fe₁ : FEnv) (env₁ : Env) (fe : FEnv) (p : BlockParts)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (classRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe₁ env₁ fe p block cvTas ctorsAs).val F =
      classRecCheck (ShadowOps.fueled mode F) fe₁ env₁ fe p block cvTas ctorsAs := by
  unfold classRecCheck
  simp (config := { zeta := false }) only [ShadowOps.ofOps, ShadowOps.fueled]
  datF_x [targetRecPins_datF, classInfos_datF, classKeysCyclic_datF, mapM_atF, classCrest_datF,
    classAliases_datF, classSamePairs_datF, classAllCtors_datF, classMinorSlot_datF,
    classIhsAgree_datF, classRecTysOk_datF, classRecsRulesOk_datF]

/-- **The pure install's class check, at a fuel, inverted**: a successful
run at the fueled family, read at `F`, is a `ClassRun` of the fueled
operations at `F` (the model's run). -/
theorem classRecCheck_run_atF {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {ctors : List (List ClassCtor)} {F : Nat}
    (h : (classRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe₁ env₁ fe p block cvTas
      ctorsAs).val F = .ok (out, ctors)) :
    Nonempty (ClassRun (fueledOps mode F) fe₁ env₁ fe p block cvTas ctorsAs out ctors) :=
  classRecCheck_run (by rw [classRecCheck_datF] at h; exact h)

end ConLeche
