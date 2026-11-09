module

public import ConLeche.Cached.CheckerC
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.IndRecC

public section

/-!
# The cached tail of the inductive check is the specification's (task #498)

The twins of `ConLeche/Cached/IndTail.lean` mirror the specification
(`blockRecInfosTF`, `streamRecsCheck`,
`checkBlockTablesF`) step by step at the shared operations `sharedOpsC`,
with the cached walks in place of the plain ones; each is equal to it, by
the walks' equations and unfolding.  The cached driver's lemmas
(`checkBlockTailS_run`, `checkBlockTailS_twin`, `checkBlockTailS_fresh`)
rewrite by them once and then read the specification.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-! ## The generated recursors' records -/

theorem auxRuleFireC_eq (M : TargetMajor) (rP : Nat) : auxRuleFireC M rP = auxRuleFire M rP := by
  have h : Expr.abstractPrefixC rP 0 = Expr.abstractPrefix rP 0 :=
    funext (Expr.abstractPrefixC_eq rP 0)
  simp only [auxRuleFireC, auxRuleFire, h]

theorem generatedRulesC_eq (rP : Nat) (M : TargetMajor) (rhss : List Expr) :
    generatedRulesC rP M rhss = generatedRules rP M rhss := by
  unfold generatedRulesC generatedRules
  cases M.member <;> simp only [auxRuleFireC_eq]

theorem blockRecInfosTC_eq (p : BlockShape) :
    ∀ m out, blockRecInfosTC p m out = blockRecInfosTF p m out
  | _, [] => rfl
  | m, (cv, M, rhss) :: rest => by
    simp only [blockRecInfosTC, blockRecInfosTF, generatedRulesC_eq, blockRecInfosTC_eq p (m + 1)]

theorem generatedFireC_eq (M : TargetMajor) (rP : Nat) :
    generatedFireC M rP = generatedFire M rP := by
  unfold generatedFireC generatedFire
  cases M.member <;> simp only [auxRuleFireC_eq]

/-! ## The stream's recursors -/

theorem streamNestedOkC_eq (ty : Expr) (mI rP : Nat) (f : RecRuleFire) :
    streamNestedOkC ty mI rP f = streamNestedOk ty mI rP f := by
  have h : (fun e => Expr.liftLooseBVarsC (mI - rP) e 0) = Expr.liftLooseBVars (mI - rP) 0 :=
    funext fun _ => Expr.liftLooseBVarsC_spec
  cases f <;> simp only [streamNestedOkC, streamNestedOk, Expr.getAppArgsC_spec, h] <;> rfl

theorem recDomsAtC_eq (fe : FEnv) (rec : Name) (sfvs gfvs : List Expr) :
    ∀ j k, recDomsAtC mode fe rec sfvs gfvs j k =
      recDomsAt (sharedOpsC mode fe) fe.env rec sfvs gfvs j k
  | _, 0 => rfl
  | j, k + 1 => by
    simp only [recDomsAtC, recDomsAt, recDomsAtC_eq fe rec sfvs gfvs (j + 1) k]
    rfl

theorem recTyOpenedC_eq (fe : FEnv) (rec : Name) (n : Nat) :
    ∀ a b, recTyOpenedC mode fe rec n a b = recTyOpened (sharedOpsC mode fe) fe.env rec n a b
  | some (sfvs, srest), some (gfvs, grest) => by
    simp only [recTyOpenedC, recTyOpened, recDomsAtC_eq]
    rfl
  | none, _ => rfl
  | some _, none => rfl

theorem recTyCheckC_eq (fe : FEnv) (rec : Name) (lps : List Name) (n : Nat) (s g : Expr) :
    recTyCheckC mode fe rec lps n s g = recTyCheck (sharedOpsC mode fe) fe rec lps n s g := by
  simp only [recTyCheckC, recTyCheck, Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec,
    unresolvedConstsErrorLC_true, openPisAtFvarsC_eq, recTyOpenedC_eq]
  rfl

theorem ruleAgreeC_eq (fe : FEnv) (rec ctor : Name) (lps : List Name) (s g : Expr) :
    ruleAgreeC mode fe rec ctor lps s g = ruleAgree (sharedOpsC mode fe) fe rec ctor lps s g := by
  simp only [ruleAgreeC, ruleAgree, Expr.allLevelParamsDefinedC_spec, constsResolveFC_spec,
    unresolvedConstsErrorLC_true]
  rfl

theorem streamRulesShapeC_eq (rec : Name) :
    ∀ rs cs, streamRulesShapeC rec rs cs = streamRulesShape (m := CheckCM) rec rs cs
  | [], [] => rfl
  | r :: rs, c :: cs => by
    simp only [streamRulesShapeC, streamRulesShape, streamRulesShapeC_eq rec rs cs]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem streamRulesCheckC_eq (fe : FEnv) (rec : Name) (lps : List Name) :
    ∀ rs gs, streamRulesCheckC mode fe rec lps rs gs =
      streamRulesCheck (sharedOpsC mode fe) fe rec lps rs gs
  | r :: rs, g :: gs => by
    simp only [streamRulesCheckC, streamRulesCheck, ruleAgreeC_eq,
      streamRulesCheckC_eq fe rec lps rs gs]
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem streamRecCompareC_eq (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) :
    streamRecCompareC mode fe rc g = streamRecCompare (sharedOpsC mode fe) fe rc g := by
  simp only [streamRecCompareC, streamRecCompare, recTyCheckC_eq, streamRulesCheckC_eq]

theorem streamRecCheckC_eq (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) :
    streamRecCheckC mode fe rc g = streamRecCheck (sharedOpsC mode fe) fe rc g := by
  simp only [streamRecCheckC, streamRecCheck, streamRulesShapeC_eq, streamNestedOkC_eq,
    generatedFireC_eq, streamRecCompareC_eq]

/-- **The cached stream-recursor check is the specification's at the
shared operations.** -/
theorem streamRecsCheckC_eq (fe : FEnv) :
    ∀ recs out, streamRecsCheckC mode fe recs out = streamRecsCheck (sharedOpsC mode fe) fe recs out
  | rc :: rcs, g :: gs => by
    simp only [streamRecsCheckC, streamRecsCheck, streamRecCheckC_eq,
      streamRecsCheckC_eq fe rcs gs]
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-! ## The projection tables -/

theorem checkStructProjTableC_eq (t : ProjTable) (fe : FEnv) :
    checkStructProjTableC t fe = checkStructProjTableF (m := CheckCM) t fe := by
  simp only [checkStructProjTableC, checkStructProjTableF, Expr.allLevelParamsDefinedC_spec,
    constsResolveFC_spec]

theorem checkBlockTablesC_eq (fe : FEnv) :
    ∀ Q, checkBlockTablesC fe Q = checkBlockTablesF (m := CheckCM) fe Q
  | [] => rfl
  | t :: rest => by
    simp only [checkBlockTablesC, checkBlockTablesF, checkStructProjTableC_eq,
      checkBlockTablesC_eq fe rest]

end ConLeche.Cached
