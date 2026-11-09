module

public import ConLeche.Cached.CheckerC
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.IndRecC
import ConLeche.Verify.Cached.IndPositivityC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# The block pass's and the classes' twins are the specification (task #498)

The twins of `ConLeche/Cached/IndBlock.lean` mirror
their specifications at the shared operations `sharedOpsC`: each
equation unfolds both sides, rewrites the cached walks by their spec
lemmas and the callees by their equations, and closes by `rfl` (the
shared operations are that core).  The drivers' proofs enter through
`checkBlockIndsC_eq`, `checkBlockCtorsC_eq`, `checkBlockClassesC_eq` and
`checkBlockIdxSortsC_eq`.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-! ## Stage 1: the formers -/

theorem checkBlockTeleC_eq (fe : FEnv) (nP : Nat) (ms : MemberShape) :
    checkBlockTeleC mode fe nP ms = checkBlockTeleF (sharedOpsC mode fe) fe nP ms := by
  simp only [checkBlockTeleC, checkBlockTeleF, checkConstantValC_eq]

theorem checkBlockTelesC_eq (fe : FEnv) (nP : Nat) :
    ∀ ms, checkBlockTelesC mode fe nP ms = checkBlockTelesF (sharedOpsC mode fe) fe nP ms
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockTelesC, checkBlockTelesF, checkBlockTeleC_eq,
      checkBlockTelesC_eq fe nP rest]

theorem checkBlockDomsAtC_eq (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    ∀ j, checkBlockDomsAtC mode fe off fvs doms j =
      checkBlockDomsAtF (sharedOpsC mode fe) fe off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkBlockDomsAtC, checkBlockDomsAtF, checkBlockDomsAtC_eq fe off fvs doms j]
    rfl

theorem checkBlockAgreeC_eq (fe : FEnv) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    ∀ cvs, checkBlockAgreeC mode fe nP cvTa0 s0 cvs =
      checkBlockAgreeF (sharedOpsC mode fe) fe nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    simp only [checkBlockAgreeC, checkBlockAgreeF, openPisAtFvarsC_eq, checkBlockDomsAtC_eq,
      checkBlockAgreeC_eq fe nP cvTa0 s0 rest]

/-- **The cached formers' stage is `checkBlockIndsF` at the shared operations.** -/
theorem checkBlockIndsC_eq (fe : FEnv) (p : BlockShape) (isRec : Bool) :
    checkBlockIndsC mode fe p isRec = checkBlockIndsF (sharedOpsC mode fe) fe p isRec := by
  unfold checkBlockIndsC checkBlockIndsF
  simp only [checkBlockTeleC_eq, checkBlockTelesC_eq, checkBlockAgreeC_eq]
  rfl

/-! ## Stage 1b: the constructors -/

theorem checkStructDomsAtC_eq (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    ∀ j, checkStructDomsAtC mode fe off fvs.toArray doms.toArray j =
      checkStructDomsAtF (sharedOpsC mode fe) fe off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAtC, checkStructDomsAtF, List.getElem?_toArray,
      checkStructDomsAtC_eq fe off fvs doms j]
    rfl

theorem checkStructFieldSortsC_eq (fe : FEnv) (isProp large : Bool) (s : Level) (nP : Nat)
    (fvs idxArgs : List Expr) :
    ∀ j, checkStructFieldSortsC mode fe isProp large s nP fvs.toArray idxArgs j =
      checkStructFieldSortsIF (sharedOpsC mode fe) fe isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsC, checkStructFieldSortsIF, List.getElem?_toArray,
      checkStructFieldSortsC_eq fe isProp large s nP fvs idxArgs j]
    rfl

theorem checkSumCtorC_eq (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    checkSumCtorC mode fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa =
      checkSumCtorF (sharedOpsC mode fe) fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa := by
  simp only [checkSumCtorC, checkSumCtorF, checkConstantValC_eq, openPisAtFvarsC_eq,
    checkStructDomsAtC_eq, Expr.getAppArgsC_spec, constsResolveFC_spec,
    checkStructFieldSortsC_eq]

theorem checkSumCtorsC_eq (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    ∀ cs, checkSumCtorsC mode fe₀ fe T lps nP nIdx resSort isProp large cvTa cs =
      checkSumCtorsF (sharedOpsC mode fe) fe₀ fe T lps nP nIdx resSort isProp large cvTa cs
  | [] => rfl
  | c :: cs => by
    simp only [checkSumCtorsC, checkSumCtorsF, checkSumCtorC_eq,
      checkSumCtorsC_eq fe₀ fe T lps nP nIdx resSort isProp large cvTa cs]

/-- **The cached constructors' stage is `checkBlockCtorsF` at the shared operations.** -/
theorem checkBlockCtorsC_eq (fe₀ fe : FEnv) (p : BlockShape) :
    ∀ ms, checkBlockCtorsC mode fe₀ fe p ms = checkBlockCtorsF (sharedOpsC mode fe) fe₀ fe p ms
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockCtorsC, checkBlockCtorsF, checkSumCtorsC_eq,
      checkBlockCtorsC_eq fe₀ fe p rest]

/-- The index mirror of the field-sort walk is the `Env` one at the index's environment. -/
theorem checkStructFieldSortsIF_env (ops : CheckerOps CheckCM) (fe : FEnv) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : ∀ j,
      checkStructFieldSortsIF ops fe isProp large s nP fvs idxArgs j =
        checkStructFieldSortsI ops fe.env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsIF, checkStructFieldSortsI,
      checkStructFieldSortsIF_env ops fe isProp large s nP fvs idxArgs j]

/-- **The cached index sorts are `checkBlockIdxSortsF` at the shared operations.** -/
theorem checkBlockIdxSortsC_eq (fe₁ : FEnv) (p : BlockShape) :
    ∀ ms, checkBlockIdxSortsC mode fe₁ p ms =
      checkBlockIdxSortsF (sharedOpsC mode fe₁) fe₁ p ms
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockIdxSortsC, checkBlockIdxSortsF, openPisAtFvarsC_eq,
      checkStructFieldSortsIC_eq, checkStructFieldSortsIF_env, checkBlockIdxSortsC_eq fe₁ p rest]

/-! ## The classes -/

theorem classReadMinorC_eq (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    classReadMinorC nP motPos d dom = classReadMinor nP motPos d dom := by
  simp only [classReadMinorC, classReadMinor, openPisAtFvarsC_eq, Expr.getAppArgsC_spec]
  rfl

theorem classReadSlotsC_eq (nPc : Name → Nat) (np : Nat) :
    ∀ n motPos d e, classReadSlotsC nPc np n motPos d e = classReadSlots nPc np n motPos d e := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro motPos d e
    cases e <;> simp only [classReadSlotsC, classReadSlots, classReadMinorC_eq,
      Expr.getAppArgsC_spec, Expr.instantiate1C_spec, ih] <;> rfl

/-- **The cached pre-pass is `classRead`.** -/
theorem classReadC_eq (nP : Nat) (nPc : Name → Nat) (recs : List RecShape) :
    classReadC nP nPc recs = classRead nP nPc recs := by
  simp only [classReadC, classRead, openPisAtFvarsC_eq, classReadSlotsC_eq]
  rfl

theorem classKeyOfC_eq (nP : Nat) (params : List Expr) :
    classKeyOfC nP params = classKeyOf (m := CheckCM) nP params := by
  have hc : targetCanonParamsC params = targetCanonParams params := funext (targetCanonParamsC_eq params)
  funext k
  simp only [classKeyOfC, classKeyOf, classKeyCanonC, classKeyCanon, hc]
  rfl

theorem targetOutsideInstC_eq (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr) :
    targetOutsideInstC mode fe I us ds = targetOutsideInst (sharedOpsC mode fe) fe I us ds := by
  simp only [targetOutsideInstC, targetOutsideInst, familyTelescopeC_eq, Expr.instPisWithC_eq,
    Expr.instLevelParams_spec]
  rfl

theorem targetMajorOfC_eq (fe : FEnv) (p : BlockShape) (pfvs fvs : List Expr) (mty : Expr) :
    targetMajorOfC mode fe p pfvs fvs mty = targetMajorOf (sharedOpsC mode fe) fe p pfvs fvs mty := by
  simp only [targetMajorOfC, targetMajorOf, Expr.getAppArgsC_spec, Expr.nestOccC_spec,
    targetOutsideInstC_eq]
  rfl

theorem targetPinTysC_eq (fe : FEnv) (d : Nat) :
    ∀ xs, targetPinTysC mode fe d xs = targetPinTys (sharedOpsC mode fe) fe.env d xs
  | [] => rfl
  | x :: xs => by
    simp only [targetPinTysC, targetPinTys, targetPinTysC_eq fe d xs]
    rfl

theorem targetMajorPinsC_eq (fe : FEnv) (rP : Nat) (M : TargetMajor) :
    targetMajorPinsC mode fe rP M = targetMajorPins (sharedOpsC mode fe) fe rP M := by
  simp only [targetMajorPinsC, targetMajorPins, targetPinTysC_eq, familyKeyCheckC_eq]

theorem classMajorsC_eq (fe : FEnv) (p : BlockShape) (pfvs : List Expr) :
    ∀ keys, classMajorsC mode fe p pfvs keys = classMajors (sharedOpsC mode fe) fe p pfvs keys
  | [] => rfl
  | key :: keys => by
    simp only [classMajorsC, classMajors, targetMajorOfC_eq, targetMajorPinsC_eq,
      classMajorsC_eq fe p pfvs keys]

/-- **The cached classes are `checkBlockClasses` at the shared operations.** -/
theorem checkBlockClassesC_eq (fe₁ : FEnv) (p : BlockShape) (params : List Expr) :
    checkBlockClassesC mode fe₁ p params = checkBlockClasses (sharedOpsC mode fe₁) fe₁ p params := by
  simp only [checkBlockClassesC, checkBlockClasses, classReadC_eq, classKeyOfC_eq, classMajorsC_eq]

end ConLeche.Cached
