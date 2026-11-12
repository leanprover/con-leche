module

public import ConLeche.Cached.CheckerC
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.IndRecC
import ConLeche.Verify.Cached.IndPositivityC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.CheckerF

public section

/-!
# The block pass's and the classes' twins are the specification (task #498)

The twins of `ConLeche/Cached/IndBlock.lean` mirror
their (`Env`-level) specifications at the shared operations `sharedOpsC`: each
equation unfolds both sides, rewrites the cached walks by their spec
lemmas and the callees by their equations, and closes by `rfl` (the
shared operations are that core).  The drivers' proofs enter through
`checkBlockIndsC_eq`, `checkBlockCtorsC_eq`, `checkBlockClassesC_eq` and
`checkBlockIdxSortsC_eq`.  A stage that reads its environment (the constant check, the
resolution gates) is related at the index `mkFEnv env` of the specification's `env`; a stage that
reads it only through the operations, at any index and its `env`.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-! ## The pushes -/

theorem consBlockIndsF_mkFEnv (p₁ : BlockShape) (isRec : Bool) :
    ∀ (formers : List ConstantVal) (i : Nat) (env : Env),
      consBlockIndsF p₁ isRec formers i (mkFEnv env) = mkFEnv (consBlockInds p₁ isRec formers i env)
  | [], _, _ => rfl
  | cvTa :: rest, i, env => by
    simp only [consBlockIndsF, consBlockInds, push_mkFEnv]
    exact consBlockIndsF_mkFEnv p₁ isRec rest (i + 1) _

/-- The constructors' pushes onto `mkFEnv env` are the index of the consed environment. -/
theorem consSumCtorsF_mkFEnv (nP : Nat) (T : Name) :
    ∀ (cs : List (ConstantVal × Nat)) (env : Env),
      consSumCtorsF nP T cs (mkFEnv env) = mkFEnv (consSumCtors nP T cs env)
  | [], _ => rfl
  | c :: cs, env => by
    simp only [consSumCtorsF, consSumCtors, push_mkFEnv,
      consSumCtorsF_mkFEnv nP T cs ⟨.ctorInfo c.1 nP c.2 T :: env.consts, env.tables⟩]

theorem consBlockCtorsF_mkFEnv (nP : Nat) :
    ∀ (groups : List (Name × List (ConstantVal × Nat))) (env : Env),
      consBlockCtorsF nP groups (mkFEnv env) = mkFEnv (consBlockCtors nP groups env)
  | [], _ => rfl
  | (T, ctorList) :: rest, env => by
    simp only [consBlockCtorsF, consBlockCtors, consSumCtorsF_mkFEnv]
    exact consBlockCtorsF_mkFEnv nP rest _

/-! ## Stage 1: the formers -/

theorem checkBlockTeleC_eq (env : Env) (nP : Nat) (ms : MemberShape) :
    checkBlockTeleC mode (mkFEnv env) nP ms =
      checkBlockTele (sharedOpsC mode (mkFEnv env)) env nP ms := by
  simp only [checkBlockTeleC, checkBlockTele, checkConstantValC_eq, checkConstantValF_eq]

theorem checkBlockTelesC_eq (env : Env) (nP : Nat) :
    ∀ ms, checkBlockTelesC mode (mkFEnv env) nP ms =
      checkBlockTeles (sharedOpsC mode (mkFEnv env)) env nP ms
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockTelesC, checkBlockTeles, checkBlockTeleC_eq,
      checkBlockTelesC_eq env nP rest]

theorem checkBlockDomsAtC_eq (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    ∀ j, checkBlockDomsAtC mode fe off fvs doms j =
      checkBlockDomsAt (sharedOpsC mode fe) fe.env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkBlockDomsAtC, checkBlockDomsAt, checkBlockDomsAtC_eq fe off fvs doms j]
    rfl

theorem checkBlockAgreeC_eq (fe : FEnv) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    ∀ cvs, checkBlockAgreeC mode fe nP cvTa0 s0 cvs =
      checkBlockAgree (sharedOpsC mode fe) fe.env nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    simp only [checkBlockAgreeC, checkBlockAgree, openPisAtFvarsC_eq, checkBlockDomsAtC_eq,
      checkBlockAgreeC_eq fe nP cvTa0 s0 rest]

/-- **The cached formers' stage is `checkBlockInds` at the shared operations**, its
environment pushed onto the index. -/
theorem checkBlockIndsC_eq (env : Env) (p : BlockShape) (isRec : Bool) :
    checkBlockIndsC mode (mkFEnv env) p isRec =
      checkBlockInds (sharedOpsC mode (mkFEnv env)) env p isRec >>=
        fun r => pure (mkFEnv r.1, r.2) := by
  unfold checkBlockIndsC checkBlockInds
  rcases p.members with _ | ⟨ms0, rest⟩
  · rfl
  · simp only [checkBlockTeleC_eq, checkBlockTelesC_eq, checkBlockAgreeC_eq, mkFEnv_env,
      bind_assoc, pure_bind, consBlockIndsF_mkFEnv]

/-! ## Stage 1b: the constructors -/

theorem checkStructDomsAtC_eq (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    ∀ j, checkStructDomsAtC mode fe off fvs.toArray doms.toArray j =
      checkStructDomsAt (sharedOpsC mode fe) fe.env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAtC, checkStructDomsAt, List.getElem?_toArray,
      checkStructDomsAtC_eq fe off fvs doms j]
    rfl

theorem checkStructFieldSortsC_eq (fe : FEnv) (isProp large : Bool) (s : Level) (nP : Nat)
    (fvs idxArgs : List Expr) :
    ∀ j, checkStructFieldSortsC mode fe isProp large s nP fvs.toArray idxArgs j =
      checkStructFieldSortsI (sharedOpsC mode fe) fe.env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsC, checkStructFieldSortsI, List.getElem?_toArray,
      checkStructFieldSortsC_eq fe isProp large s nP fvs idxArgs j]
    rfl

theorem checkSumCtorC_eq (env₀ env : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    checkSumCtorC mode (mkFEnv env₀) (mkFEnv env) T lps nP nIdx resSort isProp large cvC nF cvTa =
      checkSumCtor (sharedOpsC mode (mkFEnv env)) env₀ env T lps nP nIdx resSort isProp large
        cvC nF cvTa := by
  simp only [checkSumCtorC, checkSumCtor, checkConstantValC_eq, checkConstantValF_eq,
    openPisAtFvarsC_eq, checkStructDomsAtC_eq, Expr.getAppArgsC_spec, constsResolveFC_spec,
    constsResolveF_eq, checkStructFieldSortsC_eq, mkFEnv_env]

theorem checkSumCtorsC_eq (env₀ env : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    ∀ cs, checkSumCtorsC mode (mkFEnv env₀) (mkFEnv env) T lps nP nIdx resSort isProp large
        cvTa cs =
      checkSumCtors (sharedOpsC mode (mkFEnv env)) env₀ env T lps nP nIdx resSort isProp large
        cvTa cs
  | [] => rfl
  | c :: cs => by
    simp only [checkSumCtorsC, checkSumCtors, checkSumCtorC_eq,
      checkSumCtorsC_eq env₀ env T lps nP nIdx resSort isProp large cvTa cs]

/-- **The cached constructors' stage is `checkBlockCtors` at the shared operations.** -/
theorem checkBlockCtorsC_eq (env₀ env : Env) (p : BlockShape) :
    ∀ ms, checkBlockCtorsC mode (mkFEnv env₀) (mkFEnv env) p ms =
      checkBlockCtors (sharedOpsC mode (mkFEnv env)) env₀ env p ms
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockCtorsC, checkBlockCtors, checkSumCtorsC_eq,
      checkBlockCtorsC_eq env₀ env p rest]

/-- **The cached index sorts are `checkBlockIdxSorts` at the shared operations.** -/
theorem checkBlockIdxSortsC_eq (fe₁ : FEnv) (p : BlockShape) :
    ∀ ms, checkBlockIdxSortsC mode fe₁ p ms =
      checkBlockIdxSorts (sharedOpsC mode fe₁) fe₁.env p ms
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockIdxSortsC, checkBlockIdxSorts, openPisAtFvarsC_eq,
      checkStructFieldSortsIC_eq, checkBlockIdxSortsC_eq fe₁ p rest]

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
