module

import ConLeche.Verify.Inductives.SumWF
public import ConLeche.Verify.Inductives.FixWF

@[expose] public section

/-!
# `DeclNativeRun`: the direct recursive declaration relation
(task #188)

The direct recursive arm of `checkDecl`'s `.indDecl` clause
(`checkNative`, `ConLeche/Kernel/Inductives/NativeInstall.lean`), recorded as
a run relation exactly as `DeclSumRun`: the three front guards
(positivity — no negative field kind; the elimination restriction —
a large eliminator needs a provably nonzero sort, the one-constructor
`Prop` case being declined; the constructors' distinct names), the
former's run (the sum's stage), the constructors' runs at the
former's environment with the resolution guard pointed at that same
environment, the field kinds re-checked on the annotated types, the
recursor's run at the environment holding all constructors, and the
install spine.

Since the flip (milestone M6) no checker run produces this relation:
the fold reaches every non-nested block through `DeclBlockRun`.  It
remains the input of the one-member model route (`declNative`,
`ConLeche/Model/Inductives/DeclNative.lean`), whose retirement is a
separate census.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape NativeParts RecRule fueledOps checkSumInd checkSumCtors
  checkNativeRec checkNative checkNativeTable consSumCtors sumRules
  nativeFieldsOk nativeCaps)

/-- **The direct recursive declaration, as checked**: the stage runs
of `checkNative`.  `env` is the pre-block environment.  The pass the
install settled on (task #268) is the one recorded: the former at the
record at some `is_rec` verdict, the constructors at its environment,
the kinds classified on THOSE constructors, and the classified record
equal to the one the former carries. -/
def DeclNativeRun (μ : CheckMode) (F : Nat) (env : Env)
    (p₀ : NativeParts) (env₂ : Env) : Prop :=
  (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env) (cvTa : ConstantVal) (p₁ : InductiveShape) (p : NativeParts)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (kinds : List (List RecFieldKind))
    (cvRa : ConstantVal) (rhss : List Expr) (tfvs : List Expr) (trest : Expr)
    (isorts : List Level),
    -- the former's run completes the record with the sort it read
    -- (task #195; task #210 Part B: this route too); every later stage
    -- runs on the completed record `p` — the sort and the kinds
    checkSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p₀.toInductiveShape
      (fun p₁ => nativeCapsAt p₁ isRec) = .ok (env₁, cvTa, p₁) ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    checkSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok (ctorsA, sortss) ∧
    classifyFixKinds (m := ConLeche.CheckM) p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      = .ok kinds ∧
    -- the record the block owes is the one the former carries
    nativeCaps p = nativeCapsAt p₁ isRec ∧
    -- the elimination restriction: a large eliminator needs a provably
    -- nonzero sort unless the block has one constructor (the subsingleton
    -- case, task #202 Stage A2)
    (p.large = true → p.resSort.isNeverZero = true ∨ p.ctors.length < 2) ∧
    openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    ConLeche.checkStructFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) env₁ true false p.resSort
      p.nP (tfvs.drop p.nP) [] p.nIdx = .ok isorts ∧
    nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      ctorsA p.kinds p.rhss p.cvR.type = true ∧
    checkNativeRec (m := ConLeche.CheckM) (fueledOps μ F) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) ∧
    -- the projection table at a structure-like block (task #210 Part A)
    checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok env₂

end ConLeche.Semantics
