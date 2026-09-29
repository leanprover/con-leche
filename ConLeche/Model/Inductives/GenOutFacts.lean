module

public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetNodeRb
public import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# An outside class's counts, from its check as a major (lane GENREC-B2)

The generated stage checks every outside class as a major
(`targetMajorOf`'s outside arm: `targetCtorsOf`, `targetOutsideInst`);
the target check read the same counts off the recursor's type.  At the
class's recorded clause (`TgtOutCls`):

* `genOutParamsLen` — the clause's parameters number the class's;
* `genOutIdxLen` — its indices number the class's (`tgtOutIdx_len`
  without the target run);
* `nestInstType_count` — the positivity walk's index count of a container
  instance (`nestInstType`) is the class check's (`targetOutsideInst`):
  both count the index binders of the container's former, which the
  parameters do not change.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape TargetMajor FEnv mkFEnv
  NestCtx NestKey)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **An outside class's clause has the class's parameter count.** -/
theorem genOutParamsLen {envC : Env} {mpC : EnvModelM V μ envC} (hcov : LfpCover mpC [])
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) {sI : Level}
    (hinst : ConLeche.targetOutsideInst (m := ConLeche.CheckM) (mkFEnv envC) M.ind M.lvls M.ds
      = .ok (M.nIdx, sI))
    (hct : ConLeche.targetCtorsOf (mkFEnv envC) M.ind = some (M.nPc, M.ctors))
    (hdsLen : M.ds.length = M.nPc) (ψ : Name → Nat) :
    (D.params (Level.substFn ψ cvI.levelParams M.lvls)).length = M.ds.length := by
  sorry

/-- **An outside class's clause has the class's index count**
(`tgtOutIdx_len`, from the class's own check). -/
theorem genOutIdxLen {envC : Env} {mpC : EnvModelM V μ envC}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) {sI : Level}
    (hinst : ConLeche.targetOutsideInst (m := ConLeche.CheckM) (mkFEnv envC) M.ind M.lvls M.ds
      = .ok (M.nIdx, sI)) (ψ : Name → Nat)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams M.lvls)).length = M.ds.length) :
    (D.ids mm (Level.substFn ψ cvI.levelParams M.lvls)).length = M.nIdx := by
  sorry

/-- **The walk's index count of a container instance is the class
check's.** -/
theorem nestInstType_count {ctx : NestCtx} {hi : Nat} {I : Name} {us : List Level}
    {ds : List Expr} {nI : Nat} {cty : Expr}
    (h1 : ConLeche.nestInstType (m := ConLeche.CheckM) ctx hi ⟨I, us, ds⟩ = .ok (nI, cty))
    {fe : FEnv} {us' : List Level} {ds' : List Expr} {nIdx : Nat} {sI : Level}
    (h2 : ConLeche.targetOutsideInst (m := ConLeche.CheckM) fe I us' ds' = .ok (nIdx, sI))
    (hfind : ∃ cv caps, ctx.find? I = some (.indInfo cv caps) ∧
      fe.find? I = some (.indInfo cv caps))
    (hlen : ds.length = ds'.length) : nI = nIdx := by
  sorry

end ConLeche.Model
