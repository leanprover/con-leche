module

public import ConLeche.Model.Inductives.TargetClass
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Model.Inductives.TargetOutIdx
public import ConLeche.Model.Inductives.FamilyRun
public import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.TargetOutRows

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
  each counts the index binders of a run's result for the container,
  which the parameters do not change (`instPis_count_of_read`), and both
  results read as towers of the block's telescope's length (`FormerRead`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape TargetMajor FEnv mkFEnv
  NestCtx NestKey)

universe w

variable {V : Type w} [SetTheory V]

/-- **An outside class's clause has the class's parameter count.** -/
theorem genOutParamsLen {envC : Env} {mpC : EnvModelM V envC} (hcov : LfpCover mpC [])
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI)
    (hct : ConLeche.targetCtorsOf (mkFEnv envC) M.ind = some (M.nPc, M.ctors))
    (hdsLen : M.ds.length = M.nPc) (ψ : Name → Nat) :
    (D.params (Level.substFn ψ cvI.levelParams M.lvls)).length = M.ds.length := by
  rw [hdsLen]
  by_cases hL : M.ctors = []
  · have hnc : ConLeche.nestContainer (envCtx envC) (D.member mm) = some (M.nPc, []) := by
      rw [hcl.hmem, ← targetCtorsOf_mkFEnv, hct, hL]
    obtain ⟨-, -, -, -, hlen, -⟩ := (hcov.own D hcl.hD).noCtors mm hcl.hmm M.nPc hnc
    exact hlen _
  · have h0 : 0 < M.ctors.length := List.length_pos_iff.mpr hL
    obtain ⟨-, -, -, hcrd, -⟩ := mpC.lfp_ok D hcl.hD
    obtain ⟨cv0, nPc0, nF0, _, hf0, -, -, -, _A, -, -, hread0⟩ :=
      hcrd.2 mm hcl.hmm 0 (by rw [← hcl.hlen]; exact h0)
    rw [(hcl.hctor 0 h0).choose_spec] at hf0
    obtain ⟨-, rfl, -⟩ : M.ctors[0].1 = cv0 ∧ M.nPc = nPc0 ∧ M.ctors[0].2 = nF0 := by
      simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf0
      exact ⟨hf0.1, hf0.2.1, hf0.2.2.1⟩
    exact (hread0 _).1

/-- **An outside class's clause has the class's index count**
(`tgtOutIdx_len`, from the class's own check). -/
theorem genOutIdxLen {envC : Env} {mpC : EnvModelM V envC}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) {F : Nat} {sI : Level}
    (hinst : ConLeche.targetOutsideInst (ConLeche.fueledOps .verified F) (mkFEnv envC) M.ind M.lvls M.ds
      = .ok (M.nIdx, sI)) (ψ : Name → Nat)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams M.lvls)).length = M.ds.length) :
    (D.ids mm (Level.substFn ψ cvI.levelParams M.lvls)).length = M.nIdx := by
  obtain ⟨-, tyI, ty, s, -, -, hR, hty, hs, hr'⟩ := hcl.outsideInst hinst
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  generalize hψ : Level.substFn ψ cvI.levelParams M.lvls = ψ' at hlenP ⊢
  obtain ⟨ab, u, hta, habl, -⟩ := hR.2.2.2 ψ'
  have hc := instPis_count_of_read hta cvI.levelParams M.lvls hty hs
  have hpl := hC.parsLen mm hcl.hmm ψ'
  rw [List.length_append] at habl
  have hn : M.nIdx = ty.piBinders.1.length := congrArg Prod.fst hr'
  omega

/-- **The walk's index count of a container instance is the class
check's**: the walk's run (at its own model `mk`) and the class check's
both read as towers of the block's telescope's length. -/
theorem nestInstType_count {envC envK : Env} {mpC : EnvModelM V envC} {mk : EnvModelM V envK}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) {ty : Expr} (hRK : FormerRead mk D mm ty) {ctx : NestCtx}
    {hi F : Nat} {key : ConLeche.NestKey} {nI : Nat} {cty : Expr}
    (hF : ConLeche.NestInstFacts ctx hi key cvI.levelParams ty nI cty)
    {us' : List Level} {ds' : List Expr} {nIdx : Nat} {sI : Level}
    (h2 : ConLeche.targetOutsideInst (ConLeche.fueledOps .verified F) (mkFEnv envC) M.ind us' ds'
      = .ok (nIdx, sI))
    (hlen : key.ds.length = ds'.length) : nI = nIdx := by
  obtain ⟨-, tyI, ty', s', -, -, hR, hty', hs', hr'⟩ := hcl.outsideInst h2
  obtain ⟨s, hs, -⟩ := hF.sort
  obtain ⟨abK, uK, htaK, hlK, -⟩ := hRK.2.2.2 (fun _ => 0)
  obtain ⟨abI, uI, htaI, hlI, -⟩ := hR.2.2.2 (fun _ => 0)
  have hcK := instPis_count_of_read htaK cvI.levelParams key.lvls hF.inst hs
  have hcI := instPis_count_of_read htaI cvI.levelParams us' hty' hs'
  have hn : nIdx = ty'.piBinders.1.length := congrArg Prod.fst hr'
  rw [hF.count, hn]
  omega

end ConLeche.Model
