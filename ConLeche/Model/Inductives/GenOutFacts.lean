module

public import ConLeche.Model.Inductives.TargetClass
import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Cached.EnvBound

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
  parameters do not change — provided the former's syntactic Π-tail is
  no variable (`TailOk`; else a parameter could be substituted into the
  tail and open binders).  A recorded class has it off its former's
  reading (`TgtOutCls.tailOk`).
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
    (_hinst : ConLeche.targetOutsideInst (m := ConLeche.CheckM) (mkFEnv envC) M.ind M.lvls M.ds
      = .ok (M.nIdx, sI))
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
    obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
    obtain ⟨cv0, nPc0, nF0, hf0, -, -, -, _A, -, -, hread0⟩ :=
      hcrd.2 mm hcl.hmm 0 (by rw [← hcl.hlen]; exact h0)
    rw [hcl.hctor 0 h0] at hf0
    obtain ⟨-, rfl, -⟩ : M.ctors[0].1 = cv0 ∧ M.nPc = nPc0 ∧ M.ctors[0].2 = nF0 := by
      simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf0
      exact ⟨hf0.1, hf0.2.1, hf0.2.2⟩
    exact (hread0 _).1

/-- **An outside class's clause has the class's index count**
(`tgtOutIdx_len`, from the class's own check). -/
theorem genOutIdxLen {envC : Env} {mpC : EnvModelM V μ envC}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) {sI : Level}
    (hinst : ConLeche.targetOutsideInst (m := ConLeche.CheckM) (mkFEnv envC) M.ind M.lvls M.ds
      = .ok (M.nIdx, sI)) (ψ : Name → Nat)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams M.lvls)).length = M.ds.length) :
    (D.ids mm (Level.substFn ψ cvI.levelParams M.lvls)).length = M.nIdx := by
  obtain ⟨cvI', caps', ty, s, hf', hty, hs, hr'⟩ := targetOutsideInst_inv hinst
  obtain ⟨caps, hfI⟩ := hcl.hfind
  rw [mkFEnv_find?, hfI] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cvI' ∧ caps = caps' := by simpa using hf'
  obtain ⟨hC, -, hrd, -⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hcl.hmm
  rw [hcl.hmem, hfI] at hf₂
  obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  generalize hψ : Level.substFn ψ cvI.levelParams M.lvls = ψ' at hlenP ⊢
  obtain ⟨ab, hta, hmap, -⟩ := hab ψ'
  have hc := instPis_count_of_read hta cvI.levelParams M.lvls hty hs
  have hpl := hC.parsLen mm hcl.hmm ψ'
  have habl : ab.length = (D.pars mm ψ').length + (D.ids mm ψ').length := by
    have := congrArg List.length hmap
    simpa using this
  have hn : M.nIdx = ty.piBinders.1.length := congrArg Prod.fst hr'
  omega

/-- **A recorded class's former has a variable-free Π-tail** (its
reading is a Π-tower ending in a sort, `tailOk_of_read`). -/
theorem TgtOutCls.tailOk {envC : Env} {mpC : EnvModelM V μ envC}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) : TailOk cvI.type := by
  obtain ⟨caps, hfI⟩ := hcl.hfind
  obtain ⟨-, -, hrd, -⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hcl.hmm
  rw [hcl.hmem, hfI] at hf₂
  obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  obtain ⟨ab, hta, -, -⟩ := hab (fun _ => 0)
  exact tailOk_of_read _ _ rfl hta

/-- **The walk's index count of a container instance is the class
check's.** -/
theorem nestInstType_count {ctx : NestCtx} {hi : Nat} {I : Name} {us : List Level}
    {ds : List Expr} {nI : Nat} {cty : Expr}
    (h1 : ConLeche.nestInstType (m := ConLeche.CheckM) ctx hi ⟨I, us, ds⟩ = .ok (nI, cty))
    {fe : FEnv} {us' : List Level} {ds' : List Expr} {nIdx : Nat} {sI : Level}
    (h2 : ConLeche.targetOutsideInst (m := ConLeche.CheckM) fe I us' ds' = .ok (nIdx, sI))
    (hfind : ∃ cv caps, ctx.find? I = some (.indInfo cv caps) ∧
      fe.find? I = some (.indInfo cv caps) ∧ TailOk cv.type)
    (hlen : ds.length = ds'.length) : nI = nIdx := by
  obtain ⟨cv, caps, hc, hf, htl⟩ := hfind
  obtain ⟨cvC, capsC, hc', -, -, ty, s, hty, hs, -, rfl, -⟩ := ConLeche.nestInstType_inv h1
  obtain ⟨cvI, capsI, ty', s', hf', hty', hs', hr'⟩ := targetOutsideInst_inv h2
  simp only [hc, Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at hc'
  obtain ⟨rfl, rfl⟩ := hc'
  simp only [hf, Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  have hn : nIdx = ty'.piBinders.1.length := congrArg Prod.fst hr'
  obtain ⟨a1, -, a3⟩ := tail_instantiateLevelParams cv.levelParams us cv.type
  obtain ⟨b1, -, b3⟩ := tail_instantiateLevelParams cv.levelParams us' cv.type
  obtain ⟨k1, -⟩ := tail_instPisWith ds (a3.mpr htl) hty
  obtain ⟨k1', -⟩ := tail_instPisWith ds' (b3.mpr htl) hty'
  rw [hn, ← piCount_eq_length, ← piCount_eq_length]
  omega

end ConLeche.Model
