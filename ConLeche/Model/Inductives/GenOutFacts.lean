module

public import ConLeche.Model.Inductives.TargetClass
import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Model.Inductives.TargetOutIdx
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
  obtain ⟨ty, s, hty, hs, hr'⟩ := hcl.outsideInst hinst
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  generalize hψ : Level.substFn ψ cvI.levelParams M.lvls = ψ' at hlenP ⊢
  obtain ⟨ab, hta, hmap⟩ := hcl.read ψ'
  have hc := instPis_count_of_read hta cvI.levelParams M.lvls hty hs
  have hpl := hC.parsLen mm hcl.hmm ψ'
  have habl : ab.length = (D.pars mm ψ').length + (D.ids mm ψ').length := by
    have := congrArg List.length hmap
    simpa using this
  have hn : M.nIdx = ty.piBinders.1.length := congrArg Prod.fst hr'
  omega

/-- **A recorded class's telescope has a variable-free Π-tail** (its
reading is a Π-tower ending in a sort, `tailOk_of_read`). -/
theorem TgtOutCls.tailOk {envC : Env} {mpC : EnvModelM V envC}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC M D mm cvI) : TailOk (D.formerAt mm cvI).type := by
  obtain ⟨ab, hta, -⟩ := hcl.read (fun _ => 0)
  exact tailOk_of_read _ _ rfl hta

/-- **The walk's index count of a container instance is the class
check's.** -/
theorem nestInstType_count {envC : Env} {mpC : EnvModelM V envC} {M : TargetMajor} {D : LfpDatum V}
    {mm : Nat} {cvI : ConstantVal} (hcl : TgtOutCls mpC M D mm cvI) {ctx : NestCtx}
    {hi F : Nat} {key : ConLeche.NestKey} {nI : Nat} {cty : Expr}
    (hF : ConLeche.NestInstFacts ctx hi key cvI.levelParams (D.formerAt mm cvI).type nI cty)
    {us' : List Level} {ds' : List Expr} {nIdx : Nat} {sI : Level}
    (h2 : ConLeche.targetOutsideInst (ConLeche.fueledOps .verified F) (mkFEnv envC) M.ind us' ds'
      = .ok (nIdx, sI))
    (hlen : key.ds.length = ds'.length) : nI = nIdx := by
  have htl := hcl.tailOk
  obtain ⟨ty', s', hty', -, hr'⟩ := hcl.outsideInst h2
  have hn : nIdx = ty'.piBinders.1.length := congrArg Prod.fst hr'
  have hty := hF.inst
  obtain ⟨a1, -, a3⟩ := tail_instantiateLevelParams cvI.levelParams key.lvls (D.formerAt mm cvI).type
  obtain ⟨b1, -, b3⟩ := tail_instantiateLevelParams cvI.levelParams us' (D.formerAt mm cvI).type
  obtain ⟨k1, -⟩ := tail_instPisWith key.ds (a3.mpr htl) hty
  obtain ⟨k1', -⟩ := tail_instPisWith ds' (b3.mpr htl) hty'
  rw [hF.count, hn, ← piCount_eq_length, ← piCount_eq_length]
  omega

end ConLeche.Model
