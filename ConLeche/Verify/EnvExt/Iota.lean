module

public import ConLeche.Verify.EnvExt.Ok
import ConLeche.Verify.EnvExt.Certs
import ConLeche.Verify.EnvExt.Reads
import ConLeche.Verify.EnvExt.ScOps

public section

/-!
# Env extension, part 6: the ι step

The stuck-major rescues (`majorToCtor`), the major's preparation
(`prepareMajor`) and the ι step (`iotaRec`).  The reads of kind C live
here: a rule's constructor (`find? rl.ctor`), that constructor's
inductive (the result head of its stored type), the η constructor and
the nested rules' stored instantiations — all scoped by `Agree.closed`.
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop} {E₁ E₂ : Env} (H : Agree N E₁ E₂)
  {r₁ r₂ : CoreFns CheckM} (hr : RecOK N r₁ r₂) (mode : CheckMode)

include H hr in
theorem majorToCtor_ok (d : Nat) (recName : Name) {rules : List RecRule}
    (hrules : ∀ rl ∈ rules, RuleSc N rl)
    (heta : ∀ rl ∈ rules, rl.eta = true → recRuleEtaOf E₁.find? recName rl.ctor = true)
    {major : Expr} (hmaj : Sc N major) :
    Ok (Sc N) (majorToCtor mode r₂ E₂ d recName rules major)
      (majorToCtor mode r₁ E₁ d recName rules major) := by
  unfold majorToCtor
  rw [H.isCtorApp_eq hmaj]
  refine Ok.ite (fun _ => Ok.pure hmaj) (fun _ => ?_)
  split
  · rename_i rl
    have hrl := hrules rl (by simp)
    have hctor : N rl.ctor := hrl.1
    rw [H.find hctor]
    split
    · rename_i cvj cnP _cnF hfj
      have hcvj : Sc N cvj.type := H.stored_type_sc hctor hfj
      split
      · rename_i T _ hfnT
        have hT : N T := head_const_N (sc_piResult hcvj) hfnT
        rw [H.find hT]
        split
        · rename_i cvT caps hfT
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.ite (fun hEta => ?_)
            (fun _ => Ok.ite (fun hAnd => ?_) (fun _ => Ok.pure hmaj)))
          · -- the K rescue
            refine Ok.bind (hr.inferIO d major hmaj) (fun tm htm => ?_)
            refine Ok.bind (hr.whnf d tm htm) (fun tmaj htmaj => ?_)
            have hargs := sc_getAppArgs htmaj
            split
            · rename_i T' ust _
              have hfab : Sc N (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) :=
                sc_mkAppN (sc_const.mpr hctor) (sc_mem_take hargs)
              refine Ok.ite (fun _ => Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj))
                (fun _ => Ok.pure hmaj)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (iotaCerts_ok hr d false _ _ (H.const_type_sc hctor hfj _ _)
                (sc_mem_take hargs)) (fun v₁ _ => ?_)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (hr.inferIO d _ hfab) (fun tf htf => ?_)
              refine Ok.bind (hr.defeq d tmaj tf htmaj htf) (fun v₂ _ => ?_)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (proofIrrel_ok H hr d hfab hmaj) (fun v₃ _ => ?_)
              exact Ok.ite (fun _ => Ok.pure hfab) (fun _ => Ok.pure hmaj)
            · exact Ok.pure hmaj
          · -- the structure-η rescue: the η bit says the η constructor is the rule's
            have hcaps : N caps.etaCtor := by
              have h := heta rl (by simp) hEta
              simp only [recRuleEtaOf, hfj, hfnT, hfT, Bool.and_eq_true, beq_iff_eq] at h
              rw [h.1.1.2]; exact hctor
            refine Ok.bind (hr.inferIO d major hmaj) (fun tm htm => ?_)
            refine Ok.bind (hr.whnf d tm htm) (fun tmaj htmaj => ?_)
            have hargs := sc_getAppArgs htmaj
            split
            · rename_i T' ust _
              rw [H.etaFabArgsE_eq hT]
              have hfa := H.etaFabArgsE_sc hT (us := ust) (nF := caps.etaFields) hargs hmaj
              have hfab : Sc N (Expr.mkAppN (.const caps.etaCtor ust)
                  (etaFabArgsE E₁ T ust tmaj.getAppArgs major caps.etaFields)) :=
                sc_mkAppN (sc_const.mpr hcaps) hfa
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (iotaCerts_ok hr d false _ _ (H.const_type_sc hctor hfj _ _) hfa)
                (fun v₁ _ => ?_)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (structEtaCertWith_ok H hr mode d hfab hmaj htmaj) (fun v₂ _ => ?_)
              refine Ok.ite (fun _ => Ok.pure hfab) (fun _ => Ok.ite (fun _ => ?_)
                (fun _ => Ok.pure hmaj))
              refine Ok.bind (proofIrrel_ok H hr d hfab hmaj) (fun v₃ _ => ?_)
              exact Ok.ite (fun _ => Ok.pure hfab) (fun _ => Ok.pure hmaj)
            · exact Ok.pure hmaj
          · -- the `And` rescue
            refine Ok.bind (hr.inferIO d major hmaj) (fun tm htm => ?_)
            refine Ok.bind (hr.whnf d tm htm) (fun tmaj htmaj => ?_)
            have hargs := sc_getAppArgs htmaj
            split
            · rename_i T' ust _
              rw [H.andRescueSlots_eq (hAnd ▸ hT)]
              have hprojs : ∀ x ∈ tmaj.getAppArgs ++
                  [Expr.proj T 0 major, Expr.proj T 1 major], Sc N x :=
                sc_mem_append hargs (by
                  intro x hx
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                  rcases hx with rfl | rfl <;> exact sc_proj.mpr ⟨hT, hmaj⟩)
              have hfab : Sc N (Expr.mkAppN (.const rl.ctor ust) _) :=
                sc_mkAppN (sc_const.mpr hctor) hprojs
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (iotaCerts_ok hr d false _ _ (H.const_type_sc hctor hfj _ _) hprojs)
                (fun v₁ _ => ?_)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (hr.inferIO d _ hfab) (fun tf htf => ?_)
              refine Ok.bind (hr.defeq d tmaj tf htmaj htf) (fun v₂ _ => ?_)
              refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hmaj)
              refine Ok.bind (proofIrrel_ok H hr d hfab hmaj) (fun v₃ _ => ?_)
              exact Ok.ite (fun _ => Ok.pure hfab) (fun _ => Ok.pure hmaj)
            · exact Ok.pure hmaj
        · exact Ok.pure hmaj
      · exact Ok.pure hmaj
    · exact Ok.pure hmaj
  · exact Ok.pure hmaj

include H hr in
theorem prepareMajor_ok (d : Nat) (recName : Name) {rules : List RecRule}
    (hrules : ∀ rl ∈ rules, RuleSc N rl)
    (heta : ∀ rl ∈ rules, rl.eta = true → recRuleEtaOf E₁.find? recName rl.ctor = true)
    {major : Expr} (hmaj : Sc N major) :
    Ok (Sc N) (prepareMajor mode r₂ E₂ d recName rules major)
      (prepareMajor mode r₁ E₁ d recName rules major) := by
  unfold prepareMajor
  refine Ok.ite (fun _ => ?_) (fun _ => ?_)
  · refine Ok.bind (majorToCtor_ok H hr mode d recName hrules heta hmaj) (fun mk hmk => ?_)
    refine Ok.bind (hr.whnf d mk hmk) (fun m₀ hm₀ => ?_)
    exact litMajorToCtor_ok H hr d hm₀
  · refine Ok.bind (hr.whnf d major hmaj) (fun m₀ hm₀ => ?_)
    refine Ok.bind (litMajorToCtor_ok H hr d hm₀) (fun m₁ hm₁ => ?_)
    exact majorToCtor_ok H hr mode d recName hrules heta hm₁

include H hr in
theorem iotaRec_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (OSc N) (iotaRec mode r₂ E₂ d e) (iotaRec mode r₁ E₁ d e) := by
  unfold iotaRec
  have hargs := sc_getAppArgs he
  have hnone : OSc N none := fun _ h => by cases h
  split
  · rename_i c us hfn
    have hc := head_const_N he hfn
    rw [H.find hc]
    split
    · rename_i cv mI rP rules hfc
      have hcl := H.closed hc hfc
      simp only [CiSc] at hcl
      have hcv : Sc N cv.type := hcl.1
      have hrules := hcl.2
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
      refine Ok.bind (prepareMajor_ok H hr mode d c hrules (H.etaRule hc hfc)
        (sc_getD hargs sc_bvar))
        (fun major hmaj => ?_)
      have hmargs := sc_getAppArgs hmaj
      split
      · rename_i cj usj hfnj
        have hcj := head_const_N hmaj hfnj
        rw [H.find hcj]
        split
        · rename_i cvj _ _ hfj
          split
          · rename_i rl hrlf
            have hrl : RuleSc N rl := hrules rl (List.mem_of_find?_eq_some hrlf)
            refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
            refine Ok.ite (fun _ => Ok.throw _) (fun _ => ?_)
            refine Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial)) (fun v₁ _ => ?_)
            refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
            refine Ok.bind (?_ : Ok (fun _ => True) _ _) (fun v₂ _ => ?_)
            · exact Ok.ite (fun _ => defEqList_ok hr d _ _ (sc_mem_take hmargs)
                (recFireComparands_sc hrl _ _ _ hargs _)) (fun _ => Ok.pure trivial)
            refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
            refine Ok.bind (iotaCerts_ok hr d _ _ _ (sc_instantiateLevelParams _ _ _ hcv)
              (sc_mem_append (sc_mem_take hargs) (by simpa using hmaj))) (fun v₃ _ => ?_)
            refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
            refine Ok.bind (iotaCerts_ok hr d _ _ _ (H.const_type_sc hcj hfj _ _) hmargs)
              (fun v₄ _ => ?_)
            refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
            refine Ok.bind (iotaIndexOk_ok hr d _ _ _ (H.const_type_sc hcj hfj _ _) hmargs
              (sc_mem_drop (sc_mem_take hargs))) (fun v₅ _ => ?_)
            refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hnone)
            refine Ok.pure (fun x hx => ?_)
            cases hx
            exact sc_mkAppN (sc_instantiateLevelParams _ _ _ hrl.2.1)
              (sc_mem_append (sc_mem_take hargs) (sc_mem_drop hmargs))
          · exact Ok.pure hnone
        · exact Ok.pure hnone
      · exact Ok.pure hnone
    · exact Ok.pure hnone
  · exact Ok.pure hnone

end ConLeche.EnvExt
