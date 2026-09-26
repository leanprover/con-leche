module

public import ConLeche.Verify.EnvExt.Ok

public section

/-!
# Env extension, part 5: the certificate and comparison helpers

The helpers the bodies call that return a verdict or a small value:
`iotaCerts`, `defEqList`, `iotaIndexOk`, `ensureSort`, `reduceNat`,
`boolTrueShortcut`, `defeqSpine`, the proof-irrelevance and η/unit
certificates, `stuckIrrel`, `projCert`.
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop} {E₁ E₂ : Env} (H : Agree N E₁ E₂)
  {r₁ r₂ : CoreFns CheckM} (hr : RecOK N r₁ r₂) (mode : CheckMode)

include hr in
theorem iotaCerts_ok (d : Nat) (lic : Bool) :
    ∀ (ty : Expr) (args : List Expr), Sc N ty → (∀ a ∈ args, Sc N a) →
      Ok (fun _ => True) (iotaCerts r₂ E₂ d lic ty args) (iotaCerts r₁ E₁ d lic ty args)
  | _, [], _, _ => Ok.pure trivial
  | .forallE ty body mb, arg :: rest, hty, hargs => by
    have hty' := sc_forallE.mp hty
    have ha : Sc N arg := hargs arg (by simp)
    have hrest : ∀ a ∈ rest, Sc N a := fun a h => hargs a (by simp [h])
    have ih := iotaCerts_ok d lic (body.instantiate1 arg) rest
      (sc_instantiate1' hty'.2 ha) hrest
    simp only [iotaCerts]
    refine Ok.ite (fun _ => ih) (fun _ => ?_)
    refine Ok.bind (hr.inferIO d arg ha) (fun ta hta => ?_)
    refine Ok.bind (hr.defeq d ta ty hta hty'.1) (fun b _ => ?_)
    cases b
    · exact Ok.pure trivial
    · exact ih
  | .bvar _, _ :: _, _, _ | .fvar _ _, _ :: _, _, _ | .sort _, _ :: _, _, _
  | .const _ _, _ :: _, _, _ | .app _ _, _ :: _, _, _ | .lam _ _ _, _ :: _, _, _
  | .letE _ _ _, _ :: _, _, _ | .lit _, _ :: _, _, _ | .proj _ _ _, _ :: _, _, _ =>
    Ok.pure trivial

include hr in
theorem defEqList_ok (d : Nat) :
    ∀ (as bs : List Expr), (∀ a ∈ as, Sc N a) → (∀ b ∈ bs, Sc N b) →
      Ok (fun _ => True) (defEqList r₂ E₂ d as bs) (defEqList r₁ E₁ d as bs)
  | [], [], _, _ => Ok.pure trivial
  | a :: as, b :: bs, has, hbs => by
    simp only [defEqList]
    refine Ok.bind (hr.defeq d a b (has a (by simp)) (hbs b (by simp))) (fun v _ => ?_)
    cases v
    · exact Ok.pure trivial
    · exact defEqList_ok d as bs (fun x h => has x (by simp [h])) (fun x h => hbs x (by simp [h]))
  | [], _ :: _, _, _ | _ :: _, [], _, _ => Ok.pure trivial

include hr in
theorem iotaIndexOk_ok (d mI rP cnP : Nat) {tyCtor : Expr} {margs idx : List Expr}
    (hty : Sc N tyCtor) (hm : ∀ a ∈ margs, Sc N a) (hi : ∀ a ∈ idx, Sc N a) :
    Ok (fun _ => True) (iotaIndexOk r₂ E₂ d mI rP cnP tyCtor margs idx)
      (iotaIndexOk r₁ E₁ d mI rP cnP tyCtor margs idx) := by
  unfold iotaIndexOk
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  cases hres : piResidual tyCtor margs with
  | none => exact Ok.pure trivial
  | some res =>
    exact defEqList_ok hr d _ _
      (sc_mem_drop (sc_getAppArgs (sc_piResidual hty hm hres))) hi

include hr in
theorem ensureSort_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (fun _ => True) (ensureSort r₂ E₂ d e) (ensureSort r₁ E₁ d e) := by
  unfold ensureSort
  refine Ok.bind (hr.whnf d e he) (fun w _ => ?_)
  cases w <;> first | exact Ok.pure trivial | exact Ok.throw _

include hr in
theorem boolTrueShortcut_ok (d : Nat) {a : Expr} (ha : Sc N a) :
    Ok (fun _ => True) (boolTrueShortcut r₂ d a) (boolTrueShortcut r₁ d a) := by
  unfold boolTrueShortcut
  exact Ok.bind (hr.whnf d a ha) (fun _ _ => Ok.pure trivial)

include H hr in
theorem reduceNat_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (OSc N) (reduceNat r₂ E₂ d e) (reduceNat r₁ E₁ d e) := by
  unfold reduceNat
  split
  · rename_i c a
    have ha : Sc N a := (sc_app.mp he).2
    rw [H.natLitSupported_eq]
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure (fun _ h => by cases h))
    refine Ok.bind (hr.whnf d a ha) (fun w _ => ?_)
    split
    · exact Ok.pure (fun _ h => by cases h; exact sc_lit)
    · exact Ok.pure (fun _ h => by cases h)
  · rename_i c a b
    have hab := sc_app.mp he
    have hc : N c := sc_const.mp (sc_app.mp hab.1).1
    have ha : Sc N a := (sc_app.mp hab.1).2
    have hb : Sc N b := hab.2
    rw [H.natOpStored_eq hc, H.natLitSupported_eq]
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.ite (fun _ => ?_) (fun _ => Ok.pure (fun _ h => by cases h)))
    · refine Ok.bind (hr.whnf d a ha) (fun w _ => ?_)
      split
      · refine Ok.bind (hr.whnf d b hb) (fun w' _ => ?_)
        split
        · exact Ok.pure (fun _ h => sc_natOpResult H h)
        · exact Ok.pure (fun _ h => by cases h)
      · exact Ok.pure (fun _ h => by cases h)
    · refine Ok.bind (hr.whnf d a ha) (fun w _ => ?_)
      split
      · refine Ok.bind (hr.whnf d b hb) (fun w' _ => ?_)
        split
        · exact Ok.throw _
        · exact Ok.pure (fun _ h => by cases h)
      · exact Ok.pure (fun _ h => by cases h)
  · exact Ok.pure (fun _ h => by cases h)

include H hr in
theorem proofIrrel_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (proofIrrel r₂ E₂ d a b) (proofIrrel r₁ E₁ d a b) := by
  unfold proofIrrel
  refine Ok.bind (hr.inferIO d a ha) (fun ta hta => ?_)
  refine Ok.bind (hr.whnf d ta hta) (fun wa _ => ?_)
  rw [H.isUnitLikeTy_eq]
  refine Ok.ite (fun _ => ?_) (fun _ => ?_)
  · refine Ok.bind (hr.inferIO d b hb) (fun tb htb => ?_)
    refine Ok.bind (hr.whnf d tb htb) (fun wb _ => ?_)
    rw [H.isUnitLikeTy_eq]
    exact Ok.ite (fun _ => Ok.pure trivial) (fun _ => Ok.pure trivial)
  · refine Ok.bind (hr.inferIO d ta hta) (fun tta htta => ?_)
    refine Ok.bind (hr.whnf d tta htta) (fun w _ => ?_)
    split
    · refine Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial)) (fun okA _ => ?_)
      refine Ok.bind (hr.inferIO d b hb) (fun tb htb => ?_)
      refine Ok.bind (hr.inferIO d tb htb) (fun ttb httb => ?_)
      refine Ok.bind (hr.whnf d ttb httb) (fun w' _ => ?_)
      split
      · refine Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial)) (fun okB _ => ?_)
        exact Ok.pure trivial
      · exact Ok.pure trivial
    · exact Ok.pure trivial

include H hr in
theorem propIrrel_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (propIrrel r₂ E₂ d a b) (propIrrel r₁ E₁ d a b) := by
  unfold propIrrel
  rw [H.notProofFast_eq ha, H.notProofFast_eq hb, H.isProofFast_eq ha, H.isProofFast_eq hb]
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_))
  refine Ok.bind (hr.inferIO d a ha) (fun ta hta => ?_)
  refine Ok.bind (hr.inferIO d ta hta) (fun tta htta => ?_)
  refine Ok.bind (hr.whnf d tta htta) (fun w _ => ?_)
  split
  · refine Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial)) (fun okA _ => ?_)
    refine Ok.bind (hr.inferIO d b hb) (fun tb htb => ?_)
    refine Ok.bind (hr.inferIO d tb htb) (fun ttb httb => ?_)
    refine Ok.bind (hr.whnf d ttb httb) (fun w' _ => ?_)
    split
    · refine Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial)) (fun okB _ => ?_)
      exact Ok.pure trivial
    · exact Ok.pure trivial
  · exact Ok.pure trivial

include H hr in
theorem structEtaProjCerts_ok (d : Nat) {T : Name} (hT : N T) (us' : List Level)
    {targs : List Expr} {b : Expr} (htargs : ∀ a ∈ targs, Sc N a) (hb : Sc N b)
    (lpsT : List Name) :
    ∀ is : List Nat, Ok (fun _ => True) (structEtaProjCerts r₂ E₂ d T us' targs b lpsT is)
      (structEtaProjCerts r₁ E₁ d T us' targs b lpsT is)
  | [] => Ok.pure trivial
  | i :: rest => by
    simp only [structEtaProjCerts]
    have hpi := H.projFn i hT
    rw [H.find hpi]
    split
    · rename_i cvp _ _ _ hfind
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
      refine Ok.bind (iotaCerts_ok hr d false _ _
        (H.const_type_sc hpi hfind _ _) (sc_mem_append htargs (by simpa using hb)))
        (fun v _ => ?_)
      cases v
      · exact Ok.pure trivial
      · exact structEtaProjCerts_ok d hT us' htargs hb lpsT rest
    · exact Ok.pure trivial

include H hr in
theorem structEtaCertWith_ok (d : Nat) {a b wtb : Expr} (ha : Sc N a) (hb : Sc N b)
    (hw : Sc N wtb) :
    Ok (fun _ => True) (structEtaCertWith mode r₂ E₂ d a b wtb)
      (structEtaCertWith mode r₁ E₁ d a b wtb) := by
  unfold structEtaCertWith
  have hargs := sc_getAppArgs ha
  have hwargs := sc_getAppArgs hw
  split
  · rename_i c us hfn
    have hc := head_const_N ha hfn
    rw [H.find hc]
    split
    · rename_i cvc cnP cnF hfc
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
      split
      · rename_i T us' hfnT
        have hT := head_const_N hw hfnT
        rw [H.find hT]
        split
        · rename_i cvT caps hfT
          rw [H.towerSlotsAll_eq hT, H.recSlotsAll_eq hT, H.etaProjs_eq hT]
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
          refine Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial)) (fun v₁ _ => ?_)
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
          refine Ok.bind (iotaCerts_ok hr d false _ _ (H.const_type_sc hT hfT _ _) hwargs)
            (fun v₂ _ => ?_)
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
          refine Ok.bind (?_ : Ok (fun _ => True) _ _) (fun v₃ _ => ?_)
          · exact Ok.ite (fun _ => Ok.pure trivial)
              (fun _ => structEtaProjCerts_ok H hr d hT us' hwargs hb _ _)
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
          refine Ok.bind (defEqList_ok hr d _ _ (sc_mem_take hargs) hwargs) (fun v₄ _ => ?_)
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
          have hprojs := H.etaProjs_sc hT (us := us') (nF := caps.etaFields) hwargs hb
          refine Ok.bind (?_ : Ok (fun _ => True) _ _) (fun v₅ _ => ?_)
          · exact Ok.ite (fun _ => iotaCerts_ok hr d false _ _ (H.const_type_sc hc hfc _ _)
                (sc_mem_append hwargs hprojs))
              (fun _ => Ok.pure trivial)
          refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
          exact defEqList_ok hr d _ _ (sc_mem_drop hargs) hprojs
        · exact Ok.pure trivial
      · exact Ok.pure trivial
    · exact Ok.pure trivial
  · exact Ok.pure trivial

include H hr in
theorem structEtaCert_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (structEtaCert mode r₂ E₂ d a b) (structEtaCert mode r₁ E₁ d a b) := by
  unfold structEtaCert
  rw [H.etaCtorShape_eq ha]
  refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
  refine Ok.bind (hr.inferIO d b hb) (fun tb htb => ?_)
  refine Ok.bind (hr.whnf d tb htb) (fun wtb hwtb => ?_)
  exact structEtaCertWith_ok H hr mode d ha hb hwtb

include H hr in
theorem structUnitCert_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (structUnitCert r₂ E₂ d a b) (structUnitCert r₁ E₁ d a b) := by
  unfold structUnitCert
  refine Ok.bind (hr.inferIO d a ha) (fun ta hta => ?_)
  refine Ok.bind (hr.whnf d ta hta) (fun wta hwta => ?_)
  split
  · rename_i T us' hfnT
    have hT := head_const_N hwta hfnT
    rw [H.find hT]
    split
    · rename_i cvT caps hfT
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
      refine Ok.bind (hr.inferIO d b hb) (fun tb htb => ?_)
      refine Ok.bind (hr.whnf d tb htb) (fun wtb hwtb => ?_)
      refine Ok.bind (hr.defeq d wta wtb hwta hwtb) (fun v _ => ?_)
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
      exact iotaCerts_ok hr d false _ _ (H.const_type_sc hT hfT _ _) (sc_getAppArgs hwta)
    · exact Ok.pure trivial
  · exact Ok.pure trivial

include hr in
theorem etaCert_ok (d : Nat) {ty₁ body₁ b : Expr} (m₁ : BinderMeta) (hty : Sc N ty₁)
    (hbody : Sc N body₁) (hb : Sc N b) :
    Ok (fun _ => True) (etaCert mode r₂ E₂ d ty₁ body₁ m₁ b)
      (etaCert mode r₁ E₁ d ty₁ body₁ m₁ b) := by
  unfold etaCert
  refine Ok.bind (hr.inferIO d b hb) (fun tb htb => ?_)
  refine Ok.bind (hr.whnf d tb htb) (fun w hw => ?_)
  split
  · rename_i ty₂ _ m₂
    have hty₂ := (sc_forallE.mp hw).1
    refine Ok.bind (hr.defeq d ty₂ ty₁ hty₂ hty) (fun v _ => ?_)
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
    have hfv : Sc N (Expr.fvar d ty₁) := sc_fvar.mpr hty
    refine Ok.bind (hr.defeq (d + 1) _ _ (sc_instantiate1' hbody hfv)
      (sc_app.mpr ⟨hb, hfv⟩)) (fun v' _ => ?_)
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
    refine Ok.ite (fun _ => Ok.throw _) (fun _ => Ok.pure trivial)
  · exact Ok.pure trivial

include H hr in
theorem stuckIrrel_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (stuckIrrel mode r₂ E₂ d a b) (stuckIrrel mode r₁ E₁ d a b) := by
  unfold stuckIrrel
  refine Ok.bind (structEtaCert_ok H hr mode d ha hb) (fun v _ => ?_)
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  refine Ok.bind (structEtaCert_ok H hr mode d hb ha) (fun v' _ => ?_)
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  refine Ok.bind (structUnitCert_ok H hr d ha hb) (fun v'' _ => ?_)
  exact Ok.ite (fun _ => Ok.pure trivial) (fun _ => proofIrrel_ok H hr d ha hb)

include H hr in
theorem projCert_ok (d : Nat) (lic : Bool) {c : Name} (hc : N c) (us : List Level)
    {args : List Expr} (hargs : ∀ a ∈ args, Sc N a) :
    Ok (fun _ => True) (projCert r₂ E₂ d lic c us args) (projCert r₁ E₁ d lic c us args) := by
  unfold projCert
  rw [H.find hc]
  split
  · rename_i cvC _ _ hf
    exact iotaCerts_ok hr d lic _ _ (H.const_type_sc hc hf _ _) hargs
  · exact Ok.pure trivial

include H hr in
theorem projCertAt_ok (d : Nat) (verified lic : Bool) {c : Name} (hc : N c) (us : List Level)
    {args : List Expr} (hargs : ∀ a ∈ args, Sc N a) :
    Ok (fun _ => True) (projCertAt r₂ E₂ d verified lic c us args)
      (projCertAt r₁ E₁ d verified lic c us args) := by
  unfold projCertAt
  exact Ok.ite (fun _ => projCert_ok H hr d lic hc us hargs) (fun _ => Ok.pure trivial)

include H hr in
theorem litMajorToCtor_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (litMajorToCtor r₂ E₂ d e) (litMajorToCtor r₁ E₁ d e) := by
  unfold litMajorToCtor
  split
  · rw [H.strLitSupported_eq]
    exact Ok.ite (fun _ => hr.whnf d _ (sc_strLitToConstructor H _)) (fun _ => Ok.pure sc_lit)
  · rw [H.litToCtorIfNat_eq]; exact Ok.pure (H.litToCtorIfNat_sc he)

include H hr in
theorem projLitToCtor_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (projLitToCtor r₂ E₂ d e) (projLitToCtor r₁ E₁ d e) := by
  unfold projLitToCtor
  split
  · rw [H.strLitSupported_eq]
    exact Ok.ite (fun _ => hr.whnf d _ (sc_strLitToConstructor H _)) (fun _ => Ok.pure sc_lit)
  · exact Ok.pure he

include hr in
theorem defeqSpine_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (defeqSpine r₂ E₂ d a b) (defeqSpine r₁ E₁ d a b) := by
  unfold defeqSpine
  split
  · split
    · refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial)
      split
      · exact defEqList_ok hr d _ _ (sc_getAppArgs ha) (sc_getAppArgs hb)
      · exact Ok.pure trivial
    · exact Ok.pure trivial
  · exact Ok.pure trivial

end ConLeche.EnvExt
