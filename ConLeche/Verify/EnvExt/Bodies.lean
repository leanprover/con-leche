module

public import ConLeche.Verify.EnvExt.Ok
import ConLeche.Verify.EnvExt.Iota
import ConLeche.Verify.EnvExt.Certs
import ConLeche.Verify.EnvExt.Reads
import ConLeche.Verify.EnvExt.ScOps

public section

/-!
# Env extension, part 7: the knot's bodies

Each body of the knot, at a pair of records in the currency (`RecOK`),
is in the currency: same run at `E₂` as at `E₁`, scoped results.
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop} {E₁ E₂ : Env} (H : Agree N E₁ E₂)
  {r₁ r₂ : CoreFns CheckM} (hr : RecOK N r₁ r₂) (mode : CheckMode)

include H hr in
theorem whnfCoreBody_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (whnfCoreBody mode r₂ E₂ d e) (whnfCoreBody mode r₁ E₁ d e) := by
  unfold whnfCoreBody
  split
  · exact Ok.pure he
  · exact Ok.pure he
  · exact Ok.pure he
  · exact Ok.pure he
  · exact Ok.pure he
  · exact Ok.pure he
  · rename_i f a
    have hf := (sc_app.mp he).1
    have ha := (sc_app.mp he).2
    refine Ok.bind (hr.whnfCore d f hf) (fun f' hf' => ?_)
    split
    · rename_i ty body mb
      have hlam := sc_lam.mp hf'
      refine Ok.ite (fun _ => hr.whnfCore d _ (sc_instantiate1' hlam.2 ha)) (fun _ => ?_)
      refine Ok.bind (hr.inferIO d a ha) (fun ta hta => ?_)
      refine Ok.bind (hr.defeq d ta ty hta hlam.1) (fun v _ => ?_)
      exact Ok.ite (fun _ => hr.whnfCore d _ (sc_instantiate1' hlam.2 ha))
        (fun _ => Ok.pure (sc_app.mpr ⟨hf', ha⟩))
    · refine Ok.bind (iotaRec_ok H hr mode d (sc_app.mpr ⟨hf', ha⟩)) (fun o ho => ?_)
      split
      · rename_i e''; exact hr.whnfCore d e'' (ho e'' rfl)
      · exact Ok.pure (sc_app.mpr ⟨hf', ha⟩)
  · rename_i sn i pe
    have hsn := (sc_proj.mp he).1
    have hpe := (sc_proj.mp he).2
    refine Ok.bind (hr.whnf d pe hpe) (fun e₁ he₁ => ?_)
    refine Ok.bind (projLitToCtor_ok H hr d he₁) (fun e' he' => ?_)
    rw [H.findProj? hsn]
    split
    · rename_i entry hentry
      split
      · rename_i c us hfn
        have hc := head_const_N he' hfn
        refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure (sc_proj.mpr ⟨hsn, he'⟩))
        refine Ok.bind (projCertAt_ok H hr d _ _ hc us (sc_getAppArgs he')) (fun v _ => ?_)
        exact Ok.ite (fun _ => hr.whnfCore d _ (sc_getD (sc_getAppArgs he') sc_bvar))
          (fun _ => Ok.pure (sc_proj.mpr ⟨hsn, he'⟩))
      · exact Ok.pure (sc_proj.mpr ⟨hsn, he'⟩)
    · exact Ok.pure (sc_proj.mpr ⟨hsn, he'⟩)
  · exact Ok.throw _
  · exact Ok.throw _

include H hr in
theorem whnfStep_ok (d : Nat) {k₁ k₂ : Expr → CheckM Expr}
    (hk : ∀ e, Sc N e → Ok (Sc N) (k₂ e) (k₁ e)) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (whnfStep r₂ E₂ d k₂ e) (whnfStep r₁ E₁ d k₁ e) := by
  unfold whnfStep
  refine Ok.bind (hr.whnfCore d e he) (fun e₁ he₁ => ?_)
  refine Ok.bind (reduceNat_ok H hr d he₁) (fun o ho => ?_)
  split
  · rename_i e₂; exact hk e₂ (ho e₂ rfl)
  · rw [H.unfoldDefinition_eq he₁]
    split
    · rename_i e₂ h₂; exact hk e₂ (H.unfoldDefinition_sc he₁ h₂)
    · exact Ok.pure he₁

include H hr in
theorem whnfLoop_ok (d : Nat) : ∀ (n : Nat) {e : Expr}, Sc N e →
    Ok (Sc N) (whnfLoop r₂ E₂ d n e) (whnfLoop r₁ E₁ d n e)
  | 0, _, _ => Ok.throw _
  | n + 1, _, he => by
    simp only [whnfLoop]
    exact whnfStep_ok H hr d (fun e' he' => whnfLoop_ok d n he') he

include H hr in
theorem whnfBody_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (whnfBody r₂ E₂ d e) (whnfBody r₁ E₁ d e) :=
  whnfLoop_ok H hr d _ he

include H hr in
theorem inferBody_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (inferBody mode r₂ E₂ d e) (inferBody mode r₁ E₁ d e) := by
  unfold inferBody
  split
  · exact Ok.pure sc_sort
  · rename_i idx ty
    exact Ok.ite (fun _ => Ok.pure (sc_fvar.mp he)) (fun _ => Ok.throw _)
  · rename_i n us
    have hn := sc_const.mp he
    rw [H.find hn]
    split
    · exact Ok.throw _
    · rename_i ci hf
      dsimp only
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.throw_bind _)
      exact Ok.ite (fun _ => Ok.pure (H.const_type_sc hn hf _ _)) (fun _ => Ok.throw_bind _)
  · rw [H.natLitSupported_eq (sc_lit.mp he)]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr (sc_lit.mp he _ (by simp [litNames, natLitNames]))))
      (fun _ => Ok.throw _)
  · rw [H.strLitSupported_eq (sc_lit.mp he)]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr (sc_lit.mp he _ (by simp [litNames, litGuardNames]))))
      (fun _ => Ok.throw _)
  · rename_i ty body mb
    have h := sc_forallE.mp he
    refine Ok.bind (hr.infer d ty h.1) (fun tt htt => ?_)
    refine Ok.bind (hr.whnf d tt htt) (fun w _ => ?_)
    split
    · have hfv : Sc N (Expr.fvar d ty) := sc_fvar.mpr h.1
      refine Ok.bind (hr.infer (d + 1) _ (sc_instantiate1' h.2 hfv)) (fun tb htb => ?_)
      refine Ok.bind (ensureSort_ok hr (d + 1) htb) (fun v _ => ?_)
      dsimp only
      exact Ok.ite (fun _ => Ok.ite (fun _ => Ok.pure sc_sort) (fun _ => Ok.throw_bind _))
        (fun _ => Ok.pure sc_sort)
    · exact Ok.throw _
  · rename_i ty body mb
    have h := sc_lam.mp he
    refine Ok.bind (hr.infer d ty h.1) (fun tt htt => ?_)
    refine Ok.bind (hr.whnf d tt htt) (fun w _ => ?_)
    split
    · have hfv : Sc N (Expr.fvar d ty) := sc_fvar.mpr h.1
      refine Ok.bind (hr.infer (d + 1) _ (sc_instantiate1' h.2 hfv)) (fun bt hbt => ?_)
      have hres : Sc N (Expr.forallE ty (bt.abstract1 d) mb) :=
        sc_forallE.mpr ⟨h.1, sc_abstract1 _ _ _ hbt⟩
      dsimp only
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hres)
      split
      · exact Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _)
      · refine Ok.bind (hr.inferIO (d + 1) bt hbt) (fun btt hbtt => ?_)
        refine Ok.bind (ensureSort_ok hr (d + 1) hbtt) (fun vb _ => ?_)
        exact Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _)
    · exact Ok.throw _
  · rename_i f a
    have h := sc_app.mp he
    refine Ok.bind (hr.infer d f h.1) (fun tf htf => ?_)
    refine Ok.bind (hr.whnf d tf htf) (fun w hw => ?_)
    split
    · rename_i ty body _
      have hpi := sc_forallE.mp hw
      refine Ok.bind (hr.infer d a h.2) (fun ta hta => ?_)
      refine Ok.bind (hr.defeq d ta ty hta hpi.1) (fun v _ => ?_)
      dsimp only
      exact Ok.ite (fun _ => Ok.pure (sc_instantiate1' hpi.2 h.2)) (fun _ => Ok.throw_bind _)
    · exact Ok.throw _
  · rename_i sn i pe
    have h := sc_proj.mp he
    refine Ok.bind (hr.infer d pe h.2) (fun tp htp => ?_)
    refine Ok.bind (hr.whnf d tp htp) (fun te hte => ?_)
    split
    · rename_i T us hfn
      have hT := head_const_N hte hfn
      rw [H.findProj? hT]
      split
      · rename_i entry hentry
        have hres := H.typeAt_sc hT hentry us (sc_getAppArgs hte) h.2
        refine Ok.ite (fun _ => ?_) (fun _ => Ok.throw _)
        dsimp only
        exact Ok.ite (fun _ => Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _))
          (fun _ => Ok.pure hres)
      · exact Ok.throw _
    · exact Ok.throw _
  · exact Ok.throw _
  · exact Ok.throw _

include H hr in
theorem inferBodyIO_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (inferBodyIO mode r₂ E₂ d e) (inferBodyIO mode r₁ E₁ d e) := by
  unfold inferBodyIO
  split
  · exact Ok.pure sc_sort
  · rename_i idx ty
    exact Ok.ite (fun _ => Ok.pure (sc_fvar.mp he)) (fun _ => Ok.throw _)
  · rename_i n us
    have hn := sc_const.mp he
    rw [H.find hn]
    split
    · exact Ok.throw _
    · rename_i ci hf
      dsimp only
      refine Ok.ite (fun _ => ?_) (fun _ => Ok.throw_bind _)
      exact Ok.ite (fun _ => Ok.pure (H.const_type_sc hn hf _ _)) (fun _ => Ok.throw_bind _)
  · rw [H.natLitSupported_eq (sc_lit.mp he)]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr (sc_lit.mp he _ (by simp [litNames, natLitNames]))))
      (fun _ => Ok.throw _)
  · rw [H.strLitSupported_eq (sc_lit.mp he)]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr (sc_lit.mp he _ (by simp [litNames, litGuardNames]))))
      (fun _ => Ok.throw _)
  · rename_i ty body mb
    have h := sc_forallE.mp he
    refine Ok.bind (hr.infer d ty h.1) (fun tt htt => ?_)
    refine Ok.bind (hr.whnf d tt htt) (fun w _ => ?_)
    split
    · have hfv : Sc N (Expr.fvar d ty) := sc_fvar.mpr h.1
      refine Ok.bind (hr.infer (d + 1) _ (sc_instantiate1' h.2 hfv)) (fun tb htb => ?_)
      refine Ok.bind (ensureSort_ok hr (d + 1) htb) (fun v _ => ?_)
      dsimp only
      exact Ok.ite (fun _ => Ok.ite (fun _ => Ok.pure sc_sort) (fun _ => Ok.throw_bind _))
        (fun _ => Ok.pure sc_sort)
    · exact Ok.throw _
  · rename_i ty body mb
    have h := sc_lam.mp he
    have hfv : Sc N (Expr.fvar d ty) := sc_fvar.mpr h.1
    refine Ok.bind (hr.infer (d + 1) _ (sc_instantiate1' h.2 hfv)) (fun bt hbt => ?_)
    have hres : Sc N (Expr.forallE ty (bt.abstract1 d) mb) :=
      sc_forallE.mpr ⟨h.1, sc_abstract1 _ _ _ hbt⟩
    dsimp only
    refine Ok.ite (fun _ => ?_) (fun _ => Ok.pure hres)
    split
    · exact Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _)
    · refine Ok.bind (hr.infer (d + 1) bt hbt) (fun btt hbtt => ?_)
      refine Ok.bind (ensureSort_ok hr (d + 1) hbtt) (fun vb _ => ?_)
      exact Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _)
  · rename_i f a
    have h := sc_app.mp he
    refine Ok.bind (hr.infer d f h.1) (fun tf htf => ?_)
    refine Ok.bind (hr.whnf d tf htf) (fun w hw => ?_)
    split
    · rename_i ty body _
      have hpi := sc_forallE.mp hw
      have hres := sc_instantiate1' hpi.2 h.2 (d := 0)
      dsimp only
      refine Ok.ite (fun _ => Ok.pure hres) (fun _ => ?_)
      refine Ok.bind (hr.infer d a h.2) (fun ta hta => ?_)
      refine Ok.bind (hr.defeq d ta ty hta hpi.1) (fun v _ => ?_)
      exact Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _)
    · exact Ok.throw _
  · rename_i sn i pe
    have h := sc_proj.mp he
    refine Ok.bind (hr.infer d pe h.2) (fun tp htp => ?_)
    refine Ok.bind (hr.whnf d tp htp) (fun te hte => ?_)
    split
    · rename_i T us hfn
      have hT := head_const_N hte hfn
      rw [H.findProj? hT]
      split
      · rename_i entry hentry
        have hres := H.typeAt_sc hT hentry us (sc_getAppArgs hte) h.2
        refine Ok.ite (fun _ => ?_) (fun _ => Ok.throw _)
        dsimp only
        exact Ok.ite (fun _ => Ok.ite (fun _ => Ok.pure hres) (fun _ => Ok.throw_bind _))
          (fun _ => Ok.pure hres)
      · exact Ok.throw _
    · exact Ok.throw _
  · exact Ok.throw _
  · exact Ok.throw _

include H hr in
theorem defeqStep_ok (d : Nat) {k₁ k₂ : Bool → Expr → Expr → CheckM Bool}
    (hk : ∀ pi a b, Sc N a → Sc N b → Ok (fun _ => True) (k₂ pi a b) (k₁ pi a b))
    (pi : Bool) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (defeqStep mode r₂ E₂ d k₂ pi a b) (defeqStep mode r₁ E₁ d k₁ pi a b) := by
  unfold defeqStep
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  refine Ok.bind (Ok.ite (fun _ => boolTrueShortcut_ok hr d ha) (fun _ => Ok.pure trivial))
    (fun _ _ => ?_)
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  refine Ok.bind (hr.whnfCore d a ha) (fun a' ha' => ?_)
  refine Ok.bind (hr.whnfCore d b hb) (fun b' hb' => ?_)
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  refine Ok.bind (Ok.ite (fun _ => propIrrel_ok H hr d ha' hb') (fun _ => Ok.pure trivial))
    (fun _ _ => ?_)
  refine Ok.ite (fun _ => Ok.pure trivial) (fun _ => ?_)
  refine Ok.bind (Ok.ite (fun _ => reduceNat_ok H hr d ha')
    (fun _ => Ok.pure (fun _ h => by cases h))) (fun o₁ ho₁ => ?_)
  split
  · rename_i a₂; exact hk _ _ _ (ho₁ a₂ rfl) hb'
  refine Ok.bind (Ok.ite (fun _ => reduceNat_ok H hr d hb')
    (fun _ => Ok.pure (fun _ h => by cases h))) (fun o₂ ho₂ => ?_)
  split
  · rename_i b₂; exact hk _ _ _ ha' (ho₂ b₂ rfl)
  rw [H.unfoldableHead_eq ha', H.unfoldableHead_eq hb', H.unfoldDefinition_eq ha',
    H.unfoldDefinition_eq hb', H.headHint_eq ha', H.headHint_eq hb']
  have hu₁ : OSc N (unfoldDefinition E₁ a') := fun x h => H.unfoldDefinition_sc ha' h
  have hu₂ : OSc N (unfoldDefinition E₁ b') := fun x h => H.unfoldDefinition_sc hb' h
  have one₁ : ∀ (b₀ : Expr), Sc N b₀ →
      Ok (fun _ => True)
        (match unfoldDefinition E₁ a' with | some a₂ => k₂ false a₂ b₀ | none => pure false)
        (match unfoldDefinition E₁ a' with | some a₂ => k₁ false a₂ b₀ | none => pure false) := by
    intro b₀ hb₀
    cases h : unfoldDefinition E₁ a' with
    | none => exact Ok.pure trivial
    | some a₂ => exact hk _ _ _ (hu₁ a₂ h) hb₀
  have one₂ : ∀ (a₀ : Expr), Sc N a₀ →
      Ok (fun _ => True)
        (match unfoldDefinition E₁ b' with | some b₂ => k₂ false a₀ b₂ | none => pure false)
        (match unfoldDefinition E₁ b' with | some b₂ => k₁ false a₀ b₂ | none => pure false) := by
    intro a₀ ha₀
    cases h : unfoldDefinition E₁ b' with
    | none => exact Ok.pure trivial
    | some b₂ => exact hk _ _ _ ha₀ (hu₂ b₂ h)
  have both : Ok (fun _ => True)
      (match unfoldDefinition E₁ a', unfoldDefinition E₁ b' with
        | some a₂, some b₂ => k₂ false a₂ b₂ | _, _ => pure false)
      (match unfoldDefinition E₁ a', unfoldDefinition E₁ b' with
        | some a₂, some b₂ => k₁ false a₂ b₂ | _, _ => pure false) := by
    cases h₁ : unfoldDefinition E₁ a' with
    | none => exact Ok.pure trivial
    | some a₂ =>
      cases h₂ : unfoldDefinition E₁ b' with
      | none => exact Ok.pure trivial
      | some b₂ => exact hk _ _ _ (hu₁ a₂ h₁) (hu₂ b₂ h₂)
  split
  · exact one₁ b' hb'
  · exact one₂ a' ha'
  · dsimp only
    refine Ok.ite (fun _ => one₁ b' hb') (fun _ => Ok.ite (fun _ => one₂ a' ha')
      (fun _ => Ok.ite (fun _ => ?_) (fun _ => both)))
    refine Ok.bind (defeqSpine_ok hr d ha' hb') (fun v _ => ?_)
    exact Ok.ite (fun _ => Ok.pure trivial) (fun _ => both)
  · split
    all_goals first
      | exact Ok.liftFueled _ _ (fun _ _ => trivial)
      | exact Ok.pure trivial
      | exact stuckIrrel_ok H hr mode d ha' hb'
      | exact Ok.ite (fun _ => Ok.pure trivial) (fun _ => stuckIrrel_ok H hr mode d ha' hb')
      | skip
    case h_5 =>
      split
      · exact Ok.ite (fun _ => hr.defeq d _ _ (sc_lit.mpr (sc_lit.mp ha')) (sc_app.mp hb').2)
          (fun _ => stuckIrrel_ok H hr mode d ha' hb')
      · exact stuckIrrel_ok H hr mode d ha' hb'
    case h_6 =>
      split
      · exact Ok.ite (fun _ => hr.defeq d _ _ (sc_app.mp ha').2 (sc_lit.mpr (sc_lit.mp hb')))
          (fun _ => stuckIrrel_ok H hr mode d ha' hb')
      · exact stuckIrrel_ok H hr mode d ha' hb'
    case h_7 =>
      rw [H.strLitSupported_eq (sc_lit.mp ha')]
      exact Ok.ite (fun _ => hr.defeq d _ _ (sc_strLitToConstructor _ (sc_lit.mp ha')) hb')
        (fun _ => stuckIrrel_ok H hr mode d ha' hb')
    case h_8 =>
      rw [H.strLitSupported_eq (sc_lit.mp hb')]
      exact Ok.ite (fun _ => hr.defeq d _ _ ha' (sc_strLitToConstructor _ (sc_lit.mp hb')))
        (fun _ => stuckIrrel_ok H hr mode d ha' hb')
    case h_10 =>
      exact Ok.ite (fun _ => Ok.bind (Ok.liftFueled _ _ (fun _ _ => trivial))
          (fun _ _ => Ok.ite (fun _ => Ok.pure trivial) (fun _ => stuckIrrel_ok H hr mode d ha' hb')))
        (fun _ => stuckIrrel_ok H hr mode d ha' hb')
    case h_13 =>
      exact Ok.ite (fun _ => Ok.bind (hr.defeq d _ _ (sc_getAppFn ha') (sc_getAppFn hb'))
          (fun _ _ => Ok.ite (fun _ => Ok.bind
            (defEqList_ok hr d _ _ (sc_getAppArgs ha') (sc_getAppArgs hb'))
            (fun _ _ => Ok.ite (fun _ => Ok.pure trivial)
              (fun _ => stuckIrrel_ok H hr mode d ha' hb')))
            (fun _ => stuckIrrel_ok H hr mode d ha' hb')))
        (fun _ => stuckIrrel_ok H hr mode d ha' hb')
    case h_14 =>
      exact Ok.ite (fun _ => Ok.bind (hr.defeq d _ _ (sc_proj.mp ha').2 (sc_proj.mp hb').2)
          (fun _ _ => Ok.ite (fun _ => Ok.pure trivial)
            (fun _ => stuckIrrel_ok H hr mode d ha' hb')))
        (fun _ => stuckIrrel_ok H hr mode d ha' hb')
    case h_15 =>
      exact Ok.bind (etaCert_ok hr mode d _ (sc_lam.mp ha').1 (sc_lam.mp ha').2 hb')
        (fun _ _ => Ok.ite (fun _ => Ok.pure trivial) (fun _ => stuckIrrel_ok H hr mode d ha' hb'))
    case h_16 =>
      exact Ok.bind (etaCert_ok hr mode d _ (sc_lam.mp hb').1 (sc_lam.mp hb').2 ha')
        (fun _ _ => Ok.ite (fun _ => Ok.pure trivial) (fun _ => stuckIrrel_ok H hr mode d ha' hb'))
    case h_11 =>
      have h₁ := sc_forallE.mp ha'
      have h₂ := sc_forallE.mp hb'
      have hfv : Sc N (Expr.fvar d _) := sc_fvar.mpr h₂.1
      refine Ok.bind (hr.defeq d _ _ h₁.1 h₂.1) (fun _ _ => Ok.ite (fun _ => ?_)
        (fun _ => Ok.pure trivial))
      refine Ok.bind (hr.defeq (d + 1) _ _ (sc_instantiate1' h₁.2 hfv)
        (sc_instantiate1' h₂.2 hfv)) (fun _ _ => Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial))
      dsimp only
      exact Ok.ite (fun _ => Ok.throw_bind _) (fun _ => Ok.pure trivial)
    case h_12 =>
      have h₁ := sc_lam.mp ha'
      have h₂ := sc_lam.mp hb'
      have hfv : Sc N (Expr.fvar d _) := sc_fvar.mpr h₂.1
      refine Ok.bind (hr.defeq d _ _ h₁.1 h₂.1) (fun _ _ => Ok.ite (fun _ => ?_)
        (fun _ => Ok.pure trivial))
      refine Ok.bind (hr.defeq (d + 1) _ _ (sc_instantiate1' h₁.2 hfv)
        (sc_instantiate1' h₂.2 hfv)) (fun _ _ => Ok.ite (fun _ => ?_) (fun _ => Ok.pure trivial))
      dsimp only
      exact Ok.ite (fun _ => Ok.throw_bind _) (fun _ => Ok.pure trivial)

include H hr in
theorem defeqLoop_ok (d : Nat) : ∀ (n : Nat) (pi : Bool) {a b : Expr}, Sc N a → Sc N b →
    Ok (fun _ => True) (defeqLoop mode r₂ E₂ d n pi a b) (defeqLoop mode r₁ E₁ d n pi a b)
  | 0, _, _, _, _, _ => Ok.throw _
  | n + 1, pi, _, _, ha, hb => by
    simp only [defeqLoop]
    exact defeqStep_ok H hr mode d (fun pi' _ _ ha' hb' => defeqLoop_ok d n pi' ha' hb') pi ha hb

include H hr in
theorem defeqBody_ok (d : Nat) {a b : Expr} (ha : Sc N a) (hb : Sc N b) :
    Ok (fun _ => True) (defeqBody mode r₂ E₂ d a b) (defeqBody mode r₁ E₁ d a b) :=
  defeqLoop_ok H hr mode d _ _ ha hb

include H hr in
theorem annotPwPi_ok (d : Nat) {body' : Expr} (hb : Sc N body') :
    Ok (fun _ => True) (annotPwPi r₂ E₂ d body') (annotPwPi r₁ E₁ d body') := by
  unfold annotPwPi
  rw [H.typeSortPW_eq hb]
  split
  · exact Ok.pure trivial
  · refine Ok.bind (hr.inferIO d body' hb) (fun t ht => ?_)
    exact Ok.bind (ensureSort_ok hr d ht) (fun _ _ => Ok.pure trivial)

include H hr in
theorem annotPwLam_ok (d : Nat) {body' : Expr} (hb : Sc N body') :
    Ok (fun _ => True) (annotPwLam r₂ E₂ d body') (annotPwLam r₁ E₁ d body') := by
  unfold annotPwLam
  rw [H.proofPW_eq hb]
  split
  · exact Ok.pure trivial
  · refine Ok.bind (hr.inferIO d body' hb) (fun bt hbt => ?_)
    refine Ok.bind (hr.inferIO d bt hbt) (fun t ht => ?_)
    exact Ok.bind (ensureSort_ok hr d ht) (fun _ _ => Ok.pure trivial)

include H hr in
theorem annotateBody_ok (d : Nat) {e : Expr} (he : Sc N e) :
    Ok (Sc N) (annotateBody r₂ E₂ d e) (annotateBody r₁ E₁ d e) := by
  unfold annotateBody
  split
  · exact Ok.pure he
  · exact Ok.ite (fun _ => Ok.pure he) (fun _ => Ok.throw _)
  · exact Ok.pure he
  · exact Ok.pure he
  · rw [H.natLitSupported_eq (sc_lit.mp he)]
    exact Ok.ite (fun _ => Ok.pure he) (fun _ => Ok.throw _)
  · rw [H.strLitSupported_eq (sc_lit.mp he)]
    exact Ok.ite (fun _ => Ok.pure he) (fun _ => Ok.throw _)
  · have h := sc_app.mp he
    refine Ok.bind (hr.annotate d _ h.1) (fun f' hf' => ?_)
    refine Ok.bind (hr.annotate d _ h.2) (fun a' ha' => ?_)
    exact Ok.pure (sc_app.mpr ⟨hf', ha'⟩)
  · have h := sc_forallE.mp he
    refine Ok.bind (hr.annotate d _ h.1) (fun ty' hty' => ?_)
    refine Ok.bind (hr.annotate (d + 1) _ (sc_instantiate1' h.2 (sc_fvar.mpr hty')))
      (fun body' hbody' => ?_)
    dsimp only
    refine Ok.ite (fun _ => Ok.bind (annotPwPi_ok H hr (d + 1) hbody') (fun _ _ => ?_))
      (fun _ => Ok.bind (Ok.pure (P := fun _ => True) trivial) (fun _ _ => ?_)) <;>
    exact Ok.pure (sc_forallE.mpr ⟨hty', sc_abstract1 _ _ _ hbody'⟩)
  · have h := sc_lam.mp he
    refine Ok.bind (hr.annotate d _ h.1) (fun ty' hty' => ?_)
    refine Ok.bind (hr.annotate (d + 1) _ (sc_instantiate1' h.2 (sc_fvar.mpr hty')))
      (fun body' hbody' => ?_)
    dsimp only
    refine Ok.ite (fun _ => Ok.bind (annotPwLam_ok H hr (d + 1) hbody') (fun _ _ => ?_))
      (fun _ => Ok.bind (Ok.pure (P := fun _ => True) trivial) (fun _ _ => ?_)) <;>
    exact Ok.pure (sc_lam.mpr ⟨hty', sc_abstract1 _ _ _ hbody'⟩)
  · have h := sc_letE.mp he
    refine Ok.bind (hr.annotate d _ h.1) (fun ty' hty' => ?_)
    refine Ok.bind (hr.infer d _ hty') (fun tt htt => ?_)
    refine Ok.bind (ensureSort_ok hr d htt) (fun _ _ => ?_)
    refine Ok.bind (hr.annotate d _ h.2.1) (fun v' hv' => ?_)
    refine Ok.bind (hr.infer d _ hv') (fun tv htv => ?_)
    refine Ok.bind (hr.defeq d _ _ htv hty') (fun _ _ => ?_)
    dsimp only
    exact Ok.ite (fun _ => hr.annotate d _ (sc_instantiate1' h.2.2 h.2.1))
      (fun _ => Ok.throw_bind _)
  · rename_i sn i pe
    have h := sc_proj.mp he
    refine Ok.bind (hr.annotate d _ h.2) (fun e' he' => ?_)
    refine Ok.bind (hr.inferIO d _ he') (fun t ht => ?_)
    refine Ok.bind (hr.whnf d _ ht) (fun te hte => ?_)
    split
    · rename_i T _ hfn
      have hT := head_const_N hte hfn
      simp only [H.findProj? hT]
      split
      · refine Ok.ite (fun _ => ?_) (fun _ => Ok.throw_bind _)
        exact Ok.ite (fun _ => Ok.pure (sc_proj.mpr ⟨hT, he'⟩)) (fun _ => Ok.throw_bind _)
      · exact Ok.throw _
    · exact Ok.throw _

end ConLeche.EnvExt
