module

public import ConLeche.Verify.EnvExt.Iota

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
  · rw [H.natLitSupported_eq]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr H.fixed_nat)) (fun _ => Ok.throw _)
  · rw [H.strLitSupported_eq]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr H.fixed_string)) (fun _ => Ok.throw _)
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
  · rw [H.natLitSupported_eq]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr H.fixed_nat)) (fun _ => Ok.throw _)
  · rw [H.strLitSupported_eq]
    exact Ok.ite (fun _ => Ok.pure (sc_const.mpr H.fixed_string)) (fun _ => Ok.throw _)
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

end ConLeche.EnvExt
