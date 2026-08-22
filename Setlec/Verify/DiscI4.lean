import Setlec.Verify.DiscI3

/-!
# Interned body walks, part 4: head normalization and the whnf loop

Simulation walks for `whnfCoreBodyI` and `whnfBodyI`, mirroring
`whnfCoreBody_disc`/`whnfBody_disc` (`Setlec/Verify/Disc.lean`).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Setlec

open EStore Expr

section Walks

variable {env : Env} {f : Nat}

private theorem whnfCoreBody_unfold (env : Env) (d : Nat) (e : Expr) :
    whnfCoreBody (fueledFns env) env d e =
    (match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body mb => pure (.lam n ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app g' a =>
      (fueledFns env).whnfCore d g' >>= fun f' =>
      match f' with
      | .lam n ty body mb =>
        match mb.cod with
        | some v =>
          if v.isNonZero then
            (fueledFns env).whnfCore d (body.instantiate1 a)
          else
            (fueledFns env).infer d a >>= fun ta =>
            (fueledFns env).defeq d ta ty >>= fun b =>
            if b then
              (fueledFns env).whnfCore d (body.instantiate1 a)
            else pure (.app (.lam n ty body mb) a)
        | none => pure (.app (.lam n ty body mb) a)
      | f' =>
        iotaRec (fueledFns env) env d (.app f' a) >>= fun o =>
        match o with
        | some e'' => (fueledFns env).whnfCore d e''
        | none => pure (.app f' a)
    | .proj sn i pe =>
      (fueledFns env).whnf d pe >>= fun e' =>
      match env.findProj? sn i with
      | some entry =>
        match e'.getAppFn with
        | .const c us =>
          if entry.native ∧ c = entry.ctor ∧ i < entry.numFields ∧
              e'.getAppArgs.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then
            if (Level.subst entry.levelParams us
                entry.structSort).isNonZero then
              (fueledFns env).whnfCore d
                (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))
            else
              projCert (fueledFns env) env d e' i
                (Level.subst entry.levelParams us entry.fieldSort)
                (Level.subst entry.levelParams us entry.structSort)
                entry.numParams >>= fun b =>
              if b then
                (fueledFns env).whnfCore d
                  (e'.getAppArgs.getD (entry.numParams + i) (.bvar 0))
              else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | none => pure (.proj sn i e')
    | .bvar _ | .letE _ _ _ _ =>
      throw (.notImplemented "whnf beyond the supported fragment")) := by
  cases e <;> rfl

/-- The stuck/iota tail of `whnfCoreBodyI`'s application case. -/
private theorem whnfCoreI_iota_tail (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {f' a : EIdx} {f'x xa : Expr} {s₀ : IState}
    (hs : ISOK env s₀) (hf'd : s₀.store.denote f' = some f'x)
    (had : s₀.store.denote a = some xa)
    (hwf' : WScoped d f'x) (hwa : WScoped d xa) :
    SimAt env s₀ (RelE d)
      (internI (.app f' a) >>= fun fa =>
        iotaRecI (coreKnotI (mkFEnv env) f) (mkFEnv env) d fa >>= fun o =>
        match o with
        | some e'' => (coreKnotI (mkFEnv env) f).whnfCore d e''
        | none => pure fa)
      (iotaRec (fueledFns env) env d (.app f'x xa) >>= fun o =>
        match o with
        | some e'' => (fueledFns env).whnfCore d e''
        | none => pure (.app f'x xa)) := by
  have hwapp : WScoped d (Expr.app f'x xa) := by
    simp only [WScoped]
    exact ⟨hwf', hwa⟩
  have hfa : denoteNode s₀.store.denote (ENode.app f' a)
      = some (.app f'x xa) := by
    rw [denoteNode, hf'd, had]; rfl
  refine SimAt.bind_left (internI_eff hs hfa)
    (fun s₁ fa hs₁ hext₁ hQfa => ?_)
  refine SimAt.bind (iotaRecI_sim ih henv hs₁ hQfa hwapp)
    (fun s₂ o ox hs₂ hext₂ hPo => ?_)
  cases o with
  | some e'' =>
    cases ox with
    | none => exact absurd hPo (by simp [RelO])
    | some e''x =>
      obtain ⟨hred, hwred⟩ := hPo
      exact ih.whnfCore hs₂ hred hwred
  | none =>
    cases ox with
    | some e''x => exact absurd hPo (by simp [RelO])
    | none =>
      exact SimAt.pure hs₂ ⟨denote_mono hext₂ hQfa, hwapp⟩

theorem whnfCoreBodyI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some ex) (hw : WScoped d ex) :
    SimAt env s₀ (RelE d)
      (whnfCoreBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (whnfCoreBody (fueledFns env) env d ex) := by
  unfold whnfCoreBodyI
  rw [whnfCoreBody_unfold]
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  rw [hn]
  cases n with
  | sort u => cases hd; exact SimAt.pure hs ⟨hden, hw⟩
  | fvar idx nm t => invert_node hd; exact SimAt.pure hs ⟨hden, hw⟩
  | forallE nm t b m => invert_node hd; exact SimAt.pure hs ⟨hden, hw⟩
  | lam nm t b m => invert_node hd; exact SimAt.pure hs ⟨hden, hw⟩
  | const nm us => cases hd; exact SimAt.pure hs ⟨hden, hw⟩
  | lit l => cases hd; exact SimAt.pure hs ⟨hden, hw⟩
  | bvar k => cases hd; exact SimAt.throw
  | letE nm t v b => invert_node hd; exact SimAt.throw
  | app g' a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨xg, hg, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨xa, ha, hd⟩ := hd
    subst hd
    have hwfa : WScoped d xg ∧ WScoped d xa := by
      simpa only [WScoped] using hw
    refine SimAt.bind (ih.whnfCore hs hg hwfa.1)
      (fun s₁ f' f'x hs₁ hext₁ hP => ?_)
    obtain ⟨hf'd, hwf'⟩ := hP
    refine SimAt.view ?_
    obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hf'd
    rw [hn']
    cases n' with
    | lam nm ty body mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨tyx, hty, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨bodyx, hbody, hd'⟩ := hd'
      subst hd'
      have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
        simpa only [WScoped] using hwf'
      have hwred : WScoped d (bodyx.instantiate1 xa) :=
        WScoped.instantiate1_gen hwfa.2 0 hwtb.2
      have hwapp : WScoped d (Expr.app (.lam nm tyx bodyx mb) xa) := by
        simp only [WScoped]
        exact ⟨hwtb, hwfa.2⟩
      obtain ⟨mbbi, mbcod⟩ := mb
      dsimp only
      cases mbcod with
      | none =>
        dsimp only
        refine SimAt.of_eff (internI_eff hs₁ (x :=
            .app (.lam nm tyx bodyx ⟨mbbi, none⟩) xa) ?_) _
          (fun s fa hQ => ⟨hQ, hwapp⟩)
        rw [denoteNode, hf'd, denote_mono hext₁ ha]
        rfl
      | some v =>
        dsimp only
        by_cases hnz : v.isNonZero
        · rw [if_pos hnz, if_pos hnz]
          refine SimAt.bind_left (inst1M_eff hs₁ hbody
            (denote_mono hext₁ ha)) (fun s₂ red hs₂ hext₂ hQ => ?_)
          exact ih.whnfCore hs₂ hQ hwred
        · rw [if_neg hnz, if_neg hnz]
          refine SimAt.bind (ih.infer hs₁ (denote_mono hext₁ ha) hwfa.2)
            (fun s₂ ta tax hs₂ hext₂ hP₂ => ?_)
          obtain ⟨htad, hwta⟩ := hP₂
          refine SimAt.bind (ih.defeq hs₂ htad
            (denote_mono hext₂ hty) hwta hwtb.1)
            (fun s₃ b b' hs₃ hext₃ hPb => ?_)
          obtain rfl : b = b' := hPb
          cases b with
          | true =>
            simp only [↓reduceIte]
            refine SimAt.bind_left (inst1M_eff hs₃
              (denote_mono ((hext₂.trans hext₃)) hbody)
              (denote_mono ((hext₁.trans hext₂).trans hext₃) ha))
              (fun s₄ red hs₄ hext₄ hQ => ?_)
            exact ih.whnfCore hs₄ hQ hwred
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine SimAt.of_eff (internI_eff hs₃ (x :=
                .app (.lam nm tyx bodyx ⟨mbbi, some v⟩) xa) ?_) _
              (fun s fa hQ => ⟨hQ, hwapp⟩)
            rw [denoteNode,
              denote_mono (hext₂.trans hext₃) hf'd,
              denote_mono ((hext₁.trans hext₂).trans hext₃) ha]
            rfl
    | bvar k =>
      cases hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | sort u =>
      cases hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | const nm us =>
      cases hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | lit l =>
      cases hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | fvar idx nm t =>
      invert_node hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | app f₂ a₂ =>
      invert_node hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | forallE nm t b m =>
      invert_node hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | letE nm t v b =>
      invert_node hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
    | proj s' j' e' =>
      invert_node hd'
      refine whnfCoreI_iota_tail ih henv hs₁ hf'd
        (denote_mono hext₁ ha) hwf' hwfa.2
  | proj sn ip pe =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨pex, hpe, hd⟩ := hd
    subst hd
    have hwpe : WScoped d pex := by simpa only [WScoped] using hw
    refine SimAt.bind (ih.whnf hs hpe hwpe)
      (fun s₁ e' e'x hs₁ hext₁ hP => ?_)
    obtain ⟨he'd, hwe'⟩ := hP
    have hwproj : WScoped d (Expr.proj sn ip e'x) := by
      simpa only [WScoped] using hwe'
    rw [mkFEnv_findProj?]
    cases hfp : env.findProj? sn ip with
    | none =>
      dsimp only
      refine SimAt.of_eff (internI_eff hs₁ (x := .proj sn ip e'x) ?_) _
        (fun s pr hQ => ⟨hQ, hwproj⟩)
      rw [denoteNode, he'd]; rfl
    | some entry =>
      dsimp only
      refine SimAt.withStore ?_
      obtain ⟨n', hn', hc', hd'⟩ :=
        denote_some_inv (getAppFnI_spec hs₁.wf he'd)
      rw [hn']
      cases n' with
      | const c us =>
        rw [← Option.some.inj hd']
        dsimp only
        refine SimAt.withStore ?_
        have hargs := getAppArgsI_spec hs₁.wf he'd
        rw [hargs.length_eq]
        have hwarg : WScoped d
            (e'x.getAppArgs.getD (entry.numParams + ip) (.bvar 0)) :=
          wscoped_getD hwe'.getAppArgs _
        split
        · have hbv : denoteNode s₁.store.denote (.bvar 0)
              = some (.bvar 0) := rfl
          refine SimAt.bind_left (internI_eff hs₁ hbv)
            (fun s₂ bvar0 hs₂ hext₂ hQ0 => ?_)
          by_cases hnz : (Level.subst entry.levelParams us
              entry.structSort).isNonZero
          · rw [if_pos hnz, if_pos hnz]
            exact ih.whnfCore hs₂
              (DenL.getD hQ0 (entry.numParams + ip)
                (hargs.mono hext₂)) hwarg
          · rw [if_neg hnz, if_neg hnz]
            refine SimAt.bind (projCertI_sim ih hs₂
              (denote_mono hext₂ he'd) hwe')
              (fun s₃ b b' hs₃ hext₃ hPb => ?_)
            obtain rfl : b = b' := hPb
            cases b with
            | true =>
              simp only [↓reduceIte]
              exact ih.whnfCore hs₃
                (DenL.getD (denote_mono hext₃ hQ0)
                  (entry.numParams + ip)
                  (hargs.mono (hext₂.trans hext₃))) hwarg
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              refine SimAt.of_eff (internI_eff hs₃
                (x := .proj sn ip e'x) ?_) _
                (fun s pr hQ => ⟨hQ, hwproj⟩)
              rw [denoteNode,
                denote_mono (hext₂.trans hext₃) he'd]
              rfl
        · refine SimAt.of_eff (internI_eff hs₁
            (x := .proj sn ip e'x) ?_) _
            (fun s pr hQ => ⟨hQ, hwproj⟩)
          rw [denoteNode, he'd]; rfl
      | bvar k =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | sort u =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | lit l =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | fvar idx nm t =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | app f₂ a₂ =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | lam nm t b m =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | forallE nm t b m =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | letE nm t v b =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl
      | proj s' j' e'' =>
        invert_head hd'
        refine SimAt.of_eff (internI_eff hs₁
          (x := .proj sn ip e'x) ?_) _ (fun s pr hQ => ⟨hQ, hwproj⟩)
        rw [denoteNode, he'd]; rfl

end Walks

section Walks2

variable {env : Env} {f : Nat}

private theorem whnfBody_unfold (env : Env) (d : Nat) (e : Expr) :
    whnfBody (fueledFns env) env d e =
    ((fueledFns env).whnfCore d e >>= fun e₁ =>
      reduceNat (fueledFns env) env d e₁ >>= fun o =>
      match o with
      | some e₂ => (fueledFns env).whnf d e₂
      | none =>
        match unfoldDefinition env e₁ with
        | some e₂ => (fueledFns env).whnf d e₂
        | none => pure e₁) := rfl

theorem whnfBodyI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some ex) (hw : WScoped d ex) :
    SimAt env s₀ (RelE d)
      (whnfBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (whnfBody (fueledFns env) env d ex) := by
  unfold whnfBodyI
  rw [whnfBody_unfold]
  refine SimAt.bind (ih.whnfCore hs hden hw)
    (fun s₁ e₁ e₁x hs₁ hext₁ hP => ?_)
  obtain ⟨he₁d, hwe₁⟩ := hP
  refine SimAt.bind (reduceNatI_sim ih hs₁ he₁d hwe₁)
    (fun s₂ o ox hs₂ hext₂ hPo => ?_)
  cases o with
  | some e₂ =>
    cases ox with
    | none => exact absurd hPo (by simp [RelO])
    | some e₂x =>
      obtain ⟨he₂d, hwe₂⟩ := hPo
      exact ih.whnf hs₂ he₂d hwe₂
  | none =>
    cases ox with
    | some e₂x => exact absurd hPo (by simp [RelO])
    | none =>
      refine SimAt.bind_left (unfoldDefinitionI_eff hs₂
        (denote_mono hext₂ he₁d)) (fun s₃ o₂ hs₃ hext₃ hQ => ?_)
      cases hu : unfoldDefinition env e₁x with
      | some e₂x =>
        rw [hu] at hQ
        cases o₂ with
        | none => exact absurd hQ (by simp [OptDen])
        | some e₂ =>
          exact ih.whnf hs₃ hQ (unfoldDefinition_WScoped henv hu hwe₁)
      | none =>
        rw [hu] at hQ
        cases o₂ with
        | some e₂ => exact absurd hQ (by simp [OptDen])
        | none =>
          exact SimAt.pure hs₃
            ⟨denote_mono (hext₂.trans hext₃) he₁d, hwe₁⟩

end Walks2

section Walks3

variable {env : Env} {f : Nat}

set_option maxHeartbeats 4000000 in
theorem inferBodyI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some ex) (hw : WScoped d ex) :
    SimAt env s₀ (RelE d)
      (inferBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (inferBody (fueledFns env) env d ex) := by
  unfold inferBodyI
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  rw [hn]
  cases n with
  | sort u =>
    cases hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    exact SimAt.of_eff (internI_eff hs (x := .sort (.succ u)) rfl) _
      (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
  | bvar k =>
    cases hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    exact SimAt.throw
  | letE nm t v b =>
    invert_node hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    exact SimAt.throw
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    subst hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    have h' : idx < d ∧ WScoped idx tyx := by
      simpa only [WScoped] using hw
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimAt.pure hs ⟨hty, WScoped.mono (Nat.le_of_lt h'.1) h'.2⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimAt.throw
  | lit l =>
    cases hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimAt.of_eff (internI_eff hs (x := .const natName []) rfl)
          _ (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimAt.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimAt.of_eff (internI_eff hs (x := .const stringName []) rfl)
          _ (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
      · rw [if_neg hg, if_neg hg]
        exact SimAt.throw
  | const nm us =>
    cases hd
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    rw [mkFEnv_find?]
    cases hfn : env.find? nm with
    | none => exact SimAt.throw
    | some ci =>
      dsimp only
      by_cases hlen : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hlen, if_pos hlen]
        refine SimAt.of_eff (constTyAtM_eff hs hfn) _ (fun s r hQ => ?_)
        refine ⟨hQ, ?_⟩
        obtain ⟨htf, -⟩ := henv _ (find?_mem hfn)
        exact wscoped_instLevels_of_not_hasFvar htf _ _
      · rw [if_neg hlen, if_neg hlen]
        exact SimAt.throw_bind
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    obtain ⟨mbbi, mbcod⟩ := m
    dsimp only
    cases mbcod with
    | none => exact SimAt.throw
    | some v =>
      dsimp only
      refine SimAt.bind (ih.infer hs hty hwtb.1)
        (fun s₁ tty ttyx hs₁ hext₁ hP => ?_)
      obtain ⟨httyd, hwtty⟩ := hP
      refine SimAt.bind (ih.whnf hs₁ httyd hwtty)
        (fun s₂ w wx hs₂ hext₂ hP₂ => ?_)
      obtain ⟨hwd, hww⟩ := hP₂
      refine SimAt.view ?_
      obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hwd
      rw [hn']
      cases n' with
      | sort u =>
        cases hd'
        exact SimAt.of_eff (internI_eff hs₂
          (x := .sort (.imax u v)) rfl) _
          (fun s r hQ => ⟨hQ, by simp [WScoped]⟩)
      | bvar k => invert_node hd'; exact SimAt.throw
      | const nm' us => invert_node hd'; exact SimAt.throw
      | lit l => invert_node hd'; exact SimAt.throw
      | fvar idx nm' t' => invert_node hd'; exact SimAt.throw
      | app f' a' => invert_node hd'; exact SimAt.throw
      | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
      | forallE nm' t' b' m' => invert_node hd'; exact SimAt.throw
      | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
      | proj s' j' e' => invert_node hd'; exact SimAt.throw
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    obtain ⟨mbbi, mbcod⟩ := m
    dsimp only
    cases mbcod with
    | none => exact SimAt.throw
    | some v =>
      dsimp only
      refine SimAt.bind (ih.infer hs hty hwtb.1)
        (fun s₁ tty ttyx hs₁ hext₁ hP => ?_)
      obtain ⟨httyd, hwtty⟩ := hP
      refine SimAt.bind (ih.whnf hs₁ httyd hwtty)
        (fun s₂ w wx hs₂ hext₂ hP₂ => ?_)
      obtain ⟨hwd, hww⟩ := hP₂
      refine SimAt.view ?_
      obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hwd
      rw [hn']
      cases n' with
      | sort u =>
        cases hd'
        have hext₀₂ := hext₁.trans hext₂
        have hfvd : denoteNode s₂.store.denote (.fvar d nm t)
            = some (.fvar d nm tyx) := by
          rw [denoteNode, denote_mono hext₀₂ hty]; rfl
        refine SimAt.bind_left (internI_eff hs₂ hfvd)
          (fun s₃ fv hs₃ hext₃ hQfv => ?_)
        refine SimAt.bind_left (inst1M_eff hs₃
          (denote_mono (hext₀₂.trans hext₃) hbody) hQfv)
          (fun s₄ ob hs₄ hext₄ hQob => ?_)
        refine SimAt.bind (ih.infer hs₄ hQob
          (WScoped.instantiate1 hwtb.1 0 hwtb.2))
          (fun s₅ bt btx hs₅ hext₅ hP₅ => ?_)
        obtain ⟨hbtd, hwbt⟩ := hP₅
        refine SimAt.bind (ih.infer hs₅ hbtd hwbt)
          (fun s₆ tbt tbtx hs₆ hext₆ hP₆ => ?_)
        obtain ⟨htbtd, hwtbt⟩ := hP₆
        refine SimAt.bind (ih.whnf hs₆ htbtd hwtbt)
          (fun s₇ w' w'x hs₇ hext₇ hP₇ => ?_)
        obtain ⟨hw'd, hww'⟩ := hP₇
        refine SimAt.view ?_
        obtain ⟨n'', hn'', hc'', hd''⟩ := denote_some_inv hw'd
        rw [hn'']
        cases n'' with
        | sort v' =>
          cases hd''
          refine SimAt.bind (SimAt.liftFueled _ _ hs₇)
            (fun s₈ ok ok' hs₈ hext₈ hPok => ?_)
          obtain rfl : ok = ok' := hPok
          cases ok with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            refine SimAt.bind_left (abstract1M_eff hs₈
              (denote_mono ((hext₆.trans hext₇).trans hext₈) hbtd))
              (fun s₉ btAbs hs₉ hext₉ hQabs => ?_)
            refine SimAt.of_eff (internI_eff hs₉
              (x := .forallE nm tyx (btx.abstract1 d) ⟨mbbi, some v⟩) ?_)
              _ (fun s r hQ => ?_)
            · rw [denoteNode, denote_mono
                (((((((hext₀₂.trans hext₃).trans hext₄).trans
                  hext₅).trans hext₆).trans hext₇).trans hext₈).trans
                  hext₉) hty, hQabs]
              rfl
            · refine ⟨hQ, ?_⟩
              simp only [WScoped]
              exact ⟨hwtb.1, WScoped.abstract1 0 hwbt⟩
        | bvar k => invert_node hd''; exact SimAt.throw
        | const nm' us => invert_node hd''; exact SimAt.throw
        | lit l => invert_node hd''; exact SimAt.throw
        | fvar idx nm' t' => invert_node hd''; exact SimAt.throw
        | app f' a' => invert_node hd''; exact SimAt.throw
        | lam nm' t' b' m' => invert_node hd''; exact SimAt.throw
        | forallE nm' t' b' m' => invert_node hd''; exact SimAt.throw
        | letE nm' t' v' b' => invert_node hd''; exact SimAt.throw
        | proj s' j' e' => invert_node hd''; exact SimAt.throw
      | bvar k => invert_node hd'; exact SimAt.throw
      | const nm' us => invert_node hd'; exact SimAt.throw
      | lit l => invert_node hd'; exact SimAt.throw
      | fvar idx nm' t' => invert_node hd'; exact SimAt.throw
      | app f' a' => invert_node hd'; exact SimAt.throw
      | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
      | forallE nm' t' b' m' => invert_node hd'; exact SimAt.throw
      | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
      | proj s' j' e' => invert_node hd'; exact SimAt.throw
  | app g' a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨xg, hg, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨xa, ha, hd⟩ := hd
    subst hd
    have hwfa : WScoped d xg ∧ WScoped d xa := by
      simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    refine SimAt.bind (ih.infer hs hg hwfa.1)
      (fun s₁ tf tfx hs₁ hext₁ hP => ?_)
    obtain ⟨htfd, hwtf⟩ := hP
    refine SimAt.bind (ih.whnf hs₁ htfd hwtf)
      (fun s₂ w wx hs₂ hext₂ hP₂ => ?_)
    obtain ⟨hwd, hww⟩ := hP₂
    refine SimAt.view ?_
    obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hwd
    rw [hn']
    cases n' with
    | forallE nm ty body mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨tyx, hty, hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨bodyx, hbody, hd'⟩ := hd'
      subst hd'
      have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
        simpa only [WScoped] using hww
      refine SimAt.bind (ih.infer hs₂
        (denote_mono (hext₁.trans hext₂) ha) hwfa.2)
        (fun s₃ ta tax hs₃ hext₃ hP₃ => ?_)
      obtain ⟨htad, hwta⟩ := hP₃
      refine SimAt.bind (ih.defeq hs₃ htad
        (denote_mono hext₃ hty) hwta hwtb.1)
        (fun s₄ b b' hs₄ hext₄ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimAt.throw_bind
      | true =>
        simp only [↓reduceIte]
        refine SimAt.of_eff (inst1M_eff hs₄
          (denote_mono (hext₃.trans hext₄) hbody)
          (denote_mono (((hext₁.trans hext₂).trans hext₃).trans hext₄)
            ha)) _ (fun s r hQ => ?_)
        exact ⟨hQ, WScoped.instantiate1_gen hwfa.2 0 hwtb.2⟩
    | bvar k => invert_node hd'; exact SimAt.throw
    | sort u => invert_node hd'; exact SimAt.throw
    | const nm' us => invert_node hd'; exact SimAt.throw
    | lit l => invert_node hd'; exact SimAt.throw
    | fvar idx nm' t' => invert_node hd'; exact SimAt.throw
    | app f' a' => invert_node hd'; exact SimAt.throw
    | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
    | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
    | proj s' j' e' => invert_node hd'; exact SimAt.throw
  | proj sn ip pe =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨pex, hpe, hd⟩ := hd
    subst hd
    have hwpe : WScoped d pex := by simpa only [WScoped] using hw
    unfold inferBody
    dsimp only [viewM, Expr.view]
    refine SimAt.bind_pure_right ?_
    try dsimp only
    refine SimAt.bind (ih.infer hs hpe hwpe)
      (fun s₁ tpe tpex hs₁ hext₁ hP => ?_)
    obtain ⟨htped, hwtpe⟩ := hP
    refine SimAt.bind (ih.whnf hs₁ htped hwtpe)
      (fun s₂ te tex hs₂ hext₂ hP₂ => ?_)
    obtain ⟨hted, hwte⟩ := hP₂
    refine SimAt.withStore ?_
    obtain ⟨n', hn', hc', hd'⟩ :=
      denote_some_inv (getAppFnI_spec hs₂.wf hted)
    rw [hn']
    cases n' with
    | const T us =>
      rw [← Option.some.inj hd']
      dsimp only
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none => exact SimAt.throw
      | some entry =>
        dsimp only
        refine SimAt.withStore ?_
        have htargs := getAppArgsI_spec hs₂.wf hted
        rw [htargs.length_eq]
        split
        · refine SimAt.bind_left (constTyAtM_eff hs₂
            (Env.findProj?_some hfp)) (fun s₃ pty hs₃ hext₃ hQty => ?_)
          simp only [ConstantInfo.toConstantVal] at hQty
          refine SimAt.bind_left (piResidualM_eff hs₃ hQty
            ((htargs.mono hext₃).append (DenL.cons
              (denote_mono ((hext₁.trans hext₂).trans hext₃) hpe)
              DenL.nil))) (fun s₄ ores hs₄ hext₄ hQres => ?_)
          cases hres : piResidual
              (entry.ty.instantiateLevelParams entry.levelParams us)
              (tex.getAppArgs ++ [pex]) with
          | some resTy =>
            rw [hres] at hQres
            cases ores with
            | none => exact absurd hQres (by simp [OptDen])
            | some res =>
              refine SimAt.pure hs₄ ⟨hQres, ?_⟩
              have hclosed := (henv _ (find?_mem
                (Env.findProj?_some hfp))).1
              refine piResidual_WScoped hres
                (WScoped.of_not_hasFvar (by
                  rw [hasFvar_instantiateLevelParams]
                  exact hclosed)) ?_
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hwte.getAppArgs x hx
              · rcases List.mem_singleton.mp hx with rfl
                exact hwpe
          | none =>
            rw [hres] at hQres
            cases ores with
            | some res => exact absurd hQres (by simp [OptDen])
            | none => exact SimAt.throw
        · exact SimAt.throw
    | bvar k => invert_head hd'; exact SimAt.throw
    | sort u => invert_head hd'; exact SimAt.throw
    | lit l => invert_head hd'; exact SimAt.throw
    | fvar idx nm' t' => invert_head hd'; exact SimAt.throw
    | app f' a' => invert_head hd'; exact SimAt.throw
    | lam nm' t' b' m' => invert_head hd'; exact SimAt.throw
    | forallE nm' t' b' m' => invert_head hd'; exact SimAt.throw
    | letE nm' t' v' b' => invert_head hd'; exact SimAt.throw
    | proj s' j' e' => invert_head hd'; exact SimAt.throw

end Walks3

end Setlec
