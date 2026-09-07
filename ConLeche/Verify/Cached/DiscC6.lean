import ConLeche.Verify.Cached.DiscC5

/-!
# Cached body walks, part 6: annotation

Port of `ConLeche/Verify/DiscI6.lean` under the recipe (DESIGN.md,
task #163): the simulation walks for `isPropTypeI` and `annotateBodyI`
(`ConLeche/Cached/CoreC.lean`), whose bodies are character-identical to
their `ConLeche/Kernel/CoreI.lean` originals up to `EIdx → ExprC` /
`CheckIM → CheckCM` (plus the two recorded `peelFuelM` deviation lines
in `annotateBodyI`'s binder clauses).  Task #175 wiring W5: the
projection elimination fallbacks (`projFieldDomI`,
`annotateProjRecI`, `annotateProjElimI`) and their walks are gone —
every supported projection is a tower table entry, and the
`.proj` clause's non-tower arms are verdicts.

One representation shrinkage simplifies the statements against the
interned originals: the structure/constructor names are plain `Name`s
(so the `NIdx` denotation premises vanish).  The pure comparand side
of every statement is byte-identical to the interned original's.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche.Cached.ExprC

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- Port of `isPropTypeI_sim`. -/
theorem isPropTypeC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {ty : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ty) (hw : Expr.WScoped d ty) :
    SimC mode env s₀ RelVC
      (isPropTypeI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (isPropType (fueledFns mode env) env d ty) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).annotate d i >>= fun ty' =>
      (coreKnotI mode (mkFEnv env) f).inferIO d ty' >>= fun tty =>
      ensureSortI (coreKnotI mode (mkFEnv env) f) d tty >>= fun s =>
      pure .zero >>= fun z =>
      isEquivLM s z >>= fun o =>
      liftFueled "level comparison" o)
    ((fueledFns mode env).annotate d ty >>= fun ty' =>
      (fueledFns mode env).inferIO d ty' >>= fun tty =>
      ensureSort (fueledFns mode env) env d tty >>= fun s =>
      liftFueled "level comparison" (Level.isEquiv s Level.zero))
  refine SimC.bind (ih.annotate hs hden hw)
    (fun s₁ ty' ty'x hs₁ hP => ?_)
  obtain ⟨hty'd, hwty'⟩ := hP
  refine SimC.bind (ih.inferIO hs₁ hty'd hwty')
    (fun s₂ tty ttyx hs₂ hP₂ => ?_)
  obtain ⟨httyd, hwtty⟩ := hP₂
  refine SimC.bind (ensureSortC_sim ih hs₂ httyd hwtty)
    (fun s₃ u lu hs₃ hPu => ?_)
  obtain rfl : u = lu := hPu
  refine SimC.bind_left (pureEq_eff hs₃ Level.zero)
    (fun s₃z z hs₃z hz => ?_)
  subst hz
  refine SimC.bind_left (isEquivLM_eff hs₃z u Level.zero)
    (fun s₃o o hs₃o ho => ?_)
  subst ho
  exact SimC.liftFueled _ _ hs₃o

end Walks

section Walks3

variable {env : Env} {f : Nat}

/-- Port of `annotateBodyI_sim`. -/
theorem annotateBodyC_sim (ih : SSimC mode env f) (_henv : EnvWF env)
    {d : Nat} {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (annotateBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (annotateBody (fueledFns mode env) env d ex) := by
  unfold annotateBodyI
  obtain rfl := hden
  have hden : RelC i i := rfl
  cases i with
  | bvar k =>
    dsimp only
    exact SimC.pure hs ⟨hden, hw⟩
  | sort u =>
    dsimp only
    exact SimC.pure hs ⟨hden, hw⟩
  | const nmN us =>
    dsimp only
    exact SimC.pure hs ⟨hden, hw⟩
  | letE t v b =>
    dsimp only
    have hwtvb : Expr.WScoped d t ∧ Expr.WScoped d v ∧
        Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.letE t v b) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwtvb.1)
      (fun s₁ ty' ty'x hs₁ hP₁ => ?_)
    obtain ⟨-, -⟩ := hP₁
    refine SimC.bind (ih.annotate hs₁ rfl hwtvb.2.1)
      (fun s₄ v' v'x hs₄ hP₄ => ?_)
    obtain ⟨-, -⟩ := hP₄
    refine SimC.bind_left (inst1M_eff hs₄ rfl rfl)
      (fun s₇ ob hs₇ hQob => ?_)
    exact ih.annotate hs₇ hQob
      (Expr.WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
  | fvar idx t =>
    dsimp only
    unfold annotateBody
    try dsimp only
    by_cases hidx : idx < d
    · rw [if_pos hidx, if_pos hidx]
      exact SimC.pure hs ⟨hden, hw⟩
    · rw [if_neg hidx, if_neg hidx]
      exact SimC.throw
  | lit l =>
    cases l with
    | natVal k =>
      dsimp only
      unfold annotateBody
      try dsimp only
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimC.pure hs ⟨hden, hw⟩
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
    | strVal str =>
      dsimp only
      unfold annotateBody
      try dsimp only
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimC.pure hs ⟨hden, hw⟩
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
  | app g' a =>
    dsimp only
    -- structural (task #100 stage 6: the application rule's checks
    -- moved to the driver's inference sweep, so the spine loop is
    -- gone and the clause annotates the two children)
    have hwga : Expr.WScoped d g' ∧ Expr.WScoped d a := by
      have hw' : Expr.WScoped d (Expr.app g' a) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwga.1)
      (fun s₁ g'' g''x hs₁ hP₁ => ?_)
    obtain ⟨hg''d, hwg''⟩ := hP₁
    refine SimC.bind (ih.annotate hs₁ rfl hwga.2)
      (fun s₂ a'' a''x hs₂ hP₂ => ?_)
    obtain ⟨ha''d, hwa''⟩ := hP₂
    obtain ⟨hg''w, rfl⟩ := hg''d
    obtain ⟨ha''w, rfl⟩ := ha''d
    exact SimC.of_eff
      (pureC_eff hs₂ (x := Expr.app g'' a'')) _
      (fun r hQ => ⟨hQ, by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (Nat.le_refl _) hwg'', hwa''⟩⟩)
  | forallE t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.forallE t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwtb.1)
      (fun s₁ ty' ty'x hs₁ hP => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP
    obtain rfl := hty'd
    refine SimC.bind_left
      (pureC_eff hs₁ (x := Expr.fvar d ty'))
      (fun s₂ fv hs₂ hQfv => ?_)
    have hQfv' : RelC fv (Expr.fvar d ty') := hQfv
    refine SimC.bind_left (peelFuelM_eff hs₂)
      (fun s₃ fuel hs₃ _hQfuel => ?_)
    exact annotatePisC_tail_sim ih hs₃ rfl rfl rfl
      hQfv' hwty' hwtb.2
  | lam t b m =>
    dsimp only
    have hwtb : Expr.WScoped d t ∧ Expr.WScoped d b := by
      have hw' : Expr.WScoped d
        (Expr.lam t b m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind_left (bvarBoundM_eff hs)
      (fun sb bnd hsb hQb => ?_)
    by_cases hb0 : bnd = 0
    · rw [if_pos hb0]
      subst hb0
      refine SimC.bind (ih.annotate hsb rfl hwtb.1)
        (fun s₁ ty' ty'x hs₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      obtain rfl := hty'd
      refine SimC.bind_left
        (pureC_eff hs₁ (x := Expr.fvar d ty'))
        (fun s₂ fv hs₂ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar d ty') := hQfv
      refine SimC.bind_left (peelFuelM_eff hs₂)
        (fun s₃ fuel hs₃ _hQfuel => ?_)
      exact annotateLamsC_tail_sim ih hs₃ rfl rfl rfl
        hQfv' hwty' hwtb.2
    · rw [if_neg hb0]
      refine SimC.bind (ih.annotate hsb rfl hwtb.1)
        (fun s₁ ty' ty'x hs₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      obtain rfl := hty'd
      refine SimC.bind_left
        (pureC_eff hs₁ (x := Expr.fvar d ty'))
        (fun s₂ fv hs₂ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar d ty') := hQfv
      refine SimC.bind_left (inst1M_eff hs₂ rfl hQfv')
        (fun s₃ ob hs₃ hQob => ?_)
      refine SimC.bind (ih.annotate hs₃ hQob
        (Expr.WScoped.instantiate1 hwty' 0 hwtb.2))
        (fun s₄ body' body'x hs₄ hP₄ => ?_)
      obtain ⟨hbody'd, hwbody'⟩ := hP₄
      refine SimC.bind_left (abstract1M_eff hs₄ hbody'd)
        (fun s₈ bAbs hs₈ hQabs => ?_)
      -- task #161 P5: the single-binder write — the λ chain rule at a
      -- chain of length one, the same `annotPwLam` the spec clause runs.
      -- The rebuilt node is the same on both sides whatever the datum.
      have hstep : ∀ (s' : CState) (pw : PropWhen), CSOK mode env s' →
          SimC mode env s' (RelEC d)
            (pure (Expr.lam ty' bAbs ⟨pw⟩))
            (pure (Expr.lam ty' (body'x.abstract1 d)
              ⟨pw⟩)) := by
        intro s' pw hsS
        refine SimC.of_eff (pureC_eff hsS
          (x := Expr.lam ty' bAbs ⟨pw⟩)) _ (fun r hQ => ⟨by
            show _ = _
            have h2 : r
              = Expr.lam ty' bAbs ⟨pw⟩ := hQ
            rw [h2, hQabs], by
            simp only [Expr.WScoped]
            exact ⟨hwty', ConLeche.WScoped.abstract1 0 hwbody'⟩⟩)
      -- task #172 B3 method row: the cached guard reads
      -- `mode.verified`, the pure one `mode.verifiedChecks`; a bare
      -- `split` decides only one of the two `if`s.
      by_cases hpw : (!pwWritten m.pw) = true
      · simp only [hpw, ↓reduceIte]
        refine SimC.bind (annotPwLamC_sim ih hs₈ hbody'd hwbody')
          (fun s₉ pw pwx hs₉ hPpw => ?_)
        obtain rfl : pw = pwx := hPpw
        exact hstep s₉ pw hs₉
      · simp only [Bool.not_eq_true] at hpw
        simp only [hpw, ↓reduceIte]
        exact hstep s₈ m.pw hs₈
  | proj snN ipN pe =>
    dsimp only
    have hwpe : Expr.WScoped d pe := by
      have hw' : Expr.WScoped d (Expr.proj snN ipN pe) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs rfl hwpe)
      (fun s₁ e' e'x hs₁ hP => ?_)
    obtain ⟨he'd, hwe'⟩ := hP
    refine SimC.bind (ih.inferIO hs₁ he'd hwe')
      (fun s₂ tpe tpex hs₂ hP₂ => ?_)
    obtain ⟨htped, hwtpe⟩ := hP₂
    refine SimC.bind (ih.whnf hs₂ htped hwtpe)
      (fun s₃ te tex hs₃ hP₃ => ?_)
    obtain ⟨hted, hwte⟩ := hP₃
    refine SimC.pureB ?_
    obtain rfl := hted
    have hted : RelC te te := rfl
    have htargs : RelCL (ExprC.getAppArgs te) (Expr.getAppArgs te) :=
      ExprC.getAppArgs_spec te
    have hfn := ExprC.getAppFn_spec te
    generalize hgn : ExprC.getAppFn te = g at hfn ⊢
    cases g with
    | const T us =>
      rw [show (Expr.getAppFn te) = Expr.const T us from hfn.symm]
      dsimp only
      refine SimC.bind_left (pureEq_eff hs₃ T)
        (fun s₃T Tw hs₃T hTw => ?_)
      subst hTw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? Tw ipN with
      | none =>
        exact SimC.throw
      | some entry =>
        dsimp only
        refine SimC.pureB ?_
        simp only [RelCL.length htargs]
        by_cases hlen : (Expr.getAppArgs te).length = entry.numParams
        · rw [if_pos hlen, if_pos hlen]
          exact SimC.of_eff
            (pureC_eff hs₃T (x := Expr.proj Tw ipN e')) _
            (fun r hQ => ⟨by
                show _ = _
                have h2 : r = Expr.proj Tw ipN e' := hQ
                rw [h2, he'd], by
              simp only [Expr.WScoped]
              exact hwe'⟩)
        · rw [if_neg hlen, if_neg hlen]
          exact SimC.throw
    | bvar k =>
      rw [show (Expr.getAppFn te) = Expr.bvar k from hfn.symm]
      exact SimC.throw
    | sort u =>
      rw [show (Expr.getAppFn te) = Expr.sort u from hfn.symm]
      exact SimC.throw
    | lit l =>
      rw [show (Expr.getAppFn te) = Expr.lit l from hfn.symm]
      exact SimC.throw
    | fvar idx t' =>
      rw [show (Expr.getAppFn te) = Expr.fvar idx t'
        from hfn.symm]
      exact SimC.throw
    | app f₂ a₂ =>
      rw [show (Expr.getAppFn te) = Expr.app (f₂) (a₂)
        from hfn.symm]
      exact SimC.throw
    | lam t' b' m' =>
      rw [show (Expr.getAppFn te) = Expr.lam t' b' m'
        from hfn.symm]
      exact SimC.throw
    | forallE t' b' m' =>
      rw [show (Expr.getAppFn te)
        = Expr.forallE t' b' m' from hfn.symm]
      exact SimC.throw
    | letE t' v' b' =>
      rw [show (Expr.getAppFn te)
        = Expr.letE t' v' b' from hfn.symm]
      exact SimC.throw
    | proj s' j' e'' =>
      rw [show (Expr.getAppFn te) = Expr.proj s' j' e''
        from hfn.symm]
      exact SimC.throw

end Walks3

end ConLeche.Cached
