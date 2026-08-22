import Setlec.Verify.DiscI5

/-!
# Interned body walks, part 6: annotation and the projection fallbacks

Simulation walks for `isPropTypeI`, `projFieldDomI`,
`annotateProjRecI`, `annotateProjElimI` and `annotateBodyI`, mirroring
the corresponding `Setlec/Verify/Disc.lean` walks.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Setlec

open EStore Expr

section Walks

variable {env : Env} {f : Nat}

theorem isPropTypeI_sim (ih : SSimI env f) {d : Nat} {i : EIdx}
    {ty : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some ty) (hw : WScoped d ty) :
    SimAt env s₀ RelV
      (isPropTypeI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (isPropType (fueledFns env) env d ty) := by
  show SimAt env s₀ RelV
    ((coreKnotI (mkFEnv env) f).annotate d i >>= fun ty' =>
      (coreKnotI (mkFEnv env) f).infer d ty' >>= fun tty =>
      ensureSortI (coreKnotI (mkFEnv env) f) d tty >>= fun s =>
      liftFueled "level comparison" (Level.isEquiv s Level.zero))
    ((fueledFns env).annotate d ty >>= fun ty' =>
      (fueledFns env).infer d ty' >>= fun tty =>
      ensureSort (fueledFns env) env d tty >>= fun s =>
      liftFueled "level comparison" (Level.isEquiv s Level.zero))
  refine SimAt.bind (ih.annotate hs hden hw)
    (fun s₁ ty' ty'x hs₁ hext₁ hP => ?_)
  obtain ⟨hty'd, hwty'⟩ := hP
  refine SimAt.bind (ih.infer hs₁ hty'd hwty')
    (fun s₂ tty ttyx hs₂ hext₂ hP₂ => ?_)
  obtain ⟨httyd, hwtty⟩ := hP₂
  refine SimAt.bind (ensureSortI_sim ih hs₂ httyd hwtty)
    (fun s₃ u u' hs₃ hext₃ hPu => ?_)
  obtain rfl : u = u' := hPu
  exact SimAt.liftFueled _ _ hs₃

theorem projFieldDomI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {structProp : Bool} {sn : Name} {e' : EIdx} {e'x : Expr}
    (hwe : WScoped d e'x) :
    ∀ (k j : Nat) {tel : EIdx} {telx : Expr} {s₀ : IState},
      ISOK env s₀ → s₀.store.denote e' = some e'x →
      s₀.store.denote tel = some telx → WScoped d telx →
      SimAt env s₀ (RelE d)
        (projFieldDomI (coreKnotI (mkFEnv env) f) (mkFEnv env) d
          structProp sn e' j k tel)
        (projFieldDom (fueledFns env) env d structProp sn e'x j k telx)
  | 0, jj, tel, telx, s₀, hs, hde, hdt, hwtel => by
    unfold projFieldDomI
    refine SimAt.view ?_
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hdt
    rw [hn]
    cases n with
    | forallE nm dom rest mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨domx, hdom, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨restx, hrest, hd⟩ := hd
      subst hd
      have hw' : WScoped d domx ∧ WScoped d restx := by
        simpa only [WScoped] using hwtel
      exact SimAt.pure hs ⟨hdom, hw'.1⟩
    | bvar k => cases hd; exact SimAt.throw
    | sort u => cases hd; exact SimAt.throw
    | const nm us => cases hd; exact SimAt.throw
    | lit l => cases hd; exact SimAt.throw
    | fvar idx nm t => invert_node hd; exact SimAt.throw
    | app f' a' => invert_node hd; exact SimAt.throw
    | lam nm t b m => invert_node hd; exact SimAt.throw
    | letE nm t v b => invert_node hd; exact SimAt.throw
    | proj s' j' e'' => invert_node hd; exact SimAt.throw
  | k + 1, jj, tel, telx, s₀, hs, hde, hdt, hwtel => by
    unfold projFieldDomI
    refine SimAt.view ?_
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hdt
    rw [hn]
    cases n with
    | forallE nm dom rest mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨domx, hdom, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨restx, hrest, hd⟩ := hd
      subst hd
      have hw' : WScoped d domx ∧ WScoped d restx := by
        simpa only [WScoped] using hwtel
      have hwrest' : WScoped d (restx.instantiate1 (.proj sn jj e'x)) :=
        WScoped.instantiate1_gen
          (show WScoped d (.proj sn jj e'x) by
            simpa only [WScoped] using hwe) 0 hw'.2
      dsimp only [projFieldDom]
      refine SimAt.withStore ?_
      rw [looseBVarsBoundedI_spec hs.wf hrest]
      by_cases hcl : restx.looseBVarsBounded 0 = true
      · rw [if_pos hcl, if_pos hcl]
        exact projFieldDomI_sim ih henv hwe k (jj + 1) hs hde hrest hw'.2
      · rw [if_neg hcl, if_neg hcl]
        cases structProp with
        | true =>
          simp only [↓reduceIte]
          refine SimAt.bind (isPropTypeI_sim ih hs hdom hw'.1)
            (fun s₁ p p' hs₁ hext₁ hPp => ?_)
          obtain rfl : p = p' := hPp
          cases p with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.throw_bind
          | true =>
            simp only [↓reduceIte]
            have hpj : denoteNode s₁.store.denote (.proj sn jj e')
                = some (.proj sn jj e'x) := by
              rw [denoteNode, denote_mono hext₁ hde]; rfl
            refine SimAt.bind_left (internI_eff hs₁ hpj)
              (fun s₂ pj hs₂ hext₂ hQpj => ?_)
            refine SimAt.bind_left (inst1M_eff hs₂
              (denote_mono (hext₁.trans hext₂) hrest) hQpj)
              (fun s₃ rest' hs₃ hext₃ hQr => ?_)
            exact projFieldDomI_sim ih henv hwe k (jj + 1) hs₃
              (denote_mono ((hext₁.trans hext₂).trans hext₃) hde)
              hQr hwrest'
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hpj : denoteNode s₀.store.denote (.proj sn jj e')
              = some (.proj sn jj e'x) := by
            rw [denoteNode, hde]; rfl
          refine SimAt.bind_left (internI_eff hs hpj)
            (fun s₂ pj hs₂ hext₂ hQpj => ?_)
          refine SimAt.bind_left (inst1M_eff hs₂
            (denote_mono hext₂ hrest) hQpj)
            (fun s₃ rest' hs₃ hext₃ hQr => ?_)
          exact projFieldDomI_sim ih henv hwe k (jj + 1) hs₃
            (denote_mono (hext₂.trans hext₃) hde) hQr hwrest'
    | bvar k' => cases hd; exact SimAt.throw
    | sort u => cases hd; exact SimAt.throw
    | const nm us => cases hd; exact SimAt.throw
    | lit l => cases hd; exact SimAt.throw
    | fvar idx nm t => invert_node hd; exact SimAt.throw
    | app f' a' => invert_node hd; exact SimAt.throw
    | lam nm t b m => invert_node hd; exact SimAt.throw
    | letE nm t v b => invert_node hd; exact SimAt.throw
    | proj s' j' e'' => invert_node hd; exact SimAt.throw

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The shared reduct tail of the Prop-projection fallback: build the
recursor elimination and re-annotate it under the scope guard. -/
private theorem annotateProjRecI_rest (ih : SSimI env f)
    {d : Nat} {entry : ProjEntry} {te e' fi minor : EIdx}
    {params : List EIdx} {tex e'x fix minorx : Expr}
    {paramsx : List Expr} {us uf : List Level} {s₀ : IState}
    (hs : ISOK env s₀)
    (hte : s₀.store.denote te = some tex)
    (hde : s₀.store.denote e' = some e'x)
    (hfi : s₀.store.denote fi = some fix)
    (hmin : s₀.store.denote minor = some minorx)
    (hparams : DenL s₀.store params paramsx) :
    SimAt env s₀ (RelE d)
      (internI (.const (entry.structName.str "rec") (uf ++ us)) >>=
        fun recC =>
       internI (.lam (.str .anonymous "t") te fi ⟨.default, none⟩) >>=
        fun motive =>
       mkAppNM recC (params ++ [motive, minor, e']) >>= fun raw =>
       Setlec.withStore (fun st => st.wscopedBI d raw &&
         st.looseBVarsBoundedI 0 raw &&
         (st.fvarLeavesI raw).all
           (fun l => (st.fvarLeavesI e').contains l)) >>= fun g =>
       if g then (coreKnotI (mkFEnv env) f).annotate d raw
       else throw (.notImplemented "projection elimination scoping"))
      (let raw := Expr.mkAppN
          (.const (entry.structName.str "rec") (uf ++ us))
          (paramsx ++ [.lam (.str .anonymous "t") tex fix
            ⟨.default, none⟩, minorx, e'x])
        if raw.wscopedB d && raw.looseBVarsBounded 0 &&
            raw.fvarLeaves.all
              (fun l => e'x.fvarLeaves.contains l) then
          (fueledFns env).annotate d raw
        else throw (.notImplemented "projection elimination scoping")) := by
  have hcn : denoteNode s₀.store.denote
      (ENode.const (entry.structName.str "rec") (uf ++ us))
      = some (.const (entry.structName.str "rec") (uf ++ us)) := rfl
  refine SimAt.bind_left (internI_eff hs hcn)
    (fun s₁ recC hs₁ hext₁ hQrec => ?_)
  have hmot : denoteNode s₁.store.denote
      (ENode.lam (.str .anonymous "t") te fi ⟨.default, none⟩)
      = some (.lam (.str .anonymous "t") tex fix ⟨.default, none⟩) := by
    rw [denoteNode, denote_mono hext₁ hte, denote_mono hext₁ hfi]
    rfl
  refine SimAt.bind_left (internI_eff hs₁ hmot)
    (fun s₂ motive hs₂ hext₂ hQmot => ?_)
  refine SimAt.bind_left (mkAppNM_eff hs₂
    (denote_mono hext₂ hQrec)
    ((hparams.mono (hext₁.trans hext₂)).append
      (DenL.cons hQmot (DenL.cons
        (denote_mono (hext₁.trans hext₂) hmin)
        (DenL.cons (denote_mono (hext₁.trans hext₂) hde) DenL.nil)))))
    (fun s₃ raw hs₃ hext₃ hQraw => ?_)
  refine SimAt.withStore ?_
  rw [wscopedBI_spec hs₃.wf hQraw, looseBVarsBoundedI_spec hs₃.wf hQraw,
    leafGuardI_spec hs₃.wf hQraw
      (denote_mono ((hext₁.trans hext₂).trans hext₃) hde)]
  dsimp only
  split
  · rename_i hguard
    exact ih.annotate hs₃ hQraw (WScoped.of_wscopedB
      (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1))
  · exact SimAt.throw

set_option maxHeartbeats 8000000 in
theorem annotateProjRecI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {entry : ProjEntry} {ip : Nat} {te e' : EIdx}
    {tex e'x : Expr} {us : List Level} {s₀ : IState} (hs : ISOK env s₀)
    (hte : s₀.store.denote te = some tex)
    (hde : s₀.store.denote e' = some e'x)
    (hwte : WScoped d tex) (hwe : WScoped d e'x) :
    SimAt env s₀ (RelE d)
      (annotateProjRecI (coreKnotI (mkFEnv env) f) (mkFEnv env) d entry
        ip te e' us)
      (annotateProjRec (fueledFns env) env d entry ip tex e'x us) := by
  unfold annotateProjRecI
  unfold annotateProjRec
  rw [mkFEnv_find?]
  cases hfC : env.find? entry.ctor with
  | none => exact SimAt.throw
  | some ci =>
    cases ci with
    | ctorInfo cvC cnP cnF =>
      dsimp only
      refine SimAt.withStore ?_
      have hparams := getAppArgsI_spec hs.wf hte
      rw [hparams.length_eq]
      split
      · refine SimAt.bind_left (constTyAtM_eff hs hfC)
          (fun s₁ ctorTy hs₁ hext₁ hQty => ?_)
        simp only [ConstantInfo.toConstantVal] at hQty
        refine SimAt.bind_left (piResidualM_eff hs₁ hQty
          (hparams.mono hext₁)) (fun s₂ otel hs₂ hext₂ hQtel => ?_)
        rw [instPis_eq_piResidual]
        cases htel : piResidual
            (cvC.type.instantiateLevelParams cvC.levelParams us)
            tex.getAppArgs with
        | none =>
          rw [htel] at hQtel
          cases otel with
          | some tel => exact absurd hQtel (by simp [OptDen])
          | none => exact SimAt.throw
        | some telx =>
          rw [htel] at hQtel
          cases otel with
          | none => exact absurd hQtel (by simp [OptDen])
          | some tel =>
            have hwtel : WScoped d telx := by
              refine instPis_WScoped
                (by rw [instPis_eq_piResidual]; exact htel) ?_
                hwte.getAppArgs
              obtain ⟨htf, -⟩ := henv _ (find?_mem hfC)
              exact wscoped_instLevels_of_not_hasFvar htf _ _
            refine SimAt.bind (isPropTypeI_sim ih hs₂
              (denote_mono (hext₁.trans hext₂) hte) hwte)
              (fun s₃ sp sp' hs₃ hext₃ hPsp => ?_)
            obtain rfl : sp = sp' := hPsp
            refine SimAt.bind (projFieldDomI_sim ih henv hwe ip 0 hs₃
              (denote_mono ((hext₁.trans hext₂).trans hext₃) hde)
              (denote_mono hext₃ hQtel) hwtel)
              (fun s₄ fi fix hs₄ hext₄ hPfi => ?_)
            obtain ⟨hfid, hwfi⟩ := hPfi
            have hbv : denoteNode s₄.store.denote (.bvar (cnF - 1 - ip))
                = some (.bvar (cnF - 1 - ip)) := rfl
            refine SimAt.bind_left (internI_eff hs₄ hbv)
              (fun s₅ fieldBvar hs₅ hext₅ hQbv => ?_)
            refine SimAt.bind_left (pisToLamsM_eff (k := cnF) hs₅
              (denote_mono ((hext₃.trans hext₄).trans hext₅) hQtel)
              hQbv) (fun s₆ ominor hs₆ hext₆ hQmin => ?_)
            cases hmin : Expr.pisToLams cnF telx
                (.bvar (cnF - 1 - ip)) with
            | none =>
              rw [hmin] at hQmin
              cases ominor with
              | some minor => exact absurd hQmin (by simp [OptDen])
              | none => exact SimAt.throw
            | some minorx =>
              rw [hmin] at hQmin
              cases ominor with
              | none => exact absurd hQmin (by simp [OptDen])
              | some minor =>
                refine SimAt.bind (ih.annotate hs₆
                  (denote_mono (hext₅.trans hext₆) hfid)
                  hwfi) (fun s₇ fi' fi'x hs₇ hext₇ hPfi' => ?_)
                obtain ⟨hfi'd, hwfi'⟩ := hPfi'
                refine SimAt.bind (ih.infer hs₇ hfi'd hwfi')
                  (fun s₈ tfi tfix hs₈ hext₈ hPtfi => ?_)
                obtain ⟨htfid, hwtfi⟩ := hPtfi
                refine SimAt.bind (ensureSortI_sim ih hs₈ htfid hwtfi)
                  (fun s₉ sfi sfi' hs₉ hext₉ hPsfi => ?_)
                obtain rfl : sfi = sfi' := hPsfi
                have hext₀₉ :=
                  ((((((hext₁.trans hext₂).trans hext₃).trans
                    hext₄).trans hext₅).trans hext₆).trans
                    ((hext₇.trans hext₈).trans hext₉))
                have hteN := denote_mono hext₀₉ hte
                have hdeN := denote_mono hext₀₉ hde
                have hfiN := denote_mono
                  ((((hext₅.trans hext₆).trans hext₇).trans
                    hext₈).trans hext₉) hfid
                have hminN : s₉.store.denote minor = some minorx :=
                  hQmin.mono ((hext₇.trans hext₈).trans hext₉)
                have hparamsN := hparams.mono
                  (hext₀₉.trans (Ext.refl _))
                cases sp with
                | true =>
                  simp only [↓reduceIte]
                  refine SimAt.bind (SimAt.liftFueled _ _ hs₉)
                    (fun s₁₀ ok ok' hs₁₀ hext₁₀ hPok => ?_)
                  obtain rfl : ok = ok' := hPok
                  cases ok with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact SimAt.throw_bind
                  | true =>
                    simp only [↓reduceIte]
                    exact annotateProjRecI_rest ih hs₁₀
                      (denote_mono hext₁₀ hteN)
                      (denote_mono hext₁₀ hdeN)
                      (denote_mono hext₁₀ hfiN)
                      (denote_mono hext₁₀ hminN)
                      (hparamsN.mono hext₁₀)
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact annotateProjRecI_rest ih hs₉ hteN hdeN hfiN
                    hminN hparamsN
      · exact SimAt.throw
    | axiomInfo cv => exact SimAt.throw
    | defnInfo cv v h => exact SimAt.throw
    | thmInfo cv v => exact SimAt.throw
    | indInfo cv caps => exact SimAt.throw
    | recInfo cv mI rP rules => exact SimAt.throw
    | projInfo entry' => exact SimAt.throw

end Walks2

section Walks3

variable {env : Env} {f : Nat}

set_option maxHeartbeats 8000000 in
theorem annotateProjElimI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {sn : Name} {ip : Nat} {te e' : EIdx} {tex e'x : Expr}
    {s₀ : IState} (hs : ISOK env s₀)
    (hte : s₀.store.denote te = some tex)
    (hde : s₀.store.denote e' = some e'x)
    (hwte : WScoped d tex) (hwe : WScoped d e'x) :
    SimAt env s₀ (RelE d)
      (annotateProjElimI (coreKnotI (mkFEnv env) f) (mkFEnv env) d sn
        ip te e')
      (annotateProjElim (fueledFns env) env d sn ip tex e'x) := by
  unfold annotateProjElimI
  unfold annotateProjElim
  refine SimAt.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hs.wf hte)
  rw [hn]
  cases n with
  | const T us =>
    rw [← Option.some.inj hd]
    dsimp only
    by_cases hT : T = sn
    · rw [if_pos hT, if_pos hT]
      rw [mkFEnv_find?]
      cases hfp : env.find? (projFnName T ip) with
      | none =>
        rw [mkFEnv_find?]
        exact SimAt.throw
      | some ci =>
        cases ci with
        | recInfo cvp mI rP rules =>
          try dsimp only
          refine SimAt.withStore ?_
          have htargs := getAppArgsI_spec hs.wf hte
          rw [htargs.length_eq]
          split
          · have hcn : denoteNode s₀.store.denote
                (ENode.const (projFnName T ip) us)
                = some (.const (projFnName T ip) us) := rfl
            refine SimAt.bind_left (internI_eff hs hcn)
              (fun s₁ h hs₁ hext₁ hQh => ?_)
            refine SimAt.bind_left (mkAppNM_eff hs₁ hQh
              ((htargs.mono hext₁).append
                (DenL.cons (denote_mono hext₁ hde) DenL.nil)))
              (fun s₂ raw hs₂ hext₂ hQraw => ?_)
            refine SimAt.withStore ?_
            rw [wscopedBI_spec hs₂.wf hQraw,
              looseBVarsBoundedI_spec hs₂.wf hQraw,
              leafGuardI_spec hs₂.wf hQraw
                (denote_mono (hext₁.trans hext₂) hde)]
            try dsimp only
            split
            · rename_i hguard
              exact ih.annotate hs₂ hQraw (WScoped.of_wscopedB
                (by simp only [Bool.and_eq_true] at hguard
                    exact hguard.1.1))
            · exact SimAt.throw
          · exact SimAt.throw
        | projInfo entry =>
          try dsimp only
          cases hnat : entry.native with
          | true =>
            simp only [↓reduceIte]
            exact SimAt.throw
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact annotateProjRecI_sim ih henv hs hte hde hwte hwe
        | axiomInfo cv => exact SimAt.throw
        | defnInfo cv v h => exact SimAt.throw
        | thmInfo cv v => exact SimAt.throw
        | indInfo cv caps => exact SimAt.throw
        | ctorInfo cv nP nF => exact SimAt.throw
    · rw [if_neg hT, if_neg hT]
      exact SimAt.throw
  | bvar k => invert_head hd; exact SimAt.throw
  | sort u => invert_head hd; exact SimAt.throw
  | lit l => invert_head hd; exact SimAt.throw
  | fvar idx nm t => invert_head hd; exact SimAt.throw
  | app f' a' => invert_head hd; exact SimAt.throw
  | lam nm t b m => invert_head hd; exact SimAt.throw
  | forallE nm t b m => invert_head hd; exact SimAt.throw
  | letE nm t v b => invert_head hd; exact SimAt.throw
  | proj s' j' e'' => invert_head hd; exact SimAt.throw

set_option maxHeartbeats 8000000 in
theorem annotateBodyI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some ex) (hw : WScoped d ex) :
    SimAt env s₀ (RelE d)
      (annotateBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (annotateBody (fueledFns env) env d ex) := by
  unfold annotateBodyI
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hden
  rw [hn]
  cases n with
  | bvar k =>
    cases hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | sort u =>
    cases hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | const nm us =>
    cases hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | letE nm t v b =>
    invert_node hd
    exact SimAt.throw
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    subst hd
    have h' : idx < d ∧ WScoped idx tyx := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    by_cases hidx : idx < d
    · simp only [hidx, ↓reduceIte]
      exact SimAt.pure hs ⟨hden, hw⟩
    · simp only [hidx, ↓reduceIte]
      exact SimAt.throw
  | lit l =>
    cases hd
    unfold annotateBody
    try dsimp only
    cases l with
    | natVal k =>
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · simp only [hg, ↓reduceIte]
        exact SimAt.pure hs ⟨hden, hw⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        exact SimAt.throw
    | strVal str =>
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · simp only [hg, ↓reduceIte]
        exact SimAt.pure hs ⟨hden, hw⟩
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        exact SimAt.throw
  | app g' a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨xg, hg, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨xa, ha, hd⟩ := hd
    subst hd
    have hwfa : WScoped d xg ∧ WScoped d xa := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hg hwfa.1)
      (fun s₁ f' f'x hs₁ hext₁ hP => ?_)
    obtain ⟨hf'd, hwf'⟩ := hP
    refine SimAt.bind (ih.annotate hs₁ (denote_mono hext₁ ha) hwfa.2)
      (fun s₂ a' a'x hs₂ hext₂ hP₂ => ?_)
    obtain ⟨ha'd, hwa'⟩ := hP₂
    refine SimAt.bind (ih.infer hs₂ (denote_mono hext₂ hf'd) hwf')
      (fun s₃ tf tfx hs₃ hext₃ hP₃ => ?_)
    obtain ⟨htfd, hwtf⟩ := hP₃
    refine SimAt.bind (ih.whnf hs₃ htfd hwtf)
      (fun s₄ w wx hs₄ hext₄ hP₄ => ?_)
    obtain ⟨hwd, hww⟩ := hP₄
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
      refine SimAt.bind (ih.infer hs₄
        (denote_mono (hext₃.trans hext₄) ha'd) hwa')
        (fun s₅ ta tax hs₅ hext₅ hP₅ => ?_)
      obtain ⟨htad, hwta⟩ := hP₅
      refine SimAt.bind (ih.defeq hs₅ htad
        (denote_mono hext₅ hty) hwta hwtb.1)
        (fun s₆ b b' hs₆ hext₆ hPb => ?_)
      obtain rfl : b = b' := hPb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimAt.throw_bind
      | true =>
        simp only [↓reduceIte]
        refine SimAt.of_eff (internI_eff hs₆ (x := .app f'x a'x) ?_) _
          (fun s r hQ => ?_)
        · rw [denoteNode,
            denote_mono ((((hext₂.trans hext₃).trans hext₄).trans
              hext₅).trans hext₆) hf'd,
            denote_mono (((hext₃.trans hext₄).trans hext₅).trans
              hext₆) ha'd]
          rfl
        · refine ⟨hQ, ?_⟩
          simp only [WScoped]
          exact ⟨hwf', hwa'⟩
    | bvar k => invert_node hd'; exact SimAt.throw
    | sort u => invert_node hd'; exact SimAt.throw
    | const nm' us => invert_node hd'; exact SimAt.throw
    | lit l => invert_node hd'; exact SimAt.throw
    | fvar idx nm' t' => invert_node hd'; exact SimAt.throw
    | app f₂ a₂ => invert_node hd'; exact SimAt.throw
    | lam nm' t' b' m' => invert_node hd'; exact SimAt.throw
    | letE nm' t' v' b' => invert_node hd'; exact SimAt.throw
    | proj s' j' e'' => invert_node hd'; exact SimAt.throw
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hty hwtb.1)
      (fun s₁ ty' ty'x hs₁ hext₁ hP => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP
    have hfvd : denoteNode s₁.store.denote (.fvar d nm ty')
        = some (.fvar d nm ty'x) := by
      rw [denoteNode, hty'd]; rfl
    refine SimAt.bind_left (internI_eff hs₁ hfvd)
      (fun s₂ fv hs₂ hext₂ hQfv => ?_)
    refine SimAt.bind_left (inst1M_eff hs₂
      (denote_mono (hext₁.trans hext₂) hbody) hQfv)
      (fun s₃ ob hs₃ hext₃ hQob => ?_)
    refine SimAt.bind (ih.annotate hs₃ hQob
      (WScoped.instantiate1 hwty' 0 hwtb.2))
      (fun s₄ body' body'x hs₄ hext₄ hP₄ => ?_)
    obtain ⟨hbody'd, hwbody'⟩ := hP₄
    refine SimAt.bind (ih.infer hs₄ hbody'd hwbody')
      (fun s₅ tb tbx hs₅ hext₅ hP₅ => ?_)
    obtain ⟨htbd, hwtb'⟩ := hP₅
    refine SimAt.bind (ensureSortI_sim ih hs₅ htbd hwtb')
      (fun s₆ v v' hs₆ hext₆ hPv => ?_)
    obtain rfl : v = v' := hPv
    refine SimAt.bind_left (abstract1M_eff hs₆
      (denote_mono (hext₅.trans hext₆) hbody'd))
      (fun s₇ bAbs hs₇ hext₇ hQabs => ?_)
    refine SimAt.of_eff (internI_eff hs₇
      (x := .forallE nm ty'x (body'x.abstract1 d) ⟨m.bi, some v⟩) ?_) _
      (fun s r hQ => ?_)
    · rw [denoteNode,
        denote_mono (((((hext₂.trans hext₃).trans hext₄).trans
          hext₅).trans hext₆).trans hext₇) hty'd, hQabs]
      rfl
    · refine ⟨hQ, ?_⟩
      simp only [WScoped]
      exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hty hwtb.1)
      (fun s₁ ty' ty'x hs₁ hext₁ hP => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP
    have hfvd : denoteNode s₁.store.denote (.fvar d nm ty')
        = some (.fvar d nm ty'x) := by
      rw [denoteNode, hty'd]; rfl
    refine SimAt.bind_left (internI_eff hs₁ hfvd)
      (fun s₂ fv hs₂ hext₂ hQfv => ?_)
    refine SimAt.bind_left (inst1M_eff hs₂
      (denote_mono (hext₁.trans hext₂) hbody) hQfv)
      (fun s₃ ob hs₃ hext₃ hQob => ?_)
    refine SimAt.bind (ih.annotate hs₃ hQob
      (WScoped.instantiate1 hwty' 0 hwtb.2))
      (fun s₄ body' body'x hs₄ hext₄ hP₄ => ?_)
    obtain ⟨hbody'd, hwbody'⟩ := hP₄
    refine SimAt.bind (ih.infer hs₄ hbody'd hwbody')
      (fun s₅ bt btx hs₅ hext₅ hP₅ => ?_)
    obtain ⟨hbtd, hwbt⟩ := hP₅
    refine SimAt.bind (ih.infer hs₅ hbtd hwbt)
      (fun s₆ tbt tbtx hs₆ hext₆ hP₆ => ?_)
    obtain ⟨htbtd, hwtbt⟩ := hP₆
    refine SimAt.bind (ensureSortI_sim ih hs₆ htbtd hwtbt)
      (fun s₇ v v' hs₇ hext₇ hPv => ?_)
    obtain rfl : v = v' := hPv
    refine SimAt.bind_left (abstract1M_eff hs₇
      (denote_mono ((hext₅.trans hext₆).trans hext₇) hbody'd))
      (fun s₈ bAbs hs₈ hext₈ hQabs => ?_)
    refine SimAt.of_eff (internI_eff hs₈
      (x := .lam nm ty'x (body'x.abstract1 d) ⟨m.bi, some v⟩) ?_) _
      (fun s r hQ => ?_)
    · rw [denoteNode,
        denote_mono ((((((hext₂.trans hext₃).trans hext₄).trans
          hext₅).trans hext₆).trans hext₇).trans hext₈) hty'd, hQabs]
      rfl
    · refine ⟨hQ, ?_⟩
      simp only [WScoped]
      exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | proj sn ip pe =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨pex, hpe, hd⟩ := hd
    subst hd
    have hwpe : WScoped d pex := by simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hpe hwpe)
      (fun s₁ e' e'x hs₁ hext₁ hP => ?_)
    obtain ⟨he'd, hwe'⟩ := hP
    refine SimAt.bind (ih.infer hs₁ he'd hwe')
      (fun s₂ tpe tpex hs₂ hext₂ hP₂ => ?_)
    obtain ⟨htped, hwtpe⟩ := hP₂
    refine SimAt.bind (ih.whnf hs₂ htped hwtpe)
      (fun s₃ te tex hs₃ hext₃ hP₃ => ?_)
    obtain ⟨hted, hwte⟩ := hP₃
    refine SimAt.withStore ?_
    obtain ⟨n', hn', hc', hd'⟩ :=
      denote_some_inv (getAppFnI_spec hs₃.wf hted)
    rw [hn']
    cases n' with
    | const T us =>
      rw [← Option.some.inj hd']
      dsimp only
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? T ip with
      | none =>
        exact annotateProjElimI_sim ih henv hs₃ hted
          (denote_mono (hext₂.trans hext₃) he'd)
          hwte hwe'
      | some entry =>
        dsimp only
        cases hnat : entry.native with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact annotateProjElimI_sim ih henv hs₃ hted
            (denote_mono (hext₂.trans hext₃) he'd)
            hwte hwe'
        | true =>
          simp only [↓reduceIte]
          refine SimAt.withStore ?_
          have htargs := getAppArgsI_spec hs₃.wf hted
          rw [htargs.length_eq]
          by_cases hlen : tex.getAppArgs.length = entry.numParams
          · rw [if_pos hlen, if_pos hlen]
            refine SimAt.of_eff (internI_eff hs₃
              (x := .proj T ip e'x) ?_) _ (fun s r hQ => ?_)
            · rw [denoteNode, denote_mono
                (hext₂.trans hext₃) he'd]
              rfl
            · refine ⟨hQ, ?_⟩
              simp only [WScoped]
              exact hwe'
          · rw [if_neg hlen, if_neg hlen]
            exact SimAt.throw
    | bvar k =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | sort u =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | lit l =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | fvar idx nm' t' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | app f₂ a₂ =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | lam nm' t' b' m' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | forallE nm' t' b' m' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | letE nm' t' v' b' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | proj s' j' e'' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃ hted
        (denote_mono (hext₂.trans hext₃) he'd) hwte hwe'

end Walks3

end Setlec
