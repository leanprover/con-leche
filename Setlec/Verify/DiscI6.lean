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
    (hden : s₀.store.denoteT i = some ty) (hw : WScoped d ty) :
    SimAt env s₀ RelV
      (isPropTypeI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (isPropType (fueledFns env) env d ty) := by
  show SimAt env s₀ RelV
    ((coreKnotI (mkFEnv env) f).annotate d i >>= fun ty' =>
      (coreKnotI (mkFEnv env) f).infer d ty' >>= fun tty =>
      ensureSortI (coreKnotI (mkFEnv env) f) d tty >>= fun s =>
      internLM .zero >>= fun z =>
      isEquivLM s z >>= fun o =>
      liftFueled "level comparison" o)
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
    (fun s₃ u lu hs₃ hext₃ hPu => ?_)
  refine SimAt.bind_left (internLM_eff hs₃ (n := .zero) rfl)
    (fun s₃z z hs₃z hext₃z hz => ?_)
  refine SimAt.bind_left (isEquivLM_eff hs₃z
    (denoteL_mono hext₃z hPu) hz)
    (fun s₃o o hs₃o hext₃o ho => ?_)
  subst ho
  exact SimAt.liftFueled _ _ hs₃o

theorem projFieldDomI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {structProp : Bool} {sn : NIdx} {snx : Name}
    {e' : EIdx} {e'x : Expr}
    (hwe : WScoped d e'x) :
    ∀ (k j : Nat) {tel : EIdx} {telx : Expr} {s₀ : IState},
      ISOK env s₀ → s₀.store.denoteN sn = some snx →
      s₀.store.denoteT e' = some e'x →
      s₀.store.denoteT tel = some telx → WScoped d telx →
      SimAt env s₀ (RelE d)
        (projFieldDomI (coreKnotI (mkFEnv env) f) (mkFEnv env) d
          structProp sn e' j k tel)
        (projFieldDom (fueledFns env) env d structProp snx e'x j k
          telx)
  | 0, jj, tel, telx, s₀, hs, hsn, hde, hdt, hwtel => by
    unfold projFieldDomI
    refine SimAt.view ?_
    obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hdt
    rw [hn]
    cases n with
    | forallE nmᵢ dom rest mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨domx, hdom, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨restx, hrest, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bm, hbmDen, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nm, hnmDen, hd⟩ := hd
      subst hd
      have hw' : WScoped d domx ∧ WScoped d restx := by
        simpa only [WScoped] using hwtel
      exact SimAt.pure hs ⟨hdom, hw'.1⟩
    | bvar k => cases hd; exact SimAt.throw
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lu, _, rfl⟩ := hd
      exact SimAt.throw
    | const nmᵢ us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨lus, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nm, hnmDen, rfl⟩ := hd
      exact SimAt.throw
    | lit l => cases hd; exact SimAt.throw
    | fvar idx nmᵢ t => invert_node hd; exact SimAt.throw

    | app f' a' => invert_node hd; exact SimAt.throw
    | lam nmᵢ t b m => invert_node hd; exact SimAt.throw

    | letE nmᵢ t v b => invert_node hd; exact SimAt.throw

    | proj s'ᵢ j' e'' => invert_node hd; exact SimAt.throw

  | k + 1, jj, tel, telx, s₀, hs, hsn, hde, hdt, hwtel => by
    unfold projFieldDomI
    refine SimAt.view ?_
    obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hdt
    rw [hn]
    cases n with
    | forallE nmᵢ dom rest mb =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨domx, hdom, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨restx, hrest, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨bm, hbmDen, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nm, hnmDen, hd⟩ := hd
      subst hd
      have hw' : WScoped d domx ∧ WScoped d restx := by
        simpa only [WScoped] using hwtel
      have hwrest' : WScoped d (restx.instantiate1 (.proj snx jj e'x)) :=
        WScoped.instantiate1_gen
          (show WScoped d (.proj snx jj e'x) by
            simpa only [WScoped] using hwe) 0 hw'.2
      dsimp only [projFieldDom]
      refine SimAt.withStore ?_
      rw [looseBVarsBoundedI_spec hs.wf hrest]
      by_cases hcl : restx.looseBVarsBounded 0 = true
      · rw [if_pos hcl, if_pos hcl]
        exact projFieldDomI_sim ih henv hwe k (jj + 1) hs hsn hde
          hrest hw'.2
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
            have hpj : denoteNode s₁.store.denoteT s₁.store.denoteL
                s₁.store.denoteN (.proj sn jj e')
                = some (.proj snx jj e'x) := by
              rw [denoteNode, denoteT_mono hext₁ hde,
                denoteN_mono hext₁ hsn]; rfl
            refine SimAt.bind_left (internI_eff hs₁ hpj)
              (fun s₂ pj hs₂ hext₂ hQpj => ?_)
            refine SimAt.bind_left (inst1M_eff hs₂
              (denoteT_mono (hext₁.trans hext₂) hrest) hQpj)
              (fun s₃ rest' hs₃ hext₃ hQr => ?_)
            exact projFieldDomI_sim ih henv hwe k (jj + 1) hs₃
              (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hsn)
              (denoteT_mono ((hext₁.trans hext₂).trans hext₃) hde)
              hQr hwrest'
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hpj : denoteNode s₀.store.denoteT s₀.store.denoteL
              s₀.store.denoteN (.proj sn jj e')
              = some (.proj snx jj e'x) := by
            rw [denoteNode, hde, hsn]; rfl
          refine SimAt.bind_left (internI_eff hs hpj)
            (fun s₂ pj hs₂ hext₂ hQpj => ?_)
          refine SimAt.bind_left (inst1M_eff hs₂
            (denoteT_mono hext₂ hrest) hQpj)
            (fun s₃ rest' hs₃ hext₃ hQr => ?_)
          exact projFieldDomI_sim ih henv hwe k (jj + 1) hs₃
            (denoteN_mono (hext₂.trans hext₃) hsn)
            (denoteT_mono (hext₂.trans hext₃) hde) hQr hwrest'
    | bvar k' => cases hd; exact SimAt.throw
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lu, _, rfl⟩ := hd
      exact SimAt.throw
    | const nmᵢ us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨lus, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨nm, hnmDen, rfl⟩ := hd
      exact SimAt.throw
    | lit l => cases hd; exact SimAt.throw
    | fvar idx nmᵢ t => invert_node hd; exact SimAt.throw

    | app f' a' => invert_node hd; exact SimAt.throw
    | lam nmᵢ t b m => invert_node hd; exact SimAt.throw

    | letE nmᵢ t v b => invert_node hd; exact SimAt.throw

    | proj s'ᵢ j' e'' => invert_node hd; exact SimAt.throw

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The shared reduct tail of the Prop-projection fallback: build the
recursor elimination and re-annotate it under the scope guard. -/
private theorem annotateProjRecI_rest (ih : SSimI env f)
    {d : Nat} {entry : ProjEntry} {te e' fi minor : EIdx}
    {params : List EIdx} {tex e'x fix minorx : Expr}
    {paramsx : List Expr} {us uf : List LIdx} {lus luf : List Level}
    {s₀ : IState}
    (hs : ISOK env s₀)
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (huf : denoteLList s₀.store.denoteL uf = some luf)
    (hte : s₀.store.denoteT te = some tex)
    (hde : s₀.store.denoteT e' = some e'x)
    (hfi : s₀.store.denoteT fi = some fix)
    (hmin : s₀.store.denoteT minor = some minorx)
    (hparams : DenL s₀.store params paramsx) :
    SimAt env s₀ (RelE d)
      (internNameM (entry.structName.str "rec") >>= fun recI =>
       internI (.const recI (uf ++ us)) >>=
        fun recC =>
       internNameM (.str .anonymous "t") >>= fun tI =>
       internI (.lam tI te fi ⟨.default⟩) >>=
        fun motive =>
       mkAppNM recC (params ++ [motive, minor, e']) >>= fun raw =>
       Setlec.withStore (fun st => st.wscopedBI d raw &&
         st.looseBVarsBoundedI 0 raw &&
         st.leafGuardI raw e') >>= fun g =>
       if g then (coreKnotI (mkFEnv env) f).annotate d raw
       else throw (.notImplemented "projection elimination scoping"))
      (let raw := Expr.mkAppN
          (.const (entry.structName.str "rec") (luf ++ lus))
          (paramsx ++ [.lam (.str .anonymous "t") tex fix
            ⟨.default⟩, minorx, e'x])
        if raw.wscopedB d && raw.looseBVarsBounded 0 &&
            raw.fvarLeaves.all
              (fun l => e'x.fvarLeaves.contains l) then
          (fueledFns env).annotate d raw
        else throw (.notImplemented "projection elimination scoping")) := by
  refine SimAt.bind_left
    (internNameM_eff hs (entry.structName.str "rec"))
    (fun s₀r recI hs hext₀r hQrecI => ?_)
  replace hus := denoteLList_mono hext₀r hus
  replace huf := denoteLList_mono hext₀r huf
  replace hte := denoteT_mono hext₀r hte
  replace hde := denoteT_mono hext₀r hde
  replace hfi := denoteT_mono hext₀r hfi
  replace hmin := denoteT_mono hext₀r hmin
  replace hparams := hparams.mono hext₀r
  have hcn : denoteNode s₀r.store.denoteT s₀r.store.denoteL
      s₀r.store.denoteN
      (ENode.const recI (uf ++ us))
      = some (.const (entry.structName.str "rec") (luf ++ lus)) := by
    rw [denoteNode, denoteLList_append huf hus, hQrecI]
    rfl
  refine SimAt.bind_left (internI_eff hs hcn)
    (fun s₁ recC hs₁ hext₁ hQrec => ?_)
  refine SimAt.bind_left (internNameM_eff hs₁ (.str .anonymous "t"))
    (fun s₁t tI hs₁ hext₁t hQtI => ?_)
  replace hQrec := denoteT_mono hext₁t hQrec
  replace hext₁ := hext₁.trans hext₁t
  have hmot : denoteNode s₁t.store.denoteT s₁t.store.denoteL
      s₁t.store.denoteN
      (ENode.lam tI te fi ⟨.default⟩)
      = some (.lam (.str .anonymous "t") tex fix ⟨.default⟩) := by
    rw [denoteNode, denoteT_mono hext₁ hte, denoteT_mono hext₁ hfi, hQtI]
    rfl
  refine SimAt.bind_left (internI_eff hs₁ hmot)
    (fun s₂ motive hs₂ hext₂ hQmot => ?_)
  refine SimAt.bind_left (mkAppNM_eff hs₂
    (denoteT_mono hext₂ hQrec)
    ((hparams.mono (hext₁.trans hext₂)).append
      (DenL.cons hQmot (DenL.cons
        (denoteT_mono (hext₁.trans hext₂) hmin)
        (DenL.cons (denoteT_mono (hext₁.trans hext₂) hde) DenL.nil)))))
    (fun s₃ raw hs₃ hext₃ hQraw => ?_)
  refine SimAt.withStore ?_
  rw [wscopedBI_spec hs₃.wf hQraw, looseBVarsBoundedI_spec hs₃.wf hQraw,
    leafGuardI_spec hs₃.wf hQraw
      (denoteT_mono ((hext₁.trans hext₂).trans hext₃) hde)]
  dsimp only
  split
  · rename_i hguard
    exact ih.annotate hs₃ hQraw (WScoped.of_wscopedB
      (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1))
  · exact SimAt.throw

set_option maxHeartbeats 8000000 in
theorem annotateProjRecI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {entry : ProjEntry} {ip : Nat} {te e' : EIdx}
    {tex e'x : Expr} {us : List LIdx} {lus : List Level} {s₀ : IState}
    (hs : ISOK env s₀)
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (hte : s₀.store.denoteT te = some tex)
    (hde : s₀.store.denoteT e' = some e'x)
    (hwte : WScoped d tex) (hwe : WScoped d e'x) :
    SimAt env s₀ (RelE d)
      (annotateProjRecI (coreKnotI (mkFEnv env) f) (mkFEnv env) d entry
        ip te e' us)
      (annotateProjRec (fueledFns env) env d entry ip tex e'x lus) := by
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
      · refine SimAt.bind_left (internNameM_eff hs entry.ctor)
          (fun s₀c ctorI hs hext₀c hQctorI => ?_)
        refine SimAt.bind_left (constTyAtM_eff hs hQctorI
          (denoteLList_mono hext₀c hus) hfC)
          (fun s₁ ctorTy hs₁ hext₁' hQty => ?_)
        have hext₁ := hext₀c.trans hext₁'
        simp only [ConstantInfo.toConstantVal] at hQty
        refine SimAt.bind_left (piResidualM_eff hs₁ hQty
          (hparams.mono hext₁)) (fun s₂ otel hs₂ hext₂ hQtel => ?_)
        rw [instPis_eq_piResidual]
        cases htel : piResidual
            (cvC.type.instantiateLevelParams cvC.levelParams lus)
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
              (denoteT_mono (hext₁.trans hext₂) hte) hwte)
              (fun s₃ sp sp' hs₃ hext₃ hPsp => ?_)
            obtain rfl : sp = sp' := hPsp
            refine SimAt.bind_left
              (internNameM_eff hs₃ entry.structName)
              (fun s₃n snI hs₃ hext₃n hQsnI => ?_)
            replace hext₃ := hext₃.trans hext₃n
            refine SimAt.bind (projFieldDomI_sim ih henv hwe ip 0 hs₃
              hQsnI
              (denoteT_mono ((hext₁.trans hext₂).trans hext₃) hde)
              (denoteT_mono hext₃ hQtel) hwtel)
              (fun s₄ fi fix hs₄ hext₄ hPfi => ?_)
            obtain ⟨hfid, hwfi⟩ := hPfi
            have hbv : denoteNode s₄.store.denoteT s₄.store.denoteL s₄.store.denoteN (.bvar (cnF - 1 - ip))
                = some (.bvar (cnF - 1 - ip)) := rfl
            refine SimAt.bind_left (internI_eff hs₄ hbv)
              (fun s₅ fieldBvar hs₅ hext₅ hQbv => ?_)
            refine SimAt.bind_left (pisToLamsM_eff (k := cnF) hs₅
              (denoteT_mono ((hext₃.trans hext₄).trans hext₅) hQtel)
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
                  (denoteT_mono (hext₅.trans hext₆) hfid)
                  hwfi) (fun s₇ fi' fi'x hs₇ hext₇ hPfi' => ?_)
                obtain ⟨hfi'd, hwfi'⟩ := hPfi'
                refine SimAt.bind (ih.infer hs₇ hfi'd hwfi')
                  (fun s₈ tfi tfix hs₈ hext₈ hPtfi => ?_)
                obtain ⟨htfid, hwtfi⟩ := hPtfi
                refine SimAt.bind (ensureSortI_sim ih hs₈ htfid hwtfi)
                  (fun s₉ sfi lsfi hs₉ hext₉ hPsfi => ?_)
                have hext₀₉ :=
                  ((((((hext₁.trans hext₂).trans hext₃).trans
                    hext₄).trans hext₅).trans hext₆).trans
                    ((hext₇.trans hext₈).trans hext₉))
                have hteN := denoteT_mono hext₀₉ hte
                have hdeN := denoteT_mono hext₀₉ hde
                have hfiN := denoteT_mono
                  ((((hext₅.trans hext₆).trans hext₇).trans
                    hext₈).trans hext₉) hfid
                have hminN : s₉.store.denoteT minor = some minorx :=
                  hQmin.mono ((hext₇.trans hext₈).trans hext₉)
                have hparamsN := hparams.mono
                  (hext₀₉.trans (Ext.refl _))
                have husN : denoteLList s₉.store.denoteL us
                    = some lus := denoteLList_mono hext₀₉ hus
                cases sp with
                | true =>
                  simp only [↓reduceIte]
                  refine SimAt.bind_left (internLM_eff hs₉
                    (n := .zero) rfl)
                    (fun s₉z z hs₉z hext₉z hz => ?_)
                  refine SimAt.bind_left (isEquivLM_eff hs₉z
                    (denoteL_mono hext₉z hPsfi) hz)
                    (fun s₉o o hs₉o hext₉o ho => ?_)
                  subst ho
                  refine SimAt.bind (SimAt.liftFueled _ _ hs₉o)
                    (fun s₁₀ ok ok' hs₁₀ hext₁₀ hPok => ?_)
                  obtain rfl : ok = ok' := hPok
                  have hextZ := (hext₉z.trans hext₉o).trans hext₁₀
                  cases ok with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact SimAt.throw_bind
                  | true =>
                    simp only [↓reduceIte]
                    exact annotateProjRecI_rest ih hs₁₀
                      (denoteLList_mono hextZ husN)
                      (by
                        by_cases hel : entry.recExtraLevel <;>
                          simp [hel, denoteLList,
                            denoteL_mono hextZ
                              (show s₉.store.denoteL sfi = some lsfi
                                from hPsfi)])
                      (denoteT_mono hextZ hteN)
                      (denoteT_mono hextZ hdeN)
                      (denoteT_mono hextZ hfiN)
                      (denoteT_mono hextZ hminN)
                      (hparamsN.mono hextZ)
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact annotateProjRecI_rest ih hs₉ husN
                    (by
                      by_cases hel : entry.recExtraLevel <;>
                        simp [hel, denoteLList,
                          show s₉.store.denoteL sfi = some lsfi
                            from hPsfi])
                    hteN hdeN hfiN hminN hparamsN
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
    {d : Nat} {sn : NIdx} {snx : Name} {ip : Nat} {te e' : EIdx}
    {tex e'x : Expr}
    {s₀ : IState} (hs : ISOK env s₀)
    (hsn : s₀.store.denoteN sn = some snx)
    (hte : s₀.store.denoteT te = some tex)
    (hde : s₀.store.denoteT e' = some e'x)
    (hwte : WScoped d tex) (hwe : WScoped d e'x) :
    SimAt env s₀ (RelE d)
      (annotateProjElimI (coreKnotI (mkFEnv env) f) (mkFEnv env) d sn
        ip te e')
      (annotateProjElim (fueledFns env) env d snx ip tex e'x) := by
  unfold annotateProjElimI
  unfold annotateProjElim
  refine SimAt.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv (getAppFnI_spec hs.wf hte)
  rw [hn]
  cases n with
  | const Tᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, hlusDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨T, hTDen, hd⟩ := hd
    rw [← hd]
    dsimp only
    refine SimAt.bind_left (readbackNM_eff hs hTDen)
      (fun s₀T Tw hs hextT hTw => ?_)
    subst Tw
    replace hte := denoteT_mono hextT hte
    replace hde := denoteT_mono hextT hde
    replace hlusDen := denoteLList_mono hextT hlusDen
    replace hTDen := denoteN_mono hextT hTDen
    replace hsn := denoteN_mono hextT hsn
    by_cases hT : T = snx
    · rw [if_pos (show Tᵢ = sn from
          (denoteN_eq_iff hs.wf hTDen hsn).mpr hT), if_pos hT]
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
          · refine SimAt.bind_left (projFnIdxM_eff hs hTDen ip)
              (fun s₀p pf hs hextp hQpf => ?_)
            replace hte := denoteT_mono hextp hte
            replace hde := denoteT_mono hextp hde
            replace hlusDen := denoteLList_mono hextp hlusDen
            replace htargs := htargs.mono hextp
            have hcn : denoteNode s₀p.store.denoteT s₀p.store.denoteL
                s₀p.store.denoteN
                (ENode.const pf us)
                = some (.const (projFnName T ip) lus) := by
              rw [denoteNode, hlusDen, hQpf]
              rfl
            refine SimAt.bind_left (internI_eff hs hcn)
              (fun s₁ h hs₁ hext₁ hQh => ?_)
            refine SimAt.bind_left (mkAppNM_eff hs₁ hQh
              ((htargs.mono hext₁).append
                (DenL.cons (denoteT_mono hext₁ hde) DenL.nil)))
              (fun s₂ raw hs₂ hext₂ hQraw => ?_)
            refine SimAt.withStore ?_
            rw [wscopedBI_spec hs₂.wf hQraw,
              looseBVarsBoundedI_spec hs₂.wf hQraw,
              leafGuardI_spec hs₂.wf hQraw
                (denoteT_mono (hext₁.trans hext₂) hde)]
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
            exact annotateProjRecI_sim ih henv hs hlusDen hte hde hwte hwe
        | axiomInfo cv => exact SimAt.throw
        | defnInfo cv v h => exact SimAt.throw
        | thmInfo cv v => exact SimAt.throw
        | indInfo cv caps => exact SimAt.throw
        | ctorInfo cv nP nF => exact SimAt.throw
    · rw [if_neg (show ¬ Tᵢ = sn from fun h =>
          hT ((denoteN_eq_iff hs.wf hTDen hsn).mp h)), if_neg hT]
      exact SimAt.throw
  | bvar k => invert_head hd; exact SimAt.throw
  | sort u => invert_head hd; exact SimAt.throw
  | lit l => invert_head hd; exact SimAt.throw
  | fvar idx nmᵢ t => invert_head hd; exact SimAt.throw

  | app f' a' => invert_head hd; exact SimAt.throw
  | lam nmᵢ t b m => invert_head hd; exact SimAt.throw

  | forallE nmᵢ t b m => invert_head hd; exact SimAt.throw

  | letE nmᵢ t v b => invert_head hd; exact SimAt.throw

  | proj s'ᵢ j' e'' => invert_head hd; exact SimAt.throw


set_option maxHeartbeats 8000000 in
theorem annotateBodyI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denoteT i = some ex) (hw : WScoped d ex) :
    SimAt env s₀ (RelE d)
      (annotateBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (annotateBody (fueledFns env) env d ex) := by
  unfold annotateBodyI
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denoteT_some_inv hden
  rw [hn]
  cases n with
  | bvar k =>
    cases hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | const nmᵢ us =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, rfl⟩ := hd
    exact SimAt.pure hs ⟨hden, hw⟩
  | letE nmᵢ t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨vx, hv, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    have hwtvb : WScoped d tyx ∧ WScoped d vx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hty hwtvb.1)
      (fun s₁ ty' ty'x hs₁ hext₁ hP₁ => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP₁
    refine SimAt.bind (ih.infer hs₁ hty'd hwty')
      (fun s₂ tty ttyx hs₂ hext₂ hP₂ => ?_)
    obtain ⟨httyd, hwtty⟩ := hP₂
    refine SimAt.bind (ensureSortI_sim ih hs₂ httyd hwtty)
      (fun s₃ u lu hs₃ hext₃ hPu => ?_)
    refine SimAt.bind (ih.annotate hs₃
      (denoteT_mono ((hext₁.trans hext₂).trans hext₃) hv) hwtvb.2.1)
      (fun s₄ v' v'x hs₄ hext₄ hP₄ => ?_)
    obtain ⟨hv'd, hwv'⟩ := hP₄
    refine SimAt.bind (ih.infer hs₄ hv'd hwv')
      (fun s₅ tv tvx hs₅ hext₅ hP₅ => ?_)
    obtain ⟨htvd, hwtv⟩ := hP₅
    refine SimAt.bind (ih.defeq hs₅ htvd
      (denoteT_mono (((hext₂.trans hext₃).trans hext₄).trans hext₅) hty'd)
      hwtv hwty')
      (fun s₆ bb bb' hs₆ hext₆ hPb => ?_)
    obtain rfl : bb = bb' := hPb
    cases bb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.throw_bind
    | true =>
      simp only [↓reduceIte]
      refine SimAt.bind_left (inst1M_eff hs₆
        (denoteT_mono (((((hext₁.trans hext₂).trans hext₃).trans
          hext₄).trans hext₅).trans hext₆) hbody)
        (denoteT_mono (((((hext₁.trans hext₂).trans hext₃).trans
          hext₄).trans hext₅).trans hext₆) hv))
        (fun s₇ ob hs₇ hext₇ hQob => ?_)
      exact ih.annotate hs₇ hQob
        (WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
  | fvar idx nmᵢ t =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
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
    -- structural (task #100 stage 6: the application rule's checks
    -- moved to the driver's inference sweep, so the spine loop is
    -- gone and the clause annotates the two children)
    have hwga : WScoped d xg ∧ WScoped d xa := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hg hwga.1)
      (fun s₁ g'' g''x hs₁ hext₁ hP₁ => ?_)
    obtain ⟨hg''d, hwg''⟩ := hP₁
    refine SimAt.bind (ih.annotate hs₁ (denoteT_mono hext₁ ha) hwga.2)
      (fun s₂ a'' a''x hs₂ hext₂ hP₂ => ?_)
    obtain ⟨ha''d, hwa''⟩ := hP₂
    exact SimAt.of_eff (internI_eff hs₂ (n := .app g'' a'')
      (x := .app g''x a''x) (by
        rw [denoteNode, denoteT_mono hext₂ hg''d, ha''d]; rfl))
      _ (fun s r hQ => ⟨hQ, by
        simp only [WScoped]
        exact ⟨WScoped.mono (Nat.le_refl _) hwg'', hwa''⟩⟩)

  | forallE nmᵢ t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind (ih.annotate hs hty hwtb.1)
      (fun s₁ ty' ty'x hs₁ hext₁ hP => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP
    have hfvd : denoteNode s₁.store.denoteT s₁.store.denoteL s₁.store.denoteN (.fvar d nmᵢ ty')
        = some (.fvar d nm ty'x) := by
      rw [denoteNode, hty'd,
        denoteN_mono hext₁ hnmDen]; rfl
    refine SimAt.bind_left (internI_eff hs₁ hfvd)
      (fun s₂ fv hs₂ hext₂ hQfv => ?_)
    refine SimAt.withStore ?_
    rw [show (m : IBinderMeta).bi = bm.bi from (denoteBM_bi hbmDen).symm]
    exact annotatePisI_tail_sim ih hs₂
      (denoteN_mono (hext₁.trans hext₂) hnmDen)
      (denoteT_mono (hext₁.trans hext₂) hbody)
      (denoteT_mono hext₂ hty'd) hQfv hwty' hwtb.2
  | lam nmᵢ t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨tyx, hty, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bodyx, hbody, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨bm, hbmDen, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨nm, hnmDen, hd⟩ := hd
    subst hd
    have hwtb : WScoped d tyx ∧ WScoped d bodyx := by
      simpa only [WScoped] using hw
    unfold annotateBody
    try dsimp only
    refine SimAt.bind_left (bvarBoundM_eff hs)
      (fun sb bb hsb hextb hQb => ?_)
    by_cases hb0 : bb = 0
    · rw [if_pos hb0]
      subst hb0
      refine SimAt.bind (ih.annotate hsb (denoteT_mono hextb hty) hwtb.1)
        (fun s₁ ty' ty'x hs₁ hext₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      have hfvd : denoteNode s₁.store.denoteT s₁.store.denoteL
          s₁.store.denoteN
          (.fvar d nmᵢ ty') = some (.fvar d nm ty'x) := by
        rw [denoteNode, hty'd,
          denoteN_mono (hextb.trans hext₁) hnmDen]; rfl
      refine SimAt.bind_left (internI_eff hs₁ hfvd)
        (fun s₂ fv hs₂ hext₂ hQfv => ?_)
      refine SimAt.withStore ?_
      rw [show (m : IBinderMeta).bi = bm.bi from (denoteBM_bi hbmDen).symm]
      exact annotateLamsI_tail_sim ih hs₂
        (denoteN_mono ((hextb.trans hext₁).trans hext₂) hnmDen)
        (denoteT_mono ((hextb.trans hext₁).trans hext₂) hbody)
        (denoteT_mono hext₂ hty'd) hQfv hwty' hwtb.2
    · rw [if_neg hb0]
      refine SimAt.bind (ih.annotate hsb (denoteT_mono hextb hty) hwtb.1)
        (fun s₁ ty' ty'x hs₁ hext₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      have hfvd : denoteNode s₁.store.denoteT s₁.store.denoteL
          s₁.store.denoteN (.fvar d nmᵢ ty')
          = some (.fvar d nm ty'x) := by
        rw [denoteNode, hty'd,
          denoteN_mono (hextb.trans hext₁) hnmDen]; rfl
      refine SimAt.bind_left (internI_eff hs₁ hfvd)
        (fun s₂ fv hs₂ hext₂ hQfv => ?_)
      refine SimAt.bind_left (inst1M_eff hs₂
        (denoteT_mono ((hextb.trans hext₁).trans hext₂) hbody) hQfv)
        (fun s₃ ob hs₃ hext₃ hQob => ?_)
      refine SimAt.bind (ih.annotate hs₃ hQob
        (WScoped.instantiate1 hwty' 0 hwtb.2))
        (fun s₄ body' body'x hs₄ hext₄ hP₄ => ?_)
      obtain ⟨hbody'd, hwbody'⟩ := hP₄
      refine SimAt.bind_left (abstract1M_eff hs₄ hbody'd)
        (fun s₈ bAbs hs₈ hext₈ hQabs => ?_)
      refine SimAt.of_eff (internI_eff hs₈
        (x := .lam nm ty'x (body'x.abstract1 d) ⟨bm.bi⟩) ?_) _
        (fun s r hQ => ?_)
      · rw [denoteNode,
          denoteT_mono (((hext₂.trans hext₃).trans hext₄).trans hext₈)
            hty'd, hQabs,
          denoteN_mono (((((hextb.trans hext₁).trans hext₂).trans
            hext₃).trans hext₄).trans hext₈) hnmDen]
        simp [denoteBM, denoteBM_bi hbmDen]
      · refine ⟨hQ, ?_⟩
        simp only [WScoped]
        exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | proj snᵢ ip pe =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨pex, hpe, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨sn, hnmDen, hd⟩ := hd
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
      denoteT_some_inv (getAppFnI_spec hs₃.wf hted)
    rw [hn']
    cases n' with
    | const Tᵢ us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd'
      obtain ⟨lus, hlusDen', hd'⟩ := hd'
      rw [Option.map_eq_some_iff] at hd'
      obtain ⟨Tx, hTxDen, hd'⟩ := hd'
      rw [← hd']
      dsimp only
      refine SimAt.bind_left (readbackNM_eff hs₃ hTxDen)
        (fun s₃T Tw hs₃ hextT hTw => ?_)
      subst Tw
      replace hted := denoteT_mono hextT hted
      replace he'd := denoteT_mono ((hext₂.trans hext₃).trans hextT) he'd
      replace hnmDen := denoteN_mono
        (((hext₁.trans hext₂).trans hext₃).trans hextT) hnmDen
      replace hTxDen := denoteN_mono hextT hTxDen
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? Tx ip with
      | none =>
        exact annotateProjElimI_sim ih henv hs₃ hnmDen hted he'd
          hwte hwe'
      | some entry =>
        dsimp only
        cases hnat : entry.native with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact annotateProjElimI_sim ih henv hs₃ hnmDen hted he'd
            hwte hwe'
        | true =>
          simp only [↓reduceIte]
          refine SimAt.withStore ?_
          have htargs := getAppArgsI_spec hs₃.wf hted
          rw [htargs.length_eq]
          by_cases hlen : tex.getAppArgs.length = entry.numParams
          · rw [if_pos hlen, if_pos hlen]
            refine SimAt.of_eff (internI_eff hs₃
              (x := .proj Tx ip e'x) ?_) _ (fun s r hQ => ?_)
            · rw [denoteNode, he'd, hTxDen]
              rfl
            · refine ⟨hQ, ?_⟩
              simp only [WScoped]
              exact hwe'
          · rw [if_neg hlen, if_neg hlen]
            exact SimAt.throw
    | bvar k =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | sort u =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | lit l =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | fvar idx nm' t' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | app f₂ a₂ =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | lam nm' t' b' m' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | forallE nm' t' b' m' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | letE nm' t' v' b' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'
    | proj s' j' e'' =>
      invert_head hd'
      exact annotateProjElimI_sim ih henv hs₃
        (denoteN_mono ((hext₁.trans hext₂).trans hext₃) hnmDen) hted
        (denoteT_mono (hext₂.trans hext₃) he'd) hwte hwe'

end Walks3

end Setlec
