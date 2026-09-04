import Setlec.Verify.Cached.DiscC5

/-!
# Cached body walks, part 6: annotation and the projection fallbacks

Port of `Setlec/Verify/DiscI6.lean` under the recipe (DESIGN.md,
task #163): the simulation walks for `isPropTypeI`, `projFieldDomI`,
`annotateProjRecI`, `annotateProjElimI` and `annotateBodyI`
(`Setlec/Cached/CoreC.lean`), whose bodies are character-identical to
their `Setlec/Kernel/CoreI.lean` originals up to `EIdx → ExprC` /
`CheckIM → CheckCM` (plus the two recorded `peelFuelM` deviation lines
in `annotateBodyI`'s binder clauses).

Two representation shrinkages simplify the statements against the
interned originals: the structure/constructor names are plain `Name`s
(so the `NIdx` denotation premises vanish) and the level lists are
plain `List Level`s (so `denoteLList` premises — and with them the
`entry.recExtraLevel` case split of `annotateProjRecI_sim`'s `uf`
argument — vanish).  The pure comparand side of every statement is
byte-identical to the interned original's.
-/

set_option linter.unusedSimpArgs false

namespace Setlec.Cached

open Setlec.Cached.ExprC

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
      (coreKnotI mode (mkFEnv env) f).infer d ty' >>= fun tty =>
      ensureSortI (coreKnotI mode (mkFEnv env) f) d tty >>= fun s =>
      internLM .zero >>= fun z =>
      isEquivLM s z >>= fun o =>
      liftFueled "level comparison" o)
    ((fueledFns mode env).annotate d ty >>= fun ty' =>
      (fueledFns mode env).infer d ty' >>= fun tty =>
      ensureSort (fueledFns mode env) env d tty >>= fun s =>
      liftFueled "level comparison" (Level.isEquiv s Level.zero))
  refine SimC.bind (ih.annotate hs hden hw)
    (fun s₁ ty' ty'x hs₁ hP => ?_)
  obtain ⟨hty'd, hwty'⟩ := hP
  refine SimC.bind (ih.infer hs₁ hty'd hwty')
    (fun s₂ tty ttyx hs₂ hP₂ => ?_)
  obtain ⟨httyd, hwtty⟩ := hP₂
  refine SimC.bind (ensureSortC_sim ih hs₂ httyd hwtty)
    (fun s₃ u lu hs₃ hPu => ?_)
  obtain rfl : u = lu := hPu
  refine SimC.bind_left (internLM_eff hs₃ .zero)
    (fun s₃z z hs₃z hz => ?_)
  subst hz
  refine SimC.bind_left (isEquivLM_eff hs₃z u Level.zero)
    (fun s₃o o hs₃o ho => ?_)
  subst ho
  exact SimC.liftFueled _ _ hs₃o

/-- Port of `projFieldDomI_sim`.  The `NIdx` denotation premise of the
interned original vanishes (the structure name is a plain `Name`), so
the walk's `∀` carries only the telescope's relation. -/
theorem projFieldDomC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {structProp : Bool} {sn : Name}
    {e' : ExprC} {e'x : Expr}
    (hde : RelC e' e'x) (hwe : Expr.WScoped d e'x) :
    ∀ (k j : Nat) {tel : ExprC} {telx : Expr} {s₀ : CState},
      CSOK mode env s₀ → RelC tel telx → Expr.WScoped d telx →
      SimC mode env s₀ (RelEC d)
        (projFieldDomI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          structProp sn e' j k tel)
        (projFieldDom (fueledFns mode env) env d structProp sn e'x j k
          telx)
  | 0, jj, tel, telx, s₀, hs, hdt, hwtel => by
    unfold projFieldDomI
    refine SimC.view ?_
    obtain ⟨hwc, rfl⟩ := hdt
    cases tel with
    | forallE nmN dom rest mbN =>
      dsimp only [eraseC, ExprC.view]
      obtain ⟨hdomc, hrestc, -⟩ := hwc.forallE_inv
      have hw' : Expr.WScoped d (eraseC dom) ∧ Expr.WScoped d (eraseC rest) := by
        have hw2 : Expr.WScoped d
          (Expr.forallE nmN (eraseC dom) (eraseC rest) mbN) := hwtel
        simpa only [Expr.WScoped] using hw2
      exact SimC.pure hs ⟨⟨hdomc, rfl⟩, hw'.1⟩
    | bvar k => exact SimC.throw
    | sort u => exact SimC.throw
    | const nmN us => exact SimC.throw
    | lit l => exact SimC.throw
    | fvar idx nmN t => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam nmN t b m => exact SimC.throw
    | letE nmN t v b => exact SimC.throw
    | proj s'N j' e'' => exact SimC.throw
  | k + 1, jj, tel, telx, s₀, hs, hdt, hwtel => by
    unfold projFieldDomI
    refine SimC.view ?_
    obtain ⟨hwc, rfl⟩ := hdt
    cases tel with
    | forallE nmN dom rest mbN =>
      dsimp only [eraseC, ExprC.view]
      obtain ⟨hdomc, hrestc, -⟩ := hwc.forallE_inv
      have hw' : Expr.WScoped d (eraseC dom) ∧ Expr.WScoped d (eraseC rest) := by
        have hw2 : Expr.WScoped d
          (Expr.forallE nmN (eraseC dom) (eraseC rest) mbN) := hwtel
        simpa only [Expr.WScoped] using hw2
      have hwpj : Expr.WScoped d (Expr.proj sn jj e'x) := by
        simpa only [Expr.WScoped] using hwe
      have hwrest' : Expr.WScoped d
          ((eraseC rest).instantiate1 (.proj sn jj e'x)) :=
        Expr.WScoped.instantiate1_gen hwpj 0 hw'.2
      dsimp only [projFieldDom]
      refine SimC.withStore ?_
      rw [looseBVarsBoundedI_spec hrestc rfl]
      by_cases hcl : (eraseC rest).looseBVarsBounded 0 = true
      · rw [if_pos hcl, if_pos hcl]
        exact projFieldDomC_sim ih henv hde hwe k (jj + 1) hs
          ⟨hrestc, rfl⟩ hw'.2
      · rw [if_neg hcl, if_neg hcl]
        cases structProp with
        | true =>
          simp only [↓reduceIte]
          refine SimC.bind (isPropTypeC_sim ih hs ⟨hdomc, rfl⟩ hw'.1)
            (fun s₁ p p' hs₁ hPp => ?_)
          obtain rfl : p = p' := hPp
          cases p with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.throw_bind
          | true =>
            simp only [↓reduceIte]
            refine SimC.bind_left
              (internI_eff hs₁ (n := ExprView.proj sn jj e') hde.1)
              (fun s₂ pj hs₂ hQpj => ?_)
            have hQpj' : RelC pj (Expr.proj sn jj e'x) :=
              ⟨hQpj.1, by
                have h2 : eraseC pj = Expr.proj sn jj (eraseC e') := hQpj.2
                rw [h2, hde.2]⟩
            refine SimC.bind_left (inst1M_eff hs₂ ⟨hrestc, rfl⟩ hQpj')
              (fun s₃ rest' hs₃ hQr => ?_)
            exact projFieldDomC_sim ih henv hde hwe k (jj + 1) hs₃
              hQr hwrest'
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind_left
            (internI_eff hs (n := ExprView.proj sn jj e') hde.1)
            (fun s₂ pj hs₂ hQpj => ?_)
          have hQpj' : RelC pj (Expr.proj sn jj e'x) :=
            ⟨hQpj.1, by
              have h2 : eraseC pj = Expr.proj sn jj (eraseC e') := hQpj.2
              rw [h2, hde.2]⟩
          refine SimC.bind_left (inst1M_eff hs₂ ⟨hrestc, rfl⟩ hQpj')
            (fun s₃ rest' hs₃ hQr => ?_)
          exact projFieldDomC_sim ih henv hde hwe k (jj + 1) hs₃
            hQr hwrest'
    | bvar k' => exact SimC.throw
    | sort u => exact SimC.throw
    | const nmN us => exact SimC.throw
    | lit l => exact SimC.throw
    | fvar idx nmN t => exact SimC.throw
    | app f' a' => exact SimC.throw
    | lam nmN t b m => exact SimC.throw
    | letE nmN t v b => exact SimC.throw
    | proj s'N j' e'' => exact SimC.throw

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The shared reduct tail of the Prop-projection fallback: build the
recursor elimination and re-annotate it under the scope guard. -/
private theorem annotateProjRecC_rest (ih : SSimC mode env f)
    {d : Nat} {entry : ProjEntry} {te e' fi minor : ExprC}
    {params : List ExprC} {tex e'x fix minorx : Expr}
    {paramsx : List Expr} {us uf : List Level}
    {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hte : RelC te tex)
    (hde : RelC e' e'x)
    (hfi : RelC fi fix)
    (hmin : RelC minor minorx)
    (hparams : RelCL params paramsx) :
    SimC mode env s₀ (RelEC d)
      (internNameM (entry.structName.str "rec") >>= fun recI =>
       internI (.const recI (uf ++ us)) >>=
        fun recC =>
       internNameM (.str .anonymous "t") >>= fun tI =>
       internI (.lam tI te fi ⟨.default, .never⟩) >>=
        fun motive =>
       mkAppNM recC (params ++ [motive, minor, e']) >>= fun raw =>
       Setlec.Cached.withStore (fun st => st.wscopedBI d raw &&
         st.looseBVarsBoundedI 0 raw &&
         st.leafGuardI raw e') >>= fun g =>
       if g then (coreKnotI mode (mkFEnv env) f).annotate d raw
       else throw (.notImplemented "projection elimination scoping"))
      (let raw := Expr.mkAppN
          (.const (entry.structName.str "rec") (uf ++ us))
          (paramsx ++ [.lam (.str .anonymous "t") tex fix
            ⟨.default, .never⟩, minorx, e'x])
        if raw.wscopedB d && raw.looseBVarsBounded 0 &&
            raw.fvarLeaves.all
              (fun l => e'x.fvarLeaves.contains l) then
          (fueledFns mode env).annotate d raw
        else throw (.notImplemented "projection elimination scoping")) := by
  refine SimC.bind_left
    (internNameM_eff hs (entry.structName.str "rec"))
    (fun s₀r recI hs hQrecI => ?_)
  subst hQrecI
  refine SimC.bind_left
    (internI_eff hs
      (n := ExprView.const (entry.structName.str "rec") (uf ++ us)) trivial)
    (fun s₁ recC hs₁ hQrec => ?_)
  have hQrec' : RelC recC
    (Expr.const (entry.structName.str "rec") (uf ++ us)) := hQrec
  refine SimC.bind_left (internNameM_eff hs₁ (.str .anonymous "t"))
    (fun s₁t tI hs₁t hQtI => ?_)
  subst hQtI
  refine SimC.bind_left
    (internI_eff hs₁t
      (n := ExprView.lam (.str .anonymous "t") te fi ⟨.default, .never⟩)
      ⟨hte.1, hfi.1⟩)
    (fun s₂ motive hs₂ hQmot => ?_)
  have hQmot' : RelC motive
      (Expr.lam (.str .anonymous "t") tex fix ⟨.default, .never⟩) :=
    ⟨hQmot.1, by
      have h2 : eraseC motive =
        Expr.lam (.str .anonymous "t") (eraseC te) (eraseC fi)
          ⟨.default, .never⟩ := hQmot.2
      rw [h2, hte.2, hfi.2]⟩
  refine SimC.bind_left (mkAppNM_eff hs₂ hQrec'
    (hparams.append (RelCL.cons hQmot' (RelCL.cons hmin
      (RelCL.cons hde RelCL.nil)))))
    (fun s₃ raw hs₃ hQraw => ?_)
  refine SimC.withStore ?_
  rw [wscopedBI_spec hQraw.1 hQraw.2, looseBVarsBoundedI_spec hQraw.1 hQraw.2,
    leafGuardI_spec hQraw.1 hde.1 hQraw.2 hde.2]
  dsimp only
  split
  · rename_i hguard
    exact ih.annotate hs₃ hQraw (Expr.WScoped.of_wscopedB
      (by simp only [Bool.and_eq_true] at hguard; exact hguard.1.1))
  · exact SimC.throw

/-- Port of `annotateProjRecI_sim`. -/
theorem annotateProjRecC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {entry : ProjEntry} {ip : Nat} {te e' : ExprC}
    {tex e'x : Expr} {us : List Level} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hte : RelC te tex)
    (hde : RelC e' e'x)
    (hwte : Expr.WScoped d tex) (hwe : Expr.WScoped d e'x) :
    SimC mode env s₀ (RelEC d)
      (annotateProjRecI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d entry
        ip te e' us)
      (annotateProjRec (fueledFns mode env) env d entry ip tex e'x us) := by
  unfold annotateProjRecI
  unfold annotateProjRec
  rw [mkFEnv_find?]
  cases hfC : env.find? entry.ctor with
  | none => exact SimC.throw
  | some ci =>
    cases ci with
    | ctorInfo cvC cnP cnF =>
      dsimp only
      refine SimC.withStore ?_
      have hparams : RelCL (ExprC.getAppArgs te) tex.getAppArgs := by
        have hg := ExprC.getAppArgs_spec hte.1
        exact ⟨hg.1, by rw [hg.2, hte.2]⟩
      simp only [CStore.getAppArgsI, RelCL.length hparams]
      split
      · refine SimC.bind_left (internNameM_eff hs entry.ctor)
          (fun s₀c ctorI hs hQctorI => ?_)
        subst hQctorI
        refine SimC.bind_left (constTyAtM_eff hs hfC)
          (fun s₁ ctorTy hs₁ hQty => ?_)
        simp only [ConstantInfo.toConstantVal] at hQty
        refine SimC.bind_left (piResidualM_eff hs₁ hQty hparams)
          (fun s₂ otel hs₂ hQtel => ?_)
        rw [instPis_eq_piResidual]
        cases htel : piResidual
            (cvC.type.instantiateLevelParams cvC.levelParams us)
            tex.getAppArgs with
        | none =>
          rw [htel] at hQtel
          cases otel with
          | some tel => exact absurd hQtel (by simp [OptEr])
          | none => exact SimC.throw
        | some telx =>
          rw [htel] at hQtel
          cases otel with
          | none => exact absurd hQtel (by simp [OptEr])
          | some tel =>
            have hwtel : Expr.WScoped d telx := by
              refine instPis_WScoped
                (by rw [instPis_eq_piResidual]; exact htel) ?_
                hwte.getAppArgs
              obtain ⟨htf, -⟩ := henv _ (find?_mem hfC)
              exact wscoped_instLevels_of_not_hasFvar htf _ _
            refine SimC.bind (isPropTypeC_sim ih hs₂ hte hwte)
              (fun s₃ sp sp' hs₃ hPsp => ?_)
            obtain rfl : sp = sp' := hPsp
            refine SimC.bind_left
              (internNameM_eff hs₃ entry.structName)
              (fun s₃n snI hs₃n hQsnI => ?_)
            subst hQsnI
            refine SimC.bind (projFieldDomC_sim ih henv hde hwe ip 0 hs₃n
              hQtel hwtel)
              (fun s₄ fi fix hs₄ hPfi => ?_)
            obtain ⟨hfid, hwfi⟩ := hPfi
            refine SimC.bind_left
              (internI_eff hs₄ (n := ExprView.bvar (cnF - 1 - ip)) trivial)
              (fun s₅ fieldBvar hs₅ hQbv => ?_)
            have hQbv' : RelC fieldBvar (Expr.bvar (cnF - 1 - ip)) := hQbv
            refine SimC.bind_left (pisToLamsM_eff (k := cnF) hs₅
              hQtel hQbv') (fun s₆ ominor hs₆ hQmin => ?_)
            cases hmin : Expr.pisToLams cnF telx
                (.bvar (cnF - 1 - ip)) with
            | none =>
              rw [hmin] at hQmin
              cases ominor with
              | some minor => exact absurd hQmin (by simp [OptEr])
              | none => exact SimC.throw
            | some minorx =>
              rw [hmin] at hQmin
              cases ominor with
              | none => exact absurd hQmin (by simp [OptEr])
              | some minor =>
                refine SimC.bind (ih.annotate hs₆ hfid hwfi)
                  (fun s₇ fi' fi'x hs₇ hPfi' => ?_)
                obtain ⟨hfi'd, hwfi'⟩ := hPfi'
                refine SimC.bind (ih.infer hs₇ hfi'd hwfi')
                  (fun s₈ tfi tfix hs₈ hPtfi => ?_)
                obtain ⟨htfid, hwtfi⟩ := hPtfi
                refine SimC.bind (ensureSortC_sim ih hs₈ htfid hwtfi)
                  (fun s₉ sfi lsfi hs₉ hPsfi => ?_)
                obtain rfl : sfi = lsfi := hPsfi
                cases sp with
                | true =>
                  simp only [↓reduceIte]
                  refine SimC.bind_left (internLM_eff hs₉ .zero)
                    (fun s₉z z hs₉z hz => ?_)
                  subst hz
                  refine SimC.bind_left (isEquivLM_eff hs₉z sfi Level.zero)
                    (fun s₉o o hs₉o ho => ?_)
                  subst ho
                  refine SimC.bind (SimC.liftFueled _ _ hs₉o)
                    (fun s₁₀ ok ok' hs₁₀ hPok => ?_)
                  obtain rfl : ok = ok' := hPok
                  cases ok with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact SimC.throw_bind
                  | true =>
                    simp only [↓reduceIte]
                    exact annotateProjRecC_rest ih hs₁₀ hte hde hfid hQmin
                      hparams
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact annotateProjRecC_rest ih hs₉ hte hde hfid hQmin
                    hparams
      · exact SimC.throw
    | axiomInfo cv => exact SimC.throw
    | defnInfo cv v h => exact SimC.throw
    | thmInfo cv v => exact SimC.throw
    | indInfo cv caps => exact SimC.throw
    | recInfo cv mI rP rules => exact SimC.throw
    | projInfo entry' => exact SimC.throw

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- Port of `annotateProjElimI_sim`. -/
theorem annotateProjElimC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {sn : Name} {ip : Nat} {te e' : ExprC}
    {tex e'x : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hte : RelC te tex)
    (hde : RelC e' e'x)
    (hwte : Expr.WScoped d tex) (hwe : Expr.WScoped d e'x) :
    SimC mode env s₀ (RelEC d)
      (annotateProjElimI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn
        ip te e')
      (annotateProjElim (fueledFns mode env) env d sn ip tex e'x) := by
  unfold annotateProjElimI
  unfold annotateProjElim
  refine SimC.withStore ?_
  obtain ⟨hwc, rfl⟩ := hte
  have hte : RelC te (eraseC te) := ⟨hwc, rfl⟩
  have htargs : RelCL (ExprC.getAppArgs te) (eraseC te).getAppArgs :=
    ExprC.getAppArgs_spec hwc
  obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec hwc
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hgn : ExprC.getAppFn te = g at hwfn hfn ⊢
  cases g with
  | const T us =>
    rw [show (eraseC te).getAppFn = Expr.const T us from hfn.symm]
    dsimp only
    refine SimC.bind_left (readbackNM_eff hs T)
      (fun s₀T Tw hs hTw => ?_)
    subst hTw
    by_cases hT : Tw = sn
    · rw [if_pos hT, if_pos hT]
      rw [mkFEnv_find?]
      cases hfp : env.find? (projFnName Tw ip) with
      | none => exact SimC.throw
      | some ci =>
        cases ci with
        | recInfo cvp mI rP rules =>
          dsimp only
          refine SimC.withStore ?_
          simp only [CStore.getAppArgsI, RelCL.length htargs]
          split
          · refine SimC.bind_left (projFnIdxM_eff hs Tw ip)
              (fun s₀p pf hs hQpf => ?_)
            subst hQpf
            refine SimC.bind_left
              (internI_eff hs
                (n := ExprView.const (projFnName Tw ip) us) trivial)
              (fun s₁ hcst hs₁ hQh => ?_)
            have hQh' : RelC hcst (Expr.const (projFnName Tw ip) us) := hQh
            refine SimC.bind_left (mkAppNM_eff hs₁ hQh'
              (htargs.append (RelCL.cons hde RelCL.nil)))
              (fun s₂ raw hs₂ hQraw => ?_)
            refine SimC.withStore ?_
            rw [wscopedBI_spec hQraw.1 hQraw.2,
              looseBVarsBoundedI_spec hQraw.1 hQraw.2,
              leafGuardI_spec hQraw.1 hde.1 hQraw.2 hde.2]
            try dsimp only
            split
            · rename_i hguard
              exact ih.annotate hs₂ hQraw (Expr.WScoped.of_wscopedB
                (by simp only [Bool.and_eq_true] at hguard
                    exact hguard.1.1))
            · exact SimC.throw
          · exact SimC.throw
        | projInfo entry =>
          dsimp only
          cases hnat : entry.native with
          | true =>
            simp only [↓reduceIte]
            exact SimC.throw
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact annotateProjRecC_sim ih henv hs hte hde hwte hwe
        | axiomInfo cv => exact SimC.throw
        | defnInfo cv v hd => exact SimC.throw
        | thmInfo cv v => exact SimC.throw
        | indInfo cv caps => exact SimC.throw
        | ctorInfo cv nP nF => exact SimC.throw
    · rw [if_neg hT, if_neg hT]
      exact SimC.throw
  | bvar k =>
    rw [show (eraseC te).getAppFn = Expr.bvar k from hfn.symm]
    exact SimC.throw
  | sort u =>
    rw [show (eraseC te).getAppFn = Expr.sort u from hfn.symm]
    exact SimC.throw
  | lit l =>
    rw [show (eraseC te).getAppFn = Expr.lit l from hfn.symm]
    exact SimC.throw
  | fvar idx nmN t =>
    rw [show (eraseC te).getAppFn = Expr.fvar idx nmN (eraseC t)
      from hfn.symm]
    exact SimC.throw
  | app f' a' =>
    rw [show (eraseC te).getAppFn = Expr.app (eraseC f') (eraseC a')
      from hfn.symm]
    exact SimC.throw
  | lam nmN t b m =>
    rw [show (eraseC te).getAppFn = Expr.lam nmN (eraseC t) (eraseC b) m
      from hfn.symm]
    exact SimC.throw
  | forallE nmN t b m =>
    rw [show (eraseC te).getAppFn = Expr.forallE nmN (eraseC t) (eraseC b) m
      from hfn.symm]
    exact SimC.throw
  | letE nmN t v b =>
    rw [show (eraseC te).getAppFn
      = Expr.letE nmN (eraseC t) (eraseC v) (eraseC b) from hfn.symm]
    exact SimC.throw
  | proj s'N j' e'' =>
    rw [show (eraseC te).getAppFn = Expr.proj s'N j' (eraseC e'')
      from hfn.symm]
    exact SimC.throw

/-- Port of `annotateBodyI_sim`. -/
theorem annotateBodyC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelEC d)
      (annotateBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (annotateBody mode (fueledFns mode env) env d ex) := by
  unfold annotateBodyI
  refine SimC.view ?_
  obtain ⟨hwc, rfl⟩ := hden
  have hden : RelC i (eraseC i) := ⟨hwc, rfl⟩
  cases i with
  | bvar k =>
    dsimp only [eraseC, ExprC.view]
    exact SimC.pure hs ⟨hden, hw⟩
  | sort u =>
    dsimp only [eraseC, ExprC.view]
    exact SimC.pure hs ⟨hden, hw⟩
  | const nmN us =>
    dsimp only [eraseC, ExprC.view]
    exact SimC.pure hs ⟨hden, hw⟩
  | letE nmN t v b =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, hwvc, hwbc, -⟩ := hwc.letE_inv
    have hwtvb : Expr.WScoped d (eraseC t) ∧ Expr.WScoped d (eraseC v) ∧
        Expr.WScoped d (eraseC b) := by
      have hw' : Expr.WScoped d
        (Expr.letE nmN (eraseC t) (eraseC v) (eraseC b)) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs ⟨hwtc, rfl⟩ hwtvb.1)
      (fun s₁ ty' ty'x hs₁ hP₁ => ?_)
    obtain ⟨-, -⟩ := hP₁
    refine SimC.bind (ih.annotate hs₁ ⟨hwvc, rfl⟩ hwtvb.2.1)
      (fun s₄ v' v'x hs₄ hP₄ => ?_)
    obtain ⟨-, -⟩ := hP₄
    refine SimC.bind_left (inst1M_eff hs₄ ⟨hwbc, rfl⟩ ⟨hwvc, rfl⟩)
      (fun s₇ ob hs₇ hQob => ?_)
    exact ih.annotate hs₇ hQob
      (Expr.WScoped.instantiate1_gen hwtvb.2.1 0 hwtvb.2.2)
  | fvar idx nmN t =>
    dsimp only [eraseC, ExprC.view]
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
      dsimp only [eraseC, ExprC.view]
      unfold annotateBody
      try dsimp only
      rw [natLitSupportedF_eq]
      by_cases hg : natLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimC.pure hs ⟨hden, hw⟩
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
    | strVal str =>
      dsimp only [eraseC, ExprC.view]
      unfold annotateBody
      try dsimp only
      rw [strLitSupportedF_eq]
      by_cases hg : strLitSupported env
      · rw [if_pos hg, if_pos hg]
        exact SimC.pure hs ⟨hden, hw⟩
      · rw [if_neg hg, if_neg hg]
        exact SimC.throw
  | app g' a =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwgc, hwac, -⟩ := hwc.app_inv
    -- structural (task #100 stage 6: the application rule's checks
    -- moved to the driver's inference sweep, so the spine loop is
    -- gone and the clause annotates the two children)
    have hwga : Expr.WScoped d (eraseC g') ∧ Expr.WScoped d (eraseC a) := by
      have hw' : Expr.WScoped d (Expr.app (eraseC g') (eraseC a)) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs ⟨hwgc, rfl⟩ hwga.1)
      (fun s₁ g'' g''x hs₁ hP₁ => ?_)
    obtain ⟨hg''d, hwg''⟩ := hP₁
    refine SimC.bind (ih.annotate hs₁ ⟨hwac, rfl⟩ hwga.2)
      (fun s₂ a'' a''x hs₂ hP₂ => ?_)
    obtain ⟨ha''d, hwa''⟩ := hP₂
    obtain ⟨hg''w, rfl⟩ := hg''d
    obtain ⟨ha''w, rfl⟩ := ha''d
    exact SimC.of_eff
      (internI_eff hs₂ (n := ExprView.app g'' a'') ⟨hg''w, ha''w⟩) _
      (fun r hQ => ⟨hQ, by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (Nat.le_refl _) hwg'', hwa''⟩⟩)
  | forallE nmN t b m =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, hwbc, -⟩ := hwc.forallE_inv
    have hwtb : Expr.WScoped d (eraseC t) ∧ Expr.WScoped d (eraseC b) := by
      have hw' : Expr.WScoped d
        (Expr.forallE nmN (eraseC t) (eraseC b) m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs ⟨hwtc, rfl⟩ hwtb.1)
      (fun s₁ ty' ty'x hs₁ hP => ?_)
    obtain ⟨hty'd, hwty'⟩ := hP
    obtain ⟨hty'w, rfl⟩ := hty'd
    refine SimC.bind_left
      (internI_eff hs₁ (n := ExprView.fvar d nmN ty') hty'w)
      (fun s₂ fv hs₂ hQfv => ?_)
    have hQfv' : RelC fv (Expr.fvar d nmN (eraseC ty')) := hQfv
    refine SimC.bind_left (peelFuelM_eff hs₂)
      (fun s₃ fuel hs₃ _hQfuel => ?_)
    exact annotatePisC_tail_sim ih hs₃ rfl rfl ⟨hwbc, rfl⟩ ⟨hty'w, rfl⟩
      hQfv' hwty' hwtb.2
  | lam nmN t b m =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwtc, hwbc, -⟩ := hwc.lam_inv
    have hwtb : Expr.WScoped d (eraseC t) ∧ Expr.WScoped d (eraseC b) := by
      have hw' : Expr.WScoped d
        (Expr.lam nmN (eraseC t) (eraseC b) m) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind_left (bvarBoundM_eff hs hwc)
      (fun sb bnd hsb hQb => ?_)
    by_cases hb0 : bnd = 0
    · rw [if_pos hb0]
      subst hb0
      refine SimC.bind (ih.annotate hsb ⟨hwtc, rfl⟩ hwtb.1)
        (fun s₁ ty' ty'x hs₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      obtain ⟨hty'w, rfl⟩ := hty'd
      refine SimC.bind_left
        (internI_eff hs₁ (n := ExprView.fvar d nmN ty') hty'w)
        (fun s₂ fv hs₂ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar d nmN (eraseC ty')) := hQfv
      refine SimC.bind_left (peelFuelM_eff hs₂)
        (fun s₃ fuel hs₃ _hQfuel => ?_)
      exact annotateLamsC_tail_sim ih hs₃ rfl rfl ⟨hwbc, rfl⟩ ⟨hty'w, rfl⟩
        hQfv' hwty' hwtb.2
    · rw [if_neg hb0]
      refine SimC.bind (ih.annotate hsb ⟨hwtc, rfl⟩ hwtb.1)
        (fun s₁ ty' ty'x hs₁ hP => ?_)
      obtain ⟨hty'd, hwty'⟩ := hP
      obtain ⟨hty'w, rfl⟩ := hty'd
      refine SimC.bind_left
        (internI_eff hs₁ (n := ExprView.fvar d nmN ty') hty'w)
        (fun s₂ fv hs₂ hQfv => ?_)
      have hQfv' : RelC fv (Expr.fvar d nmN (eraseC ty')) := hQfv
      refine SimC.bind_left (inst1M_eff hs₂ ⟨hwbc, rfl⟩ hQfv')
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
            (internI (.lam nmN ty' bAbs ⟨m.bi, pw⟩))
            (pure (Expr.lam nmN (eraseC ty') (body'x.abstract1 d)
              ⟨m.bi, pw⟩)) := by
        intro s' pw hsS
        refine SimC.of_eff (internI_eff hsS
          (n := ExprView.lam nmN ty' bAbs ⟨m.bi, pw⟩)
          ⟨hty'w, hQabs.1⟩) _ (fun r hQ => ⟨⟨hQ.1, by
            have h2 : eraseC r
              = Expr.lam nmN (eraseC ty') (eraseC bAbs) ⟨m.bi, pw⟩ := hQ.2
            rw [h2, hQabs.2]⟩, by
            simp only [Expr.WScoped]
            exact ⟨hwty', Setlec.WScoped.abstract1 0 hwbody'⟩⟩)
      split
      · refine SimC.bind (annotPwLamC_sim ih hs₈ hbody'd hwbody')
          (fun s₉ pw pwx hs₉ hPpw => ?_)
        obtain rfl : pw = pwx := hPpw
        exact hstep s₉ pw hs₉
      · exact hstep s₈ m.pw hs₈
  | proj snN ipN pe =>
    dsimp only [eraseC, ExprC.view]
    obtain ⟨hwpec, -⟩ := hwc.proj_inv
    have hwpe : Expr.WScoped d (eraseC pe) := by
      have hw' : Expr.WScoped d (Expr.proj snN ipN (eraseC pe)) := hw
      simpa only [Expr.WScoped] using hw'
    unfold annotateBody
    try dsimp only
    refine SimC.bind (ih.annotate hs ⟨hwpec, rfl⟩ hwpe)
      (fun s₁ e' e'x hs₁ hP => ?_)
    obtain ⟨he'd, hwe'⟩ := hP
    refine SimC.bind (ih.infer hs₁ he'd hwe')
      (fun s₂ tpe tpex hs₂ hP₂ => ?_)
    obtain ⟨htped, hwtpe⟩ := hP₂
    refine SimC.bind (ih.whnf hs₂ htped hwtpe)
      (fun s₃ te tex hs₃ hP₃ => ?_)
    obtain ⟨hted, hwte⟩ := hP₃
    refine SimC.withStore ?_
    obtain ⟨hwtec, rfl⟩ := hted
    have hted : RelC te (eraseC te) := ⟨hwtec, rfl⟩
    have htargs : RelCL (ExprC.getAppArgs te) (eraseC te).getAppArgs :=
      ExprC.getAppArgs_spec hwtec
    obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec hwtec
    dsimp only [CStore.getNode, CStore.getAppFnI]
    generalize hgn : ExprC.getAppFn te = g at hwfn hfn ⊢
    cases g with
    | const T us =>
      rw [show (eraseC te).getAppFn = Expr.const T us from hfn.symm]
      dsimp only
      refine SimC.bind_left (readbackNM_eff hs₃ T)
        (fun s₃T Tw hs₃T hTw => ?_)
      subst hTw
      rw [mkFEnv_findProj?]
      cases hfp : env.findProj? Tw ipN with
      | none =>
        exact annotateProjElimC_sim ih henv hs₃T hted he'd hwte hwe'
      | some entry =>
        dsimp only
        cases hnat : entry.native with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact annotateProjElimC_sim ih henv hs₃T hted he'd hwte hwe'
        | true =>
          simp only [↓reduceIte]
          refine SimC.withStore ?_
          simp only [CStore.getAppArgsI, RelCL.length htargs]
          by_cases hlen : (eraseC te).getAppArgs.length = entry.numParams
          · rw [if_pos hlen, if_pos hlen]
            exact SimC.of_eff
              (internI_eff hs₃T (n := ExprView.proj Tw ipN e') he'd.1) _
              (fun r hQ => ⟨⟨hQ.1, by
                  have h2 : eraseC r = Expr.proj Tw ipN (eraseC e') := hQ.2
                  rw [h2, he'd.2]⟩, by
                simp only [Expr.WScoped]
                exact hwe'⟩)
          · rw [if_neg hlen, if_neg hlen]
            exact SimC.throw
    | bvar k =>
      rw [show (eraseC te).getAppFn = Expr.bvar k from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | sort u =>
      rw [show (eraseC te).getAppFn = Expr.sort u from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | lit l =>
      rw [show (eraseC te).getAppFn = Expr.lit l from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | fvar idx nm' t' =>
      rw [show (eraseC te).getAppFn = Expr.fvar idx nm' (eraseC t')
        from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | app f₂ a₂ =>
      rw [show (eraseC te).getAppFn = Expr.app (eraseC f₂) (eraseC a₂)
        from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | lam nm' t' b' m' =>
      rw [show (eraseC te).getAppFn = Expr.lam nm' (eraseC t') (eraseC b') m'
        from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | forallE nm' t' b' m' =>
      rw [show (eraseC te).getAppFn
        = Expr.forallE nm' (eraseC t') (eraseC b') m' from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | letE nm' t' v' b' =>
      rw [show (eraseC te).getAppFn
        = Expr.letE nm' (eraseC t') (eraseC v') (eraseC b') from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'
    | proj s' j' e'' =>
      rw [show (eraseC te).getAppFn = Expr.proj s' j' (eraseC e'')
        from hfn.symm]
      exact annotateProjElimC_sim ih henv hs₃ hted he'd hwte hwe'

end Walks3

end Setlec.Cached
