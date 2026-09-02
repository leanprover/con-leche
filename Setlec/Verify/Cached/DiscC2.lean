import Setlec.Verify.Cached.DiscC1

/-!
# Cached body walks, part 2: the stuck-term certificates (task #163)

The port of `Setlec/Verify/DiscI2.lean` under the recipe (DESIGN.md,
task #163): `SimAt → SimC`, denotation hypotheses → `RelC`/`RelCL`, no
`Ext`, node inversion by `WFc.*_inv` and `cases` on the `ExprC`
constructor instead of `denoteNode` unpacking, and the identity
name/level wrapper effects of `SimCEff.lean` where the interned walks
carried interning and readback steps.  The pure comparand side of every
statement is byte-identical to the interned original's.
-/

namespace Setlec.Cached

open Setlec.Cached.ExprC

variable {mode : CheckMode}

/-- Scope inversion at an `app` node, phrased on the erasure (the
`DiscC` replacement for the interned walks' `simp only [WScoped] at`
steps, which had a denoted `Expr` to unfold). -/
private theorem wscoped_appC_inv {d : Nat} {fn arg : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : Expr.WScoped d (eraseC (ExprC.app fn arg h bb fb lp))) :
    Expr.WScoped d (eraseC fn) ∧ Expr.WScoped d (eraseC arg) := by
  have hw' : Expr.WScoped d (.app (eraseC fn) (eraseC arg)) := hw
  simpa only [Expr.WScoped] using hw'

section Walks

variable {env : Env} {f : Nat}

/-- Port of `proofIrrelI_sim`. -/
theorem proofIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : ExprC}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (proofIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (proofIrrel (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).infer d i >>= fun ta =>
      (coreKnotI mode (mkFEnv env) f).whnf d ta >>= fun wta =>
      Setlec.Cached.withStore (fun st => isUnitLikeTyI (mkFEnv env) st wta) >>=
        fun c₁ =>
      if c₁ then
        (coreKnotI mode (mkFEnv env) f).infer d j >>= fun tb =>
        (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
        Setlec.Cached.withStore (fun st => isUnitLikeTyI (mkFEnv env) st wtb) >>=
          fun c₂ =>
        if c₂ then pure true else pure false
      else
        (coreKnotI mode (mkFEnv env) f).infer d ta >>= fun tta =>
        (coreKnotI mode (mkFEnv env) f).whnf d tta >>= fun wtta =>
        viewI wtta >>= fun n =>
        match n with
        | some (.sort uT) =>
          internLM .zero >>= fun zA =>
          isEquivLM uT zA >>= fun oA =>
          liftFueled "level comparison" oA >>= fun okA =>
          (coreKnotI mode (mkFEnv env) f).infer d j >>= fun tb =>
          (coreKnotI mode (mkFEnv env) f).infer d tb >>= fun ttb =>
          (coreKnotI mode (mkFEnv env) f).whnf d ttb >>= fun wttb =>
          viewI wttb >>= fun n' =>
          match n' with
          | some (.sort vT) =>
            internLM .zero >>= fun zB =>
            isEquivLM vT zB >>= fun oB =>
            liftFueled "level comparison" oB >>= fun okB =>
            pure (okA && okB)
          | _ => pure false
        | _ => pure false)
    (proofIrrel (fueledFns mode env) env d a b)
  refine SimC.bind (ih.infer hs hdena hwa) (fun s₁ ta tax hs₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htad hwta) (fun s₂ wta wtax hs₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimC.withStore ?_
  rw [isUnitLikeTyI_spec hwtad.2]
  by_cases hu : isUnitLikeTy env wtax
  · rw [if_pos hu, if_pos hu]
    refine SimC.bind (ih.infer hs₂ hdenb hwb) (fun s₃ tb tbx hs₃ hP₃ => ?_)
    obtain ⟨htbd, hwtb⟩ := hP₃
    refine SimC.bind (ih.whnf hs₃ htbd hwtb) (fun s₄ wtb wtbx hs₄ hP₄ => ?_)
    obtain ⟨hwtbd, hwwtb⟩ := hP₄
    refine SimC.withStore ?_
    rw [isUnitLikeTyI_spec hwtbd.2]
    by_cases hu₂ : isUnitLikeTy env wtbx
    · rw [if_pos hu₂, if_pos hu₂]
      exact SimC.pure hs₄ rfl
    · rw [if_neg hu₂, if_neg hu₂]
      exact SimC.pure hs₄ rfl
  · rw [if_neg hu, if_neg hu]
    refine SimC.bind (ih.infer hs₂ htad hwta) (fun s₃ tta ttax hs₃ hP₃ => ?_)
    obtain ⟨httad, hwtta⟩ := hP₃
    refine SimC.bind (ih.whnf hs₃ httad hwtta) (fun s₄ wtta wttax hs₄ hP₄ => ?_)
    obtain ⟨hwttad, hwwtta⟩ := hP₄
    refine SimC.view ?_
    obtain ⟨hwc, rfl⟩ := hwttad
    cases wtta with
    | sort uT h bb fb lp =>
      refine SimC.bind_left (internLM_eff hs₄ .zero)
        (fun s₄z zA hs₄z hzA => ?_)
      subst hzA
      refine SimC.bind_left (isEquivLM_eff hs₄z uT .zero)
        (fun s₄o oA hs₄o hoA => ?_)
      subst hoA
      refine SimC.bind (SimC.liftFueled _ _ hs₄o)
        (fun s₅ okA okA' hs₅ hPok => ?_)
      obtain rfl : okA = okA' := hPok
      refine SimC.bind (ih.infer hs₅ hdenb hwb) (fun s₆ tb tbx hs₆ hP₆ => ?_)
      obtain ⟨htbd, hwtb⟩ := hP₆
      refine SimC.bind (ih.infer hs₆ htbd hwtb) (fun s₇ ttb ttbx hs₇ hP₇ => ?_)
      obtain ⟨httbd, hwttb⟩ := hP₇
      refine SimC.bind (ih.whnf hs₇ httbd hwttb)
        (fun s₈ wttb wttbx hs₈ hP₈ => ?_)
      obtain ⟨hwttbd, hwwttb⟩ := hP₈
      refine SimC.view ?_
      obtain ⟨hwc', rfl⟩ := hwttbd
      cases wttb with
      | sort vT h' bb' fb' lp' =>
        refine SimC.bind_left (internLM_eff hs₈ .zero)
          (fun s₈z zB hs₈z hzB => ?_)
        subst hzB
        refine SimC.bind_left (isEquivLM_eff hs₈z vT .zero)
          (fun s₈o oB hs₈o hoB => ?_)
        subst hoB
        refine SimC.bind (SimC.liftFueled _ _ hs₈o)
          (fun s₉ okB okB' hs₉ hPok' => ?_)
        obtain rfl : okB = okB' := hPok'
        exact SimC.pure hs₉ rfl
      | bvar k h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | const nm us h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | lit l h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | fvar idx nm t h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | app f' a' h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | lam nm t b' m h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | forallE nm t b' m h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | letE nm t v b' h' bb' fb' lp' => exact SimC.pure hs₈ rfl
      | proj sn j' e' h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | bvar k h bb fb lp => exact SimC.pure hs₄ rfl
    | const nm us h bb fb lp => exact SimC.pure hs₄ rfl
    | lit l h bb fb lp => exact SimC.pure hs₄ rfl
    | fvar idx nm t h bb fb lp => exact SimC.pure hs₄ rfl
    | app f' a' h bb fb lp => exact SimC.pure hs₄ rfl
    | lam nm t b' m h bb fb lp => exact SimC.pure hs₄ rfl
    | forallE nm t b' m h bb fb lp => exact SimC.pure hs₄ rfl
    | letE nm t v b' h bb fb lp => exact SimC.pure hs₄ rfl
    | proj sn j' e' h bb fb lp => exact SimC.pure hs₄ rfl

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- Port of `etaCertI_sim`.  The name and binder-meta bridges collapse:
the cached representation stores `Name`s and `BinderMeta`s directly, so
`hn₁` and `hbm₁` are identities and the spec side reads the very
arguments the twin is given. -/
theorem etaCertC_sim (ih : SSimC mode env f) {d : Nat} {n₁ : Name}
    {ty₁ body₁ b : ExprC} {ty₁x body₁x bx : Expr} {m₁ : BinderMeta}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hty : RelC ty₁ ty₁x) (hbody : RelC body₁ body₁x) (hb : RelC b bx)
    (hwty : Expr.WScoped d ty₁x) (hwbody : Expr.WScoped d body₁x)
    (hwb : Expr.WScoped d bx) :
    SimC mode env s₀ RelVC
      (etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        n₁ ty₁ body₁ m₁ b)
      (etaCert mode (fueledFns mode env) env d n₁ ty₁x body₁x m₁ bx) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).infer d b >>= fun tb =>
      (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
      viewI wtb >>= fun n =>
      match n with
      | some (.forallE _ ty₂ _ m₂) =>
        (coreKnotI mode (mkFEnv env) f).defeq d ty₂ ty₁ >>= fun r =>
        if r then
          internI (.fvar d n₁ ty₁) >>= fun fv =>
          inst1M body₁ fv >>= fun b₁ =>
          internI (.app b fv) >>= fun ba =>
          (coreKnotI mode (mkFEnv env) f).defeq (d + 1) b₁ ba
            >>= fun r₂ =>
          if r₂ = true then
            if (mode.verified && !(m₁.pw.equiv m₂.pw)) = true then
              (throw (.notImplemented "sort-annotation mismatch (eta)")
                : CheckCM Unit) >>= fun _ => pure true
            else pure true
          else pure false
        else pure false
      | _ => pure false)
    ((fueledFns mode env).infer d bx >>= fun tb =>
      (fueledFns mode env).whnf d tb >>= fun wtb =>
      match wtb with
      | .forallE _ ty₂ _ m₂ =>
        (fueledFns mode env).defeq d ty₂ ty₁x >>= fun r =>
        if r then
          (fueledFns mode env).defeq (d + 1)
            (body₁x.instantiate1 (.fvar d n₁ ty₁x))
            (.app bx (.fvar d n₁ ty₁x)) >>= fun r₂ =>
          if r₂ = true then
            if (mode.verified && !(m₁.pw.equiv m₂.pw)) = true then
              (throw (.notImplemented "sort-annotation mismatch (eta)")
                : FueledM Unit) >>= fun _ => pure true
            else pure true
          else pure false
        else pure false
      | _ => pure false)
  obtain ⟨hwty₁, rfl⟩ := hty
  obtain ⟨hwbody₁, rfl⟩ := hbody
  obtain ⟨hwb₁, rfl⟩ := hb
  have hty : RelC ty₁ (eraseC ty₁) := ⟨hwty₁, rfl⟩
  have hbody : RelC body₁ (eraseC body₁) := ⟨hwbody₁, rfl⟩
  have hb : RelC b (eraseC b) := ⟨hwb₁, rfl⟩
  refine SimC.bind (ih.infer hs hb hwb) (fun s₁ tb tbx hs₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htbd hwtb) (fun s₂ wtb wtbx hs₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  refine SimC.view ?_
  obtain ⟨hwc, rfl⟩ := hwtbd
  cases wtb with
  | forallE nm ty₂ b₂ m₂ h bb fb lp =>
    obtain ⟨hwty₂, hwb₂, -⟩ := hwc.forallE_inv
    have hwty₂x : Expr.WScoped d (eraseC ty₂) := by
      rw [show eraseC (ExprC.forallE nm ty₂ b₂ m₂ h bb fb lp)
          = Expr.forallE nm (eraseC ty₂) (eraseC b₂) m₂ from rfl] at hwwtb
      simp only [Expr.WScoped] at hwwtb
      exact hwwtb.1
    refine SimC.bind (ih.defeq hs₂ ⟨hwty₂, rfl⟩ hty hwty₂x hwty)
      (fun s₄ r r' hs₄ hPr => ?_)
    obtain rfl : r = r' := hPr
    cases r with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₄ rfl
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind_left
        (internI_eff hs₄ (n := ExprView.fvar d n₁ ty₁) hwty₁)
        (fun s₅ fv hs₅ hQfv => ?_)
      have hQfv' : RelC fv (.fvar d n₁ (eraseC ty₁)) := hQfv
      refine SimC.bind_left (inst1M_eff hs₅ hbody hQfv')
        (fun s₆ b₁ hs₆ hQb₁ => ?_)
      refine SimC.bind_left
        (internI_eff hs₆ (n := ExprView.app b fv) ⟨hwb₁, hQfv.1⟩)
        (fun s₇ ba hs₇ hQba => ?_)
      have hQba' : RelC ba (.app (eraseC b) (.fvar d n₁ (eraseC ty₁))) := by
        refine ⟨hQba.1, ?_⟩
        rw [show eraseC ba = .app (eraseC b) (eraseC fv) from hQba.2,
          hQfv'.2]
      have hwapp : Expr.WScoped (d + 1)
          (.app (eraseC b) (.fvar d n₁ (eraseC ty₁))) := by
        simp only [Expr.WScoped]
        exact ⟨Expr.WScoped.mono (Nat.le_succ d) hwb, Nat.lt_succ_self d,
          hwty⟩
      refine SimC.bind (ih.defeq hs₇ hQb₁ hQba'
        (Expr.WScoped.instantiate1 hwty 0 hwbody) hwapp)
        (fun s₈ r₂ r₂x hs₈ hPr₂ => ?_)
      obtain rfl : r₂ = r₂x := hPr₂
      cases r₂ with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₈ rfl
      | true =>
        simp only [↓reduceIte]
        split
        · exact SimC.throw_bind
        · exact SimC.pure hs₈ rfl
  | bvar k h bb fb lp => exact SimC.pure hs₂ rfl
  | sort u h bb fb lp => exact SimC.pure hs₂ rfl
  | const nm us h bb fb lp => exact SimC.pure hs₂ rfl
  | lit l h bb fb lp => exact SimC.pure hs₂ rfl
  | fvar idx nm t h bb fb lp => exact SimC.pure hs₂ rfl
  | app f' a' h bb fb lp => exact SimC.pure hs₂ rfl
  | lam nm t b' m h bb fb lp => exact SimC.pure hs₂ rfl
  | letE nm t v b' h bb fb lp => exact SimC.pure hs₂ rfl
  | proj sn j' e' h bb fb lp => exact SimC.pure hs₂ rfl

/-- Indexed readout of a related list (the `DenL.getD` transposition:
the erasure is a `List.map`, so the default travels with it). -/
theorem RelCL.getD {dflt : ExprC} {dfltx : Expr} (hd : RelC dflt dfltx) :
    ∀ (n : Nat) {l : List ExprC} {xs : List Expr}, RelCL l xs →
      RelC (l.getD n dflt) (xs.getD n dfltx)
  | _, [], xs, h => by rw [h.nil_inv]; exact hd
  | 0, a :: as, xs, h => by
    obtain ⟨x, xs', rfl, hax, -⟩ := h.cons_inv
    exact hax
  | n + 1, a :: as, xs, h => by
    obtain ⟨x, xs', rfl, -, has⟩ := h.cons_inv
    exact RelCL.getD hd n has

/-- Port of `projCertI_sim`. -/
theorem projCertC_sim (ih : SSimC mode env f) {d : Nat} {i : ExprC}
    {e₂ : Expr} {idx : Nat} {fl sl : Level} {nP : Nat}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e₂) (hw : Expr.WScoped d e₂) :
    SimC mode env s₀ RelVC
      (projCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i idx
        fl sl nP)
      (projCert (fueledFns mode env) env d e₂ idx fl sl nP) := by
  show SimC mode env s₀ RelVC
    (internI (.bvar 0) >>= fun bvar0 =>
      Setlec.Cached.withStore (·.getAppArgsI i) >>= fun args =>
      (coreKnotI mode (mkFEnv env) f).infer d (args.getD (nP + idx) bvar0) >>=
        fun ta =>
      (coreKnotI mode (mkFEnv env) f).infer d ta >>= fun tta =>
      (coreKnotI mode (mkFEnv env) f).whnf d tta >>= fun wtta =>
      viewI wtta >>= fun n =>
      match n with
      | some (.sort uT) =>
        isEquivLM uT fl >>= fun oT =>
        liftFueled "level comparison" oT >>= fun okT =>
        (coreKnotI mode (mkFEnv env) f).infer d i >>= fun te =>
        (coreKnotI mode (mkFEnv env) f).infer d te >>= fun tte =>
        (coreKnotI mode (mkFEnv env) f).whnf d tte >>= fun wtte =>
        viewI wtte >>= fun n' =>
        match n' with
        | some (.sort wT) =>
          isEquivLM wT sl >>= fun oW =>
          liftFueled "level comparison" oW >>= fun okW =>
          pure (okT && okW)
        | _ => pure false
      | _ => pure false)
    (projCert (fueledFns mode env) env d e₂ idx fl sl nP)
  refine SimC.bind_left (internI_eff hs (n := ExprView.bvar 0) trivial)
    (fun s₁ bvar0 hs₁ hQ0 => ?_)
  refine SimC.withStore ?_
  obtain ⟨hwc, rfl⟩ := hden
  have hargs := ExprC.getAppArgs_spec hwc
  have hargd : RelC ((ExprC.getAppArgs i).getD (nP + idx) bvar0)
      ((eraseC i).getAppArgs.getD (nP + idx) (.bvar 0)) :=
    RelCL.getD hQ0 (nP + idx) hargs
  have hwarg : Expr.WScoped d
      ((eraseC i).getAppArgs.getD (nP + idx) (.bvar 0)) :=
    wscoped_getD hw.getAppArgs _
  refine SimC.bind (ih.infer hs₁ hargd hwarg)
    (fun s₂ ta tax hs₂ hP₂ => ?_)
  obtain ⟨htad, hwta⟩ := hP₂
  refine SimC.bind (ih.infer hs₂ htad hwta) (fun s₃ tta ttax hs₃ hP₃ => ?_)
  obtain ⟨httad, hwtta⟩ := hP₃
  refine SimC.bind (ih.whnf hs₃ httad hwtta) (fun s₄ wtta wttax hs₄ hP₄ => ?_)
  obtain ⟨hwttad, hwwtta⟩ := hP₄
  refine SimC.view ?_
  obtain ⟨hwc₄, rfl⟩ := hwttad
  cases wtta with
  | sort uT h bb fb lp =>
    refine SimC.bind_left (isEquivLM_eff hs₄ uT fl)
      (fun s₄o oT hs₄o hoT => ?_)
    subst hoT
    refine SimC.bind (SimC.liftFueled _ _ hs₄o)
      (fun s₅ okT okT' hs₅ hPok => ?_)
    obtain rfl : okT = okT' := hPok
    refine SimC.bind (ih.infer hs₅ ⟨hwc, rfl⟩ hw)
      (fun s₆ te tex hs₆ hP₆ => ?_)
    obtain ⟨hted, hwte⟩ := hP₆
    refine SimC.bind (ih.infer hs₆ hted hwte) (fun s₇ tte ttex hs₇ hP₇ => ?_)
    obtain ⟨htted, hwtte⟩ := hP₇
    refine SimC.bind (ih.whnf hs₇ htted hwtte)
      (fun s₈ wtte wttex hs₈ hP₈ => ?_)
    obtain ⟨hwtted, hwwtte⟩ := hP₈
    refine SimC.view ?_
    obtain ⟨hwc₈, rfl⟩ := hwtted
    cases wtte with
    | sort wT h' bb' fb' lp' =>
      refine SimC.bind_left (isEquivLM_eff hs₈ wT sl)
        (fun s₈o oW hs₈o hoW => ?_)
      subst hoW
      refine SimC.bind (SimC.liftFueled _ _ hs₈o)
        (fun s₉ okW okW' hs₉ hPok' => ?_)
      obtain rfl : okW = okW' := hPok'
      exact SimC.pure hs₉ rfl
    | bvar k h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | const nm us h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | lit l h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | fvar idx' nm t h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | app f' a' h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | lam nm t b' m h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | forallE nm t b' m h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | letE nm t v b' h' bb' fb' lp' => exact SimC.pure hs₈ rfl
    | proj sn j' e' h' bb' fb' lp' => exact SimC.pure hs₈ rfl
  | bvar k h bb fb lp => exact SimC.pure hs₄ rfl
  | const nm us h bb fb lp => exact SimC.pure hs₄ rfl
  | lit l h bb fb lp => exact SimC.pure hs₄ rfl
  | fvar idx' nm t h bb fb lp => exact SimC.pure hs₄ rfl
  | app f' a' h bb fb lp => exact SimC.pure hs₄ rfl
  | lam nm t b' m h bb fb lp => exact SimC.pure hs₄ rfl
  | forallE nm t b' m h bb fb lp => exact SimC.pure hs₄ rfl
  | letE nm t v b' h bb fb lp => exact SimC.pure hs₄ rfl
  | proj sn j' e' h bb fb lp => exact SimC.pure hs₄ rfl

/-- Port of `structUnitCertI_sim`. -/
theorem structUnitCertC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (structUnitCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (structUnitCert (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).infer d i >>= fun ta =>
      (coreKnotI mode (mkFEnv env) f).whnf d ta >>= fun wta =>
      Setlec.Cached.withStore (fun st => st.getNode (st.getAppFnI wta)) >>=
        fun n =>
      match n with
      | some (.const T us') =>
        readbackNM T >>= fun Tn =>
        match (mkFEnv env).find? Tn with
        | some (.indInfo cvT caps) =>
          Setlec.Cached.withStore (·.getAppArgsI wta) >>= fun targs =>
          if caps.unitlike = true ∧
              reservedBasisNames.contains Tn = false ∧
              targs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length ∧
              (cvT.type.stripPis caps.unitParams).isSome = true then
            (coreKnotI mode (mkFEnv env) f).infer d j >>= fun tb =>
            (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
            (coreKnotI mode (mkFEnv env) f).defeq d wta wtb >>= fun r =>
            if r then
              constTyAtM (mkFEnv env) T Tn us' >>= fun tyT =>
              iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d tyT
                targs
            else pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    ((fueledFns mode env).infer d a >>= fun ta =>
      (fueledFns mode env).whnf d ta >>= fun wta =>
      match wta.getAppFn with
      | .const T us' =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if caps.unitlike = true ∧
              reservedBasisNames.contains T = false ∧
              wta.getAppArgs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length ∧
              (cvT.type.stripPis caps.unitParams).isSome = true then
            (fueledFns mode env).infer d b >>= fun tb =>
            (fueledFns mode env).whnf d tb >>= fun wtb =>
            (fueledFns mode env).defeq d wta wtb >>= fun r =>
            if r then
              iotaCerts (fueledFns mode env) env d
                (cvT.type.instantiateLevelParams cvT.levelParams us')
                wta.getAppArgs
            else pure false
          else pure false
        | _ => pure false
      | _ => pure false)
  refine SimC.bind (ih.infer hs hdena hwa) (fun s₁ ta tax hs₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htad hwta) (fun s₂ wta wtax hs₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimC.withStore ?_
  obtain ⟨hwc, rfl⟩ := hwtad
  have hargs := ExprC.getAppArgs_spec hwc
  have hlena : (ExprC.getAppArgs wta).length
      = (eraseC wta).getAppArgs.length := RelCL.length hargs
  obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec hwc
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hg : ExprC.getAppFn wta = g at hwfn hfn ⊢
  cases g with
  | const T us' h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.const T us' from hfn.symm]
    dsimp only
    refine SimC.bind_left (readbackNM_eff hs₂ T)
      (fun s₂' Tv hs₂ hTv => ?_)
    subst hTv
    rw [mkFEnv_find?]
    cases hfT : env.find? Tv with
    | none => exact SimC.pure hs₂ rfl
    | some ci =>
      cases ci with
      | indInfo cvT caps =>
        dsimp only
        refine SimC.withStore ?_
        simp only [CStore.getAppArgsI, hlena]
        split
        · refine SimC.bind (ih.infer hs₂ hdenb hwb)
            (fun s₃ tb tbx hs₃ hP₃ => ?_)
          obtain ⟨htbd, hwtb⟩ := hP₃
          refine SimC.bind (ih.whnf hs₃ htbd hwtb)
            (fun s₄ wtb wtbx hs₄ hP₄ => ?_)
          obtain ⟨hwtbd, hwwtb⟩ := hP₄
          refine SimC.bind (ih.defeq hs₄ ⟨hwc, rfl⟩ hwtbd hwwta hwwtb)
            (fun s₅ r r' hs₅ hPr => ?_)
          obtain rfl : r = r' := hPr
          cases r with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.pure hs₅ rfl
          | true =>
            simp only [↓reduceIte]
            refine SimC.bind_left (constTyAtM_eff hs₅ hfT)
              (fun s₆ tyT hs₆ hQty => ?_)
            have htyw : Expr.WScoped d
                (cvT.type.instantiateLevelParams cvT.levelParams us') := by
              obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
              exact wscoped_instLevels_of_not_hasFvar htf _ _
            exact iotaCertsC_sim ih hs₆ hQty htyw hargs hwwta.getAppArgs
        · exact SimC.pure hs₂ rfl
      | axiomInfo cv => exact SimC.pure hs₂ rfl
      | defnInfo cv v h => exact SimC.pure hs₂ rfl
      | thmInfo cv v => exact SimC.pure hs₂ rfl
      | ctorInfo cv nP nF => exact SimC.pure hs₂ rfl
      | recInfo cv mI rP rules => exact SimC.pure hs₂ rfl
      | projInfo entry => exact SimC.pure hs₂ rfl
  | bvar k h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.bvar k from hfn.symm]
    exact SimC.pure hs₂ rfl
  | sort u h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.sort u from hfn.symm]
    exact SimC.pure hs₂ rfl
  | lit l h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.lit l from hfn.symm]
    exact SimC.pure hs₂ rfl
  | fvar idx nm t h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.fvar idx nm (eraseC t)
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | app f' a' h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.app (eraseC f') (eraseC a')
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | lam nm t b' m h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.lam nm (eraseC t) (eraseC b') m
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | forallE nm t b' m h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.forallE nm (eraseC t) (eraseC b') m
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | letE nm t v b' h bb fb lp =>
    rw [show (eraseC wta).getAppFn
      = Expr.letE nm (eraseC t) (eraseC v) (eraseC b') from hfn.symm]
    exact SimC.pure hs₂ rfl
  | proj sn j' e' h bb fb lp =>
    rw [show (eraseC wta).getAppFn = Expr.proj sn j' (eraseC e')
      from hfn.symm]
    exact SimC.pure hs₂ rfl

end Walks2

section Walks3

variable {env : Env} {f : Nat}

private theorem pairEtaCertC_unfold (env : Env) (d : Nat) (a b : Expr) :
    pairEtaCert mode (fueledFns mode env) env d a b =
    (match a with
    | .app (.app (.app (.app (.const c us) _pα) _pβ) xs₁) xs₂ =>
      match env.find? c with
      | some (.ctorInfo _cvm 2 2) =>
        (fueledFns mode env).infer d b >>= fun tb =>
        (fueledFns mode env).whnf d tb >>= fun wtb =>
        match wtb with
        | .app (.app (.const c' us') _A) _B =>
          match env.find? c' with
          | some (.indInfo _ _) =>
            match env.find? (c'.str "rec") with
            | some (.recInfo _ mI rP [rr]) =>
              if rr.ctor = c ∧ rr.nfields = 2 ∧ mI = rP ∧
                  reservedBasisNames.contains (c'.str "rec") = true then
                liftFueled "level comparison"
                  (Level.isEquivList us us') >>= fun ok =>
                if ok then
                  (fueledFns mode env).defeq d _pα _A >>= fun rA =>
                  if rA then
                    (fueledFns mode env).defeq d _pβ _B >>= fun rB =>
                    if rB then
                      (fueledFns mode env).defeq d xs₁ (.proj c' 0 b) >>= fun r₁ =>
                      if r₁ then
                        (fueledFns mode env).defeq d xs₂ (.proj c' 1 b) >>=
                          fun r₂ =>
                        if r₂ then pure true
                        else pure false
                      else pure false
                    else pure false
                  else pure false
                else pure false
              else pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false) := rfl

/-- Port of `pairEtaCertI_sim`. -/
theorem pairEtaCertC_sim (ih : SSimC mode env f) (_henv : EnvWF env)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (pairEtaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (pairEtaCert mode (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (viewI i >>= fun n₀ =>
      match n₀ with
      | some (.app f₄ s₂) =>
        viewI f₄ >>= fun n₁ =>
        match n₁ with
        | some (.app f₃ s₁) =>
          viewI f₃ >>= fun n₂ =>
          match n₂ with
          | some (.app f₂ pβ) =>
            viewI f₂ >>= fun n₃ =>
            match n₃ with
            | some (.app f₁ pα) =>
              viewI f₁ >>= fun n₄ =>
              match n₄ with
              | some (.const c us) =>
                readbackNM c >>= fun cn =>
                match (mkFEnv env).find? cn with
                | some (.ctorInfo _cvm 2 2) =>
                  (coreKnotI mode (mkFEnv env) f).infer d j >>= fun tb =>
                  (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
                  viewI wtb >>= fun m₀ =>
                  match m₀ with
                  | some (.app g₂ B) =>
                    viewI g₂ >>= fun m₁ =>
                    match m₁ with
                    | some (.app g₁ A) =>
                      viewI g₁ >>= fun m₂ =>
                      match m₂ with
                      | some (.const c' us') =>
                        readbackNM c' >>= fun c'n =>
                        match (mkFEnv env).find? c'n with
                        | some (.indInfo _ _) =>
                          match (mkFEnv env).find? (c'n.str "rec") with
                          | some (.recInfo _ mI rP [rr]) =>
                            if rr.ctor = cn ∧ rr.nfields = 2 ∧ mI = rP ∧
                                reservedBasisNames.contains (c'n.str "rec")
                                  = true then
                              isEquivListLM us us' >>= fun o =>
                              liftFueled "level comparison" o >>= fun ok =>
                              if ok then
                                (coreKnotI mode (mkFEnv env) f).defeq d pα A >>=
                                  fun rA =>
                                if rA then
                                  (coreKnotI mode (mkFEnv env) f).defeq d pβ B >>=
                                    fun rB =>
                                  if rB then
                                    internI (.proj c' 0 j) >>= fun p₀ =>
                                    (coreKnotI mode (mkFEnv env) f).defeq d s₁
                                      p₀ >>= fun r₁ =>
                                    if r₁ then
                                      internI (.proj c' 1 j) >>= fun p₁ =>
                                      (coreKnotI mode (mkFEnv env) f).defeq d s₂
                                        p₁ >>= fun r₂ =>
                                      if r₂ then pure true
                                      else pure false
                                    else pure false
                                  else pure false
                                else pure false
                              else pure false
                            else pure false
                          | _ => pure false
                        | _ => pure false
                      | _ => pure false
                    | _ => pure false
                  | _ => pure false
                | _ => pure false
              | _ => pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false)
    (pairEtaCert mode (fueledFns mode env) env d a b)
  obtain ⟨hwca, rfl⟩ := hdena
  obtain ⟨hwcb, rfl⟩ := hdenb
  have hdenb : RelC j (eraseC j) := ⟨hwcb, rfl⟩
  rw [pairEtaCertC_unfold]
  refine SimC.view ?_
  cases i with
  | app f₄ s₂ h₄ bb₄ fb₄ lp₄ =>
    obtain ⟨hwf₄, hws₂w⟩ := wscoped_appC_inv hwa
    obtain ⟨hwcf₄, hwcs₂, -⟩ := hwca.app_inv
    refine SimC.view ?_
    cases f₄ with
    | app f₃ s₁ h₃ bb₃ fb₃ lp₃ =>
      obtain ⟨hwf₃, hws₁w⟩ := wscoped_appC_inv hwf₄
      obtain ⟨hwcf₃, hwcs₁, -⟩ := hwcf₄.app_inv
      refine SimC.view ?_
      cases f₃ with
      | app f₂ pβ h₂ bb₂ fb₂ lp₂ =>
        obtain ⟨hwf₂, hwpβ⟩ := wscoped_appC_inv hwf₃
        obtain ⟨hwcf₂, hwcpβ, -⟩ := hwcf₃.app_inv
        refine SimC.view ?_
        cases f₂ with
        | app f₁ pα h₁ bb₁ fb₁ lp₁ =>
          obtain ⟨hwf₁, hwpα⟩ := wscoped_appC_inv hwf₂
          obtain ⟨hwcf₁, hwcpα, -⟩ := hwcf₂.app_inv
          refine SimC.view ?_
          cases f₁ with
          | const c us h₀ bb₀ fb₀ lp₀ =>
            dsimp only [eraseC]
            refine SimC.bind_left (readbackNM_eff hs c)
              (fun s₀' cv hs hcv => ?_)
            subst cv
            rw [mkFEnv_find?]
            cases hfc : env.find? c with
            | none => exact SimC.pure hs rfl
            | some ci =>
              cases ci with
              | ctorInfo cvm nP nF =>
                match nP, nF with
                | 2, 2 =>
                  refine SimC.bind (ih.infer hs hdenb hwb)
                    (fun s₁' tb tbx hs₁' hP => ?_)
                  obtain ⟨htbd, hwtb⟩ := hP
                  refine SimC.bind (ih.whnf hs₁' htbd hwtb)
                    (fun s₂' wtb wtbx hs₂' hP₂ => ?_)
                  obtain ⟨hwtbd, hwwtb⟩ := hP₂
                  refine SimC.view ?_
                  obtain ⟨hwcw, rfl⟩ := hwtbd
                  cases wtb with
                  | app g₂ B hgB bbB fbB lpB =>
                    obtain ⟨hwg₂, hwB⟩ := wscoped_appC_inv hwwtb
                    obtain ⟨hwcg₂, hwcB, -⟩ := hwcw.app_inv
                    refine SimC.view ?_
                    cases g₂ with
                    | app g₁ A hgA bbA fbA lpA =>
                      obtain ⟨hwg₁, hwA⟩ := wscoped_appC_inv hwg₂
                      obtain ⟨hwcg₁, hwcA, -⟩ := hwcg₂.app_inv
                      refine SimC.view ?_
                      cases g₁ with
                      | const c' us' hc'0 bbc' fbc' lpc' =>
                        dsimp only [eraseC]
                        refine SimC.bind_left (readbackNM_eff hs₂' c')
                          (fun s₂'' c'w hs₂' hc'w => ?_)
                        subst c'w
                        rw [mkFEnv_find?, mkFEnv_find?]
                        cases hfc' : env.find? c' with
                        | none => exact SimC.pure hs₂' rfl
                        | some ci' =>
                          cases ci' with
                          | indInfo cvI capsI =>
                            dsimp only
                            cases hfr : env.find? (c'.str "rec") with
                            | none => exact SimC.pure hs₂' rfl
                            | some cir =>
                              cases cir with
                              | recInfo cvr mI rP rules =>
                                match rules with
                                | [] => exact SimC.pure hs₂' rfl
                                | _ :: _ :: _ => exact SimC.pure hs₂' rfl
                                | [rr] =>
                                  dsimp only
                                  split
                                  · refine SimC.bind_left
                                      (isEquivListLM_eff hs₂')
                                      (fun s₂o o hs₂o ho => ?_)
                                    subst ho
                                    refine SimC.bind
                                      (SimC.liftFueled _ _ hs₂o)
                                      (fun s₃' ok ok' hs₃' hPok => ?_)
                                    obtain rfl : ok = ok' := hPok
                                    cases ok with
                                    | false =>
                                      simp only [Bool.false_eq_true,
                                        ↓reduceIte]
                                      exact SimC.pure hs₃' rfl
                                    | true =>
                                      simp only [↓reduceIte]
                                      refine SimC.bind (ih.defeq hs₃'
                                        ⟨hwcpα, rfl⟩ ⟨hwcA, rfl⟩ hwpα hwA)
                                        (fun sA' rA rA' hsA' hPrA => ?_)
                                      obtain rfl : rA = rA' := hPrA
                                      cases rA with
                                      | false =>
                                        simp only [Bool.false_eq_true,
                                          ↓reduceIte]
                                        exact SimC.pure hsA' rfl
                                      | true =>
                                        simp only [↓reduceIte]
                                        refine SimC.bind (ih.defeq hsA'
                                          ⟨hwcpβ, rfl⟩ ⟨hwcB, rfl⟩ hwpβ hwB)
                                          (fun sB' rB rB' hsB' hPrB => ?_)
                                        obtain rfl : rB = rB' := hPrB
                                        cases rB with
                                        | false =>
                                          simp only [Bool.false_eq_true,
                                            ↓reduceIte]
                                          exact SimC.pure hsB' rfl
                                        | true =>
                                          simp only [↓reduceIte]
                                          refine SimC.bind_left
                                            (internI_eff hsB'
                                              (n := ExprView.proj c' 0 j)
                                              hwcb)
                                            (fun s₄' p₀ hs₄' hQ₀ => ?_)
                                          have hQ₀' :
                                              RelC p₀ (.proj c' 0 (eraseC j)) :=
                                            hQ₀
                                          have hwp₀ : Expr.WScoped d
                                              (.proj c' 0 (eraseC j)) := by
                                            simp only [Expr.WScoped]
                                            exact hwb
                                          refine SimC.bind (ih.defeq hs₄'
                                            ⟨hwcs₁, rfl⟩ hQ₀' hws₁w hwp₀)
                                            (fun s₅' r₁ r₁' hs₅' hPr₁ => ?_)
                                          obtain rfl : r₁ = r₁' := hPr₁
                                          cases r₁ with
                                          | false =>
                                            simp only [Bool.false_eq_true,
                                              ↓reduceIte]
                                            exact SimC.pure hs₅' rfl
                                          | true =>
                                            simp only [↓reduceIte]
                                            refine SimC.bind_left
                                              (internI_eff hs₅'
                                                (n := ExprView.proj c' 1 j)
                                                hwcb)
                                              (fun s₆' p₁ hs₆' hQ₁ => ?_)
                                            have hQ₁' : RelC p₁
                                                (.proj c' 1 (eraseC j)) := hQ₁
                                            have hwp₁ : Expr.WScoped d
                                                (.proj c' 1 (eraseC j)) := by
                                              simp only [Expr.WScoped]
                                              exact hwb
                                            refine SimC.bind (ih.defeq hs₆'
                                              ⟨hwcs₂, rfl⟩ hQ₁' hws₂w hwp₁)
                                              (fun s₇' r₂ r₂' hs₇' hPr₂ => ?_)
                                            obtain rfl : r₂ = r₂' := hPr₂
                                            cases r₂ with
                                            | false =>
                                              simp only [Bool.false_eq_true,
                                                ↓reduceIte]
                                              exact SimC.pure hs₇' rfl
                                            | true =>
                                              simp only [↓reduceIte]
                                              exact SimC.pure hs₇' rfl
                                  · exact SimC.pure hs₂' rfl
                              | axiomInfo cv => exact SimC.pure hs₂' rfl
                              | defnInfo cv v h => exact SimC.pure hs₂' rfl
                              | thmInfo cv v => exact SimC.pure hs₂' rfl
                              | indInfo cv caps => exact SimC.pure hs₂' rfl
                              | ctorInfo cv nP' nF' => exact SimC.pure hs₂' rfl
                              | projInfo entry => exact SimC.pure hs₂' rfl
                          | axiomInfo cv => exact SimC.pure hs₂' rfl
                          | defnInfo cv v h => exact SimC.pure hs₂' rfl
                          | thmInfo cv v => exact SimC.pure hs₂' rfl
                          | ctorInfo cv nP' nF' => exact SimC.pure hs₂' rfl
                          | recInfo cv mI rP rules => exact SimC.pure hs₂' rfl
                          | projInfo entry => exact SimC.pure hs₂' rfl
                      | bvar k hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                      | sort u hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                      | lit l hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                      | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                      | app g₀ a₀ hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                      | lam nm t b' m hk bbk fbk lpk =>
                        exact SimC.pure hs₂' rfl
                      | forallE nm t b' m hk bbk fbk lpk =>
                        exact SimC.pure hs₂' rfl
                      | letE nm t v b' hk bbk fbk lpk =>
                        exact SimC.pure hs₂' rfl
                      | proj sn jx e' hk bbk fbk lpk =>
                        exact SimC.pure hs₂' rfl
                    | bvar k hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                    | sort u hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                    | const nm us'' hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                    | lit l hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                    | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                    | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                    | forallE nm t b' m hk bbk fbk lpk =>
                      exact SimC.pure hs₂' rfl
                    | letE nm t v b' hk bbk fbk lpk =>
                      exact SimC.pure hs₂' rfl
                    | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | bvar k hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | sort u hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | const nm us'' hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | lit l hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | forallE nm t b' m hk bbk fbk lpk =>
                    exact SimC.pure hs₂' rfl
                  | letE nm t v b' hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                  | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs₂' rfl
                | 0, _ => exact SimC.pure hs rfl
                | 1, _ => exact SimC.pure hs rfl
                | Nat.succ (Nat.succ (Nat.succ _)), _ => exact SimC.pure hs rfl
                | 2, 0 => exact SimC.pure hs rfl
                | 2, 1 => exact SimC.pure hs rfl
                | 2, Nat.succ (Nat.succ (Nat.succ _)) => exact SimC.pure hs rfl
              | axiomInfo cv => exact SimC.pure hs rfl
              | defnInfo cv v h => exact SimC.pure hs rfl
              | thmInfo cv v => exact SimC.pure hs rfl
              | indInfo cv caps => exact SimC.pure hs rfl
              | recInfo cv mI rP rules => exact SimC.pure hs rfl
              | projInfo entry => exact SimC.pure hs rfl
          | bvar k hk bbk fbk lpk => exact SimC.pure hs rfl
          | sort u hk bbk fbk lpk => exact SimC.pure hs rfl
          | lit l hk bbk fbk lpk => exact SimC.pure hs rfl
          | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs rfl
          | app f₀ a₀ hk bbk fbk lpk => exact SimC.pure hs rfl
          | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
          | forallE nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
          | letE nm t v b' hk bbk fbk lpk => exact SimC.pure hs rfl
          | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs rfl
        | bvar k hk bbk fbk lpk => exact SimC.pure hs rfl
        | sort u hk bbk fbk lpk => exact SimC.pure hs rfl
        | const nm us hk bbk fbk lpk => exact SimC.pure hs rfl
        | lit l hk bbk fbk lpk => exact SimC.pure hs rfl
        | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs rfl
        | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
        | forallE nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
        | letE nm t v b' hk bbk fbk lpk => exact SimC.pure hs rfl
        | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs rfl
      | bvar k hk bbk fbk lpk => exact SimC.pure hs rfl
      | sort u hk bbk fbk lpk => exact SimC.pure hs rfl
      | const nm us hk bbk fbk lpk => exact SimC.pure hs rfl
      | lit l hk bbk fbk lpk => exact SimC.pure hs rfl
      | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs rfl
      | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
      | forallE nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
      | letE nm t v b' hk bbk fbk lpk => exact SimC.pure hs rfl
      | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs rfl
    | bvar k hk bbk fbk lpk => exact SimC.pure hs rfl
    | sort u hk bbk fbk lpk => exact SimC.pure hs rfl
    | const nm us hk bbk fbk lpk => exact SimC.pure hs rfl
    | lit l hk bbk fbk lpk => exact SimC.pure hs rfl
    | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs rfl
    | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
    | forallE nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
    | letE nm t v b' hk bbk fbk lpk => exact SimC.pure hs rfl
    | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs rfl
  | bvar k hk bbk fbk lpk => exact SimC.pure hs rfl
  | sort u hk bbk fbk lpk => exact SimC.pure hs rfl
  | const nm us hk bbk fbk lpk => exact SimC.pure hs rfl
  | lit l hk bbk fbk lpk => exact SimC.pure hs rfl
  | fvar ix nm t hk bbk fbk lpk => exact SimC.pure hs rfl
  | lam nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
  | forallE nm t b' m hk bbk fbk lpk => exact SimC.pure hs rfl
  | letE nm t v b' hk bbk fbk lpk => exact SimC.pure hs rfl
  | proj sn jx e' hk bbk fbk lpk => exact SimC.pure hs rfl

end Walks3

section Walks4

variable {env : Env} {f : Nat}

/-- Port of `projAppsI_eff`: the cached projection-application spine
denotes the spec's mapped list. -/
theorem projAppsC_eff (T : Name) (us' : List Level) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {targs : List ExprC} {xs : List Expr} {b : ExprC} {xb : Expr},
      RelCL targs xs → RelC b xb →
      CEff mode env s₀ (fun rs => RelCL rs
          (l.map fun i => Expr.mkAppN (.const (projFnName T i) us')
            (xs ++ [xb])))
        (projAppsI T us' targs b l)
  | [], s₀, hs, targs, xs, b, xb, htargs, hb => by
    exact CEff.pure hs RelCL.nil
  | i :: rest, s₀, hs, targs, xs, b, xb, htargs, hb => by
    show CEff mode env s₀ _
      (projFnIdxM T i >>= fun pf =>
        internI (.const pf us') >>= fun hd =>
        mkAppNM hd (targs ++ [b]) >>= fun r =>
        projAppsI T us' targs b rest >>= fun rs =>
        pure (r :: rs))
    refine CEff.bind (projFnIdxM_eff hs T i) (fun s₀' pf hs₀' hQpf => ?_)
    subst hQpf
    refine CEff.bind
      (internI_eff hs₀' (n := ExprView.const (projFnName T i) us') trivial)
      (fun s₁ hd hs₁ hQh => ?_)
    refine CEff.bind
      (mkAppNM_eff hs₁ hQh (htargs.append (RelCL.cons hb RelCL.nil)))
      (fun s₂ r hs₂ hQr => ?_)
    refine CEff.bind (projAppsC_eff T us' rest hs₂ htargs hb)
      (fun s₃ rs hs₃ hQrs => ?_)
    exact CEff.pure hs₃ (RelCL.cons hQr hQrs)

/-- Port of `structEtaProjCertsI_sim`. -/
theorem structEtaProjCertsC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} (TI : Name) (T : Name) (us' : List Level) (lpsT : List Name) :
    ∀ (idxs : List Nat) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {targs : List ExprC} {xs : List Expr} {b : ExprC} {xb : Expr},
      RelCL targs xs → RelC b xb →
      (∀ x ∈ xs, Expr.WScoped d x) → Expr.WScoped d xb →
      SimC mode env s₀ RelVC
        (structEtaProjCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          TI T us' targs b lpsT idxs)
        (structEtaProjCerts (fueledFns mode env) env d T us' xs xb lpsT idxs)
  | [], s₀, hs, targs, xs, b, xb, htargs, hb, hwxs, hwxb => by
    exact SimC.pure hs rfl
  | i :: rest, s₀, hs, targs, xs, b, xb, htargs, hb, hwxs, hwxb => by
    show SimC mode env s₀ RelVC
      (match (mkFEnv env).find? (projFnName T i) with
      | some (.recInfo cvp _ _ _) =>
        if cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (targs.length + 1)).isSome = true then
          projFnIdxM TI i >>= fun pf =>
          constTyAtM (mkFEnv env) pf (projFnName T i) us' >>= fun pty =>
          iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d pty
              (targs ++ [b]) >>= fun r =>
          if r then
            structEtaProjCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
              TI T us' targs b lpsT rest
          else pure false
        else pure false
      | _ => pure false)
      (match env.find? (projFnName T i) with
      | some (.recInfo cvp _ _ _) =>
        if cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (xs.length + 1)).isSome = true then
          iotaCerts (fueledFns mode env) env d
              (cvp.type.instantiateLevelParams cvp.levelParams us')
              (xs ++ [xb]) >>= fun r =>
          if r then
            structEtaProjCerts (fueledFns mode env) env d T us' xs xb lpsT rest
          else pure false
        else pure false
      | _ => pure false)
    rw [mkFEnv_find?, htargs.length]
    cases hf : env.find? (projFnName T i) with
    | none => exact SimC.pure hs rfl
    | some ci =>
      cases ci with
      | recInfo cvp mI rP rules =>
        dsimp only
        split
        · refine SimC.bind_left (projFnIdxM_eff hs TI i)
            (fun s₀p pf hs hQpf => ?_)
          refine SimC.bind_left (constTyAtM_eff hs hf)
            (fun s₁ pty hs₁ hQty => ?_)
          have htyw : Expr.WScoped d
              (cvp.type.instantiateLevelParams cvp.levelParams us') := by
            obtain ⟨htf, -⟩ := henv _ (find?_mem hf)
            exact wscoped_instLevels_of_not_hasFvar htf _ _
          have hargs : ∀ x ∈ xs ++ [xb], Expr.WScoped d x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hwxs x hx
            · rcases List.mem_singleton.mp hx with rfl
              exact hwxb
          refine SimC.bind (iotaCertsC_sim ih hs₁ hQty htyw
            (htargs.append (RelCL.cons hb RelCL.nil)) hargs)
            (fun s₂ r r' hs₂ hPr => ?_)
          obtain rfl : r = r' := hPr
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCertsC_sim ih henv TI T us' lpsT rest hs₂
              htargs hb hwxs hwxb
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimC.pure hs₂ rfl
        · exact SimC.pure hs rfl
      | axiomInfo cv => exact SimC.pure hs rfl
      | defnInfo cv v h => exact SimC.pure hs rfl
      | thmInfo cv v => exact SimC.pure hs rfl
      | indInfo cv caps => exact SimC.pure hs rfl
      | ctorInfo cv nP nF => exact SimC.pure hs rfl
      | projInfo entry => exact SimC.pure hs rfl

/-- Prefix of a related list. -/
theorem RelCL.take {l : List ExprC} {xs : List Expr} (h : RelCL l xs)
    (k : Nat) : RelCL (l.take k) (xs.take k) :=
  ⟨fun x hx => h.1 x (List.mem_of_mem_take hx),
    by rw [← h.2, List.map_take]⟩

/-- Suffix of a related list. -/
theorem RelCL.drop {l : List ExprC} {xs : List Expr} (h : RelCL l xs)
    (k : Nat) : RelCL (l.drop k) (xs.drop k) :=
  ⟨fun x hx => h.1 x (List.mem_of_mem_drop hx),
    by rw [← h.2, List.map_drop]⟩

private theorem structEtaCertWithC_unfold (env : Env) (d : Nat)
    (a b wtb : Expr) :
    structEtaCertWith mode (fueledFns mode env) env d a b wtb =
    (match a.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.ctorInfo cvc cnP cnF) =>
        if a.getAppArgs.length = cnP + cnF then
          match wtb.getAppFn with
          | .const T us' =>
            match env.find? T with
            | some (.indInfo cvT caps) =>
              if caps.eta = true ∧ caps.etaCtor = c ∧
                  caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                  reservedBasisNames.contains T = false ∧
                  reservedBasisNames.contains c = false ∧
                  wtb.getAppArgs.length = cnP ∧
                  us'.length = cvT.levelParams.length ∧
                  cvc.levelParams = cvT.levelParams ∧
                  (cvT.type.stripPis cnP).isSome = true then
                liftFueled "level comparison"
                  (Level.isEquivList us us') >>= fun ok =>
                if ok then
                  iotaCerts (fueledFns mode env) env d
                      (cvT.type.instantiateLevelParams cvT.levelParams us')
                      wtb.getAppArgs >>= fun r₁ =>
                  if r₁ then
                    structEtaProjCerts (fueledFns mode env) env d T us'
                        wtb.getAppArgs b cvT.levelParams
                        (List.range cnF) >>= fun r₂ =>
                    if r₂ then
                      defEqList (fueledFns mode env) env d
                          (a.getAppArgs.take cnP) wtb.getAppArgs >>=
                        fun r₃ =>
                      if r₃ then
                        (if mode.ttChecks then
                            iotaCerts (fueledFns mode env) env d
                              (cvc.type.instantiateLevelParams
                                cvc.levelParams us)
                              (wtb.getAppArgs ++
                                (List.range cnF).map fun i =>
                                  Expr.mkAppN (.const (projFnName T i) us')
                                    (wtb.getAppArgs ++ [b]))
                          else pure true) >>= fun r₄ =>
                        if r₄ then
                          defEqList (fueledFns mode env) env d
                            (a.getAppArgs.drop cnP)
                            ((List.range cnF).map fun i =>
                              Expr.mkAppN (.const (projFnName T i) us')
                                (wtb.getAppArgs ++ [b]))
                        else pure false
                      else pure false
                    else pure false
                  else pure false
                else pure false
              else pure false
            | _ => pure false
          | _ => pure false
        else pure false
      | _ => pure false
    | _ => pure false) := rfl

/-- Port of `structEtaCertWithI_sim`. -/
theorem structEtaCertWithC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j w : ExprC} {a b wtb : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b) (hdenw : RelC w wtb)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (hwwtb : Expr.WScoped d wtb) :
    SimC mode env s₀ RelVC
      (structEtaCertWithI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        i j w)
      (structEtaCertWith mode (fueledFns mode env) env d a b wtb) := by
  show SimC mode env s₀ RelVC
    (Setlec.Cached.withStore (fun st => st.getNode (st.getAppFnI i)) >>=
      fun n =>
      match n with
      | some (.const c us) =>
        readbackNM c >>= fun cn =>
        match (mkFEnv env).find? cn with
        | some (.ctorInfo cvc cnP cnF) =>
          Setlec.Cached.withStore (·.getAppArgsI i) >>= fun aargs =>
          if aargs.length = cnP + cnF then
            Setlec.Cached.withStore (fun st => st.getNode (st.getAppFnI w)) >>=
              fun n' =>
            match n' with
            | some (.const T us') =>
              readbackNM T >>= fun Tn =>
              match (mkFEnv env).find? Tn with
              | some (.indInfo cvT caps) =>
                Setlec.Cached.withStore (·.getAppArgsI w) >>= fun targs =>
                if caps.eta = true ∧ caps.etaCtor = cn ∧
                    caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                    reservedBasisNames.contains Tn = false ∧
                    reservedBasisNames.contains cn = false ∧
                    targs.length = cnP ∧
                    us'.length = cvT.levelParams.length ∧
                    cvc.levelParams = cvT.levelParams ∧
                    (cvT.type.stripPis cnP).isSome = true then
                  isEquivListLM us us' >>= fun o =>
                  liftFueled "level comparison" o >>= fun ok =>
                  if ok then
                    constTyAtM (mkFEnv env) T Tn us' >>= fun tyT =>
                    iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
                        tyT targs >>= fun r₁ =>
                    if r₁ then
                      structEtaProjCertsI (coreKnotI mode (mkFEnv env) f)
                          (mkFEnv env) d T Tn us' targs j cvT.levelParams
                          (List.range cnF) >>= fun r₂ =>
                      if r₂ then
                        defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
                            d (aargs.take cnP) targs >>= fun r₃ =>
                        if r₃ then
                          projAppsI T us' targs j (List.range cnF) >>=
                            fun projs =>
                          (if mode.ttChecks then
                              constTyAtM (mkFEnv env) c cn us >>= fun tyCtor =>
                              iotaCertsI (coreKnotI mode (mkFEnv env) f)
                                (mkFEnv env) d tyCtor (targs ++ projs)
                            else pure true) >>= fun r₄ =>
                          if r₄ then
                            defEqListI (coreKnotI mode (mkFEnv env) f)
                              (mkFEnv env) d (aargs.drop cnP) projs
                          else pure false
                        else pure false
                      else pure false
                    else pure false
                  else pure false
                else pure false
              | _ => pure false
            | _ => pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    (structEtaCertWith mode (fueledFns mode env) env d a b wtb)
  obtain ⟨hwca, rfl⟩ := hdena
  obtain ⟨hwcb, rfl⟩ := hdenb
  obtain ⟨hwcw, rfl⟩ := hdenw
  have hdenb : RelC j (eraseC j) := ⟨hwcb, rfl⟩
  rw [structEtaCertWithC_unfold]
  refine SimC.withStore ?_
  have haargs : RelCL (ExprC.getAppArgs i) (eraseC i).getAppArgs :=
    ExprC.getAppArgs_spec hwca
  have hlena : (ExprC.getAppArgs i).length
      = (eraseC i).getAppArgs.length := RelCL.length haargs
  have htargs : RelCL (ExprC.getAppArgs w) (eraseC w).getAppArgs :=
    ExprC.getAppArgs_spec hwcw
  have hlenw : (ExprC.getAppArgs w).length
      = (eraseC w).getAppArgs.length := RelCL.length htargs
  obtain ⟨hwfa, hfa⟩ := ExprC.getAppFn_spec hwca
  obtain ⟨hwfw, hfw⟩ := ExprC.getAppFn_spec hwcw
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hga : ExprC.getAppFn i = ga at hwfa hfa ⊢
  cases ga with
  | const c us hh bb fb lp =>
    rw [show (eraseC i).getAppFn = Expr.const c us from hfa.symm]
    dsimp only
    refine SimC.bind_left (readbackNM_eff hs c) (fun s₀c cw hs hcw => ?_)
    subst cw
    rw [mkFEnv_find?]
    cases hfc : env.find? c with
    | none => exact SimC.pure hs rfl
    | some ci =>
      cases ci with
      | ctorInfo cvc cnP cnF =>
        dsimp only
        refine SimC.withStore ?_
        simp only [CStore.getAppArgsI, hlena]
        split
        · refine SimC.withStore ?_
          generalize hgw : ExprC.getAppFn w = gw at hwfw hfw ⊢
          cases gw with
          | const T us' hh' bb' fb' lp' =>
            rw [show (eraseC w).getAppFn = Expr.const T us' from hfw.symm]
            dsimp only
            refine SimC.bind_left (readbackNM_eff hs T)
              (fun s₀T Tw hs hTw => ?_)
            subst Tw
            rw [mkFEnv_find?]
            cases hfT : env.find? T with
            | none => exact SimC.pure hs rfl
            | some ciT =>
              cases ciT with
              | indInfo cvT caps =>
                dsimp only
                refine SimC.withStore ?_
                simp only [hlenw]
                split
                · refine SimC.bind_left (isEquivListLM_eff hs)
                    (fun s₀o o hs₀o ho => ?_)
                  subst ho
                  refine SimC.bind (SimC.liftFueled _ _ hs₀o)
                    (fun s₁ ok ok' hs₁ hPok => ?_)
                  obtain rfl : ok = ok' := hPok
                  cases ok with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact SimC.pure hs₁ rfl
                  | true =>
                    simp only [↓reduceIte]
                    refine SimC.bind_left (constTyAtM_eff hs₁ hfT)
                      (fun s₂ tyT hs₂ hQty => ?_)
                    have htyw : Expr.WScoped d
                        (cvT.type.instantiateLevelParams
                          cvT.levelParams us') := by
                      obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
                      exact wscoped_instLevels_of_not_hasFvar htf _ _
                    refine SimC.bind (iotaCertsC_sim ih hs₂ hQty htyw
                      htargs hwwtb.getAppArgs)
                      (fun s₃ r₁ r₁' hs₃ hPr₁ => ?_)
                    obtain rfl : r₁ = r₁' := hPr₁
                    cases r₁ with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact SimC.pure hs₃ rfl
                    | true =>
                      simp only [↓reduceIte]
                      refine SimC.bind (structEtaProjCertsC_sim ih henv
                        T T us' cvT.levelParams (List.range cnF) hs₃
                        htargs hdenb hwwtb.getAppArgs hwb)
                        (fun s₄ r₂ r₂' hs₄ hPr₂ => ?_)
                      obtain rfl : r₂ = r₂' := hPr₂
                      cases r₂ with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact SimC.pure hs₄ rfl
                      | true =>
                        simp only [↓reduceIte]
                        refine SimC.bind (defEqListC_sim ih hs₄
                          (haargs.take cnP) htargs
                          (fun x hx => hwa.getAppArgs x
                            (List.mem_of_mem_take hx))
                          hwwtb.getAppArgs)
                          (fun s₅ r₃ r₃' hs₅ hPr₃ => ?_)
                        obtain rfl : r₃ = r₃' := hPr₃
                        cases r₃ with
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimC.pure hs₅ rfl
                        | true =>
                          simp only [↓reduceIte]
                          refine SimC.bind_left (projAppsC_eff T us'
                            (List.range cnF) hs₅ htargs hdenb)
                            (fun s₆ projs hs₆ hQp => ?_)
                          have hwprojs : ∀ x ∈ (List.range cnF).map
                              (fun i' => Expr.mkAppN
                                (.const (projFnName T i') us')
                                ((eraseC w).getAppArgs ++ [eraseC j])),
                              Expr.WScoped d x := by
                            intro x hx
                            obtain ⟨i', -, rfl⟩ := List.mem_map.mp hx
                            refine Expr.WScoped.mkAppN
                              (by simp [Expr.WScoped]) ?_
                            intro y hy
                            rcases List.mem_append.mp hy with hy | hy
                            · exact hwwtb.getAppArgs y hy
                            · rcases List.mem_singleton.mp hy with rfl
                              exact hwb
                          refine SimC.bind (P := RelVC) ?_
                            (fun s₈ r₄ r₄' hs₈ hPr₄ => ?_)
                          · cases htt : mode.ttChecks with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₆ rfl
                            | true =>
                              simp only [↓reduceIte]
                              refine SimC.bind_left (constTyAtM_eff hs₆ hfc)
                                (fun s₇ tyCtor hs₇ hQtyc => ?_)
                              have htycw : Expr.WScoped d
                                  (cvc.type.instantiateLevelParams
                                    cvc.levelParams us) := by
                                obtain ⟨htf, -⟩ := henv _ (find?_mem hfc)
                                exact wscoped_instLevels_of_not_hasFvar
                                  htf _ _
                              exact iotaCertsC_sim ih hs₇ hQtyc htycw
                                (htargs.append hQp)
                                (fun x hx => by
                                  rcases List.mem_append.mp hx with hx | hx
                                  · exact hwwtb.getAppArgs x hx
                                  · exact hwprojs x hx)
                          obtain rfl : r₄ = r₄' := hPr₄
                          cases r₄ with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₈ rfl
                          | true =>
                            simp only [↓reduceIte]
                            exact defEqListC_sim ih hs₈ (haargs.drop cnP) hQp
                              (fun x hx => hwa.getAppArgs x
                                (List.mem_of_mem_drop hx)) hwprojs
                · exact SimC.pure hs rfl
              | axiomInfo cv => exact SimC.pure hs rfl
              | defnInfo cv v h => exact SimC.pure hs rfl
              | thmInfo cv v => exact SimC.pure hs rfl
              | ctorInfo cv nP' nF' => exact SimC.pure hs rfl
              | recInfo cv mI rP rules => exact SimC.pure hs rfl
              | projInfo entry => exact SimC.pure hs rfl
          | bvar k hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn = Expr.bvar k from hfw.symm]
            exact SimC.pure hs rfl
          | sort u hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn = Expr.sort u from hfw.symm]
            exact SimC.pure hs rfl
          | lit l hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn = Expr.lit l from hfw.symm]
            exact SimC.pure hs rfl
          | fvar ix nm t hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn = Expr.fvar ix nm (eraseC t)
              from hfw.symm]
            exact SimC.pure hs rfl
          | app f' a' hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn = Expr.app (eraseC f') (eraseC a')
              from hfw.symm]
            exact SimC.pure hs rfl
          | lam nm t b' m hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn
              = Expr.lam nm (eraseC t) (eraseC b') m from hfw.symm]
            exact SimC.pure hs rfl
          | forallE nm t b' m hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn
              = Expr.forallE nm (eraseC t) (eraseC b') m from hfw.symm]
            exact SimC.pure hs rfl
          | letE nm t v b' hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn
              = Expr.letE nm (eraseC t) (eraseC v) (eraseC b')
              from hfw.symm]
            exact SimC.pure hs rfl
          | proj sn jx e' hk bbk fbk lpk =>
            rw [show (eraseC w).getAppFn = Expr.proj sn jx (eraseC e')
              from hfw.symm]
            exact SimC.pure hs rfl
        · exact SimC.pure hs rfl
      | axiomInfo cv => exact SimC.pure hs rfl
      | defnInfo cv v h => exact SimC.pure hs rfl
      | thmInfo cv v => exact SimC.pure hs rfl
      | indInfo cv caps => exact SimC.pure hs rfl
      | recInfo cv mI rP rules => exact SimC.pure hs rfl
      | projInfo entry => exact SimC.pure hs rfl
  | bvar k hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.bvar k from hfa.symm]
    exact SimC.pure hs rfl
  | sort u hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.sort u from hfa.symm]
    exact SimC.pure hs rfl
  | lit l hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.lit l from hfa.symm]
    exact SimC.pure hs rfl
  | fvar ix nm t hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.fvar ix nm (eraseC t) from hfa.symm]
    exact SimC.pure hs rfl
  | app f' a' hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.app (eraseC f') (eraseC a')
      from hfa.symm]
    exact SimC.pure hs rfl
  | lam nm t b' m hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.lam nm (eraseC t) (eraseC b') m
      from hfa.symm]
    exact SimC.pure hs rfl
  | forallE nm t b' m hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.forallE nm (eraseC t) (eraseC b') m
      from hfa.symm]
    exact SimC.pure hs rfl
  | letE nm t v b' hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn
      = Expr.letE nm (eraseC t) (eraseC v) (eraseC b') from hfa.symm]
    exact SimC.pure hs rfl
  | proj sn jx e' hk bbk fbk lpk =>
    rw [show (eraseC i).getAppFn = Expr.proj sn jx (eraseC e') from hfa.symm]
    exact SimC.pure hs rfl

/-- Port of `structEtaCertI_sim`. -/
theorem structEtaCertC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (structEtaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (structEtaCert mode (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).infer d j >>= fun tb =>
      (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
      structEtaCertWithI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        i j wtb)
    ((fueledFns mode env).infer d b >>= fun tb =>
      (fueledFns mode env).whnf d tb >>= fun wtb =>
      structEtaCertWith mode (fueledFns mode env) env d a b wtb)
  refine SimC.bind (ih.infer hs hdenb hwb) (fun s₁ tb tbx hs₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htbd hwtb) (fun s₂ wtb wtbx hs₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  exact structEtaCertWithC_sim ih henv hs₂ hdena hdenb hwtbd hwa hwb hwwtb

/-- Port of `stuckIrrelI_sim`. -/
theorem stuckIrrelC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (stuckIrrelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (stuckIrrel mode (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (pairEtaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
      fun r₁ =>
      if r₁ then pure true else
      pairEtaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d j i >>=
        fun r₂ =>
      if r₂ then pure true else
      structEtaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₃ =>
      if r₃ then pure true else
      structEtaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d j i >>=
        fun r₄ =>
      if r₄ then pure true else
      structUnitCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₅ =>
      if r₅ then pure true else
      proofIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
    (pairEtaCert mode (fueledFns mode env) env d a b >>= fun r₁ =>
      if r₁ then pure true else
      pairEtaCert mode (fueledFns mode env) env d b a >>= fun r₂ =>
      if r₂ then pure true else
      structEtaCert mode (fueledFns mode env) env d a b >>= fun r₃ =>
      if r₃ then pure true else
      structEtaCert mode (fueledFns mode env) env d b a >>= fun r₄ =>
      if r₄ then pure true else
      structUnitCert (fueledFns mode env) env d a b >>= fun r₅ =>
      if r₅ then pure true else
      proofIrrel (fueledFns mode env) env d a b)
  refine SimC.bind (pairEtaCertC_sim ih henv hs hdena hdenb hwa hwb)
    (fun s₁ r₁ r₁' hs₁ hP₁ => ?_)
  obtain rfl : r₁ = r₁' := hP₁
  cases r₁ with
  | true => simp only [↓reduceIte]; exact SimC.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimC.bind (pairEtaCertC_sim ih henv hs₁ hdenb hdena hwb hwa)
      (fun s₂ r₂ r₂' hs₂ hP₂ => ?_)
    obtain rfl : r₂ = r₂' := hP₂
    cases r₂ with
    | true => simp only [↓reduceIte]; exact SimC.pure hs₂ rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine SimC.bind (structEtaCertC_sim ih henv hs₂ hdena hdenb hwa hwb)
        (fun s₃ r₃ r₃' hs₃ hP₃ => ?_)
      obtain rfl : r₃ = r₃' := hP₃
      cases r₃ with
      | true => simp only [↓reduceIte]; exact SimC.pure hs₃ rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SimC.bind (structEtaCertC_sim ih henv hs₃ hdenb hdena hwb hwa)
          (fun s₄ r₄ r₄' hs₄ hP₄ => ?_)
        obtain rfl : r₄ = r₄' := hP₄
        cases r₄ with
        | true => simp only [↓reduceIte]; exact SimC.pure hs₄ rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine SimC.bind (structUnitCertC_sim ih henv hs₄ hdena hdenb
            hwa hwb) (fun s₅ r₅ r₅' hs₅ hP₅ => ?_)
          obtain rfl : r₅ = r₅' := hP₅
          cases r₅ with
          | true => simp only [↓reduceIte]; exact SimC.pure hs₅ rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact proofIrrelC_sim ih hs₅ hdena hdenb hwa hwb

end Walks4

end Setlec.Cached
