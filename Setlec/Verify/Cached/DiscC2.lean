import Setlec.Verify.Cached.DiscC1

/-!
# Cached body walks, part 2: the stuck-term certificates (task #163)

The port of `Setlec/Verify/DiscI2.lean` under the recipe (DESIGN.md,
task #163): `SimAt → SimC`, denotation hypotheses → `RelC`/`RelCL`, no
`Ext`, node inversion by `cases` on the `ExprC`
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
    (hw : Expr.WScoped d ((Expr.app fn arg))) :
    Expr.WScoped d fn ∧ Expr.WScoped d arg := by
  have hw' : Expr.WScoped d (.app fn arg) := hw
  simpa only [Expr.WScoped] using hw'

section Walks

variable {env : Env} {f : Nat}

/-- The hoisted `Prop`-branch test (task #168): the fast arm is the
same pure read on both sides (`mkFEnv_find?_fun`); the slow branch is
`proofIrrelC_sim`'s `Prop` branch. -/
theorem propIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : ExprC}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (propIrrelI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
        d i j)
      (propIrrel mode (fueledFns mode env) env d a b) := by
  obtain rfl : a = i := hdena.symm
  obtain rfl : b = j := hdenb.symm
  show SimC mode env s₀ RelVC
    (if mode.verified &&
        (notProofFast (mkFEnv env).find? a || notProofFast (mkFEnv env).find? b)
      then pure false
      else if mode.verified && mode.betaGate &&
        isProofFast (mkFEnv env).find? a && isProofFast (mkFEnv env).find? b
      then pure true else
      (coreKnotI mode (mkFEnv env) f).inferIO d a >>= fun ta =>
      (coreKnotI mode (mkFEnv env) f).inferIO d ta >>= fun tta =>
      (coreKnotI mode (mkFEnv env) f).whnf d tta >>= fun wtta =>
      viewI wtta >>= fun n =>
      match n with
      | some (.sort uT) =>
        internLM .zero >>= fun zA =>
        isEquivLM uT zA >>= fun oA =>
        liftFueled "level comparison" oA >>= fun okA =>
        (coreKnotI mode (mkFEnv env) f).inferIO d b >>= fun tb =>
        (coreKnotI mode (mkFEnv env) f).inferIO d tb >>= fun ttb =>
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
    (propIrrel mode (fueledFns mode env) env d a b)
  rw [show (mkFEnv env).find? = env.find? from funext (mkFEnv_find? env)]
  unfold propIrrel
  by_cases hc : (mode.verified &&
      (notProofFast env.find? a || notProofFast env.find? b)) = true
  · rw [if_pos hc, if_pos hc]
    exact SimC.pure hs rfl
  · rw [if_neg hc, if_neg hc]
    by_cases hy : (mode.verified && mode.betaGate &&
        isProofFast env.find? a && isProofFast env.find? b) = true
    · rw [if_pos hy, if_pos hy]
      exact SimC.pure hs rfl
    rw [if_neg hy, if_neg hy]
    refine SimC.bind (ih.inferIO hs rfl hwa) (fun s₁ ta tax hs₁ hP => ?_)
    obtain ⟨htad, hwta⟩ := hP
    refine SimC.bind (ih.inferIO hs₁ htad hwta) (fun s₃ tta ttax hs₃ hP₃ => ?_)
    obtain ⟨httad, hwtta⟩ := hP₃
    refine SimC.bind (ih.whnf hs₃ httad hwtta) (fun s₄ wtta wttax hs₄ hP₄ => ?_)
    obtain ⟨hwttad, hwwtta⟩ := hP₄
    refine SimC.view ?_
    obtain rfl := hwttad
    cases wtta with
    | sort uT =>
      refine SimC.bind_left (internLM_eff hs₄ .zero)
        (fun s₄z zA hs₄z hzA => ?_)
      subst hzA
      refine SimC.bind_left (isEquivLM_eff hs₄z uT .zero)
        (fun s₄o oA hs₄o hoA => ?_)
      subst hoA
      refine SimC.bind (SimC.liftFueled _ _ hs₄o)
        (fun s₅ okA okA' hs₅ hPok => ?_)
      obtain rfl : okA = okA' := hPok
      refine SimC.bind (ih.inferIO hs₅ rfl hwb) (fun s₆ tb tbx hs₆ hP₆ => ?_)
      obtain ⟨htbd, hwtb⟩ := hP₆
      refine SimC.bind (ih.inferIO hs₆ htbd hwtb) (fun s₇ ttb ttbx hs₇ hP₇ => ?_)
      obtain ⟨httbd, hwttb⟩ := hP₇
      refine SimC.bind (ih.whnf hs₇ httbd hwttb)
        (fun s₈ wttb wttbx hs₈ hP₈ => ?_)
      obtain ⟨hwttbd, hwwttb⟩ := hP₈
      refine SimC.view ?_
      obtain ⟨hwc', rfl⟩ := hwttbd
      cases wttb with
      | sort vT =>
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
      | bvar k => exact SimC.pure hs₈ rfl
      | const nm us => exact SimC.pure hs₈ rfl
      | lit l => exact SimC.pure hs₈ rfl
      | fvar idx nm t => exact SimC.pure hs₈ rfl
      | app f' a' => exact SimC.pure hs₈ rfl
      | lam nm t b' m => exact SimC.pure hs₈ rfl
      | forallE nm t b' m => exact SimC.pure hs₈ rfl
      | letE nm t v b' => exact SimC.pure hs₈ rfl
      | proj s i e => exact SimC.pure hs₈ rfl
    | bvar k => exact SimC.pure hs₄ rfl
    | const nm us => exact SimC.pure hs₄ rfl
    | lit l => exact SimC.pure hs₄ rfl
    | fvar idx nm t => exact SimC.pure hs₄ rfl
    | app f' a' => exact SimC.pure hs₄ rfl
    | lam nm t b' m => exact SimC.pure hs₄ rfl
    | forallE nm t b' m => exact SimC.pure hs₄ rfl
    | letE nm t v b' => exact SimC.pure hs₄ rfl
    | proj s i e => exact SimC.pure hs₄ rfl

/-- Port of `proofIrrelI_sim`. -/
theorem proofIrrelC_sim (ih : SSimC mode env f) {d : Nat} {i j : ExprC}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (proofIrrelI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (proofIrrel (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).inferIO d i >>= fun ta =>
      (coreKnotI mode (mkFEnv env) f).whnf d ta >>= fun wta =>
      Setlec.Cached.withStore (fun st => isUnitLikeTyI (mkFEnv env) st wta) >>=
        fun c₁ =>
      if c₁ then
        (coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
        (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
        Setlec.Cached.withStore (fun st => isUnitLikeTyI (mkFEnv env) st wtb) >>=
          fun c₂ =>
        if c₂ then pure true else pure false
      else
        (coreKnotI mode (mkFEnv env) f).inferIO d ta >>= fun tta =>
        (coreKnotI mode (mkFEnv env) f).whnf d tta >>= fun wtta =>
        viewI wtta >>= fun n =>
        match n with
        | some (.sort uT) =>
          internLM .zero >>= fun zA =>
          isEquivLM uT zA >>= fun oA =>
          liftFueled "level comparison" oA >>= fun okA =>
          (coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
          (coreKnotI mode (mkFEnv env) f).inferIO d tb >>= fun ttb =>
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
  refine SimC.bind (ih.inferIO hs hdena hwa) (fun s₁ ta tax hs₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htad hwta) (fun s₂ wta wtax hs₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimC.withStore ?_
  rw [isUnitLikeTyI_spec hwtad]
  by_cases hu : isUnitLikeTy env wtax
  · rw [if_pos hu, if_pos hu]
    refine SimC.bind (ih.inferIO hs₂ hdenb hwb) (fun s₃ tb tbx hs₃ hP₃ => ?_)
    obtain ⟨htbd, hwtb⟩ := hP₃
    refine SimC.bind (ih.whnf hs₃ htbd hwtb) (fun s₄ wtb wtbx hs₄ hP₄ => ?_)
    obtain ⟨hwtbd, hwwtb⟩ := hP₄
    refine SimC.withStore ?_
    rw [isUnitLikeTyI_spec hwtbd]
    by_cases hu₂ : isUnitLikeTy env wtbx
    · rw [if_pos hu₂, if_pos hu₂]
      exact SimC.pure hs₄ rfl
    · rw [if_neg hu₂, if_neg hu₂]
      exact SimC.pure hs₄ rfl
  · rw [if_neg hu, if_neg hu]
    refine SimC.bind (ih.inferIO hs₂ htad hwta) (fun s₃ tta ttax hs₃ hP₃ => ?_)
    obtain ⟨httad, hwtta⟩ := hP₃
    refine SimC.bind (ih.whnf hs₃ httad hwtta) (fun s₄ wtta wttax hs₄ hP₄ => ?_)
    obtain ⟨hwttad, hwwtta⟩ := hP₄
    refine SimC.view ?_
    obtain rfl := hwttad
    cases wtta with
    | sort uT =>
      refine SimC.bind_left (internLM_eff hs₄ .zero)
        (fun s₄z zA hs₄z hzA => ?_)
      subst hzA
      refine SimC.bind_left (isEquivLM_eff hs₄z uT .zero)
        (fun s₄o oA hs₄o hoA => ?_)
      subst hoA
      refine SimC.bind (SimC.liftFueled _ _ hs₄o)
        (fun s₅ okA okA' hs₅ hPok => ?_)
      obtain rfl : okA = okA' := hPok
      refine SimC.bind (ih.inferIO hs₅ hdenb hwb) (fun s₆ tb tbx hs₆ hP₆ => ?_)
      obtain ⟨htbd, hwtb⟩ := hP₆
      refine SimC.bind (ih.inferIO hs₆ htbd hwtb) (fun s₇ ttb ttbx hs₇ hP₇ => ?_)
      obtain ⟨httbd, hwttb⟩ := hP₇
      refine SimC.bind (ih.whnf hs₇ httbd hwttb)
        (fun s₈ wttb wttbx hs₈ hP₈ => ?_)
      obtain ⟨hwttbd, hwwttb⟩ := hP₈
      refine SimC.view ?_
      obtain ⟨hwc', rfl⟩ := hwttbd
      cases wttb with
      | sort vT =>
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
      | bvar k => exact SimC.pure hs₈ rfl
      | const nm us => exact SimC.pure hs₈ rfl
      | lit l => exact SimC.pure hs₈ rfl
      | fvar idx nm t => exact SimC.pure hs₈ rfl
      | app f' a' => exact SimC.pure hs₈ rfl
      | lam nm t b' m => exact SimC.pure hs₈ rfl
      | forallE nm t b' m => exact SimC.pure hs₈ rfl
      | letE nm t v b' => exact SimC.pure hs₈ rfl
      | proj sn j' e' => exact SimC.pure hs₈ rfl
    | bvar k => exact SimC.pure hs₄ rfl
    | const nm us => exact SimC.pure hs₄ rfl
    | lit l => exact SimC.pure hs₄ rfl
    | fvar idx nm t => exact SimC.pure hs₄ rfl
    | app f' a' => exact SimC.pure hs₄ rfl
    | lam nm t b' m => exact SimC.pure hs₄ rfl
    | forallE nm t b' m => exact SimC.pure hs₄ rfl
    | letE nm t v b' => exact SimC.pure hs₄ rfl
    | proj sn j' e' => exact SimC.pure hs₄ rfl

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
      (etaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        n₁ ty₁ body₁ m₁ b)
      (etaCert mode (fueledFns mode env) env d n₁ ty₁x body₁x m₁ bx) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).inferIO d b >>= fun tb =>
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
    ((fueledFns mode env).inferIO d bx >>= fun tb =>
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
  obtain rfl := hty
  obtain rfl := hbody
  obtain rfl := hb
  have hty : RelC ty₁ (ty₁) := rfl
  have hbody : RelC body₁ (body₁) := rfl
  have hb : RelC b b := rfl
  refine SimC.bind (ih.inferIO hs hb hwb) (fun s₁ tb tbx hs₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htbd hwtb) (fun s₂ wtb wtbx hs₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  refine SimC.view ?_
  obtain rfl := hwtbd
  cases wtb with
  | forallE nm ty₂ b₂ m₂ =>
    have hwty₂x : Expr.WScoped d (ty₂) := by
      rw [show (Expr.forallE nm ty₂ b₂ m₂)
          = Expr.forallE nm (ty₂) (b₂) m₂ from rfl] at hwwtb
      simp only [Expr.WScoped] at hwwtb
      exact hwwtb.1
    refine SimC.bind (ih.defeq hs₂ rfl hty hwty₂x hwty)
      (fun s₄ r r' hs₄ hPr => ?_)
    obtain rfl : r = r' := hPr
    cases r with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₄ rfl
    | true =>
      simp only [↓reduceIte]
      refine SimC.bind_left
        (internI_eff hs₄ (n := ExprView.fvar d n₁ ty₁))
        (fun s₅ fv hs₅ hQfv => ?_)
      have hQfv' : RelC fv (.fvar d n₁ (ty₁)) := hQfv
      refine SimC.bind_left (inst1M_eff hs₅ hbody hQfv')
        (fun s₆ b₁ hs₆ hQb₁ => ?_)
      refine SimC.bind_left
        (internI_eff hs₆ (n := ExprView.app b fv))
        (fun s₇ ba hs₇ hQba => ?_)
      have hQba' : RelC ba (.app b (.fvar d n₁ (ty₁))) := by
        show _ = _
        rw [show ba = .app b fv from hQba,
          hQfv']
      have hwapp : Expr.WScoped (d + 1)
          (.app b (.fvar d n₁ (ty₁))) := by
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
  | bvar k => exact SimC.pure hs₂ rfl
  | sort u => exact SimC.pure hs₂ rfl
  | const nm us => exact SimC.pure hs₂ rfl
  | lit l => exact SimC.pure hs₂ rfl
  | fvar idx nm t => exact SimC.pure hs₂ rfl
  | app f' a' => exact SimC.pure hs₂ rfl
  | lam nm t b' m => exact SimC.pure hs₂ rfl
  | letE nm t v b' => exact SimC.pure hs₂ rfl
  | proj sn j' e' => exact SimC.pure hs₂ rfl

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
    {e₂ : Expr} {idx : Nat} {nP : Nat}
    {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e₂) (hw : Expr.WScoped d e₂) :
    SimC mode env s₀ RelVC
      (projCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i idx nP)
      (projCert (fueledFns mode env) env d e₂ idx nP) := by
  show SimC mode env s₀ RelVC
    (internI (.bvar 0) >>= fun bvar0 =>
      Setlec.Cached.withStore (·.getAppArgsI i) >>= fun args =>
      (coreKnotI mode (mkFEnv env) f).inferIO d (args.getD (nP + idx) bvar0) >>=
        fun _ta =>
      (coreKnotI mode (mkFEnv env) f).inferIO d i >>= fun _te =>
      pure true)
    (projCert (fueledFns mode env) env d e₂ idx nP)
  refine SimC.bind_left (internI_eff hs (n := ExprView.bvar 0))
    (fun s₁ bvar0 hs₁ hQ0 => ?_)
  refine SimC.withStore ?_
  obtain rfl := hden
  have hargs := ExprC.getAppArgs_spec i
  have hargd : RelC ((ExprC.getAppArgs i).getD (nP + idx) bvar0)
      ((Expr.getAppArgs i).getD (nP + idx) (.bvar 0)) :=
    RelCL.getD hQ0 (nP + idx) hargs
  have hwarg : Expr.WScoped d
      ((Expr.getAppArgs i).getD (nP + idx) (.bvar 0)) :=
    wscoped_getD hw.getAppArgs _
  refine SimC.bind (ih.inferIO hs₁ hargd hwarg)
    (fun s₂ ta tax hs₂ hP₂ => ?_)
  refine SimC.bind (ih.inferIO hs₂ rfl hw)
    (fun s₃ te tex hs₃ hP₃ => ?_)
  exact SimC.pure hs₃ rfl

/-- Port of `structUnitCertI_sim`. -/
theorem structUnitCertC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (structUnitCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (structUnitCert (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).inferIO d i >>= fun ta =>
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
            (coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
            (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
            (coreKnotI mode (mkFEnv env) f).defeq d wta wtb >>= fun r =>
            if r then
              constTyAtM (mkFEnv env) T Tn us' >>= fun tyT =>
              iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d false
                tyT targs
            else pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    ((fueledFns mode env).inferIO d a >>= fun ta =>
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
            (fueledFns mode env).inferIO d b >>= fun tb =>
            (fueledFns mode env).whnf d tb >>= fun wtb =>
            (fueledFns mode env).defeq d wta wtb >>= fun r =>
            if r then
              iotaCerts (fueledFns mode env) env d false
                (cvT.type.instantiateLevelParams cvT.levelParams us')
                wta.getAppArgs
            else pure false
          else pure false
        | _ => pure false
      | _ => pure false)
  refine SimC.bind (ih.inferIO hs hdena hwa) (fun s₁ ta tax hs₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimC.bind (ih.whnf hs₁ htad hwta) (fun s₂ wta wtax hs₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimC.withStore ?_
  obtain rfl := hwtad
  have hargs := ExprC.getAppArgs_spec wta
  have hlena : (ExprC.getAppArgs wta).length
      = (Expr.getAppArgs wta).length := RelCL.length hargs
  have hfn := ExprC.getAppFn_spec wta
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hg : ExprC.getAppFn wta = g at hfn ⊢
  cases g with
  | const T us' =>
    rw [show (Expr.getAppFn wta) = Expr.const T us' from hfn.symm]
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
        · refine SimC.bind (ih.inferIO hs₂ hdenb hwb)
            (fun s₃ tb tbx hs₃ hP₃ => ?_)
          obtain ⟨htbd, hwtb⟩ := hP₃
          refine SimC.bind (ih.whnf hs₃ htbd hwtb)
            (fun s₄ wtb wtbx hs₄ hP₄ => ?_)
          obtain ⟨hwtbd, hwwtb⟩ := hP₄
          refine SimC.bind (ih.defeq hs₄ rfl hwtbd hwwta hwwtb)
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
  | bvar k =>
    rw [show (Expr.getAppFn wta) = Expr.bvar k from hfn.symm]
    exact SimC.pure hs₂ rfl
  | sort u =>
    rw [show (Expr.getAppFn wta) = Expr.sort u from hfn.symm]
    exact SimC.pure hs₂ rfl
  | lit l =>
    rw [show (Expr.getAppFn wta) = Expr.lit l from hfn.symm]
    exact SimC.pure hs₂ rfl
  | fvar idx nm t =>
    rw [show (Expr.getAppFn wta) = Expr.fvar idx nm t
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | app f' a' =>
    rw [show (Expr.getAppFn wta) = Expr.app f' a'
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | lam nm t b' m =>
    rw [show (Expr.getAppFn wta) = Expr.lam nm t b' m
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | forallE nm t b' m =>
    rw [show (Expr.getAppFn wta) = Expr.forallE nm t b' m
      from hfn.symm]
    exact SimC.pure hs₂ rfl
  | letE nm t v b' =>
    rw [show (Expr.getAppFn wta)
      = Expr.letE nm t v b' from hfn.symm]
    exact SimC.pure hs₂ rfl
  | proj sn j' e' =>
    rw [show (Expr.getAppFn wta) = Expr.proj sn j' e'
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
        (fueledFns mode env).inferIO d b >>= fun tb =>
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
theorem pairEtaCertC_sim (ih : SSimC mode env f)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (pairEtaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
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
                  (coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
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
  obtain rfl := hdena
  obtain rfl := hdenb
  have hdenb : RelC j j := rfl
  rw [pairEtaCertC_unfold]
  refine SimC.view ?_
  cases i with
  | app f₄ s₂ =>
    obtain ⟨hwf₄, hws₂w⟩ := wscoped_appC_inv hwa
    refine SimC.view ?_
    cases f₄ with
    | app f₃ s₁ =>
      obtain ⟨hwf₃, hws₁w⟩ := wscoped_appC_inv hwf₄
      refine SimC.view ?_
      cases f₃ with
      | app f₂ pβ =>
        obtain ⟨hwf₂, hwpβ⟩ := wscoped_appC_inv hwf₃
        refine SimC.view ?_
        cases f₂ with
        | app f₁ pα =>
          obtain ⟨hwf₁, hwpα⟩ := wscoped_appC_inv hwf₂
          refine SimC.view ?_
          cases f₁ with
          | const c us =>
            dsimp only
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
                  refine SimC.bind (ih.inferIO hs hdenb hwb)
                    (fun s₁' tb tbx hs₁' hP => ?_)
                  obtain ⟨htbd, hwtb⟩ := hP
                  refine SimC.bind (ih.whnf hs₁' htbd hwtb)
                    (fun s₂' wtb wtbx hs₂' hP₂ => ?_)
                  obtain ⟨hwtbd, hwwtb⟩ := hP₂
                  refine SimC.view ?_
                  obtain rfl := hwtbd
                  cases wtb with
                  | app g₂ B =>
                    obtain ⟨hwg₂, hwB⟩ := wscoped_appC_inv hwwtb
                    refine SimC.view ?_
                    cases g₂ with
                    | app g₁ A =>
                      obtain ⟨hwg₁, hwA⟩ := wscoped_appC_inv hwg₂
                      refine SimC.view ?_
                      cases g₁ with
                      | const c' us' =>
                        dsimp only
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
                                        rfl rfl hwpα hwA)
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
                                          rfl rfl hwpβ hwB)
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
                                              (n := ExprView.proj c' 0 j))
                                            (fun s₄' p₀ hs₄' hQ₀ => ?_)
                                          have hQ₀' :
                                              RelC p₀ (.proj c' 0 j) :=
                                            hQ₀
                                          have hwp₀ : Expr.WScoped d
                                              (.proj c' 0 j) := by
                                            simp only [Expr.WScoped]
                                            exact hwb
                                          refine SimC.bind (ih.defeq hs₄'
                                            rfl hQ₀' hws₁w hwp₀)
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
                                                (n := ExprView.proj c' 1 j))
                                              (fun s₆' p₁ hs₆' hQ₁ => ?_)
                                            have hQ₁' : RelC p₁
                                                (.proj c' 1 j) := hQ₁
                                            have hwp₁ : Expr.WScoped d
                                                (.proj c' 1 j) := by
                                              simp only [Expr.WScoped]
                                              exact hwb
                                            refine SimC.bind (ih.defeq hs₆'
                                              rfl hQ₁' hws₂w hwp₁)
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
                      | bvar k => exact SimC.pure hs₂' rfl
                      | sort u => exact SimC.pure hs₂' rfl
                      | lit l => exact SimC.pure hs₂' rfl
                      | fvar ix nm t => exact SimC.pure hs₂' rfl
                      | app g₀ a₀ => exact SimC.pure hs₂' rfl
                      | lam nm t b' m =>
                        exact SimC.pure hs₂' rfl
                      | forallE nm t b' m =>
                        exact SimC.pure hs₂' rfl
                      | letE nm t v b' =>
                        exact SimC.pure hs₂' rfl
                      | proj sn jx e' =>
                        exact SimC.pure hs₂' rfl
                    | bvar k => exact SimC.pure hs₂' rfl
                    | sort u => exact SimC.pure hs₂' rfl
                    | const nm us'' => exact SimC.pure hs₂' rfl
                    | lit l => exact SimC.pure hs₂' rfl
                    | fvar ix nm t => exact SimC.pure hs₂' rfl
                    | lam nm t b' m => exact SimC.pure hs₂' rfl
                    | forallE nm t b' m =>
                      exact SimC.pure hs₂' rfl
                    | letE nm t v b' =>
                      exact SimC.pure hs₂' rfl
                    | proj sn jx e' => exact SimC.pure hs₂' rfl
                  | bvar k => exact SimC.pure hs₂' rfl
                  | sort u => exact SimC.pure hs₂' rfl
                  | const nm us'' => exact SimC.pure hs₂' rfl
                  | lit l => exact SimC.pure hs₂' rfl
                  | fvar ix nm t => exact SimC.pure hs₂' rfl
                  | lam nm t b' m => exact SimC.pure hs₂' rfl
                  | forallE nm t b' m =>
                    exact SimC.pure hs₂' rfl
                  | letE nm t v b' => exact SimC.pure hs₂' rfl
                  | proj sn jx e' => exact SimC.pure hs₂' rfl
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
          | bvar k => exact SimC.pure hs rfl
          | sort u => exact SimC.pure hs rfl
          | lit l => exact SimC.pure hs rfl
          | fvar ix nm t => exact SimC.pure hs rfl
          | app f₀ a₀ => exact SimC.pure hs rfl
          | lam nm t b' m => exact SimC.pure hs rfl
          | forallE nm t b' m => exact SimC.pure hs rfl
          | letE nm t v b' => exact SimC.pure hs rfl
          | proj sn jx e' => exact SimC.pure hs rfl
        | bvar k => exact SimC.pure hs rfl
        | sort u => exact SimC.pure hs rfl
        | const nm us => exact SimC.pure hs rfl
        | lit l => exact SimC.pure hs rfl
        | fvar ix nm t => exact SimC.pure hs rfl
        | lam nm t b' m => exact SimC.pure hs rfl
        | forallE nm t b' m => exact SimC.pure hs rfl
        | letE nm t v b' => exact SimC.pure hs rfl
        | proj sn jx e' => exact SimC.pure hs rfl
      | bvar k => exact SimC.pure hs rfl
      | sort u => exact SimC.pure hs rfl
      | const nm us => exact SimC.pure hs rfl
      | lit l => exact SimC.pure hs rfl
      | fvar ix nm t => exact SimC.pure hs rfl
      | lam nm t b' m => exact SimC.pure hs rfl
      | forallE nm t b' m => exact SimC.pure hs rfl
      | letE nm t v b' => exact SimC.pure hs rfl
      | proj sn jx e' => exact SimC.pure hs rfl
    | bvar k => exact SimC.pure hs rfl
    | sort u => exact SimC.pure hs rfl
    | const nm us => exact SimC.pure hs rfl
    | lit l => exact SimC.pure hs rfl
    | fvar ix nm t => exact SimC.pure hs rfl
    | lam nm t b' m => exact SimC.pure hs rfl
    | forallE nm t b' m => exact SimC.pure hs rfl
    | letE nm t v b' => exact SimC.pure hs rfl
    | proj sn jx e' => exact SimC.pure hs rfl
  | bvar k => exact SimC.pure hs rfl
  | sort u => exact SimC.pure hs rfl
  | const nm us => exact SimC.pure hs rfl
  | lit l => exact SimC.pure hs rfl
  | fvar ix nm t => exact SimC.pure hs rfl
  | lam nm t b' m => exact SimC.pure hs rfl
  | forallE nm t b' m => exact SimC.pure hs rfl
  | letE nm t v b' => exact SimC.pure hs rfl
  | proj sn jx e' => exact SimC.pure hs rfl

end Walks3

section Walks4

variable {env : Env} {f : Nat}

/-- Port of `projAppsFnI_eff`: the cached projection-function spine
denotes the spec's mapped list. -/
theorem projAppsFnC_eff (T : Name) (us' : List Level) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {targs : List ExprC} {xs : List Expr} {b : ExprC} {xb : Expr},
      RelCL targs xs → RelC b xb →
      CEff mode env s₀ (fun rs => RelCL rs
          (l.map fun i => Expr.mkAppN (.const (projFnName T i) us')
            (xs ++ [xb])))
        (projAppsFnI T us' targs b l)
  | [], s₀, hs, targs, xs, b, xb, htargs, hb => by
    exact CEff.pure hs RelCL.nil
  | i :: rest, s₀, hs, targs, xs, b, xb, htargs, hb => by
    show CEff mode env s₀ _
      (projFnIdxM T i >>= fun pf =>
        internI (.const pf us') >>= fun hd =>
        mkAppNM hd (targs ++ [b]) >>= fun r =>
        projAppsFnI T us' targs b rest >>= fun rs =>
        pure (r :: rs))
    refine CEff.bind (projFnIdxM_eff hs T i) (fun s₀' pf hs₀' hQpf => ?_)
    subst hQpf
    refine CEff.bind
      (internI_eff hs₀' (n := ExprView.const (projFnName T i) us'))
      (fun s₁ hd hs₁ hQh => ?_)
    refine CEff.bind
      (mkAppNM_eff hs₁ hQh (htargs.append (RelCL.cons hb RelCL.nil)))
      (fun s₂ r hs₂ hQr => ?_)
    refine CEff.bind (projAppsFnC_eff T us' rest hs₂ htargs hb)
      (fun s₃ rs hs₃ hQrs => ?_)
    exact CEff.pure hs₃ (RelCL.cons hQr hQrs)

/-- The cached `.proj` spine (the tower spelling, task #175 W4c). -/
theorem projNodesC_eff (T : Name) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {b : ExprC} {xb : Expr}, RelC b xb →
      CEff mode env s₀ (fun rs => RelCL rs (l.map fun i => Expr.proj T i xb))
        (projNodesI T b l)
  | [], s₀, hs, b, xb, hb => by
    exact CEff.pure hs RelCL.nil
  | i :: rest, s₀, hs, b, xb, hb => by
    obtain rfl := hb
    show CEff mode env s₀ _
      (internI (.proj T i b) >>= fun r =>
        projNodesI T b rest >>= fun rs =>
        pure (r :: rs))
    refine CEff.bind (internI_eff hs (n := ExprView.proj T i b))
      (fun s₁ r hs₁ hQr => ?_)
    refine CEff.bind (projNodesC_eff T rest hs₁ rfl)
      (fun s₂ rs hs₂ hQrs => ?_)
    exact CEff.pure hs₂ (RelCL.cons hQr hQrs)

/-- The index's slot tests are the spec's (`mkFEnv`). -/
theorem towerSlotsAllF_mkFEnv (env : Env) (T : Name) (n : Nat) :
    (mkFEnv env).towerSlotsAllF T n = towerSlotsAll env T n := by
  simp only [FEnv.towerSlotsAllF, towerSlotsAll, Env.findProj?, mkFEnv_find?]
  all_goals
    congr 1
    funext j
    cases env.find? (projFnName T j) with
    | none => rfl
    | some ci => cases ci <;> rfl

theorem recSlotsAllF_mkFEnv (env : Env) (T : Name) (n : Nat) :
    (mkFEnv env).recSlotsAllF T n = recSlotsAll env T n := by
  simp only [FEnv.recSlotsAllF, recSlotsAll, mkFEnv_find?]
  all_goals first
    | (congr 1; done)
    | (congr 1
       funext j
       cases env.find? (projFnName T j) with
       | none => rfl
       | some ci => cases ci <;> rfl)

/-- Port of `projAppsI_eff`: the cached fabricated-projection spine
denotes `etaProjs` (task #175 W4c: by entry kind). -/
theorem projAppsC_eff (T : Name) (us' : List Level) (nF : Nat)
    {s₀ : CState} (hs : CSOK mode env s₀)
    {targs : List ExprC} {xs : List Expr} {b : ExprC} {xb : Expr}
    (htargs : RelCL targs xs) (hb : RelC b xb) :
    CEff mode env s₀ (fun rs => RelCL rs (etaProjs env T us' xs xb nF))
      (projAppsI (mkFEnv env) T T us' targs b nF) := by
  unfold projAppsI etaProjs
  rw [towerSlotsAllF_mkFEnv]
  split
  · exact projNodesC_eff T (List.range nF) hs hb
  · exact projAppsFnC_eff T us' (List.range nF) hs htargs hb

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
    simp only [structEtaProjCertsI, structEtaProjCerts]
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
      | projInfo entry =>
        -- the tower-backed slot (task #175 W4c), as the recursor's
        dsimp only
        split
        · refine SimC.bind_left (projFnIdxM_eff hs TI i)
            (fun s₀p pf hs hQpf => ?_)
          refine SimC.bind_left (constTyAtM_eff hs hf)
            (fun s₁ pty hs₁ hQty => ?_)
          have htyw : Expr.WScoped d
              (entry.ty.instantiateLevelParams entry.levelParams us') := by
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

/-- Prefix of a related list. -/
theorem RelCL.take {l : List ExprC} {xs : List Expr} (h : RelCL l xs)
    (k : Nat) : RelCL (l.take k) (xs.take k) := by
  show _ = _
  rw [show l = xs from h]

/-- Suffix of a related list. -/
theorem RelCL.drop {l : List ExprC} {xs : List Expr} (h : RelCL l xs)
    (k : Nat) : RelCL (l.drop k) (xs.drop k) := by
  show _ = _
  rw [show l = xs from h]

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
                  (cvT.type.stripPis cnP).isSome = true ∧
                  (towerSlotsAll env T cnF || recSlotsAll env T cnF) = true then
                liftFueled "level comparison"
                  (Level.isEquivList us us') >>= fun ok =>
                if ok then
                  iotaCerts (fueledFns mode env) env d false
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
                            iotaCerts (fueledFns mode env) env d false
                              (cvc.type.instantiateLevelParams
                                cvc.levelParams us)
                              (wtb.getAppArgs ++
                                etaProjs env T us' wtb.getAppArgs b cnF)
                          else pure true) >>= fun r₄ =>
                        if r₄ then
                          defEqList (fueledFns mode env) env d
                            (a.getAppArgs.drop cnP)
                            (etaProjs env T us' wtb.getAppArgs b cnF)
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
                    (cvT.type.stripPis cnP).isSome = true ∧
                    ((mkFEnv env).towerSlotsAllF Tn cnF ||
                      (mkFEnv env).recSlotsAllF Tn cnF) = true then
                  isEquivListLM us us' >>= fun o =>
                  liftFueled "level comparison" o >>= fun ok =>
                  if ok then
                    constTyAtM (mkFEnv env) T Tn us' >>= fun tyT =>
                    iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
                        false tyT targs >>= fun r₁ =>
                    if r₁ then
                      structEtaProjCertsI (coreKnotI mode (mkFEnv env) f)
                          (mkFEnv env) d T Tn us' targs j cvT.levelParams
                          (List.range cnF) >>= fun r₂ =>
                      if r₂ then
                        defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
                            d (aargs.take cnP) targs >>= fun r₃ =>
                        if r₃ then
                          projAppsI (mkFEnv env) Tn T us' targs j cnF >>=
                            fun projs =>
                          (if mode.ttChecks then
                              constTyAtM (mkFEnv env) c cn us >>= fun tyCtor =>
                              iotaCertsI (coreKnotI mode (mkFEnv env) f)
                                (mkFEnv env) d false tyCtor (targs ++ projs)
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
  obtain rfl := hdena
  obtain rfl := hdenb
  obtain rfl := hdenw
  have hdenb : RelC j j := rfl
  rw [structEtaCertWithC_unfold]
  refine SimC.withStore ?_
  have haargs : RelCL (ExprC.getAppArgs i) (Expr.getAppArgs i) :=
    ExprC.getAppArgs_spec i
  have hlena : (ExprC.getAppArgs i).length
      = (Expr.getAppArgs i).length := RelCL.length haargs
  have htargs : RelCL (ExprC.getAppArgs w) (Expr.getAppArgs w) :=
    ExprC.getAppArgs_spec w
  have hlenw : (ExprC.getAppArgs w).length
      = (Expr.getAppArgs w).length := RelCL.length htargs
  have hfa := ExprC.getAppFn_spec i
  have hfw := ExprC.getAppFn_spec w
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hga : ExprC.getAppFn i = ga at hfa ⊢
  cases ga with
  | const c us =>
    rw [show (Expr.getAppFn i) = Expr.const c us from hfa.symm]
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
          generalize hgw : ExprC.getAppFn w = gw at hfw ⊢
          cases gw with
          | const T us' =>
            rw [show (Expr.getAppFn w) = Expr.const T us' from hfw.symm]
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
                rw [towerSlotsAllF_mkFEnv, recSlotsAllF_mkFEnv]
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
                            cnF hs₅ htargs hdenb)
                            (fun s₆ projs hs₆ hQp => ?_)
                          have hwprojs : ∀ x ∈ etaProjs env T us'
                              (Expr.getAppArgs w) j cnF,
                              Expr.WScoped d x := by
                            intro x hx
                            unfold etaProjs at hx
                            split at hx
                            · obtain ⟨i', -, rfl⟩ := List.mem_map.mp hx
                              simpa [Expr.WScoped] using hwb
                            · obtain ⟨i', -, rfl⟩ := List.mem_map.mp hx
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
          | bvar k =>
            rw [show (Expr.getAppFn w) = Expr.bvar k from hfw.symm]
            exact SimC.pure hs rfl
          | sort u =>
            rw [show (Expr.getAppFn w) = Expr.sort u from hfw.symm]
            exact SimC.pure hs rfl
          | lit l =>
            rw [show (Expr.getAppFn w) = Expr.lit l from hfw.symm]
            exact SimC.pure hs rfl
          | fvar ix nm t =>
            rw [show (Expr.getAppFn w) = Expr.fvar ix nm t
              from hfw.symm]
            exact SimC.pure hs rfl
          | app f' a' =>
            rw [show (Expr.getAppFn w) = Expr.app f' a'
              from hfw.symm]
            exact SimC.pure hs rfl
          | lam nm t b' m =>
            rw [show (Expr.getAppFn w)
              = Expr.lam nm t b' m from hfw.symm]
            exact SimC.pure hs rfl
          | forallE nm t b' m =>
            rw [show (Expr.getAppFn w)
              = Expr.forallE nm t b' m from hfw.symm]
            exact SimC.pure hs rfl
          | letE nm t v b' =>
            rw [show (Expr.getAppFn w)
              = Expr.letE nm t v b'
              from hfw.symm]
            exact SimC.pure hs rfl
          | proj sn jx e' =>
            rw [show (Expr.getAppFn w) = Expr.proj sn jx e'
              from hfw.symm]
            exact SimC.pure hs rfl
        · exact SimC.pure hs rfl
      | axiomInfo cv => exact SimC.pure hs rfl
      | defnInfo cv v h => exact SimC.pure hs rfl
      | thmInfo cv v => exact SimC.pure hs rfl
      | indInfo cv caps => exact SimC.pure hs rfl
      | recInfo cv mI rP rules => exact SimC.pure hs rfl
      | projInfo entry => exact SimC.pure hs rfl
  | bvar k =>
    rw [show (Expr.getAppFn i) = Expr.bvar k from hfa.symm]
    exact SimC.pure hs rfl
  | sort u =>
    rw [show (Expr.getAppFn i) = Expr.sort u from hfa.symm]
    exact SimC.pure hs rfl
  | lit l =>
    rw [show (Expr.getAppFn i) = Expr.lit l from hfa.symm]
    exact SimC.pure hs rfl
  | fvar ix nm t =>
    rw [show (Expr.getAppFn i) = Expr.fvar ix nm t from hfa.symm]
    exact SimC.pure hs rfl
  | app f' a' =>
    rw [show (Expr.getAppFn i) = Expr.app f' a'
      from hfa.symm]
    exact SimC.pure hs rfl
  | lam nm t b' m =>
    rw [show (Expr.getAppFn i) = Expr.lam nm t b' m
      from hfa.symm]
    exact SimC.pure hs rfl
  | forallE nm t b' m =>
    rw [show (Expr.getAppFn i) = Expr.forallE nm t b' m
      from hfa.symm]
    exact SimC.pure hs rfl
  | letE nm t v b' =>
    rw [show (Expr.getAppFn i)
      = Expr.letE nm t v b' from hfa.symm]
    exact SimC.pure hs rfl
  | proj sn jx e' =>
    rw [show (Expr.getAppFn i) = Expr.proj sn jx e' from hfa.symm]
    exact SimC.pure hs rfl

/-- Port of `structEtaCertI_sim`. -/
theorem structEtaCertC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : ExprC} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (structEtaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (structEtaCert mode (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    ((coreKnotI mode (mkFEnv env) f).inferIO d j >>= fun tb =>
      (coreKnotI mode (mkFEnv env) f).whnf d tb >>= fun wtb =>
      structEtaCertWithI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
        i j wtb)
    ((fueledFns mode env).inferIO d b >>= fun tb =>
      (fueledFns mode env).whnf d tb >>= fun wtb =>
      structEtaCertWith mode (fueledFns mode env) env d a b wtb)
  refine SimC.bind (ih.inferIO hs hdenb hwb) (fun s₁ tb tbx hs₁ hP => ?_)
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
      (stuckIrrelI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (stuckIrrel mode (fueledFns mode env) env d a b) := by
  show SimC mode env s₀ RelVC
    (pairEtaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
      fun r₁ =>
      if r₁ then pure true else
      pairEtaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d j i >>=
        fun r₂ =>
      if r₂ then pure true else
      structEtaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₃ =>
      if r₃ then pure true else
      structEtaCertI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d j i >>=
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
  refine SimC.bind (pairEtaCertC_sim ih hs hdena hdenb hwa hwb)
    (fun s₁ r₁ r₁' hs₁ hP₁ => ?_)
  obtain rfl : r₁ = r₁' := hP₁
  cases r₁ with
  | true => simp only [↓reduceIte]; exact SimC.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimC.bind (pairEtaCertC_sim ih hs₁ hdenb hdena hwb hwa)
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
