import Setlec.Verify.DiscI1

/-!
# Interned body walks, part 2: the stuck-term certificates

Simulation walks for `proofIrrelI`, the eta/unit certificates,
`projCertI` and `stuckIrrelI`, mirroring the corresponding
`Setlec/Verify/Disc.lean` walks (same sites, same scoping facts) with
the denotation plumbing on top.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

section Walks

variable {env : Env} {f : Nat}

theorem proofIrrelI_sim (ih : SSimI env f) {d : Nat} {i j : EIdx}
    {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (proofIrrelI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (proofIrrel (fueledFns env) env d a b) := by
  show SimAt env s₀ RelV
    ((coreKnotI (mkFEnv env) f).infer d i >>= fun ta =>
      (coreKnotI (mkFEnv env) f).whnf d ta >>= fun wta =>
      Setlec.withStore (fun st => isUnitLikeTyI (mkFEnv env) st wta) >>=
        fun c₁ =>
      if c₁ then
        (coreKnotI (mkFEnv env) f).infer d j >>= fun tb =>
        (coreKnotI (mkFEnv env) f).whnf d tb >>= fun wtb =>
        Setlec.withStore (fun st => isUnitLikeTyI (mkFEnv env) st wtb) >>=
          fun c₂ =>
        if c₂ then pure true else pure false
      else
        (coreKnotI (mkFEnv env) f).infer d ta >>= fun tta =>
        (coreKnotI (mkFEnv env) f).whnf d tta >>= fun wtta =>
        viewI wtta >>= fun n =>
        match n with
        | some (.sort uT) =>
          liftFueled "level comparison" (Level.isEquiv uT .zero) >>=
            fun okA =>
          (coreKnotI (mkFEnv env) f).infer d j >>= fun tb =>
          (coreKnotI (mkFEnv env) f).infer d tb >>= fun ttb =>
          (coreKnotI (mkFEnv env) f).whnf d ttb >>= fun wttb =>
          viewI wttb >>= fun n' =>
          match n' with
          | some (.sort vT) =>
            liftFueled "level comparison" (Level.isEquiv vT .zero) >>=
              fun okB =>
            pure (okA && okB)
          | _ => pure false
        | _ => pure false)
    (proofIrrel (fueledFns env) env d a b)
  refine SimAt.bind (ih.infer hs hdena hwa)
    (fun s₁ ta tax hs₁ hext₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimAt.bind (ih.whnf hs₁ htad hwta)
    (fun s₂ wta wtax hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimAt.withStore ?_
  rw [isUnitLikeTyI_spec hs₂.wf hwtad]
  by_cases hu : isUnitLikeTy env wtax
  · rw [if_pos hu, if_pos hu]
    refine SimAt.bind (ih.infer hs₂
      (denote_mono (hext₁.trans hext₂) hdenb) hwb)
      (fun s₃ tb tbx hs₃ hext₃ hP₃ => ?_)
    obtain ⟨htbd, hwtb⟩ := hP₃
    refine SimAt.bind (ih.whnf hs₃ htbd hwtb)
      (fun s₄ wtb wtbx hs₄ hext₄ hP₄ => ?_)
    obtain ⟨hwtbd, hwwtb⟩ := hP₄
    refine SimAt.withStore ?_
    rw [isUnitLikeTyI_spec hs₄.wf hwtbd]
    by_cases hu₂ : isUnitLikeTy env wtbx
    · rw [if_pos hu₂, if_pos hu₂]
      exact SimAt.pure hs₄ rfl
    · rw [if_neg hu₂, if_neg hu₂]
      exact SimAt.pure hs₄ rfl
  · rw [if_neg hu, if_neg hu]
    refine SimAt.bind (ih.infer hs₂ (denote_mono hext₂ htad)
      (WScoped.mono (Nat.le_refl d) hwta))
      (fun s₃ tta ttax hs₃ hext₃ hP₃ => ?_)
    obtain ⟨httad, hwtta⟩ := hP₃
    refine SimAt.bind (ih.whnf hs₃ httad hwtta)
      (fun s₄ wtta wttax hs₄ hext₄ hP₄ => ?_)
    obtain ⟨hwttad, hwwtta⟩ := hP₄
    refine SimAt.view ?_
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hwttad
    rw [hn]
    cases n with
    | sort uT =>
      cases hd
      refine SimAt.bind (SimAt.liftFueled _ _ hs₄)
        (fun s₅ okA okA' hs₅ hext₅ hPok => ?_)
      obtain rfl : okA = okA' := hPok
      refine SimAt.bind (ih.infer hs₅
        (denote_mono ((((hext₁.trans hext₂).trans hext₃).trans
          hext₄).trans hext₅) hdenb) hwb)
        (fun s₆ tb tbx hs₆ hext₆ hP₆ => ?_)
      obtain ⟨htbd, hwtb⟩ := hP₆
      refine SimAt.bind (ih.infer hs₆ htbd hwtb)
        (fun s₇ ttb ttbx hs₇ hext₇ hP₇ => ?_)
      obtain ⟨httbd, hwttb⟩ := hP₇
      refine SimAt.bind (ih.whnf hs₇ httbd hwttb)
        (fun s₈ wttb wttbx hs₈ hext₈ hP₈ => ?_)
      obtain ⟨hwttbd, hwwttb⟩ := hP₈
      refine SimAt.view ?_
      obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hwttbd
      rw [hn']
      cases n' with
      | sort vT =>
        cases hd'
        refine SimAt.bind (SimAt.liftFueled _ _ hs₈)
          (fun s₉ okB okB' hs₉ hext₉ hPok' => ?_)
        obtain rfl : okB = okB' := hPok'
        exact SimAt.pure hs₉ rfl
      | bvar k => invert_node hd'; exact SimAt.pure hs₈ rfl
      | const nm us => invert_node hd'; exact SimAt.pure hs₈ rfl
      | lit l => invert_node hd'; exact SimAt.pure hs₈ rfl
      | fvar idx nm t => invert_node hd'; exact SimAt.pure hs₈ rfl
      | app f' a' => invert_node hd'; exact SimAt.pure hs₈ rfl
      | lam nm t b' m => invert_node hd'; exact SimAt.pure hs₈ rfl
      | forallE nm t b' m => invert_node hd'; exact SimAt.pure hs₈ rfl
      | letE nm t v b' => invert_node hd'; exact SimAt.pure hs₈ rfl
      | proj s' j' e' => invert_node hd'; exact SimAt.pure hs₈ rfl
    | bvar k => invert_node hd; exact SimAt.pure hs₄ rfl
    | const nm us => invert_node hd; exact SimAt.pure hs₄ rfl
    | lit l => invert_node hd; exact SimAt.pure hs₄ rfl
    | fvar idx nm t => invert_node hd; exact SimAt.pure hs₄ rfl
    | app f' a' => invert_node hd; exact SimAt.pure hs₄ rfl
    | lam nm t b' m => invert_node hd; exact SimAt.pure hs₄ rfl
    | forallE nm t b' m => invert_node hd; exact SimAt.pure hs₄ rfl
    | letE nm t v b' => invert_node hd; exact SimAt.pure hs₄ rfl
    | proj s' j' e' => invert_node hd; exact SimAt.pure hs₄ rfl

end Walks

section Walks2

variable {env : Env} {f : Nat}

theorem etaCertI_sim (ih : SSimI env f) {d : Nat} {n₁ : Name}
    {ty₁ body₁ b : EIdx} {ty₁x body₁x bx : Expr} {m₁ : BinderMeta}
    {s₀ : IState} (hs : ISOK env s₀)
    (hty : s₀.store.denote ty₁ = some ty₁x)
    (hbody : s₀.store.denote body₁ = some body₁x)
    (hb : s₀.store.denote b = some bx)
    (hwty : WScoped d ty₁x) (hwbody : WScoped d body₁x)
    (hwb : WScoped d bx) :
    SimAt env s₀ RelV
      (etaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d n₁ ty₁ body₁ m₁ b)
      (etaCert (fueledFns env) env d n₁ ty₁x body₁x m₁ bx) := by
  show SimAt env s₀ RelV
    ((coreKnotI (mkFEnv env) f).infer d b >>= fun tb =>
      (coreKnotI (mkFEnv env) f).whnf d tb >>= fun wtb =>
      viewI wtb >>= fun n =>
      match n with
      | some (.forallE _ ty₂ _ m₂) =>
        match m₁.cod, m₂.cod with
        | some v₁, some v₂ =>
          liftFueled "level comparison" (Level.isEquiv v₁ v₂) >>= fun ok =>
          if ok then
            (coreKnotI (mkFEnv env) f).defeq d ty₂ ty₁ >>= fun r =>
            if r then
              internI (.fvar d n₁ ty₁) >>= fun fv =>
              inst1M body₁ fv >>= fun b₁ =>
              internI (.app b fv) >>= fun ba =>
              (coreKnotI (mkFEnv env) f).defeq (d + 1) b₁ ba
            else pure false
          else pure false
        | _, _ => pure false
      | _ => pure false)
    ((fueledFns env).infer d bx >>= fun tb =>
      (fueledFns env).whnf d tb >>= fun wtb =>
      match wtb with
      | .forallE _ ty₂ _ m₂ =>
        match m₁.cod, m₂.cod with
        | some v₁, some v₂ =>
          liftFueled "level comparison" (Level.isEquiv v₁ v₂) >>= fun ok =>
          if ok then
            (fueledFns env).defeq d ty₂ ty₁x >>= fun r =>
            if r then
              (fueledFns env).defeq (d + 1)
                (body₁x.instantiate1 (.fvar d n₁ ty₁x))
                (.app bx (.fvar d n₁ ty₁x))
            else pure false
          else pure false
        | _, _ => pure false
      | _ => pure false)
  refine SimAt.bind (ih.infer hs hb hwb) (fun s₁ tb tbx hs₁ hext₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimAt.bind (ih.whnf hs₁ htbd hwtb)
    (fun s₂ wtb wtbx hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hwtbd
  rw [hn]
  cases n with
  | forallE nm ty₂ b₂ m₂ =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ty₂x, hty₂, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨b₂x, hb₂, hd⟩ := hd
    subst hd
    dsimp only
    have hwty₂ : WScoped d ty₂x := by
      simp only [WScoped] at hwwtb
      exact hwwtb.1
    cases hc₁ : m₁.cod with
    | none => exact SimAt.pure hs₂ rfl
    | some v₁ =>
      cases hc₂ : m₂.cod with
      | none => exact SimAt.pure hs₂ rfl
      | some v₂ =>
        dsimp only
        refine SimAt.bind (SimAt.liftFueled _ _ hs₂)
          (fun s₃ ok ok' hs₃ hext₃ hPok => ?_)
        obtain rfl : ok = ok' := hPok
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.pure hs₃ rfl
        | true =>
          simp only [↓reduceIte]
          refine SimAt.bind (ih.defeq hs₃ (denote_mono hext₃ hty₂)
            (denote_mono ((hext₁.trans hext₂).trans hext₃) hty)
            hwty₂ hwty) (fun s₄ r r' hs₄ hext₄ hPr => ?_)
          obtain rfl : r = r' := hPr
          cases r with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.pure hs₄ rfl
          | true =>
            simp only [↓reduceIte]
            have hext₀₄ :=
              ((hext₁.trans hext₂).trans hext₃).trans hext₄
            have hfvd : denoteNode s₄.store.denote (.fvar d n₁ ty₁)
                = some (.fvar d n₁ ty₁x) := by
              rw [denoteNode, denote_mono hext₀₄ hty]; rfl
            refine SimAt.bind_left (internI_eff hs₄ hfvd)
              (fun s₅ fv hs₅ hext₅ hQfv => ?_)
            refine SimAt.bind_left (inst1M_eff hs₅
              (denote_mono (hext₀₄.trans hext₅) hbody) hQfv)
              (fun s₆ b₁ hs₆ hext₆ hQb₁ => ?_)
            have hbad : denoteNode s₆.store.denote (.app b fv)
                = some (.app bx (.fvar d n₁ ty₁x)) := by
              rw [denoteNode,
                denote_mono ((hext₀₄.trans hext₅).trans hext₆) hb,
                denote_mono hext₆ hQfv]
              rfl
            refine SimAt.bind_left (internI_eff hs₆ hbad)
              (fun s₇ ba hs₇ hext₇ hQba => ?_)
            refine ih.defeq hs₇ (denote_mono hext₇ hQb₁) hQba
              (WScoped.instantiate1 hwty 0 hwbody) ?_
            show WScoped (d + 1) (.app bx (.fvar d n₁ ty₁x))
            simp only [WScoped]
            exact ⟨WScoped.mono (Nat.le_succ d) hwb, Nat.lt_succ_self d,
              hwty⟩
  | bvar k => invert_node hd; exact SimAt.pure hs₂ rfl
  | sort u => invert_node hd; exact SimAt.pure hs₂ rfl
  | const nm us => invert_node hd; exact SimAt.pure hs₂ rfl
  | lit l => invert_node hd; exact SimAt.pure hs₂ rfl
  | fvar idx nm t => invert_node hd; exact SimAt.pure hs₂ rfl
  | app f' a' => invert_node hd; exact SimAt.pure hs₂ rfl
  | lam nm t b' m => invert_node hd; exact SimAt.pure hs₂ rfl
  | letE nm t v b' => invert_node hd; exact SimAt.pure hs₂ rfl
  | proj s' j' e' => invert_node hd; exact SimAt.pure hs₂ rfl

theorem projCertI_sim (ih : SSimI env f) {d : Nat} {i : EIdx} {e₂ : Expr}
    {idx : Nat} {fieldLvl structLvl : Level} {nP : Nat}
    {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some e₂) (hw : WScoped d e₂) :
    SimAt env s₀ RelV
      (projCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i idx
        fieldLvl structLvl nP)
      (projCert (fueledFns env) env d e₂ idx fieldLvl structLvl nP) := by
  show SimAt env s₀ RelV
    (internI (.bvar 0) >>= fun bvar0 =>
      Setlec.withStore (·.getAppArgsI i) >>= fun args =>
      (coreKnotI (mkFEnv env) f).infer d (args.getD (nP + idx) bvar0) >>=
        fun ta =>
      (coreKnotI (mkFEnv env) f).infer d ta >>= fun tta =>
      (coreKnotI (mkFEnv env) f).whnf d tta >>= fun wtta =>
      viewI wtta >>= fun n =>
      match n with
      | some (.sort uT) =>
        liftFueled "level comparison" (Level.isEquiv uT fieldLvl) >>=
          fun okT =>
        (coreKnotI (mkFEnv env) f).infer d i >>= fun te =>
        (coreKnotI (mkFEnv env) f).infer d te >>= fun tte =>
        (coreKnotI (mkFEnv env) f).whnf d tte >>= fun wtte =>
        viewI wtte >>= fun n' =>
        match n' with
        | some (.sort wT) =>
          liftFueled "level comparison" (Level.isEquiv wT structLvl) >>=
            fun okW =>
          pure (okT && okW)
        | _ => pure false
      | _ => pure false)
    (projCert (fueledFns env) env d e₂ idx fieldLvl structLvl nP)
  have hbv : denoteNode s₀.store.denote (.bvar 0) = some (.bvar 0) := rfl
  refine SimAt.bind_left (internI_eff hs hbv)
    (fun s₁ bvar0 hs₁ hext₁ hQ0 => ?_)
  refine SimAt.withStore ?_
  have hargs := getAppArgsI_spec hs₁.wf (denote_mono hext₁ hden)
  have hargd := DenL.getD hQ0 (nP + idx) hargs
  have hwarg : WScoped d (e₂.getAppArgs.getD (nP + idx) (.bvar 0)) :=
    wscoped_getD hw.getAppArgs _
  refine SimAt.bind (ih.infer hs₁ hargd hwarg)
    (fun s₂ ta tax hs₂ hext₂ hP₂ => ?_)
  obtain ⟨htad, hwta⟩ := hP₂
  refine SimAt.bind (ih.infer hs₂ htad hwta)
    (fun s₃ tta ttax hs₃ hext₃ hP₃ => ?_)
  obtain ⟨httad, hwtta⟩ := hP₃
  refine SimAt.bind (ih.whnf hs₃ httad hwtta)
    (fun s₄ wtta wttax hs₄ hext₄ hP₄ => ?_)
  obtain ⟨hwttad, hwwtta⟩ := hP₄
  refine SimAt.view ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hwttad
  rw [hn]
  cases n with
  | sort uT =>
    cases hd
    refine SimAt.bind (SimAt.liftFueled _ _ hs₄)
      (fun s₅ okT okT' hs₅ hext₅ hPok => ?_)
    obtain rfl : okT = okT' := hPok
    refine SimAt.bind (ih.infer hs₅
      (denote_mono (((((hext₁.trans hext₂).trans hext₃).trans
        hext₄).trans hext₅)) hden) hw)
      (fun s₆ te tex hs₆ hext₆ hP₆ => ?_)
    obtain ⟨hted, hwte⟩ := hP₆
    refine SimAt.bind (ih.infer hs₆ hted hwte)
      (fun s₇ tte ttex hs₇ hext₇ hP₇ => ?_)
    obtain ⟨htted, hwtte⟩ := hP₇
    refine SimAt.bind (ih.whnf hs₇ htted hwtte)
      (fun s₈ wtte wttex hs₈ hext₈ hP₈ => ?_)
    obtain ⟨hwtted, hwwtte⟩ := hP₈
    refine SimAt.view ?_
    obtain ⟨n', hn', hc', hd'⟩ := denote_some_inv hwtted
    rw [hn']
    cases n' with
    | sort wT =>
      cases hd'
      refine SimAt.bind (SimAt.liftFueled _ _ hs₈)
        (fun s₉ okW okW' hs₉ hext₉ hPok' => ?_)
      obtain rfl : okW = okW' := hPok'
      exact SimAt.pure hs₉ rfl
    | bvar k => invert_node hd'; exact SimAt.pure hs₈ rfl
    | const nm us => invert_node hd'; exact SimAt.pure hs₈ rfl
    | lit l => invert_node hd'; exact SimAt.pure hs₈ rfl
    | fvar idx' nm t => invert_node hd'; exact SimAt.pure hs₈ rfl
    | app f' a' => invert_node hd'; exact SimAt.pure hs₈ rfl
    | lam nm t b' m => invert_node hd'; exact SimAt.pure hs₈ rfl
    | forallE nm t b' m => invert_node hd'; exact SimAt.pure hs₈ rfl
    | letE nm t v b' => invert_node hd'; exact SimAt.pure hs₈ rfl
    | proj s' j' e' => invert_node hd'; exact SimAt.pure hs₈ rfl
  | bvar k => invert_node hd; exact SimAt.pure hs₄ rfl
  | const nm us => invert_node hd; exact SimAt.pure hs₄ rfl
  | lit l => invert_node hd; exact SimAt.pure hs₄ rfl
  | fvar idx' nm t => invert_node hd; exact SimAt.pure hs₄ rfl
  | app f' a' => invert_node hd; exact SimAt.pure hs₄ rfl
  | lam nm t b' m => invert_node hd; exact SimAt.pure hs₄ rfl
  | forallE nm t b' m => invert_node hd; exact SimAt.pure hs₄ rfl
  | letE nm t v b' => invert_node hd; exact SimAt.pure hs₄ rfl
  | proj s' j' e' => invert_node hd; exact SimAt.pure hs₄ rfl

theorem structUnitCertI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i j : EIdx} {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (structUnitCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (structUnitCert (fueledFns env) env d a b) := by
  show SimAt env s₀ RelV
    ((coreKnotI (mkFEnv env) f).infer d i >>= fun ta =>
      (coreKnotI (mkFEnv env) f).whnf d ta >>= fun wta =>
      Setlec.withStore (fun st => st.nodes[st.getAppFnI wta]?) >>= fun n =>
      match n with
      | some (.const T us') =>
        match (mkFEnv env).find? T with
        | some (.indInfo cvT caps) =>
          Setlec.withStore (·.getAppArgsI wta) >>= fun targs =>
          if caps.unitlike = true ∧
              reservedBasisNames.contains T = false ∧
              targs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length ∧
              (cvT.type.stripPis caps.unitParams).isSome = true then
            (coreKnotI (mkFEnv env) f).infer d j >>= fun tb =>
            (coreKnotI (mkFEnv env) f).whnf d tb >>= fun wtb =>
            (coreKnotI (mkFEnv env) f).defeq d wta wtb >>= fun r =>
            if r then
              constTyAtM (mkFEnv env) T us' >>= fun tyT =>
              iotaCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d tyT targs
            else pure false
          else pure false
        | _ => pure false
      | _ => pure false)
    ((fueledFns env).infer d a >>= fun ta =>
      (fueledFns env).whnf d ta >>= fun wta =>
      match wta.getAppFn with
      | .const T us' =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if caps.unitlike = true ∧
              reservedBasisNames.contains T = false ∧
              wta.getAppArgs.length = caps.unitParams ∧
              us'.length = cvT.levelParams.length ∧
              (cvT.type.stripPis caps.unitParams).isSome = true then
            (fueledFns env).infer d b >>= fun tb =>
            (fueledFns env).whnf d tb >>= fun wtb =>
            (fueledFns env).defeq d wta wtb >>= fun r =>
            if r then
              iotaCerts (fueledFns env) env d
                (cvT.type.instantiateLevelParams cvT.levelParams us')
                wta.getAppArgs
            else pure false
          else pure false
        | _ => pure false
      | _ => pure false)
  refine SimAt.bind (ih.infer hs hdena hwa)
    (fun s₁ ta tax hs₁ hext₁ hP => ?_)
  obtain ⟨htad, hwta⟩ := hP
  refine SimAt.bind (ih.whnf hs₁ htad hwta)
    (fun s₂ wta wtax hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hwtad, hwwta⟩ := hP₂
  refine SimAt.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hs₂.wf hwtad)
  rw [hn]
  cases n with
  | const T us' =>
    have hxf := Option.some.inj hd
    rw [← hxf]
    dsimp only
    rw [mkFEnv_find?]
    cases hfT : env.find? T with
    | none => exact SimAt.pure hs₂ rfl
    | some ci =>
      cases ci with
      | indInfo cvT caps =>
        dsimp only
        refine SimAt.withStore ?_
        have hargs := getAppArgsI_spec hs₂.wf hwtad
        rw [hargs.length_eq]
        split
        · rename_i hcond
          refine SimAt.bind (ih.infer hs₂
            (denote_mono (hext₁.trans hext₂) hdenb) hwb)
            (fun s₃ tb tbx hs₃ hext₃ hP₃ => ?_)
          obtain ⟨htbd, hwtb⟩ := hP₃
          refine SimAt.bind (ih.whnf hs₃ htbd hwtb)
            (fun s₄ wtb wtbx hs₄ hext₄ hP₄ => ?_)
          obtain ⟨hwtbd, hwwtb⟩ := hP₄
          refine SimAt.bind (ih.defeq hs₄
            (denote_mono (hext₃.trans hext₄) hwtad) hwtbd
            hwwta hwwtb) (fun s₅ r r' hs₅ hext₅ hPr => ?_)
          obtain rfl : r = r' := hPr
          cases r with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.pure hs₅ rfl
          | true =>
            simp only [↓reduceIte]
            refine SimAt.bind_left (constTyAtM_eff hs₅ hfT)
              (fun s₆ tyT hs₆ hext₆ hQty => ?_)
            have htyw : WScoped d
                (cvT.type.instantiateLevelParams cvT.levelParams us') := by
              obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
              exact wscoped_instLevels_of_not_hasFvar htf _ _
            refine iotaCertsI_sim ih hs₆ hQty htyw
              (hargs.mono ((((hext₃.trans hext₄).trans hext₅).trans
                hext₆)))
              hwwta.getAppArgs
        · exact SimAt.pure hs₂ rfl
      | axiomInfo cv => exact SimAt.pure hs₂ rfl
      | defnInfo cv v h => exact SimAt.pure hs₂ rfl
      | thmInfo cv v => exact SimAt.pure hs₂ rfl
      | ctorInfo cv nP nF => exact SimAt.pure hs₂ rfl
      | recInfo cv mI rP rules => exact SimAt.pure hs₂ rfl
      | projInfo entry => exact SimAt.pure hs₂ rfl
  | bvar k =>
    rw [← Option.some.inj hd]; exact SimAt.pure hs₂ rfl
  | sort u =>
    rw [← Option.some.inj hd]; exact SimAt.pure hs₂ rfl
  | lit l =>
    rw [← Option.some.inj hd]; exact SimAt.pure hs₂ rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs₂ rfl
  | app f' a' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs₂ rfl
  | lam nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs₂ rfl
  | forallE nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs₂ rfl
  | letE nm t v b' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs₂ rfl
  | proj s' j' e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs₂ rfl

end Walks2

section Walks3

variable {env : Env} {f : Nat}

private theorem pairEtaCert_unfold (env : Env) (d : Nat) (a b : Expr) :
    pairEtaCert (fueledFns env) env d a b =
    (match a with
    | .app (.app (.app (.app (.const c us) _pα) _pβ) xs₁) xs₂ =>
      match env.find? c with
      | some (.ctorInfo _cvm 2 2) =>
        (fueledFns env).infer d b >>= fun tb =>
        (fueledFns env).whnf d tb >>= fun wtb =>
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
                  (fueledFns env).defeq d xs₁ (.proj c' 0 b) >>= fun r₁ =>
                  if r₁ then
                    (fueledFns env).defeq d xs₂ (.proj c' 1 b)
                  else pure false
                else pure false
              else pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false) := rfl

theorem pairEtaCertI_sim (ih : SSimI env f) {d : Nat} {i j : EIdx}
    {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (pairEtaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (pairEtaCert (fueledFns env) env d a b) := by
  show SimAt env s₀ RelV
    (viewI i >>= fun n₀ =>
      match n₀ with
      | some (.app f₄ s₂) =>
        viewI f₄ >>= fun n₁ =>
        match n₁ with
        | some (.app f₃ s₁) =>
          viewI f₃ >>= fun n₂ =>
          match n₂ with
          | some (.app f₂ _pβ) =>
            viewI f₂ >>= fun n₃ =>
            match n₃ with
            | some (.app f₁ _pα) =>
              viewI f₁ >>= fun n₄ =>
              match n₄ with
              | some (.const c us) =>
                match (mkFEnv env).find? c with
                | some (.ctorInfo _cvm 2 2) =>
                  (coreKnotI (mkFEnv env) f).infer d j >>= fun tb =>
                  (coreKnotI (mkFEnv env) f).whnf d tb >>= fun wtb =>
                  viewI wtb >>= fun m₀ =>
                  match m₀ with
                  | some (.app g₂ _B) =>
                    viewI g₂ >>= fun m₁ =>
                    match m₁ with
                    | some (.app g₁ _A) =>
                      viewI g₁ >>= fun m₂ =>
                      match m₂ with
                      | some (.const c' us') =>
                        match (mkFEnv env).find? c' with
                        | some (.indInfo _ _) =>
                          match (mkFEnv env).find? (c'.str "rec") with
                          | some (.recInfo _ mI rP [rr]) =>
                            if rr.ctor = c ∧ rr.nfields = 2 ∧ mI = rP ∧
                                reservedBasisNames.contains (c'.str "rec")
                                  = true then
                              liftFueled "level comparison"
                                (Level.isEquivList us us') >>= fun ok =>
                              if ok then
                                internI (.proj c' 0 j) >>= fun p₀ =>
                                (coreKnotI (mkFEnv env) f).defeq d s₁ p₀ >>=
                                  fun r₁ =>
                                if r₁ then
                                  internI (.proj c' 1 j) >>= fun p₁ =>
                                  (coreKnotI (mkFEnv env) f).defeq d s₂ p₁
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
    (pairEtaCert (fueledFns env) env d a b)
  rw [pairEtaCert_unfold]
  refine SimAt.view ?_
  obtain ⟨n₀, hn₀, hc₀, hd₀⟩ := denote_some_inv hdena
  rw [hn₀]
  cases n₀ with
  | app f₄ s₂ =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd₀
    obtain ⟨xf₄, hf₄, hd₀⟩ := hd₀
    rw [Option.map_eq_some_iff] at hd₀
    obtain ⟨xs₂, hs₂d, hd₀⟩ := hd₀
    subst hd₀
    refine SimAt.view ?_
    obtain ⟨n₁, hn₁, hc₁, hd₁⟩ := denote_some_inv hf₄
    rw [hn₁]
    cases n₁ with
    | app f₃ s₁ =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd₁
      obtain ⟨xf₃, hf₃, hd₁⟩ := hd₁
      rw [Option.map_eq_some_iff] at hd₁
      obtain ⟨xs₁, hs₁d, hd₁⟩ := hd₁
      subst hd₁
      refine SimAt.view ?_
      obtain ⟨n₂, hn₂, hc₂, hd₂⟩ := denote_some_inv hf₃
      rw [hn₂]
      cases n₂ with
      | app f₂ pβ =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd₂
        obtain ⟨xf₂, hf₂, hd₂⟩ := hd₂
        rw [Option.map_eq_some_iff] at hd₂
        obtain ⟨xpβ, hpβ, hd₂⟩ := hd₂
        subst hd₂
        refine SimAt.view ?_
        obtain ⟨n₃, hn₃, hc₃, hd₃⟩ := denote_some_inv hf₂
        rw [hn₃]
        cases n₃ with
        | app f₁ pα =>
          rw [denoteNode, Option.bind_eq_some_iff] at hd₃
          obtain ⟨xf₁, hf₁, hd₃⟩ := hd₃
          rw [Option.map_eq_some_iff] at hd₃
          obtain ⟨xpα, hpα, hd₃⟩ := hd₃
          subst hd₃
          refine SimAt.view ?_
          obtain ⟨n₄, hn₄, hc₄, hd₄⟩ := denote_some_inv hf₁
          rw [hn₄]
          cases n₄ with
          | const c us =>
            have hxc := Option.some.inj hd₄
            subst hxc
            dsimp only
            rw [mkFEnv_find?]
            have hws : WScoped d xs₁ ∧ WScoped d xs₂ := by
              simp only [WScoped] at hwa
              exact ⟨hwa.1.2, hwa.2⟩
            cases hfc : env.find? c with
            | none => exact SimAt.pure hs rfl
            | some ci =>
              cases ci with
              | ctorInfo cvm nP nF =>
                match nP, nF with
                | 2, 2 =>
                  refine SimAt.bind (ih.infer hs hdenb hwb)
                    (fun s₁' tb tbx hs₁' hext₁ hP => ?_)
                  obtain ⟨htbd, hwtb⟩ := hP
                  refine SimAt.bind (ih.whnf hs₁' htbd hwtb)
                    (fun s₂' wtb wtbx hs₂' hext₂ hP₂ => ?_)
                  obtain ⟨hwtbd, hwwtb⟩ := hP₂
                  refine SimAt.view ?_
                  obtain ⟨m₀, hm₀, hcm₀, hdm₀⟩ := denote_some_inv hwtbd
                  rw [hm₀]
                  cases m₀ with
                  | app g₂ B =>
                    rw [denoteNode, Option.bind_eq_some_iff] at hdm₀
                    obtain ⟨xg₂, hg₂, hdm₀⟩ := hdm₀
                    rw [Option.map_eq_some_iff] at hdm₀
                    obtain ⟨xB, hB, hdm₀⟩ := hdm₀
                    subst hdm₀
                    refine SimAt.view ?_
                    obtain ⟨m₁, hm₁, hcm₁, hdm₁⟩ := denote_some_inv hg₂
                    rw [hm₁]
                    cases m₁ with
                    | app g₁ A =>
                      rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
                      obtain ⟨xg₁, hg₁, hdm₁⟩ := hdm₁
                      rw [Option.map_eq_some_iff] at hdm₁
                      obtain ⟨xA, hA, hdm₁⟩ := hdm₁
                      subst hdm₁
                      refine SimAt.view ?_
                      obtain ⟨m₂, hm₂, hcm₂, hdm₂⟩ := denote_some_inv hg₁
                      rw [hm₂]
                      cases m₂ with
                      | const c' us' =>
                        have hxc' := Option.some.inj hdm₂
                        subst hxc'
                        dsimp only
                        rw [mkFEnv_find?, mkFEnv_find?]
                        cases hfc' : env.find? c' with
                        | none => exact SimAt.pure hs₂' rfl
                        | some ci' =>
                          cases ci' with
                          | indInfo cvI capsI =>
                            dsimp only
                            cases hfr : env.find? (c'.str "rec") with
                            | none => exact SimAt.pure hs₂' rfl
                            | some cir =>
                              cases cir with
                              | recInfo cvr mI rP rules =>
                                match rules with
                                | [] => exact SimAt.pure hs₂' rfl
                                | [rr] =>
                                  dsimp only
                                  split
                                  · refine SimAt.bind
                                      (SimAt.liftFueled _ _ hs₂')
                                      (fun s₃' ok ok' hs₃' hext₃ hPok => ?_)
                                    obtain rfl : ok = ok' := hPok
                                    cases ok with
                                    | false =>
                                      simp only [Bool.false_eq_true,
                                        ↓reduceIte]
                                      exact SimAt.pure hs₃' rfl
                                    | true =>
                                      simp only [↓reduceIte]
                                      have hext₀₃ :=
                                        (hext₁.trans hext₂).trans hext₃
                                      have hp₀d : denoteNode s₃'.store.denote
                                          (.proj c' 0 j)
                                          = some (.proj c' 0 b) := by
                                        rw [denoteNode,
                                          denote_mono hext₀₃ hdenb]
                                        rfl
                                      refine SimAt.bind_left
                                        (internI_eff hs₃' hp₀d)
                                        (fun s₄' p₀ hs₄' hext₄ hQ₀ => ?_)
                                      refine SimAt.bind (ih.defeq hs₄'
                                        (denote_mono (hext₀₃.trans hext₄)
                                          hs₁d) hQ₀ hws.1 ?_)
                                        (fun s₅' r₁ r₁' hs₅' hext₅
                                          hPr₁ => ?_)
                                      · show WScoped d (.proj c' 0 b)
                                        simp only [WScoped]
                                        exact hwb
                                      obtain rfl : r₁ = r₁' := hPr₁
                                      cases r₁ with
                                      | false =>
                                        simp only [Bool.false_eq_true,
                                          ↓reduceIte]
                                        exact SimAt.pure hs₅' rfl
                                      | true =>
                                        simp only [↓reduceIte]
                                        have hp₁d :
                                            denoteNode s₅'.store.denote
                                            (.proj c' 1 j)
                                            = some (.proj c' 1 b) := by
                                          rw [denoteNode, denote_mono
                                            ((hext₀₃.trans hext₄).trans
                                              hext₅) hdenb]
                                          rfl
                                        refine SimAt.bind_left
                                          (internI_eff hs₅' hp₁d)
                                          (fun s₆' p₁ hs₆' hext₆ hQ₁ => ?_)
                                        refine ih.defeq hs₆'
                                          (denote_mono
                                            (((hext₀₃.trans hext₄).trans
                                              hext₅).trans hext₆) hs₂d)
                                          hQ₁ hws.2 ?_
                                        show WScoped d (.proj c' 1 b)
                                        simp only [WScoped]
                                        exact hwb
                                  · exact SimAt.pure hs₂' rfl
                                | _ :: _ :: _ => exact SimAt.pure hs₂' rfl
                              | axiomInfo cv => exact SimAt.pure hs₂' rfl
                              | defnInfo cv v h =>
                                exact SimAt.pure hs₂' rfl
                              | thmInfo cv v => exact SimAt.pure hs₂' rfl
                              | indInfo cv caps =>
                                exact SimAt.pure hs₂' rfl
                              | ctorInfo cv nP' nF' =>
                                exact SimAt.pure hs₂' rfl
                              | projInfo entry => exact SimAt.pure hs₂' rfl
                          | axiomInfo cv => exact SimAt.pure hs₂' rfl
                          | defnInfo cv v h => exact SimAt.pure hs₂' rfl
                          | thmInfo cv v => exact SimAt.pure hs₂' rfl
                          | ctorInfo cv nP' nF' =>
                            exact SimAt.pure hs₂' rfl
                          | recInfo cv mI rP rules =>
                            exact SimAt.pure hs₂' rfl
                          | projInfo entry => exact SimAt.pure hs₂' rfl
                      | bvar k => invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | sort u => invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | lit l => invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | fvar idx nm t =>
                        invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | app g₀ a₀ =>
                        invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | lam nm t b' m =>
                        invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | forallE nm t b' m =>
                        invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | letE nm t v b' =>
                        invert_node hdm₂; exact SimAt.pure hs₂' rfl
                      | proj s' j' e' =>
                        invert_node hdm₂; exact SimAt.pure hs₂' rfl
                    | bvar k => invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | sort u => invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | const nm us'' =>
                      invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | lit l => invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | fvar idx nm t =>
                      invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | lam nm t b' m =>
                      invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | forallE nm t b' m =>
                      invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | letE nm t v b' =>
                      invert_node hdm₁; exact SimAt.pure hs₂' rfl
                    | proj s' j' e' =>
                      invert_node hdm₁; exact SimAt.pure hs₂' rfl
                  | bvar k => invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | sort u => invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | const nm us'' =>
                    invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | lit l => invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | fvar idx nm t =>
                    invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | lam nm t b' m =>
                    invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | forallE nm t b' m =>
                    invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | letE nm t v b' =>
                    invert_node hdm₀; exact SimAt.pure hs₂' rfl
                  | proj s' j' e' =>
                    invert_node hdm₀; exact SimAt.pure hs₂' rfl
                | 0, _ => exact SimAt.pure hs rfl
                | 1, _ => exact SimAt.pure hs rfl
                | Nat.succ (Nat.succ (Nat.succ _)), _ =>
                  exact SimAt.pure hs rfl
                | 2, 0 => exact SimAt.pure hs rfl
                | 2, 1 => exact SimAt.pure hs rfl
                | 2, Nat.succ (Nat.succ (Nat.succ _)) =>
                  exact SimAt.pure hs rfl
              | axiomInfo cv => exact SimAt.pure hs rfl
              | defnInfo cv v h => exact SimAt.pure hs rfl
              | thmInfo cv v => exact SimAt.pure hs rfl
              | indInfo cv caps => exact SimAt.pure hs rfl
              | recInfo cv mI rP rules => exact SimAt.pure hs rfl
              | projInfo entry => exact SimAt.pure hs rfl
          | bvar k => invert_node hd₄; exact SimAt.pure hs rfl
          | sort u => invert_node hd₄; exact SimAt.pure hs rfl
          | lit l => invert_node hd₄; exact SimAt.pure hs rfl
          | fvar idx nm t => invert_node hd₄; exact SimAt.pure hs rfl
          | app f₀ a₀ => invert_node hd₄; exact SimAt.pure hs rfl
          | lam nm t b' m => invert_node hd₄; exact SimAt.pure hs rfl
          | forallE nm t b' m => invert_node hd₄; exact SimAt.pure hs rfl
          | letE nm t v b' => invert_node hd₄; exact SimAt.pure hs rfl
          | proj s' j' e' => invert_node hd₄; exact SimAt.pure hs rfl
        | bvar k => invert_node hd₃; exact SimAt.pure hs rfl
        | sort u => invert_node hd₃; exact SimAt.pure hs rfl
        | const nm us => invert_node hd₃; exact SimAt.pure hs rfl
        | lit l => invert_node hd₃; exact SimAt.pure hs rfl
        | fvar idx nm t => invert_node hd₃; exact SimAt.pure hs rfl
        | lam nm t b' m => invert_node hd₃; exact SimAt.pure hs rfl
        | forallE nm t b' m => invert_node hd₃; exact SimAt.pure hs rfl
        | letE nm t v b' => invert_node hd₃; exact SimAt.pure hs rfl
        | proj s' j' e' => invert_node hd₃; exact SimAt.pure hs rfl
      | bvar k => invert_node hd₂; exact SimAt.pure hs rfl
      | sort u => invert_node hd₂; exact SimAt.pure hs rfl
      | const nm us => invert_node hd₂; exact SimAt.pure hs rfl
      | lit l => invert_node hd₂; exact SimAt.pure hs rfl
      | fvar idx nm t => invert_node hd₂; exact SimAt.pure hs rfl
      | lam nm t b' m => invert_node hd₂; exact SimAt.pure hs rfl
      | forallE nm t b' m => invert_node hd₂; exact SimAt.pure hs rfl
      | letE nm t v b' => invert_node hd₂; exact SimAt.pure hs rfl
      | proj s' j' e' => invert_node hd₂; exact SimAt.pure hs rfl
    | bvar k => invert_node hd₁; exact SimAt.pure hs rfl
    | sort u => invert_node hd₁; exact SimAt.pure hs rfl
    | const nm us => invert_node hd₁; exact SimAt.pure hs rfl
    | lit l => invert_node hd₁; exact SimAt.pure hs rfl
    | fvar idx nm t => invert_node hd₁; exact SimAt.pure hs rfl
    | lam nm t b' m => invert_node hd₁; exact SimAt.pure hs rfl
    | forallE nm t b' m => invert_node hd₁; exact SimAt.pure hs rfl
    | letE nm t v b' => invert_node hd₁; exact SimAt.pure hs rfl
    | proj s' j' e' => invert_node hd₁; exact SimAt.pure hs rfl
  | bvar k => invert_node hd₀; exact SimAt.pure hs rfl
  | sort u => invert_node hd₀; exact SimAt.pure hs rfl
  | const nm us => invert_node hd₀; exact SimAt.pure hs rfl
  | lit l => invert_node hd₀; exact SimAt.pure hs rfl
  | fvar idx nm t => invert_node hd₀; exact SimAt.pure hs rfl
  | lam nm t b' m => invert_node hd₀; exact SimAt.pure hs rfl
  | forallE nm t b' m => invert_node hd₀; exact SimAt.pure hs rfl
  | letE nm t v b' => invert_node hd₀; exact SimAt.pure hs rfl
  | proj s' j' e' => invert_node hd₀; exact SimAt.pure hs rfl

end Walks3

section Walks4

variable {env : Env} {f : Nat}

/-- The interned projection-application spine denotes the spec's
mapped list. -/
theorem projAppsI_eff (T : Name) (us' : List Level) :
    ∀ (l : List Nat) {s₀ : IState}, ISOK env s₀ →
      ∀ {targs : List EIdx} {xs : List Expr} {b : EIdx} {xb : Expr},
      DenL s₀.store targs xs → s₀.store.denote b = some xb →
      IEff env s₀ (fun s rs => DenL s.store rs
          (l.map fun i => Expr.mkAppN (.const (projFnName T i) us')
            (xs ++ [xb])))
        (projAppsI T us' targs b l)
  | [], s₀, hs, targs, xs, b, xb, htargs, hb => by
    exact IEff.pure hs trivial
  | i :: rest, s₀, hs, targs, xs, b, xb, htargs, hb => by
    show IEff env s₀ _
      (internI (.const (projFnName T i) us') >>= fun h =>
        mkAppNM h (targs ++ [b]) >>= fun r =>
        projAppsI T us' targs b rest >>= fun rs =>
        pure (r :: rs))
    have hcn : denoteNode s₀.store.denote (.const (projFnName T i) us')
        = some (.const (projFnName T i) us') := rfl
    refine IEff.bind (internI_eff hs hcn) (fun s₁ h hs₁ hext₁ hQh => ?_)
    refine IEff.bind (mkAppNM_eff hs₁ hQh
      ((htargs.mono hext₁).append (DenL.cons (denote_mono hext₁ hb) DenL.nil)))
      (fun s₂ r hs₂ hext₂ hQr => ?_)
    refine IEff.bind (projAppsI_eff T us' rest hs₂
      (htargs.mono (hext₁.trans hext₂))
      (denote_mono (hext₁.trans hext₂) hb))
      (fun s₃ rs hs₃ hext₃ hQrs => ?_)
    exact IEff.pure hs₃ ⟨denote_mono hext₃ hQr, hQrs⟩

theorem structEtaProjCertsI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} (T : Name) (us' : List Level) (lpsT : List Name) :
    ∀ (idxs : List Nat) {s₀ : IState}, ISOK env s₀ →
      ∀ {targs : List EIdx} {xs : List Expr} {b : EIdx} {xb : Expr},
      DenL s₀.store targs xs → s₀.store.denote b = some xb →
      (∀ x ∈ xs, WScoped d x) → WScoped d xb →
      SimAt env s₀ RelV
        (structEtaProjCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d
          T us' targs b lpsT idxs)
        (structEtaProjCerts (fueledFns env) env d T us' xs xb lpsT idxs)
  | [], s₀, hs, targs, xs, b, xb, htargs, hb, hwxs, hwxb => by
    exact SimAt.pure hs rfl
  | i :: rest, s₀, hs, targs, xs, b, xb, htargs, hb, hwxs, hwxb => by
    show SimAt env s₀ RelV
      (match (mkFEnv env).find? (projFnName T i) with
      | some (.recInfo cvp _ _ _) =>
        if cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (targs.length + 1)).isSome = true then
          constTyAtM (mkFEnv env) (projFnName T i) us' >>= fun pty =>
          iotaCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d pty
              (targs ++ [b]) >>= fun r =>
          if r then
            structEtaProjCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d
              T us' targs b lpsT rest
          else pure false
        else pure false
      | _ => pure false)
      (match env.find? (projFnName T i) with
      | some (.recInfo cvp _ _ _) =>
        if cvp.levelParams = lpsT ∧
            (cvp.type.stripPis (xs.length + 1)).isSome = true then
          iotaCerts (fueledFns env) env d
              (cvp.type.instantiateLevelParams cvp.levelParams us')
              (xs ++ [xb]) >>= fun r =>
          if r then
            structEtaProjCerts (fueledFns env) env d T us' xs xb lpsT rest
          else pure false
        else pure false
      | _ => pure false)
    rw [mkFEnv_find?, htargs.length_eq]
    cases hf : env.find? (projFnName T i) with
    | none => exact SimAt.pure hs rfl
    | some ci =>
      cases ci with
      | recInfo cvp mI rP rules =>
        dsimp only
        split
        · refine SimAt.bind_left (constTyAtM_eff hs hf)
            (fun s₁ pty hs₁ hext₁ hQty => ?_)
          have htyw : WScoped d
              (cvp.type.instantiateLevelParams cvp.levelParams us') := by
            obtain ⟨htf, -⟩ := henv _ (find?_mem hf)
            exact wscoped_instLevels_of_not_hasFvar htf _ _
          have hargs : ∀ x ∈ xs ++ [xb], WScoped d x := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hwxs x hx
            · rcases List.mem_singleton.mp hx with rfl
              exact hwxb
          refine SimAt.bind (iotaCertsI_sim ih hs₁ hQty htyw
            ((htargs.mono hext₁).append
              (DenL.cons (denote_mono hext₁ hb) DenL.nil)) hargs)
            (fun s₂ r r' hs₂ hext₂ hPr => ?_)
          obtain rfl : r = r' := hPr
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCertsI_sim ih henv T us' lpsT rest hs₂
              (htargs.mono (hext₁.trans hext₂))
              (denote_mono (hext₁.trans hext₂) hb) hwxs hwxb
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact SimAt.pure hs₂ rfl
        · exact SimAt.pure hs rfl
      | axiomInfo cv => exact SimAt.pure hs rfl
      | defnInfo cv v h => exact SimAt.pure hs rfl
      | thmInfo cv v => exact SimAt.pure hs rfl
      | indInfo cv caps => exact SimAt.pure hs rfl
      | ctorInfo cv nP nF => exact SimAt.pure hs rfl
      | projInfo entry => exact SimAt.pure hs rfl

private theorem structEtaCertWith_unfold (env : Env) (d : Nat)
    (a b wtb : Expr) :
    structEtaCertWith (fueledFns env) env d a b wtb =
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
                  iotaCerts (fueledFns env) env d
                      (cvT.type.instantiateLevelParams cvT.levelParams us')
                      wtb.getAppArgs >>= fun r₁ =>
                  if r₁ then
                    structEtaProjCerts (fueledFns env) env d T us'
                        wtb.getAppArgs b cvT.levelParams
                        (List.range cnF) >>= fun r₂ =>
                    if r₂ then
                      defEqList (fueledFns env) env d
                          (a.getAppArgs.take cnP) wtb.getAppArgs >>=
                        fun r₃ =>
                      if r₃ then
                        defEqList (fueledFns env) env d
                          (a.getAppArgs.drop cnP)
                          ((List.range cnF).map fun i =>
                            Expr.mkAppN (.const (projFnName T i) us')
                              (wtb.getAppArgs ++ [b]))
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

theorem structEtaCertWithI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i j w : EIdx} {a b wtb : Expr} {s₀ : IState}
    (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hdenw : s₀.store.denote w = some wtb)
    (hwa : WScoped d a) (hwb : WScoped d b) (hwwtb : WScoped d wtb) :
    SimAt env s₀ RelV
      (structEtaCertWithI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j w)
      (structEtaCertWith (fueledFns env) env d a b wtb) := by
  show SimAt env s₀ RelV
    (Setlec.withStore (fun st => st.nodes[st.getAppFnI i]?) >>= fun n =>
      match n with
      | some (.const c us) =>
        match (mkFEnv env).find? c with
        | some (.ctorInfo cvc cnP cnF) =>
          Setlec.withStore (·.getAppArgsI i) >>= fun aargs =>
          if aargs.length = cnP + cnF then
            Setlec.withStore (fun st => st.nodes[st.getAppFnI w]?) >>=
              fun n' =>
            match n' with
            | some (.const T us') =>
              match (mkFEnv env).find? T with
              | some (.indInfo cvT caps) =>
                Setlec.withStore (·.getAppArgsI w) >>= fun targs =>
                if caps.eta = true ∧ caps.etaCtor = c ∧
                    caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                    reservedBasisNames.contains T = false ∧
                    reservedBasisNames.contains c = false ∧
                    targs.length = cnP ∧
                    us'.length = cvT.levelParams.length ∧
                    cvc.levelParams = cvT.levelParams ∧
                    (cvT.type.stripPis cnP).isSome = true then
                  liftFueled "level comparison"
                    (Level.isEquivList us us') >>= fun ok =>
                  if ok then
                    constTyAtM (mkFEnv env) T us' >>= fun tyT =>
                    iotaCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d
                        tyT targs >>= fun r₁ =>
                    if r₁ then
                      structEtaProjCertsI (coreKnotI (mkFEnv env) f)
                          (mkFEnv env) d T us' targs j cvT.levelParams
                          (List.range cnF) >>= fun r₂ =>
                      if r₂ then
                        defEqListI (coreKnotI (mkFEnv env) f) (mkFEnv env)
                            d (aargs.take cnP) targs >>= fun r₃ =>
                        if r₃ then
                          projAppsI T us' targs j (List.range cnF) >>=
                            fun projs =>
                          defEqListI (coreKnotI (mkFEnv env) f)
                            (mkFEnv env) d (aargs.drop cnP) projs
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
    (structEtaCertWith (fueledFns env) env d a b wtb)
  rw [structEtaCertWith_unfold]
  refine SimAt.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hs.wf hdena)
  rw [hn]
  cases n with
  | const c us =>
    rw [← Option.some.inj hd]
    dsimp only
    rw [mkFEnv_find?]
    cases hfc : env.find? c with
    | none => exact SimAt.pure hs rfl
    | some ci =>
      cases ci with
      | ctorInfo cvc cnP cnF =>
        dsimp only
        refine SimAt.withStore ?_
        have haargs := getAppArgsI_spec hs.wf hdena
        rw [haargs.length_eq]
        split
        · refine SimAt.withStore ?_
          obtain ⟨n', hn', hc', hd'⟩ :=
            denote_some_inv (getAppFnI_spec hs.wf hdenw)
          rw [hn']
          cases n' with
          | const T us' =>
            rw [← Option.some.inj hd']
            dsimp only
            rw [mkFEnv_find?]
            cases hfT : env.find? T with
            | none => exact SimAt.pure hs rfl
            | some ciT =>
              cases ciT with
              | indInfo cvT caps =>
                dsimp only
                refine SimAt.withStore ?_
                have htargs := getAppArgsI_spec hs.wf hdenw
                rw [htargs.length_eq]
                split
                · refine SimAt.bind (SimAt.liftFueled _ _ hs)
                    (fun s₁ ok ok' hs₁ hext₁ hPok => ?_)
                  obtain rfl : ok = ok' := hPok
                  cases ok with
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    exact SimAt.pure hs₁ rfl
                  | true =>
                    simp only [↓reduceIte]
                    refine SimAt.bind_left (constTyAtM_eff hs₁ hfT)
                      (fun s₂ tyT hs₂ hext₂ hQty => ?_)
                    have htyw : WScoped d (cvT.type.instantiateLevelParams
                        cvT.levelParams us') := by
                      obtain ⟨htf, -⟩ := henv _ (find?_mem hfT)
                      exact wscoped_instLevels_of_not_hasFvar htf _ _
                    refine SimAt.bind (iotaCertsI_sim ih hs₂ hQty htyw
                      (htargs.mono (hext₁.trans hext₂))
                      hwwtb.getAppArgs)
                      (fun s₃ r₁ r₁' hs₃ hext₃ hPr₁ => ?_)
                    obtain rfl : r₁ = r₁' := hPr₁
                    cases r₁ with
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact SimAt.pure hs₃ rfl
                    | true =>
                      simp only [↓reduceIte]
                      have hext₀₃ := (hext₁.trans hext₂).trans hext₃
                      refine SimAt.bind (structEtaProjCertsI_sim ih henv
                        T us' cvT.levelParams (List.range cnF) hs₃
                        (htargs.mono hext₀₃)
                        (denote_mono hext₀₃ hdenb)
                        hwwtb.getAppArgs hwb)
                        (fun s₄ r₂ r₂' hs₄ hext₄ hPr₂ => ?_)
                      obtain rfl : r₂ = r₂' := hPr₂
                      cases r₂ with
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        exact SimAt.pure hs₄ rfl
                      | true =>
                        simp only [↓reduceIte]
                        have hext₀₄ := hext₀₃.trans hext₄
                        refine SimAt.bind (defEqListI_sim ih hs₄
                          ((haargs.mono hext₀₄).take cnP)
                          (htargs.mono hext₀₄)
                          (fun x hx => hwa.getAppArgs x
                            (List.mem_of_mem_take hx))
                          hwwtb.getAppArgs)
                          (fun s₅ r₃ r₃' hs₅ hext₅ hPr₃ => ?_)
                        obtain rfl : r₃ = r₃' := hPr₃
                        cases r₃ with
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimAt.pure hs₅ rfl
                        | true =>
                          simp only [↓reduceIte]
                          have hext₀₅ := hext₀₄.trans hext₅
                          refine SimAt.bind_left (projAppsI_eff T us'
                            (List.range cnF) hs₅
                            (htargs.mono hext₀₅)
                            (denote_mono hext₀₅ hdenb))
                            (fun s₆ projs hs₆ hext₆ hQp => ?_)
                          refine defEqListI_sim ih hs₆
                            ((haargs.mono (hext₀₅.trans hext₆)).drop cnP)
                            hQp
                            (fun x hx => hwa.getAppArgs x
                              (List.mem_of_mem_drop hx)) ?_
                          intro x hx
                          obtain ⟨i', -, rfl⟩ := List.mem_map.mp hx
                          refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
                          intro y hy
                          rcases List.mem_append.mp hy with hy | hy
                          · exact hwwtb.getAppArgs y hy
                          · rcases List.mem_singleton.mp hy with rfl
                            exact hwb
                · exact SimAt.pure hs rfl
              | axiomInfo cv => exact SimAt.pure hs rfl
              | defnInfo cv v h => exact SimAt.pure hs rfl
              | thmInfo cv v => exact SimAt.pure hs rfl
              | ctorInfo cv nP' nF' => exact SimAt.pure hs rfl
              | recInfo cv mI rP rules => exact SimAt.pure hs rfl
              | projInfo entry => exact SimAt.pure hs rfl
          | bvar k => rw [← Option.some.inj hd']; exact SimAt.pure hs rfl
          | sort u => rw [← Option.some.inj hd']; exact SimAt.pure hs rfl
          | lit l => rw [← Option.some.inj hd']; exact SimAt.pure hs rfl
          | fvar idx nm t =>
            rw [denoteNode, Option.map_eq_some_iff] at hd'
            obtain ⟨t', _, hd'⟩ := hd'
            rw [← hd']; exact SimAt.pure hs rfl
          | app f' a' =>
            rw [denoteNode, Option.bind_eq_some_iff] at hd'
            obtain ⟨ef, _, hd'⟩ := hd'
            rw [Option.map_eq_some_iff] at hd'
            obtain ⟨ea, _, hd'⟩ := hd'
            rw [← hd']; exact SimAt.pure hs rfl
          | lam nm t b' m =>
            rw [denoteNode, Option.bind_eq_some_iff] at hd'
            obtain ⟨et, _, hd'⟩ := hd'
            rw [Option.map_eq_some_iff] at hd'
            obtain ⟨eb, _, hd'⟩ := hd'
            rw [← hd']; exact SimAt.pure hs rfl
          | forallE nm t b' m =>
            rw [denoteNode, Option.bind_eq_some_iff] at hd'
            obtain ⟨et, _, hd'⟩ := hd'
            rw [Option.map_eq_some_iff] at hd'
            obtain ⟨eb, _, hd'⟩ := hd'
            rw [← hd']; exact SimAt.pure hs rfl
          | letE nm t v b' =>
            rw [denoteNode, Option.bind_eq_some_iff] at hd'
            obtain ⟨et, _, hd'⟩ := hd'
            rw [Option.bind_eq_some_iff] at hd'
            obtain ⟨ev, _, hd'⟩ := hd'
            rw [Option.map_eq_some_iff] at hd'
            obtain ⟨eb, _, hd'⟩ := hd'
            rw [← hd']; exact SimAt.pure hs rfl
          | proj s' j' e' =>
            rw [denoteNode, Option.map_eq_some_iff] at hd'
            obtain ⟨ee, _, hd'⟩ := hd'
            rw [← hd']; exact SimAt.pure hs rfl
        · exact SimAt.pure hs rfl
      | axiomInfo cv => exact SimAt.pure hs rfl
      | defnInfo cv v h => exact SimAt.pure hs rfl
      | thmInfo cv v => exact SimAt.pure hs rfl
      | indInfo cv caps => exact SimAt.pure hs rfl
      | recInfo cv mI rP rules => exact SimAt.pure hs rfl
      | projInfo entry => exact SimAt.pure hs rfl
  | bvar k => rw [← Option.some.inj hd]; exact SimAt.pure hs rfl
  | sort u => rw [← Option.some.inj hd]; exact SimAt.pure hs rfl
  | lit l => rw [← Option.some.inj hd]; exact SimAt.pure hs rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs rfl
  | app f' a' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs rfl
  | lam nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs rfl
  | forallE nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs rfl
  | letE nm t v b' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs rfl
  | proj s' j' e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [← hd]; exact SimAt.pure hs rfl

theorem structEtaCertI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i j : EIdx} {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (structEtaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (structEtaCert (fueledFns env) env d a b) := by
  show SimAt env s₀ RelV
    ((coreKnotI (mkFEnv env) f).infer d j >>= fun tb =>
      (coreKnotI (mkFEnv env) f).whnf d tb >>= fun wtb =>
      structEtaCertWithI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j wtb)
    ((fueledFns env).infer d b >>= fun tb =>
      (fueledFns env).whnf d tb >>= fun wtb =>
      structEtaCertWith (fueledFns env) env d a b wtb)
  refine SimAt.bind (ih.infer hs hdenb hwb)
    (fun s₁ tb tbx hs₁ hext₁ hP => ?_)
  obtain ⟨htbd, hwtb⟩ := hP
  refine SimAt.bind (ih.whnf hs₁ htbd hwtb)
    (fun s₂ wtb wtbx hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hwtbd, hwwtb⟩ := hP₂
  exact structEtaCertWithI_sim ih henv hs₂
    (denote_mono (hext₁.trans hext₂) hdena)
    (denote_mono (hext₁.trans hext₂) hdenb) hwtbd hwa hwb hwwtb

theorem stuckIrrelI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i j : EIdx} {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (stuckIrrelI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (stuckIrrel (fueledFns env) env d a b) := by
  show SimAt env s₀ RelV
    (pairEtaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j >>=
      fun r₁ =>
      if r₁ then pure true else
      pairEtaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d j i >>=
        fun r₂ =>
      if r₂ then pure true else
      structEtaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₃ =>
      if r₃ then pure true else
      structEtaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d j i >>=
        fun r₄ =>
      if r₄ then pure true else
      structUnitCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j >>=
        fun r₅ =>
      if r₅ then pure true else
      proofIrrelI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
    (pairEtaCert (fueledFns env) env d a b >>= fun r₁ =>
      if r₁ then pure true else
      pairEtaCert (fueledFns env) env d b a >>= fun r₂ =>
      if r₂ then pure true else
      structEtaCert (fueledFns env) env d a b >>= fun r₃ =>
      if r₃ then pure true else
      structEtaCert (fueledFns env) env d b a >>= fun r₄ =>
      if r₄ then pure true else
      structUnitCert (fueledFns env) env d a b >>= fun r₅ =>
      if r₅ then pure true else
      proofIrrel (fueledFns env) env d a b)
  refine SimAt.bind (pairEtaCertI_sim ih hs hdena hdenb hwa hwb)
    (fun s₁ r₁ r₁' hs₁ hext₁ hP₁ => ?_)
  obtain rfl : r₁ = r₁' := hP₁
  cases r₁ with
  | true => simp only [↓reduceIte]; exact SimAt.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimAt.bind (pairEtaCertI_sim ih hs₁
      (denote_mono hext₁ hdenb) (denote_mono hext₁ hdena) hwb hwa)
      (fun s₂ r₂ r₂' hs₂ hext₂ hP₂ => ?_)
    obtain rfl : r₂ = r₂' := hP₂
    cases r₂ with
    | true => simp only [↓reduceIte]; exact SimAt.pure hs₂ rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hext₀₂ := hext₁.trans hext₂
      refine SimAt.bind (structEtaCertI_sim ih henv hs₂
        (denote_mono hext₀₂ hdena) (denote_mono hext₀₂ hdenb) hwa hwb)
        (fun s₃ r₃ r₃' hs₃ hext₃ hP₃ => ?_)
      obtain rfl : r₃ = r₃' := hP₃
      cases r₃ with
      | true => simp only [↓reduceIte]; exact SimAt.pure hs₃ rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hext₀₃ := hext₀₂.trans hext₃
        refine SimAt.bind (structEtaCertI_sim ih henv hs₃
          (denote_mono hext₀₃ hdenb) (denote_mono hext₀₃ hdena) hwb hwa)
          (fun s₄ r₄ r₄' hs₄ hext₄ hP₄ => ?_)
        obtain rfl : r₄ = r₄' := hP₄
        cases r₄ with
        | true => simp only [↓reduceIte]; exact SimAt.pure hs₄ rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hext₀₄ := hext₀₃.trans hext₄
          refine SimAt.bind (structUnitCertI_sim ih henv hs₄
            (denote_mono hext₀₄ hdena) (denote_mono hext₀₄ hdenb)
            hwa hwb)
            (fun s₅ r₅ r₅' hs₅ hext₅ hP₅ => ?_)
          obtain rfl : r₅ = r₅' := hP₅
          cases r₅ with
          | true => simp only [↓reduceIte]; exact SimAt.pure hs₅ rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hext₀₅ := hext₀₄.trans hext₅
            exact proofIrrelI_sim ih hs₅
              (denote_mono hext₀₅ hdena) (denote_mono hext₀₅ hdenb)
              hwa hwb

end Walks4

end Setlec
