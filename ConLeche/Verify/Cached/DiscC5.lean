module

public import ConLeche.Verify.Cached.DiscC4

public section

/-!
# Cached body walks, part 5: definitional equality (task #163)

The simulation walks for the definitional-equality pieces
(`quickDefEqI`, `defeqOffsetI`, `tryUnfoldProjAppI`, `lazyDeltaStepI`,
the two lazy-delta loops, `defeqProjPairI`, `defeqStuckI`) and
`defeqBodyI` (`ConLeche/Cached/CoreC.lean`).  A decided `Expr` comparison on the
cached side is the spec's structural comparison (`beq_transferC`): the
two sides are the same terms, with no store in sight.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche.Expr

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- Decided `Expr` equality decides expression equality on the field
invariant. -/
private theorem beq_transferC {i j : Expr} {a b : Expr}
    (ha : RelC i a) (hb : RelC j b) : (i == j) = (a == b) := by
  obtain rfl := ha
  obtain rfl := hb
  rfl

/-- The one-sided-λ (right) stuck arm (the cached representation
stores `Name`s and `BinderMeta`s directly). -/
private theorem defeqC_etaR_arm (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {a' b' t₂ b₂ : Expr} {a'x ty₂x body₂x : Expr}
    {bm₂ : BinderMeta} {s₀ : CState} (hs : CSOK mode env s₀)
    (haS : RelC a' a'x)
    (hty₂ : RelC t₂ ty₂x)
    (hbody₂ : RelC b₂ body₂x)
    (hbS : RelC b' (.lam ty₂x body₂x bm₂))
    (hwa' : Expr.WScoped d a'x)
    (hwb' : Expr.WScoped d (Expr.lam ty₂x body₂x bm₂)) :
    SimC mode env s₀ RelVC
      (etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          t₂ b₂ bm₂ a' >>= fun r =>
        if r then pure true
        else stuckIrrelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a' b')
      (etaCert mode (fueledFns mode env) env d ty₂x body₂x bm₂
          a'x >>= fun r =>
        if r then pure true
        else stuckIrrel mode (fueledFns mode env) env d a'x
          (.lam ty₂x body₂x bm₂)) := by
  have h2 : Expr.WScoped d ty₂x ∧ Expr.WScoped d body₂x := by
    simpa only [Expr.WScoped] using hwb'
  refine SimC.bind (etaCertC_sim ih hs hty₂ hbody₂ haS h2.1 h2.2 hwa')
    (fun s₁ r r' hs₁ hP => ?_)
  obtain rfl : r = r' := hP
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact stuckIrrelC_sim hμ ih henv hs₁ haS hbS hwa' hwb'

/-- The one-sided-λ (left) stuck arm. -/
private theorem defeqC_etaL_arm (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {a' b' t₁ b₁ : Expr} {b'x ty₁x body₁x : Expr}
    {bm₁ : BinderMeta} {s₀ : CState} (hs : CSOK mode env s₀)
    (haS : RelC a' (.lam ty₁x body₁x bm₁))
    (hty₁ : RelC t₁ ty₁x)
    (hbody₁ : RelC b₁ body₁x)
    (hbS : RelC b' b'x)
    (hwa' : Expr.WScoped d (Expr.lam ty₁x body₁x bm₁))
    (hwb' : Expr.WScoped d b'x) :
    SimC mode env s₀ RelVC
      (etaCertI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
          t₁ b₁ bm₁ b' >>= fun r =>
        if r then pure true
        else stuckIrrelI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a' b')
      (etaCert mode (fueledFns mode env) env d ty₁x body₁x bm₁
          b'x >>= fun r =>
        if r then pure true
        else stuckIrrel mode (fueledFns mode env) env d
          (.lam ty₁x body₁x bm₁) b'x) := by
  have h1 : Expr.WScoped d ty₁x ∧ Expr.WScoped d body₁x := by
    simpa only [Expr.WScoped] using hwa'
  refine SimC.bind (etaCertC_sim ih hs hty₁ hbody₁ hbS h1.1 h1.2 hwb')
    (fun s₁ r r' hs₁ hP => ?_)
  obtain rfl : r = r' := hP
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact stuckIrrelC_sim hμ ih henv hs₁ haS hbS hwa' hwb'

/-- A lazy-delta step's outcome, related: equal, the handed-on pair in
scope. -/
def RelDSC (d : Nat) (s s' : DeltaStep) : Prop :=
  s = s' ∧ (∀ a b, s' = .cont a b → Expr.WScoped d a ∧ Expr.WScoped d b)

/-- The lazy-delta loop's outcome, related: equal, the stuck pair in
scope. -/
def RelLSC (d : Nat) (r r' : LazyRes) : Prop :=
  r = r' ∧ (∀ a b, r' = .unknown a b → Expr.WScoped d a ∧ Expr.WScoped d b)

/-- The binder arms of `quickDefEq` (∀ and λ alike). -/
private theorem quickBinderC (ih : SSimC mode env f)
    {d : Nat} {t₁ b₁ t₂ b₂ : Expr} {m₁ m₂ : BinderMeta} {msg : String}
    {s₆ : CState} (hs₆ : CSOK mode env s₆)
    (h1 : Expr.WScoped d t₁ ∧ Expr.WScoped d b₁)
    (h2 : Expr.WScoped d t₂ ∧ Expr.WScoped d b₂) :
    SimC mode env s₆ RelVC
      (do
        unless ← (coreKnotI mode (mkFEnv env) f).defeq d t₁ t₂ do return some false
        let fv ← pure (Expr.fvar d t₂)
        let o₁ ← inst1M b₁ fv
        let o₂ ← inst1M b₂ fv
        unless ← (coreKnotI mode (mkFEnv env) f).defeq (d + 1) o₁ o₂ do return some false
        if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
          throw (.notImplemented msg)
        pure (some true) : CheckCM (Option Bool))
      (do
        unless ← (fueledFns mode env).defeq d t₁ t₂ do return some false
        unless ← (fueledFns mode env).defeq (d + 1)
            (b₁.instantiate1 (.fvar d t₂))
            (b₂.instantiate1 (.fvar d t₂)) do return some false
        if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
          throw (.notImplemented msg)
        pure (some true) : FueledM (Option Bool)) := by
  refine SimC.bind (ih.defeq hs₆ rfl rfl h1.1 h2.1)
    (fun s₇ r₁ r₁' hs₇ hP₁ => ?_)
  obtain rfl : r₁ = r₁' := hP₁
  cases r₁ with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.pure hs₇ rfl
  | true =>
    simp only [↓reduceIte]
    refine SimC.bind_left
      (pureC_eff hs₇ (x := Expr.fvar d t₂))
      (fun s₈ fv hs₈ hQf => ?_)
    have hQf' : RelC fv (Expr.fvar d t₂) := hQf
    refine SimC.bind_left
      (inst1M_eff hs₈ rfl hQf')
      (fun s₉ ob₁ hs₉ hQo₁ => ?_)
    refine SimC.bind_left
      (inst1M_eff hs₉ rfl hQf')
      (fun s₁₁ ob₂ hs₁₁ hQo₂ => ?_)
    refine SimC.bind (ih.defeq hs₁₁ hQo₁ hQo₂
      (Expr.WScoped.instantiate1 h2.1 0 h1.2)
      (Expr.WScoped.instantiate1 h2.1 0 h2.2))
      (fun s₁₂ r₂ r₂x hs₁₂ hPr₂ => ?_)
    obtain rfl : r₂ = r₂x := hPr₂
    cases r₂ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₁₂ rfl
    | true =>
      simp only [↓reduceIte]
      by_cases hpw : (mode.verifiedChecks && !m₁.pw == m₂.pw) = true
      · simp only [hpw, ↓reduceIte]
        exact SimC.throw_bind
      · simp only [Bool.not_eq_true] at hpw
        simp only [hpw, ↓reduceIte]
        exact SimC.pure hs₁₂ rfl

/-- The easy cases simulate their specification. -/
theorem quickDefEqC_sim (_hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (quickDefEqI mode (coreKnotI mode (mkFEnv env) f) d i j)
      (quickDefEq mode (fueledFns mode env) d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  unfold quickDefEqI quickDefEq
  by_cases hab : (i == j) = true
  · rw [ite_eq_left hab, ite_eq_left hab]
    exact SimC.pure hs rfl
  rw [ite_eq_right hab, ite_eq_right hab]
  cases i <;> cases j <;> (try exact SimC.pure hs rfl)
  case sort.sort u₁ u₂ =>
    refine SimC.bind_left (isEquivLM_eff hs u₁ u₂)
      (fun sE o hsE ho => ?_)
    subst ho
    refine SimC.bind (SimC.liftFueled _ _ hsE)
      (fun s₁ ok ok' hs₁ hP => ?_)
    obtain rfl : ok = ok' := hP
    exact SimC.pure hs₁ rfl
  case forallE.forallE t₁ b₁ m₁ t₂ b₂ m₂ =>
    exact quickBinderC ih hs (by simpa only [Expr.WScoped] using hwa)
      (by simpa only [Expr.WScoped] using hwb)
  case lam.lam t₁ b₁ m₁ t₂ b₂ m₂ =>
    exact quickBinderC ih hs (by simpa only [Expr.WScoped] using hwa)
      (by simpa only [Expr.WScoped] using hwb)

/-- Offsets simulate their specification. -/
theorem defeqOffsetC_sim (ih : SSimC mode env f)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqOffsetI (coreKnotI mode (mkFEnv env) f) d i j)
      (defeqOffset (fueledFns mode env) d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  unfold defeqOffsetI defeqOffset
  by_cases hz : (i.isNatZero && j.isNatZero) = true
  · rw [ite_eq_left hz, ite_eq_left hz]
    exact SimC.pure hs rfl
  rw [ite_eq_right hz, ite_eq_right hz]
  by_cases hl : (i.isLit && j.isLit) = true
  · rw [ite_eq_left hl, ite_eq_left hl]
    exact SimC.pure hs rfl
  rw [ite_eq_right hl, ite_eq_right hl]
  cases hx : i.natPred? <;> cases hy : j.natPred? <;> (try exact SimC.pure hs rfl)
  rename_i x y
  dsimp only
  refine SimC.bind (ih.defeq hs rfl rfl (natPred?_WScoped hx hwa)
    (natPred?_WScoped hy hwb)) (fun s₁ v v' hs₁ hP => ?_)
  obtain rfl : v = v' := hP
  exact SimC.pure hs₁ rfl

/-- `try_unfold_proj_app` simulates its specification. -/
theorem tryUnfoldProjAppC_sim (ih : SSimC mode env f)
    {d : Nat} {i : Expr} {e : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelOC d)
      (tryUnfoldProjAppI (coreKnotI mode (mkFEnv env) f) d i)
      (tryUnfoldProjApp (fueledFns mode env) d e) := by
  obtain rfl := hden
  unfold tryUnfoldProjAppI tryUnfoldProjApp
  by_cases hp : i.headIsProj = true
  · rw [ite_eq_left hp, ite_eq_left hp]
    refine SimC.bind (ih.whnfCore hs rfl hw) (fun s₁ e' e'x hs₁ hP => ?_)
    obtain ⟨rfl, hwe'⟩ := hP
    by_cases he : (e' == i) = true
    · rw [ite_eq_left he, ite_eq_left he]
      exact SimC.pure hs₁ trivial
    · rw [ite_eq_right he, ite_eq_right he]
      exact SimC.pure hs₁ (show RelEC d e' e' from ⟨rfl, hwe'⟩)
  · rw [ite_eq_right hp, ite_eq_right hp]
    exact SimC.pure hs trivial

/-- The end of a step simulates its specification. -/
theorem deltaQuickC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ (RelDSC d)
      (deltaQuickI mode (coreKnotI mode (mkFEnv env) f) d i j)
      (deltaQuick mode (fueledFns mode env) d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  unfold deltaQuickI deltaQuick
  refine SimC.bind (quickDefEqC_sim hμ ih hs rfl rfl hwa hwb)
    (fun s₁ o o' hs₁ hP => ?_)
  obtain rfl : o = o' := hP
  match o with
  | none =>
    exact SimC.pure hs₁ ⟨rfl, fun x y h => by
      cases h
      exact ⟨hwa, hwb⟩⟩
  | some true => exact SimC.pure hs₁ ⟨rfl, fun _ _ h => nomatch h⟩
  | some false => exact SimC.pure hs₁ ⟨rfl, fun _ _ h => nomatch h⟩

/-- One side unfolded and put through the cheap `whnfCore`, then the
step's end. -/
private theorem unfoldQuickLC (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ (RelDSC d)
      (unfoldDefinitionI (mkFEnv env) a >>= fun ua =>
        match ua with
        | some a₂ => do
          let a₃ ← (coreKnotI mode (mkFEnv env) f).whnfCore true d a₂
          deltaQuickI mode (coreKnotI mode (mkFEnv env) f) d a₃ b
        | none => pure .unknown)
      (match unfoldDefinition env a with
        | some a₂ => do
          let a₃ ← (fueledFns mode env).whnfCore true d a₂
          deltaQuick mode (fueledFns mode env) d a₃ b
        | none => pure .unknown) := by
  refine SimC.bind_left (unfoldDefinitionC_eff hs rfl)
    (fun s₁ ua hs₁ hQa => ?_)
  cases hua : unfoldDefinition env a with
  | none =>
    rw [hua] at hQa
    cases ua with
    | some a₂ => exact absurd hQa (by simp [OptEr])
    | none => exact SimC.pure hs₁ ⟨rfl, fun _ _ h => nomatch h⟩
  | some a₂x =>
    rw [hua] at hQa
    cases ua with
    | none => exact absurd hQa (by simp [OptEr])
    | some a₂ =>
      dsimp only
      refine SimC.bind (ih.whnfCore hs₁ hQa (unfoldDefinition_WScoped henv hua hwa))
        (fun s₂ a₃ a₃x hs₂ hP => ?_)
      exact deltaQuickC_sim hμ ih hs₂ hP.1 rfl hP.2 hwb

private theorem unfoldQuickRC (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ (RelDSC d)
      (unfoldDefinitionI (mkFEnv env) b >>= fun ub =>
        match ub with
        | some b₂ => do
          let b₃ ← (coreKnotI mode (mkFEnv env) f).whnfCore true d b₂
          deltaQuickI mode (coreKnotI mode (mkFEnv env) f) d a b₃
        | none => pure .unknown)
      (match unfoldDefinition env b with
        | some b₂ => do
          let b₃ ← (fueledFns mode env).whnfCore true d b₂
          deltaQuick mode (fueledFns mode env) d a b₃
        | none => pure .unknown) := by
  refine SimC.bind_left (unfoldDefinitionC_eff hs rfl)
    (fun s₁ ub hs₁ hQb => ?_)
  cases hub : unfoldDefinition env b with
  | none =>
    rw [hub] at hQb
    cases ub with
    | some b₂ => exact absurd hQb (by simp [OptEr])
    | none => exact SimC.pure hs₁ ⟨rfl, fun _ _ h => nomatch h⟩
  | some b₂x =>
    rw [hub] at hQb
    cases ub with
    | none => exact absurd hQb (by simp [OptEr])
    | some b₂ =>
      dsimp only
      refine SimC.bind (ih.whnfCore hs₁ hQb (unfoldDefinition_WScoped henv hub hwb))
        (fun s₂ b₃ b₃x hs₂ hP => ?_)
      exact deltaQuickC_sim hμ ih hs₂ rfl hP.1 hwa hP.2

/-- One lazy-delta step simulates its specification. -/
theorem lazyDeltaStepC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ (RelDSC d)
      (lazyDeltaStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (lazyDeltaStep mode (fueledFns mode env) env d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  unfold lazyDeltaStepI lazyDeltaStep
  refine SimC.pureB ?_
  refine SimC.pureB ?_
  rw [unfoldableHeadC_spec' rfl, unfoldableHeadC_spec' rfl]
  cases hda : unfoldableHead env i <;> cases hdb : unfoldableHead env j <;> dsimp only
  · exact SimC.pure hs ⟨rfl, fun _ _ h => nomatch h⟩
  · refine SimC.bind (tryUnfoldProjAppC_sim ih hs rfl hwa)
      (fun s₁ o ox hs₁ hPo => ?_)
    cases o with
    | some a₂ =>
      cases ox with
      | none => exact absurd hPo (by simp [RelOC])
      | some a₂x =>
        obtain ⟨ha₂d, hwa₂⟩ := hPo
        exact deltaQuickC_sim hμ ih hs₁ ha₂d rfl hwa₂ hwb
    | none =>
      cases ox with
      | some a₂x => exact absurd hPo (by simp [RelOC])
      | none => exact unfoldQuickRC hμ ih henv hs₁ hwa hwb
  · refine SimC.bind (tryUnfoldProjAppC_sim ih hs rfl hwb)
      (fun s₁ o ox hs₁ hPo => ?_)
    cases o with
    | some b₂ =>
      cases ox with
      | none => exact absurd hPo (by simp [RelOC])
      | some b₂x =>
        obtain ⟨hb₂d, hwb₂⟩ := hPo
        exact deltaQuickC_sim hμ ih hs₁ rfl hb₂d hwa hwb₂
    | none =>
      cases ox with
      | some b₂x => exact absurd hPo (by simp [RelOC])
      | none => exact unfoldQuickLC hμ ih henv hs₁ hwa hwb
  · refine SimC.pureB ?_
    refine SimC.pureB ?_
    rw [headHintC_spec' rfl, headHintC_spec' rfl]
    by_cases hlt₁ : ReducibilityHint.lt (headHint env j) (headHint env i) = true
    · rw [ite_eq_left hlt₁, ite_eq_left hlt₁]
      exact unfoldQuickLC hμ ih henv hs hwa hwb
    rw [ite_eq_right hlt₁, ite_eq_right hlt₁]
    by_cases hlt₂ : ReducibilityHint.lt (headHint env i) (headHint env j) = true
    · rw [ite_eq_left hlt₂, ite_eq_left hlt₂]
      exact unfoldQuickRC hμ ih henv hs hwa hwb
    rw [ite_eq_right hlt₂, ite_eq_right hlt₂]
    refine SimC.pureB ?_
    rw [sameConstHeadsC_spec' rfl rfl]
    have hboth : ∀ {s₀ : CState}, CSOK mode env s₀ → SimC mode env s₀ (RelDSC d)
        (unfoldDefinitionI (mkFEnv env) i >>= fun ua =>
          unfoldDefinitionI (mkFEnv env) j >>= fun ub =>
          match ua, ub with
          | some a₂, some b₂ => do
            let a₃ ← (coreKnotI mode (mkFEnv env) f).whnfCore true d a₂
            let b₃ ← (coreKnotI mode (mkFEnv env) f).whnfCore true d b₂
            deltaQuickI mode (coreKnotI mode (mkFEnv env) f) d a₃ b₃
          | _, _ => pure .unknown)
        (match unfoldDefinition env i, unfoldDefinition env j with
          | some a₂, some b₂ => do
            let a₃ ← (fueledFns mode env).whnfCore true d a₂
            let b₃ ← (fueledFns mode env).whnfCore true d b₂
            deltaQuick mode (fueledFns mode env) d a₃ b₃
          | _, _ => pure .unknown) := by
      intro s₀ hs
      refine SimC.bind_left (unfoldDefinitionC_eff hs rfl)
        (fun s₁ ua hs₁ hQa => ?_)
      refine SimC.bind_left (unfoldDefinitionC_eff hs₁ rfl)
        (fun s₂ ub hs₂ hQb => ?_)
      cases hua : unfoldDefinition env i with
      | none =>
        rw [hua] at hQa
        cases ua with
        | some a₂ => exact absurd hQa (by simp [OptEr])
        | none => cases ub <;> exact SimC.pure hs₂ ⟨rfl, fun _ _ h => nomatch h⟩
      | some a₂x =>
        rw [hua] at hQa
        cases ua with
        | none => exact absurd hQa (by simp [OptEr])
        | some a₂ =>
          cases hub : unfoldDefinition env j with
          | none =>
            rw [hub] at hQb
            cases ub with
            | some b₂ => exact absurd hQb (by simp [OptEr])
            | none => exact SimC.pure hs₂ ⟨rfl, fun _ _ h => nomatch h⟩
          | some b₂x =>
            rw [hub] at hQb
            cases ub with
            | none => exact absurd hQb (by simp [OptEr])
            | some b₂ =>
              dsimp only
              refine SimC.bind (ih.whnfCore hs₂ hQa (unfoldDefinition_WScoped henv hua hwa))
                (fun s₃ a₃ a₃x hs₃ hPa => ?_)
              refine SimC.bind (ih.whnfCore hs₃ hQb (unfoldDefinition_WScoped henv hub hwb))
                (fun s₄ b₃ b₃x hs₄ hPb => ?_)
              exact deltaQuickC_sim hμ ih hs₄ hPa.1 hPb.1 hPa.2 hPb.2
    by_cases hsr : (ReducibilityHint.sameRegular (headHint env i) (headHint env j) &&
        sameConstHeads i j) = true
    · rw [ite_eq_left hsr, ite_eq_left hsr]
      refine SimC.bind (defeqSpineC_sim ih hs rfl rfl hwa hwb)
        (fun s₇ sp sp' hs₇ hPsp => ?_)
      obtain rfl : sp = sp' := hPsp
      cases sp with
      | true =>
        simp only [↓reduceIte]
        exact SimC.pure hs₇ ⟨rfl, fun _ _ h => nomatch h⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hboth hs₇
    · rw [ite_eq_right hsr, ite_eq_right hsr]
      refine SimC.pureB ?_
      refine SimC.bind_pure_right ?_
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hboth hs

/-- The lazy-delta loop simulates its specification, by induction on
its step budget. -/
theorem lazyDeltaReductionC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} :
    ∀ (n : Nat) {i j : Expr} {a b : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i a → RelC j b → Expr.WScoped d a → Expr.WScoped d b →
      SimC mode env s₀ (RelLSC d)
        (lazyDeltaReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i j)
        (lazyDeltaReduction mode (fueledFns mode env) env d n a b)
  | 0, _, _, _, _, _, _, _, _, _, _ => SimC.throw
  | n + 1, i, j, _, _, s₀, hs, hda, hdb, hwa, hwb => by
    obtain rfl := hda
    obtain rfl := hdb
    simp only [lazyDeltaReductionI, lazyDeltaReduction]
    refine SimC.bind (defeqOffsetC_sim ih hs rfl rfl hwa hwb)
      (fun s₁ o o' hs₁ hP => ?_)
    obtain rfl : o = o' := hP
    cases o with
    | some v => exact SimC.pure hs₁ ⟨rfl, fun _ _ h => nomatch h⟩
    | none =>
    dsimp only
    refine SimC.pureB ?_
    rw [hasFvar_spec' rfl, hasFvar_spec' rfl]
    refine SimC.bind (reduceNatIfC_sim ih hs₁ rfl hwa _)
      (fun s₂ oa oax hs₂ hPa => ?_)
    cases oa with
    | some a₂ =>
      cases oax with
      | none => exact absurd hPa (by simp [RelOC])
      | some a₂x =>
        obtain ⟨ha₂d, hwa₂⟩ := hPa
        dsimp only
        refine SimC.bind (ih.defeq hs₂ ha₂d rfl hwa₂ hwb)
          (fun s₃ v v' hs₃ hv => ?_)
        obtain rfl : v = v' := hv
        exact SimC.pure hs₃ ⟨rfl, fun _ _ h => nomatch h⟩
    | none =>
      cases oax with
      | some a₂x => exact absurd hPa (by simp [RelOC])
      | none =>
      dsimp only
      refine SimC.bind (reduceNatIfC_sim ih hs₂ rfl hwb _)
        (fun s₃ ob obx hs₃ hPb => ?_)
      cases ob with
      | some b₂ =>
        cases obx with
        | none => exact absurd hPb (by simp [RelOC])
        | some b₂x =>
          obtain ⟨hb₂d, hwb₂⟩ := hPb
          dsimp only
          refine SimC.bind (ih.defeq hs₃ rfl hb₂d hwa hwb₂)
            (fun s₄ v v' hs₄ hv => ?_)
          obtain rfl : v = v' := hv
          exact SimC.pure hs₄ ⟨rfl, fun _ _ h => nomatch h⟩
      | none =>
        cases obx with
        | some b₂x => exact absurd hPb (by simp [RelOC])
        | none =>
        dsimp only
        refine SimC.bind (lazyDeltaStepC_sim hμ ih henv hs₃ rfl rfl hwa hwb)
          (fun s₄ st st' hs₄ hPs => ?_)
        obtain ⟨rfl, hsc⟩ := hPs
        cases st with
        | cont a' b' =>
          obtain ⟨hwa', hwb'⟩ := hsc a' b' rfl
          exact lazyDeltaReductionC_sim hμ ih henv n hs₄ rfl rfl hwa' hwb'
        | eq => exact SimC.pure hs₄ ⟨rfl, fun _ _ h => nomatch h⟩
        | diff => exact SimC.pure hs₄ ⟨rfl, fun _ _ h => nomatch h⟩
        | unknown => exact SimC.pure hs₄ ⟨rfl, fun x y h => by
            cases h
            exact ⟨hwa, hwb⟩⟩

/-- `lazy_delta_proj_reduction` simulates its specification. -/
theorem lazyDeltaProjReductionC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} {sn : Name} {ip : Nat} :
    ∀ (n : Nat) {i j : Expr} {a b : Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelC i a → RelC j b → Expr.WScoped d a → Expr.WScoped d b →
      SimC mode env s₀ RelVC
        (lazyDeltaProjReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn ip
          n i j)
        (lazyDeltaProjReduction mode (fueledFns mode env) env d sn ip n a b)
  | 0, _, _, _, _, _, _, _, _, _, _ => SimC.throw
  | n + 1, i, j, _, _, s₀, hs, hda, hdb, hwa, hwb => by
    obtain rfl := hda
    obtain rfl := hdb
    simp only [lazyDeltaProjReductionI, lazyDeltaProjReduction]
    refine SimC.bind (lazyDeltaStepC_sim hμ ih henv hs rfl rfl hwa hwb)
      (fun s₁ st st' hs₁ hPs => ?_)
    obtain ⟨rfl, hsc⟩ := hPs
    cases st
    case cont a' b' =>
      obtain ⟨hwa', hwb'⟩ := hsc a' b' rfl
      exact lazyDeltaProjReductionC_sim hμ ih henv n hs₁ rfl rfl hwa' hwb'
    case eq => exact SimC.pure hs₁ rfl
    all_goals
      dsimp only
      refine SimC.bind (reduceProjCoreC_sim ih henv hs₁ rfl hwa)
        (fun s₂ ox oxx hs₂ hPx => ?_)
      cases ox with
      | none =>
        cases oxx with
        | some _ => exact absurd hPx (by simp [RelOC])
        | none => exact ih.defeq hs₂ rfl rfl hwa hwb
      | some x =>
        cases oxx with
        | none => exact absurd hPx (by simp [RelOC])
        | some xx =>
        obtain ⟨hxd, hwx⟩ := hPx
        dsimp only
        refine SimC.bind (reduceProjCoreC_sim ih henv hs₂ rfl hwb)
          (fun s₃ oy oyx hs₃ hPy => ?_)
        cases oy with
        | none =>
          cases oyx with
          | some _ => exact absurd hPy (by simp [RelOC])
          | none => exact ih.defeq hs₃ rfl rfl hwa hwb
        | some y =>
          cases oyx with
          | none => exact absurd hPy (by simp [RelOC])
          | some yx =>
          obtain ⟨hyd, hwy⟩ := hPy
          exact ih.defeq hs₃ hxd hyd hwx hwy

/-- The proj/proj check simulates its specification. -/
theorem defeqProjPairC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqProjPairI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqProjPair mode (fueledFns mode env) env d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  unfold defeqProjPairI defeqProjPair
  cases i <;> cases j <;> (try exact SimC.pure hs rfl)
  case proj.proj s₁ i₁ e₁ s₂ i₂ e₂ =>
    dsimp only
    by_cases hii : (s₁ == s₂ && i₁ == i₂) = true
    · rw [ite_eq_left hii, ite_eq_left hii]
      exact lazyDeltaProjReductionC_sim hμ ih henv _ hs rfl rfl
        (by simpa only [Expr.WScoped] using hwa) (by simpa only [Expr.WScoped] using hwb)
    · rw [ite_eq_right hii, ite_eq_right hii]
      exact SimC.pure hs rfl

set_option maxHeartbeats 3200000 in
/-- The stuck comparison simulates its specification. -/
theorem defeqStuckC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqStuckI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqStuck mode (fueledFns mode env) env d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  have haS : RelC i i := rfl
  have hbS : RelC j j := rfl
  unfold defeqStuckI defeqStuck
  cases i <;> cases j <;> dsimp only <;>
    first
    | exact stuckIrrelC_sim hμ ih henv hs haS hbS hwa hwb
    | exact defeqC_etaL_arm hμ ih henv hs haS rfl rfl hbS hwa hwb
    | exact defeqC_etaR_arm hμ ih henv hs haS rfl rfl hbS hwa hwb
    | skip
  case lit.app l f x =>
    cases l <;> cases f <;> dsimp only <;>
      first
      | exact stuckIrrelC_sim hμ ih henv hs haS hbS hwa hwb
      | skip
    rename_i str cf usf
    rw [strLitSupportedF_eq]
    refine SimC.bind_left (pureEq_eff hs (cf == stringOfListName))
      (fun s₆b bq hs₆b hbq => ?_)
    subst bq
    simp only [beq_iff_eq]
    by_cases hsc : cf = stringOfListName ∧ usf = [] ∧ strLitSupported env = true
    · rw [ite_eq_left hsc, ite_eq_left hsc]
      refine SimC.bind_left (pureC_eff hs₆b (strLitToConstructor str))
        (fun s₇ sc hs₇ hQs => ?_)
      exact ih.defeq hs₇ hQs hbS (strLitToConstructor_WScoped str d) hwb
    · rw [ite_eq_right hsc, ite_eq_right hsc]
      exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS hwa hwb
  case app.lit f x l =>
    cases l <;> cases f <;> dsimp only <;>
      first
      | exact stuckIrrelC_sim hμ ih henv hs haS hbS hwa hwb
      | skip
    rename_i str cf usf
    rw [strLitSupportedF_eq]
    refine SimC.bind_left (pureEq_eff hs (cf == stringOfListName))
      (fun s₆b bq hs₆b hbq => ?_)
    subst bq
    simp only [beq_iff_eq]
    by_cases hsc : cf = stringOfListName ∧ usf = [] ∧ strLitSupported env = true
    · rw [ite_eq_left hsc, ite_eq_left hsc]
      refine SimC.bind_left (pureC_eff hs₆b (strLitToConstructor str))
        (fun s₇ sc hs₇ hQs => ?_)
      exact ih.defeq hs₇ haS hQs hwa (strLitToConstructor_WScoped str d)
    · rw [ite_eq_right hsc, ite_eq_right hsc]
      exact stuckIrrelC_sim hμ ih henv hs₆b haS hbS hwa hwb
  case fvar.fvar i₁ t₁ i₂ t₂ =>
    by_cases hij : (i₁ == i₂) = true
    · rw [ite_eq_left hij, ite_eq_left hij]
      exact SimC.pure hs rfl
    · rw [ite_eq_right hij, ite_eq_right hij]
      exact stuckIrrelC_sim hμ ih henv hs haS hbS hwa hwb
  case const.const c₁ us₁ c₂ us₂ =>
    by_cases hcc : c₁ = c₂
    · rw [ite_eq_left hcc, ite_eq_left hcc]
      refine SimC.bind_left (isEquivListLM_eff hs)
        (fun sE o hsE ho => ?_)
      subst ho
      refine SimC.bind (SimC.liftFueled _ _ hsE)
        (fun s₇ ok ok' hs₇ hPok => ?_)
      obtain rfl : ok = ok' := hPok
      cases ok with
      | true =>
        simp only [↓reduceIte]
        exact SimC.pure hs₇ rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact stuckIrrelC_sim hμ ih henv hs₇ haS hbS hwa hwb
    · rw [ite_eq_right hcc, ite_eq_right hcc]
      exact stuckIrrelC_sim hμ ih henv hs haS hbS hwa hwb
  case app.app f₁ x₁ f₂ x₂ =>
    refine SimC.pureB ?_
    refine SimC.pureB ?_
    have hAA : RelCL (Expr.getAppArgsC (Expr.app f₁ x₁)) (Expr.app f₁ x₁).getAppArgs :=
      Expr.getAppArgsC_spec _
    have hBB : RelCL (Expr.getAppArgsC (Expr.app f₂ x₂)) (Expr.app f₂ x₂).getAppArgs :=
      Expr.getAppArgsC_spec _
    have hlena : (Expr.getAppArgsC (Expr.app f₁ x₁)).length
        = (Expr.app f₁ x₁).getAppArgs.length := RelCL.length hAA
    have hlenb : (Expr.getAppArgsC (Expr.app f₂ x₂)).length
        = (Expr.app f₂ x₂).getAppArgs.length := RelCL.length hBB
    simp only [hlena, hlenb]
    by_cases hlen : (Expr.app f₁ x₁).getAppArgs.length = (Expr.app f₂ x₂).getAppArgs.length
    · rw [ite_eq_left hlen, ite_eq_left hlen]
      refine SimC.pureB ?_
      refine SimC.pureB ?_
      refine SimC.bind (ih.defeq hs rfl rfl hwa.getAppFn hwb.getAppFn)
        (fun s₇ r₁ r₁' hs₇ hP₁ => ?_)
      obtain rfl : r₁ = r₁' := hP₁
      cases r₁ with
      | true =>
        simp only [↓reduceIte]
        refine SimC.bind (defEqListC_sim ih hs₇ hAA hBB hwa.getAppArgs hwb.getAppArgs)
          (fun s₈ r₂ r₂' hs₈ hP₂ => ?_)
        obtain rfl : r₂ = r₂' := hP₂
        cases r₂ with
        | true =>
          simp only [↓reduceIte]
          exact SimC.pure hs₈ rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact stuckIrrelC_sim hμ ih henv hs₈ haS hbS hwa hwb
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact stuckIrrelC_sim hμ ih henv hs₇ haS hbS hwa hwb
    · rw [ite_eq_right hlen, ite_eq_right hlen]
      exact stuckIrrelC_sim hμ ih henv hs haS hbS hwa hwb

theorem defeqBodyC_sim (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i j : Expr} {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC
      (defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqBody mode (fueledFns mode env) env d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  unfold defeqBodyI defeqBody
  by_cases hab : (i == j) = true
  · simp only [ite_eq_left hab]
    exact SimC.pure hs rfl
  simp only [ite_eq_right hab]
  refine SimC.pureB ?_
  rw [isBoolTrue_spec' rfl]
  refine SimC.pureB ?_
  rw [hasFvar_spec' rfl]
  refine SimC.bind (boolTrueShortcutIfC_sim ih hs rfl hwa _)
    (fun s₀b rbt rbtx hs₀b hPbt => ?_)
  cases hPbt
  cases rbt with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₀b rfl
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine SimC.bind (ih.whnfCore hs₀b rfl hwa)
    (fun s₁ a' a'x hs₁ hPa => ?_)
  obtain ⟨rfl, hwa'⟩ := hPa
  refine SimC.bind (ih.whnfCore hs₁ rfl hwb)
    (fun s₂ b' b'x hs₂ hPb => ?_)
  obtain ⟨rfl, hwb'⟩ := hPb
  refine SimC.bind (quickDefEqC_sim hμ ih hs₂ rfl rfl hwa' hwb')
    (fun s₃ o o' hs₃ hPo => ?_)
  obtain rfl : o = o' := hPo
  cases o with
  | some v => exact SimC.pure hs₃ rfl
  | none =>
  dsimp only
  refine SimC.bind (propIrrelC_sim ih hs₃ rfl rfl hwa' hwb')
    (fun s₄ rp rp' hs₄ hPp => ?_)
  obtain rfl : rp = rp' := hPp
  cases rp with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₄ rfl
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine SimC.bind (lazyDeltaReductionC_sim hμ ih henv _ hs₄ rfl rfl hwa' hwb')
    (fun s₅ lr lr' hs₅ hPl => ?_)
  obtain ⟨rfl, hsc⟩ := hPl
  cases lr with
  | verdict v => exact SimC.pure hs₅ rfl
  | unknown a₁ b₁ =>
  obtain ⟨hwa₁, hwb₁⟩ := hsc a₁ b₁ rfl
  dsimp only
  refine SimC.bind (defeqProjPairC_sim hμ ih henv hs₅ rfl rfl hwa₁ hwb₁)
    (fun s₆ rq rq' hs₆ hPq => ?_)
  obtain rfl : rq = rq' := hPq
  cases rq with
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₆ rfl
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hhp : (!a₁.headIsProj && !b₁.headIsProj) = true
  · rw [ite_eq_left hhp, ite_eq_left hhp]
    exact defeqStuckC_sim hμ ih henv hs₆ rfl rfl hwa₁ hwb₁
  rw [ite_eq_right hhp, ite_eq_right hhp]
  refine SimC.bind (ih.whnfCore hs₆ rfl hwa₁)
    (fun s₇ a₂ a₂x hs₇ hPa₂ => ?_)
  obtain ⟨rfl, hwa₂⟩ := hPa₂
  refine SimC.bind (ih.whnfCore hs₇ rfl hwb₁)
    (fun s₈ b₂ b₂x hs₈ hPb₂ => ?_)
  obtain ⟨rfl, hwb₂⟩ := hPb₂
  by_cases hun : (a₂ == a₁ && b₂ == b₁) = true
  · rw [ite_eq_left hun, ite_eq_left hun]
    exact defeqStuckC_sim hμ ih henv hs₈ rfl rfl hwa₁ hwb₁
  · rw [ite_eq_right hun, ite_eq_right hun]
    exact ih.defeq hs₈ rfl rfl hwa₂ hwb₂

end Walks

end ConLeche.Cached
