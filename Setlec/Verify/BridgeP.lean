import Setlec.Verify.BridgeS1
import Setlec.Verify.CheckerF
import Setlec.Verify.ParseP

/-!
# Parsed-index drivers: the simulation walks (task #78)

Each lemma relates a parsed-index driver function
(`Setlec/Kernel/CheckerS.lean`, `checkConstantValP` …) to the generic
declaration checker at the fueled families, as a `SimAt` from any
invariant state.  Compared to the `sharedOps` walks
(`Setlec/Verify/BridgeS1.lean`) the entry operations consume *indices*
(no per-call interning — the knot simulations `ssimI` apply directly,
given the argument's denotation), the raw and post-annotate syntactic
checks run DAG-memoized on the arena (rewritten to their `Expr`-level
counterparts by the walker specs of `Setlec/Verify/ParseP.lean`), and
the accepted constant's indices are recorded in the interned
environment (`recordIConst` — sound by `ISOK.insertIEnv`, the
self-certifying `ienv` clause).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

section WalksP

variable {env : Env} {s₀ : IState}

/-! ## State-only steps -/

/-- Inserting a tagged interned-environment entry preserves the
invariant (the `ienv` clause is exactly the tags' denotations). -/
theorem ISOK.insertIEnv {s : IState} (hs : ISOK env s) {n : Name}
    {ent : IConstE} (hty : s.store.denote ent.ty = some ent.tyE)
    (hval : ∀ vE vi, ent.val = some (vE, vi) →
      s.store.denote vi = some vE) :
    ISOK env { s with ienv := s.ienv.insert n ent } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC,
    hs.whnfC, hs.inferC, hs.annotC, hs.defeqC, hs.codOfC, hs.lsimp,
    hs.lnz, hs.eqv, ?_⟩
  intro nm ent' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : n == nm
  · rw [if_pos hk] at hl
    cases hl
    exact ⟨hty, hval⟩
  · rw [if_neg hk] at hl
    exact hs.ienv nm ent' hl

/-- `recordIConst` runs to the ienv-extended state. -/
theorem recordIConst_run (n : Name) (tyE : Expr) (ty : EIdx)
    (val : Option (Expr × EIdx)) (s : IState) :
    recordIConst n tyE ty val s =
      .ok ((), { s with ienv := s.ienv.insert n ⟨tyE, ty, val⟩ }) := rfl

/-- `recordIConst` as a state-only effect. -/
theorem recordIConst_eff (hs : ISOK env s₀) {n : Name} {tyE : Expr}
    {ty : EIdx} {val : Option (Expr × EIdx)}
    (hty : s₀.store.denote ty = some tyE)
    (hval : ∀ vE vi, val = some (vE, vi) →
      s₀.store.denote vi = some vE) :
    IEff env s₀ (fun _ _ => True) (recordIConst n tyE ty val) := by
  intro v' s' hr
  rw [recordIConst_run] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.insertIEnv hty hval, Ext.refl _, trivial⟩

/-- `readbackEM` yields the denotation, state untouched. -/
theorem readbackEM_eff (hs : ISOK env s₀) {j : EIdx} {w : Expr}
    (hden : s₀.store.denote j = some w) :
    IEff env s₀ (fun _ v => v = w) (readbackEM j) := by
  intro v' s' hr
  rw [show readbackEM j = (Setlec.withStore (fun st => st.readbackI j) >>=
      fun o => match o with
      | some v => pure v
      | none => throw (.internal "interned readback failed") :
      CheckIM Expr) from rfl] at hr
  simp only [Bind.bind, StateT.bind, Setlec.withStore, Functor.map,
    StateT.map, get, getThe, MonadStateOf.get, StateT.get, Except.map,
    Except.bind, pure, StateT.pure, Except.pure] at hr
  rw [readbackI_spec hs.wf hden] at hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, Ext.refl _, rfl⟩

/-! ## Parsed-index entry operations -/

private theorem fueledM_bind_pure' {α : Type} (x : FueledM α) :
    x >>= pure = x := by
  refine Subtype.ext (funext fun F => ?_)
  show x.val F >>= pure = x.val F
  cases x.val F <;> rfl

/-- Parsed-index `ensureSort` simulates the fueled family. -/
theorem opSIx_sim (henv : EnvWF env) {d : Nat} {i : EIdx} {e : Expr}
    (hs : ISOK env s₀) (hden : s₀.store.denote i = some e)
    (hw : WScoped d e) :
    SimAt env s₀ RelV (opSIx (mkFEnv env) d i)
      (fueledOpsM.ensureSort env d e) := by
  have h1 : SimAt env s₀ RelV (opSIx (mkFEnv env) d i)
      (ensureSort (fueledFns env) env d e >>= pure) := by
    show SimAt env s₀ RelV
      (ensureSortI (coreKnotI (mkFEnv env) checkFuel) d i >>= fun u =>
        readbackLevelM u)
      (ensureSort (fueledFns env) env d e >>= pure)
    refine SimAt.bind
      (ensureSortI_sim (ssimI env henv checkFuel) hs hden hw)
      (fun s₂ u lu hs₂ hext₂ hPu => ?_)
    exact SimAt.of_eff (readbackLevelM_eff hs₂
      (hPu : s₂.store.denoteL u = some lu)) lu (fun s r hQ => hQ)
  refine SimAt.wr h1 (fun u F h => ⟨F, ?_⟩)
  rw [FueledM.atF_bind] at h
  simp only [Bind.bind] at h
  cases hx : (ensureSort (fueledFns env) env d e).val F with
  | error er =>
    rw [hx] at h
    exact nomatch h
  | ok v =>
    rw [hx] at h
    dsimp only [Except.bind] at h
    obtain rfl : v = u := by
      simpa [pure, Except.pure] using h
    rw [ensureSort_atF, ensureSort_def] at hx
    exact hx

/-! ## The parsed-index checker functions -/

/-- `checkConstantValP` simulates the generic `checkConstantVal` at
the fueled families on the denoted header: the returned constant is
the fueled result, its type well-scoped, and the returned index
denotes it. -/
theorem checkConstantValP_sim (henv : EnvWF env) {cvp : ConstantValP}
    {tyE : Expr} (hs : ISOK env s₀)
    (hden : s₀.store.denote cvp.type = some tyE) :
    SimAt env s₀ (fun s v w => v.1 = w ∧ WScoped 0 v.1.type ∧
        s.store.denote v.2 = some v.1.type)
      (checkConstantValP (mkFEnv env) cvp)
      (checkConstantVal fueledOpsM env
        ⟨cvp.name, cvp.levelParams, tyE⟩) := by
  unfold checkConstantValP checkConstantVal
  have hme : (mkFEnv env).env = env := rfl
  simp only [mkFEnv_find?, hme]
  by_cases h1 : (env.find? cvp.name).isSome = true
  · simp only [if_pos h1]
    exact SimAt.throw_bind
  simp only [if_neg h1]
  by_cases h2 : reservedBasisNames.contains cvp.name = true
  · simp only [if_pos h2]
    exact SimAt.throw_bind
  simp only [if_neg h2]
  by_cases h3 : cvp.name.isProjFnShape = true
  · simp only [if_pos h3]
    exact SimAt.throw_bind
  simp only [if_neg h3]
  by_cases h4 : Name.nodup cvp.levelParams = true
  case neg =>
    simp only [if_neg h4]
    exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.withStore ?_
  rw [looseBVarsBoundedI_spec hs.wf hden]
  by_cases h5 : tyE.looseBVarsBounded 0 = true
  case neg =>
    simp only [if_neg h5]
    exact SimAt.throw_bind
  simp only [if_pos h5]
  refine SimAt.withStore ?_
  rw [hasFvarI_spec hs.wf hden]
  by_cases h6 : tyE.hasFvar = true
  · simp only [if_pos h6]
    exact SimAt.throw_bind
  simp only [if_neg h6]
  refine SimAt.bind ((ssimI env henv checkFuel).annotate hs hden
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)))
    (fun s₁ jA w hs₁ hext₁ hP => ?_)
  obtain ⟨hjA, hwty⟩ := hP
  refine SimAt.withStore ?_
  rw [allLevelParamsDefinedI_spec hs₁.wf hjA]
  by_cases h7 : w.allLevelParamsDefined cvp.levelParams = true
  case neg =>
    simp only [if_neg h7]
    exact SimAt.throw_bind
  simp only [if_pos h7]
  refine SimAt.withStore ?_
  rw [constsResolveFI_spec hs₁.wf hjA]
  by_cases h8 : w.constsResolve env = true
  case neg =>
    simp only [if_neg h8]
    exact SimAt.throw_bind
  simp only [if_pos h8]
  refine SimAt.bind ((ssimI env henv checkFuel).infer hs₁ hjA hwty)
    (fun s₂ jsty wsty hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hjsty, hwsty⟩ := hP₂
  refine SimAt.bind (opSIx_sim henv hs₂ hjsty hwsty)
    (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
  refine SimAt.bind_left (readbackEM_eff hs₃
      (denote_mono hext₃ (denote_mono hext₂ hjA)))
    (fun s₄ tyR hs₄ hext₄ hQ => ?_)
  subst hQ
  exact SimAt.pure hs₄ ⟨rfl, hwty,
    denote_mono hext₄ (denote_mono hext₃ (denote_mono hext₂ hjA))⟩

/-- `checkDefnValP` simulates the generic `checkDefnVal`: the pushed
index is `mkFEnv` of the fueled environment, whose head stores the
annotated (fvar-free) value. -/
theorem checkDefnValP_sim (henv : EnvWF env) {cvA : ConstantVal}
    {jty : EIdx} {value : EIdx} {ve : Expr} {hint : ReducibilityHint}
    (htf : WScoped 0 cvA.type) (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => v.env = w ∧ v = mkFEnv v.env ∧
        ∀ cv' v' h', v.env.find? cvA.name = some (.defnInfo cv' v' h') →
          v'.hasFvar = false)
      (checkDefnValP (mkFEnv env) cvA jty value hint)
      (checkDefnVal fueledOpsM env cvA ve hint) := by
  unfold checkDefnValP checkDefnVal
  refine SimAt.withStore ?_
  rw [looseBVarsBoundedI_spec hs.wf hdenv]
  by_cases h1 : ve.looseBVarsBounded 0 = true
  case neg =>
    simp only [if_neg h1]
    exact SimAt.throw_bind
  simp only [if_pos h1]
  refine SimAt.withStore ?_
  rw [hasFvarI_spec hs.wf hdenv]
  by_cases h2 : ve.hasFvar = true
  · simp only [if_pos h2]
    exact SimAt.throw_bind
  simp only [if_neg h2]
  refine SimAt.bind ((ssimI env henv checkFuel).annotate hs hdenv
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ jv w hs₁ hext₁ hP => ?_)
  obtain ⟨hjv, hwv⟩ := hP
  refine SimAt.withStore ?_
  rw [allLevelParamsDefinedI_spec hs₁.wf hjv]
  by_cases h3 : w.allLevelParamsDefined cvA.levelParams = true
  case neg =>
    simp only [if_neg h3]
    exact SimAt.throw_bind
  simp only [if_pos h3]
  refine SimAt.withStore ?_
  rw [constsResolveFI_spec hs₁.wf hjv]
  by_cases h4 : w.constsResolve env = true
  case neg =>
    simp only [if_neg h4]
    exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind ((ssimI env henv checkFuel).infer hs₁ hjv hwv)
    (fun s₂ jvt wvt hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hjvt, hwvt⟩ := hP₂
  refine SimAt.bind ((ssimI env henv checkFuel).defeq hs₂ hjvt
      (denote_mono hext₂ (denote_mono hext₁ hjty)) hwvt htf)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    have hjv₃ : s₃.store.denote jv = some w :=
      denote_mono hext₃ (denote_mono hext₂ hjv)
    refine SimAt.bind_left (readbackEM_eff hs₃ hjv₃)
      (fun s₄ vE hs₄ hext₄ hQ => ?_)
    subst hQ
    refine SimAt.bind_left (recordIConst_eff hs₄
        (denote_mono hext₄ (denote_mono hext₃
          (denote_mono hext₂ (denote_mono hext₁ hjty))))
        (fun vE' vi h => by
          cases h
          exact denote_mono hext₄ hjv₃))
      (fun s₅ u hs₅ hext₅ hQ' => ?_)
    refine SimAt.pure hs₅ ⟨rfl, mkFEnv_push env _, ?_⟩
    intro cv' v' h' hf
    rw [show ((mkFEnv env).push (.defnInfo cvA vE hint)).env =
      ⟨.defnInfo cvA vE hint :: env.consts⟩ from rfl] at hf
    rw [Env.find?_cons, if_pos (show (ConstantInfo.defnInfo cvA vE
      hint).name = cvA.name from rfl)] at hf
    simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf
    obtain ⟨-, rfl, -⟩ := hf
    exact not_hasFvar_of_fvarsBelow_zero hwv.fvarsBelow

/-- `checkThmValP` simulates the generic `checkThmVal`. -/
theorem checkThmValP_sim (henv : EnvWF env) {cvA : ConstantVal}
    {jty : EIdx} {value : EIdx} {ve : Expr}
    (htf : WScoped 0 cvA.type) (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => v.env = w ∧ v = mkFEnv v.env)
      (checkThmValP (mkFEnv env) cvA jty value)
      (checkThmVal fueledOpsM env cvA ve) := by
  unfold checkThmValP checkThmVal
  refine SimAt.bind ((ssimI env henv checkFuel).infer hs hjty htf)
    (fun s₁ jsty wsty hs₁ hext₁ hP => ?_)
  obtain ⟨hjsty, hwsty⟩ := hP
  refine SimAt.bind (opSIx_sim henv hs₁ hjsty hwsty)
    (fun s₂ u u' hs₂ hext₂ hP₂ => ?_)
  obtain rfl : u = u' := hP₂
  refine SimAt.bind (SimAt.liftFueled _ _ hs₂)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
  simp only [↓reduceIte]
  have hjty₃ : s₃.store.denote jty = some cvA.type :=
    denote_mono hext₃ (denote_mono hext₂ (denote_mono hext₁ hjty))
  have hdenv₃ : s₃.store.denote value = some ve :=
    denote_mono hext₃ (denote_mono hext₂ (denote_mono hext₁ hdenv))
  refine SimAt.withStore ?_
  rw [looseBVarsBoundedI_spec hs₃.wf hdenv₃]
  by_cases h1 : ve.looseBVarsBounded 0 = true
  case neg =>
    simp only [if_neg h1]
    exact SimAt.throw_bind
  simp only [if_pos h1]
  refine SimAt.withStore ?_
  rw [hasFvarI_spec hs₃.wf hdenv₃]
  by_cases h2 : ve.hasFvar = true
  · simp only [if_pos h2]
    exact SimAt.throw_bind
  simp only [if_neg h2]
  refine SimAt.bind ((ssimI env henv checkFuel).annotate hs₃ hdenv₃
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₄ jv w hs₄ hext₄ hP₄ => ?_)
  obtain ⟨hjv, hwv⟩ := hP₄
  refine SimAt.withStore ?_
  rw [allLevelParamsDefinedI_spec hs₄.wf hjv]
  by_cases h3 : w.allLevelParamsDefined cvA.levelParams = true
  case neg =>
    simp only [if_neg h3]
    exact SimAt.throw_bind
  simp only [if_pos h3]
  refine SimAt.withStore ?_
  rw [constsResolveFI_spec hs₄.wf hjv]
  by_cases h4 : w.constsResolve env = true
  case neg =>
    simp only [if_neg h4]
    exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind ((ssimI env henv checkFuel).infer hs₄ hjv hwv)
    (fun s₅ jvt wvt hs₅ hext₅ hP₅ => ?_)
  obtain ⟨hjvt, hwvt⟩ := hP₅
  refine SimAt.bind ((ssimI env henv checkFuel).defeq hs₅ hjvt
      (denote_mono hext₅ (denote_mono hext₄ hjty₃)) hwvt htf)
    (fun s₆ b b' hs₆ hext₆ hP₆ => ?_)
  obtain rfl : b = b' := hP₆
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    have hjv₆ : s₆.store.denote jv = some w := denote_mono hext₆
      (denote_mono hext₅ hjv)
    refine SimAt.bind_left (readbackEM_eff hs₆ hjv₆)
      (fun s₇ vE hs₇ hext₇ hQ => ?_)
    subst hQ
    refine SimAt.bind_left (recordIConst_eff hs₇
        (denote_mono hext₇ (denote_mono hext₆
          (denote_mono hext₅ (denote_mono hext₄ hjty₃))))
        (fun vE' vi h => by
          cases h
          exact denote_mono hext₇ hjv₆))
      (fun s₈ u₀ hs₈ hext₈ hQ' => ?_)
    exact SimAt.pure hs₈ ⟨rfl, mkFEnv_push env _⟩

/-- `checkOpaqueValP` simulates the generic `checkOpaqueVal`. -/
theorem checkOpaqueValP_sim (henv : EnvWF env) {cvA : ConstantVal}
    {jty : EIdx} {value : EIdx} {ve : Expr}
    (htf : WScoped 0 cvA.type) (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hs : ISOK env s₀) :
    SimAt env s₀ (fun _ v w => (v.env = w ∧ v = mkFEnv v.env) ∧
        ve.hasFvar = false)
      (checkOpaqueValP (mkFEnv env) cvA jty value)
      (checkOpaqueVal fueledOpsM env cvA ve) := by
  unfold checkOpaqueValP checkOpaqueVal
  refine SimAt.withStore ?_
  rw [looseBVarsBoundedI_spec hs.wf hdenv]
  by_cases h1 : ve.looseBVarsBounded 0 = true
  case neg =>
    simp only [if_neg h1]
    exact SimAt.throw_bind
  simp only [if_pos h1]
  refine SimAt.withStore ?_
  rw [hasFvarI_spec hs.wf hdenv]
  by_cases h2 : ve.hasFvar = true
  · simp only [if_pos h2]
    exact SimAt.throw_bind
  simp only [if_neg h2]
  refine SimAt.bind ((ssimI env henv checkFuel).annotate hs hdenv
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ jv w hs₁ hext₁ hP => ?_)
  obtain ⟨hjv, hwv⟩ := hP
  refine SimAt.withStore ?_
  rw [allLevelParamsDefinedI_spec hs₁.wf hjv]
  by_cases h3 : w.allLevelParamsDefined cvA.levelParams = true
  case neg =>
    simp only [if_neg h3]
    exact SimAt.throw_bind
  simp only [if_pos h3]
  refine SimAt.withStore ?_
  rw [constsResolveFI_spec hs₁.wf hjv]
  by_cases h4 : w.constsResolve env = true
  case neg =>
    simp only [if_neg h4]
    exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind ((ssimI env henv checkFuel).infer hs₁ hjv hwv)
    (fun s₂ jvt wvt hs₂ hext₂ hP₂ => ?_)
  obtain ⟨hjvt, hwvt⟩ := hP₂
  refine SimAt.bind ((ssimI env henv checkFuel).defeq hs₂ hjvt
      (denote_mono hext₂ (denote_mono hext₁ hjty)) hwvt htf)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    refine SimAt.bind_left (recordIConst_eff hs₃
        (denote_mono hext₃ (denote_mono hext₂
          (denote_mono hext₁ hjty)))
        (fun vE' vi h => nomatch h))
      (fun s₄ u hs₄ hext₄ hQ' => ?_)
    exact SimAt.pure hs₄ ⟨⟨rfl, mkFEnv_push env _⟩,
      Bool.not_eq_true _ ▸ h2⟩

/-! ## The parsed declaration -/

/-- The non-inductive branches of `checkDeclSP` simulate the generic
`checkDecl` at the fueled families on the denoted declaration. -/
theorem checkDeclSP_sim (henv : EnvWF env) (hs : ISOK env s₀)
    {pd : DeclP} {d : Declaration}
    (hden : denoteDeclP s₀.store pd = some d)
    (hnotind : ∀ block, pd ≠ .indDecl block) :
    SimAt env s₀ (fun _ v w => v.env = w ∧ v = mkFEnv v.env)
      (checkDeclSP (mkFEnv env) pd)
      (checkDecl fueledOpsM env d) := by
  cases pd with
  | indDecl block => exact absurd rfl (hnotind block)
  | basisDecl kind =>
    obtain rfl : Declaration.basisDecl kind = d := by
      simpa [denoteDeclP] using hden
    show SimAt env s₀ _ (do
        if kind = .quotK then
          unless (mkFEnv env).find? eqName = some eqA do
            throw (.notImplemented
              "quotient basis requires the pinned Eq basis")
        kind.declsA.foldlM installBasisDeclF (mkFEnv env) :
        CheckIM FEnv) _
    unfold checkDecl
    dsimp only
    rw [installBasisFoldF_push]
    simp only [mkFEnv_find?]
    by_cases hq : kind = .quotK
    · simp only [if_pos hq]
      by_cases he : env.find? eqName = some eqA
      · simp only [if_pos he]
        rw [← fueledM_bind_pure'
          (kind.declsA.foldlM installBasisDecl env : FueledM Env)]
        refine SimAt.bind (installBasisFoldS_sim _ env hs)
          (fun s₁ e e' hs₁ hext₁ hP => ?_)
        obtain rfl : e = e' := hP
        exact SimAt.pure hs₁ ⟨rfl, rfl⟩
      · simp only [if_neg he]
        exact SimAt.throw_bind
    · simp only [if_neg hq]
      rw [← fueledM_bind_pure'
        (kind.declsA.foldlM installBasisDecl env : FueledM Env)]
      refine SimAt.bind (installBasisFoldS_sim _ env hs)
        (fun s₁ e e' hs₁ hext₁ hP => ?_)
      obtain rfl : e = e' := hP
      exact SimAt.pure hs₁ ⟨rfl, rfl⟩
  | axiomDecl cvp =>
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, rfl⟩ := hden
    show SimAt env s₀ _ _ (checkDecl fueledOpsM env
      (.axiomDecl ⟨cvp.name, cvp.levelParams, tyE⟩))
    unfold checkDeclSP checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    simp only [stdAxiomOkF_eq, trustCompilerOkF_eq, ofReduceAxOkF_eq]
    by_cases h1 : stdAxiomOk env cvR = true
    · simp only [if_pos h1]
      refine SimAt.bind_left (recordIConst_eff hs₁ hjty
          (fun vE vi h => nomatch h))
        (fun s₂ u hs₂ hext₂ hQ => ?_)
      exact SimAt.pure hs₂ ⟨rfl, mkFEnv_push env _⟩
    · simp only [if_neg h1]
      by_cases htc : cvR.name = trustCompilerName
      · simp only [if_pos htc]
        by_cases htok : trustCompilerOk env cvR = true
        · simp only [if_pos htok]
          refine SimAt.bind_left (recordIConst_eff hs₁ hjty
              (fun vE vi h => nomatch h))
            (fun s₂ u hs₂ hext₂ hQ => ?_)
          exact SimAt.pure hs₂ ⟨rfl, mkFEnv_push env _⟩
        · simp only [if_neg htok]
          exact SimAt.throw
      · simp only [if_neg htc]
        by_cases hor : cvR.name = ofReduceNatName ∨
            cvR.name = ofReduceBoolName
        · simp only [if_pos hor]
          by_cases hoo : ofReduceAxOk env cvR = true
          · simp only [if_pos hoo]
            refine SimAt.bind_left (recordIConst_eff hs₁ hjty
                (fun vE vi h => nomatch h))
              (fun s₂ u hs₂ hext₂ hQ => ?_)
            exact SimAt.pure hs₂ ⟨rfl, mkFEnv_push env _⟩
          · simp only [if_neg hoo]
            exact SimAt.throw
        · simp only [if_neg hor]
          by_cases h2 : cvR.name = propextName ∨ cvR.name = choiceName
          · simp only [if_pos h2]
            exact SimAt.throw
          · simp only [if_neg h2]
            by_cases h3 : toleratedAxiomNames.contains cvR.name = true
            · simp only [if_pos h3]
              exact SimAt.pure hs₁ ⟨rfl, rfl⟩
            · simp only [if_neg h3]
              exact SimAt.throw
  | thmDecl cvp value =>
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, ve, hve, rfl⟩ := hden
    unfold checkDeclSP checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    refine SimAt.mono (fun s v w h => h) (checkThmValP_sim henv hwty hjty
      (denote_mono hext₁ hve) hs₁)
  | opaqueDecl cvp value =>
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, ve, hve, rfl⟩ := hden
    unfold checkDeclSP checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    refine SimAt.bind (checkOpaqueValP_sim henv hwty hjty
        (denote_mono hext₁ hve) hs₁)
      (fun s₂ fe2 env2 hs₂ hext₂ hP₂ => ?_)
    obtain ⟨⟨henvEq, hmk⟩, hvf⟩ := hP₂
    subst henvEq
    rw [hmk]
    simp only [mkFEnv_env]
    by_cases hred : reduceOpNames.contains cvR.name = true
    case neg =>
      simp only [if_neg hred]
      exact SimAt.pure hs₂ ⟨rfl, hmk ▸ hmk⟩
    simp only [if_pos hred]
    refine SimAt.bind_left (readbackEM_eff hs₂
        (denote_mono hext₂ (denote_mono hext₁ hve)))
      (fun s₃ vE hs₃ hext₃ hQ => ?_)
    subst hQ
    rw [checkReducePinF_eq]
    refine SimAt.bind (checkReducePinS_sim henv hvf hs₃)
      (fun s₄ u u' hs₄ hext₄ hP₄ => ?_)
    exact SimAt.pure hs₄ ⟨rfl, hmk ▸ hmk⟩
  | defnDecl cvp value hint =>
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, ve, hve, rfl⟩ := hden
    unfold checkDeclSP checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    by_cases hb : (natOpNames.contains cvR.name ||
        natDivModNames.contains cvR.name) = true
    case neg =>
      obtain ⟨h1, h4⟩ : ¬(natOpNames.contains cvR.name = true) ∧
          ¬(natDivModNames.contains cvR.name = true) := by
        simpa [not_or] using hb
      simp only [if_neg hb, if_neg h1, if_neg h4]
      rw [← bind_pure (checkDefnValP (mkFEnv env) _ jty value hint)]
      refine SimAt.bind (checkDefnValP_sim henv hwty hjty
          (denote_mono hext₁ hve) hs₁)
        (fun s₂ fe2 env2 hs₂ hext₂ hP₂ => ?_)
      obtain ⟨henvEq, hmk, -⟩ := hP₂
      subst henvEq
      exact SimAt.pure hs₂ ⟨rfl, hmk⟩
    simp only [if_pos hb]
    refine SimAt.bind (checkDefnValP_sim henv hwty hjty
        (denote_mono hext₁ hve) hs₁)
      (fun s₂ fe2 env2 hs₂ hext₂ hP₂ => ?_)
    obtain ⟨henvEq, hmk, hv'fD⟩ := hP₂
    subst henvEq
    rw [hmk]
    simp only [natOpGuardF_eq, natOpStoredOkF_eq_fun, mkFEnv_find?,
      checkDivModPinF_eq, mkFEnv_env]
    by_cases h1 : natOpNames.contains cvR.name = true
    case neg =>
      simp only [if_neg h1]
      by_cases h4 : natDivModNames.contains cvR.name = true
      case neg =>
        simp only [if_neg h4]
        exact SimAt.pure hs₂ ⟨rfl, hmk ▸ hmk⟩
      simp only [if_pos h4]
      refine SimAt.bind (checkDivModPinS_sim henv
          (List.contains_iff_mem.mp h4) hv'fD hs₂)
        (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
      exact SimAt.pure hs₃ ⟨rfl, hmk ▸ hmk⟩
    simp only [if_pos h1]
    by_cases h2 : (natOpGuard fe2.env cvR.name &&
        (natOpDeps cvR.name).all (natOpStoredOk fe2.env)) = true
    case neg => simp only [if_neg h2]; exact SimAt.throw_bind
    simp only [h2, ↓reduceIte]
    cases hfind : fe2.env.find? cvR.name with
    | none => exact SimAt.throw_bind
    | some ci =>
      cases ci with
      | defnInfo cvS value' hintS =>
        dsimp only
        have hvf : value'.hasFvar = false := hv'fD _ _ _ hfind
        have hsc : ∀ eq ∈ (natOpEquations 0 cvR.name).map
            (fun eq => (Expr.substConst0 cvR.name value' eq.1,
              Expr.substConst0 cvR.name value' eq.2)),
            (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true) := by
          intro eq heq
          obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
          obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB
            (by simpa using h1) eq₀ heq₀
          exact ⟨wscopedB_substConst0 hvf _ hs1,
            wscopedB_substConst0 hvf _ hs2⟩
        refine SimAt.bind (certifyNatEqsS_sim henv hsc hs₂)
          (fun s₃ ok ok' hs₃ hext₃ hP₃ => ?_)
        obtain rfl : ok = ok' := hP₃
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.throw_bind
        | true =>
          simp only [↓reduceIte]
          by_cases h4 : natDivModNames.contains cvR.name = true
          case neg =>
            simp only [if_neg h4]
            exact SimAt.pure hs₃ ⟨rfl, hmk ▸ hmk⟩
          simp only [if_pos h4]
          refine SimAt.bind (checkDivModPinS_sim henv
              (List.contains_iff_mem.mp h4) hv'fD hs₃)
            (fun s₄ u u' hs₄ hext₄ hP₄ => ?_)
          exact SimAt.pure hs₄ ⟨rfl, hmk ▸ hmk⟩
      | axiomInfo cv' => exact SimAt.throw_bind
      | thmInfo cv' v' => exact SimAt.throw_bind
      | indInfo cv' caps => exact SimAt.throw_bind
      | ctorInfo cv' nP nF => exact SimAt.throw_bind
      | recInfo cv' mI rP rules => exact SimAt.throw_bind
      | projInfo _ => exact SimAt.throw_bind

end WalksP

end Setlec
