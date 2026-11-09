module

public import ConLeche.Verify.Cached.DiscC1

public section

/-!
# Cached body walks, part 2: the stuck-term certificates (task #163)

Each walk is a `Std.WP` triple whose post names the cached value as the
fueled answer (`Runs`), proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`; the triple forms of the knot's
entry points and the vocabulary these walks add are in `DiscC1.lean`).
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

section Walks

variable {env : Env} {f : Nat}

/-- The hoisted `Prop`-branch test (task #168): the fast arms are the
same pure reads on both sides (`mkFEnv_find_fun`). -/
theorem propIrrelC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ propIrrelI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (propIrrel (fueledFns mode eager env) env d a b) v;
        ⊤⦄ := by
  sym only [conleche_grind, propIrrel, mkFEnv_find_fun, mkFEnv_findTable_fun] =>
    vcgen [propIrrelI, ih.inferIO_spec, ih.whnf_spec, isEquivLM_spec (mode := mode) (eager :=
        eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

/-- The eq-true shortcut (the audit's E2) simulates its specification:
one `whnf`, then the store read of the head test. -/
theorem boolTrueShortcutC_spec (ih : SSimC mode eager env f) {d : Nat} {a : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d a) :
    ⦃fun s => s = s₀⦄ boolTrueShortcutI (coreKnotI mode eager (mkFEnv env) f) d a
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (boolTrueShortcut (fueledFns mode eager env) d a) v;
        ⊤⦄ := by
  sym only [conleche_grind, boolTrueShortcut] =>
    vcgen [boolTrueShortcutI, ih.whnf_spec] <;> finish

/-- `proofIrrelI` simulates its fueled original. -/
theorem proofIrrelC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ proofIrrelI (coreKnotI mode eager (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (proofIrrel (fueledFns mode eager env) d a b) v; ⊤⦄
        := by
  sym only [conleche_grind, proofIrrel] =>
    vcgen [proofIrrelI, ih.inferIO_spec, ih.whnf_spec, isEquivLM_spec (mode := mode) (eager :=
        eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- `etaCertI` simulates its fueled original. -/
theorem etaCertC_spec (ih : SSimC mode eager env f) {d : Nat} {ty₁ body₁ b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwty : Expr.WScoped d ty₁) (hwbody : Expr.WScoped d body₁)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ etaCertI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d ty₁ body₁ b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (etaCert mode (fueledFns mode eager env) env d ty₁ body₁ b) v; ⊤⦄ := by
  sym only [conleche_grind, etaCert] =>
    vcgen [etaCertI, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec, ih.infer_spec,
      inst1M_spec (mode := mode) (eager := eager) (env := env)] <;>
      -- the verified arm is seven binds deep, one `Runs.bind_eq` generation each
      finish (gen := 10)

/-- The cached projection-fire check is the spec's (`mkFEnv`). -/
theorem projCertAtF_mkFEnv (env : Env) (v : Bool) (c : Name) (args : List Expr) :
    projCertAtF (mkFEnv env) v c args = projCertAt env v c args := by
  unfold projCertAtF projCertAt projCertF projCert
  rw [mkFEnv_find?]
  split <;> rfl

/-- `isPropTypeI` simulates its fueled original. -/
theorem isPropTypeC_spec (ih : SSimC mode eager env f) {d : Nat} {T : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d T) :
    ⦃fun s => s = s₀⦄ isPropTypeI (coreKnotI mode eager (mkFEnv env) f) d T
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (isPropType (fueledFns mode eager env) d T) v; ⊤⦄ := by
  sym only [conleche_grind, isPropType] =>
    vcgen [isPropTypeI, ih.inferIO_spec, ih.whnf_spec,
      isEquivLM_spec (mode := mode) (eager := eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;> finish

/-- The field loop of the unit-like test simulates its fueled original,
given the field test's simulation. -/
theorem unitLikeFieldsC_spec (ih : SSimC mode eager env f)
    {ul : Nat → Expr → CheckCM Bool} {ul' : Nat → Expr → FueledM Bool}
    (hul : ∀ {d : Nat} {e : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ ul d e
      ⦃fun v s' => CSOK mode eager env s' ∧ Runs (ul' d e) v; ⊤⦄) :
    ∀ {n d : Nat} {t : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d t →
      ⦃fun s => s = s₀⦄ unitLikeFieldsI (coreKnotI mode eager (mkFEnv env) f) ul n d t
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (unitLikeFields (fueledFns mode eager env) ul' n d t) v; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro d t s₀ hs hw
    sym only [conleche_grind, unitLikeFields] =>
      vcgen [unitLikeFieldsI] <;> finish
  | succ n ihn =>
    intro d t s₀ hs hw
    cases t with
    | forallE dom body =>
      sym only [conleche_grind, unitLikeFields] =>
        vcgen [unitLikeFieldsI, isPropTypeC_spec ih, hul,
          inst1M_spec (mode := mode) (eager := eager) (env := env), ihn] <;> finish
    | _ =>
      simp only [unitLikeFieldsI, unitLikeFields]
      sym only [conleche_grind] => vcgen <;> finish
/-- The index's slot tests are the spec's (`mkFEnv`). -/
theorem towerSlotsAllF_mkFEnv (env : Env) (T : Name) (n : Nat) :
    (mkFEnv env).towerSlotsAllF T n = towerSlotsAll env T n := by
  simp only [FEnv.towerSlotsAllF, towerSlotsAll, mkFEnv_findProj?]
  all_goals rfl

/-- The cached shape read is the spec's (`mkFEnv`). -/
theorem unitLikeShapeF_mkFEnv (env : Env) (w : Expr) :
    unitLikeShapeF (mkFEnv env) w = unitLikeShape env w := by
  unfold unitLikeShapeF unitLikeShape unitFieldTele
  simp only [mkFEnv_find?, mkFEnv_findTable?, Expr.getAppArgsC_spec,
    Expr.instLevelParams_spec, Expr.instantiateListC_spec, Option.map_map]
  rfl

/-- The structure arm of the unit-like test simulates its fueled
original, given the field test's simulation. -/
theorem unitLikeStructC_spec (ih : SSimC mode eager env f) (henv : EnvWF env)
    {ul : Nat → Expr → CheckCM Bool} {ul' : Nat → Expr → FueledM Bool}
    (hul : ∀ {d : Nat} {e : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ ul d e
      ⦃fun v s' => CSOK mode eager env s' ∧ Runs (ul' d e) v; ⊤⦄)
    {d : Nat} {w : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d w) :
    ⦃fun s => s = s₀⦄ unitLikeStructI (coreKnotI mode eager (mkFEnv env) f) ul (mkFEnv env) d w
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (unitLikeStruct (fueledFns mode eager env) ul' env d w) v; ⊤⦄ := by
  unfold unitLikeStructI unitLikeStruct
  rw [unitLikeShapeF_mkFEnv]
  cases hsh : unitLikeShape env w with
  | none => sym only [conleche_grind] => vcgen <;> finish
  | some x =>
    obtain ⟨tele, n⟩ := x
    exact unitLikeFieldsC_spec ih hul hs (unitLikeShape_WScoped henv hw hsh)

/-- The unit-like test simulates its fueled original. -/
theorem unitLikeLoopC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    ∀ {fuel d : Nat} {T : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d T →
      ⦃fun s => s = s₀⦄ unitLikeLoopI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) fuel d T
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (unitLikeLoop (fueledFns mode eager env) env fuel d T) v; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro d T s₀ hs hw
    sym only [conleche_grind, unitLikeLoop] =>
      vcgen [unitLikeLoopI] <;> finish
  | succ fuel ihf =>
    intro d T s₀ hs hw
    sym only [conleche_grind, unitLikeLoop] =>
      vcgen [unitLikeLoopI, ih.whnf_spec,
        inst1M_spec (mode := mode) (eager := eager) (env := env), ihf,
        unitLikeStructC_spec ih henv ihf] <;> finish
/-- `structUnitCertI` simulates its fueled original. -/
theorem structUnitCertC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structUnitCertI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structUnitCert (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structUnitCert] =>
    vcgen [structUnitCertI, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec,
      unitLikeLoopC_spec ih henv] <;> finish
end Walks2

section Walks4

variable {env : Env} {f : Nat}

/-- The cached `.proj` spine (the tower spelling, task #175 W4c). -/
theorem projNodesC_spec (T : Name) (b : Expr) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode eager env s₀ →
      ⦃fun s => s = s₀⦄ projNodesI T b l
      ⦃fun rs s' => CSOK mode eager env s' ∧ rs = projsOf T b l; ⊤⦄ := by
  intro l
  induction l with
  | nil =>
    intro _ _
    sym only [conleche_grind] =>
      vcgen [projNodesI] <;> finish
  | cons _ rest ih =>
    intro _ _
    sym only [conleche_grind] =>
      vcgen [projNodesI, ih] <;> finish

/-- `structEtaCertWithI` simulates its fueled original. -/
theorem structEtaCertWithC_spec (ih : SSimC mode eager env f) {d : Nat} {a b wtb : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (hwwtb : Expr.WScoped d wtb) :
    ⦃fun s => s = s₀⦄
      structEtaCertWithI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b wtb
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaCertWith (fueledFns mode eager env) env d a b wtb) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCertWith,
      towerSlotsAllF_mkFEnv] =>
    vcgen [structEtaCertWithI, isEquivListLM_spec (mode := mode) (eager := eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env), defEqListC_spec ih,
      projNodesC_spec (mode := mode) (eager := eager) (env := env)] <;> finish

/-- The partial-constructor gate reads the same store on both sides. -/
theorem etaCtorPartialC_eq (env : Env) (e : Expr) :
    etaCtorPartialC (mkFEnv env) e = etaCtorPartial env e := by
  unfold etaCtorPartialC etaCtorPartial
  simp only [mkFEnv_find?]
  cases e.getAppFn <;> rfl

/-- `structEtaFullI` simulates its fueled original. -/
theorem structEtaFullC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structEtaFullI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaFull (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaFull] =>
    vcgen [structEtaFullI, ih.inferIO_spec, ih.whnf_spec, structEtaCertWithC_spec ih] <;>
      finish

/-- The η-expansion simulates its fueled original. -/
theorem structEtaExpandC_spec (ih : SSimC mode eager env f) :
    ∀ {k d : Nat} {a b t : Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d a → Expr.WScoped d b → Expr.WScoped d t →
      ⦃fun s => s = s₀⦄ structEtaExpandI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) k d a b t
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaExpand (fueledFns mode eager env) env k d a b t) v; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro d a b t s₀ hs hwa hwb hwt
    sym only [conleche_grind, structEtaExpand] =>
      vcgen [structEtaExpandI, structEtaFullC_spec ih] <;> finish
  | succ k ihk =>
    intro d a b t s₀ hs hwa hwb hwt
    cases t with
    | forallE dom body =>
      sym only [conleche_grind, structEtaExpand] =>
        vcgen [structEtaExpandI, inst1M_spec (mode := mode) (eager := eager) (env := env),
          ihk] <;> finish
    | _ =>
      simp only [structEtaExpandI, structEtaExpand]
      sym only [conleche_grind] => vcgen <;> finish

/-- `structEtaCertI` simulates its fueled original. -/
theorem structEtaCertC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structEtaCertI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaCert (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCert, etaCtorPartialC_eq] =>
    vcgen [structEtaCertI, structEtaFullC_spec ih, ih.inferIO_spec, ih.defeq_spec,
      structEtaExpandC_spec ih] <;> finish

/-- `stuckIrrelI` simulates its fueled original. -/
theorem stuckIrrelC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ stuckIrrelI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (stuckIrrel (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, stuckIrrel] =>
    vcgen [stuckIrrelI, structEtaCertC_spec ih, structUnitCertC_spec ih henv,
      proofIrrelC_spec ih] <;> finish

end Walks4


end ConLeche.Cached
