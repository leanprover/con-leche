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

/-- `structUnitCertI` simulates its fueled original. -/
theorem structUnitCertC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structUnitCertI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structUnitCert (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structUnitCert] =>
    vcgen [structUnitCertI, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec] <;> finish

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

/-- The index's slot tests are the spec's (`mkFEnv`). -/
theorem towerSlotsAllF_mkFEnv (env : Env) (T : Name) (n : Nat) :
    (mkFEnv env).towerSlotsAllF T n = towerSlotsAll env T n := by
  simp only [FEnv.towerSlotsAllF, towerSlotsAll, mkFEnv_findProj?]
  all_goals rfl

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

/-- `structEtaCertI` simulates its fueled original. -/
theorem structEtaCertC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structEtaCertI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaCert (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCert] =>
    vcgen [structEtaCertI, ih.inferIO_spec, ih.whnf_spec, structEtaCertWithC_spec ih] <;>
      finish

/-- `stuckIrrelI` simulates its fueled original. -/
theorem stuckIrrelC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ stuckIrrelI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (stuckIrrel (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, stuckIrrel] =>
    vcgen [stuckIrrelI, structEtaCertC_spec ih, structUnitCertC_spec ih,
      proofIrrelC_spec ih] <;> finish

end Walks4

end ConLeche.Cached
