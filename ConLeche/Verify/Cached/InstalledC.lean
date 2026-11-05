module

import ConLeche.Verify.Cached.BridgeC
public import ConLeche.Cached.Installed
public import ConLeche.Verify.Cached.Grind
public import ConLeche.Verify.BridgeDecl
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.Cached.ParInstall
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# Phase A's steps simulate the pure guards and value check

`FullyChecked μ ds` (`ConLeche/Cached/Installed.lean`) is what the
driver's two loops assemble: phase A's accepting run (`InstallRun`)
installs a value declaration by its guards and records its datum, and every record was checked against the prefix view
`fe.restrictTo vis` from a fresh memo state (`GroupChecked`).  This
module holds the model-free half of the walk over that run:

* `headerGuardsC_spec` / `valueGuardsC_spec` / `valueDeclGuardsC_spec` —
  phase A's guards are the pure ones
  (`headerGuards`, `valueGuards`, `ConLeche/Kernel/ValueCheck.lean`).
* `checkPending_spec` — the check at the prefix view simulates the pure
  value check `checkValueGroup` at the truncated environment.  The view
  and `mkFEnv` of the truncated environment have the same `find?`
  (`mkFEnv_find?_visibleBelow`, under the name uniqueness every driver
  step preserves — `PushChain`), so by `coreKnotI_congr` they run the
  SAME core, and the simulation stated at `mkFEnv env` covers the check
  at the view.

The walks are `Std.WP` triples proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`); the `…_run` forms the model's walk
consumes read a triple on one run, at a fuel (`…_datF`).

The walk itself — the model carried along the run, and the letters on
the fully checked environment — is `ConLeche/Model/InstallRun.lean`:
it needs the model's well-formedness at every step, so it stands above
the model lane (`tests/layering.sh`).
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open Std.WP
open scoped Lean.Order

variable {μ : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## The flush -/

/-- The per-declaration flush re-establishes the invariant at any
environment, from the residue. -/
theorem flushC_spec {env : Env} {s₀ : CState} (hres : CSOKF s₀) :
    ⦃fun s => s = s₀⦄ flushC ⦃fun _ s' => CSOK μ false env s'; ⊤⦄ :=
  triple_iff_run.mpr fun _ _ h => by
    rw [flushC_run] at h
    cases h
    exact flushC_csok hres

/-! ## The install halves at fuel `F` -/

theorem headerGuards_datF (env : Env) (cv : ConstantVal) (F : Nat) :
    (headerGuards (m := FueledM) env cv).val F = headerGuards (m := CheckM) env cv := by
  simp only [headerGuards, FueledM.atF_bind, FueledM.atF_ite, FueledM.atF_pure,
    FueledM.atF_throw]

theorem valueGuards_datF (env : Env) (cv : ConstantVal) (value : Expr) (F : Nat) :
    (valueGuards (m := FueledM) env cv value).val F
      = valueGuards (m := CheckM) env cv value := by
  simp only [valueGuards, FueledM.atF_bind, FueledM.atF_ite, FueledM.atF_pure,
    FueledM.atF_throw]

theorem checkValueGroup_datF (env : Env) (g : ValueGroup) (F : Nat) :
    (checkValueGroup (fueledOpsM μ) env g).val F = checkValueGroup (fueledOps μ F) env g := by
  simp only [checkValueGroup, FueledM.atF_bind, FueledM.atF_ite, FueledM.atF_pure,
    FueledM.atF_throw, valueGuards_datF, liftFueled_atF, fueledOpsM_inferType_atF,
    fueledOpsM_ensureSort_atF, fueledOpsM_isDefEq_atF]

/-! ## The two-phase driver: phase A's install halves -/

/-- Phase A's header install is the pure install half: from an
invariant state at `mkFEnv env`, a successful run is the fueled
`headerGuards`'s, and the header's type is well scoped. -/
theorem headerGuardsC_spec {env : Env} {cv : ConstantVal} {s₀ : CState}
    (hs : CSOK μ false env s₀) :
    ⦃fun s => s = s₀⦄ headerGuardsC (mkFEnv env) cv
    ⦃fun v s' => CSOK μ false env s' ∧
      Runs (headerGuards (m := FueledM) env cv) v ∧ Expr.WScoped 0 cv.type; ⊤⦄ := by
  sym only [conleche_grind, headerGuards.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 cv.type] =>
    vcgen [headerGuardsC] <;> finish

/-- Phase A's value install is the pure install half. -/
theorem valueGuardsC_spec {env : Env} {cv : ConstantVal} {value : Expr} {s₀ : CState}
    (hs : CSOK μ false env s₀) :
    ⦃fun s => s = s₀⦄ valueGuardsC (mkFEnv env) cv value
    ⦃fun v s' => CSOK μ false env s' ∧
      Runs (valueGuards (m := FueledM) env cv value) v ∧ Expr.WScoped 0 value; ⊤⦄ := by
  sym only [conleche_grind, valueGuards.eq_1, Expr.allLevelParamsDefinedC_spec,
      constsResolveFC_spec, constsResolveF_eq, @wscoped_of_hasFvar_false 0 value] =>
    vcgen [valueGuardsC] <;> finish

/-- `headerGuardsC_spec` on a run, at the install half's `CheckM`
instance (`ConLeche/Model/InstallRun.lean`). -/
theorem headerGuardsC_run {env : Env}
    {cv : ConstantVal} {s₀ s' : CState} (hs : CSOK μ false env s₀)
    (h : headerGuardsC (mkFEnv env) cv s₀ = .ok ((), s')) :
    CSOK μ false env s' ∧ Expr.WScoped 0 cv.type ∧
    headerGuards (m := CheckM) env cv = .ok () := by
  obtain ⟨hs', ⟨F, hF⟩, hw⟩ := triple_iff_run.mp (headerGuardsC_spec hs) _ _ h
  exact ⟨hs', hw, headerGuards_datF env cv F ▸ hF⟩

/-- Phase A's value install: the flush, then the two install halves. -/
theorem valueDeclGuardsC_spec {env : Env} {cv : ConstantVal} {value : Expr} {s₀ : CState}
    (hres : CSOKF s₀) :
    ⦃fun s => s = s₀⦄ valueDeclGuardsC (mkFEnv env) cv value
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs (headerGuards (m := FueledM) env cv) () ∧
      Runs (valueGuards (m := FueledM) env cv value) v ∧
      Expr.WScoped 0 cv.type ∧ Expr.WScoped 0 value; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [valueDeclGuardsC, flushC_spec (μ := .verified) (env := env) hres,
      headerGuardsC_spec (μ := .verified), valueGuardsC_spec (μ := .verified)] <;>
      finish

/-- Phase A's value install, run: the two install halves, the header
and the value as declared and well scoped, the residue kept. -/
theorem valueDeclGuardsC_run {env : Env}
    {cv : ConstantVal} {value : Expr} {s₀ s' : CState}
    (hres : CSOKF s₀)
    (h : valueDeclGuardsC (mkFEnv env) cv value s₀ = .ok ((), s')) :
    CSOKF s' ∧
    Expr.WScoped 0 cv.type ∧ Expr.WScoped 0 value ∧
    headerGuards (m := CheckM) env cv = .ok () ∧
    valueGuards (m := CheckM) env cv value = .ok () := by
  obtain ⟨hs', ⟨F₁, hF₁⟩, ⟨F₂, hF₂⟩, hwty, hwv⟩ :=
    triple_iff_run.mp (valueDeclGuardsC_spec hres) _ _ h
  exact ⟨hs'.residue, hwty, hwv, headerGuards_datF env cv F₁ ▸ hF₁,
    valueGuards_datF env cv value F₂ ▸ hF₂⟩

/-! ## The two-phase driver: phase B's check at the prefix view -/

/-- Phase B's check at the prefix view simulates the pure check half at
the environment the view names: the view and `mkFEnv env` have the same
`find?`, so by `coreKnotI_congr` the check runs the core the
simulation is stated about.  A theorem's value arrives unchecked and
its guards run here (`valueGuardsC` at the view, `valueGuardsC_congr`), so
the well-scopedness premise on the value is asked only of the other two
kinds. -/
theorem checkPending_spec {env : Env} (henv : EnvWF env)
    {feFinal : FEnv} {pc : PendingCheck}
    (hfind : ∀ n, (feFinal.restrictTo pc.vis).find? n = env.find? n)
    (htab : ∀ T, (feFinal.restrictTo pc.vis).findTable? T = env.findTable? T)
    (hwty : Expr.WScoped 0 pc.vg.cv.type)
    (hwv : pc.vg.kind ≠ .thm → Expr.WScoped 0 pc.vg.jv)
    {s₀ : CState} (hres : CSOKF s₀) :
    ⦃fun s => s = s₀⦄ checkPending .verified feFinal pc
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs (checkValueGroup (fueledOpsM .verified) env pc.vg) v; ⊤⦄ := by
  have hfe : (feFinal.restrictTo pc.vis).find? = (mkFEnv env).find? :=
    funext fun n => (hfind n).trans (mkFEnv_find? env n).symm
  have htb : (feFinal.restrictTo pc.vis).findTable? = (mkFEnv env).findTable? :=
    funext fun T => (htab T).trans (mkFEnv_findTable? env T).symm
  -- the view runs the core at `mkFEnv env` (structural: the congruence
  -- is an equation of programs, ahead of the walk)
  simp only [checkPending, coreKnotI_congr hfe htb, opSIxC_congr hfe htb,
    valueGuardsC_congr hfe]
  clear hfind hfe htab htb
  sym only [conleche_grind, checkValueGroup.eq_1] =>
    vcgen [flushC_spec (μ := .verified) (env := env) hres, inferK_spec henv, opSIxC_spec henv,
      liftFueled_spec (mode := .verified) (eager := false) (env := env), valueGuardsC_spec (μ := .verified),
      defeqK_spec henv] <;> finish

/-- `checkPending_spec` on a run, at a fuel. -/
theorem checkPending_run {env : Env} (henv : EnvWF env)
    {feFinal : FEnv} {pc : PendingCheck}
    (hfind : ∀ n, (feFinal.restrictTo pc.vis).find? n = env.find? n)
    (htab : ∀ T, (feFinal.restrictTo pc.vis).findTable? T = env.findTable? T)
    (hwty : Expr.WScoped 0 pc.vg.cv.type)
    (hwv : pc.vg.kind ≠ .thm → Expr.WScoped 0 pc.vg.jv)
    {s₀ s' : CState} (hres : CSOKF s₀)
    (h : checkPending .verified feFinal pc s₀ = .ok ((), s')) :
    CSOKF s' ∧ ∃ F, checkValueGroup (fueledOps .verified F) env pc.vg = .ok () := by
  obtain ⟨hs', F, hF⟩ :=
    triple_iff_run.mp (checkPending_spec henv hfind htab hwty hwv hres) _ _ h
  exact ⟨hs'.residue, F, checkValueGroup_datF env pc.vg F ▸ hF⟩

/-- The lookup at the prefix view of a canonical, name-unique index whose
environment extends `env` by exactly the constants above `env`'s
length is `env`'s lookup. -/
theorem restrictTo_find?_of_extends {feFinal : FEnv} {env : Env}
    (hcanon : feFinal = mkFEnv feFinal.env) (hnd : NodupNames feFinal.env)
    {new : List ConstantInfo} (hext : feFinal.env.consts = new ++ env.consts) (n : Name) :
    (feFinal.restrictTo env.consts.length).find? n = env.find? n := by
  have h1 : (feFinal.restrictTo env.consts.length).find? n
      = ((mkFEnv feFinal.env).restrictTo env.consts.length).find? n := by
    rw [← hcanon]
  rw [h1, mkFEnv_find?_visibleBelow feFinal.env env.consts.length n hnd]
  unfold Env.find?
  rw [Env.prefixTo_consts_of_extends hext]

/-- The table lookup at the prefix view of a canonical, name-unique
index whose environment extends `env` by constants above `env`'s length
and by tables of structures not in `env` is `env`'s (task #362). -/
theorem restrictTo_findTable?_of_extends {feFinal : FEnv} {env : Env}
    (hcanon : feFinal = mkFEnv feFinal.env) (hnd : NodupNames feFinal.env)
    {new : List ConstantInfo} (hext : feFinal.env.consts = new ++ env.consts)
    {newQ : List ProjTable} (hextT : feFinal.env.tables = newQ ++ env.tables)
    (hfresh : ∀ t ∈ newQ, env.find? t.structName = none) (T : Name) :
    (feFinal.restrictTo env.consts.length).findTable? T = env.findTable? T := by
  have h1 : (feFinal.restrictTo env.consts.length).findTable? T
      = ((mkFEnv feFinal.env).restrictTo env.consts.length).findTable? T := by
    rw [← hcanon]
  rw [h1, mkFEnv_findTable?_visibleBelow feFinal.env env.consts.length T hnd]
  have hf : (feFinal.env.prefixTo env.consts.length).find? T = env.find? T := by
    unfold Env.find?
    rw [Env.prefixTo_consts_of_extends hext]
  unfold Env.findTable?
  rw [hf]
  split
  · next hT =>
    rw [Env.prefixTo_tables, hextT, List.find?_append]
    have : newQ.find? (·.structName == T) = none := by
      rw [List.find?_eq_none]
      intro t ht hq
      have hn : t.structName = T := by simpa using hq
      have := hfresh t ht
      rw [hn] at this
      rw [this] at hT
      exact absurd hT (by simp)
    rw [this, Option.none_or]
  · rfl

end ConLeche.Cached
