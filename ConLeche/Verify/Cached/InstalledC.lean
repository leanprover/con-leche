module

import ConLeche.Verify.Cached.BridgeC
public import ConLeche.Cached.Installed
public import ConLeche.Verify.Cached.SimC
public import ConLeche.Verify.EnvBound
import ConLeche.Verify.Cached.KnotCongr
import ConLeche.Verify.CheckerSplit

public section

/-!
# Phase A's steps simulate the pure install and check halves

`FullyChecked μ ds` (`ConLeche/Cached/Installed.lean`) is what the
driver's two loops assemble: phase A's accepting run (`InstallRun`)
installs a separable value declaration by the install half and records
its datum, and every record was checked against the prefix view
`fe.restrictTo vis` from a fresh memo state (`GroupChecked`).  This
module holds the model-free half of the walk over that run:

* `annotConstantValC_run` / `annotValC_run` / `annotValueC_run` — phase
  A's install simulates the pure install halves
  (`installConstantVal`, `installValue`, `ConLeche/Kernel/CheckerSplit.lean`).
* `checkPending_run` — the check at the prefix view simulates the pure
  check half `checkValueGroup` at the truncated environment.  The view
  and `mkFEnv` of the truncated environment have the same `find?`
  (`mkFEnv_find?_visibleBelow`, under the name uniqueness every driver
  step preserves — `PushChain`), so by `coreKnotI_congr` they run the
  SAME core, and the simulation stated at `mkFEnv env` covers the check
  at the view.

The walk itself — the model carried along the run, and the letters on
the fully checked environment — is `ConLeche/Model/InstallRun.lean`:
it needs the model's well-formedness at every step, so it stands above
the model lane (`tests/layering.sh`).
-/

namespace ConLeche.Cached

open ConLeche

variable {μ : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## The two-phase driver: phase A's install halves -/

/-- Phase A's header install simulates the pure install half: from an
invariant state at `mkFEnv env`, a successful run returns the header
with its annotated type, well scoped, and `installConstantVal` succeeds
on it at some fuel. -/
theorem annotConstantValC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cv cvA : ConstantVal} {jty : Expr} {s₀ s' : CState} (hs : CSOK μ env s₀)
    (h : annotConstantValC μ (mkFEnv env) cv s₀ = .ok ((cvA, jty), s')) :
    CSOK μ env s' ∧ cvA = { cv with type := jty } ∧ Expr.WScoped 0 jty ∧
    ∃ F, installConstantVal (fueledOps μ F) env cv = .ok cvA := by
  unfold annotConstantValC at h
  simp only [mkFEnv_find?] at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; exact absurd h throwC_bind_ok
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; exact absurd h throwC_bind_ok
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; exact absurd h throwC_bind_ok
  rw [if_pos h5] at h
  rw [hasFvar_spec' rfl] at h
  by_cases h6 : Expr.hasFvar cv.type = true
  · rw [if_pos h6] at h; exact absurd h throwC_bind_ok
  rw [if_neg h6] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  obtain ⟨hs₁, w, ⟨hjA, hwty⟩, F, hF⟩ :=
    (ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)) jA s₁ hann
  obtain rfl := hjA
  rw [Expr.allLevelParamsDefinedC_spec] at h
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams jA = true
  case neg => rw [if_neg h7] at h; exact absurd h throwC_bind_ok
  rw [if_pos h7] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h8 : Expr.constsResolve env jA = true
  case neg => rw [if_neg h8] at h; exact absurd h throwC_bind_ok
  rw [if_pos h8] at h
  obtain ⟨hv, rfl⟩ := pureC_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hv
  refine ⟨hs₁, rfl, hwty, F, ?_⟩
  exact installConstantVal_of_facts (Option.not_isSome_iff_eq_none.mp h1)
    (by simpa using h2) (by simpa using h3) h4 h5 (by simpa using h6) hF h7 h8

/-- Phase A's value install simulates the pure install half. -/
theorem annotValC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {jty value jv : Expr} {record : Bool} {s₀ s' : CState}
    (hjty : jty = cvA.type) (hs : CSOK μ env s₀)
    (h : annotValC μ (mkFEnv env) cvA jty value record s₀ = .ok (jv, s')) :
    CSOK μ env s' ∧ Expr.WScoped 0 jv ∧
    ∃ F, installValue (fueledOps μ F) env cvA value = .ok jv := by
  unfold annotValC at h
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => rw [if_neg h1] at h; exact absurd h throwC_bind_ok
  rw [if_pos h1] at h
  rw [hasFvar_spec' rfl] at h
  by_cases h2 : Expr.hasFvar value = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  obtain ⟨hs₁, w, ⟨hjA, hwv⟩, F, hF⟩ :=
    (ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)) jA s₁ hann
  obtain rfl := hjA
  rw [Expr.allLevelParamsDefinedC_spec] at h
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams jA = true
  case neg => rw [if_neg h3] at h; exact absurd h throwC_bind_ok
  rw [if_pos h3] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h4 : Expr.constsResolve env jA = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  obtain ⟨u, s₂, hrec, h⟩ := bindC_ok h
  obtain ⟨hs₂, -⟩ := recordCConst_eff hs₁ (hjty ▸ rfl)
    (fun vE vi hv => by
      cases record <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv
      · exact nomatch hv
      · cases hv; rfl) u s₂ hrec
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  exact ⟨hs₂, hwv, F, installValue_of_facts h1 (by simpa using h2) hF h3 h4⟩

/-! ## The two-phase driver: phase B's check at the prefix view -/

/-- `annotValC` reads its index through `find?` alone (the knot and
`constsResolveFC`), so it is congruent in the index: phase B's
annotation of a theorem's value at the prefix view is the annotation
at the environment the view names. -/
theorem annotValC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    annotValC μ fe₁ = annotValC μ fe₂ := by
  funext cvA jty value record
  unfold annotValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe]

/-- Phase B's check at the prefix view simulates the pure check half at
the environment the view names: the view and `mkFEnv env` have the same
`find?`, so by `coreKnotI_congr` the check runs the core the
simulation is stated about.  A theorem's value arrives RAW and is
annotated here (`annotValC` at the view, `annotValC_congr`), so the
well-scopedness premise on the value is asked only of the other two
kinds. -/
theorem checkPending_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {feFinal : FEnv} {pc : PendingCheck}
    (hfind : ∀ n, (feFinal.restrictTo pc.vis).find? n = env.find? n)
    (hwty : Expr.WScoped 0 pc.vg.cvA.type)
    (hwv : pc.vg.kind ≠ .thm → Expr.WScoped 0 pc.vg.jv)
    {s₀ s' : CState} (hres : CSOKF s₀)
    (h : checkPending μ feFinal pc s₀ = .ok ((), s')) :
    CSOKF s' ∧ ∃ F, checkValueGroup (fueledOps μ F) env pc.vg = .ok () := by
  have hfe : (feFinal.restrictTo pc.vis).find? = (mkFEnv env).find? :=
    funext fun n => (hfind n).trans (mkFEnv_find? env n).symm
  unfold checkPending at h
  simp only [coreKnotI_congr hfe, opSIxC_congr hfe, annotValC_congr hfe] at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcs : CSOK μ env s₀.flushed := flushC_csok hres
  obtain ⟨jsty, s₂, hst, h⟩ := bindC_ok h
  obtain ⟨hs₂, wsty, ⟨rfl, hwsty⟩, F₁, hF₁⟩ :=
    (ssimC hμ env henv checkFuel).infer hcs rfl hwty jsty s₂ hst
  obtain ⟨u, s₃, hsort, h⟩ := bindC_ok h
  obtain ⟨hs₃, u', rfl, F₂, hF₂⟩ := opSIxC_sim hμ henv hs₂ rfl hwsty u s₃ hsort
  -- the value's typing, after the theorem test (and a theorem's value
  -- install)
  have tail : ∀ {s₄ : CState} (jv : Expr), CSOK μ env s₄ → Expr.WScoped 0 jv →
      ((coreKnotI μ (mkFEnv env) checkFuel).infer 0 jv >>= fun jvt =>
        (coreKnotI μ (mkFEnv env) checkFuel).defeq 0 jvt pc.vg.cvA.type >>= fun b =>
          if b = true then pure () else
            throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")) s₄
        = .ok ((), s') →
      CSOKF s' ∧ ∃ F jvt, inferTypeCore μ env F 0 jv = .ok jvt ∧
        isDefEqCore μ env F 0 jvt pc.vg.cvA.type = .ok true := by
    intro s₄ jv hs₄ hwjv h
    obtain ⟨jvt, s₅, hvt, h⟩ := bindC_ok h
    obtain ⟨hs₅, wvt, ⟨rfl, hwvt⟩, F₃, hF₃⟩ :=
      (ssimC hμ env henv checkFuel).infer hs₄ rfl hwjv jvt s₅ hvt
    obtain ⟨b, s₆, hde, h⟩ := bindC_ok h
    obtain ⟨hs₆, b', rfl, F₄, hF₄⟩ :=
      (ssimC hμ env henv checkFuel).defeq hs₅ rfl rfl hwvt hwty b s₆ hde
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact nomatch h
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨-, rfl⟩ := pureC_ok h
      exact ⟨hs₆.residue, max F₃ F₄, jvt, inferTypeCore_mono (Nat.le_max_left _ _) hF₃,
        isDefEqCore_mono (Nat.le_max_right _ _) hF₄⟩
  by_cases hk : pc.vg.kind = .thm
  · rw [if_pos hk] at h
    obtain ⟨b, s₄, hlift, h⟩ := bindC_ok h
    obtain ⟨hs₄, b', rfl, F₀, hF₀⟩ := SimC.liftFueled _ _ hs₃ b s₄ hlift
    rw [liftFueled_atF] at hF₀
    cases heqv : Level.isEquiv u .zero with
    | none => rw [heqv] at hF₀; exact nomatch hF₀
    | some b₀ =>
    rw [heqv] at hF₀
    simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at hF₀
    subst hF₀
    cases b₀ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h throwC_bind_ok
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨jv, s₅, hval, h⟩ := bindC_ok h
    obtain ⟨hs₅, hwjv, F₃, hV⟩ := annotValC_run hμ henv rfl hs₄ hval
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail jv hs₅ hwjv h
    refine ⟨hres', max (max (max F₁ F₂) F₃) F₅, ?_⟩
    exact checkValueGroup_of_facts (jv := jv)
      (inferTypeCore_mono (by omega) hF₁)
      (ensureSortCore_mono (by omega) hF₂)
      (fun _ => heqv) (fun _ => installValue_mono (by omega) hV)
      (fun hk' => absurd hk hk')
      (inferTypeCore_mono (by omega) hvt)
      (isDefEqCore_mono (by omega) hde)
  · rw [if_neg hk] at h
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail _ hs₃ (hwv hk) h
    refine ⟨hres', max (max F₁ F₂) F₅, ?_⟩
    exact checkValueGroup_of_facts (jv := pc.vg.jv)
      (inferTypeCore_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hF₁)
      (ensureSortCore_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hF₂)
      (fun hk' => absurd hk' hk) (fun hk' => absurd hk' hk) (fun _ => rfl)
      (inferTypeCore_mono (Nat.le_max_right _ _) hvt)
      (isDefEqCore_mono (Nat.le_max_right _ _) hde)

/-- Phase A's value install, run: the two halves at a common fuel, the
annotated terms well scoped, the residue kept. -/
theorem annotValueC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cv cvA : ConstantVal} {value jty jv : Expr} {record : Bool} {s₀ s' : CState}
    (hres : CSOKF s₀)
    (h : annotValueC μ (mkFEnv env) cv value record s₀ = .ok ((cvA, jty, jv), s')) :
    CSOKF s' ∧ cvA = { cv with type := jty } ∧ Expr.WScoped 0 jty ∧ Expr.WScoped 0 jv ∧
    ∃ F, installConstantVal (fueledOps μ F) env cv = .ok cvA ∧
      installValue (fueledOps μ F) env cvA value = .ok jv := by
  unfold annotValueC at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  obtain ⟨pr, s₂, hcv, h⟩ := bindC_ok h
  obtain ⟨cvA', jty'⟩ := pr
  obtain ⟨hs₂, hcvA, hwty, F₁, hI⟩ := annotConstantValC_run hμ henv (flushC_csok hres) hcv
  obtain ⟨jv', s₃, hv, h⟩ := bindC_ok h
  obtain ⟨hs₃, hwv, F₂, hV⟩ := annotValC_run hμ henv (by rw [hcvA]) hs₂ hv
  obtain ⟨hv, rfl⟩ := pureC_ok h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  exact ⟨hs₃.residue, hcvA, hwty, hwv, max F₁ F₂,
    installConstantVal_mono (Nat.le_max_left _ _) hI, installValue_mono (Nat.le_max_right _ _) hV⟩

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
  rw [h1, mkFEnv_find?_visibleBelow feFinal.env env.consts.length n hnd,
    Env.prefixTo_of_extends hext]

end ConLeche.Cached
