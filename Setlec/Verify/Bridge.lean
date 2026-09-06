import Setlec.Verify.Disc
import Setlec.Kernel.Checker

/-!
# The cache-refinement bridge, part B: the memoized knot

Memo keys are depth-free and the memo operations run **without any
scope check** (`memoE`/`memoB` in `Setlec/Kernel/TypeCheckerC.lean`):
a cache entry must therefore be consumable at *every* depth at which
its key is well-scoped — `CacheOK` (`Setlec/Verify/Scoped.lean`) backs
each entry by a pure run at one fuel valid at all such depths.  An
entry is created from a run at the ambient depth and transported to
every other well-scoped depth by the depth invariance theorems
(`Setlec/Verify/Deep.lean`, requiring `EnvWF`).

What makes the missing runtime check sound is the **call discipline**
(`Setlec/Verify/Disc.lean`): the conditional simulation (`ScopedSim`)
holds for well-scoped arguments only, and the per-body walks prove
that the cached knot never invokes a memoized entry point on an
ill-scoped argument — a disciplined body run is verbatim a run at the
guarded record `gFns`, to which the pair battery applies.  The knot
induction below ties the two: at each fuel level, the entry points
simulate the pure fueled families on well-scoped arguments
(`scopedSim`).  The interned entry-point bridges
(`cachedOps_*_bridge`) went with the arena (task #172)
carry `EnvWF env` plus the argument's well-scopedness as hypotheses —
discharged at the consistency layer from the environment model and the
declaration checker's own input validation (raw declarations are
checked closed once, and the core's outputs stay well-scoped).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

open Expr

/-! ## The memoized knot simulates the fueled families -/

theorem cached_whnfCore_sim (env : Env) (henv : EnvWF env) (f : Nat)
    (ih : ScopedSim mode env f)
    {d : Nat} {e : Expr} (hg : e.wscopedB d = true) :
    (simRel mode env).R ((fueledFns mode env).whnfCore d e)
      ((cachedFns mode env (f + 1)).whnfCore d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns mode env (f + 1)).whnfCore d e =
    memoE (·.whnfCore) (fun st mp => { st with whnfCore := mp })
      (fun d e => whnfCoreBody mode (cachedFns mode env f) env d e) d e from rfl]
    at hrun
  have hbody : ∀ v σ', whnfCoreBody mode (cachedFns mode env f) env d e σ =
      .ok (v, σ') →
      (∃ F, whnfCore mode env (F + 1) d e = .ok v) ∧ CacheOK mode env σ' := by
    intro v σ' hb
    have hgb := (whnfCoreBody_disc ih henv (WScoped.of_wscopedB hg)
      σ hσ v σ' hb).1
    have hpair := (whnfCoreBody mode
      (pairFns (fueledFns mode env) (gFns mode env f) (gFns_rel ih))
      env d e).property
    rw [whnfCoreBody_fst_proj, whnfCoreBody_snd_proj] at hpair
    obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ v σ' hgb
    rw [whnfCoreBody_atF] at hF
    exact ⟨⟨F, hF⟩, hσ₁⟩
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.whnfCore[e]? with
  | some r =>
    rw [hl] at hrun
    try dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hall⟩ := hσ.1 e r hl
    exact ⟨⟨F, hall d hg⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    try dsimp only at hrun
    try simp only [StateT.bind] at hrun
    cases hb : whnfCoreBody mode (cachedFns mode env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok pr =>
      obtain ⟨r, σ₁⟩ := pr
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨⟨F, hpure⟩, hσ₁⟩ := hbody r σ₁ hb
      refine ⟨⟨F + 1, hpure⟩, ?_, hσ₁.2.1, hσ₁.2.2.1, hσ₁.2.2.2.1,
        hσ₁.2.2.2.2.1, hσ₁.2.2.2.2.2⟩
      intro e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : e == e'
      · rw [if_pos hk] at hl'
        obtain rfl : e = e' := eq_of_beq hk
        obtain rfl : r = r' := by injection hl'
        refine ⟨F + 1, fun d' hd' => ?_⟩
        rw [whnfCore_depth_inv henv (F + 1) hd' hg]
        exact hpure
      · rw [if_neg hk] at hl'
        exact hσ₁.1 e' r' hl'

theorem cached_whnf_sim (env : Env) (henv : EnvWF env) (f : Nat)
    (ih : ScopedSim mode env f)
    {d : Nat} {e : Expr} (hg : e.wscopedB d = true) :
    (simRel mode env).R ((fueledFns mode env).whnf d e)
      ((cachedFns mode env (f + 1)).whnf d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns mode env (f + 1)).whnf d e =
    memoE (·.whnf) (fun st mp => { st with whnf := mp })
      (fun d e => whnfBody (cachedFns mode env f) env d e) d e from rfl]
    at hrun
  have hbody : ∀ v σ', whnfBody (cachedFns mode env f) env d e σ =
      .ok (v, σ') →
      (∃ F, whnf mode env (F + 1) d e = .ok v) ∧ CacheOK mode env σ' := by
    intro v σ' hb
    have hgb := (whnfBody_disc ih henv (WScoped.of_wscopedB hg)
      σ hσ v σ' hb).1
    have hpair := (whnfBody
      (pairFns (fueledFns mode env) (gFns mode env f) (gFns_rel ih))
      env d e).property
    rw [whnfBody_fst_proj, whnfBody_snd_proj] at hpair
    obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ v σ' hgb
    rw [whnfBody_atF] at hF
    exact ⟨⟨F, hF⟩, hσ₁⟩
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.whnf[e]? with
  | some r =>
    rw [hl] at hrun
    try dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hall⟩ := hσ.2.1 e r hl
    exact ⟨⟨F, hall d hg⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    try dsimp only at hrun
    try simp only [StateT.bind] at hrun
    cases hb : whnfBody (cachedFns mode env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok pr =>
      obtain ⟨r, σ₁⟩ := pr
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨⟨F, hpure⟩, hσ₁⟩ := hbody r σ₁ hb
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, ?_, hσ₁.2.2.1, hσ₁.2.2.2.1,
        hσ₁.2.2.2.2.1, hσ₁.2.2.2.2.2⟩
      intro e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : e == e'
      · rw [if_pos hk] at hl'
        obtain rfl : e = e' := eq_of_beq hk
        obtain rfl : r = r' := by injection hl'
        refine ⟨F + 1, fun d' hd' => ?_⟩
        rw [whnf_depth_inv henv (F + 1) hd' hg]
        exact hpure
      · rw [if_neg hk] at hl'
        exact hσ₁.2.1 e' r' hl'

theorem cached_infer_sim (env : Env) (henv : EnvWF env) (f : Nat)
    (ih : ScopedSim mode env f)
    {d : Nat} {e : Expr} (hg : e.wscopedB d = true) :
    (simRel mode env).R ((fueledFns mode env).infer d e)
      ((cachedFns mode env (f + 1)).infer d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns mode env (f + 1)).infer d e =
    memoE (·.infer) (fun st mp => { st with infer := mp })
      (fun d e => inferBody mode (cachedFns mode env f) env d e) d e from rfl]
    at hrun
  have hbody : ∀ v σ', inferBody mode (cachedFns mode env f) env d e σ =
      .ok (v, σ') →
      (∃ F, inferTypeCore mode env (F + 1) d e = .ok v) ∧ CacheOK mode env σ' := by
    intro v σ' hb
    have hgb := (inferBody_disc ih henv (WScoped.of_wscopedB hg)
      σ hσ v σ' hb).1
    have hpair := (inferBody mode
      (pairFns (fueledFns mode env) (gFns mode env f) (gFns_rel ih))
      env d e).property
    rw [inferBody_fst_proj, inferBody_snd_proj] at hpair
    obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ v σ' hgb
    rw [inferBody_atF] at hF
    exact ⟨⟨F, hF⟩, hσ₁⟩
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.infer[e]? with
  | some r =>
    rw [hl] at hrun
    try dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hall⟩ := hσ.2.2.1 e r hl
    exact ⟨⟨F, hall d hg⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    try dsimp only at hrun
    try simp only [StateT.bind] at hrun
    cases hb : inferBody mode (cachedFns mode env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok pr =>
      obtain ⟨r, σ₁⟩ := pr
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨⟨F, hpure⟩, hσ₁⟩ := hbody r σ₁ hb
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, ?_, hσ₁.2.2.2.1,
        hσ₁.2.2.2.2.1, hσ₁.2.2.2.2.2⟩
      intro e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : e == e'
      · rw [if_pos hk] at hl'
        obtain rfl : e = e' := eq_of_beq hk
        obtain rfl : r = r' := by injection hl'
        refine ⟨F + 1, fun d' hd' => ?_⟩
        rw [inferTypeCore_depth_inv henv (F + 1) hd' hg]
        exact hpure
      · rw [if_neg hk] at hl'
        exact hσ₁.2.2.1 e' r' hl'

theorem cached_annotate_sim (env : Env) (henv : EnvWF env) (f : Nat)
    (ih : ScopedSim mode env f)
    {d : Nat} {e : Expr} (hg : e.wscopedB d = true) :
    (simRel mode env).R ((fueledFns mode env).annotate d e)
      ((cachedFns mode env (f + 1)).annotate d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns mode env (f + 1)).annotate d e =
    memoE (·.annot) (fun st mp => { st with annot := mp })
      (fun d e => annotateBody (cachedFns mode env f) env d e) d e from rfl]
    at hrun
  have hbody : ∀ v σ', annotateBody (cachedFns mode env f) env d e σ =
      .ok (v, σ') →
      (∃ F, annotateCore mode env (F + 1) d e = .ok v) ∧ CacheOK mode env σ' := by
    intro v σ' hb
    have hgb := (annotateBody_disc ih henv (WScoped.of_wscopedB hg)
      σ hσ v σ' hb).1
    have hpair := (annotateBody
      (pairFns (fueledFns mode env) (gFns mode env f) (gFns_rel ih))
      env d e).property
    rw [annotateBody_fst_proj, annotateBody_snd_proj] at hpair
    obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ v σ' hgb
    rw [annotateBody_atF] at hF
    exact ⟨⟨F, hF⟩, hσ₁⟩
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.annot[e]? with
  | some r =>
    rw [hl] at hrun
    try dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hall⟩ := hσ.2.2.2.2.1 e r hl
    exact ⟨⟨F, hall d hg⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    try dsimp only at hrun
    try simp only [StateT.bind] at hrun
    cases hb : annotateBody (cachedFns mode env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok pr =>
      obtain ⟨r, σ₁⟩ := pr
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨⟨F, hpure⟩, hσ₁⟩ := hbody r σ₁ hb
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, hσ₁.2.2.1,
        hσ₁.2.2.2.1, ?_, hσ₁.2.2.2.2.2⟩
      intro e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : e == e'
      · rw [if_pos hk] at hl'
        obtain rfl : e = e' := eq_of_beq hk
        obtain rfl : r = r' := by injection hl'
        refine ⟨F + 1, fun d' hd' => ?_⟩
        rw [annotateCore_depth_inv henv (F + 1) hd' hg]
        exact hpure
      · rw [if_neg hk] at hl'
        exact hσ₁.2.2.2.2.1 e' r' hl'

theorem cached_defeq_sim (env : Env) (henv : EnvWF env) (f : Nat)
    (ih : ScopedSim mode env f)
    {d : Nat} {a b : Expr} (hga : a.wscopedB d = true)
    (hgb : b.wscopedB d = true) :
    (simRel mode env).R ((fueledFns mode env).defeq d a b)
      ((cachedFns mode env (f + 1)).defeq d a b) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns mode env (f + 1)).defeq d a b =
    memoB (fun d a b => defeqBody mode (cachedFns mode env f) env d a b) d a b
      from rfl] at hrun
  have hbody : ∀ v σ', defeqBody mode (cachedFns mode env f) env d a b σ =
      .ok (v, σ') →
      (∃ F, isDefEqCore mode env (F + 1) d a b = .ok v) ∧ CacheOK mode env σ' := by
    intro v σ' hb
    have hgbody := (defeqBody_disc ih henv (WScoped.of_wscopedB hga)
      (WScoped.of_wscopedB hgb) σ hσ v σ' hb).1
    have hpair := (defeqBody mode
      (pairFns (fueledFns mode env) (gFns mode env f) (gFns_rel ih))
      env d a b).property
    rw [defeqBody_fst_proj, defeqBody_snd_proj] at hpair
    obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ v σ' hgbody
    rw [defeqBody_atF] at hF
    exact ⟨⟨F, hF⟩, hσ₁⟩
  simp only [memoB, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.defeq[((a, b) : Expr × Expr)]? with
  | some r =>
    rw [hl] at hrun
    try dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hall⟩ := hσ.2.2.2.1 a b r hl
    exact ⟨⟨F, hall d hga hgb⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    try dsimp only at hrun
    try simp only [StateT.bind] at hrun
    cases hb : defeqBody mode (cachedFns mode env f) env d a b σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok pr =>
      obtain ⟨r, σ₁⟩ := pr
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨⟨F, hpure⟩, hσ₁⟩ := hbody r σ₁ hb
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, hσ₁.2.2.1, ?_,
        hσ₁.2.2.2.2.1, hσ₁.2.2.2.2.2⟩
      intro a' b' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : ((a, b) : Expr × Expr) == (a', b')
      · rw [if_pos hk] at hl'
        obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by
          have := eq_of_beq hk
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        obtain rfl : r = r' := by injection hl'
        refine ⟨F + 1, fun d' hda' hdb' => ?_⟩
        rw [isDefEqCore_depth_inv henv (F + 1) hda' hdb' hga hgb]
        exact hpure
      · rw [if_neg hk] at hl'
        exact hσ₁.2.2.2.1 a' b' r' hl'

/-- **The io slot's memo step** (task #172 B4).  At a gate-off mode the
slot is the full-inference memo closure, verbatim — one memo, the
task-#170 R clause — so the infer step's simulation transports across
`inferTypeIO_off`.  At the gated mode it is the io body under its own
memo (`KCache.inferIO`), and the proof is `cached_infer_sim`'s shape
with the io walk (`inferBodyIO_disc`), the io pair projections, the io
`atF`, and the io depth invariance. -/
theorem cached_inferIO_sim (env : Env) (henv : EnvWF env) (f : Nat)
    (ih : ScopedSim mode env f)
    {d : Nat} {e : Expr} (hg : e.wscopedB d = true) :
    (simRel mode env).R ((fueledFns mode env).inferIO d e)
      ((cachedFns mode env (f + 1)).inferIO d e) := by
  cases hgb : mode.betaGate with
  | false =>
    have hio : (cachedFns mode env (f + 1)).inferIO =
        (cachedFns mode env (f + 1)).infer := by
      show (if mode.betaGate then _ else _) = _
      rw [if_neg (by simp [hgb])]
      rfl
    rw [hio]
    intro σ hσ v σ' hrun
    obtain ⟨⟨F, hF⟩, hσ'⟩ :=
      cached_infer_sim env henv f ih hg σ hσ v σ' hrun
    refine ⟨⟨F, ?_⟩, hσ'⟩
    show inferTypeIO mode env F d e = .ok v
    rw [inferTypeIO_off hgb]
    exact hF
  | true =>
    have hio : (cachedFns mode env (f + 1)).inferIO =
        memoE (·.inferIO) (fun st mp => { st with inferIO := mp })
          (fun d e => inferBodyIO mode
            (CoreFns.ioView (cachedFns mode env f)) env d e) := by
      show (if mode.betaGate then _ else _) = _
      rw [if_pos hgb]
      congr 1
      funext d' e'
      exact if_pos hgb
    rw [hio]
    intro σ hσ v σ' hrun
    have hbody : ∀ v σ',
        inferBodyIO mode (CoreFns.ioView (cachedFns mode env f)) env d e σ =
          .ok (v, σ') →
        (∃ F, inferTypeIO mode env (F + 1) d e = .ok v) ∧
          CacheOK mode env σ' := by
      intro v σ' hb
      have hgbody := (inferBodyIO_disc ih henv (WScoped.of_wscopedB hg)
        σ hσ v σ' hb).1
      have hpair := (inferBodyIO mode
        (pairFns (CoreFns.ioView (fueledFns mode env))
          (CoreFns.ioView (gFns mode env f)) (gFns_rel ih).ioView)
        env d e).property
      rw [inferBodyIO_fst_proj, inferBodyIO_snd_proj] at hpair
      obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ v σ' hgbody
      rw [inferBodyIO_atF] at hF
      refine ⟨⟨F, ?_⟩, hσ₁⟩
      rw [inferTypeIO_succ, hgb, if_pos rfl]
      exact hF
    simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
    cases hl : σ.inferIO[e]? with
    | some r =>
      rw [hl] at hrun
      try dsimp only at hrun
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      obtain ⟨F, hall⟩ := hσ.2.2.2.2.2 e r hl
      exact ⟨⟨F, hall d hg⟩, hσ⟩
    | none =>
      rw [hl] at hrun
      try dsimp only at hrun
      try simp only [StateT.bind] at hrun
      cases hb : inferBodyIO mode
          (CoreFns.ioView (cachedFns mode env f)) env d e σ with
      | error err =>
        rw [hb] at hrun
        simp only [Bind.bind, Except.bind] at hrun
        exact nomatch hrun
      | ok pr =>
        obtain ⟨r, σ₁⟩ := pr
        rw [hb] at hrun
        simp only [Bind.bind, Except.bind, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
          Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨⟨F, hpure⟩, hσ₁⟩ := hbody r σ₁ hb
        refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, hσ₁.2.2.1, hσ₁.2.2.2.1,
          hσ₁.2.2.2.2.1, ?_⟩
        intro e' r' hl'
        simp only at hl'
        rw [Std.HashMap.getElem?_insert] at hl'
        by_cases hk : e == e'
        · rw [if_pos hk] at hl'
          obtain rfl : e = e' := eq_of_beq hk
          obtain rfl : r = r' := by injection hl'
          refine ⟨F + 1, fun d' hd' => ?_⟩
          rw [inferTypeIO_depth_inv henv (F + 1) hd' hg]
          exact hpure
        · rw [if_neg hk] at hl'
          exact hσ₁.2.2.2.2.2 e' r' hl'

/-- The memoized knot simulates the fueled families at every level, on
well-scoped arguments (well-formed environments). -/
theorem scopedSim (env : Env) (henv : EnvWF env) :
    ∀ f, ScopedSim mode env f
  | 0 =>
    { whnfCore := fun {_ _} _ _ _ _ _ hrun => nomatch hrun
      whnf := fun {_ _} _ _ _ _ _ hrun => nomatch hrun
      infer := fun {_ _} _ _ _ _ _ hrun => nomatch hrun
      defeq := fun {_ _ _} _ _ _ _ _ _ hrun => nomatch hrun
      annotate := fun {_ _} _ _ _ _ _ hrun => nomatch hrun
      inferIO := fun {_ _} _ _ _ _ _ hrun => nomatch hrun }
  | f + 1 =>
    { whnfCore := fun hg =>
        cached_whnfCore_sim env henv f (scopedSim env henv f) hg
      whnf := fun hg =>
        cached_whnf_sim env henv f (scopedSim env henv f) hg
      infer := fun hg =>
        cached_infer_sim env henv f (scopedSim env henv f) hg
      defeq := fun hga hgb =>
        cached_defeq_sim env henv f (scopedSim env henv f) hga hgb
      annotate := fun hg =>
        cached_annotate_sim env henv f (scopedSim env henv f) hg
      inferIO := fun hg =>
        cached_inferIO_sim env henv f (scopedSim env henv f) hg }

end Setlec
