module

public import ConLeche.Verify.Cached.DiscC3
public import ConLeche.Verify.BinderLoop

public section

/-!
# Cached binder-loop walks (task #163)

Simulation walks relating the cached binder-telescope loops
(`inferLamsI`/`inferPisI`, `ConLeche/Cached/CoreC.lean`) to the pure
mirrors (`ConLeche/Verify/BinderLoop.lean`) at the fueled record, plus
the two *tail compositions* against `inferBody`'s own λ/∀ tails.  The
loops are `Std.WP` triples proved by `vcgen` and `grind`, each loop
unfolded by its `eq_def`; the tail
compositions are run-level `SimC`s (`SimC.wp`/`SimC.wr` over the pure
loops' soundness, `inferLams_sound`), read as triples in `DiscC4.lean`.

**The peel fuel is not a parameter of these walks.**  Every loop
theorem quantifies over the fuel, so the constant `peelFuel` is an
instance, and no proof below reads a property of the fuel value.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

variable {env : Env} {f : Nat}

/-! ## The infer-λ loop walks

The cached loops match their term on `.lam`/`.forallE`; the equation
compiler states their successor step as one equation per arm, the
fall-through one conditional, which `vcgen` skips, so each loop is
unfolded by its unconditional `eq_def`, and the pure mirrors' own
equation lemmas go into the `sym` list. -/

theorem inferLamsOutC_spec {d : Nat} :
    ∀ {stk : List Expr} {j : Nat} {cur : Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      ⦃fun s => s = s₀⦄ inferLamsOutI d stk j cur
      ⦃fun v s' => CSOK mode eager env s' ∧ Runs (inferLamsOut (m := FueledM) d stk j cur) v; ⊤⦄ :=
          by
  intro stk
  induction stk with
  | nil =>
    intro _ _ _ _
    sym only [conleche_grind, inferLamsOut.eq_1] => vcgen [inferLamsOutI] <;> finish
  | cons _ rest ih =>
    intro _ _ _ _
    sym only [conleche_grind, inferLamsOut.eq_2] =>
      vcgen [inferLamsOutI, abstractRangeM_spec (mode := mode) (eager := eager) (env := env), ih]
          <;> finish

theorem inferLamsLeafC_spec (ih : SSimC mode eager env f) {d : Nat} {t : Expr} {k : Nat}
    {fvs : Array Expr} {stk : List Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hw : Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse)) :
    ⦃fun s => s = s₀⦄ inferLamsLeafI (coreKnotI mode eager (mkFEnv env) f) d t k fvs stk
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (inferLamsLeaf (fueledFns mode eager env) d t k fvs.toList.reverse stk) v; ⊤⦄ := by
  sym only [conleche_grind, inferLamsLeaf.eq_1] =>
    vcgen [inferLamsLeafI, instListRevM_spec hs, ih.infer_spec,
      abstractRangeM_spec (mode := mode) (eager := eager) (env := env),
      inferLamsOutC_spec (mode := mode) (eager := eager) (env := env)] <;> finish

theorem inferLamsC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Expr} {s₀ : CState},
      CSOK mode eager env s₀ → Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse) →
      ⦃fun s => s = s₀⦄ inferLamsI (coreKnotI mode eager (mkFEnv env) f) d fuel t k fvs stk
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (inferLams (fueledFns mode eager env) d fuel t k fvs.toList.reverse stk) v; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ hs hw
    sym only [conleche_grind, inferLams.eq_3] =>
      vcgen [inferLamsI, inferLamsLeafC_spec ih] <;> finish
  | succ fuel ihFuel =>
    intro _ _ _ _ _ hs hw
    sym only [conleche_grind, inferLams.eq_1, inferLams.eq_2] =>
      vcgen [inferLamsI.eq_def, instListRevM_spec hs, ih.infer_spec, ih.whnf_spec,
        ihFuel, inferLamsLeafC_spec ih] <;> finish

/-! ## The infer-∀ loop walks (task #100 stage 6: the ∀-rule infers
its codomain sort, so the cached side runs a telescope loop) -/

theorem inferPisOutC_spec :
    ∀ {stk : List Level} {v : Level} {s₀ : CState}, CSOK mode eager env s₀ →
      ⦃fun s => s = s₀⦄ inferPisOutI stk v
      ⦃fun r s' => CSOK mode eager env s' ∧ Runs (inferPisOut (m := FueledM) stk v) r; ⊤⦄ := by
  intro stk
  induction stk with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, inferPisOut.eq_1] => vcgen [inferPisOutI] <;> finish
  | cons _ rest ih =>
    intro _ _ _
    sym only [conleche_grind, inferPisOut.eq_2] =>
      vcgen [inferPisOutI, ih] <;> finish

theorem inferPisLeafC_spec (ih : SSimC mode eager env f) {d : Nat} {t : Expr} {k : Nat}
    {fvs : Array Expr} {stk : List Level} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hw : Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse)) :
    ⦃fun s => s = s₀⦄ inferPisLeafI (coreKnotI mode eager (mkFEnv env) f) d t k fvs stk
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (inferPisLeaf (fueledFns mode eager env) d t k fvs.toList.reverse stk) v; ⊤⦄ := by
  sym only [conleche_grind, inferPisLeaf.eq_1] =>
    vcgen [inferPisLeafI, instListRevM_spec hs, ih.infer_spec, ih.whnf_spec,
      inferPisOutC_spec (mode := mode) (eager := eager) (env := env)] <;> finish

theorem inferPisC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Level} {s₀ : CState},
      CSOK mode eager env s₀ → Expr.WScoped (d + k) (t.instantiateList fvs.toList.reverse) →
      ⦃fun s => s = s₀⦄ inferPisI (coreKnotI mode eager (mkFEnv env) f) d fuel t k fvs stk
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (inferPis (fueledFns mode eager env) d fuel t k fvs.toList.reverse stk) v; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ hs hw
    sym only [conleche_grind, inferPis.eq_3] =>
      vcgen [inferPisI, inferPisLeafC_spec ih] <;> finish
  | succ fuel ihFuel =>
    intro _ _ _ _ _ hs hw
    sym only [conleche_grind, inferPis.eq_1, inferPis.eq_2] =>
      vcgen [inferPisI.eq_def, instListRevM_spec hs, ih.infer_spec, ih.whnf_spec,
        ihFuel, inferPisLeafC_spec ih] <;> finish

/-! ## Tail compositions: the infer loops against the chained bodies'
own tails, with the result scoping recovered from the chained run -/

private theorem inferLamTail_atF {env : Env} (d : Nat)
    (tyx bodyx : Expr) (F : Nat) :
    ((do
      let bt ← (fueledFns mode eager env).infer (d + 1)
        (bodyx.instantiate1 (.fvar d tyx))
      pure (Expr.forallE tyx (bt.abstract1 d))) : FueledM Expr).val F
    = (inferTypeCore mode eager env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => pure (Expr.forallE tyx (bt.abstract1 d))) := by
  rw [FueledM.atF_bind]
  rfl

/-- The λ-inference loop against `inferBody`'s own λ-tail (a pure
rebuild). -/
theorem inferLamsC_tail_sim (ih : SSimC mode eager env f) (henv : EnvWF env)
    {d fuel : Nat} {b t fv : Expr} {bodyx tyx : Expr}
    {s₀ : CState}
    (hs : CSOK mode eager env s₀)
    (hbody : RelC b bodyx)
    (hty : RelC t tyx)
    (hfv : RelC fv (.fvar d tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode eager env s₀ (RelEC d)
      (inferLamsI (coreKnotI mode eager (mkFEnv env) f) d fuel b 1 #[fv]
        [t])
      (do
        let bt ← (fueledFns mode eager env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d tyx))
        pure (Expr.forallE tyx (bt.abstract1 d))) := by
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hb : bodyx = b := hbody.symm
  have ht : tyx = t := hty.symm
  subst hb ht
  have hf : .fvar d tyx = fv := hfv.symm
  subst hf
  have hcore : SimC mode eager env s₀ RelVC
      (inferLamsI (coreKnotI mode eager (mkFEnv env) f) d fuel bodyx 1 #[.fvar d tyx] [tyx])
      (inferLams (fueledFns mode eager env) d fuel bodyx 1 [Expr.fvar d tyx] [tyx]) :=
    SimC.of_tripleVC (inferLamsC_spec ih fuel hs hwopen)
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferLams_atF] at hF
    obtain ⟨F', hchain⟩ := inferLams_sound fuel bodyx 1
      [Expr.fvar d tyx] [tyx] F res rfl hF
    refine ⟨F', ?_⟩
    rw [inferLamTail_atF]
    obtain ⟨bt, hbt, htail⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode eager env F' (d + 1)
        (bodyx.instantiate1 (.fvar d tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d tyx)]
      exact hbt
    rw [hbt', okB_bind]
    exact htail
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferLamTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    have hwbt : Expr.WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv F hbt
        (Expr.WScoped.instantiate1 hwty 0 hwbody)
    have hres : vv = Expr.forallE tyx (bt.abstract1 d) := by
      injection hF with hres
      exact hres.symm
    subst hres
    exact (by
      simp only [Expr.WScoped]
      exact ⟨hwty, ConLeche.WScoped.abstract1 0 hwbt⟩ :
      Expr.WScoped d (Expr.forallE tyx (bt.abstract1 d)))

private theorem inferPiTail_atF {env : Env} (d : Nat)
    (tyx bodyx : Expr) (lu : Level) (F : Nat) :
    ((do
      let v ← ensureSort (fueledFns mode eager env) env (d + 1)
        (← (fueledFns mode eager env).infer (d + 1)
          (bodyx.instantiate1 (.fvar d tyx)))
      pure (Expr.sort (.imax lu v))) : FueledM Expr).val F
    = (inferTypeCore mode eager env F (d + 1) (bodyx.instantiate1 (.fvar d tyx))
        >>= fun bt => ensureSortCore mode eager env F (d + 1) bt >>= fun v =>
        pure (Expr.sort (.imax lu v))) := by
  rw [FueledM.atF_bind]
  congr 1
  funext bt
  rw [FueledM.atF_bind, ensureSort_atF]
  rfl

/-- The ∀-inference loop against `inferBody`'s own ∀-tail (the codomain
sort is inferred). -/
theorem inferPisC_tail_sim (ih : SSimC mode eager env f)
    {d fuel : Nat} {b fv : Expr} {bodyx tyx : Expr}
    {u : Level} {lu : Level} {s₀ : CState}
    (hs : CSOK mode eager env s₀)
    (hbody : RelC b bodyx)
    (hlu : u = lu)
    (hfv : RelC fv (.fvar d tyx))
    (hwty : Expr.WScoped d tyx) (hwbody : Expr.WScoped d bodyx) :
    SimC mode eager env s₀ (RelEC d)
      (inferPisI (coreKnotI mode eager (mkFEnv env) f) d fuel b 1 #[fv] [u])
      (do
        let v ← ensureSort (fueledFns mode eager env) env (d + 1)
          (← (fueledFns mode eager env).infer (d + 1)
            (bodyx.instantiate1 (.fvar d tyx)))
        pure (Expr.sort (.imax lu v))) := by
  subst hlu
  have hwopen : Expr.WScoped (d + 1)
      (bodyx.instantiateList [Expr.fvar d tyx]) := by
    rw [instList_single]
    exact Expr.WScoped.instantiate1 hwty 0 hwbody
  have hb : bodyx = b := hbody.symm
  have hf : .fvar d tyx = fv := hfv.symm
  subst hb hf
  have hcore : SimC mode eager env s₀ RelVC
      (inferPisI (coreKnotI mode eager (mkFEnv env) f) d fuel bodyx 1 #[.fvar d tyx] [u])
      (inferPis (fueledFns mode eager env) d fuel bodyx 1 [Expr.fvar d tyx] [u]) :=
    SimC.of_tripleVC (inferPisC_spec ih fuel hs hwopen)
  refine SimC.wp (SimC.wr hcore ?himp) ?hsc
  case himp =>
    intro res F hF
    rw [inferPis_atF] at hF
    obtain ⟨F', hchain⟩ := inferPis_sound fuel bodyx 1
      [Expr.fvar d tyx] [u] F res rfl (Nat.le_refl 1) hF
    refine ⟨F', ?_⟩
    rw [inferPiTail_atF]
    obtain ⟨bt, hbt, hwrap⟩ := bind_okB hchain
    have hbt' : inferTypeCore mode eager env F' (d + 1)
        (bodyx.instantiate1 (.fvar d tyx)) = .ok bt := by
      rw [← instList_single bodyx (Expr.fvar d tyx)]
      exact hbt
    rw [hbt', okB_bind]
    unfold inferPisWrap at hwrap
    obtain ⟨v, hv, hwrap⟩ := bind_okB hwrap
    rw [ensureSort_def] at hv
    have hv' : ensureSortCore mode eager env F' (d + 1) bt = .ok v := hv
    rw [hv', okB_bind]
    unfold inferPisWrap at hwrap
    exact hwrap
  case hsc =>
    intro v' vv hden hrun
    refine ⟨hden, ?_⟩
    obtain ⟨F, hF⟩ := hrun
    rw [inferPiTail_atF] at hF
    obtain ⟨bt, hbt, hF⟩ := bind_okB hF
    obtain ⟨v, hv, hF⟩ := bind_okB hF
    injection hF with hres
    subst hres
    simp [Expr.WScoped]

end ConLeche.Cached
