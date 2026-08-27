import Setlec.Verify.SimI
import Setlec.Verify.Knot

/-!
# The interned knot: memo wrappers and the conditional simulation

`SSimI env f` is the interned analogue of `ScopedSim`: at fuel `f`,
every interned entry point (`coreKnotI (mkFEnv env) f`) simulates the
corresponding fueled family under the denotation, on denoting,
well-scoped inputs.  This module proves the *memo-wrapper step*: from
per-body simulation walks at fuel `f` (`Setlec/Verify/DiscI*.lean`),
each entry point simulates at `f + 1` — a cache hit consumes the
backed entry (`ISOK`) at the call's depth, a miss runs the body walk
and re-inserts the result in the depth-universal form via the depth
invariance theorems, exactly as the Expr-level bridge does
(`Setlec/Verify/Bridge.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

/-- The interned conditional simulation at fuel `f`. -/
structure SSimI (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
    ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) f).whnfCore d i)
      ((fueledFns env).whnfCore d e)
  whnf : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
    ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) f).whnf d i)
      ((fueledFns env).whnf d e)
  infer : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
    ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) f).infer d i)
      ((fueledFns env).infer d e)
  defeq : ∀ {s₀ : IState} {d : Nat} {i j : EIdx} {a b : Expr},
    ISOK env s₀ → s₀.store.denoteT i = some a →
    s₀.store.denoteT j = some b → WScoped d a → WScoped d b →
    SimAt env s₀ RelV ((coreKnotI (mkFEnv env) f).defeq d i j)
      ((fueledFns env).defeq d a b)
  annotate : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
    ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) f).annotate d i)
      ((fueledFns env).annotate d e)

/-- The base case: fuel `0` throws everywhere. -/
theorem ssimI_zero (env : Env) : SSimI env 0 :=
  { whnfCore := fun _ _ _ => SimAt.throw
    whnf := fun _ _ _ => SimAt.throw
    infer := fun _ _ _ => SimAt.throw
    defeq := fun _ _ _ _ _ => SimAt.throw
    annotate := fun _ _ _ => SimAt.throw }

/-! ## Cache-insert preservation for the entry-point memos -/

section Inserts

variable {env : Env}

theorem ISOK.insertWhnfCoreC {s : IState} (hs : ISOK env s)
    {i j : EIdx} {a b : Expr}
    (hi : s.store.denoteT i = some a) (hj : s.store.denoteT j = some b)
    (hrun : ∃ F, ∀ d, a.wscopedB d = true → whnfCore env F d a = .ok b) :
    ISOK env { s with whnfCoreC := s.whnfCoreC.insert i j } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, hs.ruleRhs, ?_, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv,
    hs.ienv, hs.instC⟩
  intro i' j' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == i'
  · rw [if_pos hk] at hl
    obtain rfl : i = i' := eq_of_beq hk
    cases hl
    exact ⟨a, b, hi, hj, hrun⟩
  · rw [if_neg hk] at hl
    exact hs.whnfCoreC i' j' hl

theorem ISOK.insertWhnfC {s : IState} (hs : ISOK env s)
    {i j : EIdx} {a b : Expr}
    (hi : s.store.denoteT i = some a) (hj : s.store.denoteT j = some b)
    (hrun : ∃ F, ∀ d, a.wscopedB d = true → whnf env F d a = .ok b) :
    ISOK env { s with whnfC := s.whnfC.insert i j } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, ?_,
    hs.inferC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv,
    hs.ienv, hs.instC⟩
  intro i' j' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == i'
  · rw [if_pos hk] at hl
    obtain rfl : i = i' := eq_of_beq hk
    cases hl
    exact ⟨a, b, hi, hj, hrun⟩
  · rw [if_neg hk] at hl
    exact hs.whnfC i' j' hl

theorem ISOK.insertInferC {s : IState} (hs : ISOK env s)
    {i j : EIdx} {a b : Expr}
    (hi : s.store.denoteT i = some a) (hj : s.store.denoteT j = some b)
    (hrun : ∃ F, ∀ d, a.wscopedB d = true →
      inferTypeCore env F d a = .ok b) :
    ISOK env { s with inferC := s.inferC.insert i j } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC,
    hs.whnfC, ?_, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv,
    hs.ienv, hs.instC⟩
  intro i' j' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == i'
  · rw [if_pos hk] at hl
    obtain rfl : i = i' := eq_of_beq hk
    cases hl
    exact ⟨a, b, hi, hj, hrun⟩
  · rw [if_neg hk] at hl
    exact hs.inferC i' j' hl

theorem ISOK.insertAnnotC {s : IState} (hs : ISOK env s)
    {i j : EIdx} {a b : Expr}
    (hi : s.store.denoteT i = some a) (hj : s.store.denoteT j = some b)
    (hrun : ∃ F, ∀ d, a.wscopedB d = true →
      annotateCore env F d a = .ok b) :
    ISOK env { s with annotC := s.annotC.insert i j } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC,
    hs.whnfC, hs.inferC, ?_, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv,
    hs.ienv, hs.instC⟩
  intro i' j' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == i'
  · rw [if_pos hk] at hl
    obtain rfl : i = i' := eq_of_beq hk
    cases hl
    exact ⟨a, b, hi, hj, hrun⟩
  · rw [if_neg hk] at hl
    exact hs.annotC i' j' hl

theorem ISOK.insertDefeqC {s : IState} (hs : ISOK env s)
    {i j : EIdx} {r : Bool} {a b : Expr}
    (hi : s.store.denoteT i = some a) (hj : s.store.denoteT j = some b)
    (hrun : ∃ F, ∀ d, a.wscopedB d = true → b.wscopedB d = true →
      isDefEqCore env F d a b = .ok r) :
    ISOK env { s with defeqC := s.defeqC.insert (i, j) r } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC,
    hs.whnfC, hs.inferC, hs.annotC, ?_, hs.lsimp, hs.lnz, hs.eqv,
    hs.ienv, hs.instC⟩
  intro i' j' r' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((i, j) : EIdx × EIdx) == (i', j')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : i = i' ∧ j = j' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    cases hl
    exact ⟨a, b, hi, hj, hrun⟩
  · rw [if_neg hk] at hl
    exact hs.defeqC i' j' r' hl

end Inserts

/-! ## The memo-wrapper steps -/

section Wrappers

variable {env : Env} {f : Nat}

theorem memoEI_whnfCore_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
      ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
      SimAt env s₀ (RelE d)
        (whnfCoreBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
        (whnfCoreBody (fueledFns env) env d e))
    {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr}
    (hs : ISOK env s₀) (hden : s₀.store.denoteT i = some e)
    (hw : WScoped d e) :
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) (f + 1)).whnfCore d i)
      ((fueledFns env).whnfCore d e) := by
  intro v' s' hr
  rw [show (coreKnotI (mkFEnv env) (f + 1)).whnfCore d i =
    memoEI (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
      (fun d e => whnfCoreBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.whnfCoreC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨a, b, hia, hjb, F, hall⟩ := hs.whnfCoreC i _ hl
    rw [hden] at hia
    cases hia
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, Ext.refl _, b, ⟨hjb, whnfCore_WScoped henv F hrun hw⟩,
      F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : whnfCoreBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i s₀
        with
    | error err =>
      rw [hb] at hr
      simp only [Bind.bind, Except.bind] at hr
      exact nomatch hr
    | ok pr =>
      obtain ⟨r, s₁⟩ := pr
      rw [hb] at hr
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      obtain ⟨hs₁, hext₁, v, ⟨hrv, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [whnfCoreBody_atF] at hF
      rw [← whnfCore_succ] at hF
      have hins := hs₁.insertWhnfCoreC (denoteT_mono hext₁ hden) hrv
        ⟨F + 1, fun d' hd' => by
          rw [whnfCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, hext₁, v, ⟨hrv, hwv⟩, F + 1, hF⟩

theorem memoEI_whnf_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
      ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
      SimAt env s₀ (RelE d)
        (whnfBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
        (whnfBody (fueledFns env) env d e))
    {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr}
    (hs : ISOK env s₀) (hden : s₀.store.denoteT i = some e)
    (hw : WScoped d e) :
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) (f + 1)).whnf d i)
      ((fueledFns env).whnf d e) := by
  intro v' s' hr
  rw [show (coreKnotI (mkFEnv env) (f + 1)).whnf d i =
    memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
      (fun d e => whnfBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.whnfC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨a, b, hia, hjb, F, hall⟩ := hs.whnfC i _ hl
    rw [hden] at hia
    cases hia
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, Ext.refl _, b, ⟨hjb, whnf_WScoped henv F hrun hw⟩, F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : whnfBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i s₀ with
    | error err =>
      rw [hb] at hr
      simp only [Bind.bind, Except.bind] at hr
      exact nomatch hr
    | ok pr =>
      obtain ⟨r, s₁⟩ := pr
      rw [hb] at hr
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      obtain ⟨hs₁, hext₁, v, ⟨hrv, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [whnfBody_atF] at hF
      rw [← whnf_succ] at hF
      have hins := hs₁.insertWhnfC (denoteT_mono hext₁ hden) hrv
        ⟨F + 1, fun d' hd' => by
          rw [whnf_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, hext₁, v, ⟨hrv, hwv⟩, F + 1, hF⟩

theorem memoEI_infer_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
      ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
      SimAt env s₀ (RelE d)
        (inferBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
        (inferBody (fueledFns env) env d e))
    {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr}
    (hs : ISOK env s₀) (hden : s₀.store.denoteT i = some e)
    (hw : WScoped d e) :
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) (f + 1)).infer d i)
      ((fueledFns env).infer d e) := by
  intro v' s' hr
  rw [show (coreKnotI (mkFEnv env) (f + 1)).infer d i =
    memoEI (·.inferC) (fun st mp => { st with inferC := mp })
      (fun d e => inferBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.inferC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨a, b, hia, hjb, F, hall⟩ := hs.inferC i _ hl
    rw [hden] at hia
    cases hia
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, Ext.refl _, b,
      ⟨hjb, inferTypeCore_WScoped henv F hrun hw⟩, F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : inferBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i s₀ with
    | error err =>
      rw [hb] at hr
      simp only [Bind.bind, Except.bind] at hr
      exact nomatch hr
    | ok pr =>
      obtain ⟨r, s₁⟩ := pr
      rw [hb] at hr
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      obtain ⟨hs₁, hext₁, v, ⟨hrv, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [inferBody_atF] at hF
      rw [← inferTypeCore_succ] at hF
      have hins := hs₁.insertInferC (denoteT_mono hext₁ hden) hrv
        ⟨F + 1, fun d' hd' => by
          rw [inferTypeCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, hext₁, v, ⟨hrv, hwv⟩, F + 1, hF⟩

theorem memoEI_annotate_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr},
      ISOK env s₀ → s₀.store.denoteT i = some e → WScoped d e →
      SimAt env s₀ (RelE d)
        (annotateBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
        (annotateBody (fueledFns env) env d e))
    {s₀ : IState} {d : Nat} {i : EIdx} {e : Expr}
    (hs : ISOK env s₀) (hden : s₀.store.denoteT i = some e)
    (hw : WScoped d e) :
    SimAt env s₀ (RelE d) ((coreKnotI (mkFEnv env) (f + 1)).annotate d i)
      ((fueledFns env).annotate d e) := by
  intro v' s' hr
  rw [show (coreKnotI (mkFEnv env) (f + 1)).annotate d i =
    memoEI (·.annotC) (fun st mp => { st with annotC := mp })
      (fun d e => annotateBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.annotC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨a, b, hia, hjb, F, hall⟩ := hs.annotC i _ hl
    rw [hden] at hia
    cases hia
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, Ext.refl _, b,
      ⟨hjb, annotateCore_WScoped F _ hrun hw⟩, F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : annotateBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i s₀
        with
    | error err =>
      rw [hb] at hr
      simp only [Bind.bind, Except.bind] at hr
      exact nomatch hr
    | ok pr =>
      obtain ⟨r, s₁⟩ := pr
      rw [hb] at hr
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      obtain ⟨hs₁, hext₁, v, ⟨hrv, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [annotateBody_atF] at hF
      rw [← annotateCore_succ] at hF
      have hins := hs₁.insertAnnotC (denoteT_mono hext₁ hden) hrv
        ⟨F + 1, fun d' hd' => by
          rw [annotateCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, hext₁, v, ⟨hrv, hwv⟩, F + 1, hF⟩

theorem memoBI_defeq_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : IState} {d : Nat} {i j : EIdx} {a b : Expr},
      ISOK env s₀ → s₀.store.denoteT i = some a →
      s₀.store.denoteT j = some b → WScoped d a → WScoped d b →
      SimAt env s₀ RelV
        (defeqBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
        (defeqBody (fueledFns env) env d a b))
    {s₀ : IState} {d : Nat} {i j : EIdx} {a b : Expr}
    (hs : ISOK env s₀) (hdena : s₀.store.denoteT i = some a)
    (hdenb : s₀.store.denoteT j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV ((coreKnotI (mkFEnv env) (f + 1)).defeq d i j)
      ((fueledFns env).defeq d a b) := by
  intro v' s' hr
  rw [show (coreKnotI (mkFEnv env) (f + 1)).defeq d i j =
    memoBI
      (fun d i j => defeqBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      d i j from rfl] at hr
  simp only [memoBI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.defeqC[((i, j) : EIdx × EIdx)]? with
  | some r =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨a', b', hia, hjb, F, hall⟩ := hs.defeqC i j _ hl
    rw [hdena] at hia
    cases hia
    rw [hdenb] at hjb
    cases hjb
    exact ⟨hs, Ext.refl _, r, rfl, F,
      hall d hwa.to_wscopedB hwb.to_wscopedB⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : defeqBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j s₀
        with
    | error err =>
      rw [hb] at hr
      simp only [Bind.bind, Except.bind] at hr
      exact nomatch hr
    | ok pr =>
      obtain ⟨r, s₁⟩ := pr
      rw [hb] at hr
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      obtain ⟨hs₁, hext₁, v, hrv, F, hF⟩ := hbody hs hdena hdenb hwa hwb
        r s₁ hb
      rw [defeqBody_atF] at hF
      rw [← isDefEqCore_succ] at hF
      obtain rfl : r = v := hrv
      have hins := hs₁.insertDefeqC (denoteT_mono hext₁ hdena)
        (denoteT_mono hext₁ hdenb)
        ⟨F + 1, fun d' hda' hdb' => by
          rw [isDefEqCore_depth_inv henv (F + 1) hda' hdb'
            hwa.to_wscopedB hwb.to_wscopedB]
          exact hF⟩
      exact ⟨hins, hext₁, r, rfl, F + 1, hF⟩

end Wrappers

end Setlec
