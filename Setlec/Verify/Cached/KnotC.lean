import Setlec.Verify.Cached.DiscC6

/-!
# The cached knot: memo wrappers and the conditional simulation

Port of `Setlec/Verify/SimIKnot.lean` and `Setlec/Verify/BridgeI.lean`'s
induction (lines 22-51) under the recipe (DESIGN.md, task #163).

`SSimC mode env f` (declared in `Setlec/Verify/Cached/DiscC1.lean`) is
the cached analogue of `SSimI`: at fuel `f`, every cached entry point
(`Setlec.Cached.coreKnotI mode (mkFEnv env) f`) simulates the
corresponding fueled family on well-scoped inputs.  This module
proves the *memo-wrapper step*: from per-body simulation walks at fuel
`f` (`Setlec/Verify/Cached/DiscC4-6.lean`), each entry point simulates
at `f + 1` — a cache hit consumes the backed `CSOK` clause at the query
key (an *erasure-function* of the key, so it yields the pure run at the
query's erasure directly), a miss runs the body walk and re-inserts the
result in the depth-universal form via the `Expr`-side depth-invariance
theorems (`Setlec/Verify/Deep.lean`), exactly as the interned and
`Expr`-level bridges do.  `ssimC` then ties the two by fuel induction.

The pure comparand side of every statement is byte-identical to the
interned original's.
-/

set_option linter.unusedSimpArgs false

namespace Setlec.Cached

open Setlec
open Setlec.Cached.ExprC

variable {mode : CheckMode}

/-! ## Cache-insert preservation for the entry-point memos

The port of `ISOK.insert*`: the
depth-universal backing run replace the arena's two denotation legs.
A `beq` collision pins the stored key to the query (`beq_sound`),
which is exactly what the clauses — erasure
functions of their keys — need. -/

section Inserts

variable {env : Env}

theorem CSOK.insertWhnfCoreC {s : CState} (hs : CSOK mode env s)
    {i j : ExprC}
    (hrun : ∃ F, ∀ d, (Expr.wscopedB d i) = true →
      whnfCore mode env F d i = .ok j) :
    CSOK mode env { s with whnfCoreC := s.whnfCoreC.insert i j } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, ?_, hs.whnfC, hs.inferC,
    hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro k v hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == k
  · rw [if_pos hk] at hl
    cases hl
    rw [← beq_sound hk]
    exact hrun
  · rw [if_neg hk] at hl
    exact hs.whnfCoreC k v hl

theorem CSOK.insertWhnfC {s : CState} (hs : CSOK mode env s)
    {i j : ExprC}
    (hrun : ∃ F, ∀ d, (Expr.wscopedB d i) = true →
      whnf mode env F d i = .ok j) :
    CSOK mode env { s with whnfC := s.whnfC.insert i j } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, ?_, hs.inferC,
    hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro k v hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == k
  · rw [if_pos hk] at hl
    cases hl
    rw [← beq_sound hk]
    exact hrun
  · rw [if_neg hk] at hl
    exact hs.whnfC k v hl

theorem CSOK.insertInferC {s : CState} (hs : CSOK mode env s)
    {i j : ExprC}
    (hrun : ∃ F, ∀ d, (Expr.wscopedB d i) = true →
      inferTypeCore mode env F d i = .ok j) :
    CSOK mode env { s with inferC := s.inferC.insert i j } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC, ?_,
    hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro k v hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == k
  · rw [if_pos hk] at hl
    cases hl
    rw [← beq_sound hk]
    exact hrun
  · rw [if_neg hk] at hl
    exact hs.inferC k v hl

theorem CSOK.insertAnnotC {s : CState} (hs : CSOK mode env s)
    {i j : ExprC}
    (hrun : ∃ F, ∀ d, (Expr.wscopedB d i) = true →
      annotateCore mode env F d i = .ok j) :
    CSOK mode env { s with annotC := s.annotC.insert i j } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, ?_, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro k v hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : i == k
  · rw [if_pos hk] at hl
    cases hl
    rw [← beq_sound hk]
    exact hrun
  · rw [if_neg hk] at hl
    exact hs.annotC k v hl

theorem CSOK.insertDefeqC {s : CState} (hs : CSOK mode env s)
    {i j : ExprC} {r : Bool}
    (hrun : ∃ F, ∀ d, (Expr.wscopedB d i) = true →
      (Expr.wscopedB d j) = true →
      isDefEqCore mode env F d i j = .ok r) :
    CSOK mode env { s with defeqC := s.defeqC.insert (i, j) r } := by
  refine ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, ?_, hs.lsimp, hs.lnz, hs.eqv, hs.ienv, hs.instC⟩
  intro a b r' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((i, j) : ExprC × ExprC) == (a, b)
  · rw [if_pos hk] at hl
    obtain ⟨hia, hjb⟩ := pairKey_inv hk
    have hjb' : j = b := beq_sound hjb
    cases hl
    rw [← hia, ← hjb']
    exact hrun
  · rw [if_neg hk] at hl
    exact hs.defeqC a b r' hl

end Inserts

/-! ## The memo-wrapper steps -/

section Wrappers

variable {env : Env} {f : Nat}

theorem memoEI_whnfCore_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
      CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
      SimC mode env s₀ (RelEC d)
        (whnfCoreBodyI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
        (whnfCoreBody mode (fueledFns mode env) env d e))
    {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr}
    (hs : CSOK mode env s₀) (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d) ((coreKnotI mode (mkFEnv env) (f + 1)).whnfCore d i)
      ((fueledFns mode env).whnfCore d e) := by
  obtain rfl := hden
  have hden : RelC i i := rfl
  intro v' s' hr
  rw [show (coreKnotI mode (mkFEnv env) (f + 1)).whnfCore d i =
    memoEI (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
      (fun d e => whnfCoreBodyI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.whnfCoreC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨F, hall⟩ := hs.whnfCoreC i _ hl
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, j, ⟨rfl, whnfCore_WScoped henv F hrun hw⟩,
      F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : whnfCoreBodyI (cfgOf mode) (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i s₀
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
      obtain ⟨hs₁, v, ⟨rfl, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [whnfCoreBody_atF] at hF
      rw [← whnfCore_succ] at hF
      have hins := hs₁.insertWhnfCoreC
        ⟨F + 1, fun d' hd' => by
          rw [whnfCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, r, ⟨rfl, hwv⟩, F + 1, hF⟩

theorem memoEI_whnf_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
      CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
      SimC mode env s₀ (RelEC d)
        (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
        (whnfBody (fueledFns mode env) env d e))
    {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr}
    (hs : CSOK mode env s₀) (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d) ((coreKnotI mode (mkFEnv env) (f + 1)).whnf d i)
      ((fueledFns mode env).whnf d e) := by
  obtain rfl := hden
  have hden : RelC i i := rfl
  intro v' s' hr
  rw [show (coreKnotI mode (mkFEnv env) (f + 1)).whnf d i =
    memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
      (fun d e => whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.whnfC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨F, hall⟩ := hs.whnfC i _ hl
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, j, ⟨rfl, whnf_WScoped henv F hrun hw⟩, F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i s₀ with
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
      obtain ⟨hs₁, v, ⟨rfl, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [whnfBody_atF] at hF
      rw [← whnf_succ] at hF
      have hins := hs₁.insertWhnfC
        ⟨F + 1, fun d' hd' => by
          rw [whnf_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, r, ⟨rfl, hwv⟩, F + 1, hF⟩

theorem memoEI_infer_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
      CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
      SimC mode env s₀ (RelEC d)
        (inferBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
        (inferBody mode (fueledFns mode env) env d e))
    {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr}
    (hs : CSOK mode env s₀) (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d) ((coreKnotI mode (mkFEnv env) (f + 1)).infer d i)
      ((fueledFns mode env).infer d e) := by
  obtain rfl := hden
  have hden : RelC i i := rfl
  intro v' s' hr
  rw [show (coreKnotI mode (mkFEnv env) (f + 1)).infer d i =
    memoEI (·.inferC) (fun st mp => { st with inferC := mp })
      (fun d e => inferBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.inferC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨F, hall⟩ := hs.inferC i _ hl
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, j,
      ⟨rfl, inferTypeCore_WScoped henv F hrun hw⟩, F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : inferBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i s₀ with
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
      obtain ⟨hs₁, v, ⟨rfl, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [inferBody_atF] at hF
      rw [← inferTypeCore_succ] at hF
      have hins := hs₁.insertInferC
        ⟨F + 1, fun d' hd' => by
          rw [inferTypeCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, r, ⟨rfl, hwv⟩, F + 1, hF⟩

theorem memoEI_annotate_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
      CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
      SimC mode env s₀ (RelEC d)
        (annotateBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
        (annotateBody mode (fueledFns mode env) env d e))
    {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr}
    (hs : CSOK mode env s₀) (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelEC d) ((coreKnotI mode (mkFEnv env) (f + 1)).annotate d i)
      ((fueledFns mode env).annotate d e) := by
  obtain rfl := hden
  have hden : RelC i i := rfl
  intro v' s' hr
  rw [show (coreKnotI mode (mkFEnv env) (f + 1)).annotate d i =
    memoEI (·.annotC) (fun st mp => { st with annotC := mp })
      (fun d e => annotateBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d e)
      d i from rfl] at hr
  simp only [memoEI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.annotC[i]? with
  | some j =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨F, hall⟩ := hs.annotC i _ hl
    have hrun := hall d hw.to_wscopedB
    exact ⟨hs, j,
      ⟨rfl, annotateCore_WScoped F _ hrun hw⟩, F, hrun⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : annotateBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i s₀
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
      obtain ⟨hs₁, v, ⟨rfl, hwv⟩, F, hF⟩ := hbody hs hden hw r s₁ hb
      rw [annotateBody_atF] at hF
      rw [← annotateCore_succ] at hF
      have hins := hs₁.insertAnnotC
        ⟨F + 1, fun d' hd' => by
          rw [annotateCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]
          exact hF⟩
      exact ⟨hins, r, ⟨rfl, hwv⟩, F + 1, hF⟩

theorem memoBI_defeq_sim (henv : EnvWF env)
    (hbody : ∀ {s₀ : CState} {d : Nat} {i j : ExprC} {a b : Expr},
      CSOK mode env s₀ → RelC i a → RelC j b →
      Expr.WScoped d a → Expr.WScoped d b →
      SimC mode env s₀ RelVC
        (defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
        (defeqBody mode (fueledFns mode env) env d a b))
    {s₀ : CState} {d : Nat} {i j : ExprC} {a b : Expr}
    (hs : CSOK mode env s₀) (hdena : RelC i a) (hdenb : RelC j b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC ((coreKnotI mode (mkFEnv env) (f + 1)).defeq d i j)
      ((fueledFns mode env).defeq d a b) := by
  obtain rfl := hdena
  obtain rfl := hdenb
  have hdena : RelC i i := rfl
  have hdenb : RelC j j := rfl
  intro v' s' hr
  rw [show (coreKnotI mode (mkFEnv env) (f + 1)).defeq d i j =
    memoBI
      (fun d i j => defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j)
      d i j from rfl] at hr
  simp only [memoBI, Bind.bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure,
    Except.bind] at hr
  cases hl : s₀.defeqC[((i, j) : ExprC × ExprC)]? with
  | some r =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨F, hall⟩ := hs.defeqC i j _ hl
    exact ⟨hs, r, rfl, F, hall d hwa.to_wscopedB hwb.to_wscopedB⟩
  | none =>
    rw [hl] at hr
    try dsimp only at hr
    try simp only [StateT.bind] at hr
    cases hb : defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i j s₀
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
      obtain ⟨hs₁, v, hrv, F, hF⟩ := hbody hs hdena hdenb hwa hwb r s₁ hb
      rw [defeqBody_atF] at hF
      rw [← isDefEqCore_succ] at hF
      obtain rfl : r = v := hrv
      have hins := hs₁.insertDefeqC
        ⟨F + 1, fun d' hda' hdb' => by
          rw [isDefEqCore_depth_inv henv (F + 1) hda' hdb'
            hwa.to_wscopedB hwb.to_wscopedB]
          exact hF⟩
      exact ⟨hins, r, rfl, F + 1, hF⟩

end Wrappers

/-! ## The knot induction -/

/-- Port of `ssimI`: the cached knot simulates the fueled families at
every fuel.  The wrapper steps tie each entry point at `f + 1` to the
body walks at `f`, which consume the simulation at `f` as their
induction hypothesis. -/
theorem ssimC (env : Env) (henv : EnvWF env) : ∀ f, SSimC mode env f
  | 0 => ssimC_zero env
  | f + 1 =>
    { whnfCore := fun hs hden hw =>
        memoEI_whnfCore_sim henv
          (fun hs' hden' hw' =>
            whnfCoreBodyC_sim (ssimC env henv f) henv hs' hden' hw')
          hs hden hw
      whnf := fun hs hden hw =>
        memoEI_whnf_sim henv
          (fun hs' hden' hw' =>
            whnfBodyC_sim (ssimC env henv f) henv hs' hden' hw')
          hs hden hw
      infer := fun hs hden hw =>
        memoEI_infer_sim henv
          (fun hs' hden' hw' =>
            inferBodyC_sim (ssimC env henv f) henv hs' hden' hw')
          hs hden hw
      defeq := fun hs hdena hdenb hwa hwb =>
        memoBI_defeq_sim henv
          (fun hs' hdena' hdenb' hwa' hwb' =>
            defeqBodyC_sim (ssimC env henv f) henv hs' hdena' hdenb'
              hwa' hwb')
          hs hdena hdenb hwa hwb
      annotate := fun hs hden hw =>
        memoEI_annotate_sim henv
          (fun hs' hden' hw' =>
            annotateBodyC_sim (ssimC env henv f) henv hs' hden' hw')
          hs hden hw }

end Setlec.Cached
