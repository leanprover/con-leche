module

public import ConLeche.Verify.Cached.DiscC5
import ConLeche.Verify.Cached.Grind

public section

/-!
# The cached knot: memo wrappers and the conditional simulation

`SSimC mode env f` (task #163; declared in
`ConLeche/Verify/Cached/DiscC1.lean`): at fuel `f`, every cached entry point
(`ConLeche.Cached.coreKnotI mode (mkFEnv env) f`) simulates the
corresponding fueled family on well-scoped inputs.  This module
proves the *memo-wrapper step*: from per-body simulation walks at fuel
`f` (`ConLeche/Verify/Cached/DiscC4-5.lean`), each entry point simulates
at `f + 1` — a cache hit consumes the backed `CSOK` clause at the query
key (an *erasure-function* of the key, so it yields the pure run at the
query's erasure directly), a miss runs the body walk and re-inserts the
result in the depth-universal form via the `Expr`-side depth-invariance
theorems (`ConLeche/Verify/Deep.lean`).  `ssimC` then ties the two by
fuel induction.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## The memo-wrapper steps -/

section Wrappers

variable {env : Env} {f : Nat}

/-! ### The whnfCore memos

The two modes of `whnfCore` (official `cheap_proj`) under two memos; one
triple covers both (`vcgen` splits the knot's `if c`). -/

theorem coreKnotI_whnfCore_succ (c : Bool) (d : Nat) (i : Expr) :
    (coreKnotI mode (mkFEnv env) (f + 1)).whnfCore c d i =
      if c then
        memoEI (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp })
          (fun d e => whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) true d e)
          d i
      else
        memoEI (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
          (fun d e => whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) false d e)
          d i := by
  cases c <;> rfl

/-- A full whnfCore memo hit answers the fueled whnfCore, well scoped. -/
theorem CSOK.whnfCore_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.whnfCoreC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode env).whnfCore false d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCore_hit =>
  CSOK mode env s, s.whnfCoreC[i]?, Runs ((fueledFns mode env).whnfCore false d i) r
-- con-agua patch (nightly-2026-10-06+, lean4#15487): `vcgen` now splits the
-- postcondition's `∧`, so the `WScoped` VC no longer contains the `Runs` term
-- that triggers `CSOK.whnfCore_hit`; this conjunct gets its own trigger.
theorem CSOK.whnfCore_hit_ws (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.whnfCoreC[i]? = some r) (hw : Expr.WScoped d i) :
    Expr.WScoped d r := (CSOK.whnfCore_hit henv hs hl hw).2
grind_pattern [conleche_grind] CSOK.whnfCore_hit_ws =>
  CSOK mode env s, s.whnfCoreC[i]?, Expr.WScoped d r

/-- A cheap whnfCore memo hit answers the fueled cheap whnfCore. -/
theorem CSOK.whnfCoreCheap_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.whnfCoreCheapC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode env).whnfCore true d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreCheapC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCoreCheap_hit =>
  CSOK mode env s, s.whnfCoreCheapC[i]?, Runs ((fueledFns mode env).whnfCore true d i) r
-- con-agua patch (nightly-2026-10-06+, lean4#15487): `vcgen` now splits the
-- postcondition's `∧`, so the `WScoped` VC no longer contains the `Runs` term
-- that triggers `CSOK.whnfCoreCheap_hit`; this conjunct gets its own trigger.
theorem CSOK.whnfCoreCheap_hit_ws (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.whnfCoreCheapC[i]? = some r) (hw : Expr.WScoped d i) :
    Expr.WScoped d r := (CSOK.whnfCoreCheap_hit henv hs hl hw).2
grind_pattern [conleche_grind] CSOK.whnfCoreCheap_hit_ws =>
  CSOK mode env s, s.whnfCoreCheapC[i]?, Expr.WScoped d r

/-- A body answer is a whnfCore answer one fuel up. -/
theorem Runs.whnfCore_of_body {c : Bool} {d : Nat} {i r : Expr}
    (h : Runs (whnfCoreBody mode (fueledFns mode env) env c d i) r) :
    Runs ((fueledFns mode env).whnfCore c d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [whnfCoreBody_atF, ← whnfCore_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.whnfCore_of_body =>
  Runs (whnfCoreBody mode (fueledFns mode env) env c d i) r, (fueledFns mode env).whnfCore c d i

theorem CSOK.whnfCore_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hw : Expr.WScoped d i)
    (h : Runs (whnfCoreBody mode (fueledFns mode env) env false d i) r) :
    CSOK mode env { s with whnfCoreC := s.whnfCoreC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [whnfCoreBody_atF, ← whnfCore_succ] at hF
  exact { hs with
    whnfCoreC := HashMap.insert_backed hs.whnfCoreC ⟨F + 1, fun d' hd' => by
      rw [whnfCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

theorem CSOK.whnfCoreCheap_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hw : Expr.WScoped d i)
    (h : Runs (whnfCoreBody mode (fueledFns mode env) env true d i) r) :
    CSOK mode env { s with whnfCoreCheapC := s.whnfCoreCheapC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [whnfCoreBody_atF, ← whnfCore_succ] at hF
  exact { hs with
    whnfCoreCheapC := HashMap.insert_backed hs.whnfCoreCheapC ⟨F + 1, fun d' hd' => by
      rw [whnfCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The whnfCore memo wrappers simulate the fueled whnfCore at one fuel
more than their bodies. -/
theorem memoEI_whnfCore_spec (henv : EnvWF env)
    (hbody : ∀ c, BodySpec mode env
      (whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c)
      (whnfCoreBody mode (fueledFns mode env) env c))
    {c : Bool} {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) (f + 1)).whnfCore c d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).whnfCore c d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.whnfCore_insert henv, CSOK.whnfCoreCheap_insert henv] =>
    vcgen [coreKnotI_whnfCore_succ, memoEI, BodySpec.triple (hbody true),
      BodySpec.triple (hbody false)] <;> finish

/-! ### The whnf memo, by `vcgen` and `grind`

A hit reads the backed `CSOK.whnfC` clause at the query (`CSOK.whnf_hit`);
a miss runs the body and inserts its answer, backed one fuel up by the
depth-invariant run (`CSOK.whnf_insert`, `Runs.whnf_of_body`). -/

theorem coreKnotI_whnf_succ (d : Nat) (i : Expr) :
    (coreKnotI mode (mkFEnv env) (f + 1)).whnf d i =
      memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d e) d i := rfl

/-- A whnf memo hit answers the fueled whnf, well scoped. -/
theorem CSOK.whnf_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.whnfC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode env).whnf d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnf_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnf_hit =>
  CSOK mode env s, s.whnfC[i]?, Runs ((fueledFns mode env).whnf d i) r
-- con-agua patch (nightly-2026-10-06+, lean4#15487): `vcgen` now splits the
-- postcondition's `∧`, so the `WScoped` VC no longer contains the `Runs` term
-- that triggers `CSOK.whnf_hit`; this conjunct gets its own trigger.
theorem CSOK.whnf_hit_ws (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.whnfC[i]? = some r) (hw : Expr.WScoped d i) :
    Expr.WScoped d r := (CSOK.whnf_hit henv hs hl hw).2
grind_pattern [conleche_grind] CSOK.whnf_hit_ws =>
  CSOK mode env s, s.whnfC[i]?, Expr.WScoped d r

/-- A body answer is a whnf answer one fuel up. -/
theorem Runs.whnf_of_body {d : Nat} {i r : Expr}
    (h : Runs (whnfBody (fueledFns mode env) env d i) r) :
    Runs ((fueledFns mode env).whnf d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [whnfBody_atF, ← whnf_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.whnf_of_body =>
  Runs (whnfBody (fueledFns mode env) env d i) r, (fueledFns mode env).whnf d i

/-- Inserting a body answer into the whnf memo keeps the invariant: the
entry is backed one fuel up at every depth the key is scoped at. -/
theorem CSOK.whnf_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hw : Expr.WScoped d i)
    (h : Runs (whnfBody (fueledFns mode env) env d i) r) :
    CSOK mode env { s with whnfC := s.whnfC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [whnfBody_atF, ← whnf_succ] at hF
  exact { hs with
    whnfC := HashMap.insert_backed hs.whnfC ⟨F + 1, fun d' hd' => by
      rw [whnf_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The whnf memo wrapper simulates the fueled whnf at one fuel more
than its body.  `CSOK.whnf_insert` is in the `sym` list instantiated at
`henv`: its pattern is the inserted state, which every miss builds. -/
theorem memoEI_whnf_spec (henv : EnvWF env)
    (hbody : BodySpec mode env (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env))
      (whnfBody (fueledFns mode env) env))
    {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) (f + 1)).whnf d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).whnf d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.whnf_insert henv] =>
    vcgen [coreKnotI_whnf_succ, memoEI, hbody.triple] <;> finish

/-! ### The infer memo -/

theorem coreKnotI_infer_succ (d : Nat) (i : Expr) :
    (coreKnotI mode (mkFEnv env) (f + 1)).infer d i =
      memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d e) d i := rfl

/-- An infer memo hit answers the fueled infer, well scoped. -/
theorem CSOK.infer_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.inferC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode env).infer d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.inferC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, inferTypeCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.infer_hit =>
  CSOK mode env s, s.inferC[i]?, Runs ((fueledFns mode env).infer d i) r
-- con-agua patch (nightly-2026-10-06+, lean4#15487): `vcgen` now splits the
-- postcondition's `∧`, so the `WScoped` VC no longer contains the `Runs` term
-- that triggers `CSOK.infer_hit`; this conjunct gets its own trigger.
theorem CSOK.infer_hit_ws (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.inferC[i]? = some r) (hw : Expr.WScoped d i) :
    Expr.WScoped d r := (CSOK.infer_hit henv hs hl hw).2
grind_pattern [conleche_grind] CSOK.infer_hit_ws =>
  CSOK mode env s, s.inferC[i]?, Expr.WScoped d r

/-- A body answer is an infer answer one fuel up. -/
theorem Runs.infer_of_body {d : Nat} {i r : Expr}
    (h : Runs (inferBody (fueledFns mode env) env d i) r) :
    Runs ((fueledFns mode env).infer d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [inferBody_atF, ← inferTypeCore_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.infer_of_body =>
  Runs (inferBody (fueledFns mode env) env d i) r, (fueledFns mode env).infer d i

theorem CSOK.infer_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hw : Expr.WScoped d i)
    (h : Runs (inferBody (fueledFns mode env) env d i) r) :
    CSOK mode env { s with inferC := s.inferC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [inferBody_atF, ← inferTypeCore_succ] at hF
  exact { hs with
    inferC := HashMap.insert_backed hs.inferC ⟨F + 1, fun d' hd' => by
      rw [inferTypeCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The infer memo wrapper simulates the fueled infer at one fuel more
than its body. -/
theorem memoEI_infer_spec (henv : EnvWF env)
    (hbody : BodySpec mode env (inferBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env))
      (inferBody (fueledFns mode env) env))
    {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) (f + 1)).infer d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).infer d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.infer_insert henv] =>
    vcgen [coreKnotI_infer_succ, memoEI, hbody.triple] <;> finish

/-! ### The io memo (task #172 B4)

The slot is the io body under its own memo (`CState.inferIOC`); a hit
consumes the io clause — the weaker one — and a miss re-inserts in
depth-universal form through `inferTypeIO_depth_inv`. -/

theorem coreKnotI_inferIO_succ (d : Nat) (i : Expr) :
    (coreKnotI mode (mkFEnv env) (f + 1)).inferIO d i =
      memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
        (fun d e => inferBodyIOI (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f))
          (mkFEnv env) d e) d i :=
  -- the knot's previous level is a `Unit` closure (task #179), which
  -- beta-reduces to `coreKnotI … f`
  rfl

/-- An io memo hit answers the fueled io slot, well scoped. -/
theorem CSOK.inferIO_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.inferIOC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode env).inferIO d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.inferIOC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, inferTypeIO_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.inferIO_hit =>
  CSOK mode env s, s.inferIOC[i]?, Runs ((fueledFns mode env).inferIO d i) r
-- con-agua patch (nightly-2026-10-06+, lean4#15487): `vcgen` now splits the
-- postcondition's `∧`, so the `WScoped` VC no longer contains the `Runs` term
-- that triggers `CSOK.inferIO_hit`; this conjunct gets its own trigger.
theorem CSOK.inferIO_hit_ws (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hl : s.inferIOC[i]? = some r) (hw : Expr.WScoped d i) :
    Expr.WScoped d r := (CSOK.inferIO_hit henv hs hl hw).2
grind_pattern [conleche_grind] CSOK.inferIO_hit_ws =>
  CSOK mode env s, s.inferIOC[i]?, Expr.WScoped d r

/-- An io body answer is an io-slot answer one fuel up. -/
theorem Runs.inferIO_of_body {d : Nat} {i r : Expr}
    (h : Runs (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d i) r) :
    Runs ((fueledFns mode env).inferIO d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [inferBodyIO_atF, ← inferTypeIO_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.inferIO_of_body =>
  Runs (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d i) r,
  (fueledFns mode env).inferIO d i

theorem CSOK.inferIO_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode env s) (hw : Expr.WScoped d i)
    (h : Runs (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d i) r) :
    CSOK mode env { s with inferIOC := s.inferIOC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [inferBodyIO_atF, ← inferTypeIO_succ] at hF
  exact { hs with
    inferIOC := HashMap.insert_backed hs.inferIOC ⟨F + 1, fun d' hd' => by
      rw [inferTypeIO_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The io memo wrapper simulates the fueled io slot at one fuel more
than its body. -/
theorem memoEI_inferIO_spec (henv : EnvWF env)
    (hbody : BodySpec mode env
      (inferBodyIOI (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env))
      (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env))
    {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) (f + 1)).inferIO d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).inferIO d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.inferIO_insert henv] =>
    vcgen [coreKnotI_inferIO_succ, memoEI, hbody.triple] <;> finish

/-! ### The defeq memo -/

theorem coreKnotI_defeq_succ (d : Nat) (a b : Expr) :
    (coreKnotI mode (mkFEnv env) (f + 1)).defeq d a b =
      memoBI (fun d a b => defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b)
        d a b := rfl

/-- A defeq memo hit answers the fueled defeq. -/
theorem CSOK.defeq_hit {s : CState} {d : Nat} {a b : Expr} {r : Bool}
    (hs : CSOK mode env s) (hl : s.defeqC[(a, b)]? = some r) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    Runs ((fueledFns mode env).defeq d a b) r := by
  obtain ⟨F, hall⟩ := hs.defeqC a b r hl
  exact ⟨F, hall d hwa.to_wscopedB hwb.to_wscopedB⟩
grind_pattern [conleche_grind] CSOK.defeq_hit =>
  CSOK mode env s, s.defeqC[(a, b)]?, Runs ((fueledFns mode env).defeq d a b) r

/-- A body answer is a defeq answer one fuel up. -/
theorem Runs.defeq_of_body {d : Nat} {a b : Expr} {r : Bool}
    (h : Runs (defeqBody mode (fueledFns mode env) env d a b) r) :
    Runs ((fueledFns mode env).defeq d a b) r := by
  obtain ⟨F, hF⟩ := h
  rw [defeqBody_atF, ← isDefEqCore_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.defeq_of_body =>
  Runs (defeqBody mode (fueledFns mode env) env d a b) r, (fueledFns mode env).defeq d a b

theorem CSOK.defeq_insert (henv : EnvWF env) {s : CState} {d : Nat} {a b : Expr} {r : Bool}
    (hs : CSOK mode env s) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (h : Runs (defeqBody mode (fueledFns mode env) env d a b) r) :
    CSOK mode env { s with defeqC := s.defeqC.insert (a, b) r } := by
  obtain ⟨F, hF⟩ := h
  rw [defeqBody_atF, ← isDefEqCore_succ] at hF
  -- the clause is curried in the key pair
  exact { hs with
    defeqC := fun a' b' r' => HashMap.insert_backed
      (P := fun k r => ∃ F, ∀ d, k.1.wscopedB d = true → k.2.wscopedB d = true →
        isDefEqCore mode env F d k.1 k.2 = .ok r)
      (fun k v => hs.defeqC k.1 k.2 v) ⟨F + 1, fun d' hda' hdb' => by
        rw [isDefEqCore_depth_inv henv (F + 1) hda' hdb' hwa.to_wscopedB hwb.to_wscopedB]
        exact hF⟩ (a', b') r' }

/-- The defeq memo wrapper simulates the fueled defeq at one fuel more
than its body. -/
theorem memoBI_defeq_spec (henv : EnvWF env)
    (hbody : BodySpecB mode env (defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env))
      (defeqBody mode (fueledFns mode env) env))
    {s₀ : CState} {d : Nat} {a b : Expr} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode (mkFEnv env) (f + 1)).defeq d a b
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).defeq d a b) r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.defeq_insert henv] =>
    vcgen [coreKnotI_defeq_succ, memoBI, hbody.triple] <;> finish

end Wrappers

/-! ## The knot induction -/

private theorem ssimC_all (env : Env) (henv : EnvWF env) :
    ∀ (f : Nat) (mode : CheckMode), mode.verifiedChecks = true → SSimC mode env f
  | 0, _, _ => ssimC_zero env
  | f + 1, mode, hμ =>
    { whnfCore := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_whnfCore_spec henv
          (whnfCoreBodyC_spec hμ (ssimC_all env henv f mode hμ) henv)
          hs hw)
      whnf := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_whnf_spec henv
          (whnfBodyC_spec (ssimC_all env henv f mode hμ) henv) hs hw)
      infer := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_infer_spec henv
          (inferBodyC_spec (ssimC_all env henv f mode hμ) henv) hs hw)
      defeq := fun hs hdena hdenb hwa hwb => by
        obtain rfl := hdena
        obtain rfl := hdenb
        exact SimC.of_tripleVC (memoBI_defeq_spec henv
          (fun hs hwa hwb => defeqBodyC_spec (ssimC_all env henv f mode hμ) henv hs hwa hwb)
          hs hwa hwb)
      -- the eager slot (task #353): the eager tower's memoized `defeq`
      -- on the eager tower's memos (task #361); its fueled side has the
      -- eager tower's runs (`defeqE_def`)
      defeqE := fun {s₀ d i j a b} hs hdena hdenb hwa hwb => by
        have hE : mode.toEager.verifiedChecks = true := by
          rw [CheckMode.verifiedChecks_toEager]; exact hμ
        refine SimC.congr_fueled (p := (fueledFns mode.toEager env).defeq d a b)
          (fun F => defeqE_def env F d a b) ?_
        show SimC mode env s₀ RelVC
          (withEagerMemos mode ((coreKnotI mode.toEager (mkFEnv env) (f + 1)).defeq d i j)) _
        obtain rfl := hdena
        obtain rfl := hdenb
        exact SimC.eagerMemos hs (fun hs₁ => SimC.of_tripleVC (memoBI_defeq_spec henv
          (fun hs hwa hwb =>
            defeqBodyC_spec (ssimC_all env henv f mode.toEager hE) henv hs hwa hwb)
          hs₁ hwa hwb))
      -- the io slot (task #172 B4): the io body at every mode, in both
      -- knots
      inferIO := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_inferIO_spec henv
          (inferBodyIOC_spec (ssimC_all env henv f mode hμ) henv) hs hw) }

/-- The cached knot simulates the fueled families at
every fuel.  The wrapper steps tie each entry point at `f + 1` to the
body walks at `f`, which consume the simulation at `f` as their
induction hypothesis — at the knot's mode and, for the eager slot, at
its eager tower's (task #353), so the induction runs over every mode. -/
theorem ssimC (hμ : mode.verifiedChecks = true) (env : Env) (henv : EnvWF env) (f : Nat) :
    SSimC mode env f :=
  ssimC_all env henv f mode hμ

end ConLeche.Cached
