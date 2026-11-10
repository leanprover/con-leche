module

public import ConLeche.Verify.Cached.DiscC5
import ConLeche.Verify.Cached.Grind

public section

/-!
# The cached knot: memo wrappers and the conditional simulation

`SSimC mode eager env f` (task #163; declared in
`ConLeche/Verify/Cached/DiscC1.lean`): at fuel `f`, every cached entry point
(`whnfI mode (mkFEnv env) eager f`, …) simulates the
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

variable {mode : CheckMode} {eager : Bool}

/-! ## The memo-wrapper steps -/

section Wrappers

variable {env : Env} {f : Nat}

/-! ### The whnfCore memos

The easy cases return before either memo (`whnfCoreEasy`,
`Runs.whnfCore_easy`).  The two modes of `whnfCore` (official
`cheap_proj`) under two memos; one triple covers both (`vcgen` splits the
knot's `if c`). -/

/-- An easy case is its own whnfCore answer (`whnfCoreBody`'s value arms). -/
theorem Runs.whnfCore_easy {c : Bool} {d : Nat} {i : Expr} (h : whnfCoreEasy i = true) :
    Runs ((fueledFns mode eager env).whnfCore c d i) i :=
  ⟨1, by cases i <;> first | rfl | exact nomatch h⟩
grind_pattern [conleche_grind] Runs.whnfCore_easy =>
  Runs ((fueledFns mode eager env).whnfCore c d i) i

/-- A full whnfCore memo hit answers the fueled whnfCore, well scoped. -/
theorem CSOK.whnfCore_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfCoreC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnfCore false d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCore_hit =>
  CSOK mode eager env s, s.whnfCoreC[i]?, Runs ((fueledFns mode eager env).whnfCore false d i) r

/-- A cheap whnfCore memo hit answers the fueled cheap whnfCore. -/
theorem CSOK.whnfCoreCheap_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfCoreCheapC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnfCore true d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfCoreCheapC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnfCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnfCoreCheap_hit =>
  CSOK mode eager env s, s.whnfCoreCheapC[i]?, Runs ((fueledFns mode eager env).whnfCore true d i) r

/-- A body answer is a whnfCore answer one fuel up. -/
theorem Runs.whnfCore_of_body {c : Bool} {d : Nat} {i r : Expr}
    (h : Runs (whnfCoreBody mode (fueledFns mode eager env) env c d i) r) :
    Runs ((fueledFns mode eager env).whnfCore c d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [whnfCoreBody_atF, ← whnfCore_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.whnfCore_of_body =>
  Runs (whnfCoreBody mode (fueledFns mode eager env) env c d i) r, (fueledFns mode eager
      env).whnfCore c d i

theorem CSOK.whnfCore_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hw : Expr.WScoped d i)
    (h : Runs (whnfCoreBody mode (fueledFns mode eager env) env false d i) r) :
    CSOK mode eager env { s with whnfCoreC := s.whnfCoreC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [whnfCoreBody_atF, ← whnfCore_succ] at hF
  exact { hs with
    whnfCoreC := HashMap.insert_backed hs.whnfCoreC ⟨F + 1, fun d' hd' => by
      rw [whnfCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

theorem CSOK.whnfCoreCheap_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hw : Expr.WScoped d i)
    (h : Runs (whnfCoreBody mode (fueledFns mode eager env) env true d i) r) :
    CSOK mode eager env { s with whnfCoreCheapC := s.whnfCoreCheapC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [whnfCoreBody_atF, ← whnfCore_succ] at hF
  exact { hs with
    whnfCoreCheapC := HashMap.insert_backed hs.whnfCoreCheapC ⟨F + 1, fun d' hd' => by
      rw [whnfCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The whnfCore memo wrappers simulate the fueled whnfCore at one fuel
more than their bodies. -/
theorem memoRedEI_whnfCore_spec (henv : EnvWF env)
    (hbody : ∀ c, BodySpec mode eager env
      (whnfCoreBodyI mode (mkFEnv env) eager f c)
      (whnfCoreBody mode (fueledFns mode eager env) env c))
    {c : Bool} {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode eager env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ whnfCoreI mode (mkFEnv env) eager (f + 1) c d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).whnfCore c d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.whnfCore_insert henv, CSOK.whnfCoreCheap_insert henv] =>
    vcgen [whnfCoreI.eq_def, memoRedEI, BodySpec.triple (hbody true),
      BodySpec.triple (hbody false)] <;> finish

/-! ### The whnf memo, by `vcgen` and `grind`

A hit reads the backed `CSOK.whnfC` clause at the query (`CSOK.whnf_hit`);
a miss runs the body and inserts its answer, backed one fuel up by the
depth-invariant run (`CSOK.whnf_insert`, `Runs.whnf_of_body`); an easy
case returns before the memo (`whnfEasy`, `Runs.whnf_easy`). -/

/-- An easy case is its own whnf answer: it head-normalizes to itself,
is no literal operation and does not unfold. -/
theorem Runs.whnf_easy {d : Nat} {i : Expr} (h : whnfEasy i = true) :
    Runs ((fueledFns mode eager env).whnf d i) i := by
  obtain ⟨n, hn⟩ := whnfLoopFuel_succ
  refine ⟨2, ?_⟩
  show whnfLoop (pureFns mode eager env 1) env d whnfLoopFuel i = .ok i
  rw [hn]
  cases i <;> first | rfl | exact nomatch h
grind_pattern [conleche_grind] Runs.whnf_easy =>
  Runs ((fueledFns mode eager env).whnf d i) i

/-- A whnf memo hit answers the fueled whnf, well scoped. -/
theorem CSOK.whnf_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.whnfC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).whnf d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.whnfC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, whnf_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.whnf_hit =>
  CSOK mode eager env s, s.whnfC[i]?, Runs ((fueledFns mode eager env).whnf d i) r

/-- A body answer is a whnf answer one fuel up. -/
theorem Runs.whnf_of_body {d : Nat} {i r : Expr}
    (h : Runs (whnfBody (fueledFns mode eager env) env d i) r) :
    Runs ((fueledFns mode eager env).whnf d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [whnfBody_atF, ← whnf_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.whnf_of_body =>
  Runs (whnfBody (fueledFns mode eager env) env d i) r, (fueledFns mode eager env).whnf d i

/-- Inserting a body answer into the whnf memo keeps the invariant: the
entry is backed one fuel up at every depth the key is scoped at. -/
theorem CSOK.whnf_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hw : Expr.WScoped d i)
    (h : Runs (whnfBody (fueledFns mode eager env) env d i) r) :
    CSOK mode eager env { s with whnfC := s.whnfC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [whnfBody_atF, ← whnf_succ] at hF
  exact { hs with
    whnfC := HashMap.insert_backed hs.whnfC ⟨F + 1, fun d' hd' => by
      rw [whnf_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The whnf memo wrapper simulates the fueled whnf at one fuel more
than its body.  `CSOK.whnf_insert` is in the `sym` list instantiated at
`henv`: its pattern is the inserted state, which every miss builds. -/
theorem memoEI_whnf_spec (henv : EnvWF env)
    (hbody : BodySpec mode eager env (whnfBodyI mode (mkFEnv env) eager f)
      (whnfBody (fueledFns mode eager env) env))
    {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ whnfI mode (mkFEnv env) eager (f + 1) d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).whnf d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.whnf_insert henv] =>
    vcgen [whnfI.eq_def, memoEI, hbody.triple] <;> finish

/-! ### The infer memo -/

/-- An infer memo hit answers the fueled infer, well scoped. -/
theorem CSOK.infer_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.inferC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).infer d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.inferC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, inferTypeCore_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.infer_hit =>
  CSOK mode eager env s, s.inferC[i]?, Runs ((fueledFns mode eager env).infer d i) r

/-- A body answer is an infer answer one fuel up. -/
theorem Runs.infer_of_body {d : Nat} {i r : Expr}
    (h : Runs (inferBody (fueledFns mode eager env) env d i) r) :
    Runs ((fueledFns mode eager env).infer d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [inferBody_atF, ← inferTypeCore_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.infer_of_body =>
  Runs (inferBody (fueledFns mode eager env) env d i) r, (fueledFns mode eager env).infer d i

theorem CSOK.infer_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hw : Expr.WScoped d i)
    (h : Runs (inferBody (fueledFns mode eager env) env d i) r) :
    CSOK mode eager env { s with inferC := s.inferC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [inferBody_atF, ← inferTypeCore_succ] at hF
  exact { hs with
    inferC := HashMap.insert_backed hs.inferC ⟨F + 1, fun d' hd' => by
      rw [inferTypeCore_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The infer memo wrapper simulates the fueled infer at one fuel more
than its body. -/
theorem memoEI_infer_spec (henv : EnvWF env)
    (hbody : BodySpec mode eager env (inferBodyI mode (mkFEnv env) eager f false)
      (inferBody (fueledFns mode eager env) env))
    {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ inferI mode (mkFEnv env) eager (f + 1) false d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).infer d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.infer_insert henv] =>
    vcgen [inferI.eq_def, memoEI, hbody.triple] <;> finish

/-! ### The io memo (task #172 B4)

The slot is the io body under its own memo (`CState.inferIOC`); a hit
consumes the io clause — the weaker one — and a miss re-inserts in
depth-universal form through `inferTypeIO_depth_inv`. -/

/-- An io memo hit answers the fueled io slot, well scoped. -/
theorem CSOK.inferIO_hit (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hl : s.inferIOC[i]? = some r) (hw : Expr.WScoped d i) :
    Runs ((fueledFns mode eager env).inferIO d i) r ∧ Expr.WScoped d r := by
  obtain ⟨F, hall⟩ := hs.inferIOC i r hl
  have hrun := hall d hw.to_wscopedB
  exact ⟨⟨F, hrun⟩, inferTypeIO_WScoped henv F hrun hw⟩
grind_pattern [conleche_grind] CSOK.inferIO_hit =>
  CSOK mode eager env s, s.inferIOC[i]?, Runs ((fueledFns mode eager env).inferIO d i) r

/-- An io body answer is an io-slot answer one fuel up. -/
theorem Runs.inferIO_of_body {d : Nat} {i r : Expr}
    (h : Runs (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d i) r) :
    Runs ((fueledFns mode eager env).inferIO d i) r := by
  obtain ⟨F, hF⟩ := h
  rw [inferBodyIO_atF, ← inferTypeIO_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.inferIO_of_body =>
  Runs (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d i) r,
  (fueledFns mode eager env).inferIO d i

theorem CSOK.inferIO_insert (henv : EnvWF env) {s : CState} {d : Nat} {i r : Expr}
    (hs : CSOK mode eager env s) (hw : Expr.WScoped d i)
    (h : Runs (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env d i) r) :
    CSOK mode eager env { s with inferIOC := s.inferIOC.insert i r } := by
  obtain ⟨F, hF⟩ := h
  rw [inferBodyIO_atF, ← inferTypeIO_succ] at hF
  exact { hs with
    inferIOC := HashMap.insert_backed hs.inferIOC ⟨F + 1, fun d' hd' => by
      rw [inferTypeIO_depth_inv henv (F + 1) hd' hw.to_wscopedB]; exact hF⟩ }

/-- The io memo wrapper simulates the fueled io slot at one fuel more
than its body. -/
theorem memoEI_inferIO_spec (henv : EnvWF env)
    (hbody : BodySpec mode eager env
      (inferBodyIOI mode (mkFEnv env) eager f)
      (inferBodyIO (CoreFns.ioView (fueledFns mode eager env)) env))
    {s₀ : CState} {d : Nat} {i : Expr} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ inferI mode (mkFEnv env) eager (f + 1) true d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).inferIO d i) r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.inferIO_insert henv] =>
    vcgen [inferI.eq_def, memoEI, hbody.triple] <;> finish

/-! ### The defeq memo -/

/-- A defeq memo hit answers the fueled defeq. -/
theorem CSOK.defeq_hit {s : CState} {d : Nat} {a b : Expr} {r : Bool}
    (hs : CSOK mode eager env s) (hl : s.defeqC[(a, b)]? = some r) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    Runs ((fueledFns mode eager env).defeq d a b) r := by
  obtain ⟨F, hall⟩ := hs.defeqC a b r hl
  exact ⟨F, hall d hwa.to_wscopedB hwb.to_wscopedB⟩
grind_pattern [conleche_grind] CSOK.defeq_hit =>
  CSOK mode eager env s, s.defeqC[(a, b)]?, Runs ((fueledFns mode eager env).defeq d a b) r

/-- A body answer is a defeq answer one fuel up. -/
theorem Runs.defeq_of_body {d : Nat} {a b : Expr} {r : Bool}
    (h : Runs (defeqBody mode eager (fueledFns mode eager env) env d a b) r) :
    Runs ((fueledFns mode eager env).defeq d a b) r := by
  obtain ⟨F, hF⟩ := h
  rw [defeqBody_atF, ← isDefEqCore_succ] at hF
  exact ⟨F + 1, hF⟩
grind_pattern [conleche_grind] Runs.defeq_of_body =>
  Runs (defeqBody mode eager (fueledFns mode eager env) env d a b) r, (fueledFns mode eager
      env).defeq d a b

theorem CSOK.defeq_insert (henv : EnvWF env) {s : CState} {d : Nat} {a b : Expr} {r : Bool}
    (hs : CSOK mode eager env s) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (h : Runs (defeqBody mode eager (fueledFns mode eager env) env d a b) r) :
    CSOK mode eager env { s with defeqC := s.defeqC.insert (a, b) r } := by
  obtain ⟨F, hF⟩ := h
  rw [defeqBody_atF, ← isDefEqCore_succ] at hF
  -- the clause is curried in the key pair
  exact { hs with
    defeqC := fun a' b' r' => HashMap.insert_backed
      (P := fun k r => ∃ F, ∀ d, k.1.wscopedB d = true → k.2.wscopedB d = true →
        isDefEqCore mode eager env F d k.1 k.2 = .ok r)
      (fun k v => hs.defeqC k.1 k.2 v) ⟨F + 1, fun d' hda' hdb' => by
        rw [isDefEqCore_depth_inv henv (F + 1) hda' hdb' hwa.to_wscopedB hwb.to_wscopedB]
        exact hF⟩ (a', b') r' }

/-- The defeq memo wrapper simulates the fueled defeq at one fuel more
than its body. -/
theorem memoBI_defeq_spec (henv : EnvWF env)
    (hbody : BodySpecB mode eager env (defeqBodyI mode (mkFEnv env) eager f)
      (defeqBody mode eager (fueledFns mode eager env) env))
    {s₀ : CState} {d : Nat} {a b : Expr} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqI mode (mkFEnv env) eager (f + 1) d a b
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).defeq d a b) r; ⊤⦄ := by
  sym only [conleche_grind, CSOK.defeq_insert henv] =>
    vcgen [defeqI.eq_def, memoBI, hbody.triple] <;> finish

end Wrappers

/-! ## The knot induction -/

private theorem ssimC_all (env : Env) (henv : EnvWF env) :
    ∀ (f : Nat) (eager : Bool), SSimC .verified eager env f
  | 0, _ => ssimC_zero env
  | f + 1, eager =>
    { whnfCore := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoRedEI_whnfCore_spec henv
          (whnfCoreBodyC_spec (ssimC_all env henv f eager) henv)
          hs hw)
      whnf := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_whnf_spec henv
          (whnfBodyC_spec (ssimC_all env henv f eager) henv) hs hw)
      infer := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_infer_spec henv
          (inferBodyC_spec (ssimC_all env henv f eager) henv) hs hw)
      defeq := fun hs hdena hdenb hwa hwb => by
        obtain rfl := hdena
        obtain rfl := hdenb
        exact SimC.of_tripleVC (memoBI_defeq_spec henv
          (fun hs hwa hwb => defeqBodyC_spec (ssimC_all env henv f eager) henv hs hwa hwb)
          hs hwa hwb)
      -- the eager slot (task #353): the eager tower's memoized `defeq`
      -- on the eager tower's memos (task #361); its fueled side has the
      -- eager tower's runs (`defeqE_def`)
      defeqE := fun {s₀ d i j a b} hs hdena hdenb hwa hwb => by
        refine SimC.congr_fueled (p := (fueledFns .verified true env).defeq d a b)
          (fun F => defeqE_def env F d a b) ?_
        have hE : defeqEI .verified (mkFEnv env) eager (f + 1) d i j =
            withEagerMemos eager (defeqI .verified (mkFEnv env) true (f + 1) d i j) := by
          rw [defeqEI.eq_def, defeqI.eq_def]
        rw [hE]
        obtain rfl := hdena
        obtain rfl := hdenb
        exact SimC.eagerMemos hs (fun hs₁ => SimC.of_tripleVC (memoBI_defeq_spec henv
          (fun hs hwa hwb =>
            defeqBodyC_spec (ssimC_all env henv f true) henv hs hwa hwb)
          hs₁ hwa hwb))
      -- the io slot (task #172 B4): the io body at every mode, in both
      -- knots
      inferIO := fun hs hden hw => by
        obtain rfl := hden
        exact SimC.of_triple relEC_diag (memoEI_inferIO_spec henv
          (inferBodyIOC_spec (ssimC_all env henv f eager) henv) hs hw) }

/-- The cached knot simulates the fueled families at
every fuel.  The wrapper steps tie each entry point at `f + 1` to the
body walks at `f`, which consume the simulation at `f` as their
induction hypothesis — at the knot's flag and, for the eager slot, at
`eager := true` (task #353), so the induction runs over both flags. -/
theorem ssimC (env : Env) (henv : EnvWF env) (f : Nat) :
    SSimC .verified eager env f :=
  ssimC_all env henv f eager

end ConLeche.Cached
