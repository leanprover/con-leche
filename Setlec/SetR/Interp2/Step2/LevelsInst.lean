import Setlec.SetR.Interp2.Step2.Levels

/-!
# The two checker primitives of the level crossing, settled

`Step2/Levels.lean` factored `Denote2InstLevels` into algebra (all
discharged there) plus two statements about the checker alone,
`InferInstLevels` and `WhnfSortInstLevels`, and reported the question
as **not settled**.  This file settles both, and the verdict is the
same for each: **false as stated, and false for one shared reason.**

## The verdict

Both quantify over a **bare `Env`**.  Nothing in either statement says
the stored constants are the ones a checker accepted, and `ConstWF`'s
`allLevelParamsDefined` clause is exactly what they need:

* a stored **type** may mention a level parameter that is not in its
  own `levelParams`.  Then `inferTypeCore` on `.const c []` returns a
  type carrying that parameter, while the subject `.const c []`
  contains no level at all — so instantiating the subject cannot move
  the inferred type.  `not_inferInstLevels`.
* a stored **value** may do the same.  Then `whnf` delta-unfolds
  `.const c []` to a sort carrying that parameter, and again the
  subject has no level for the instantiation to reach.
  `not_whnfSortInstLevels`.

This is not a quibble about a missing side condition: the same escape
sinks `SortOfEInstLevels` (`not_sortOfEInstLevels`), which is a
statement the delta exit consumes directly.

## What survives, and why the repair is free

`EnvWF` — and the consumer **already has it**.  `Denote2InstLevels` is
stated over an `EnvS2 V env`, whose `base : EnvS V env` carries a
`wf : EnvWF env` field.  So the factoring, not the metatheorem, is what
dropped the hypothesis; adding it back costs the consumer nothing.

The `…W` forms below are the two primitives under `EnvWF`, and the
whole chain of `Step2/Levels.lean` is re-derived through them, ending
at `Denote2InstLevels` exactly as before (`denote2_instLevels_ofW`).
The escape environments are exhibited **not** to be `EnvWF`
(`escEnvT_not_wf`, `escEnvV_not_wf`), and `EnvWF` is exhibited as
reachable (`envWF_empty`), so the repaired statements are neither
refuted by the witnesses nor vacuous.

`infer_const_instLevels` proves the repair *at the very clause the
refutation attacks*, at the same fuel and with no slack — the positive
half of the finding, and the algebraic kit
(`Level.subst_comp_of_defined`, `instLevels_comp_of_defined`) that any
later discharge of the `…W` forms will need at every `.const` clause
and at every delta step.

## The general `whnf` form: seal 19's "expect false" is now "false"

`Step2/Levels.lean` recorded, without a witness, that the *general*
"`whnf` commutes with instantiation, as an equality on reducts" should
be expected false, and restricted primitive 2 to runs landing on a
`.sort` on the argument that a sort is terminal for `whnf`.

`WhnfInstLevels` states the general form and `not_whnfInstLevels`
refutes it **in the empty environment**, so the refutation survives
`EnvWF` and every other environment hypothesis.  The witness is not
the `piResultNeverZero` rescue seal 19 predicted it would be — it is
`whnfCore`'s **beta certificate**: the redex

```
(fun _ : Sort p => Prop) (x : Prop)
```

is stuck at the parameter (`Level.isEquiv 0 p = some false`) and
beta-reduces at `p := 0`.  One level-sensitive guard, no environment,
no inductives.

**The sort-terminality argument holds, and the witness is what shows
it holds rather than merely being unrefuted.**  The uninstantiated run
lands on the *stuck redex*, which is not a `.sort`, so
`WhnfSortInstLevels`' hypothesis is unreachable at the witness; and the
divergence is one-directional (the instantiated side reduces further),
which is the direction `whnfSortInstLevels_of_upTo` needs.

The witness also names the **correct general shape**: not an equality
of reducts but a *simulation* — the instantiated subject and the
substituted reduct have a common head normal form
(`WhnfInstLevelsUpTo`).  It is untouched by the witness
(`whnfInstLevelsUpTo_at_stall`) and it implies the narrow form
(`whnfSortInstLevels_of_upTo`), because a sort is its own whnf.  That
is the statement a discharge should aim at.

## Where the argument stalls, stated honestly

The `…W` forms are **not proved here and no proof is claimed.** Two
things block a discharge, and both are recorded rather than worked
around:

1. **The two primitives are not independent, and the suggested order
   inverts.**  `InferInstLevels`' own `.app` clause needs `whnf` to
   commute at a `.forallE`, and its `.proj` clause needs `whnf` to
   commute at a **const-headed application** — i.e. at arbitrary
   reducts, the shape `not_whnfInstLevels` refutes.  So primitive 1
   cannot be discharged from primitive 2; it needs the *simulation*
   form, which is why that form is stated here.
2. **Guard monotonicity is assumed nowhere and proved nowhere.**  Every
   step of the informal argument ("instantiation only makes guards
   fire more") is a statement about `defeq`, which calls `whnf` and
   `infer`.  The three are the same knot, so the discharge is one
   simultaneous induction — the level-side twin of `shiftClaims` that
   `Step2/Levels.lean` already named as missing.

**Trap-check.**  `WhnfInstLevels` and `WhnfInstLevelsUpTo` assert a
checker success as a conclusion, so the smallest-fuel test applies and
comes back **vacuous, not clean**, exactly as for the four `Prop`s of
`Step2/Levels.lean`: at `F = 0` and `F = 1` every `whnf` run is an
error, so the hypothesis is unsatisfiable.  Per seal 11 that is worth
nothing as a bill of health — and it is not what is being relied on
here, since both new shapes come with an explicit witness
(`not_whnfInstLevels`) or an explicit positive instance
(`whnfInstLevelsUpTo_at_stall`) at a fuel where the runs are real.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec (CheckMode Env Expr Name Level)

variable {μ : CheckMode} {env : Env}

/-! ## Part 0 — the algebra `EnvWF` is the hypothesis for

Composing two level substitutions collapses to one *only* when the
inner substitution reaches every parameter of the subject.  That is
`allLevelParamsDefined`, i.e. `ConstWF`'s second clause — i.e.
`EnvWF`. -/

private theorem substGo_comp (ks : List Name) (vs : List Level) :
    ∀ (ps : List Name) (ws : List Level), ps.length = ws.length →
      ∀ n : Name, ps.contains n = true →
        Level.subst ks vs (Level.subst.go ps ws n)
          = Level.subst.go ps (ws.map (Level.subst ks vs)) n := by
  intro ps
  induction ps with
  | nil => intro ws _ n hn; simp at hn
  | cons p ps ih =>
    intro ws hlen n hn
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [List.map, Level.subst.go]
      by_cases he : p = n
      · rw [if_pos he, if_pos he]
      · rw [if_neg he, if_neg he]
        refine ih ws (by simpa using hlen) n ?_
        simp only [List.contains_cons, Bool.or_eq_true,
          beq_iff_eq] at hn
        exact hn.resolve_left fun hx => he hx.symm

/-- **Two level substitutions compose into one**, provided the inner
one is defined on every parameter of the subject. -/
theorem Level.subst_comp_of_defined (ks : List Name) (vs : List Level)
    (ps : List Name) (ws : List Level) (hlen : ps.length = ws.length) :
    ∀ l : Level, l.allParamsDefined ps = true →
      Level.subst ks vs (Level.subst ps ws l)
        = Level.subst ps (ws.map (Level.subst ks vs)) l := by
  intro l
  induction l with
  | zero => intro _; rfl
  | param n => exact substGo_comp ks vs ps ws hlen n
  | succ l ih =>
    intro h
    simp only [Level.subst, Level.succ.injEq]
    exact ih h
  | max a b iha ihb =>
    intro h
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, Level.max.injEq]
    exact ⟨iha h.1, ihb h.2⟩
  | imax a b iha ihb =>
    intro h
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, Level.imax.injEq]
    exact ⟨iha h.1, ihb h.2⟩

/-- The `Expr` form: instantiating a term whose parameters are all in
`ps`, then instantiating again, is one instantiation at the mapped
level list.  This is the step `unfoldDefinition` and `inferBody`'s
`.const` clause take, and the exact place the refutations below strike
when the hypothesis is missing. -/
theorem instLevels_comp_of_defined (ks : List Name) (vs : List Level)
    (ps : List Name) (ws : List Level) (hlen : ps.length = ws.length) :
    ∀ e : Expr, e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps ws).instantiateLevelParams ks vs
        = e.instantiateLevelParams ps
            (ws.map (Level.subst ks vs)) := by
  have hl := Level.subst_comp_of_defined ks vs ps ws hlen
  intro e
  induction e with
  | bvar i => intro _; rfl
  | lit l => intro _; rfl
  | sort u =>
    intro h
    simp only [Expr.instantiateLevelParams, hl u h]
  | const n us =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, List.map_map,
      Expr.const.injEq, true_and]
    exact List.map_congr_left fun u hu => hl u (h u hu)
  | fvar i n ty ih =>
    intro h
    simp only [Expr.instantiateLevelParams, ih h]
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam n ty b mb ihty ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihty h.1, ihb h.2]
  | forallE n ty b mb ihty ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihty h.1, ihb h.2]
  | letE n ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, ihty h.1.1, ihv h.1.2,
      ihb h.2]
  | proj s i e ih =>
    intro h
    simp only [Expr.instantiateLevelParams, ih h]

/-! ## Part 1 — the two primitives are false as stated

Both witnesses are the same shape: a stored constant whose `levelParams`
is `[]` and whose stored expression mentions a level parameter anyway.
No checker ever builds such an environment — `ConstWF` forbids it — and
nothing in `InferInstLevels`/`WhnfSortInstLevels` rules it out. -/

/-- The escaping parameter the two witnesses use. -/
private def escP : Name := .str .anonymous "escP"

/-- The stored constant the two witnesses use. -/
private def escC : Name := .str .anonymous "escC"

/-- The escape environment for **inference**: one axiom whose *type*
mentions `escP`, which is not among its (empty) `levelParams`. -/
def escEnvT : Env := ⟨[.axiomInfo ⟨escC, [], .sort (.param escP)⟩]⟩

/-- The escape environment for **reduction**: one definition whose
*value* mentions `escP`, which is not among its (empty)
`levelParams`. -/
def escEnvV : Env :=
  ⟨[.defnInfo ⟨escC, [], .sort .zero⟩ (.sort (.param escP))
      (.regular 0)]⟩

/-- The subject both witnesses run on carries **no level at all**, so
its level instantiation is the identity. -/
private theorem esc_subject_inst (ks : List Name) (us : List Level) :
    (Expr.const escC []).instantiateLevelParams ks us
      = .const escC [] := rfl

/-- Inference reads the escaping parameter straight out of the stored
type. -/
private theorem escEnvT_infer (μ : CheckMode) (F d : Nat) :
    inferTypeCore μ escEnvT (F + 1) d (.const escC [])
      = .ok (.sort (.param escP)) := rfl

private theorem whnfLoopFuel_succ2 :
    ∃ n, Setlec.whnfLoopFuel = n + 1 + 1 :=
  ⟨99998, by unfold Setlec.whnfLoopFuel; rfl⟩

/-- Reduction reads the escaping parameter straight out of the stored
value: one delta step, then the sort is terminal. -/
private theorem escEnvV_whnf (μ : CheckMode) (F d : Nat) :
    whnf μ escEnvV (F + 3) d (.const escC [])
      = .ok (.sort (.param escP)) := by
  obtain ⟨k, hk⟩ := whnfLoopFuel_succ2
  show whnfLoop (pureFns μ escEnvV (F + 2)) escEnvV d
    Setlec.whnfLoopFuel _ = _
  rw [hk]
  rfl

/-- **Primitive 2 is false as stated.**  `whnf` delta-unfolds
`escC` to `Sort escP`, and the subject `.const escC []` has no level
for `instantiateLevelParams` to reach, so the conclusion would have to
name `Sort 0` while every run answers `Sort escP`. -/
theorem not_whnfSortInstLevels (μ : CheckMode) :
    WhnfSortInstLevels μ escEnvV → False := by
  intro h
  obtain ⟨F', -, hF'⟩ := h [escP] [.zero] 3 0 (.const escC [])
    (.param escP) (escEnvV_whnf μ 0 0)
  rw [esc_subject_inst] at hF'
  have h1 := (knotFuelMono μ escEnvV).2.1
    (Nat.le_max_left F' (F' + 3)) hF'
  have h2 := (knotFuelMono μ escEnvV).2.1
    (Nat.le_max_right F' (F' + 3)) (escEnvV_whnf μ F' 0)
  rw [h1] at h2
  injection h2 with h3
  injection h3 with h4
  exact nomatch h4

/-- **Primitive 1 is false as stated**, and for the same reason one
clause earlier: `inferBody`'s `.const` clause returns the stored type
verbatim (the level list is empty, so its own instantiation is the
identity), while the subject offers the outer substitution nothing to
act on. -/
theorem not_inferInstLevels (μ : CheckMode) :
    InferInstLevels μ escEnvT → False := by
  intro h
  obtain ⟨F', -, hF'⟩ := h [escP] [.zero] 1 0 (.const escC [])
    (.sort (.param escP)) (escEnvT_infer μ 0 0)
  rw [esc_subject_inst] at hF'
  have h1 := (knotFuelMono μ escEnvT).1
    (Nat.le_max_left F' (F' + 1)) hF'
  have h2 := (knotFuelMono μ escEnvT).1
    (Nat.le_max_right F' (F' + 1)) (escEnvT_infer μ F' 0)
  rw [h1] at h2
  injection h2 with h3
  injection h3 with h4
  exact nomatch h4

/-- The escape is **not** an artefact of the factoring: it reaches the
statement the delta exit consumes.  `sortOfE` on the escape
environment returns the assignment's value at `escP`, and the two
sides of the crossing read two assignments that disagree there. -/
theorem not_sortOfEInstLevels (μ : CheckMode) :
    SortOfEInstLevels μ escEnvT → False := by
  intro h
  have hrun : ∀ (ψ : Name → Nat) (F d : Nat),
      sortOfE μ escEnvT ψ (F + 3) d (.const escC [])
        = some (ψ escP) := by
    intro ψ F d
    unfold sortOfE
    rw [show inferTypeCore μ escEnvT (F + 3) d (.const escC [])
      = .ok (.sort (.param escP)) from escEnvT_infer μ (F + 2) d]
    simp only [Except.toOption]
    rw [show whnf μ escEnvT (F + 3) d (.sort (.param escP))
      = .ok (.sort (.param escP)) from whnf_sort escEnvT (F + 1) d _]
    rfl
  obtain ⟨F', -, hF'⟩ := h (fun _ => 1) [escP] [.zero] 3 0
    (.const escC []) 0 (by
      rw [hrun (Level.substFn (fun _ => 1) [escP] [.zero]) 0 0]
      rfl)
  rw [esc_subject_inst] at hF'
  have h1 := sortOfE_fuelMono (f' := max F' (F' + 3))
    (Nat.le_max_left F' (F' + 3)) hF'
  have h2 := sortOfE_fuelMono (f' := max F' (F' + 3))
    (Nat.le_max_right F' (F' + 3)) (hrun (fun _ => 1) F' 0)
  rw [h1] at h2
  exact nomatch h2

end Setlec.SetR.Interp2
