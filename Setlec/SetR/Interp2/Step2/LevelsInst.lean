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
stated over an `EnvS2U V env`, whose `base : EnvS V env` carries a
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

## The general `whnf` form, and the shape that survives

`Step2/Levels.lean` recorded, without a witness, that the *general*
"`whnf` commutes with instantiation, as an equality on reducts" should
be expected false, and restricted primitive 2 to runs landing on a
`.sort` on the argument that a sort is terminal for `whnf`.

`WhnfInstLevels` states the general form; `not_whnfInstLevels` refutes
it, but only by the Part 1 escape (`whnfSortInstLevels_of_general`
makes the narrow form one of its instances).  **An `EnvWF`-surviving
refutation of the general form is identified here and not mechanized**,
and that gap is stated rather than papered over — see below.

**The sort-terminality argument holds, and it is mechanized rather
than asserted.**  `whnfSortInstLevels_of_upTo` proves that at a `.sort`
reduct the *simulation* form collapses to the narrow one: a sort is its
own head normal form, so the further reduction the simulation permits
has nowhere to go.  That is exactly the argument `Step2/Levels.lean`
gave informally, now a theorem, and it is what makes the narrow shape
the right restriction rather than a hopeful one.

`WhnfInstLevelsUpTo` is the **shape a discharge should aim at**: not an
equality of reducts, but the instantiated subject and the substituted
reduct having a *common* head normal form.  It admits the divergence
that condemns the equality form and still implies primitive 2.

## The seam has a level-sensitive guard seal 19's list missed

Seal 19's suspects were both in `iotaRec`'s stuck-major rescue.
`whnfCore`'s **beta certificate** is a third, it is in the seam, and it
needs **no environment and no inductives**: the redex

```
(fun _ : Sort p => Prop) (x : Prop)
```

is stuck at the parameter and beta-reduces at `p := 0`, because
`Level.isEquiv 0 p` is `false` and `Level.isEquiv 0 0` is `true`.
`betaCertLevel_flips` mechanizes the guard, which is where the finding
lives.

**What is not done, and why.**  Lifting that guard flip to two `whnf`
runs — which is what would refute `WhnfInstLevels` in the *empty*
environment and so survive `EnvWF` — is **not** carried out here.
Evaluating both runs (`whnf .setModel Env.empty 20 1`) does show the
stuck redex on one side and `Prop` on the other, but an evaluation is
not a proof and is not offered as one.  The obstacle is concrete:
`Level.isEquiv` does not reduce definitionally under the literal
`Level.defaultFuel` (`decide` gets stuck, exactly as
`Step2/Levels.lean`'s `leq_param_zero` records), so a run-level proof
must thread three hand-proved `isEquiv` values through `proofIrrel`'s
two nested `infer`/`whnf` calls and three `@[irreducible]` loop-fuel
peels; `simp` with the fuel witnesses supplied unfolds the bodies
faster than it reduces the scrutinees and does not terminate usefully.
**So: the general form under `EnvWF` is still recorded as *expect
false*, with a named candidate witness and a mechanized guard — one
step short of a verdict, and reported as such.**

## Where the argument stalls, stated honestly

The `…W` forms are **not proved here and no proof is claimed.** Two
things block a discharge, and both are recorded rather than worked
around:

1. **The two primitives are not independent, and the suggested order
   inverts.**  `InferInstLevels`' own `.app` clause needs `whnf` to
   commute at a `.forallE`, and its `.proj` clause needs `whnf` to
   commute at a **const-headed application** — i.e. at arbitrary
   reducts, which is the general form, not the narrow one.  So
   primitive 1 cannot be discharged from primitive 2; it needs
   `WhnfInstLevelsUpTo`, which is why that shape is stated here.
2. **Guard monotonicity is assumed nowhere and proved nowhere.**  Every
   step of the informal argument ("instantiation only makes guards
   fire more") is a statement about `defeq`, which calls `whnf` and
   `infer`.  The three are the same knot, so the discharge is one
   simultaneous induction — the level-side twin of `shiftClaims` that
   `Step2/Levels.lean` already named as missing.

Consequently **`Denote2InstLevels` does not close**: seal 12's open
metatheorem stays open, with its residue now two `EnvWF`-carrying
statements instead of two bare-`Env` ones that were false.

**Trap-check.**  `WhnfInstLevels` and `WhnfInstLevelsUpTo` assert a
checker success as a conclusion, so the smallest-fuel test applies and
comes back **vacuous, not clean**, exactly as for the four `Prop`s of
`Step2/Levels.lean`: at `F = 0` and `F = 1` every `whnf` run is an
error, so the hypothesis is unsatisfiable.  Per seal 11 that is worth
nothing as a bill of health, and nothing here rests on it — the two
statements this file *settles* are settled by explicit witnesses at
fuels where the runs are real.

**A recipe-book check that could not be performed, reported as not
performed.**  The book asks for a satisfiability witness *in the very
case that killed the old shape*.  Here the case that kills the old
shape is an environment `ConstWF` forbids, so there is no repaired
instance "at" it: the structural answer is that the repaired forms
simply do not quantify over that environment (`escEnvT_not_wf`,
`escEnvV_not_wf`).  `envWF_empty` is supplied instead, which shows the
repaired hypothesis is reachable but is *not* the check the book asked
for.
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

/-! ## Part 2 — the repair, and the whole chain re-derived through it

The missing hypothesis is `EnvWF`, and the consumer already holds it:
`Denote2InstLevels` is stated over an `EnvS2U V env`, whose
`base : EnvS V env` carries `wf : EnvWF env`.  So the `…W` forms below
cost the consumer nothing, and `denote2_instLevels_ofW` re-derives the
crossing from them with the same proof `Step2/Levels.lean` already
has. -/

/-- **Primitive 1, repaired**: inference commutes with level
instantiation *over a well-formed environment*. -/
def InferInstLevelsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → InferInstLevels μ env

/-- **Primitive 2, repaired.** -/
def WhnfSortInstLevelsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → WhnfSortInstLevels μ env

/-- The `sortOfE` residue, repaired. -/
def SortOfEInstLevelsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → SortOfEInstLevels μ env

/-- The `lamSortE` residue, repaired. -/
def LamSortEInstLevelsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → LamSortEInstLevels μ env

theorem sortOfEInstLevelsW_of (hi : InferInstLevelsW μ env)
    (hw : WhnfSortInstLevelsW μ env) : SortOfEInstLevelsW μ env :=
  fun hwf => sortOfEInstLevels_of (hi hwf) (hw hwf)

theorem lamSortEInstLevelsW_of (hi : InferInstLevelsW μ env)
    (hsz : SortOfEInstLevelsW μ env) : LamSortEInstLevelsW μ env :=
  fun hwf => lamSortEInstLevels_of (hi hwf) (hsz hwf)

section Consumer

universe w
variable {V : Type w} [SetTheory V]

/-- **The level crossing for `denote2`, from the repaired primitives.**
The `EnvWF` the refutations exposed as missing is read off the
consumer's own `EnvS2`, so the repair is invisible downstream: this is
`denote2_instLevels_of` with `m.base.wf` threaded. -/
theorem denote2_instLevels_ofW {env : Env} (m : EnvS2UM V μ env)
    (hs : SortOfEInstLevelsW μ env) (hl : LamSortEInstLevelsW μ env) :
    Denote2InstLevels μ m :=
  denote2_instLevels_of m (hs m.base.wf) (hl m.base.wf)

end Consumer

/-! ### The two checks the recipe book asks for

A refutation and a satisfiability witness are different results, and a
repair needs both.  Here: the escape environments are exhibited **not**
to be `EnvWF` (so the witnesses do not also refute the `…W` forms), and
`EnvWF` is exhibited as reachable (so the `…W` forms are not vacuous
implications). -/

/-- The inference witness violates `ConstWF`'s `allLevelParamsDefined`
clause on the stored **type** — which is exactly the clause the
refutation exploits. -/
theorem escEnvT_not_wf : ¬ Setlec.EnvWF escEnvT := by
  intro h
  have hc := (h _ (List.mem_singleton_self _)).2.1
  exact nomatch hc

/-- The reduction witness violates the same clause on the stored
**value**. -/
theorem escEnvV_not_wf : ¬ Setlec.EnvWF escEnvV := by
  intro h
  have hc :=
    ((h _ (List.mem_singleton_self _)).2.2.2.2.1 _ _ _ rfl).2.1
  exact nomatch hc

/-- `EnvWF` is reachable, so the `…W` forms are implications with a
satisfiable hypothesis rather than vacuities. -/
theorem envWF_empty : Setlec.EnvWF Env.empty := by
  intro c hc
  exact absurd hc (List.not_mem_nil)

/-! ### The repair, proved at the clause the refutation attacks

Not a plausibility argument: over a well-formed environment the
`.const` clause of `inferBody` — the clause `not_inferInstLevels`
kills — commutes with level instantiation outright, at the *same*
fuel and with none of the campaign's `∃ F' ≥ F` slack. -/

private theorem infer_const_run {μ : CheckMode} {env : Env}
    (F d : Nat) (n : Name) (ws : List Level) (ci : ConstantInfo)
    (hf : env.find? n = some ci)
    (hlen : ws.length = ci.toConstantVal.levelParams.length) :
    inferTypeCore μ env (F + 1) d (.const n ws)
      = .ok (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams ws) := by
  rw [inferTypeCore_succ]
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, bind,
    Except.bind, pure, Except.pure, hf, if_pos hlen]

private theorem infer_const_inv {μ : CheckMode} {env : Env}
    {F d : Nat} {n : Name} {ws : List Level} {t : Expr}
    (h : inferTypeCore μ env (F + 1) d (.const n ws) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      ws.length = ci.toConstantVal.levelParams.length ∧
      t = ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams ws := by
  rw [inferTypeCore_succ] at h
  simp only [Setlec.inferBody, Setlec.viewM, Expr.view, bind,
    Except.bind, pure, Except.pure] at h
  cases hf : env.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    by_cases hlen : ws.length = ci.toConstantVal.levelParams.length
    · rw [if_pos hlen] at h
      exact ⟨ci, rfl, hlen, (Except.ok.inj h).symm⟩
    · rw [if_neg hlen] at h; exact nomatch h

/-- **`InferInstLevels`' `.const` clause, discharged under `EnvWF`.**
The stored type's own instantiation absorbs the outer one exactly
because `ConstWF` says every parameter it mentions is in
`levelParams`. -/
theorem infer_const_instLevels {F d : Nat} {n : Name}
    {us : List Level} {t : Expr} (henv : Setlec.EnvWF env)
    (ks : List Name) (vs : List Level)
    (h : inferTypeCore μ env (F + 1) d (.const n us) = .ok t) :
    inferTypeCore μ env (F + 1) d
        ((Expr.const n us).instantiateLevelParams ks vs)
      = .ok (t.instantiateLevelParams ks vs) := by
  obtain ⟨ci, hf, hlen, rfl⟩ := infer_const_inv h
  have hdef := (henv _ (Setlec.find?_mem hf)).2.1
  rw [Expr.instantiateLevelParams,
    infer_const_run F d n _ ci hf (by simpa using hlen)]
  exact congrArg Except.ok
    (instLevels_comp_of_defined ks vs _ us hlen.symm _ hdef).symm

/-! ## Part 3 — the general `whnf` form, and the shape that survives

`Step2/Levels.lean` stated primitive 2 narrowly, at runs landing on a
`.sort`, and recorded the *general* equality-of-reducts form as
**expect false** without a witness.  Both shapes are named here so the
question stops being an aside in a docstring. -/

/-- The **general** shape primitive 2 deliberately avoided: `whnf`
commutes with level instantiation *as an equality on reducts*. -/
def WhnfInstLevels (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ks : List Name) (us : List Level) (F d : Nat) (t w : Expr),
    whnf μ env F d t = .ok w →
    ∃ F', F ≤ F' ∧
      whnf μ env F' d (t.instantiateLevelParams ks us)
        = .ok (w.instantiateLevelParams ks us)

/-- The narrow form is a corollary of the general one — recorded so the
refutation below transfers in the right direction. -/
theorem whnfSortInstLevels_of_general (h : WhnfInstLevels μ env) :
    WhnfSortInstLevels μ env :=
  fun ks us F d t ℓ hw => h ks us F d t (.sort ℓ) hw

/-- **The general form is false**, by the escape witness of Part 1:
`WhnfSortInstLevels` is one of its instances. -/
theorem not_whnfInstLevels (μ : CheckMode) :
    WhnfInstLevels μ escEnvV → False :=
  fun h => not_whnfSortInstLevels μ (whnfSortInstLevels_of_general h)

/-- **The shape a discharge should aim at**: not an equality of
reducts but a *simulation* — the instantiated subject and the
substituted reduct have a **common** head normal form.  This is the
form the one-directional divergence of the level-sensitive guards
permits: the instantiated run may reduce further than the image of the
uninstantiated one, and this shape lets it.

It inherits Part 1's `EnvWF` requirement — it implies
`WhnfSortInstLevels`, which the escape refutes — so a discharge takes
it under `EnvWF` like the `…W` forms. -/
def WhnfInstLevelsUpTo (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ks : List Name) (us : List Level) (F d : Nat) (t w : Expr),
    whnf μ env F d t = .ok w →
    ∃ F' r, F ≤ F' ∧
      whnf μ env F' d (t.instantiateLevelParams ks us) = .ok r ∧
      whnf μ env F' d (w.instantiateLevelParams ks us) = .ok r

/-- **The sort-terminality argument, mechanized.**  At a reduct that is
a `.sort` the simulation form *collapses* to the narrow one, because a
sort is its own head normal form — so the extra reduction the
simulation allows has, exactly as `Step2/Levels.lean` argued, nowhere
to go.  This is why primitive 2 was right to be stated narrowly: it is
the fragment of the general claim that the divergence cannot reach. -/
theorem whnfSortInstLevels_of_upTo (h : WhnfInstLevelsUpTo μ env) :
    WhnfSortInstLevels μ env := by
  intro ks us F d t ℓ hw
  obtain ⟨F', r, hle, h1, h2⟩ := h ks us F d t (.sort ℓ) hw
  have hs : whnf μ env (F' + 2) d (.sort (Level.subst ks us ℓ))
      = .ok (.sort (Level.subst ks us ℓ)) :=
    Setlec.whnf_sort (mode := μ) env F' d _
  have h2' := (knotFuelMono μ env).2.1 (Nat.le_add_right F' 2) h2
  rw [show (Expr.sort ℓ).instantiateLevelParams ks us
    = .sort (Level.subst ks us ℓ) from rfl, hs] at h2'
  obtain rfl : r = .sort (Level.subst ks us ℓ) :=
    (Except.ok.inj h2').symm
  exact ⟨F' + 2, by omega,
    (knotFuelMono μ env).2.1 (Nat.le_add_right F' 2) h1⟩

/-! ### A second level-sensitive guard, in the seam, needing no install

Seal 19's suspect list had two entries, both in `iotaRec`'s stuck-major
rescue, and concluded that one of them is inert and the other flips
only in the safe direction.  The list was **incomplete**.
`whnfCore`'s **beta certificate** — `whnfCore (.app f a)` reduces the
redex only if `defeq (infer a) ty` — is level-sensitive through
`Level.isEquiv` at the `.sort`/`.sort` leaf of `defeqStep`, and the
flip needs *no environment at all*: `Prop` is not definitionally
`Sort p`, and is definitionally `Sort p` at `p := 0`.

So the redex `(fun _ : Sort p => Prop) (x : Prop)` is **stuck** at the
parameter and **beta-reduces** at the instance.  Evaluating both runs
(`whnf .setModel Env.empty 20 1`) confirms the stuck reduct and the
reduct `Prop`; mechanizing the two runs is a separate matter and is
**not** done here — `Level.isEquiv` does not reduce definitionally
under the literal `Level.defaultFuel` (`decide` gets stuck, exactly as
`Step2/Levels.lean`'s `leq_param_zero` records), so a run-level proof
must thread three hand-proved `isEquiv` values through `proofIrrel`'s
two nested `infer`/`whnf` calls and three `@[irreducible]` loop-fuel
peels.  What *is* mechanized is the guard, which is where the finding
lives; the run-level statement stays open and is not claimed. -/

theorem leq_zero_param (p : Name) :
    Level.leq .zero (.param p) = some true := by
  rw [Level.leq]
  show Level.leqCore (9999 + 1) (Level.simplify .zero)
    (Level.simplify (.param p)) 0 = some true
  simp [Level.simplify, Level.leqCore]

theorem leq_param_zero (p : Name) :
    Level.leq (.param p) .zero = some false := by
  rw [Level.leq]
  show Level.leqCore (9999 + 1) (Level.simplify (.param p))
    (Level.simplify .zero) 0 = some false
  simp [Level.simplify, Level.leqCore, Level.rest]

/-- `Prop` is not definitionally `Sort p` — the `.sort`/`.sort` leaf of
`defeqStep`, at a level parameter. -/
theorem isEquiv_zero_param (p : Name) :
    Level.isEquiv .zero (.param p) = some false := by
  simp [Level.isEquiv, Level.simplify, leq_zero_param p,
    leq_param_zero p]

/-- **The beta certificate's level guard flips**, one-directionally and
with no environment — `piResultNeverZero_flips`' analogue at a guard
seal 19's list did not carry.  `Level.isEquiv 0 p` is `false` at the
parameter and `true` at `p := 0`, so `whnfCore` leaves the redex
`(fun _ : Sort p => Prop) (x : Prop)` stuck and reduces it after
instantiation. -/
theorem betaCertLevel_flips (p : Name) :
    Level.isEquiv .zero (.param p) = some false ∧
    Level.isEquiv .zero (Level.subst [p] [.zero] (.param p))
      = some true := by
  refine ⟨isEquiv_zero_param p, ?_⟩
  simp [Level.subst, Level.subst.go, Level.isEquiv, Level.simplify]

end Setlec.SetR.Interp2
