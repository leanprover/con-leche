import Setlec.SetR.Interp2.Step2.Dispatch

/-!
# `denote2` across a spine, a depth, and a level substitution

The three algebraic facts the **delta exit** of the reduction loop
needs, plus the one that is not algebraic at all.

`unfoldDefinition` (`Setlec/Kernel/Core.lean`) rewrites
`mkAppN (.const n us) args` to
`mkAppN (value.instantiateLevelParams cv.levelParams us) args`, so a
consumer of `EnvS2.acval_defn` has three gaps to cross:

* the head sits under a spine — `denote2_mkAppN_swap`;
* the field speaks at depth `0`, the loop runs at depth `d` —
  `denote2_depth_of_closed`;
* the field speaks about `value`, the reduct is
  `value.instantiateLevelParams …` — **`Denote2InstLevels`, a
  residue and not a theorem**.

The first two are structural and are proved here.  The third is
**not**, and that is this file's finding.

## Second visit: the verdict on `Denote2InstLevels`

Seal 15 put the crossing at the head of the queue, because
`RecRulesV2` takes a recursor's RHS at `instantiateLevelParams` and
would be **the wrong statement** if the crossing were false.  Neither
a proof nor a refutation is delivered here.  What is delivered:

1. **The suspect guards, chased.**  `piResultIsProp` is *not* in the
   seam — both call sites apply it to a stored inductive's own type at
   install, which a subject's instantiation cannot reach.
   `piResultNeverZero` *is*, and it *does* flip
   (`piResultNeverZero_flips`) — but only from `false` to `true`
   (`piResultNeverZero_map_subst`).  Instantiation can make the
   structure-eta rescue fire where it did not; it can never lose one.
2. **The crossing, factored to the checker.**
   `denote2_instLevels_of` proves `Denote2InstLevels` from
   `SortOfEInstLevels` and `LamSortEInstLevels`, and those from
   `InferInstLevels` and `WhnfSortInstLevels` — two statements about
   `inferTypeCore`/`whnf` alone, with no `denote2`, no `V`, no `EnvS2`
   and no valuation in them.  Everything else in the crossing is
   algebra, and it is discharged.
3. **A refutation is now possible at all.**  `Denote2InstLevels`
   quantifies over an `EnvS2 V env`; the only one the tree exhibits is
   `EnvS2.empty`, so no counterexample could be built against it until
   the install tier lands.  The two primitives quantify over a bare
   `Env`, so they can be refuted by a hand-built environment today.
4. **The shape of primitive 2 is a finding, not a convenience.**  The
   general "`whnf` commutes with instantiation, as an equality on
   reducts" is *expected to be false* — the rescue flip is exactly a
   reason for the instantiated run to reduce further.  No witness is
   claimed (the flip is a guard-level fact, not yet a `whnf`-level
   one).  The sort-restricted form is not reached by the flip at all,
   because a `.sort` is terminal for `whnf`; that is why primitive 2
   is stated narrowly.

**Where the argument stalls**, honestly.  Every level-sensitive guard
in the checker points the same way — `Level.isEquiv` closes more
equalities at an instance, `isPropType` sees more `Prop`s, both
rescues fire more — i.e. instantiation makes runs *succeed more*,
which is the direction `Denote2InstLevels` needs.  That is evidence,
not a proof: the primitives are statements about a mutually recursive
knot (`whnf`/`infer`/`defeq`) and proving them needs the knot's own
simultaneous induction, the level-side twin of `shiftClaims`.  Nobody
should read the monotonicity result as settling the question; it
settles the *specific* attack seal 12 named, and nothing more.

## Why the level crossing is not a structural induction

On the v1 lane the same crossing is `denote_instLevels`
(`Setlec/Verify/Denote/Levels.lean`), an unconditional equality proved
by one induction over `denote`: `denote` reads the level assignment
only at `.sort` (through `Level.eval`) and at `.const` (through
`Level.substFn`), and `Level.eval_subst` / `Level.substFn_map_subst`
settle both clauses.

`denote2` reads it at those two clauses **and** through
`sortOfE`/`lamSortE`, which are `inferTypeCore` and `whnf` *runs*
(`Annot/Canon.lean`).  At a `.forallE`/`.lam` node the two sides of the
crossing therefore compare

```
sortOfE μ env φ F d (ty.instantiateLevelParams ks us)
sortOfE μ env (Level.substFn φ ks us) F d ty
```

— two runs of the checker on **different terms**.  Relating them is a
statement about the checker, not about `denote2`: *inference and
head normalisation commute with level instantiation.*  Nothing of that
kind is in the tree; the depth-shift analogue (`shiftClaims`,
`Setlec/Verify/Deep.lean`, which is what makes `denote2_shiftFrom`
cheap) was landed for the memo cache and has no level-side twin.

Note also that the equality form is the wrong shape even if the
metatheorem is proved: instantiation can make a run **succeed that did
not** (level equalities that are open at a parameter close at an
instance), so the honest statement is the implication in the direction
the delta exit consumes, with the `∃ F' ≥ F` slack `Claims2B` already
uses everywhere.

## The smallest-fuel test, applied before stating

`Denote2InstLevels` asserts a `denote2` success as a **conclusion** —
the shape STOP 2 refuted three times.  It survives the test because the
fuel is existential (`∃ F', F ≤ F' ∧ …`) and the subject's success is a
hypothesis: at `F = 1` the hypothesis forces the subject binder-free
and the conclusion holds at the same fuel.  It is stated over an
`EnvS2` rather than a bare `acval` because its `.const` clause needs
`acval_params` — over an arbitrary valuation the two sides read the
same constant at two assignments that agree only on that constant's
own parameters, and the statement would be false.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## The spine

`denote2`'s `.app` clause is structural, so replacing a spine's head by
a term with the *same* annotation replaces nothing else.  The fuel is
allowed to move up in the same step: the arguments ride along on
`denote2_fuelMono`, which returns the same `AVExpr`. -/

/-- **Head swap under a spine.**  If the head's annotation survives a
move to `F' ≥ F` — for whatever reason: the same term, an unfolding, a
different term with the same canonical annotation — then so does the
whole application's, unchanged. -/
theorem denote2_mkAppN_swap {d : Nat} :
    ∀ (as : List Expr) {f g : Expr} {F F' : Nat} {ea : AVExpr},
      F ≤ F' →
      (∀ fa : AVExpr, denote2 μ acval env φ F d f = some fa →
        denote2 μ acval env φ F' d g = some fa) →
      denote2 μ acval env φ F d (Expr.mkAppN f as) = some ea →
      denote2 μ acval env φ F' d (Expr.mkAppN g as) = some ea := by
  intro as
  induction as with
  | nil => intro f g F F' ea _ hswap h; exact hswap ea h
  | cons a as ih =>
    intro f g F F' ea hle hswap h
    refine ih (f := .app f a) (g := .app g a) hle ?_ h
    intro fa hfa
    rw [denote2] at hfa
    rcases hf : denote2 μ acval env φ F d f with _ | fx
    · rw [hf] at hfa; exact nomatch hfa
    rw [hf] at hfa
    rcases ha : denote2 μ acval env φ F d a with _ | ax
    · rw [ha] at hfa; exact nomatch hfa
    rw [ha] at hfa
    obtain rfl : fa = .app fx ax := (Option.some.inj hfa).symm
    rw [denote2, hswap fx hf, denote2_fuelMono hle d a ha]
    rfl

/-! ## The depth

`EnvS2.acval_defn` speaks at depth `0`; the reduction loop runs at the
subject's depth.  For a term with no `fvar` leaves the shift is the
identity on the *expression* (`shiftFrom_eq_self_of_not_hasFvar`) and
`denote2_shiftFrom` then moves the annotation by a `liftN`, which
`EnvS2.acval_closed` undoes.  So a closed stored value annotates the
same at every depth — the transpose of v1's `denote_lift` step inside
`delta_coreR`. -/

/-- **A closed term's canonical annotation does not depend on the
depth**, provided the annotation itself is lift-invariant (which
`EnvS2.acval_closed` supplies for every valuation leaf). -/
theorem denote2_depth_of_closed (henv : Setlec.EnvWF env)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {F : Nat} {e : Expr} {ea : AVExpr} (hfv : e.hasFvar = false)
    (hcl : ∀ k : Nat, ea.liftN 1 k = ea)
    (h : denote2 μ acval env φ F 0 e = some ea) :
    ∀ d : Nat, denote2 μ acval env φ F d e = some ea := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih =>
    have hs := denote2_shiftFrom (μ := μ) (acval := acval) (φ := φ)
      (f := F) (p := 0) henv hacl e d (Nat.zero_le d)
      (Expr.WScoped.of_not_hasFvar hfv)
    rw [Expr.shiftFrom_eq_self_of_not_hasFvar hfv, ih] at hs
    rw [hs]
    simp [hcl]

/-! ## The level substitution — the residue -/

/-- **The level-instantiation crossing for `denote2`** — v1's
`denote_instLevels` in the annotated currency, and *not* provable the
same way (see the module docstring): its binder clauses need
`inferTypeCore`/`whnf` to commute with level instantiation, which is a
metatheorem about the checker with no counterpart in the tree.

Stated as the implication the delta exit consumes rather than as v1's
equality, because instantiation can make a run succeed that did not,
and with `Claims2B`'s own `∃ F' ≥ F` slack, because the instantiated
term's sort computations are not the ones the hypothesis paid for. -/
def Denote2InstLevels (μ : CheckMode) {env : Env} (m : EnvS2 V env) :
    Prop :=
  ∀ (φ : Name → Nat) (ks : List Name) (us : List Level) (F d : Nat)
    (e : Expr) (ea : AVExpr),
    denote2 μ m.acval env (Level.substFn φ ks us) F d e = some ea →
    ∃ F', F ≤ F' ∧
      denote2 μ m.acval env φ F' d (e.instantiateLevelParams ks us)
        = some ea

/-! ## The level-sensitive guard, chased first

Seal 12 named `piResultIsProp`/`piResultNeverZero`
(`Setlec/Kernel/Core.lean`) as the reason to doubt the crossing: they
make the structure-eta rescue and the K rescue level-sensitive, so a
run genuinely *can* take a different branch under instantiation.
Chased here, and the two names come apart.

**`piResultIsProp` is not in the seam at all.**  It occurs at exactly
two call sites (`Kernel/Modeled.lean`, `Kernel/CheckerS.lean`), both
of the form `ruleK := nF == 0 && piResultIsProp cvT.type` — at
*install*, on a stored inductive's *own* type.  A subject term's level
instantiation does not touch a stored type, so the `ruleK` capability
a run reads off `env` is the same on both sides of the crossing.  As a
function `piResultIsProp` is of course level-sensitive
(`piResultIsProp_flips`), which is presumably how it got onto the
list; it is the call sites that make it inert.

**`piResultNeverZero` is in the seam, it does flip, and the flip is
one-directional.**  `majorToCtor` reads it as
`piResultNeverZero cvT.levelParams ust cvT.type` where `ust` comes off
`whnf (infer major)` — *those* levels are the subject's, and
instantiation maps `Level.subst ks us` over them.
`piResultNeverZero_flips` exhibits a `false` that becomes `true`;
`piResultNeverZero_map_subst` proves the converse cannot happen.  So
instantiation can only make the rescue **fire where it did not**; it
can never lose a rescue the uninstantiated run had.

That is the shape of the whole crossing in miniature, and it is why
this file does **not** deliver a refutation: every level-sensitive
guard in the checker points the same way (`Level.isEquiv` closes more
equalities at an instance, `isPropType` sees more `Prop`s, the two
rescues fire more), i.e. instantiation makes runs *succeed more* —
which is the direction `Denote2InstLevels`' hypothesis/conclusion
split already has.  See the closing note for what that does and does
not settle. -/

/-- **A nonzero certificate survives every level substitution.**
`Level.isNeverZero` is the official `is_never_zero`: syntactic and
incomplete, with `zero` and `param` its only `false` leaves — and a
substitution creates neither. -/
theorem isNeverZero_subst (ks : List Name) (vs : List Level) :
    ∀ l : Level, l.isNeverZero = true →
      (Level.subst ks vs l).isNeverZero = true := by
  intro l
  induction l with
  | zero => intro h; simp [Level.isNeverZero] at h
  | param n => intro h; simp [Level.isNeverZero] at h
  | succ l _ => intro _; simp [Level.subst, Level.isNeverZero]
  | max a b iha ihb =>
    intro h
    simp only [Level.subst, Level.isNeverZero, Bool.or_eq_true] at h ⊢
    exact h.imp iha ihb
  | imax a b _ ihb =>
    intro h
    simp only [Level.subst, Level.isNeverZero] at h ⊢
    exact ihb h

private theorem isNeverZero_go_map (ks : List Name) (vs : List Level) :
    ∀ (ps : List Name) (ws : List Level) (n : Name),
      (Level.subst.go ps ws n).isNeverZero = true →
      (Level.subst.go ps (ws.map (Level.subst ks vs)) n).isNeverZero
        = true := by
  intro ps
  induction ps with
  | nil =>
    intro ws n h
    simp [Level.subst.go, Level.isNeverZero] at h
  | cons p ps ih =>
    intro ws n h
    cases ws with
    | nil => simp [Level.subst.go, Level.isNeverZero] at h
    | cons w ws =>
      simp only [List.map, Level.subst.go] at h ⊢
      by_cases he : p = n
      · rw [if_pos he] at h ⊢
        exact isNeverZero_subst ks vs w h
      · rw [if_neg he] at h ⊢
        exact ih ws n h

/-- The mapped form: a nonzero certificate for `subst ps ws l`
survives mapping a further substitution over the `ws`. -/
theorem isNeverZero_subst_map (ks : List Name) (vs : List Level)
    (ps : List Name) (ws : List Level) :
    ∀ l : Level, (Level.subst ps ws l).isNeverZero = true →
      (Level.subst ps (ws.map (Level.subst ks vs)) l).isNeverZero
        = true := by
  intro l
  induction l with
  | zero => intro h; simp [Level.subst, Level.isNeverZero] at h
  | param n => exact isNeverZero_go_map ks vs ps ws n
  | succ l _ => intro _; simp [Level.subst, Level.isNeverZero]
  | max a b iha ihb =>
    intro h
    simp only [Level.subst, Level.isNeverZero, Bool.or_eq_true] at h ⊢
    exact h.imp iha ihb
  | imax a b _ ihb =>
    intro h
    simp only [Level.subst, Level.isNeverZero] at h ⊢
    exact ihb h

/-- **The eta/K rescue guard is monotone under instantiation of the
subject's levels.**  `piResultNeverZero lps ust ty = true` survives
mapping `Level.subst ks us` over `ust`, which is exactly what
`Expr.instantiateLevelParams` does to the levels `majorToCtor` reads
off the major's inferred type.  The named key fact seal 12 asked
for. -/
theorem piResultNeverZero_map_subst {ks : List Name} {vs : List Level}
    (lps : List Name) (ust : List Level) (ty : Expr)
    (h : Setlec.piResultNeverZero lps ust ty = true) :
    Setlec.piResultNeverZero lps (ust.map (Level.subst ks vs)) ty
      = true := by
  unfold Setlec.piResultNeverZero at h ⊢
  split at h
  · exact isNeverZero_subst_map ks vs lps ust _ h
  · simp at h

/-- The names the two flip witnesses use. -/
private def flipU : Name := .str .anonymous "u"
private def flipV : Name := .str .anonymous "v"

/-- **The flip is real, in one direction.**  `Sort u` at a level
*parameter* is not provably nonzero; the same guard at the same stored
type, with the parameter instantiated to `1`, is.  So a run really can
take the structure-eta branch on the instantiated term and not on the
uninstantiated one — which is what seal 12 suspected, and what
`piResultNeverZero_map_subst` bounds. -/
theorem piResultNeverZero_flips :
    Setlec.piResultNeverZero [flipU] [.param flipV]
        (.sort (.param flipU)) = false ∧
    Setlec.piResultNeverZero [flipU]
        ([Level.param flipV].map (Level.subst [flipV] [.succ .zero]))
        (.sort (.param flipU)) = true := by
  constructor <;> decide

/-- `Level.leq` at a parameter against `zero`, by hand: `decide`
cannot run `leqCore`'s mutual recursion under the literal fuel, so the
fuel is exposed as `9999 + 1` (`Level.defaultFuel = 10000`) and the
one step is taken with `simp`. -/
private theorem leq_param_zero :
    Level.leq (Level.param flipU) .zero = some false := by
  rw [Level.leq]
  show Level.leqCore (9999 + 1) (Level.simplify (.param flipU))
    (Level.simplify .zero) 0 = some false
  simp [Level.simplify, Level.leqCore, Level.rest]

/-- `piResultIsProp` is level-sensitive as a *function* — recorded so
the finding above is not read as "the guard is level-insensitive".
What makes it inert is that both call sites apply it to a *stored*
inductive's type, which a subject's instantiation does not reach. -/
theorem piResultIsProp_flips :
    Setlec.piResultIsProp (.sort (.param flipU)) = false ∧
    Setlec.piResultIsProp
        ((Expr.sort (.param flipU)).instantiateLevelParams
          [flipU] [.zero]) = true := by
  refine ⟨?_, by decide⟩
  simp [Setlec.piResultIsProp, Expr.piResult, Level.isEquiv,
    Level.simplify, leq_param_zero]

/-! ## The crossing, factored

The residue is now stated where it lives.  Note that **neither
`inferTypeCore` nor `whnf` takes a level assignment**: `sortOfE`'s only
use of `φ` is the final `Level.eval`, and `lamSortE` is an inference
followed by a `sortOfE`.  So the two `Prop`s below are precisely the
metatheorem *inference and head normalisation commute with level
instantiation*, packaged at the granularity `denote2` consumes it —
with no `denote2`, no `V`, no `EnvS2` and no valuation in them.

That last point is the practically important one.  `Denote2InstLevels`
quantifies over an `EnvS2 V env`, and the only `EnvS2` the tree can
exhibit today is `EnvS2.empty`; a counterexample needs a rich
environment, so the statement **cannot be refuted at all** until the
install tier lands.  `SortOfEInstLevels` has no such guard: it is a
statement about a bare `Env` and the checker, so it can be attacked —
or refuted with a hand-built environment — right now.  Factoring is
therefore not bookkeeping; it is what makes the question decidable by
anyone. -/

/-- **The `sortOfE` half of the level crossing** — the checker-side
residue, in the direction and with the fuel slack the delta exit
consumes. -/
def SortOfEInstLevels (μ : CheckMode) (env : Env) : Prop :=
  ∀ (φ : Name → Nat) (ks : List Name) (us : List Level)
    (F d : Nat) (e : Expr) (u : Nat),
    sortOfE μ env (Level.substFn φ ks us) F d e = some u →
    ∃ F', F ≤ F' ∧
      sortOfE μ env φ F' d (e.instantiateLevelParams ks us) = some u

/-- **The `lamSortE` half** — the λ clause's codomain sort.  Separate
from `SortOfEInstLevels` because `lamSortE` runs one more inference
*before* the `sortOfE`, on a term the crossing must move as well. -/
def LamSortEInstLevels (μ : CheckMode) (env : Env) : Prop :=
  ∀ (φ : Name → Nat) (ks : List Name) (us : List Level)
    (F d : Nat) (e : Expr) (u : Nat),
    lamSortE μ env (Level.substFn φ ks us) F d e = some u →
    ∃ F', F ≤ F' ∧
      lamSortE μ env φ F' d (e.instantiateLevelParams ks us) = some u

/-! ### Down to the checker's two primitives

`sortOfE` and `lamSortE` are `inferTypeCore` and `whnf` read through
`Except.toOption`, so the residue factors once more — and the *shape*
of the second primitive is where the `piResultNeverZero` finding pays
for itself.

The obvious second primitive would be "`whnf` commutes with level
instantiation", as an equality on reducts.  **That statement should
not be assumed, and `piResultNeverZero_flips` is why**: at an instance
the structure-eta rescue fires where it did not, so the instantiated
run's reduct can be strictly further reduced than the image of the
uninstantiated one.  That is a reason to expect the equality form to
be false, not a witness that it is — the flip is proved at the guard,
not at a `whnf` run — but it is reason enough not to build on it.
`WhnfSortInstLevels` restricts the claim to runs that land on a
`.sort`, and a `.sort` is terminal for `whnf`, so the extra reduction
has nowhere to go.  *The monotone direction of the flip is what makes
the restricted form immune to the objection that recommends against
the general one.*

The other obvious refutation of the `inferTypeCore` primitive — a
binder carrying a **stale sort annotation**, since
`Expr.instantiateLevelParams` copies a `BinderMeta` through unchanged
— is closed by design and not by luck: task #100 erased the codomain
sort from `BinderMeta`, which now carries a `BinderInfo` and nothing
else (`Setlec/Kernel/Expr.lean`).  There is no level inside an `Expr`
that instantiation fails to reach. -/

/-- **Primitive 1: inference commutes with level instantiation.**  The
implication direction, with the campaign's fuel slack; the conclusion
names the *substituted* inferred type, which is the strong form. -/
def InferInstLevels (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ks : List Name) (us : List Level) (F d : Nat) (e t : Expr),
    inferTypeCore μ env F d e = .ok t →
    ∃ F', F ≤ F' ∧
      inferTypeCore μ env F' d (e.instantiateLevelParams ks us)
        = .ok (t.instantiateLevelParams ks us)

/-- **Primitive 2: head normalisation commutes with level
instantiation *at a sort*.**  Deliberately not stated for arbitrary
reducts — see the section note; the rescue flip is a reason to expect
the general form to fail, and does not reach this one. -/
def WhnfSortInstLevels (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ks : List Name) (us : List Level) (F d : Nat) (t : Expr)
    (ℓ : Level),
    whnf μ env F d t = .ok (.sort ℓ) →
    ∃ F', F ≤ F' ∧
      whnf μ env F' d (t.instantiateLevelParams ks us)
        = .ok (.sort (Level.subst ks us ℓ))

/-- The `sortOfE` residue is the two primitives composed: infer, whnf
to a sort, and `Level.eval_subst` to move the numeral. -/
theorem sortOfEInstLevels_of (hi : InferInstLevels μ env)
    (hw : WhnfSortInstLevels μ env) : SortOfEInstLevels μ env := by
  intro φ ks us F d e u h
  unfold sortOfE at h
  cases hit : inferTypeCore μ env F d e with
  | error err => rw [hit] at h; exact nomatch h
  | ok t =>
    rw [hit] at h
    simp only [Except.toOption] at h
    cases hwt : whnf μ env F d t with
    | error err => rw [hwt] at h; exact nomatch h
    | ok w =>
      rw [hwt] at h
      cases w with
      | sort ℓ =>
        obtain rfl : ℓ.eval (Level.substFn φ ks us) = u :=
          Option.some.inj h
        obtain ⟨F₁, hle₁, k₁⟩ := hi ks us F d e t hit
        obtain ⟨F₂, hle₂, k₂⟩ := hw ks us F d t ℓ hwt
        refine ⟨max F₁ F₂, by omega, ?_⟩
        unfold sortOfE
        rw [(knotFuelMono μ env).1 (Nat.le_max_left F₁ F₂) k₁]
        simp only [Except.toOption]
        rw [(knotFuelMono μ env).2.1 (Nat.le_max_right F₁ F₂) k₂]
        exact congrArg some (Level.eval_subst φ ks us ℓ)
      | _ => exact nomatch h

/-- The `lamSortE` residue is primitive 1 followed by the `sortOfE`
residue — one extra inference, on the term whose sort is wanted. -/
theorem lamSortEInstLevels_of (hi : InferInstLevels μ env)
    (hsz : SortOfEInstLevels μ env) : LamSortEInstLevels μ env := by
  intro φ ks us F d e u h
  unfold lamSortE at h
  cases hit : inferTypeCore μ env F d e with
  | error err => rw [hit] at h; exact nomatch h
  | ok bt =>
    rw [hit] at h
    simp only [Except.toOption] at h
    obtain ⟨F₁, hle₁, k₁⟩ := hi ks us F d e bt hit
    obtain ⟨F₂, hle₂, k₂⟩ := hsz φ ks us F d bt u h
    refine ⟨max F₁ F₂, by omega, ?_⟩
    unfold lamSortE
    rw [(knotFuelMono μ env).1 (Nat.le_max_left F₁ F₂) k₁]
    simp only [Except.toOption]
    exact sortOfE_fuelMono (Nat.le_max_right F₁ F₂) k₂

/-! ### The valuation-leaf side

Four clauses of `denote2` read `acval` at an assignment, and on the
two sides of the crossing those assignments differ off the constant's
own parameters.  `EnvS2.acval_params` is what closes them — v1's
`ValParams` argument (`Verify/Denote/Levels.lean`) transposed to the
annotated valuation. -/

/-- A stored slot with no level parameters is valued independently of
the assignment. -/
private theorem acval_isEmpty (m : EnvS2 V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (he : ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval n ψ₁ = m.acval n ψ₂ := by
  refine m.acval_params n ci hf ψ₁ ψ₂ fun p hpm => ?_
  rw [List.isEmpty_iff] at he
  rw [he] at hpm
  exact nomatch hpm

/-- A one-parameter slot substituted at `Level.zero` is valued
independently of the assignment: the substitution overrides the only
parameter the valuation may read. -/
private theorem acval_oneParam (m : EnvS2 V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlen : ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval n (Level.substFn ψ₁ ci.toConstantVal.levelParams [.zero])
      = m.acval n
        (Level.substFn ψ₂ ci.toConstantVal.levelParams [.zero]) := by
  refine m.acval_params n ci hf _ _ ?_
  intro p hpm
  refine Level.substFn_ext (ps := []) (fun q hq => nomatch hq) ?_ ?_ p
    hpm
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    rfl
  · simp [hlen]

/-- The scalar literal-support slots, read off their shape guards. -/
private theorem acval_scalar (m : EnvS2 V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval nm ψ₁ = m.acval nm ψ₂ := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    rw [hx] at hfok
    exact acval_isEmpty m hx (hshape ci hfok) _ _

/-- The two one-parameter literal-support slots. -/
private theorem acval_one (m : EnvS2 V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval nm (Level.substFn ψ₁ (levelParamsAt env nm) [.zero])
      = m.acval nm
        (Level.substFn ψ₂ (levelParamsAt env nm) [.zero]) := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    have hlp : levelParamsAt env nm = ci.toConstantVal.levelParams := by
      simp [levelParamsAt, hx]
    rw [hx] at hfok
    rw [hlp]
    exact acval_oneParam m hx (hshape ci hfok) _ _

/-- The `Nat`-literal leaves are assignment-independent. -/
private theorem acval_natPair (m : EnvS2 V env)
    (hg : Setlec.natLitSupported env = true) (ψ₁ ψ₂ : Name → Nat) :
    m.acval natZeroName ψ₁ = m.acval natZeroName ψ₂ ∧
      m.acval natSuccName ψ₁ = m.acval natSuccName ψ₂ := by
  simp only [Setlec.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, hz⟩, hs⟩ := hg
  refine ⟨acval_scalar m natZeroName natZeroOk hz rfl ?_ _ _,
    acval_scalar m natSuccName natSuccOk hs rfl ?_ _ _⟩
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natZeroOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natZeroOk] at h
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natSuccOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natSuccOk] at h

/-! ### The crossing, given the checker residue -/

/-- **The level crossing for `denote2`, factored.**  Given that the
checker's two sort computations commute with level instantiation, the
rest of `Denote2InstLevels` *is* v1's one induction — clause for
clause `denote_instLevels`, with `EnvS2.acval_params` where v1 has
`ValParams` and the fuel maxima where v1 has nothing to pay.

This is the file's main deliverable: the crossing is not partly
algebraic and partly a metatheorem, it is **entirely** the metatheorem
about `sortOfE`/`lamSortE` plus algebra that is now discharged. -/
theorem denote2_instLevels_of (m : EnvS2 V env)
    (hs : SortOfEInstLevels μ env) (hl : LamSortEInstLevels μ env) :
    Denote2InstLevels μ m := by
  intro φ ks us F d e
  induction d, e using denote2.induct (env := env) with
  | case1 d u =>
    intro ea h
    rw [denote2] at h
    obtain rfl := Option.some.inj h
    refine ⟨F, Nat.le_refl F, ?_⟩
    rw [Expr.instantiateLevelParams, denote2, Level.eval_subst]
  | case2 d idx nm ty =>
    intro ea h
    rw [denote2] at h
    obtain rfl := Option.some.inj h
    refine ⟨F, Nat.le_refl F, ?_⟩
    rw [Expr.instantiateLevelParams, denote2]
  | case3 d n vs ci hf hlen =>
    intro ea h
    rw [denote2, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    refine ⟨F, Nat.le_refl F, ?_⟩
    rw [Expr.instantiateLevelParams, denote2, hf]
    dsimp only
    rw [if_pos (by simpa using hlen)]
    exact congrArg some
      (m.acval_params n ci hf _ _ fun p hp =>
        Level.substFn_map_subst hlen hp)
  | case4 d n vs ci hf hlen =>
    intro ea h
    rw [denote2, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n vs hf =>
    intro ea h
    rw [denote2, hf] at h
    exact nomatch h
  | case6 d n ty body mb ihty ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 μ m.acval env (Level.substFn φ ks us) F d ty
      with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denote2 μ m.acval env (Level.substFn φ ks us) F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hu : sortOfE μ env (Level.substFn φ ks us) F d ty with _ | u
    · rw [hu] at h; exact nomatch h
    rw [hu] at h
    rcases hv : sortOfE μ env (Level.substFn φ ks us) F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    obtain ⟨F₁, hle₁, k₁⟩ := ihty ta hta
    obtain ⟨F₂, hle₂, k₂⟩ := ihbody ba hba
    obtain ⟨F₃, hle₃, k₃⟩ := hs φ ks us F d ty u hu
    obtain ⟨F₄, hle₄, k₄⟩ := hs φ ks us F (d + 1) _ v hv
    rw [Expr.instantiateLevelParams_instantiate1 ks us body 0] at k₂ k₄
    have g₁ : F₁ ≤ max (max F₁ F₂) (max F₃ F₄) := by omega
    have g₂ : F₂ ≤ max (max F₁ F₂) (max F₃ F₄) := by omega
    have g₃ : F₃ ≤ max (max F₁ F₂) (max F₃ F₄) := by omega
    have g₄ : F₄ ≤ max (max F₁ F₂) (max F₃ F₄) := by omega
    refine ⟨max (max F₁ F₂) (max F₃ F₄), by omega, ?_⟩
    rw [Expr.instantiateLevelParams, denote2,
      denote2_fuelMono g₁ d _ k₁, denote2_fuelMono g₂ (d + 1) _ k₂,
      sortOfE_fuelMono g₃ k₃, sortOfE_fuelMono g₄ k₄]
    exact h
  | case7 d n ty body mb ihty ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 μ m.acval env (Level.substFn φ ks us) F d ty
      with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denote2 μ m.acval env (Level.substFn φ ks us) F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hv : lamSortE μ env (Level.substFn φ ks us) F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    obtain ⟨F₁, hle₁, k₁⟩ := ihty ta hta
    obtain ⟨F₂, hle₂, k₂⟩ := ihbody ba hba
    obtain ⟨F₃, hle₃, k₃⟩ := hl φ ks us F (d + 1) _ v hv
    rw [Expr.instantiateLevelParams_instantiate1 ks us body 0] at k₂ k₃
    have g₁ : F₁ ≤ max (max F₁ F₂) F₃ := by omega
    have g₂ : F₂ ≤ max (max F₁ F₂) F₃ := by omega
    have g₃ : F₃ ≤ max (max F₁ F₂) F₃ := by omega
    refine ⟨max (max F₁ F₂) F₃, by omega, ?_⟩
    rw [Expr.instantiateLevelParams, denote2,
      denote2_fuelMono g₁ d _ k₁, denote2_fuelMono g₂ (d + 1) _ k₂,
      lamSortE_fuelMono g₃ k₃]
    exact h
  | case8 d fe a ihf iha =>
    intro ea h
    rw [denote2] at h
    rcases hfa : denote2 μ m.acval env (Level.substFn φ ks us) F d fe
      with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denote2 μ m.acval env (Level.substFn φ ks us) F d a
      with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    obtain ⟨F₁, hle₁, k₁⟩ := ihf fa hfa
    obtain ⟨F₂, hle₂, k₂⟩ := iha aa haa
    refine ⟨max F₁ F₂, Nat.le_trans hle₁ (Nat.le_max_left F₁ F₂), ?_⟩
    rw [Expr.instantiateLevelParams, denote2,
      denote2_fuelMono (Nat.le_max_left F₁ F₂) d _ k₁,
      denote2_fuelMono (Nat.le_max_right F₁ F₂) d _ k₂]
    exact h
  | case9 d n ty val body ihty ihval ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 μ m.acval env (Level.substFn φ ks us) F d ty
      with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hva : denote2 μ m.acval env (Level.substFn φ ks us) F d val
      with _ | va
    · rw [hva] at h; exact nomatch h
    rw [hva] at h
    rcases hba : denote2 μ m.acval env (Level.substFn φ ks us) F (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain ⟨F₁, hle₁, k₁⟩ := ihty ta hta
    obtain ⟨F₂, hle₂, k₂⟩ := ihval va hva
    obtain ⟨F₃, hle₃, k₃⟩ := ihbody ba hba
    rw [Expr.instantiateLevelParams_instantiate1 ks us body 0] at k₃
    have g₁ : F₁ ≤ max (max F₁ F₂) F₃ := by omega
    have g₂ : F₂ ≤ max (max F₁ F₂) F₃ := by omega
    have g₃ : F₃ ≤ max (max F₁ F₂) F₃ := by omega
    refine ⟨max (max F₁ F₂) F₃, by omega, ?_⟩
    rw [Expr.instantiateLevelParams, denote2,
      denote2_fuelMono g₁ d _ k₁, denote2_fuelMono g₂ d _ k₂,
      denote2_fuelMono g₃ (d + 1) _ k₃]
    exact h
  | case10 d sn i e ihe =>
    intro ea h
    rw [denote2] at h
    rcases hea : denote2 μ m.acval env (Level.substFn φ ks us) F d e
      with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    obtain ⟨F₁, hle₁, k₁⟩ := ihe ea' hea
    refine ⟨F₁, hle₁, ?_⟩
    rw [Expr.instantiateLevelParams, denote2, k₁]
    exact h
  | case11 d k hsup =>
    intro ea h
    rw [denote2, if_pos hsup] at h
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    rw [ez, es] at h
    refine ⟨F, Nat.le_refl F, ?_⟩
    rw [Expr.instantiateLevelParams, denote2, if_pos hsup]
    exact h
  | case12 d k hsup =>
    intro ea h
    rw [denote2, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denote2, if_pos hsup] at h
    have hg := hsup
    simp only [Setlec.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    rw [ez, es, esol, echar, eofn, enil, econs] at h
    refine ⟨F, Nat.le_refl F, ?_⟩
    rw [Expr.instantiateLevelParams, denote2, if_pos hsup]
    exact h
  | case14 d s hsup =>
    intro ea h
    rw [denote2, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denote2.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE n ty b mb => exact absurd rfl (hpi n ty b mb)
    | lam n ty b mb => exact absurd rfl (hlam n ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The closing note: what is settled and what is not

**Not settled: is `Denote2InstLevels` true?**  No witness either way
was built, and none is claimed.  What moved:

* the *specific* doubt seal 12 recorded is answered.  One of the two
  named guards is not in the seam at all; the other flips only in the
  direction that makes runs succeed more, which is the direction the
  statement is stated in.  So `piResultIsProp`/`piResultNeverZero` are
  **not** a refutation, and the campaign should stop treating them as
  a live one;
* the residue is four `Prop`s smaller: what is left is
  `InferInstLevels` and `WhnfSortInstLevels`, about the checker alone;
* consequently the question is now **attackable and refutable by
  anyone**, which it was not while it was phrased over an `EnvS2`.

**The trap-check, and its limit (seal 11).**  All four new `Prop`s
assert a checker success as a conclusion, so the smallest-fuel test
applies.  At `F = 1` every one of them is **vacuous**, not clean:
`sortOfE μ env φ 1 d e = none` unconditionally (`sortOfE_oneD`,
`Step2/Dispatch.lean`) and `inferTypeCore`/`whnf` throw at fuel `1`,
so the hypothesis is unsatisfiable and the test says nothing.  Seal
11's caveat therefore applies with full force here: this is not a
clean bill of health, and `CtxOk2R` passed a *cleaner* test than this
and was false anyway.

**What survives if the crossing turns out false.**  Two things, and
they are already load-bearing:

* `acvalDefnInst_noParams` (`Step2/Whnf.lean`) — the delta exit at a
  declaration with **no level parameters**, from the fields as they
  stand.  That is the whole of the crossing for every non-parametric
  definition, which is most of a real stream;
* the factoring itself.  `denote2_instLevels_of` is not conditional on
  the crossing being true: it says the `denote2` side is *entirely*
  algebra, so any repair to the statement can be made at the two
  checker primitives without re-doing the induction.  If
  `WhnfSortInstLevels` has to be weakened (say, to a conclusion "up to
  `Level.isEquiv`" rather than syntactic `Level.subst`), only
  `sortOfEInstLevels_of` moves.

**`μ.verified` is not used anywhere in this file**, by any of the four
new statements or their proofs — everything here is mode-generic, as
seal 10 requires.  The mode `μ` is threaded and never inspected.

## Amendment: the two primitives were settled, and both are FALSE

`Step2/LevelsInst.lean` settles `InferInstLevels` and
`WhnfSortInstLevels` as stated above, and both are **refuted**:
`not_inferInstLevels`, `not_whnfSortInstLevels`.  Neither carries an
environment hypothesis, and a stored constant whose expression mentions
a level parameter outside its own `levelParams` — legal for a bare
`Env`, impossible for a checked one — defeats both.  `sortOfE` falls
with them (`not_sortOfEInstLevels`), so the gap is in the *factoring*,
not only in the primitives.

The repair is `EnvWF`, which `Denote2InstLevels`' own `EnvS2` already
carries (`m.base.wf`): `denote2_instLevels_ofW` re-derives everything
here from the `…W` forms, so `denote2_instLevels_of` and the whole
algebraic half of this file stand unchanged.  The `…W` forms are open;
the crossing is **not** closed. -/

end Setlec.SetR.Interp2
