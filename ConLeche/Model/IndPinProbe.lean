module

public import ConLeche.Model.NatEqs
public import ConLeche.Model.Claims
public section

/-!
# The nested-pin conjunct is refuted (task #161 ind tier part 6, THE PROBE)

Part 5 raised a **risk flag**, unmechanized, on `RecRuleLaw`'s ∃-form
nested-pin conjunct (`Annot/EnvModelM.lean`):

```
(∀ lvls pins, RecRule.fire rl = .nested lvls pins →
  ∀ i, i < RecRule.ctorParams rl →
  ∃ vpa : AnnotTerm,
    denoteMeta m.acval env φ rP
      (ConLeche.Verify.openRev 0 rP
        ((pins.getD i default).instantiateLevelParams
          cv.levelParams us)) = some vpa ∧
    ∀ ρ : Nat → V, WellDenotedV V ρ vpa) ∧
```

— the grading `∀ ρ : Nat → V, WellDenotedV V ρ vpa` is demanded
*unconditionally in `ρ`* of the pin's **open** reading.  This file
mechanizes the refutation the flag asked for, and it is a refutation,
not a difficulty: the conjunct is **false** on a stream the e2e suite
accepts today (`tests/e2e/nested_rec.ndjson`).

## The three links

1. **The shape is what real streams store** (measured, not assumed).
   An instrumented `nestedRuleShapeF` (`Kernel/CheckerS.lean`, the
   version that executes; the trace was reverted) over the only three
   fixtures in the corpus that fire a `.nested` rule prints

   ```
   PINPROBE cvName=Tree.rec_1  rP=6 mI=6 cnP=1 bounded0=false
     pins=[Expr.app (Expr.const `Tree []) (Expr.bvar 5)]
   PINPROBE cvName=PTree.rec_1 rP=6 mI=6 cnP=2 bounded0=false
     pins=[Expr.bvar 5, …]
   PINPROBE cvName=TV.rec_1    rP=6 mI=7 cnP=1 bounded0=false
     pins=[Expr.app (Expr.const `TV []) (Expr.bvar 5)]
   ```

   Every one of them is **open** (`looseBVarsBounded 0 = false`), and
   two of the three are *applications* whose argument is a loose bvar.
   This is not incidental: `nestedRuleShape`'s own guard is
   `p.looseBVarsBounded rP` — open pins are exactly what it admits —
   and its docstring names the shape (`Impl α (fun _ => T ...)`).

2. **The reading of such a pin is an open application**
   (`openRev_pin_shape` / `denoteMeta_pin_shape` below, both by `rfl`):
   `openRev 0 rP` turns the pin's loose bvars into `fvar`s and
   `denoteMeta … rP` turns those into `.bvar`s, so `vpa` is
   `.app (m.acval `Tree ψ) (.bvar 0)` — an application at a closed
   const-leaf head with a *free* `.bvar` argument.

3. **No such reading is graded uniformly in `ρ`**
   (`not_uniform_wellDenoted_open_app`).  `WellDenoted` of `.app f a` carries
   `∃ v A B, ⟦f⟧ ∈ˢ piR v A B ∧ ⟦a⟧ ∈ˢ A`; at a **closed** head whose
   value inhabits a **positive-kind** product the domain `A` is pinned
   (`piR_dom_unique`, after `not_pt_mem_piR_pos` rules the squash
   regime out), so the conjunct asserts `ρ j ∈ˢ A` for *every* `ρ` —
   i.e. that the set `A` contains everything.  Instantiating at
   `ρ = fun _ => A` contradicts `not_mem_self`.

   The head of the measured pin is `Tree : Type → Type`, whose reading
   inhabits `piR 1 (univ 1) (fun _ => univ 1)` by the carrier's own
   `mem_type` — positive kind, so link 3's hypotheses are exactly the
   environment invariant `EnvModelM` already carries.
   `open_app_shape_realizable` exhibits the hypotheses' satisfiability
   with no environment at all.

## What this does *not* claim

It does not claim the *content* the conjunct is reaching for is
unavailable — only that the `∀ ρ` spelling is unsatisfiable.  The
supplier is the install's `checkAnnotList ops envSelf depth pinsP`
(`Inductives/Modeled.lean:288`), fired on the pins **instantiated at the
public recursor frame's openers** (`pinsP := pins.map (Expr.instSpine
(fvsP.take rP) (rP - 1) ·)`, `Inductives/Modeled.lean:282`), and every
claims-layer conversion of such a certificate produces a grading of the
form `∀ ρ, Sat V Δa ρ → WellDenotedV V ρ …` — guarded by a context, never
unconditional.  The consumer wants the same guarded form: the
conjunct's *equality* half already speaks of the **closed** comparand
`AnnotTerm.instRevChain (xs.take rP) vpa`, under the ambient
`TeleFitPA V ρ TVa (xs ++ …) restR` premise, and that is the term
`DefEqClaim` needs graded.

The repair shape is therefore "grade the term the equality half
already names, where it names it", and it is the statement layer's —
see the DESIGN entry for this seal.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Link 3: the semantic refutation -/

/-- **The open-application grading is unsatisfiable.**  If `f`'s
reading does not read the environment (every `acval` leaf is such, by
`acval_closed`) and inhabits a product at a *positive* kind, then
`.app f (.bvar j)` cannot be `WellDenoted` at every `ρ`: the app clause
pins the domain, and no set contains every value. -/
theorem not_uniform_wellDenoted_open_app {f : AnnotTerm} {j v : Nat}
    {A : V} {B : V → V} (hv : v ≠ 0)
    (hcl : ∀ ρ ρ' : Nat → V, interp V ρ f = interp V ρ' f)
    {ρ₀ : Nat → V} (hf : interp V ρ₀ f ∈ˢ piR v A B) :
    ¬ (∀ ρ : Nat → V, WellDenoted V ρ (.app f (.bvar j))) := by
  intro h
  have hA := h (fun _ => A)
  rw [WellDenoted_app] at hA
  obtain ⟨-, -, v', A', B', hf', ha', -⟩ := hA
  rw [hcl (fun _ => A) ρ₀] at hf'
  have hv' : v' ≠ 0 := by
    intro hz
    subst hz
    exact not_pt_mem_piR_pos hv (by rw [← eq_pt_of_mem_piR_zero hf']; exact hf)
  have hAA : A = A' := piR_dom_unique hv hv' hf hf'
  rw [interp_bvar] at ha'
  exact not_mem_self A (hAA ▸ ha')

/-- The same at the P tier's currency (`WellDenotedV = WellDenoted ∧
AnnotValid`). -/
theorem not_uniform_wellDenotedV_open_app {f : AnnotTerm} {j v : Nat}
    {A : V} {B : V → V} (hv : v ≠ 0)
    (hcl : ∀ ρ ρ' : Nat → V, interp V ρ f = interp V ρ' f)
    {ρ₀ : Nat → V} (hf : interp V ρ₀ f ∈ˢ piR v A B) :
    ¬ (∀ ρ : Nat → V, WellDenotedV V ρ (.app f (.bvar j))) :=
  fun h => not_uniform_wellDenoted_open_app hv hcl hf fun ρ => (h ρ).1

/-- **The refutation at an environment leaf** — the shape the pin's
reading actually has.  `hf`'s hypothesis is what `EnvModelM.mem_type`
gives for a type former at a positive sort (`Tree : Type → Type`
lands in `piR 1 (univ 1) (fun _ => univ 1)`). -/
theorem not_uniform_wellDenotedV_acval_open_app {env : Env}
    (m : EnvModel V env) (n : Name) (ψ : Name → Nat) {j v : Nat}
    {A : V} {B : V → V} (hv : v ≠ 0) {ρ₀ : Nat → V}
    (hf : interp V ρ₀ (m.acval n ψ) ∈ˢ piR v A B) :
    ¬ (∀ ρ : Nat → V, WellDenotedV V ρ (.app (m.acval n ψ) (.bvar j))) :=
  not_uniform_wellDenotedV_open_app hv
    (fun ρ ρ' => acval_interp_closedC m n ψ ρ ρ') hf

/-- The refutation's hypotheses are satisfiable with no environment at
all: the closed identity λ at `Sort 0` reads to a positive-kind
element of `piR 1 (univ 0) (fun _ => univ 0)`.  So
`not_uniform_wellDenoted_open_app` is not vacuous. -/
theorem open_app_shape_realizable :
    ∃ (f : AnnotTerm) (v : Nat) (A : V) (B : V → V),
      v ≠ 0 ∧ (∀ ρ ρ' : Nat → V, interp V ρ f = interp V ρ' f) ∧
      (∀ ρ : Nat → V, interp V ρ f ∈ˢ piR v A B) := by
  refine ⟨.lam 1 (.sort 0) (.bvar 0), 1, univ 0, fun _ => univ 0,
    Nat.one_ne_zero, ?_, ?_⟩
  · intro ρ ρ'
    simp [interp_lam, interp_sort, interp_bvar, cons_zero]
  · intro ρ
    simp only [interp_lam, interp_sort, interp_bvar, cons_zero]
    exact lamR_mem fun _ hx => hx

/-- Both halves at once: the conjunct's spelling is refuted at a
witness that exists. -/
theorem exists_ungradable_open_app :
    ∃ (f : AnnotTerm) (j : Nat),
      ¬ (∀ ρ : Nat → V, WellDenotedV V ρ (.app f (.bvar j))) := by
  obtain ⟨f, v, A, B, hv, hcl, hf⟩ := open_app_shape_realizable (V := V)
  exact ⟨f, 0, not_uniform_wellDenotedV_open_app hv hcl (hf (fun _ => A))⟩

/-! ## Link 2: the measured pin reads to exactly that shape

`Tree.rec_1`'s stored pin is `Tree (bvar 5)` at `rP = 6`; the two
steps below are the reading's syntactic half, by `rfl`. -/

/-- `openRev 0 6` sends the measured pin's loose `bvar 5` to `fvar 5`
(the reverse opening consumes the innermost variable first). -/
theorem openRev_pin_shape (c : Name) :
    ConLeche.Verify.openRev 0 6
        (Expr.app (Expr.const c []) (Expr.bvar 5))
      = Expr.app (Expr.const c [])
          (Expr.fvar 5 (Expr.sort Level.zero)) := rfl

/-- …and `denoteMeta … 6` reads that as `.app (acval c ψ) (.bvar 0)` —
an application with a **free** `.bvar` argument, which
`not_uniform_wellDenotedV_acval_open_app` refutes. -/
theorem denoteMeta_pin_shape {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (c : Name) (cv : ConLeche.ConstantInfo)
    (hfind : env.find? c = some cv)
    (hlp : cv.toConstantVal.levelParams = []) :
    denoteMeta m.acval env φ 6
        (ConLeche.Verify.openRev 0 6
          (Expr.app (Expr.const c []) (Expr.bvar 5)))
      = some (.app (m.acval c (Level.substFn φ [] [])) (.bvar 0)) := by
  rw [openRev_pin_shape, denoteMeta_app, denoteMeta_const hfind (by simp [hlp]),
    denoteMeta_fvar]
  simp [hlp]

end ConLeche.Model
