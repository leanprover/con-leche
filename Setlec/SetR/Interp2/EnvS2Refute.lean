import Setlec.SetR.Interp2.Claims2A
import Setlec.SetR.Interp2.Step2.Whnf

/-!
# STOP 2 — the shapes that demand `denote2` success at every fuel

**Repaired since; this file is the evidence.**  `EnvS2`'s two offending
fields now carry the existential form, so the refutations below are
stated against the *old* shapes, restated here as
`AcvalDefnUniform`/`AcvalThmUniform`.  A refutation that disappears
when its subject is fixed leaves no record that the fix was needed.

`EnvS2.acval_defn` and `EnvS2.acval_thm` *were* **equations demanding
success, universally quantified over the annotation fuel**:

```
acval_defn : ∀ μ φ fuel cv value hint,
  .defnInfo cv value hint ∈ env.consts →
  denote2 μ acval env φ fuel 0 value = some (acval cv.name φ)
```

`fuel = 1` is admitted, and `denote2` at fuel `1` returns `none` on
every `λ` and every `∀` (`denote2_one_lam`, `denote2_one_forallE`:
the binder clauses call `lamSortE`/`sortOfE`, which need a `whnf` run
and so cannot return at fuel `1`).  So the field is false as soon as
the environment stores **one definition whose body is a `λ`** — that
is, essentially every environment past `Env.empty`.

`EnvS2.empty` is not evidence against this: its `env.consts = []`
makes both fields vacuous.  This is the same masking that hid the
`InferClaims2` defect — *the one witness in the landed set had no
constants in it.*

## Consequence

The migration item "swap the fourteen's conclusion from
`Nonempty (EnvS V env')` to `Nonempty (EnvS2UM V μ env')`" is **not
merely unproved, it is unprovable** while these two fields keep this
shape.  No amount of work in the install layer can produce an `EnvS2`
for an environment with a λ-bodied definition in it.

## The repair, and why it is a weakening that costs nothing

`Loop.lean`'s `whnfStep2_delta`/`whnfStep2_delta_thm` are the only
consumers, and what the delta exit actually needs is *uniqueness*, not
*existence at every fuel*: given that the unfolded body annotates at
all, that annotation must be the constant's own leaf.  Stated as an
implication the field is satisfiable — vacuous at the low fuels where
`denote2` cannot return, contentful where it can:

```
acval_defn : ... → ∀ {ea}, denote2 μ acval env φ fuel 0 value = some ea
  → ea = acval cv.name φ
```

Existence is then supplied where it is genuinely available, at a fuel
the *prover* picks — which is exactly repair R3's shape in
`Claims2A.lean`, arrived at independently here.

## A second, matching defect in `Claims2A` itself

The same argument refutes `WhnfClaims2A` (and `WhnfCoreClaims2A`):
repair R1 freed the annotation fuel `F` but still demands the
**reduct's** annotation at that same `F`, and reduction can produce a
term needing more fuel than the subject did — the delta exit turns a
`.const` leaf (annotates at fuel `1`) into a `λ` body (does not).
`whnfClaims2A_delta_refuted` below is the conditional witness, and
`Interp2/Claims2B.lean` is the correction: the reduct's annotation at
some `F' ≥ F`, with `denote2_fuelMono` carrying the subject's own
annotation up to `F'` unchanged so composition still works.

*R1 and R3 are one repair, and applying it to three of the four claims
and not the fourth was the mistake.*

## The generative rule

Both defects, and nothing else in the family, fall out of one test:

> A shape that asserts `denote2 … F … e = some _` as a **conclusion**,
> for an `F` its consumer may choose, is false unless `e` is a leaf.

`denote2`'s binder clauses call `sortOfE`/`lamSortE`, which need a
`whnf` run and so cannot return at fuel `1`.  Applied deliberately:
the reduction claims asserted success for the *reduct*; `acval_defn`
asserted it for a definition's *body*; neither is a leaf.  Shapes that
assert `denote2` success as a **hypothesis** are safe — they merely go
vacuous at low fuel, which weakens the statement rather than falsifying
it.  `CtxOk2` and `mem_type2` are of that kind, and survive.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr CtxOkR)
open Setlec (CheckMode Env Expr Name Level BinderMeta ConstantInfo
  ConstantVal ReducibilityHint whnf)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {φ : Name → Nat}

/-! ## The refuted shapes, restated

`EnvS2`'s two fields have since been repaired to the existential form
(`Setlec/SetR/Annot/EnvS2.lean`).  The refutations are kept, and to
keep them the *old* shapes are restated here as standalone
predicates — a refutation that vanishes when its subject is fixed
leaves no evidence that the fix was necessary. -/

/-- The old `acval_defn`: the body's annotation demanded at **every**
fuel. -/
def AcvalDefnUniform {env : Env}
    (acval : Name → (Name → Nat) → AVExpr) : Prop :=
  ∀ (μ : CheckMode) (φ : Name → Nat) (fuel : Nat)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    denote2 μ acval env φ fuel 0 value = some (acval cv.name φ)

/-- The old `acval_thm`, ditto. -/
def AcvalThmUniform {env : Env}
    (acval : Name → (Name → Nat) → AVExpr) : Prop :=
  ∀ (μ : CheckMode) (φ : Name → Nat) (fuel : Nat)
    (cv : ConstantVal) (value : Expr),
    ConstantInfo.thmInfo cv value ∈ env.consts →
    denote2 μ acval env φ fuel 0 value = some (acval cv.name φ)

/-- **The old field admits no λ-bodied definition.**  Unconditional:
no run, no annotation hypothesis, no choice of `V`. -/
theorem acvalDefnUniform_lam_refuted {env : Env}
    {acval : Name → (Name → Nat) → AVExpr}
    (h : AcvalDefnUniform (env := env) acval)
    {cv : ConstantVal} {n : Name} {ty body : Expr} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv (.lam n ty body mb) hint
      ∈ env.consts) : False := by
  have h1 := h Setlec.CheckMode.noModel (fun _ => 0) 1 cv
    (.lam n ty body mb) hint hc
  rw [denote2_one_lam] at h1
  exact nomatch h1

/-- Ditto for a `∀`-bodied definition (a type abbreviation). -/
theorem acvalDefnUniform_pi_refuted {env : Env}
    {acval : Name → (Name → Nat) → AVExpr}
    (h : AcvalDefnUniform (env := env) acval)
    {cv : ConstantVal} {n : Name} {ty body : Expr} {mb : BinderMeta}
    {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv (.forallE n ty body mb) hint
      ∈ env.consts) : False := by
  have h1 := h Setlec.CheckMode.noModel (fun _ => 0) 1 cv
    (.forallE n ty body mb) hint hc
  rw [denote2_one_forallE] at h1
  exact nomatch h1

/-- Ditto for a theorem whose proof term is a `λ` — the proof of any
implication or any universally quantified statement. -/
theorem acvalThmUniform_lam_refuted {env : Env}
    {acval : Name → (Name → Nat) → AVExpr}
    (h : AcvalThmUniform (env := env) acval)
    {cv : ConstantVal} {n : Name} {ty body : Expr} {mb : BinderMeta}
    (hc : ConstantInfo.thmInfo cv (.lam n ty body mb)
      ∈ env.consts) : False := by
  have h1 := h Setlec.CheckMode.noModel (fun _ => 0) 1 cv
    (.lam n ty body mb) hc
  rw [denote2_one_lam] at h1
  exact nomatch h1

/-- **The matching defect in the amended reduction claim.**  Whenever
`whnf` takes its delta exit from a constant to a `λ`-shaped body, and
the constant annotates at fuel `1` (leaves do), `WhnfClaims2A` demands
the reduct's annotation at fuel `1` too — which `denote2_one_lam`
denies.  Conditional only on the run and the subject's annotation,
both of which any real environment supplies. -/
theorem whnfClaims2A_delta_refuted {env : Env} (m : EnvS2UM V μ env)
    {fuel d : Nat} {e : Expr} {Δa : List AVExpr} {ea : AVExpr}
    {n : Name} {ty body : Expr} {mb : BinderMeta}
    (hrun : whnf μ env fuel d e = .ok (.lam n ty body mb))
    (hsc : Expr.WScoped d e) (hlb : e.looseBVarsBounded 0 = true)
    (hlv : Expr.LeavesBounded e)
    (hctx : CtxOkR μ m.base.cval env φ d (Δa.map AVExpr.erase) e)
    (hea : denote2 μ m.acval env φ 1 d e = some ea) :
    ¬ WhnfClaims2A μ m φ fuel := by
  intro hclaim
  obtain ⟨ea', hea', -⟩ :=
    hclaim hrun hsc hlb hlv hctx hea
  rw [denote2_one_lam] at hea'
  exact nomatch hea'

/-! ## Is the repair satisfiable in the very case that killed it?

The repaired field is only worth having if a λ-bodied definition can
now actually satisfy it.  This arc has been burned twice by a witness
that was vacuous — `EnvS2.empty` has no constants, and seal 6's
acceptance test only killed the witness it was built from — so the
positive direction gets checked explicitly rather than assumed.

`denote2_two_lam` is the counterpart of `denote2_one_lam`: the λ that
fuel `1` cannot annotate, fuel `2` can.  It is the exact analogue of
`denote2_two_forallE`, which played this role for R3. -/

/-- **The smallest λ annotates at fuel `2`.**  `lamSortE` needs an
`inferTypeCore` run and a `sortOfE` run; both return at fuel `2`. -/
theorem denote2_two_lam {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) (n : Name) (mb : BinderMeta) :
    denote2 μ acval env φ 2 d
        (.lam n (.sort .zero) (.sort .zero) mb)
      = some (.lam 2 (.sort 0) (.sort 0)) := by
  rw [denote2, Expr.instantiate1_sort, denote2_two_sort,
    denote2_two_sort]
  rw [lamSortE, infer_two_sort]
  simp only [Except.toOption]
  rw [sortOfE_two_sort]
  simp [Level.eval]

/-- **The repaired field is satisfiable for a λ-bodied definition** —
the shape `acvalDefnUniform_lam_refuted` proves impossible for the old
one.  Stated over the *field's* form, at an arbitrary demanded fuel,
so it is the repair that is being tested and not a special case. -/
theorem acval_defn_repaired_sat {acval : Name → (Name → Nat) → AVExpr}
    {c : Name} {n : Name} {mb : BinderMeta}
    (hac : acval c φ = .lam 2 (.sort 0) (.sort 0)) (F : Nat) :
    ∃ F', F ≤ F' ∧
      denote2 μ acval env φ F' 0
        (.lam n (.sort .zero) (.sort .zero) mb) = some (acval c φ) := by
  refine ⟨max F 2, Nat.le_max_left _ _, ?_⟩
  rw [hac]
  exact denote2_fuelMono (Nat.le_max_right F 2) 0 _
    (denote2_two_lam 0 n mb)

end Setlec.SetR.Interp2
