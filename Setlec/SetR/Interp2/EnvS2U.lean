import Setlec.SetR.Interp2.Install2
import Setlec.SetR.Interp2.Step2.Whnf

/-!
# The environment tier, in the uniqueness form — the freeze

Seal 34 ruled that `EnvS2`'s two `denote2` fields take the
**uniqueness** form: *if* a stored value annotates, the annotation is
the constant's own leaf. This file freezes that.

## Why a new structure and not an edit

Seal 18's ruling: a definition that tombstones construct concretely is
amended by **new definition plus bridge**, never in place. Here the
older claim lanes (`…2B`, `…2D`) consume the *existential* fields, and
"add, never delete" keeps them green. `EnvS2U` is strictly weaker than
`EnvS2`, so the bridge runs `EnvS2 → EnvS2U` and nothing is lost.

## Why uniqueness is the right form

The existential field asserted that a stored value **annotates** —
which is `Denote2Total`'s wall (parked, seal 33), and a field is a
*conclusion*, so it cannot escape by dual success the way generation
six's claims did. Uniqueness asserts nothing about existence, and it
is what the delta exit actually consumes.

**STOP 2 said so first.** That seal's own text reads: *"what the delta
exit actually needs is uniqueness, not existence at every fuel"* — and
then adopted the existential anyway. This is a return to a recorded
truth, not a new bet.

## Where existence now lives

In exactly one place: generation six's `Exists2E` factors. That is the
point of the ruling — existence owed once, not twice.

## The tenth field, and why it is still not here

Seal 40 recorded that dropping `EnvS2`'s `cval_annot` was an omission
in writing this freeze rather than a ruling, and owed its restoration.
**Restoring it is one line here and one in `EnvS2.toU`, and it does
not land** — not because of the probes (both discharge it: see
`probeEnvS_cvalAnnot` and `piProbeEnvS_cvalAnnot`, which are exactly
the field at the two probes' valuations, ready to be spliced in), but
because of the *third* `EnvS2U` construction site.

`Keys2Cond.lean`'s `declStep2_of_axiom` builds an `EnvS2U` at a fresh
axiom install, and it cannot supply the field from its hypotheses.
Two independent reasons, both statement-level:

* the fresh name's collapse-lane valuation `hbase.cval cvA.name` is
  **unconstrained** by the theorem's premises — `MemberBlock2` is a
  membership fact, `EnvS` has no annotation field — and a valuation
  can fail `CvalAnnot`: `Infer` has no `.prf` clause
  (`Annot/Validity.lean`'s `not_infer_prf`), so a leaf like
  `.lam .prf .prf` has no `Annotates` derivation at all;
* the *old* names' `CvalAnnot` sits at `env`, and moving it to the
  extended environment is an **environment weakening for `Annotates`
  / `Infer` / `DefEq`**, which the tree does not have anywhere — the
  `denote2` lane's `denote2_envExtend` has no relational counterpart.

So the restoration needs a new hypothesis on `declStep2_of_axiom`
(a `CvalAnnot` supplier at the extended environment), and that is a
statement change to a file this batch may not touch.  Recorded here so
the next attempt does not re-discover it at the probes, which are not
where the obstruction is.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable (V : Type w) [SetTheory V]

/-- **The environment invariant, uniqueness form.**  Identical to
`EnvS2` except that the two `denote2` fields assert *identification*
rather than *existence*. -/
structure EnvS2U (env : Env) where
  /-- the collapse-lane invariant, contained -/
  base : EnvS V env
  /-- the canonical annotated valuation -/
  acval : Name → (Name → Nat) → AVExpr
  /-- it erases to the collapse-lane valuation -/
  acval_erase : ∀ (n : Name) (ψ : Name → Nat),
    (acval n ψ).erase = base.cval n ψ
  /-- every leaf is closed, as a lifting equation -/
  acval_closed : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
    (acval n ψ).liftN 1 k = acval n ψ
  /-- a leaf reads only its own level parameters -/
  acval_params : ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      acval n ψ₁ = acval n ψ₂
  /-- every leaf is truthful -/
  acval_ok2 : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOk2 V ρ (acval n ψ)
  /-- **uniqueness, not existence**: *if* a definition's value
  annotates, that annotation is the constant's own leaf -/
  acval_defn : ∀ (μ : CheckMode) (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ {ra : AVExpr},
      denote2 μ acval env φ F 0 value = some ra →
      ra = acval cv.name φ
  /-- ditto for a theorem's proof value -/
  acval_thm : ∀ (μ : CheckMode) (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr),
    ConstantInfo.thmInfo cv value ∈ env.consts →
    ∀ {ra : AVExpr},
      denote2 μ acval env φ F 0 value = some ra →
      ra = acval cv.name φ
  /-- stored constants inhabit their annotated types -/
  mem_type2 : ∀ (μ : CheckMode) (φ : Name → Nat) (fuel : Nat),
    ∀ c ∈ env.consts, ∀ ta : AVExpr,
    denote2 μ acval env φ fuel 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, interp2 V ρ (acval c.name φ) ∈ˢ interp2 V ρ ta

/-- **The bridge.**  `EnvS2U` is strictly weaker, so every `EnvS2`
yields one — the existential field identifies any other annotation by
`denote2_fuelMono` plus functionality. -/
noncomputable def EnvS2.toU {env : Env} (m : EnvS2 V env) :
    EnvS2U V env where
  base := m.base
  acval := m.acval
  acval_erase := m.acval_erase
  acval_closed := m.acval_closed
  acval_params := m.acval_params
  acval_ok2 := m.acval_ok2
  mem_type2 := m.mem_type2
  acval_defn := by
    intro μ φ F cv value hint hc ra hra
    obtain ⟨F', hle, h'⟩ := m.acval_defn μ φ F cv value hint hc
    have := denote2_fuelMono hle 0 value hra
    rw [h'] at this
    exact (Option.some.inj this).symm
  acval_thm := by
    intro μ φ F cv value hc ra hra
    obtain ⟨F', hle, h'⟩ := m.acval_thm μ φ F cv value hc
    have := denote2_fuelMono hle 0 value hra
    rw [h'] at this
    exact (Option.some.inj this).symm

/-- The empty environment, in the uniqueness form. -/
noncomputable def EnvS2U.empty : EnvS2U V Env.empty :=
  (EnvS2.empty (V := V)).toU

/-! ## The three sweeps on the frozen text

**1. Smallest fuel — satisfied by construction.** No field asserts a
`denote2` success as a *conclusion*: in `acval_defn`, `acval_thm` and
`mem_type2` alike, every `denote2` sits in a **premise**. That is the
whole content of the uniqueness ruling, and it is why the rule that
refuted the original fields cannot reach these. Per seal 11, still not
a clean bill of health — only the absence of one hazard.

**2. Vacuity — probed at the killing case.** The original fields died
on a λ-bodied definition (`acvalDefnUniform_lam_refuted`): they
demanded `denote2` success at every fuel, and `denote2_one_lam` is
`none`. The uniqueness form **survives exactly there**, and for the
right reason — the premise fails, so the obligation is discharged
rather than contradicted. `acval_defn_uniq_lam_ok` below.

This is the check seal 21 and seal 25 could *not* perform, because
their repairs excluded the killing case by construction. Here the
killing case is still admissible; only the obligation at it has
changed. **So this is the first repair in the arc whose satisfiability
could be tested in the very case that killed the old shape.**

**3. Tombstones — swept.** A file added, none edited; the tree builds
green with every `*_refuted`, `*Uniform`, `not_*` and `*_flips`
declaration in place. -/

/-- **The vacuity probe, at the case that killed the old field.**  For
a λ-bodied definition at fuel `1`, the uniqueness obligation holds for
*any* valuation — because `denote2` returns `none` there, so the
premise cannot be met. The old field asserted the equation and was
false; this one asserts an implication and is satisfied. -/
theorem acval_defn_uniq_lam_ok {env : Env}
    (acval : Name → (Name → Nat) → AVExpr) (μ : CheckMode)
    (φ : Name → Nat) (cv : ConstantVal) (n : Name)
    (ty body : Expr) (mb : Setlec.BinderMeta) :
    ∀ {ra : AVExpr},
      denote2 μ acval env φ 1 0 (.lam n ty body mb) = some ra →
      ra = acval cv.name φ := by
  intro ra hra
  rw [denote2_one_lam] at hra
  exact nomatch hra

/-! ## R5 — the six `EnvS` fields with no `EnvS2` counterpart

Ruled, on the discipline the keys survey applied to itself: **a field
is added when a consumer can attempt its discharge, and not before.**

* `proj_ok` — `ProjOkT` is **syntactic and V-free**, so `base` carries
  it unchanged. No counterpart is owed, now or later.
* `rec_rules`, `nat_ops`, `div_mod` — interp2 consumers exist
  (`IotaStep2*`, `ReduceNatStep2*`), and the laws are drafted
  (`RecRulesV2` — **marked INSUFFICIENT**, `NatOpsV2`, `DivModV2`).
  These are the three that will join, once their laws are settled.
* `caps_ok`, `reduce_ops` — **no interp2 consumer exists**.
  `reduce_ops` has exactly one consumer in the whole tree, and it is
  install-tier-internal. Adding either now would be a named `Prop`
  nobody can attempt: seal 20's *"vacuous `Prop` with a good name,
  worse than none"*.

## R6 — a non-problem, checked rather than assumed

The keys survey reported that `Nonempty (EnvS V env₂)` hides the
produced `cval`, so `DeclBasisS`/`DeclIndS` would need a Σ-valued
restatement inside a 5900-line proof. **It does not.** `Nonempty`
eliminates into `Prop`, and `Nonempty (EnvS2U V env₂)` *is* a `Prop`,
so `obtain ⟨m⟩` yields the witness and the extra fields are built
against it. Verified by elaboration before this file was written.

*A reported obstacle that costs a 5900-line edit is worth ten minutes
of checking before it is believed.*
-/

end Setlec.SetR.Interp2
