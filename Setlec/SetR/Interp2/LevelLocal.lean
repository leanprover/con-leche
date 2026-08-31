import Setlec.SetR.Interp2.Step2.Levels

/-!
# Wall 2 — level-locality, the statement seal

The lane's last item of its own. **One statement, audited against
three consumers**, because all three fail at the *same clause*:
`denote2`'s `.forallE` and `.lam` carry `sortOfE`/`lamSortE` numerals,
and those numerals are **precisely what `erase` forgets**.

## The three consumers

1. **`AxiomResidues2M.params`** (seal 61). Conjunct 2 of the axiom
   keys *is* the level-parameter law on the collapse lane, and `erase`
   carries it one way — `(A ψ₁).erase = (A ψ₂).erase`. Recovering
   `A ψ₁ = A ψ₂` needs `erase` **injective**, and it is not: the
   forgotten numerals are exactly where a level parameter shows up.
2. **`ValueResidues2M.params`** — `denote_params_ext`'s twin (seal 54),
   stopped at the same clause, in the same two constructors.
3. **`Denote2InstLevels`** (`Step2/Levels.lean`), whose own residue is
   the level crossing at those same numerals.

## Why one statement can serve all three

Each wants the numerals to depend on the level assignment **only
through the subject's own level parameters**. Given that:

* (1) and (2) follow because two assignments agreeing on a constant's
  parameters compute the *same* numerals, so the annotated leaves are
  equal — not merely equal after erasure;
* (3) follows because `Level.substFn φ ks us` and `φ`-after-
  `instantiateLevelParams` agree on every parameter the subject has,
  which is what its `∃ F' ≥ F` slack then transports.

**So the statement is about `sortOfE`/`lamSortE`, not about `erase`.**
Erase-injectivity was the shape the wall presented as; it is not the
shape of its repair. *A wall named by what blocked it is not always
named by what fixes it.*

## The audit's negative half

This does **not** subsume `Denote2InstLevels` outright. That residue
also needs the run to *succeed* on the instantiated term, which
level-locality does not give — seals 25 and 28 established that
`Level.isEquiv`'s fuel makes success non-transportable, and
`not_isEquivSubstMono` is the standing refutation. **Level-locality
serves consumer 3's *numerals*, not its *existence*.** Recorded so the
seal is not read as closing more than it does.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level)

universe w

/-- **Level-locality for the sort computation.**  `sortOfE` reads the
assignment only at parameters the subject declares.

An **equation between two runs**, not an assertion that either
succeeds — so the smallest-fuel rule has nothing to bite on, as with
`Denote2EnvExtend`. Both sides are `none` together. -/
def SortOfELevelLocal (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ps : List Name) (φ₁ φ₂ : Name → Nat) (F d : Nat) (e : Expr),
    e.allLevelParamsDefined ps = true →
    (∀ p ∈ ps, φ₁ p = φ₂ p) →
    sortOfE μ env φ₁ F d e = sortOfE μ env φ₂ F d e

/-- The `lamSortE` twin — the other of the two clauses `erase`
forgets. -/
def LamSortELevelLocal (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ps : List Name) (φ₁ φ₂ : Name → Nat) (F d : Nat) (b : Expr),
    b.allLevelParamsDefined ps = true →
    (∀ p ∈ ps, φ₁ p = φ₂ p) →
    lamSortE μ env φ₁ F d b = lamSortE μ env φ₂ F d b

/-- **What the two buy**: `denote2` itself reads the assignment only at
the subject's declared parameters. This is the form all three
consumers want, and the one an induction over `denote2.induct` should
produce from the two above. -/
def Denote2LevelLocal (μ : CheckMode) (env : Env)
    (acval : Name → (Name → Nat) → AVExpr) : Prop :=
  ∀ (ps : List Name) (φ₁ φ₂ : Name → Nat) (F d : Nat) (e : Expr),
    e.allLevelParamsDefined ps = true →
    (∀ p ∈ ps, φ₁ p = φ₂ p) →
    (∀ n ψ₁ ψ₂, (∀ p ∈ ps, ψ₁ p = ψ₂ p) → acval n ψ₁ = acval n ψ₂) →
    denote2 μ acval env φ₁ F d e = denote2 μ acval env φ₂ F d e

/-! ## The vacuity probe

The premise set is met at a closed subject with no parameters, where
`allLevelParamsDefined []` holds and the agreement is vacuous — so the
statements are not implications from contradictory hypotheses. -/

theorem levelLocal_premises_inhabited (ps : List Name)
    (φ₁ φ₂ : Name → Nat) :
    (Expr.sort .zero).allLevelParamsDefined ps = true ∧
      (∀ p ∈ ([] : List Name), φ₁ p = φ₂ p) := by
  refine ⟨?_, ?_⟩
  · simp [Setlec.Expr.allLevelParamsDefined,
      Setlec.Level.allParamsDefined]
  · intro p hp; exact absurd hp (by simp)

/-! ## The three sweeps

**Smallest fuel** — all three conclusions are **equations between two
runs**; neither side is asserted to succeed. The rule that refuted four
statements in this campaign has nothing to bite on. Per seal 11 that is
the absence of one hazard, not a clean bill of health.

**Vacuity** — probed above. This is the check that matters here, since
every statement is an implication and a premise set that cannot be met
would make all three vacuous.

**Tombstones** — this file adds and edits nothing; no `*_refuted`,
`*Uniform`, `not_*` or `*_flips` declaration is touched. In
particular `not_isEquivSubstMono` stands, and the audit above records
that it is *why* consumer 3 is only partly served.
-/

end Setlec.SetR.Interp2
