import Setlec.SetR.Interp2.LevelLocalKit

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

/-! ## The third statement, from the first two

`denote2` reads the assignment at four kinds of site: the `.sort`
clause (`Level.eval`), the `.const` and literal clauses (the valuation
at a `Level.substFn`), and the `.forallE`/`.lam` numerals
(`sortOfE`/`lamSortE`).  The first three are algebra —
`Level.eval_ext` and `Level.substFn_agree` — and the fourth is exactly
what the two statements above say.  So the induction over
`denote2.induct` goes through with them as hypotheses, in *any*
environment: this derivation is unconditional, and the environment
condition the two primitives need (below) is inherited, not added
here. -/

theorem denote2LevelLocal_of {μ : CheckMode} {env : Env}
    {acval : Name → (Name → Nat) → AVExpr}
    (hs : SortOfELevelLocal μ env) (hl : LamSortELevelLocal μ env) :
    Denote2LevelLocal μ env acval := by
  intro ps φ₁ φ₂ F d e hdef hφ hac
  revert hdef
  induction d, e using denote2.induct (env := env) with
  | case1 d u =>
    intro hdef
    rw [denote2, denote2,
      Level.eval_ext (by simpa [Expr.allLevelParamsDefined] using hdef)
        hφ]
  | case2 d idx nm ty => intro _; rw [denote2, denote2]
  | case3 d n us ci hf hlen =>
    intro hdef
    rw [denote2, hf, denote2, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen,
      hac n _ _ (Level.substFn_agree hφ (ks := ci.toConstantVal.levelParams)
        (by
          simpa [Expr.allLevelParamsDefined, List.all_eq_true]
            using hdef))]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denote2, hf, denote2, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => intro _; rw [denote2, hf, denote2, hf]
  | case6 d n ty body m ihty ihbody =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    have hopen := Expr.allLevelParamsDefined_open (d := d) (n := n)
      hdef.1 hdef.2
    rw [denote2, denote2, ihty hdef.1, ihbody hopen,
      hs ps φ₁ φ₂ F d ty hdef.1 hφ,
      hs ps φ₁ φ₂ F (d + 1) _ hopen hφ]
  | case7 d n ty body m ihty ihbody =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    have hopen := Expr.allLevelParamsDefined_open (d := d) (n := n)
      hdef.1 hdef.2
    rw [denote2, denote2, ihty hdef.1, ihbody hopen,
      hl ps φ₁ φ₂ F (d + 1) _ hopen hφ]
  | case8 d f a ihf iha =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    rw [denote2, denote2, ihf hdef.1, iha hdef.2]
  | case9 d n ty val body ihty ihval ihbody =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    rw [denote2, denote2, ihty hdef.1.1, ihval hdef.1.2,
      ihbody (Expr.allLevelParamsDefined_open (d := d) (n := n)
        hdef.1.1 hdef.2)]
  | case10 d sn i e ihe =>
    intro hdef
    simp only [Expr.allLevelParamsDefined] at hdef
    rw [denote2, denote2, ihe hdef]
  | case11 d n hsup =>
    intro _
    rw [denote2, if_pos hsup, denote2, if_pos hsup,
      hac natZeroName _ _ (Level.substFn_agree hφ (ks := []) (by simp)),
      hac natSuccName _ _ (Level.substFn_agree hφ (ks := []) (by simp))]
  | case12 d n hsup => intro _; rw [denote2, if_neg hsup, denote2,
      if_neg hsup]
  | case13 d s hsup =>
    intro _
    rw [denote2, if_pos hsup, denote2, if_pos hsup,
      hac stringOfListName _ _
        (Level.substFn_agree hφ (ks := []) (by simp)),
      hac listNilName _ _
        (Level.substFn_agree hφ
          (ks := levelParamsAt env listNilName)
          (by simp [Level.allParamsDefined])),
      hac listConsName _ _
        (Level.substFn_agree hφ
          (ks := levelParamsAt env listConsName)
          (by simp [Level.allParamsDefined])),
      hac charName _ _ (Level.substFn_agree hφ (ks := []) (by simp)),
      hac charOfNatName _ _
        (Level.substFn_agree hφ (ks := []) (by simp)),
      hac natZeroName _ _ (Level.substFn_agree hφ (ks := []) (by simp)),
      hac natSuccName _ _ (Level.substFn_agree hφ (ks := []) (by simp))]
  | case14 d s hsup => intro _; rw [denote2, if_neg hsup, denote2,
      if_neg hsup]
  | case15 d x hsrt hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denote2.eq_def, denote2.eq_def]
    | sort u => exact absurd rfl (hsrt u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b m => exact absurd rfl (hpi n ty b m)
    | lam n ty b m => exact absurd rfl (hlam n ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The form the consumers can actually use

`Denote2LevelLocal`'s valuation hypothesis is **uniform in the name**:
*every* leaf reads the assignment only at `ps`.  No consumer holds
that.  What an install holds is `EnvS2UM.acval_params` — each leaf
reads only **its own** parameters — and the two are incomparable.
They meet only at the call sites: `denote2` reads `acval n` at
`Level.substFn φ ci.levelParams us`, and *there* the per-name law
applies, because two assignments agreeing on `ps` agree at `n`'s own
parameters after the substitution (`Level.substFn_ext`, with the
clause's own length guard).

So the induction is run a second time against the per-name law.  It is
the same proof with three clauses re-derived — `.const` and the two
literal spines — and it is this form the `params` consumers take.

*Finding (statement-shape).*  The frozen `Denote2LevelLocal` is not
false; it is **not the form the audit's consumers hold**.  Its
valuation hypothesis has to be weakened to `acval_params` before
either `params` field can spend it. -/

/-- Level-locality of `denote2` over an install's own valuation. -/
def Denote2LevelLocalM (V : Type w) [SetTheory V] (μ : CheckMode)
    {env : Env} (m : EnvS2UM V μ env) : Prop :=
  ∀ (ps : List Name) (φ₁ φ₂ : Name → Nat) (F d : Nat) (e : Expr),
    e.allLevelParamsDefined ps = true →
    (∀ p ∈ ps, φ₁ p = φ₂ p) →
    denote2 μ m.acval env φ₁ F d e = denote2 μ m.acval env φ₂ F d e

theorem denote2LevelLocalM_of {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvS2UM V μ env)
    (hs : SortOfELevelLocal μ env) (hl : LamSortELevelLocal μ env) :
    Denote2LevelLocalM V μ m := by
  intro ps φ₁ φ₂ F d e hdef hφ
  revert hdef
  induction d, e using denote2.induct (env := env) with
  | case1 d u =>
    intro hdef
    rw [denote2, denote2,
      Level.eval_ext (by simpa [Expr.allLevelParamsDefined] using hdef)
        hφ]
  | case2 d idx nm ty => intro _; rw [denote2, denote2]
  | case3 d n us ci hf hlen =>
    intro hdef
    rw [denote2, hf, denote2, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen,
      m.acval_params n ci hf _ _ (fun p hp =>
        Level.substFn_ext hφ
          (by
            simpa [Expr.allLevelParamsDefined, List.all_eq_true]
              using hdef)
          hlen p hp)]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denote2, hf, denote2, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => intro _; rw [denote2, hf, denote2, hf]
  | case6 d n ty body m ihty ihbody =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    have hopen := Expr.allLevelParamsDefined_open (d := d) (n := n)
      hdef.1 hdef.2
    rw [denote2, denote2, ihty hdef.1, ihbody hopen,
      hs ps φ₁ φ₂ F d ty hdef.1 hφ,
      hs ps φ₁ φ₂ F (d + 1) _ hopen hφ]
  | case7 d n ty body m ihty ihbody =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    have hopen := Expr.allLevelParamsDefined_open (d := d) (n := n)
      hdef.1 hdef.2
    rw [denote2, denote2, ihty hdef.1, ihbody hopen,
      hl ps φ₁ φ₂ F (d + 1) _ hopen hφ]
  | case8 d f a ihf iha =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    rw [denote2, denote2, ihf hdef.1, iha hdef.2]
  | case9 d n ty val body ihty ihval ihbody =>
    intro hdef
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    rw [denote2, denote2, ihty hdef.1.1, ihval hdef.1.2,
      ihbody (Expr.allLevelParamsDefined_open (d := d) (n := n)
        hdef.1.1 hdef.2)]
  | case10 d sn i e ihe =>
    intro hdef
    simp only [Expr.allLevelParamsDefined] at hdef
    rw [denote2, denote2, ihe hdef]
  | case11 d n hsup =>
    intro _
    rw [denote2, if_pos hsup, denote2, if_pos hsup,
      (acval_natPair m hsup _ _).1, (acval_natPair m hsup _ _).2]
  | case12 d n hsup => intro _; rw [denote2, if_neg hsup, denote2,
      if_neg hsup]
  | case13 d s hsup =>
    intro _
    rw [denote2, if_pos hsup, denote2, if_pos hsup]
    have hg := hsup
    simp only [Setlec.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    rw [acval_scalar m stringOfListName stringOfListTyOk h2 rfl
        (by
          intro ci h
          simp only [stringOfListTyOk, Bool.and_eq_true] at h
          exact h.1) _ _,
      acval_scalar m charName charTyOk h6 rfl
        (by
          intro ci h
          simp only [charTyOk, Bool.and_eq_true] at h
          exact h.1) _ _,
      acval_scalar m charOfNatName charOfNatTyOk h7 rfl
        (by
          intro ci h
          simp only [charOfNatTyOk, Bool.and_eq_true] at h
          exact h.1) _ _,
      (acval_natPair m h0 _ _).1, (acval_natPair m h0 _ _).2,
      acval_one m listNilName listNilTyOk h4 rfl
        (by
          intro ci h
          simp only [listNilTyOk] at h
          split at h
          · next p hpe => simp [hpe]
          · exact nomatch h) _ _,
      acval_one m listConsName listConsTyOk h5 rfl
        (by
          intro ci h
          simp only [listConsTyOk] at h
          split at h
          · next p hpe => simp [hpe]
          · exact nomatch h) _ _]
  | case14 d s hsup => intro _; rw [denote2, if_neg hsup, denote2,
      if_neg hsup]
  | case15 d x hsrt hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denote2.eq_def, denote2.eq_def]
    | sort u => exact absurd rfl (hsrt u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b m => exact absurd rfl (hpi n ty b m)
    | lam n ty b m => exact absurd rfl (hlam n ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end Setlec.SetR.Interp2
