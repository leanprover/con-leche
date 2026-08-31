import Setlec.SetR.Decl
import Setlec.SetR.Interp2.Step2.Levels
import Setlec.Verify.LevelPres

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
open Setlec (CheckMode Env Expr Name Level ConstantVal)

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
      hac n _ _ (Level.substFn_agree hφ
        (ks := ci.toConstantVal.levelParams)
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

/-! ## First finding: all three statements are **false as frozen**

The statements quantify over a bare `Env`, and nothing in them says
the environment is well formed.  One axiom whose *stored type* mentions
a level parameter outside its (empty) `levelParams` refutes all three:
`inferBody`'s `.const` clause hands the stored type back verbatim (the
level list is empty, so its own instantiation is the identity), the
sort is terminal for `whnf`, and `sortOfE` therefore reports the
assignment's value at a parameter the subject never had.

This is **the same escape** `Step2/LevelsInst.lean` already recorded
for `InferInstLevels`/`WhnfSortInstLevels`/`SortOfEInstLevels` (its
`escEnvT`), one seal earlier and in the same lane; the missing
hypothesis is `EnvWF`, and — as recorded there — the consumers hold it
(`EnvS.wf`), so the repair costs them nothing.  The witness is rebuilt
here rather than imported because that file's is `private`. -/

/-- The escaping parameter. -/
private def llP : Name := .str .anonymous "llP"

/-- The stored constant. -/
private def llC : Name := .str .anonymous "llC"

/-- One axiom whose stored type mentions a parameter it does not
declare.  `ConstWF` forbids it; the frozen statements do not. -/
def llEnv : Env := ⟨[.axiomInfo ⟨llC, [], .sort (.param llP)⟩]⟩

private theorem llEnv_infer (μ : CheckMode) (F d : Nat) :
    Setlec.inferTypeCore μ llEnv (F + 1) d (.const llC [])
      = .ok (.sort (.param llP)) := rfl

private theorem llEnv_defined (ps : List Name) :
    (Expr.const llC []).allLevelParamsDefined ps = true := rfl

/-- The run reads the assignment at the escaping parameter. -/
private theorem llEnv_sortOfE (μ : CheckMode) (ψ : Name → Nat)
    (F d : Nat) :
    sortOfE μ llEnv ψ (F + 3) d (.const llC []) = some (ψ llP) := by
  unfold sortOfE
  rw [show Setlec.inferTypeCore μ llEnv (F + 3) d (.const llC [])
      = .ok (.sort (.param llP)) from llEnv_infer μ (F + 2) d]
  simp only [Except.toOption]
  rw [show Setlec.whnf μ llEnv (F + 3) d (.sort (.param llP))
      = .ok (.sort (.param llP))
      from Setlec.whnf_sort llEnv (F + 1) d _]
  rfl

/-- …and one inference earlier, for the λ clause's numeral. -/
private theorem llEnv_lamSortE (μ : CheckMode) (ψ : Name → Nat)
    (F d : Nat) :
    lamSortE μ llEnv ψ (F + 4) d (.const llC [])
      = some (ψ llP + 1) := by
  unfold lamSortE
  rw [show Setlec.inferTypeCore μ llEnv (F + 4) d (.const llC [])
      = .ok (.sort (.param llP)) from llEnv_infer μ (F + 3) d]
  simp only [Except.toOption]
  unfold sortOfE
  rw [show Setlec.inferTypeCore μ llEnv (F + 4) d (.sort (.param llP))
      = .ok (.sort (.succ (.param llP))) from rfl]
  simp only [Except.toOption]
  rw [show Setlec.whnf μ llEnv (F + 4) d (.sort (.succ (.param llP)))
      = .ok (.sort (.succ (.param llP)))
      from Setlec.whnf_sort llEnv (F + 2) d _]
  rfl

/-- **`SortOfELevelLocal` is false as stated.** -/
theorem not_sortOfELevelLocal (μ : CheckMode) :
    ¬ SortOfELevelLocal μ llEnv := by
  intro h
  have hx := h [] (fun _ => 0) (fun _ => 1) 3 0 (.const llC [])
    (llEnv_defined []) (fun p hp => absurd hp (by simp))
  rw [llEnv_sortOfE μ (fun _ => 0) 0 0,
    llEnv_sortOfE μ (fun _ => 1) 0 0] at hx
  exact nomatch hx

/-- **`LamSortELevelLocal` is false as stated**, at the same
environment. -/
theorem not_lamSortELevelLocal (μ : CheckMode) :
    ¬ LamSortELevelLocal μ llEnv := by
  intro h
  have hx := h [] (fun _ => 0) (fun _ => 1) 4 0 (.const llC [])
    (llEnv_defined []) (fun p hp => absurd hp (by simp))
  rw [llEnv_lamSortE μ (fun _ => 0) 0 0,
    llEnv_lamSortE μ (fun _ => 1) 0 0] at hx
  exact nomatch hx

private theorem llEnv_sortZero (μ : CheckMode) (ψ : Name → Nat)
    (F d : Nat) :
    sortOfE μ llEnv ψ (F + 3) d (.sort .zero) = some 1 := by
  unfold sortOfE
  rw [show Setlec.inferTypeCore μ llEnv (F + 3) d (.sort .zero)
      = .ok (.sort (.succ .zero)) from rfl]
  simp only [Except.toOption]
  rw [show Setlec.whnf μ llEnv (F + 3) d (.sort (.succ .zero))
      = .ok (.sort (.succ .zero))
      from Setlec.whnf_sort llEnv (F + 1) d _]
  rfl

/-- The `∀` node's annotation, computed: every slot but the domain's
numeral is assignment-independent. -/
private theorem llEnv_denote2 (μ : CheckMode) (ψ : Name → Nat) :
    denote2 μ (fun _ _ => AVExpr.sort 0) llEnv ψ 3 0
        (.forallE llC (.const llC []) (.sort .zero) ⟨.default⟩)
      = some (.pi (ψ llP) 1 (.sort 0) (.sort 0)) := by
  rw [denote2]
  simp only [Expr.instantiate1, Nat.zero_add]
  rw [show denote2 μ (fun _ _ => AVExpr.sort 0) llEnv ψ 3 0
        (.const llC []) = some (.sort 0) from by rw [denote2]; rfl,
    show denote2 μ (fun _ _ => AVExpr.sort 0) llEnv ψ 3 1
        (.sort .zero) = some (.sort 0) from by rw [denote2]; rfl,
    llEnv_sortOfE μ ψ 0 0, llEnv_sortZero μ ψ 0 1]
  rfl

/-- **`Denote2LevelLocal` is false as stated too** — the escape reaches
the numeral, not merely the primitive.  The subject is a `∀` whose
*domain* is the escaping constant and whose body is a literal sort, so
every other slot of the clause is assignment-independent and the
valuation hypothesis holds of a constant valuation. -/
theorem not_denote2LevelLocal (μ : CheckMode) :
    ¬ Denote2LevelLocal μ llEnv (fun _ _ => .sort 0) := by
  intro h
  have hx := h [] (fun _ => 0) (fun _ => 1) 3 0
    (.forallE llC (.const llC []) (.sort .zero) ⟨.default⟩)
    (by simp [Expr.allLevelParamsDefined, Level.allParamsDefined])
    (fun p hp => absurd hp (by simp))
    (fun _ _ _ _ => rfl)
  rw [llEnv_denote2 μ (fun _ => 0), llEnv_denote2 μ (fun _ => 1)] at hx
  exact nomatch hx

/-! ## The two primitives, factored to the checker

`sortOfE` and `lamSortE` take the level assignment **nowhere except
the final `Level.eval`**: `inferTypeCore` and `whnf` do not mention
`φ` at all.  So the two statements above are not about two runs — they
are about *one* run and the level it returns, and what they need is:

> inference and head normalisation introduce no level parameter the
> subject does not already have.

That is the pair below, and it is the level-side twin of
`Step2/Levels.lean`'s `InferInstLevels`/`WhnfSortInstLevels`
factoring.  Everything else is `Level.eval_ext`. -/

/-- Inference keeps the level parameters within the subject's. -/
def InferLevelParams (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ps : List Name) (F d : Nat) (e t : Expr),
    e.allLevelParamsDefined ps = true →
    Setlec.inferTypeCore μ env F d e = .ok t →
    t.allLevelParamsDefined ps = true

/-- Head normalisation keeps the level parameters within the
subject's. -/
def WhnfLevelParams (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ps : List Name) (F d : Nat) (e t : Expr),
    e.allLevelParamsDefined ps = true →
    Setlec.whnf μ env F d e = .ok t →
    t.allLevelParamsDefined ps = true

/-- **Statement 1 from the pair.** -/
theorem sortOfELevelLocal_of {μ : CheckMode} {env : Env}
    (hi : InferLevelParams μ env) (hw : WhnfLevelParams μ env) :
    SortOfELevelLocal μ env := by
  intro ps φ₁ φ₂ F d e hdef hφ
  unfold sortOfE
  cases hit : Setlec.inferTypeCore μ env F d e with
  | error err => rfl
  | ok t =>
    simp only [Except.toOption]
    cases hwt : Setlec.whnf μ env F d t with
    | error err => rfl
    | ok w =>
      have hLw := hw ps F d t w (hi ps F d e t hdef hit) hwt
      cases w with
      | sort ℓ =>
        simp only []
        rw [Level.eval_ext
          (by simpa [Expr.allLevelParamsDefined] using hLw) hφ]
      | bvar i => rfl
      | fvar i n ty => rfl
      | const n us => rfl
      | app f a => rfl
      | lam n ty b m => rfl
      | forallE n ty b m => rfl
      | letE n ty v b => rfl
      | proj s i x => rfl
      | lit l => rfl

/-- **Statement 2 from statement 1**, one inference earlier. -/
theorem lamSortELevelLocal_of {μ : CheckMode} {env : Env}
    (hi : InferLevelParams μ env) (hs : SortOfELevelLocal μ env) :
    LamSortELevelLocal μ env := by
  intro ps φ₁ φ₂ F d b hdef hφ
  unfold lamSortE
  cases hit : Setlec.inferTypeCore μ env F d b with
  | error err => rfl
  | ok bt =>
    simp only [Except.toOption]
    exact hs ps φ₁ φ₂ F d bt (hi ps F d b bt hdef hit) hφ

/-! ## The repair, and the chain re-derived through it

The missing hypothesis is `EnvWF`, and — exactly as
`Step2/LevelsInst.lean` records for its own escape — **the consumers
already hold it**: `EnvS2UM.base.wf`.  So the `…W` forms below cost
them nothing, and the whole chain from the two checker primitives to
both `params` fields closes through them. -/

/-- Primitive 1, repaired. -/
def InferLevelParamsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → InferLevelParams μ env

/-- Primitive 2, repaired. -/
def WhnfLevelParamsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → WhnfLevelParams μ env

/-- Statement 1, repaired. -/
def SortOfELevelLocalW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → SortOfELevelLocal μ env

/-- Statement 2, repaired. -/
def LamSortELevelLocalW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → LamSortELevelLocal μ env

theorem sortOfELevelLocalW_of {μ : CheckMode} {env : Env}
    (hi : InferLevelParamsW μ env) (hw : WhnfLevelParamsW μ env) :
    SortOfELevelLocalW μ env :=
  fun hwf => sortOfELevelLocal_of (hi hwf) (hw hwf)

theorem lamSortELevelLocalW_of {μ : CheckMode} {env : Env}
    (hi : InferLevelParamsW μ env) (hs : SortOfELevelLocalW μ env) :
    LamSortELevelLocalW μ env :=
  fun hwf => lamSortELevelLocal_of (hi hwf) (hs hwf)

/-- **The consumer form, through the repair.**  `EnvWF` is spent from
the invariant's own field, so the M statement is unconditional again
once the two primitives are. -/
theorem denote2LevelLocalMW_of {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvS2UM V μ env)
    (hs : SortOfELevelLocalW μ env) (hl : LamSortELevelLocalW μ env) :
    Denote2LevelLocalM V μ m :=
  denote2LevelLocalM_of m (hs m.base.wf) (hl m.base.wf)

/-! ## Second finding: the one clause that was open — and is now closed

`Setlec/Verify/LevelPres.lean` runs the two inductions.  Every site
that could introduce a level parameter instantiates a *stored*
expression at a `.const` node's level arguments, `EnvWF` bounds the
stored expression's parameters by its declaration's own, and
`Level.subst` keeps them inside the subject's **provided the two lists
have the same length** — a ragged substitution really does lose them
(`Level.subst.go` falls through to `.param n`).

Three of the four sites always checked that length themselves:
`unfoldDefinition` (the delta step), `inferBody`'s `.const` clause,
and `inferBody`'s `.proj` clause.  **`iotaRec` did not**: its guards
were the spine length, the rule lookup, `Level.isEquivList` on the
*constructor's* levels, the two `iotaCerts` and the index comparison —
none of which relates the recursor's `us` to its `cv.levelParams`.  So
the reduct `r.rhs.instantiateLevelParams cv.levelParams us` could
carry a parameter out of a short `us`, and
`Setlec/SetR/Interp2/IotaArity.lean` built the environment that did:
three constants, `EnvWF` discharged, `T.rec.{0} T.mk T.mk T.mk` firing
at `us.length = 1 < 2 = cv.levelParams.length` and leaking `.param w`.
That refuted `IotaLevelParamsW` **as stated**, so the residue could not
be proved away — the fix had to be in the checker.

**It was.**  Checker change #9 adds `us.length = cv.levelParams.length`
to `iotaRec`'s guard (`Setlec/Kernel/Core.lean`, with the `iotaRecI`
and `iotaRecNC` twins), the spelling `unfoldDefinition` already used at
the delta step, and the one the official C++ kernel
(`src/kernel/inductive.h:105`), lean4lean
(`Lean4Lean/Inductive/Reduce.lean:98`) and nanoda all carry.  The arity
is now handed to `iotaRec_inv` directly, `iotaRec_lvlParams` needs no
side hypothesis, and `Setlec/Verify/LevelPres.lean` ties the knot
(`iotaRec_lvlParamsW`): reduction and inference at fuel `F` use the
iota fact only strictly below `F`, so one induction on a bound closes
the cycle.  `IotaArity.lean` keeps the environment as a regression
test (`iota_blocked`).

So `IotaLevelParamsW` below is a **theorem** (`iotaLevelParamsW`), and
every consumer that used to take it as a hypothesis now stands alone.
The `EnvWF` premise is not removable: `IotaLevelParams` at an arbitrary
environment is still out of reach, because the bound on a rule's `rhs`
parameters is exactly `ConstWF`'s. -/

/-- Iota keeps the level parameters within the subject's. -/
def IotaLevelParams (μ : CheckMode) (env : Env) : Prop :=
  ∀ (ps : List Name) (F d : Nat) (e t : Expr),
    e.allLevelParamsDefined ps = true →
    Setlec.iotaRecP μ env F d e = .ok (some t) →
    t.allLevelParamsDefined ps = true

/-- The same, premised on the invariant's own `EnvWF`. -/
def IotaLevelParamsW (μ : CheckMode) (env : Env) : Prop :=
  Setlec.EnvWF env → IotaLevelParams μ env

/-- **The residue, discharged** — what checker change #9 bought. -/
theorem iotaLevelParamsW {μ : CheckMode} {env : Env} :
    IotaLevelParamsW μ env :=
  fun hwf _ps F d e t hp h =>
    Setlec.iotaRec_lvlParamsW hwf F d e t hp h

/-- **Primitive 1, discharged.** -/
theorem inferLevelParamsW_of {μ : CheckMode} {env : Env} :
    InferLevelParamsW μ env := by
  intro hwf ps F d e t hp h
  exact Setlec.inferTypeCore_lvlParamsW hwf F h hp

/-- **Primitive 2, discharged.** -/
theorem whnfLevelParamsW_of {μ : CheckMode} {env : Env} :
    WhnfLevelParamsW μ env := by
  intro hwf ps F d e t hp h
  exact Setlec.whnf_lvlParamsW hwf F h hp

/-- **Statement 1, discharged.** -/
theorem sortOfELevelLocalW_of_iota {μ : CheckMode} {env : Env} :
    SortOfELevelLocalW μ env :=
  sortOfELevelLocalW_of inferLevelParamsW_of whnfLevelParamsW_of

/-- **Statement 2, discharged.** -/
theorem lamSortELevelLocalW_of_iota {μ : CheckMode} {env : Env} :
    LamSortELevelLocalW μ env :=
  lamSortELevelLocalW_of inferLevelParamsW_of
    sortOfELevelLocalW_of_iota

/-- **Statement 3, discharged**, at the form the consumers hold. -/
theorem denote2LevelLocalM_of_iota {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvS2UM V μ env) :
    Denote2LevelLocalM V μ m :=
  denote2LevelLocalMW_of m sortOfELevelLocalW_of_iota
    lamSortELevelLocalW_of_iota

/-! ## The two `params` consumers, discharged from the M form

Both fields have the same shape — a leaf `A` obtained as a `denote2`
run on the *annotated* subject, and the demand that it read only the
constant's own parameters — and both front doors carry the subject's
`allLevelParamsDefined` as a conjunct (`ConstantValR`,
`ValueFrontR`, `Setlec/SetR/Decl.lean`).  So one lemma serves
`ValueResidues2M.params`, `AxiomResidues2M.params` and
`AxiomResidues3M.params`.

The only non-syntactic move is the fuel: the leaf is named at *some*
fuel per assignment, and level-locality is an equation at *one*, so the
two runs are lifted to their maximum by `denote2_fuelMono` — which
returns the same `AVExpr`, so nothing is lost. -/

/-- **The `params` field, supplied.**  `A` is level-local because the
run that names it is. -/
theorem params_of_levelLocalM {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} {m : EnvS2UM V μ env}
    (hll : Denote2LevelLocalM V μ m) {ps : List Name} {e : Expr}
    {A : (Name → Nat) → AVExpr}
    (hdef : e.allLevelParamsDefined ps = true)
    (hA : ∀ ψ : Name → Nat, ∃ F : Nat,
      denote2 μ m.acval env ψ F 0 e = some (A ψ)) :
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ps, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ := by
  intro ψ₁ ψ₂ hψ
  obtain ⟨F₁, h₁⟩ := hA ψ₁
  obtain ⟨F₂, h₂⟩ := hA ψ₂
  have k₁ := denote2_fuelMono (Nat.le_max_left F₁ F₂) 0 e h₁
  have k₂ := denote2_fuelMono (Nat.le_max_right F₁ F₂) 0 e h₂
  rw [hll ps ψ₁ ψ₂ (max F₁ F₂) 0 e hdef hψ, k₂] at k₁
  exact (Option.some.inj k₁).symm

/-- **`ValueResidues2M.params`**, at the value front door's own
level-parameter conjunct. -/
theorem valueParams_of_levelLocalM {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} {m : EnvS2UM V μ env}
    (hll : Denote2LevelLocalM V μ m) {F : Nat} {cv : ConstantVal}
    {value type' value' : Expr} {A : (Name → Nat) → AVExpr}
    (hvf : ValueFrontR μ F env m.base.cval cv value type' value')
    (hA : ∀ ψ : Name → Nat, ∃ F' : Nat,
      denote2 μ m.acval env ψ F' 0 value' = some (A ψ)) :
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ :=
  params_of_levelLocalM hll hvf.2.2.2.1 hA

/-- **`AxiomResidues2M.params`/`AxiomResidues3M.params`**, at the
constant front door's own level-parameter conjunct.  The axiom's leaf
is the run on the *annotated type*, so this is the same lemma one
front door over. -/
theorem axiomParams_of_levelLocalM {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} {m : EnvS2UM V μ env}
    (hll : Denote2LevelLocalM V μ m) {F : Nat} {cv : ConstantVal}
    {type' : Expr} {A : (Name → Nat) → AVExpr}
    (hcv : ConstantValR μ F env m.base.cval cv type')
    (hA : ∀ ψ : Name → Nat, ∃ F' : Nat,
      denote2 μ m.acval env ψ F' 0 type' = some (A ψ)) :
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ :=
  params_of_levelLocalM hll hcv.2.2.2.2.2.2.2.1 hA

/-! ## The whole chain, end to end

Both fields, from the invariant's own `EnvWF` and nothing else: no
residue, no fuel bound, no environment shape, no mode condition, and no
valuation law beyond `acval_params`.  The `hio` hypothesis these two
carried until checker change #9 is gone — it is `iotaLevelParamsW`
now, and the chain supplies it internally. -/

/-- **`ValueResidues2M.params`, outright.** -/
theorem valueParams_of_iota {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvS2UM V μ env)
    {F : Nat} {cv : ConstantVal}
    {value type' value' : Expr} {A : (Name → Nat) → AVExpr}
    (hvf : ValueFrontR μ F env m.base.cval cv value type' value')
    (hA : ∀ ψ : Name → Nat, ∃ F' : Nat,
      denote2 μ m.acval env ψ F' 0 value' = some (A ψ)) :
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ :=
  valueParams_of_levelLocalM (denote2LevelLocalM_of_iota m) hvf hA

/-- **`AxiomResidues2M.params`/`AxiomResidues3M.params`,
outright.** -/
theorem axiomParams_of_iota {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvS2UM V μ env)
    {F : Nat} {cv : ConstantVal}
    {type' : Expr} {A : (Name → Nat) → AVExpr}
    (hcv : ConstantValR μ F env m.base.cval cv type')
    (hA : ∀ ψ : Name → Nat, ∃ F' : Nat,
      denote2 μ m.acval env ψ F' 0 type' = some (A ψ)) :
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ :=
  axiomParams_of_levelLocalM (denote2LevelLocalM_of_iota m) hcv hA

end Setlec.SetR.Interp2
