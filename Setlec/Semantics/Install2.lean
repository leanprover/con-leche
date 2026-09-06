import Setlec.Semantics.Canon
import Setlec.Semantics.Ok2
import Setlec.Verify.EnvGuards
import Setlec.Verify.Denote.Install

/-!
# The `acval` install algebra — the install tier's V-free half

*(Re-based to `Setlec/SetBase/*` at THE SEPARATION's S2, task #161.
The module's own title says it: this is the V-free half, and the one
theorem that does mention `V` (`acvalWith_ok2`) takes `AnnotOk2` as a
hypothesis and returns it — no `EnvS`, no `EnvS2`.  Its
`Annot/EnvS2` import was transitive cover for four base facts
(`natLitSupported_inv`, `strLitSupported_inv`, `cvalWith_{ne,self}`),
which it now takes directly.  Path and module name changed;
namespaces, statements and proofs verbatim.)*

The keys survey (task: the six install keys over `interp2`) found
that the `EnvS2` delta over `EnvS` is **six syntactic fields and
two semantic ones** (seven syntactic before the cleanup seal withdrew
`cval_annot`): `acval` (data), `acval_erase`, `acval_closed`,
`acval_params`, `acval_defn` and `acval_thm` mention no
`V` at all, while only `acval_ok2` and `mem_type2` do.  So the first
thing the install tier needs is not semantics — it is the *algebra*
of extending a canonical annotated valuation at one fresh name, and
the fact that extending it there moves nothing already denoted.

That is this file, and it is the exact mirror of what
`Setlec/Verify/Denote/Install.lean` provides on the v1 lane
(`cvalWith`, `cvalWith_ne`, `cvalWith_self`) — except for one lemma
v1 never needed:

**`denote2_acval_congr`.**  `denote` reads `cval` at *any* name;
`denote2` reads `acval` only where the environment stores something.
Every constant leaf sits behind `env.find? n = some ci`, and the two
literal spines sit behind `natLitSupported`/`strLitSupported`, whose
inversions produce the stored entries for all seven support names.
So a valuation change confined to a **fresh** name is invisible to
`denote2` on the old environment — which is what carries `acval_defn`,
`acval_thm` and `mem_type2` for the *already installed* constants
across a new declaration's install.

## What this file deliberately does **not** contain

There is no transport of `acval_defn`/`acval_thm` across the
environment *extension* itself.  On the v1 lane that step is free —
`denote` reads `env` only through `find?`, so a fresh `cons` cannot
change it.  Over `interp2` it is not: `denote2`'s binder clauses call
`sortOfE`/`lamSortE`, which run `inferTypeCore` and `whnf` **in
`env`**, and nothing in the tree says a checker run is stable when the
environment grows.  That is a named gap, not an omission — see the
survey's supplier requests.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name natLitSupported strLitSupported)

universe w

/-! ## The one-name update -/

/-- Extend a canonical annotated valuation at one name — the `acval`
mirror of `cvalWith`. -/
def acvalWith (acval : Name → (Name → Nat) → AVExpr) (n : Name)
    (A : (Name → Nat) → AVExpr) : Name → (Name → Nat) → AVExpr :=
  fun c ψ => if c = n then A ψ else acval c ψ

theorem acvalWith_ne {acval : Name → (Name → Nat) → AVExpr}
    {n : Name} {A : (Name → Nat) → AVExpr} {c : Name} (h : c ≠ n) :
    acvalWith acval n A c = acval c := by
  funext ψ; simp [acvalWith, h]

theorem acvalWith_self {acval : Name → (Name → Nat) → AVExpr}
    {n : Name} {A : (Name → Nat) → AVExpr} :
    acvalWith acval n A n = A := by
  funext ψ; simp [acvalWith]

/-! ## `denote2` reads only what the environment stores -/

/-- **The congruence.**  `denote2` consults its valuation only at
names the environment stores — every `.const` leaf behind its own
`find?`, the two literal spines behind their support guards.  So two
valuations agreeing on the stored names denote every term alike.

Stated as an equation rather than an implication: the two runs are
`none` together as well, which is what a *fresh* install needs (an
annotation may not exist, and the statement must not silently assume
one does). -/
theorem denote2_acval_congr {mode : CheckMode}
    {acval₁ acval₂ : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} {fuel : Nat}
    (hag : ∀ n, (env.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr),
      denote2 mode acval₁ env φ fuel d e
        = denote2 mode acval₂ env φ fuel d e := by
  intro d e
  induction d, e using denote2.induct (env := env) with
  | case1 d u => rw [denote2, denote2]
  | case2 d idx nm ty => rw [denote2, denote2]
  | case3 d n us ci hf hlen =>
    rw [denote2, denote2, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen, hag n (by rw [hf]; rfl)]
  | case4 d n us ci hf hlen =>
    rw [denote2, denote2, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => rw [denote2, denote2, hf]
  | case6 d n ty body m ihty ihbody =>
    rw [denote2, denote2, ihty, ihbody]
  | case7 d n ty body m ihty ihbody =>
    rw [denote2, denote2, ihty, ihbody]
  | case8 d f a ihf iha => rw [denote2, denote2, ihf, iha]
  | case9 d n ty val body ihty ihval ihbody =>
    rw [denote2, denote2, ihty, ihval, ihbody]
  | case10 d sn i e ihe => rw [denote2, denote2, ihe]
  | case11 d n hsup =>
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hS, -⟩ :=
      natLitSupported_inv hsup
    rw [denote2, denote2, if_pos hsup, if_pos hsup,
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hS]; rfl)]
  | case12 d n hsup =>
    rw [denote2, denote2, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
      hfS, hfO, hfL, hfN, hfC, hfH, hfF, -⟩ :=
      strLitSupported_inv hsup
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hSu, -⟩ :=
      natLitSupported_inv hnat
    rw [denote2, denote2, if_pos hsup, if_pos hsup,
      hag stringOfListName (by rw [hfO]; rfl),
      hag listNilName (by rw [hfN]; rfl),
      hag listConsName (by rw [hfC]; rfl),
      hag charName (by rw [hfH]; rfl),
      hag charOfNatName (by rw [hfF]; rfl),
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hSu]; rfl)]
  | case14 d s hsup =>
    rw [denote2, denote2, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i => rw [denote2.eq_def, denote2.eq_def]
    | sort u => exact absurd rfl (hs u)
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

/-- **The install corollary**: choosing the new declaration's
annotated leaf moves no denotation in the environment it was checked
in.  This is what carries the `EnvS2` fields of the *already
installed* constants past a fresh install. -/
theorem denote2_acvalWith_fresh {mode : CheckMode}
    {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} {fuel : Nat} {n : Name}
    {A : (Name → Nat) → AVExpr} (hfresh : env.find? n = none)
    (d : Nat) (e : Expr) :
    denote2 mode (acvalWith acval n A) env φ fuel d e
      = denote2 mode acval env φ fuel d e := by
  refine denote2_acval_congr (fun c hc => ?_) d e
  refine acvalWith_ne (fun h => ?_)
  rw [h, hfresh] at hc
  exact nomatch hc

/-! ## The three syntactic fields, transported

`acval_erase`, `acval_closed` and `acval_params` are conditions on an
install-fixed object with no `denote2` and no `interp2` in them (the
`EnvS2` docstrings say so of the last two).  Each therefore extends by
a case split on the updated name and nothing else. -/

/-- `acval_erase` extends: the new leaf's own erasure link is all the
install owes. -/
theorem acvalWith_erase {acval : Name → (Name → Nat) → AVExpr}
    {cval : TConstVal} {n : Name}
    {A : (Name → Nat) → AVExpr} {W : (Name → Nat) → VExpr}
    (h : ∀ (m : Name) (ψ : Name → Nat), (acval m ψ).erase = cval m ψ)
    (hA : ∀ ψ : Name → Nat, (A ψ).erase = W ψ) :
    ∀ (m : Name) (ψ : Name → Nat),
      (acvalWith acval n A m ψ).erase = cvalWith cval n W m ψ := by
  intro m ψ
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self, cvalWith_self]
    exact hA ψ
  · rw [acvalWith_ne hm, cvalWith_ne hm]
    exact h m ψ

/-- `acval_closed` extends. -/
theorem acvalWith_closed {acval : Name → (Name → Nat) → AVExpr}
    {n : Name} {A : (Name → Nat) → AVExpr}
    (h : ∀ (m : Name) (ψ : Name → Nat) (k : Nat),
      (acval m ψ).liftN 1 k = acval m ψ)
    (hA : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ) :
    ∀ (m : Name) (ψ : Name → Nat) (k : Nat),
      (acvalWith acval n A m ψ).liftN 1 k
        = acvalWith acval n A m ψ := by
  intro m ψ k
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ k
  · rw [acvalWith_ne hm]
    exact h m ψ k

/-- `acval_params` extends across a `cons`: the stored entries are the
old ones plus the installed one, and the new leaf answers for itself.

Note the environment moves here, unlike in the two above — the field
is indexed by `env.find?`.  Freshness is **not** needed: the `cons`
shadows, so the installed entry answers first either way. -/
theorem acvalWith_params {acval : Name → (Name → Nat) → AVExpr}
    {env : Env} {c₀ : Setlec.ConstantInfo}
    {A : (Name → Nat) → AVExpr}
    (h : ∀ (m : Name) (ci : Setlec.ConstantInfo),
      env.find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval m ψ₁ = acval m ψ₂)
    (hA : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂) :
    ∀ (m : Name) (ci : Setlec.ConstantInfo),
      (⟨c₀ :: env.consts⟩ : Env).find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acvalWith acval c₀.name A m ψ₁
          = acvalWith acval c₀.name A m ψ₂ := by
  intro m ci hf ψ₁ ψ₂ hp
  rw [Env.find?_cons] at hf
  by_cases hm : c₀.name = m
  · rw [if_pos hm] at hf
    obtain rfl := Option.some.inj hf
    subst hm
    rw [acvalWith_self]
    exact hA ψ₁ ψ₂ hp
  · rw [if_neg hm] at hf
    rw [acvalWith_ne (fun hh => hm hh.symm)]
    exact h m ci hf ψ₁ ψ₂ hp

/-! ## The one semantic field that extends for free

`acval_ok2` is one of the two `EnvS2` fields that mention `V` at all,
and it is the one that carries no environment index: it is a fact
about each leaf on its own.  So its extension asks the install for
exactly the new leaf's truthfulness and nothing more.

Its partner `mem_type2` does **not** extend here, and the reason is
worth the contrast: `mem_type2` conditions on a `denote2` run of the
constant's *type* **in the extended environment**, so its transport
needs the run-stability fact this file names as missing, not a case
split. -/

/-- `acval_ok2` extends. -/
theorem acvalWith_ok2 {V : Type w} [SetTheory V]
    {acval : Name → (Name → Nat) → AVExpr} {n : Name}
    {A : (Name → Nat) → AVExpr}
    (h : ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOk2 V ρ (acval m ψ))
    (hA : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ)) :
    ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOk2 V ρ (acvalWith acval n A m ψ) := by
  intro m ψ ρ
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ ρ
  · rw [acvalWith_ne hm]
    exact h m ψ ρ

end Setlec.SetR.Interp2
