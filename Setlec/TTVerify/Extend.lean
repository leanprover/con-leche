import Setlec.TTVerify.Denote
import Setlec.TTVerify.EnvTT

/-!
# Denotations survive environment extension

The transpose of the environment-transport machinery of
`Setlec/Model/Extend/*`, at the one lemma the bridge actually needs:
**a term that denotes in `env` denotes to the same `VExpr` in any
extension of `env`.**

Every install step needs it in the same place the set model does.  The
invariant `EnvTT.has_type` quantifies over the constants stored *so
far* and mentions `denote … env …`; installing one more constant
replaces `env` by `⟨c₀ :: env.consts⟩`, so the already-established
derivations have to be re-read against the larger environment.  Since
`denote` reads the environment only in the `.const` clause (for the
arity check and the stored level parameters) and in the two literal
guards, extension can only *add* denotations, never change one.

Note what does **not** appear: nothing about `AnnotOk`, and nothing
about interpretations agreeing pointwise on a set-theoretic universe.
The set-model side needs a family of transport lemmas because
`AnnotOk` and the `IndOk`/`RecRulesOk`/`CapsOk` clauses all mention
`interpExpr` and each has to be moved separately
(`Setlec/Model/Extend/Transport.lean` and its siblings); here the
single fact below is what the corresponding clauses will consume.
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

open Setlec.TT

/-- `env₂` extends `env₁`: every constant stored in `env₁` is stored in
`env₂`, unchanged.  (The checker's installs are cons-extensions with a
freshness check, so this always holds of them; stating it as a relation
keeps the lemma independent of *how* the extension arose, exactly as
`EnvModel`'s transports are.) -/
def EnvExtends (env₁ env₂ : Env) : Prop :=
  ∀ n ci, env₁.find? n = some ci → env₂.find? n = some ci

theorem EnvExtends.refl (env : Env) : EnvExtends env env := fun _ _ h => h

theorem EnvExtends.trans {e₁ e₂ e₃ : Env} (h₁ : EnvExtends e₁ e₂)
    (h₂ : EnvExtends e₂ e₃) : EnvExtends e₁ e₃ :=
  fun n ci h => h₂ n ci (h₁ n ci h)

/-- A cons-extension over a fresh name extends. -/
theorem EnvExtends.cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    EnvExtends env ⟨c₀ :: env.consts⟩ := by
  intro n ci h
  rw [Env.find?_cons]
  split
  · next hn =>
    rw [← hn, hfresh] at h
    exact nomatch h
  · exact h

/-- **Denotations survive extension.**

The literal guards and the stored level-parameter lists are hypotheses
rather than consequences, and the reason is worth stating so that the
next person does not take them for a gap.  They *are* consequences of
`hext`: a guard that held in `env₁` forced its slots to be stored
there, `hext` carries those lookups over unchanged, and the guard reads
nothing else.  That derivation is exactly
`natLitSupported_inv` + `natLitSupported_congr` (and the `strLit`
pair), which already exist — but in `Setlec/Model/Interp.lean`, which
this hierarchy does not import.

**Both are `V`-free**: they are facts about `Env` alone and have no
business in the set model's module.  Moving them to `Setlec/Verify/*`
is the right fix and would let these three hypotheses be discharged
here rather than passed on; it is not done in this commit only because
`Setlec/Model/Interp.lean` is heavily trafficked and the move is better
made on its own. -/
theorem denote_mono {cval : TConstVal} {env₁ env₂ : Env} {φ : Name → Nat}
    (hext : EnvExtends env₁ env₂)
    (hnat : natLitSupported env₁ = true → natLitSupported env₂ = true)
    (hstr : strLitSupported env₁ = true → strLitSupported env₂ = true)
    (hlp : ∀ n, levelParamsAt env₂ n = levelParamsAt env₁ n) :
    ∀ (d : Nat) (e : Expr) {v : VExpr},
      denote cval env₁ φ d e = some v → denote cval env₂ φ d e = some v := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env₁) (φ := φ) with
  | case1 d u => intro v h; rw [denote_sort] at h ⊢; exact h
  | case2 d idx nm ty => intro v h; rw [denote_fvar] at h ⊢; exact h
  | case3 d n us ci h1 h2 =>
    intro v h
    simp only [denote_const, h1, if_pos h2] at h
    simp only [denote_const, hext n ci h1, if_pos h2]
    exact h
  | case4 d n us ci h1 h2 =>
    intro v h
    simp only [denote_const, h1, if_neg h2] at h
    exact nomatch h
  | case5 d n us h1 =>
    intro v h
    rw [denote_const, h1] at h
    exact nomatch h
  | case6 d n ty body mb h1 ihty =>
    intro v h
    rw [denote_forallE, h1] at h
    exact nomatch h
  | case7 d n ty body mb B h1 h2 ihty ihbody =>
    intro v h
    rw [denote_forallE, h1, h2] at h
    exact nomatch h
  | case8 d n ty body mb B h1 B' h2 ihty ihbody =>
    intro v h
    rw [denote_forallE, h1, h2] at h
    rw [denote_forallE, ihty h1, ihbody h2]
    exact h
  | case9 d n ty body mb h1 ihty =>
    intro v h
    rw [denote_lam, h1] at h
    exact nomatch h
  | case10 d n ty body mb B h1 h2 ihty ihbody =>
    intro v h
    rw [denote_lam, h1, h2] at h
    exact nomatch h
  | case11 d n ty body mb B h1 B' h2 ihty ihbody =>
    intro v h
    rw [denote_lam, h1, h2] at h
    rw [denote_lam, ihty h1, ihbody h2]
    exact h
  | case12 d f a vf va h1 h2 ihf iha =>
    intro v h
    rw [denote_app, h1, h2] at h
    rw [denote_app, ihf h2, iha h1]
    exact h
  | case13 d f a hbad ihf iha =>
    intro v h
    rw [denote_app] at h
    split at h
    · next vf va h1 h2 => exact (hbad vf va h1 h2).elim
    · exact nomatch h
  | case14 d n ty val body vf va h1 h2 h3 ihty ihval ihbody =>
    intro v h
    simp only [denote_letE, h1, h2, h3] at h
    exact nomatch h
  | case15 d n ty val body vf va h1 h2 B h3 ihty ihval ihbody =>
    intro v h
    simp only [denote_letE, h1, h2, h3] at h
    simp only [denote_letE, ihty h2, ihval h1, ihbody h3]
    exact h
  | case16 d n ty val body hbad ihty ihval =>
    intro v h
    rw [denote_letE] at h
    split at h
    · next vf va h1 h2 => exact (hbad vf va h1 h2).elim
    · exact nomatch h
  | case17 d sn i e h1 ihe =>
    intro v h
    rw [denote_proj, h1] at h
    exact nomatch h
  | case18 d sn i e B h1 h2 ihe =>
    intro v h
    rw [denote_proj] at h ⊢
    rw [h1] at h
    rw [ihe h1]
    exact h
  | case19 d sn i e B h1 h2 ihe =>
    intro v h
    simp only [denote_proj, h1, if_neg h2] at h
    exact nomatch h
  | case20 d n hg =>
    intro v h
    rw [denote_natLit, if_pos hg] at h
    rw [denote_natLit, if_pos (hnat hg)]
    exact h
  | case21 d n hg =>
    intro v h
    rw [denote_natLit, if_neg hg] at h
    exact nomatch h
  | case22 d s hg =>
    intro v h
    rw [denote_strLit, if_pos hg] at h
    rw [denote_strLit, if_pos (hstr hg), strLitT, hlp listNilName, hlp listConsName]
    exact h
  | case23 d s hg =>
    intro v h
    rw [denote_strLit, if_neg hg] at h
    exact nomatch h
  | case24 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro v h
    match x with
    | .bvar i => rw [denote_bvar] at h; exact nomatch h
    | .sort u => exact (k1 u rfl).elim
    | .fvar a b c => exact (k2 a b c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE a b c dd => exact (k4 a b c dd rfl).elim
    | .lam a b c dd => exact (k5 a b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE a b c dd => exact (k7 a b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-! ## Changing the valuation at a fresh name

**Read this together with `denote_mono` above: they are two halves of
one fact**, and a reader meeting either alone would not see it —

> *Installing a fresh constant disturbs no existing denotation.*

`denote_mono` moves a denotation to a **larger environment**;
`denote_cval_congr` moves it to a **changed valuation**.  An install
does both at once, so every case of `CheckDeclTT` uses both, and
neither alone says anything reassuring.

The companion to `denote_mono`, and the other half of what every
install case needs.  `denote_mono` moves a denotation to a **larger
environment**; this moves it to a **changed valuation** — which is what
happens when a declaration installs, since the new constant's value has
to be added to `cval`.

Together they say the obvious thing precisely: *installing a fresh
constant disturbs no existing denotation.*  The freshness is what makes
the hypothesis dischargeable — an old term's constants all resolve in
the old environment, and the new name is not among them.

The literal-support agreements are named **one by one** — the seven
names `natLitT` and `strLitT` actually read — rather than as a blanket
"the valuations agree".  A blanket hypothesis would make the lemma
*trivially true and useless*.

**The failure mode, and how it relates to the ease-of-proof signal of
`Setlec/TTVerify/DESIGN.md` §0.**  A statement can typecheck, prove,
and be worth nothing because a hypothesis subsumes its conclusion — and
unlike a *wrong* statement it leaves no trace, since everything
downstream still compiles.  §0 says a proof going through without
adaptation is evidence the statement has the right shape.  Both are
true, and they are **ordered, not in tension**:

> **First check the hypotheses are weaker than the conclusion; then
> take ease of proof as evidence.**  Ease is confirmation of a
> statement already established to be non-vacuous, never a substitute
> for establishing it.

So a suspiciously easy proof is not a reason to distrust the ease — it
is a reason to go and read the hypotheses.  **The tell to look for is a
hypothesis quantified more broadly than the conclusion needs**: here,
"the valuations agree *everywhere*" where exactly seven names are read.
Listing the seven is the fix.

They are hypotheses for the same reason they are in `denote_mono`: deriving them from the guards needs
`natLitSupported_inv`, a `V`-free fact stranded in
`Setlec/Model/Interp.lean` (the fifth such; see `EnvTT.lean`'s
relocation note).  Install sites discharge them from freshness. -/

/-- Denotation reads the valuation only at names the environment
resolves, so valuations agreeing there give equal denotations. -/
theorem denote_cval_congr {cval₁ cval₂ : TConstVal} {env : Env}
    {φ : Name → Nat}
    (hag : ∀ n ci, env.find? n = some ci → cval₁ n = cval₂ n)
    (hnat : cval₁ natZeroName = cval₂ natZeroName)
    (hsucc : cval₁ natSuccName = cval₂ natSuccName)
    (hsol : cval₁ stringOfListName = cval₂ stringOfListName)
    (hnil : cval₁ listNilName = cval₂ listNilName)
    (hcons : cval₁ listConsName = cval₂ listConsName)
    (hchar : cval₁ charName = cval₂ charName)
    (hofn : cval₁ charOfNatName = cval₂ charOfNatName) :
    ∀ (d : Nat) (e : Expr),
      denote cval₁ env φ d e = denote cval₂ env φ d e := by
  intro d e
  induction d, e using denote.induct (cval := cval₁) (env := env) (φ := φ) with
  | case1 d u => simp only [denote_sort]
  | case2 d idx nm ty => simp only [denote_fvar]
  | case3 d n us ci h1 h2 =>
    simp only [denote_const, h1, if_pos h2, hag n ci h1]
  | case4 d n us ci h1 h2 => simp only [denote_const, h1, if_neg h2]
  | case5 d n us h1 => simp only [denote_const, h1]
  | case6 d n ty body mb h1 ihty =>
    simp only [denote_forallE, h1, ← ihty]
  | case7 d n ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_forallE, h1, h2, ← ihty, ← ihbody]
  | case8 d n ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_forallE, h1, h2, ← ihty, ← ihbody]
  | case9 d n ty body mb h1 ihty => simp only [denote_lam, h1, ← ihty]
  | case10 d n ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_lam, h1, h2, ← ihty, ← ihbody]
  | case11 d n ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_lam, h1, h2, ← ihty, ← ihbody]
  | case12 d f a vf va h1 h2 ihf iha =>
    simp only [denote_app, h1, h2, ← ihf, ← iha]
  | case13 d f a hbad ihf iha => simp only [denote_app, ← ihf, ← iha]
  | case14 d n ty val body vf va h1 h2 h3 ihty ihval ihbody =>
    simp only [denote_letE, h1, h2, h3, ← ihty, ← ihval, ← ihbody]
  | case15 d n ty val body vf va h1 h2 B h3 ihty ihval ihbody =>
    simp only [denote_letE, h1, h2, h3, ← ihty, ← ihval, ← ihbody]
  | case16 d n ty val body hbad ihty ihval =>
    simp only [denote_letE, ← ihty, ← ihval]
  | case17 d sn i e h1 ihe => simp only [denote_proj, h1, ← ihe]
  | case18 d sn i e B h1 h2 ihe => simp only [denote_proj, h1, ← ihe]
  | case19 d sn i e B h1 h2 ihe => simp only [denote_proj, h1, ← ihe]
  | case20 d n hg => simp only [denote_natLit, hnat, hsucc]
  | case21 d n hg => simp only [denote_natLit, hnat, hsucc]
  | case22 d s hg =>
    simp only [denote_strLit, strLitT, hnat, hsucc, hsol, hnil, hcons,
      hchar, hofn]
  | case23 d s hg =>
    simp only [denote_strLit, strLitT, hnat, hsucc, hsol, hnil, hcons,
      hchar, hofn]
  | case24 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    match x with
    | .bvar i => simp only [denote_bvar]
    | .sort u => exact (k1 u rfl).elim
    | .fvar a b c => exact (k2 a b c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE a b c dd => exact (k4 a b c dd rfl).elim
    | .lam a b c dd => exact (k5 a b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE a b c dd => exact (k7 a b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-! ## The install transport

What every case of `CheckDeclTT` does to the *old* constants: they must
still denote, and still be derivably of their types, in the extended
environment under the extended valuation.  Both transport lemmas above
fire here, which is the point of naming them a pair.

The valuation hypothesis is stated as "agrees away from the new name"
rather than "agrees where the environment resolves", because that form
is **discharged by freshness alone** — `List.find?_eq_none` turns
`hfresh` into name-distinctness for every stored constant, with no
appeal to well-formedness. -/

/-- Old constants keep their derivations across a fresh install.

The seven literal-support agreements are separate hypotheses rather
than consequences of `hag`, and the reason is a real case rather than
caution: during a **basis install** the new constant *is* one of those
names, so `n ≠ c₀.name` does not hold for them.  An ordinary install
discharges all seven from `hag` immediately; the basis install owes
them, which is correct — it is the one changing those valuations. -/
theorem has_type_cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → m.cval n = cval' n)
    (hnat : m.cval natZeroName = cval' natZeroName)
    (hsucc : m.cval natSuccName = cval' natSuccName)
    (hsol : m.cval stringOfListName = cval' stringOfListName)
    (hnil : m.cval listNilName = cval' listNilName)
    (hcons : m.cval listConsName = cval' listConsName)
    (hchar : m.cval charName = cval' charName)
    (hofn : m.cval charOfNatName = cval' charOfNatName)
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlp : ∀ n, levelParamsAt ⟨c₀ :: env.consts⟩ n = levelParamsAt env n) :
    ∀ c ∈ env.consts, ∀ φ : Name → Nat,
      ∃ t, denoteClosed cval' ⟨c₀ :: env.consts⟩ φ c.toConstantVal.type
          = some t ∧ HasType [] (cval' c.name φ) t := by
  -- freshness gives name-distinctness for every stored constant, with
  -- no appeal to well-formedness
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  have hagE : ∀ n ci, env.find? n = some ci → m.cval n = cval' n := by
    intro n ci hfind
    refine hag n ?_
    intro h
    rw [h, hfresh] at hfind
    exact nomatch hfind
  intro c hc φ
  obtain ⟨t, ht, hd⟩ := m.has_type c hc φ
  refine ⟨t, ?_, ?_⟩
  · rw [denoteClosed] at ht ⊢
    rw [denote_cval_congr hagE hnat hsucc hsol hnil hcons hchar hofn 0 _] at ht
    exact denote_mono (EnvExtends.cons hfresh) hguardN hguardS hlp 0 _ ht
  · rw [← hag c.name (hne c hc)]
    exact hd

end Setlec.TTVerify
