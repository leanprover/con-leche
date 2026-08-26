import Setlec.TTVerify.Denote
import Setlec.TTVerify.EnvTT
import Setlec.Verify.EnvWF
import Setlec.Verify.InferLemmas

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
    (hlpNil : levelParamsAt env₂ listNilName = levelParamsAt env₁ listNilName)
    (hlpCons : levelParamsAt env₂ listConsName = levelParamsAt env₁ listConsName) :
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
    rw [denote_strLit, if_pos (hstr hg), strLitT, hlpNil, hlpCons]
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

They are hypotheses for the same reason they are in `denote_mono`:
deriving them from the guards needs
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
    (hlpNil : levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
      = levelParamsAt env listNilName)
    (hlpCons : levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
      = levelParamsAt env listConsName) :
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
    exact denote_mono (EnvExtends.cons hfresh) hguardN hguardS hlpNil hlpCons 0 _ ht
  · rw [← hag c.name (hne c hc)]
    exact hd

/-! ## The literal guards under a fresh install

Both guards read the environment only at fixed names, so an install
under a *different* name leaves them alone.  Proving the congruence
directly avoids needing `natLitSupported_inv`
(`Setlec/Model/Interp.lean`) at all — a fact the bridge would otherwise
have to restate, and the fifth stranded one.  **The inversion is only
needed to derive the guard from its consequences; the congruence needs
just the lookups**, which is a cheaper thing to want. -/

/-- The `Nat`-literal guard reads three slots. -/
theorem natLitSupported_cons_of_ne {env : Env} {c₀ : ConstantInfo}
    (h1 : c₀.name ≠ natName) (h2 : c₀.name ≠ natZeroName)
    (h3 : c₀.name ≠ natSuccName) :
    natLitSupported ⟨c₀ :: env.consts⟩ = natLitSupported env := by
  unfold natLitSupported
  rw [Env.find?_cons, Env.find?_cons, Env.find?_cons,
    if_neg h1, if_neg h2, if_neg h3]

/-- The `String`-literal guard reads the `Nat` slots and seven more. -/
theorem strLitSupported_cons_of_ne {env : Env} {c₀ : ConstantInfo}
    (h1 : c₀.name ≠ natName) (h2 : c₀.name ≠ natZeroName)
    (h3 : c₀.name ≠ natSuccName) (h4 : c₀.name ≠ stringName)
    (h5 : c₀.name ≠ stringOfListName) (h6 : c₀.name ≠ listName)
    (h7 : c₀.name ≠ listNilName) (h8 : c₀.name ≠ listConsName)
    (h9 : c₀.name ≠ charName) (h10 : c₀.name ≠ charOfNatName) :
    strLitSupported ⟨c₀ :: env.consts⟩ = strLitSupported env := by
  unfold strLitSupported
  rw [natLitSupported_cons_of_ne h1 h2 h3]
  rw [Env.find?_cons, Env.find?_cons, Env.find?_cons, Env.find?_cons,
    Env.find?_cons, Env.find?_cons, Env.find?_cons,
    if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
    if_neg h10]

/-- The stored level parameters of a name other than the new one. -/
theorem levelParamsAt_cons_of_ne {env : Env} {c₀ : ConstantInfo} {n : Name}
    (h : c₀.name ≠ n) :
    levelParamsAt ⟨c₀ :: env.consts⟩ n = levelParamsAt env n := by
  unfold levelParamsAt
  rw [Env.find?_cons, if_neg h]

/-! ## Denotations run *backwards* across a fresh install

`denote_mono` moves a denotation from the smaller environment to the
larger one.  The environment invariant needs the other direction as
well, and it needs it for a reason that only shows up when a *field* is
transported rather than a term (`Setlec/TTVerify/DESIGN.md` §8.1): a
law that takes a denotation as a **hypothesis** is stated about the
larger environment after the install, so discharging it from the
smaller environment's law means running that hypothesis down, not up.

The converse is false in general — the larger environment denotes
strictly more — so it is guarded exactly as the set model guards
`interp_mono`: by `Expr.constsResolve`, which holds of every *stored*
expression by `EnvWF`.  This is the transpose of `interp_mono`
(`Setlec/Model/InterpLemmas.lean`), and it is consumed the way the
model consumes it, through a telescope-level shrink at the law's own
premise.

**It needs no guard or level-parameter hypotheses**, unlike
`denote_mono`: for a literal node `constsResolve` already asserts that
every slot the guard reads is stored in the *small* environment, and
freshness then says the new constant is none of them. -/

/-- A stored name is not the freshly installed one. -/
theorem ne_of_isSome_fresh {env : Env} {c₀ : ConstantInfo} {n : Name}
    (hfresh : env.find? c₀.name = none) (h : (env.find? n).isSome = true) :
    c₀.name ≠ n := by
  intro he
  rw [← he, hfresh] at h
  exact nomatch h

/-- Denotation is unchanged by a fresh install on expressions whose
constants already resolve.  Transpose of `interp_mono`. -/
theorem denote_env_shrink {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none) :
    ∀ (d : Nat) (e : Expr), e.constsResolve env = true →
      denote cval ⟨c₀ :: env.consts⟩ φ d e = denote cval env φ d e := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env) (φ := φ) with
  | case1 d u => intro _; rw [denote_sort, denote_sort]
  | case2 d idx nm ty => intro _; rw [denote_fvar, denote_fvar]
  | case3 d n us ci h1 h2 =>
    intro _
    simp only [denote_const, h1, if_pos h2,
      Env.find?_cons_of_isSome hfresh (by rw [h1]; rfl)]
  | case4 d n us ci h1 h2 =>
    intro _
    simp only [denote_const, h1, if_neg h2,
      Env.find?_cons_of_isSome hfresh (by rw [h1]; rfl)]
  | case5 d n us h1 =>
    intro hres
    rw [Expr.constsResolve, h1] at hres
    exact nomatch hres
  | case6 d n ty body mb h1 ihty =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_forallE, denote_forallE, ihty hres.1, h1]
  | case7 d n ty body mb B h1 h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_forallE, denote_forallE, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case8 d n ty body mb B h1 B' h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_forallE, denote_forallE, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case9 d n ty body mb h1 ihty =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_lam, denote_lam, ihty hres.1, h1]
  | case10 d n ty body mb B h1 h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_lam, denote_lam, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case11 d n ty body mb B h1 B' h2 ihty ihbody =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_lam, denote_lam, ihty hres.1, h1,
      ihbody (Expr.constsResolve_instantiate1 hres.1 0 hres.2), h2]
  | case12 d f a vf va h1 h2 ihf iha =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_app, denote_app, ihf hres.1, iha hres.2]
  | case13 d f a hbad ihf iha =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_app, denote_app, ihf hres.1, iha hres.2]
  | case14 d n ty val body vf va h1 h2 h3 ihty ihval ihbody =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_letE, denote_letE, ihty hres.1.1, ihval hres.1.2,
      ihbody (Expr.constsResolve_instantiate1 hres.1.1 0 hres.2)]
  | case15 d n ty val body vf va h1 h2 B h3 ihty ihval ihbody =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_letE, denote_letE, ihty hres.1.1, ihval hres.1.2,
      ihbody (Expr.constsResolve_instantiate1 hres.1.1 0 hres.2)]
  | case16 d n ty val body hbad ihty ihval =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_letE, denote_letE, ihty hres.1.1, ihval hres.1.2]
    split
    · next vf va k1 k2 => exact (hbad vf va k1 k2).elim
    · rfl
  | case17 d sn i e h1 ihe =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_proj, denote_proj, ihe hres.2]
  | case18 d sn i e B h1 h2 ihe =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_proj, denote_proj, ihe hres.2]
  | case19 d sn i e B h1 h2 ihe =>
    intro hres
    rw [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_proj, denote_proj, ihe hres.2]
  | case20 d n hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_natLit, denote_natLit,
      natLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh hres.1.1)
        (ne_of_isSome_fresh hfresh hres.1.2)
        (ne_of_isSome_fresh hfresh hres.2)]
  | case21 d n hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    rw [denote_natLit, denote_natLit,
      natLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh hres.1.1)
        (ne_of_isSome_fresh hfresh hres.1.2)
        (ne_of_isSome_fresh hfresh hres.2)]
  | case22 d s hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hres
    rw [denote_strLit, denote_strLit,
      strLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh k1)
        (ne_of_isSome_fresh hfresh k2) (ne_of_isSome_fresh hfresh k3)
        (ne_of_isSome_fresh hfresh k4) (ne_of_isSome_fresh hfresh k5)
        (ne_of_isSome_fresh hfresh k6) (ne_of_isSome_fresh hfresh k7)
        (ne_of_isSome_fresh hfresh k8) (ne_of_isSome_fresh hfresh k9)
        (ne_of_isSome_fresh hfresh k10),
      strLitT, strLitT,
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k7),
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k8)]
  | case23 d s hg =>
    intro hres
    simp only [Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hres
    rw [denote_strLit, denote_strLit,
      strLitSupported_cons_of_ne (ne_of_isSome_fresh hfresh k1)
        (ne_of_isSome_fresh hfresh k2) (ne_of_isSome_fresh hfresh k3)
        (ne_of_isSome_fresh hfresh k4) (ne_of_isSome_fresh hfresh k5)
        (ne_of_isSome_fresh hfresh k6) (ne_of_isSome_fresh hfresh k7)
        (ne_of_isSome_fresh hfresh k8) (ne_of_isSome_fresh hfresh k9)
        (ne_of_isSome_fresh hfresh k10),
      strLitT, strLitT,
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k7),
      levelParamsAt_cons_of_ne (ne_of_isSome_fresh hfresh k8)]
  | case24 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro _
    match x with
    | .bvar i => rw [denote_bvar, denote_bvar]
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

/-- The literal-support agreements, bundled.  Every install transport
needs the same seven, so they travel together rather than as seven
arguments each time.

Kept as a *structure of equations* rather than folded into the
"agrees away from the new name" hypothesis, because a basis install
changes exactly these valuations — see `has_type_cons`. -/
structure LitAgree (cval cval' : TConstVal) : Prop where
  nat : cval natZeroName = cval' natZeroName
  succ : cval natSuccName = cval' natSuccName
  sol : cval stringOfListName = cval' stringOfListName
  nil : cval listNilName = cval' listNilName
  cons : cval listConsName = cval' listConsName
  char : cval charName = cval' charName
  ofn : cval charOfNatName = cval' charOfNatName

/-- An ordinary (non-basis) install gets all seven from freshness: the
new name is none of them. -/
theorem LitAgree.of_fresh {cval cval' : TConstVal} {c₀ : Name}
    (hag : ∀ n, n ≠ c₀ → cval n = cval' n)
    (h1 : c₀ ≠ natZeroName) (h2 : c₀ ≠ natSuccName)
    (h3 : c₀ ≠ stringOfListName) (h4 : c₀ ≠ listNilName)
    (h5 : c₀ ≠ listConsName) (h6 : c₀ ≠ charName)
    (h7 : c₀ ≠ charOfNatName) : LitAgree cval cval' :=
  ⟨hag _ (Ne.symm h1), hag _ (Ne.symm h2), hag _ (Ne.symm h3),
   hag _ (Ne.symm h4), hag _ (Ne.symm h5), hag _ (Ne.symm h6),
   hag _ (Ne.symm h7)⟩

/-- Denotations of *old* terms survive an install: same value, larger
environment, changed valuation.  The shared core of every field's
transport — `has_type_cons` above is this plus a valuation rewrite, and
`defn_eq_cons` / `thm_ok_cons` below are the same again. -/
theorem denote_install {cval cval' : TConstVal} {env : Env} {φ : Name → Nat}
    {c₀ : ConstantInfo} {d : Nat} {e : Expr} {v : VExpr}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hlit : LitAgree cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
      = levelParamsAt env listNilName)
    (hlpCons : levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
      = levelParamsAt env listConsName)
    (h : denote cval env φ d e = some v) :
    denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v := by
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hfind
    refine hag n ?_
    intro hh
    rw [hh, hfresh] at hfind
    exact nomatch hfind
  rw [denote_cval_congr hagE hlit.nat hlit.succ hlit.sol hlit.nil
    hlit.cons hlit.char hlit.ofn d _] at h
  exact denote_mono (EnvExtends.cons hfresh) hguardN hguardS hlpNil hlpCons d _ h

theorem defn_eq_cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → m.cval n = cval' n)
    (hlit : LitAgree m.cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
      = levelParamsAt env listNilName)
    (hlpCons : levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
      = levelParamsAt env listConsName) :
    ∀ cv value hint, ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ) := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro cv value hint hmem φ
  have := denote_install hfresh hag hlit hguardN hguardS hlpNil hlpCons
    (m.defn_eq cv value hint hmem φ)
  rwa [hag cv.name (hne _ hmem)] at this

/-- Theorems likewise. -/
theorem thm_ok_cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal}
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → m.cval n = cval' n)
    (hlit : LitAgree m.cval cval')
    (hguardN : natLitSupported env = true →
      natLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hguardS : strLitSupported env = true →
      strLitSupported ⟨c₀ :: env.consts⟩ = true)
    (hlpNil : levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
      = levelParamsAt env listNilName)
    (hlpCons : levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
      = levelParamsAt env listConsName) :
    ∀ cv value, ConstantInfo.thmInfo cv value ∈ env.consts →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value
          = some (cval' cv.name φ) := by
  have hne : ∀ c ∈ env.consts, c.name ≠ c₀.name := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  intro cv value hmem φ
  have := denote_install hfresh hag hlit hguardN hguardS hlpNil hlpCons
    (m.thm_ok cv value hmem φ)
  rwa [hag cv.name (hne _ hmem)] at this

/-! ## The capability laws across an install

The transport that the §8.1 correction exists for, and the direct test
that it worked: `CapsOkTT` is the field whose laws quantify over
spines, so if the restatement had not fixed the shape, this is where it
would fail.  It is the transpose of `CapsOk.cons`
(`Setlec/Model/Extend/Sibs.lean`) step for step — the head cases are
handed over, and the non-head case runs the stored type's denotation
*down* to the smaller environment before applying the old law.

The two `denote` moves compose in one order only: `denote_env_shrink`
first (the expression resolves in the small environment, so it may
descend), then `denote_cval_congr` (the valuations agree on everything
stored *there*, but not on the new constant).  Doing it the other way
would need agreement at `c₀.name`, which is exactly what an install
does not have. -/

/-- The capability laws survive a fresh install, given the head
obligations.  Transpose of `CapsOk.cons`. -/
theorem CapsOkTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo}
    (h : CapsOkTT env cval) (hwfe : EnvWF env)
    (hfresh : env.find? c₀.name = none)
    (hag : ∀ n, n ≠ c₀.name → cval n = cval' n)
    (hlit : LitAgree cval cval')
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStoredT ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawTT ⟨c₀ :: env.consts⟩ cval' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawTT ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps) :
    CapsOkTT ⟨c₀ :: env.consts⟩ cval' := by
  have hfind : ∀ n, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hf
    refine hag n ?_
    intro hh
    rw [hh, hfresh] at hf
    exact nomatch hf
  -- the stored type descends, then the valuation changes
  have hdown : ∀ (φ : Name → Nat) (d : Nat) (e : Expr) (v : VExpr),
      e.constsResolve env = true →
      denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v →
      denote cval env φ d e = some v := by
    intro φ d e v hres hv
    rw [denote_env_shrink hfresh d e hres] at hv
    rwa [denote_cval_congr hagE hlit.nat hlit.succ hlit.sol hlit.nil
      hlit.cons hlit.char hlit.ofn d e]
  refine ⟨?_, ?_⟩
  · intro T cvT caps hf hcape hres hfam
    by_cases hpart : T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name
    · exact hheadEta T cvT caps hf hcape hres hfam hpart
    · have hnT : T ≠ c₀.name := fun hh => hpart (Or.inl hh)
      have hnC : caps.etaCtor ≠ c₀.name := fun hh => hpart (Or.inr (Or.inl hh))
      have hnP : ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name :=
        fun j hj hh => hpart (Or.inr (Or.inr ⟨j, hj, hh⟩))
      rw [hfind _ hnT] at hf
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      rw [hfind _ hnC] at hfC
      have hfam₀ : EtaFamilyStoredT env T caps := by
        refine ⟨hCres, ⟨cvC, hfC⟩, ?_⟩
        intro j hj
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
        rw [hfind _ (hnP j hj)] at hf2
        exact ⟨cv2, mI2, rP2, rules2, hf2⟩
      have hlaw := h.1 T cvT caps hf hcape hres hfam₀
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        simpa [ConstantInfo.toConstantVal] using h3
      intro φ d Δ us xs TV rest B hlen hTV hfit hBt
      have hTV' := hdown φ d _ TV
        (by rw [Expr.constsResolve_instantiateLevelParams cvT.levelParams us]
            exact hTres) hTV
      rw [← hag T hnT] at hBt
      have hproj : ∀ j ∈ List.range caps.etaFields,
          VExpr.mkAppN (cval' (projFnName T j)
            (Level.substFn φ
              (levelParamsAt ⟨c₀ :: env.consts⟩ (projFnName T j)) us))
            (xs ++ [B])
          = VExpr.mkAppN (cval (projFnName T j)
            (Level.substFn φ (levelParamsAt env (projFnName T j)) us))
            (xs ++ [B]) := by
        intro j hj
        rw [← hag _ (hnP j (List.mem_range.mp hj)),
          levelParamsAt_cons_of_ne
            (fun hh => (hnP j (List.mem_range.mp hj)) hh.symm)]
      rw [List.map_congr_left hproj, ← hag _ hnC,
        levelParamsAt_cons_of_ne (fun hh => hnC hh.symm)]
      exact hlaw φ d Δ us xs TV rest B hlen hTV' hfit hBt
  · intro T cvT caps hf hcapu hres
    by_cases hn : T = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadUnit cvT caps (Option.some.inj hf) hcapu hres
    · rw [hfind _ hn] at hf
      have hlaw := h.2 T cvT caps hf hcapu hres
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        simpa [ConstantInfo.toConstantVal] using h3
      intro φ d Δ us xs TV rest B B' hlen hTV hfit hBt hBt'
      have hTV' := hdown φ d _ TV
        (by rw [Expr.constsResolve_instantiateLevelParams cvT.levelParams us]
            exact hTres) hTV
      rw [← hag T hn] at hBt hBt'
      exact hlaw φ d Δ us xs TV rest B B' hlen hTV' hfit hBt hBt'

/-! ## The guards are monotone, not merely congruent

`natLitSupported_cons_of_ne` and its siblings above need the new
constant's name to differ from each slot's.  At an install those
distinctness facts have to come from somewhere, and there is a cheaper
source than freshness plus a case analysis: **the guard itself**.  A
guard that holds has already found every slot it reads, so each slot is
`isSome` in the *small* environment, and freshness then supplies the
distinctness for free.

The resulting monotonicity lemmas take a single hypothesis and
discharge the `hguardN`/`hguardS` obligations of `denote_mono`,
`denote_install` and `has_type_cons` at every ordinary install. -/

/-- The `Nat`-literal guard is monotone under a fresh install. -/
theorem natLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : natLitSupported env = true) :
    natLitSupported ⟨c₀ :: env.consts⟩ = true := by
  simp only [natLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have i1 : (env.find? natName).isSome = true := by
    revert h1; cases env.find? natName <;> simp [natIndOk]
  have i2 : (env.find? natZeroName).isSome = true := by
    revert h2; cases env.find? natZeroName <;> simp [natZeroOk]
  have i3 : (env.find? natSuccName).isSome = true := by
    revert h3; cases env.find? natSuccName <;> simp [natSuccOk]
  rw [Env.find?_cons_of_isSome hfresh i1, Env.find?_cons_of_isSome hfresh i2,
    Env.find?_cons_of_isSome hfresh i3]
  exact ⟨⟨h1, h2⟩, h3⟩

/-- The `String`-literal guard is monotone under a fresh install. -/
theorem strLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : strLitSupported env = true) :
    strLitSupported ⟨c₀ :: env.consts⟩ = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have i1 : (env.find? stringName).isSome = true := by
    revert h1; cases env.find? stringName <;> simp [stringTyOk]
  have i2 : (env.find? stringOfListName).isSome = true := by
    revert h2; cases env.find? stringOfListName <;> simp [stringOfListTyOk]
  have i3 : (env.find? listName).isSome = true := by
    revert h3; cases env.find? listName <;> simp [listTyOk]
  have i4 : (env.find? listNilName).isSome = true := by
    revert h4; cases env.find? listNilName <;> simp [listNilTyOk]
  have i5 : (env.find? listConsName).isSome = true := by
    revert h5; cases env.find? listConsName <;> simp [listConsTyOk]
  have i6 : (env.find? charName).isSome = true := by
    revert h6; cases env.find? charName <;> simp [charTyOk]
  have i7 : (env.find? charOfNatName).isSome = true := by
    revert h7; cases env.find? charOfNatName <;> simp [charOfNatTyOk]
  rw [Env.find?_cons_of_isSome hfresh i1, Env.find?_cons_of_isSome hfresh i2,
    Env.find?_cons_of_isSome hfresh i3, Env.find?_cons_of_isSome hfresh i4,
    Env.find?_cons_of_isSome hfresh i5, Env.find?_cons_of_isSome hfresh i6,
    Env.find?_cons_of_isSome hfresh i7]
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupported_cons hfresh h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- The `Nat`-operation guard is monotone under a fresh install. -/
theorem natOpGuard_cons {env : Env} {c₀ : ConstantInfo} {c : Name}
    (hfresh : env.find? c₀.name = none) (h : natOpGuard env c = true) :
    natOpGuard ⟨c₀ :: env.consts⟩ c = true := by
  simp only [natOpGuard, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h0, hdeps⟩, hbool⟩ := h
  refine ⟨⟨natLitSupported_cons hfresh h0, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at hdeps ⊢
    intro n hn
    have hn' := hdeps n hn
    have i : (env.find? n).isSome = true := by
      revert hn'; cases env.find? n <;> simp
    rw [Env.find?_cons_of_isSome hfresh i]
    exact hn'
  · split at hbool
    · next hc =>
      rw [if_pos hc]
      simp only [Bool.and_eq_true] at hbool ⊢
      obtain ⟨hT, hF⟩ := hbool
      have iT : (env.find? boolTrueName).isSome = true := by
        revert hT; cases env.find? boolTrueName <;> simp
      have iF : (env.find? boolFalseName).isSome = true := by
        revert hF; cases env.find? boolFalseName <;> simp
      rw [Env.find?_cons_of_isSome hfresh iT,
        Env.find?_cons_of_isSome hfresh iF]
      exact ⟨hT, hF⟩
    · next hc => rw [if_neg hc]

/-! ## The install context

Every field transport wants the same five facts, and passing them one
at a time was becoming the bulk of each statement.  `Installs` bundles
them.  It describes an **ordinary** install: the new constant is fresh,
the valuation changes only at it, and the literal-support constants and
their level parameters are untouched.  A *basis* install is precisely
the case that violates the last three, and is handled separately —
which is the honest division, because a basis install is the one thing
that can change what a literal denotes. -/

/-- The context of an ordinary install: `c₀` is fresh, the valuation
moves only at `c₀.name`, and nothing a literal reads changes. -/
structure Installs (env : Env) (cval cval' : TConstVal)
    (c₀ : ConstantInfo) : Prop where
  /-- The installed name is not already stored. -/
  fresh : env.find? c₀.name = none
  /-- The valuation changes only at the installed name. -/
  ag : ∀ n, n ≠ c₀.name → cval n = cval' n
  /-- Literal support is valued the same on both sides. -/
  lit : LitAgree cval cval'
  /-- `List.nil`'s stored level parameters do not move. -/
  lpNil : levelParamsAt ⟨c₀ :: env.consts⟩ listNilName
    = levelParamsAt env listNilName
  /-- `List.cons`'s stored level parameters do not move. -/
  lpCons : levelParamsAt ⟨c₀ :: env.consts⟩ listConsName
    = levelParamsAt env listConsName

/-- A denotation survives an ordinary install.  The guard hypotheses of
`denote_install` are discharged by monotonicity, so this form takes
none. -/
theorem Installs.denoteUp {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    {φ : Name → Nat} {d : Nat} {e : Expr} {v : VExpr}
    (h : denote cval env φ d e = some v) :
    denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v :=
  denote_install hi.fresh hi.ag hi.lit (natLitSupported_cons hi.fresh)
    (strLitSupported_cons hi.fresh) hi.lpNil hi.lpCons h

/-- A stored name is valued the same after an ordinary install. -/
theorem Installs.agree {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀) {n : Name}
    (h : (env.find? n).isSome = true) : cval n = cval' n :=
  hi.ag n (Ne.symm (ne_of_isSome_fresh hi.fresh h))

/-- A denotation of a *stored* expression runs back down to the smaller
environment.  The two moves compose in one order only: shrink first
(the expression resolves there), then change the valuation (the two
agree on everything stored there, but not at the new constant). -/
theorem Installs.denoteDown {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀)
    {φ : Name → Nat} {d : Nat} {e : Expr} {v : VExpr}
    (hres : e.constsResolve env = true)
    (h : denote cval' ⟨c₀ :: env.consts⟩ φ d e = some v) :
    denote cval env φ d e = some v := by
  have hagE : ∀ n ci, env.find? n = some ci → cval n = cval' n := by
    intro n ci hf
    refine hi.ag n ?_
    intro hh
    rw [hh, hi.fresh] at hf
    exact nomatch hf
  rw [denote_env_shrink hi.fresh d e hres] at h
  rwa [denote_cval_congr hagE hi.lit.nat hi.lit.succ hi.lit.sol hi.lit.nil
    hi.lit.cons hi.lit.char hi.lit.ofn d e]

/-- Lookups of stored names are unchanged by an ordinary install. -/
theorem Installs.find {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (hi : Installs env cval cval' c₀) {n : Name}
    (h : (env.find? n).isSome = true) :
    Env.find? ⟨c₀ :: env.consts⟩ n = env.find? n :=
  Env.find?_cons_of_isSome hi.fresh h

/-! ## The remaining field transports

One `.cons` per `EnvTT` field, each in the same shape: the head case is
a hypothesis (the install must establish its own constant's law), and
everything else transports.  The `Installs` context supplies the three
moves they share — a denotation goes up, a stored name's valuation is
unchanged, a stored name's lookup is unchanged. -/

/-- The pinned basis valuations survive an install at another name. -/
theorem BasisPinnedTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : BasisPinnedTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : reservedBasisNames.contains c₀.name = true →
      ∀ (ψ : Name → Nat) (t : VExpr),
        pinnedDirectT c₀.name ψ = some t → cval' c₀.name ψ = t) :
    BasisPinnedTT ⟨c₀ :: env.consts⟩ cval' := by
  intro n ci t hf hres ψ hp
  by_cases hn : c₀.name = n
  · subst hn
    exact hhead hres ψ t hp
  · rw [Env.find?_cons, if_neg hn] at hf
    rw [← hi.ag n (fun hh => hn hh.symm)]
    exact h n ci t hf hres ψ hp

/-- The native projection table survives an install. -/
theorem ProjOkT.cons {env : Env} {c₀ : ConstantInfo} (h : ProjOkT env)
    (hfresh : env.find? c₀.name = none)
    (hhead : ∀ entry, c₀ = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA) :
    ProjOkT ⟨c₀ :: env.consts⟩ := by
  have step : ∀ entry,
      ((entry = pairFstEntry ∨ entry = pairSndEntry) ∧
        env.find? psigmaName = some psigmaA ∧
        env.find? psigmaMkName = some psigmaMkA) →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
        (⟨c₀ :: env.consts⟩ : Env).find? psigmaName = some psigmaA ∧
        (⟨c₀ :: env.consts⟩ : Env).find? psigmaMkName = some psigmaMkA := by
    intro entry ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [Env.find?_cons_of_isSome hfresh (by rw [h2]; rfl)]; exact h2
    · rw [Env.find?_cons_of_isSome hfresh (by rw [h3]; rfl)]; exact h3
  intro n entry hf hnat
  by_cases hn : c₀.name = n
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact step entry (hhead entry (Option.some.inj hf) hnat)
  · rw [Env.find?_cons, if_neg hn] at hf
    exact step entry (h n entry hf hnat)

/-- The compiler-trust identities survive an install. -/
theorem ReduceOpsTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : ReduceOpsTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
          HasType Δ X (cval' (reduceElemName c₀.name) φ) →
          Deq Δ (.app (cval' c₀.name φ) X) X) :
    ReduceOpsTT ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv hf hpin
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv (Option.some.inj hf) hc hpin
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hs, hlaw⟩ := h c hc cv hf hpin
    refine ⟨by rw [hi.find hs]; exact hs, ?_⟩
    intro φ Δ X hX
    rw [← hi.agree hs] at hX
    rw [← hi.ag c (fun hh => hn hh.symm)]
    exact hlaw φ Δ X hX

/-- The structural `Nat` recurrences survive an install. -/
theorem NatOpsTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : NatOpsTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv v hint, c₀ = .defnInfo cv v hint → c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ φ : Name → Nat, ∃ L R,
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
        Deq [cval' natName φ, cval' natName φ] L R) :
    NatOpsTT ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv v hint hf
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv v hint (Option.some.inj hf) hc
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hg, hlaw⟩ := h c hc cv v hint hf
    -- the guard pins `Nat`, so the valuation there is unchanged
    have hnat : cval natName = cval' natName := by
      refine hi.agree ?_
      have h0 : natLitSupported env = true := by
        simp only [natOpGuard, Bool.and_eq_true] at hg
        exact hg.1.1
      simp only [natLitSupported, Bool.and_eq_true] at h0
      revert h0
      cases env.find? natName <;> simp [natIndOk]
    refine ⟨natOpGuard_cons hi.fresh hg, ?_⟩
    intro eq heq φ
    obtain ⟨L, R, hL, hR, hD⟩ := hlaw eq heq φ
    exact ⟨L, R, hi.denoteUp hL, hi.denoteUp hR, by rw [← hnat]; exact hD⟩

/-- The recursor rules survive an install.  The "the rule's own
constructor is the constant being installed" case is *refuted*, not
handled: a stored recursor's rules name constructors that are already
stored, which is `hctors` — the same discharge the set model's
`RecRulesOk.cons` makes from `ind_ok`. -/
theorem RecRulesTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : RecRulesTT env cval) (hwfe : EnvWF env)
    (hi : Installs env cval cval' c₀)
    (hctors : ∀ n cv mI rP rules,
      env.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hhead : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        (⟨c₀ :: env.consts⟩ : Env).find? (RecRule.ctor rl)
          = some (.ctorInfo cvj cnP cnF) →
      ∀ (φ : Name → Nat) (d : Nat) (Δ : List VExpr)
        (us usj : List Level) (xs ys : List VExpr)
        (TV TVj restR restC R : VExpr),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        us.length = cv.levelParams.length →
        usj.length = cvj.levelParams.length →
        denote cval' ⟨c₀ :: env.consts⟩ φ d
          (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
        denote cval' ⟨c₀ :: env.consts⟩ φ d
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVj →
        denote cval' ⟨c₀ :: env.consts⟩ φ d
          ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R →
        VTeleTyped Δ TV
          (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
            (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        VTeleTyped Δ TVj ys restC →
        Deq Δ
          (VExpr.mkAppN (cval' c₀.name (Level.substFn φ cv.levelParams us))
            (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
              (Level.substFn φ cvj.levelParams usj)) ys]))
          (VExpr.mkAppN R
            (xs.take rP ++ ys.drop (RecRule.ctorParams rl)))) :
    RecRulesTT ⟨c₀ :: env.consts⟩ cval' := by
  intro n cv mI rP rules hf rl hrl hfire cvj cnP cnF hctor
  by_cases hn : c₀.name = n
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv mI rP rules (Option.some.inj hf) rl hrl hfire cvj cnP cnF
      hctor
  · rw [Env.find?_cons, if_neg hn] at hf
    -- the rule's constructor is stored already, so it is not `c₀`
    obtain ⟨cvj2, cnP2, cnF2, hfc2⟩ := hctors n cv mI rP rules hf rl hrl
    have hnc : c₀.name ≠ RecRule.ctor rl :=
      ne_of_isSome_fresh hi.fresh (by rw [hfc2]; rfl)
    rw [Env.find?_cons, if_neg hnc] at hctor
    have hlaw := h n cv mI rP rules hf rl hrl hfire cvj cnP cnF hctor
    -- the three stored expressions descend
    obtain ⟨-, -, hres1, -, -, hrules, -⟩ := hwfe _ (find?_mem hf)
    obtain ⟨-, -, hres3, -⟩ := hrules cv mI rP rules rfl rl hrl
    obtain ⟨-, -, hres2, -⟩ := hwfe _ (find?_mem hctor)
    intro φ d Δ us usj xs ys TV TVj restR restC R hlenX hlenY hlenU hlenJ
      hTV hTVj hR hfitR hfitC
    have hTV' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cv.levelParams us]
          simpa [ConstantInfo.toConstantVal] using hres1) hTV
    have hTVj' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cvj.levelParams usj]
          simpa [ConstantInfo.toConstantVal] using hres2) hTVj
    have hR' := hi.denoteDown
      (by rw [Expr.constsResolve_instantiateLevelParams cv.levelParams us]
          exact hres3) hR
    rw [← hi.ag _ (Ne.symm hnc)] at hfitR
    rw [← hi.ag n (fun hh => hn hh.symm), ← hi.ag _ (Ne.symm hnc)]
    exact hlaw φ d Δ us usj xs ys TV TVj restR restC R hlenX hlenY hlenU
      hlenJ hTV' hTVj' hR' hfitR hfitC

/-! ### The WF-recursive clauses

`DivModClausesTT` reads the valuation at a dozen names, and every one
of them is pinned by `natOpGuard` — that is what the dependency list is
*for*.  So the transport needs no new hypothesis, only the observation
that a pinned name is stored and therefore not the one being
installed. -/

/-- Every name a clause set reads is valued the same after an install
at a different name. -/
theorem divModNames_agree {env : Env} {cval cval' : TConstVal} {c : Name}
    (hag : ∀ n, (env.find? n).isSome = true → cval n = cval' n)
    (hg : natOpGuard env c = true) :
    (∀ n ∈ natOpDeps c, cval n = cval' n) ∧
      cval natZeroName = cval' natZeroName ∧
      cval natSuccName = cval' natSuccName ∧
      (natDivModNames.contains c = true →
        cval boolTrueName = cval' boolTrueName ∧
        cval boolFalseName = cval' boolFalseName) := by
  simp only [natOpGuard, Bool.and_eq_true] at hg
  obtain ⟨⟨h0, hdeps⟩, hbool⟩ := hg
  simp only [natLitSupported, Bool.and_eq_true] at h0
  obtain ⟨⟨-, h2⟩, h3⟩ := h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [List.all_eq_true] at hdeps
    have hn' := hdeps n (by simpa using hn)
    exact hag n (by revert hn'; cases env.find? n <;> simp)
  · exact hag _ (by revert h2; cases env.find? natZeroName <;> simp [natZeroOk])
  · exact hag _ (by revert h3; cases env.find? natSuccName <;> simp [natSuccOk])
  · intro hc
    rw [show (decide (c = natBeqName) || decide (c = natBleName) ||
        natDivModNames.contains c) = true from by
          simp only [hc, Bool.or_true]] at hbool
    simp only [if_true] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨hT, hF⟩ := hbool
    exact ⟨hag _ (by revert hT; cases env.find? boolTrueName <;> simp),
      hag _ (by revert hF; cases env.find? boolFalseName <;> simp)⟩

/-- The guarded recurrences survive an install. -/
theorem DivModTT.cons {env : Env} {cval cval' : TConstVal}
    {c₀ : ConstantInfo} (h : DivModTT env cval)
    (hi : Installs env cval cval' c₀)
    (hhead : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
        HasType Δ x (cval' natName φ) → HasType Δ y (cval' natName φ) →
        DivModClausesTT cval' c₀.name φ Δ x y) :
    DivModTT ⟨c₀ :: env.consts⟩ cval' := by
  intro c hc cv v hint hf
  by_cases hn : c₀.name = c
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hhead cv v hint (Option.some.inj hf) hc
  · rw [Env.find?_cons, if_neg hn] at hf
    obtain ⟨hg, hlaw⟩ := h c hc cv v hint hf
    have hagS : ∀ n, (env.find? n).isSome = true → cval n = cval' n :=
      fun n hn' => hi.agree hn'
    obtain ⟨hdep, hz, hs, hbool⟩ := divModNames_agree hagS hg
    obtain ⟨hT, hF⟩ := hbool (by simpa using hc)
    have hnat : cval natName = cval' natName := by
      simp only [natOpGuard, Bool.and_eq_true] at hg
      have h0 := hg.1.1
      simp only [natLitSupported, Bool.and_eq_true] at h0
      exact hagS _ (by revert h0; cases env.find? natName <;> simp [natIndOk])
    refine ⟨natOpGuard_cons hi.fresh hg, ?_⟩
    intro φ Δ x y hx hy
    rw [← hnat] at hx hy
    have := hlaw φ Δ x y hx hy
    have hc' : cval c = cval' c := hi.ag c (fun hh => hn hh.symm)
    clear hc'
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natBleName (by decide), hdep natModName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natBleName (by decide),
        hdep natModName (by decide), hdep natGcdName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natAddName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natModName (by decide),
        hdep natLandName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natAddName (by decide),
        hdep natSubName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natModName (by decide), hdep natLorName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natAddName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natModName (by decide),
        hdep natXorName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natShiftLeftName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natSubName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natShiftRightName (by decide)] at this ⊢
      exact this
    · simp only [DivModClausesTT, hz, hs, hT, hF, hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natLog2Name (by decide)] at this ⊢
      exact this

/-! ## Assembling an install

`EnvTT.cons` is the one theorem the six `checkDecl` cases share: it
takes the head obligations for the constant being installed and returns
the invariant for the extended environment.  Everything else is the
transports above.

The shape mirrors `Setlec/Model/Extend/Transport.lean`'s: obligations
are stated *only* for the new constant, and every clause about an
already-stored constant is discharged here once rather than nine times
in the case analysis. -/

/-- The environment invariant survives an ordinary install, given the
new constant's own obligations. -/
def EnvTT.cons {env : Env} (m : EnvTT env) {c₀ : ConstantInfo}
    {cval' : TConstVal} (hi : Installs env m.cval cval' c₀)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hclosed : ∀ ψ : Name → Nat, VExpr.Closed (cval' c₀.name ψ))
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval' c₀.name φ₁ = cval' c₀.name φ₂)
    (htype : ∀ φ : Name → Nat, ∃ t,
      denoteClosed cval' ⟨c₀ :: env.consts⟩ φ c₀.toConstantVal.type = some t ∧
        HasType [] (cval' c₀.name φ) t)
    (hdefn : ∀ cv value hint, c₀ = .defnInfo cv value hint →
      ∀ φ : Name → Nat,
        denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value = some (cval' cv.name φ))
    (hthm : ∀ cv value, c₀ = .thmInfo cv value → ∀ φ : Name → Nat,
      denoteClosed cval' ⟨c₀ :: env.consts⟩ φ value = some (cval' cv.name φ))
    (hempty : c₀.name = emptyName →
      ∀ ψ : Name → Nat, ∃ u, cval' emptyName ψ = emptyT u)
    (hctors : ∀ n cv mI rP rules,
      env.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hheadRec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        (⟨c₀ :: env.consts⟩ : Env).find? (RecRule.ctor rl)
          = some (.ctorInfo cvj cnP cnF) →
      ∀ (φ : Name → Nat) (d : Nat) (Δ : List VExpr)
        (us usj : List Level) (xs ys : List VExpr)
        (TV TVj restR restC R : VExpr),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        us.length = cv.levelParams.length →
        usj.length = cvj.levelParams.length →
        denote cval' ⟨c₀ :: env.consts⟩ φ d
          (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
        denote cval' ⟨c₀ :: env.consts⟩ φ d
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVj →
        denote cval' ⟨c₀ :: env.consts⟩ φ d
          ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
            = some R →
        VTeleTyped Δ TV
          (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
            (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        VTeleTyped Δ TVj ys restC →
        Deq Δ
          (VExpr.mkAppN (cval' c₀.name (Level.substFn φ cv.levelParams us))
            (xs ++ [VExpr.mkAppN (cval' (RecRule.ctor rl)
              (Level.substFn φ cvj.levelParams usj)) ys]))
          (VExpr.mkAppN R
            (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStoredT ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawTT ⟨c₀ :: env.consts⟩ cval' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawTT ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps)
    (hheadProj : ∀ entry, c₀ = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hheadBasis : reservedBasisNames.contains c₀.name = true →
      ∀ (ψ : Name → Nat) (t : VExpr),
        pinnedDirectT c₀.name ψ = some t → cval' c₀.name ψ = t)
    (hheadNat : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natOpNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ φ : Name → Nat, ∃ L R,
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.1 = some L ∧
        denote cval' ⟨c₀ :: env.consts⟩ φ 2 eq.2 = some R ∧
        Deq [cval' natName φ, cval' natName φ] L R)
    (hheadDivMod : ∀ cv v hint, c₀ = .defnInfo cv v hint →
      c₀.name ∈ natDivModNames →
      natOpGuard ⟨c₀ :: env.consts⟩ c₀.name = true ∧
      ∀ (φ : Name → Nat) (Δ : List VExpr) (x y : VExpr),
        HasType Δ x (cval' natName φ) → HasType Δ y (cval' natName φ) →
        DivModClausesTT cval' c₀.name φ Δ x y)
    (hheadReduce : ∀ cv, c₀ = .axiomInfo cv → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
          = true ∧
        ∀ (φ : Name → Nat) (Δ : List VExpr) (X : VExpr),
          HasType Δ X (cval' (reduceElemName c₀.name) φ) →
          Deq Δ (.app (cval' c₀.name φ) X) X) :
    EnvTT ⟨c₀ :: env.consts⟩ := by
  refine
    { cval := cval'
      cval_closed := ?_
      wf := hwf
      val_params := ?_
      has_type := ?_
      defn_eq := ?_
      thm_ok := ?_
      empty_pinned := ?_
      rec_rules := RecRulesTT.cons m.rec_rules m.wf hi hctors hheadRec
      caps_ok := CapsOkTT.cons m.caps_ok m.wf hi.fresh hi.ag hi.lit
        hheadEta hheadUnit
      proj_ok := ProjOkT.cons m.proj_ok hi.fresh hheadProj
      basis_pinned := BasisPinnedTT.cons m.basis_pinned hi hheadBasis
      nat_ops := NatOpsTT.cons m.nat_ops hi hheadNat
      div_mod := DivModTT.cons m.div_mod hi hheadDivMod
      reduce_ops := ReduceOpsTT.cons m.reduce_ops hi hheadReduce }
  · intro n ψ
    by_cases hn : n = c₀.name
    · subst hn; exact hclosed ψ
    · rw [← hi.ag n hn]; exact m.cval_closed n ψ
  · intro n ci hf φ₁ φ₂ hp
    by_cases hn : c₀.name = n
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      rw [← Option.some.inj hf] at hp
      exact hparams φ₁ φ₂ hp
    · rw [Env.find?_cons, if_neg hn] at hf
      rw [← hi.ag n (fun hh => hn hh.symm)]
      exact m.val_params n ci hf φ₁ φ₂ hp
  · intro c hc φ
    rcases hc with _ | ⟨_, hc⟩
    · exact htype φ
    · exact has_type_cons m hi.fresh hi.ag hi.lit.nat hi.lit.succ hi.lit.sol
        hi.lit.nil hi.lit.cons hi.lit.char hi.lit.ofn
        (natLitSupported_cons hi.fresh) (strLitSupported_cons hi.fresh)
        hi.lpNil hi.lpCons c hc φ
  · intro cv value hint hmem φ
    rcases hmem with _ | ⟨_, hmem⟩
    · exact hdefn cv value hint rfl φ
    · exact defn_eq_cons m hi.fresh hi.ag hi.lit
        (natLitSupported_cons hi.fresh) (strLitSupported_cons hi.fresh)
        hi.lpNil hi.lpCons cv value hint hmem φ
  · intro cv value hmem φ
    rcases hmem with _ | ⟨_, hmem⟩
    · exact hthm cv value rfl φ
    · exact thm_ok_cons m hi.fresh hi.ag hi.lit
        (natLitSupported_cons hi.fresh) (strLitSupported_cons hi.fresh)
        hi.lpNil hi.lpCons cv value hmem φ
  · intro ψ
    by_cases hn : c₀.name = emptyName
    · exact hempty hn ψ
    · rw [← hi.ag emptyName (fun hh => hn hh.symm)]
      exact m.empty_pinned ψ

end Setlec.TTVerify
