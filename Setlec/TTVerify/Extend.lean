import Setlec.TTVerify.Denote

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

end Setlec.TTVerify
