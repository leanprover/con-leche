module

public import ConLeche.Model.Annot.BitLevels

public section

/-!
# The level footprint the reading reads (`lpDefF`)

`denoteMeta_params_ext` asks `allLevelParamsDefined` of the read term,
and that predicate looks INSIDE an `fvar`'s type annotation — which
`denoteMeta` never reads (an opener reads as its de Bruijn slot).
`lpDefF` is the same footprint with the `fvar` types ignored: an
opening at fvars keeps it, and the reading is ψ-congruent under it
(`denoteMeta_params_extF`).  (Moved from `BlockRuleParams.lean`: the
uniform block's datum reads its fields with holes under it too.)
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V]

/-! ## 1. `lpDefF` — the level footprint `denoteMeta` reads -/

section LpDefF

/-- Are the level parameters `denoteMeta` can read among `ps`?
`Expr.allLevelParamsDefined` with the `fvar` type annotations
IGNORED (an `fvar` reads as its de Bruijn slot). -/
@[expose] def lpDefF (ps : List Name) : Expr → Bool
  | .bvar _ => true
  | .fvar _ _ => true
  | .sort u => u.allParamsDefined ps
  | .const _ us => us.all (Level.allParamsDefined ps)
  | .app f a => lpDefF ps f && lpDefF ps a
  | .lam t b m => lpDefF ps t && lpDefF ps b && m.pw.paramsDefined ps
  | .forallE t b m => lpDefF ps t && lpDefF ps b && m.pw.paramsDefined ps
  | .letE t v b => lpDefF ps t && lpDefF ps v && lpDefF ps b
  | .lit _ => true
  | .proj _ _ e => lpDefF ps e

variable {ps : List Name}

omit [SetTheory V] in
theorem lpDefF_of_allLevelParamsDefined :
    ∀ (e : Expr), e.allLevelParamsDefined ps = true → lpDefF ps e = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, ihf h.1, iha h.2, Bool.and_self]
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, iht h.1.1, ihb h.1.2, h.2, Bool.and_self]
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, iht h.1.1, ihb h.1.2, h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [lpDefF, iht h.1.1, ihv h.1.2, ihb h.2, Bool.and_self]
  | proj s i e ihe =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [lpDefF, ihe h]
  | bvar => intro _; rfl
  | fvar => intro _; rfl
  | lit => intro _; rfl
  | sort u => intro h; simpa [lpDefF, Expr.allLevelParamsDefined] using h
  | const n us => intro h; simpa [lpDefF, Expr.allLevelParamsDefined] using h

omit [SetTheory V] in
theorem lpDefF_instantiate1 {v : Expr} (hv : lpDefF ps v = true) :
    ∀ (e : Expr) (k : Nat), lpDefF ps e = true → lpDefF ps (e.instantiate1 v k) = true := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, lpDefF]
  case bvar i =>
    split
    · exact hv
    · split <;> rfl

omit [SetTheory V] in
theorem lpDefF_mkAppN :
    ∀ (as : List Expr) {f : Expr}, lpDefF ps f = true → (∀ a ∈ as, lpDefF ps a = true) →
      lpDefF ps (Expr.mkAppN f as) = true
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    show lpDefF ps (Expr.mkAppN (Expr.app f a) as) = true
    refine lpDefF_mkAppN as ?_ (fun x hx => has x (List.mem_cons_of_mem _ hx))
    simp only [lpDefF, hf, has a List.mem_cons_self, Bool.and_self]

omit [SetTheory V] in
theorem lpDefF_stripLams :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr},
      lpDefF ps e = true → e.stripLams n = some (bs, body) → lpDefF ps body = true
  | 0, e, bs, body, he, h => by
    simp only [ConLeche.Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | n + 1, e, bs, body, he, h => by
    match e with
    | .lam ty b mb =>
      simp only [lpDefF, Bool.and_eq_true] at he
      simp only [ConLeche.Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, body₀⟩, hst, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact lpDefF_stripLams n he.1.2 hst
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .forallE _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripLams])

omit [SetTheory V] in
/-- **An opening at fvars keeps the footprint** — whatever the openers'
type annotations. -/
theorem lpDefF_instantiateList {vs : List Expr}
    (hvs : ∀ v ∈ vs, ∃ (i : Nat) (t : Expr), v = .fvar i t) :
    ∀ (e : Expr) (d : Nat), lpDefF ps e = true → lpDefF ps (e.instantiateList vs d) = true := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [Expr.instantiateList]
    split
    · rfl
    · split
      · rename_i hj
        obtain ⟨i, t, ht⟩ := hvs _ (List.getElem_mem hj)
        rw [ht, Expr.instantiateList]; rfl
      · rfl
  | fvar => intro d _; rw [Expr.instantiateList]; rfl
  | sort u => intro d h; rw [Expr.instantiateList]; exact h
  | const n us => intro d h; rw [Expr.instantiateList]; exact h
  | lit => intro d _; rw [Expr.instantiateList]; rfl
  | app f a ihf iha =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, ihf d h.1, iha d h.2, Bool.and_self]
  | lam t b m iht ihb =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, iht d h.1.1, ihb (d + 1) h.1.2, h.2, Bool.and_self]
  | forallE t b m iht ihb =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, iht d h.1.1, ihb (d + 1) h.1.2, h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro d h
    simp only [lpDefF, Bool.and_eq_true] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, iht d h.1.1, ihv d h.1.2, ihb (d + 1) h.2, Bool.and_self]
  | proj s i e ihe =>
    intro d h
    simp only [lpDefF] at h
    rw [Expr.instantiateList]
    simp only [lpDefF, ihe d h]

omit [SetTheory V] in
/-- Replacing constants by footprint-free terms keeps the footprint. -/
theorem lpDefF_replaceConsts {f : Name → List Level → Option Expr}
    (hf : ∀ c us e, f c us = some e → lpDefF ps e = true) :
    ∀ (e : Expr), lpDefF ps e = true → lpDefF ps (e.replaceConsts f) = true := by
  intro e
  induction e with
  | const n us =>
    intro h
    simp only [Expr.replaceConsts]
    cases hfn : f n us with
    | none => exact h
    | some e => exact hf n us e hfn
  | app a b iha ihb =>
    intro h
    simp only [lpDefF, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, lpDefF, iha h.1, ihb h.2, Bool.and_self]
  | lam t b m iht ihb =>
    intro h
    simp only [lpDefF, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, lpDefF, iht h.1.1, ihb h.1.2, h.2, Bool.and_self]
  | forallE t b m iht ihb =>
    intro h
    simp only [lpDefF, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, lpDefF, iht h.1.1, ihb h.1.2, h.2, Bool.and_self]
  | letE t v b iht ihv ihb =>
    intro h
    simp only [lpDefF, Bool.and_eq_true] at h
    simp only [Expr.replaceConsts, lpDefF, iht h.1.1, ihv h.1.2, ihb h.2, Bool.and_self]
  | proj s i e ihe =>
    intro h
    simp only [Expr.replaceConsts, lpDefF] at h ⊢
    exact ihe h
  | bvar => intro _; rfl
  | fvar => intro _; rfl
  | lit => intro _; rfl
  | sort u => intro h; exact h

end LpDefF

/-! ## 2. The reading is ψ-congruent at the `lpDefF` footprint

`denoteMeta_params_ext` (`Model/Annot/BitLevels.lean`) with the one
difference in the binder cases: the body is opened at an `fvar`, and
`lpDefF` of an opened body needs nothing of the fvar's annotation. -/

section Ext

variable {env : Env}

theorem denoteMeta_params_extF (m : EnvModel V env)
    {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (d : Nat) (e : Expr), lpDefF ps e = true →
      denoteMeta m.acval env φ₁ d e = denoteMeta m.acval env φ₂ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro hd
    rw [denoteMeta, denoteMeta,
      Level.eval_ext (by simpa [lpDefF] using hd) hφ]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci h1 h2 =>
    intro hd
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [if_pos h2, if_pos h2]
    refine congrArg _ (m.acval_params n ci h1 _ _ fun p hpm => ?_)
    refine Level.substFn_ext hφ ?_ h2 p hpm
    intro u hu
    simp only [lpDefF, List.all_eq_true] at hd
    exact hd u hu
  | case4 d n us ci h1 h2 =>
    intro _
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [if_neg h2, if_neg h2]
  | case5 d n us h1 => intro _; rw [denoteMeta, denoteMeta, h1]
  | case6 d ty body mb ihty ihbody =>
    intro hd
    simp only [lpDefF, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [ConLeche.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (lpDefF_instantiate1 rfl _ 0 hd.1.2)]
    simp only [hpw]
  | case7 d ty body mb ihty ihbody =>
    intro hd
    simp only [lpDefF, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [ConLeche.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (lpDefF_instantiate1 rfl _ 0 hd.1.2)]
    simp only [hpw]
  | case8 d fe a ihf iha =>
    intro hd
    simp only [lpDefF, Bool.and_eq_true] at hd
    rw [denoteMeta, denoteMeta, ← ihf hd.1, ← iha hd.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hd
    rw [denoteMeta, denoteMeta, ← ihe (by simpa [lpDefF] using hd)]
  | case11 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end Ext

end ConLeche.Model
