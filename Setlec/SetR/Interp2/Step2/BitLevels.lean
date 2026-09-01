import Setlec.SetR.Interp2.Step2.Levels
import Setlec.SetR.Annot.Bit

/-!
# The level crossing for `denoteP`: algebra, outright (task #161, P3)

`Step2/Levels.lean` factored the canonical reading's level crossing
(`Denote2InstLevels`) into algebra plus **two open checker
metatheorems** — `SortOfEInstLevels`/`LamSortEInstLevels`, "inference
and head normalisation commute with level instantiation" — refuted as
stated over a bare `Env` (`Step2/LevelsInst.lean`), repaired under
`EnvWF`, and still residues.

For the validated-annotation reading the crossing **is** the algebra:
`denoteP` runs no checker function, its binder numerals ride the metas
that `Expr.instantiateLevelParams` pushes `Level.substPW` through, and
`PropWhen.holds_substPW` says the pushed datum reads out the composed
valuation's bit.  So the theorem below is

* **unconditional** — no checker residue, no `EnvWF`, and
* an **equality** — not `Denote2InstLevels`' one-directional
  implication with `∃ F' ≥ F` fuel slack; there is no fuel, and no run
  that instantiation could make succeed or fail asymmetrically.

This is the P3 pivot's first full payoff, measured: what was two open
metatheorems plus a conditional induction is one proved walk.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The level crossing for `denoteP`, unconditional and exact**:
reading an instantiated term at `φ` is reading the term at the
composed valuation `Level.substFn φ ks us`.  The binder step is
`pwBit_substPW` (i.e. `PropWhen.holds_substPW`); the constant step is
`EnvS2.acval_params` + `Level.substFn_map_subst`, as in the canonical
walk. -/
theorem denotePInstLevels (m : EnvS2UM V μ env)
    (φ : Name → Nat) (ks : List Name) (us : List Level) :
    ∀ (d : Nat) (e : Expr),
      denoteP m.acval env φ d (e.instantiateLevelParams ks us)
        = denoteP m.acval env (Level.substFn φ ks us) d e := by
  intro d e
  induction d, e using denoteP.induct (env := env) with
  | case1 d u =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP, Level.eval_subst]
  | case2 d idx nm ty =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP]
  | case3 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP, hf]
    dsimp only
    rw [if_pos hlen, if_pos (by simpa using hlen)]
    exact congrArg some
      (m.acval_params n ci hf _ _ fun p hp =>
        Level.substFn_map_subst hlen hp)
  | case4 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP, hf]
    dsimp only
    rw [if_neg hlen, if_neg (by simpa using hlen)]
  | case5 d n vs hf =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP, hf]
  | case6 d n ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
    simp only [pwBit_substPW]
  | case7 d n ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
    simp only [pwBit_substPW]
  | case8 d fe a ihf iha =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP, ihf, iha]
  | case9 d n ty val body ihty ihval ihbody =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihval, ihbody]
  | case10 d sn i e ihe =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP, ihe]
  | case11 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      if_pos hsup, if_pos hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      if_pos hsup, if_pos hsup]
    have hg := hsup
    simp only [Setlec.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteP, denoteP,
      if_neg hsup, if_neg hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i =>
      rw [Expr.instantiateLevelParams, denoteP.eq_def, denoteP.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE n ty b mb => exact absurd rfl (hpi n ty b mb)
    | lam n ty b mb => exact absurd rfl (hlam n ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end Setlec.SetR.Interp2
