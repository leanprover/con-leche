import Setlec.SetR.Annot.BitInstall
import Setlec.SetR.Interp2.Denote2Extend

/-!
# `denoteP` across an environment extension (task #161, P3.2)

The mirror of `Denote2EnvExtend` (`Interp2/Keys2.lean`) and its
discharge `denote2_envExtend` (`Interp2/Denote2Extend.lean`) — and the
place where the P3 pivot pays out most visibly.

**`SortAgree` is deleted.**  `denote2_envExtend` takes three premises:
`FindPreserved` (the `.const` clause and the string spine's
`levelParamsAt`), `LitGuardsAgree` (the two literal guards), and
`SortAgree` — "`sortOfE` and `lamSortE` agree at `env₀` and `env`",
itself a composition of `EnvExtendStable`, `EnvExtendReflect` and
`InferOutputBound` (`sortAgree_of`), i.e. three *open* checker
metatheorems.  It is used at exactly three rewrites, all inside the
`∀` and `λ` clauses (`hS.1 hc.1`, `hS.1 hcb`, `hS.2 hcb`).

`denoteP`'s binder numeral is `pwBit φ mb.pw`: a function of the
term's own validated meta and the valuation `φ`, mentioning no
environment at all.  So those three rewrites have no mirror and no
residue — the binder clauses close on the two induction hypotheses
alone, exactly like `.app`.  The two kept premises are the ones the
*reading itself* needs: `denoteP` consults `env` only through
`find?` and the two support guards.

That is the whole Θ-residue for this key, gone by construction rather
than by discharge.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **`denoteP` is stable under environment extension**, stated.
`Denote2EnvExtend` with the fuel and mode indices deleted.

An **equation**, not an implication, for the reason the original is
one: an install must not be able to assume silently that an
annotation exists on one side and not the other. -/
def DenotePEnvExtend (env₀ env : Env)
    (acval : Name → (Name → Nat) → AVExpr) (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
    denoteP acval env₀ φ d e = denoteP acval env φ d e

/-- **`DenotePEnvExtend`, discharged** — from `FindPreserved` and
`LitGuardsAgree` alone.  See the module docstring for the dropped
`SortAgree`. -/
theorem denoteP_envExtend {env₀ env : Env}
    {acval : Name → (Name → Nat) → AVExpr} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsAgree env₀ env) :
    DenotePEnvExtend env₀ env acval φ := by
  intro d e
  induction d, e using denoteP.induct (env := env₀) with
  | case1 d u => intro _; rw [denoteP, denoteP]
  | case2 d idx nm ty => intro _; rw [denoteP, denoteP]
  | case3 d n us ci hf hlen =>
    intro _
    rw [denoteP, hf, denoteP, hF hf]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteP, hf, denoteP, hF hf]
  | case5 d n us hf =>
    intro hc
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d n ty body m ihty ihbody =>
    intro hc
    rw [constsBound_forallE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denoteP, denoteP, ihty hc.1, ihbody hcb]
  | case7 d n ty body m ihty ihbody =>
    intro hc
    rw [constsBound_lam] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    rw [denoteP, denoteP, ihty hc.1, ihbody hcb]
  | case8 d f a ihf iha =>
    intro hc
    rw [constsBound_app] at hc
    rw [denoteP, denoteP, ihf hc.1, iha hc.2]
  | case9 d n ty val body ihty ihval ihbody =>
    intro hc
    rw [constsBound_letE] at hc
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d n ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2.2
    rw [denoteP, denoteP, ihty hc.1, ihval hc.2.1, ihbody hcb]
  | case10 d sn i e ihe =>
    intro hc
    rw [constsBound_proj] at hc
    rw [denoteP, denoteP, ihe hc]
  | case11 d n hsup =>
    intro _
    rw [denoteP, if_pos hsup, denoteP, if_pos (hG.1 ▸ hsup)]
  | case12 d n hsup =>
    intro _
    rw [denoteP, if_neg hsup, denoteP,
      if_neg (fun h => hsup (hG.1.trans h))]
  | case13 d s hsup =>
    intro _
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    rw [denoteP, if_pos hsup, denoteP, if_pos (hG.2 ▸ hsup),
      levelParamsAt_congr hF hnil, levelParamsAt_congr hF hcons]
  | case14 d s hsup =>
    intro _
    rw [denoteP, if_neg hsup, denoteP,
      if_neg (fun h => hsup (hG.2.trans h))]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteP.eq_def, denoteP.eq_def]
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

end Setlec.SetR.Interp2
