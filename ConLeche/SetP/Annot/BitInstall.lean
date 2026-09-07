import Lech.SetP.Annot.BitClosed
import Lech.Semantics.Install2
import Lech.Verify.EnvGuards

/-!
# `denoteP` at an install (task #161, P3.2)

The install-tier surface: the leaf-valuation congruence and its fresh
corollary (`Interp2/Install2.lean`), the same-run agreement
(`Interp2/Step2Cons.lean`), and the spine head swap
(`Interp2/Step2/Levels.lean`).

All four are VERIFIED-grade mirrors — the sort steps in the originals
are valuation- and spine-independent and simply vanish:

* `denoteP_acval_congr` walks the same fifteen clauses; the binder
  cases were `rw [denote2, denote2, ihty, ihbody]` and stay exactly
  that, because `pwBit φ m.pw` mentions no valuation;
* `denoteP_mkAppN_swap` loses the fuel-move (`F ≤ F'` and its
  `denote2_fuelMono` step) — with no fuel there is nothing to move,
  so the swap is stated at one reading and the argument rides along
  on `rfl`;
* `denoteP_agree_same` loses its content with the fuel it quantified
  over.  `denote2_agree_same` says two successes *at different fuels*
  agree; `denoteP` has one reading per subject, so the mirror is
  `Option.some.inj`.  It is kept, at its mirror name, because the
  consumers of the original (`hback` in `declStep2_of_value`) call it
  by name at exactly this instance.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.Verify
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

variable {env : Env} {φ : Name → Nat}

/-! ## `denoteP` reads only what the environment stores -/

/-- **The congruence.**  `denoteP` consults its valuation only at
names the environment stores — every `.const` leaf behind its own
`find?`, the two literal spines behind their support guards.  So two
valuations agreeing on the stored names denote every term alike.

Stated as an equation rather than an implication: the two runs are
`none` together as well, which is what a *fresh* install needs. -/
theorem denoteP_acval_congr
    {acval₁ acval₂ : Name → (Name → Nat) → AVExpr}
    (hag : ∀ n, (env.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr),
      denoteP acval₁ env φ d e = denoteP acval₂ env φ d e := by
  intro d e
  induction d, e using denoteP.induct (env := env) with
  | case1 d u => rw [denoteP, denoteP]
  | case2 d idx ty => rw [denoteP, denoteP]
  | case3 d n us ci hf hlen =>
    rw [denoteP, denoteP, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen, hag n (by rw [hf]; rfl)]
  | case4 d n us ci hf hlen =>
    rw [denoteP, denoteP, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => rw [denoteP, denoteP, hf]
  | case6 d ty body m ihty ihbody =>
    rw [denoteP, denoteP, ihty, ihbody]
  | case7 d ty body m ihty ihbody =>
    rw [denoteP, denoteP, ihty, ihbody]
  | case8 d f a ihf iha => rw [denoteP, denoteP, ihf, iha]
  | case9 d ty val body ihty ihval ihbody =>
    rw [denoteP, denoteP, ihty, ihval, ihbody]
  | case10 d sn i e ihe => rw [denoteP, denoteP, ihe]
  | case11 d n hsup =>
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hS, -⟩ :=
      natLitSupported_inv hsup
    rw [denoteP, denoteP, if_pos hsup, if_pos hsup,
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hS]; rfl)]
  | case12 d n hsup =>
    rw [denoteP, denoteP, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
      hfS, hfO, hfL, hfN, hfC, hfH, hfF, -⟩ :=
      strLitSupported_inv hsup
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hSu, -⟩ :=
      natLitSupported_inv hnat
    rw [denoteP, denoteP, if_pos hsup, if_pos hsup,
      hag stringOfListName (by rw [hfO]; rfl),
      hag listNilName (by rw [hfN]; rfl),
      hag listConsName (by rw [hfC]; rfl),
      hag charName (by rw [hfH]; rfl),
      hag charOfNatName (by rw [hfF]; rfl),
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hSu]; rfl)]
  | case14 d s hsup =>
    rw [denoteP, denoteP, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i => rw [denoteP.eq_def, denoteP.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-- **The install corollary**: choosing the new declaration's
annotated leaf moves no denotation in the environment it was checked
in. -/
theorem denoteP_acvalWith_fresh
    {acval : Name → (Name → Nat) → AVExpr} {n : Name}
    {A : (Name → Nat) → AVExpr} (hfresh : env.find? n = none)
    (d : Nat) (e : Expr) :
    denoteP (acvalWith acval n A) env φ d e
      = denoteP acval env φ d e := by
  refine denoteP_acval_congr (fun c hc => ?_) d e
  refine acvalWith_ne (fun h => ?_)
  rw [h, hfresh] at hc
  exact nomatch hc

/-! ## One reading per subject -/

/-- **`denote2_agree_same`'s mirror.**  The original reconciles two
successes at *different fuels* through `denote2_fuelMono`; `denoteP`
takes no fuel, so the two runs are the same run and the reconciliation
is `Option.some.inj`.  Kept at the mirror name because the consumers
of the original invoke it at exactly this instance. -/
theorem denoteP_agree_same {acval : Name → (Name → Nat) → AVExpr}
    {ψ : Name → Nat} {value : Expr} {ra ra' : AVExpr}
    (h : denoteP acval env ψ 0 value = some ra)
    (h' : denoteP acval env ψ 0 value = some ra') : ra = ra' :=
  Option.some.inj (h.symm.trans h')

/-! ## The spine -/

/-- **Head swap under a spine.**  If the head's annotation survives a
move to another head — for whatever reason: the same term, an
unfolding, a different term with the same validated annotation — then
so does the whole application's, unchanged.  `denote2_mkAppN_swap`
without the fuel move. -/
theorem denoteP_mkAppN_swap {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} :
    ∀ (as : List Expr) {f g : Expr} {ea : AVExpr},
      (∀ fa : AVExpr, denoteP acval env φ d f = some fa →
        denoteP acval env φ d g = some fa) →
      denoteP acval env φ d (Expr.mkAppN f as) = some ea →
      denoteP acval env φ d (Expr.mkAppN g as) = some ea := by
  intro as
  induction as with
  | nil => intro f g ea hswap h; exact hswap ea h
  | cons a as ih =>
    intro f g ea hswap h
    refine ih (f := .app f a) (g := .app g a) ?_ h
    intro fa hfa
    rw [denoteP] at hfa
    rcases hf : denoteP acval env φ d f with _ | fx
    · rw [hf] at hfa; exact nomatch hfa
    rw [hf] at hfa
    rcases ha : denoteP acval env φ d a with _ | ax
    · rw [ha] at hfa; exact nomatch hfa
    rw [ha] at hfa
    obtain rfl : fa = .app fx ax := (Option.some.inj hfa).symm
    rw [denoteP, hswap fx hf, ha]
    rfl

end Lech.SetP
