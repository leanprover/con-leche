module

public import ConLeche.Verify.Denote.Closed
public import ConLeche.Verify.Denote.Install
import ConLeche.Verify.EnvGuards

public section

/-!
# `denote` at an install (task #161, P3.2)

The install-tier surface: the leaf-valuation congruence and its fresh
corollary, and the spine head swap.  `denote` has no fuel and its
binder clauses read no valuation, so:

* `denote_acval_congr` walks the clauses, the binder cases by the
  induction hypotheses alone;
* `denote_mkAppN_swap` is stated at one reading and the argument
  rides along on `rfl`.
-/

namespace ConLeche.Verify

open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

variable {env : Env} {φ : Name → Nat}

/-! ## `denote` reads only what the environment stores -/

/-- **The congruence.**  `denote` consults its valuation only at
names the environment stores — every `.const` leaf behind its own
`find?`, the two literal spines behind their support guards.  So two
valuations agreeing on the stored names denote every term alike.

Stated as an equation rather than an implication: the two runs are
`none` together as well, which is what a *fresh* install needs. -/
theorem denote_acval_congr
    {acval₁ acval₂ : Name → (Name → Nat) → Term}
    (hag : ∀ n, (env.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr),
      denote acval₁ env φ d e = denote acval₂ env φ d e := by
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u => rw [denote, denote]
  | case2 d idx ty => rw [denote, denote]
  | case3 d n us ci hf hlen =>
    rw [denote, denote, hf]
    dsimp only
    rw [ite_eq_left hlen, ite_eq_left hlen, hag n (by rw [hf]; rfl)]
  | case4 d n us ci hf hlen =>
    rw [denote, denote, hf]
    dsimp only
    rw [ite_eq_right hlen, ite_eq_right hlen]
  | case5 d n us hf => rw [denote, denote, hf]
  | case6 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case7 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case8 d f a ihf iha => rw [denote, denote, ihf, iha]
  | case9 d ty val body ihty ihv ihbody =>
    rw [denote, denote, ihty, ihv, ihbody]
  | case10 d sn i e ihe => rw [denote, denote, ihe]
  | case11 d n hsup =>
    obtain ⟨cvN, caps, cv0, i0, j0, T0, cv1, i1, j1, T1, hN, hZ, hS, -⟩ :=
      natLitSupported_inv hsup
    rw [denote, denote, ite_eq_left hsup, ite_eq_left hsup,
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hS]; rfl)]
  | case12 d n hsup =>
    rw [denote, denote, ite_eq_right hsup, ite_eq_right hsup]
  | case13 d s hsup =>
    obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
      hfS, hfO, hfL, hfN, hfC, hfH, hfF, -⟩ :=
      strLitSupported_inv hsup
    obtain ⟨cvN, caps, cv0, i0, j0, T0, cv1, i1, j1, T1, hN, hZ, hSu, -⟩ :=
      natLitSupported_inv hnat
    rw [denote, denote, ite_eq_left hsup, ite_eq_left hsup,
      hag stringOfListName (by rw [hfO]; rfl),
      hag listNilName (by rw [hfN]; rfl),
      hag listConsName (by rw [hfC]; rfl),
      hag charName (by rw [hfH]; rfl),
      hag charOfNatName (by rw [hfF]; rfl),
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hSu]; rfl)]
  | case14 d s hsup =>
    rw [denote, denote, ite_eq_right hsup, ite_eq_right hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-- **The install corollary**: choosing the new declaration's
leaf moves no denotation in the environment it was checked
in. -/
theorem denote_acvalWith_fresh
    {acval : Name → (Name → Nat) → Term} {n : Name}
    {A : (Name → Nat) → Term} (hfresh : env.find? n = none)
    (d : Nat) (e : Expr) :
    denote (acvalWith acval n A) env φ d e
      = denote acval env φ d e := by
  refine denote_acval_congr (fun c hc => ?_) d e
  refine acvalWith_ne (fun h => ?_)
  rw [h, hfresh] at hc
  exact nomatch hc

/-! ## The spine -/

/-- **Head swap under a spine.**  If the head's reading survives a
move to another head — for whatever reason: the same term, an
unfolding, a different term with the same reading — then
so does the whole application's, unchanged. -/
theorem denote_mkAppN_swap {acval : Name → (Name → Nat) → Term}
    {d : Nat} :
    ∀ (as : List Expr) {f g : Expr} {ea : Term},
      (∀ fa : Term, denote acval env φ d f = some fa →
        denote acval env φ d g = some fa) →
      denote acval env φ d (Expr.mkAppN f as) = some ea →
      denote acval env φ d (Expr.mkAppN g as) = some ea := by
  intro as
  induction as with
  | nil => intro f g ea hswap h; exact hswap ea h
  | cons a as ih =>
    intro f g ea hswap h
    refine ih (f := .app f a) (g := .app g a) ?_ h
    intro fa hfa
    rw [denote] at hfa
    rcases hf : denote acval env φ d f with _ | fx
    · rw [hf] at hfa; exact nomatch hfa
    rw [hf] at hfa
    rcases ha : denote acval env φ d a with _ | ax
    · rw [ha] at hfa; exact nomatch hfa
    rw [ha] at hfa
    obtain rfl : fa = .app fx ax := (Option.some.inj hfa).symm
    rw [denote, hswap fx hf, ha]
    rfl

end ConLeche.Verify
