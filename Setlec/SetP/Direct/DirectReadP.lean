import Setlec.SetP.Direct.DirectBitsP
import Setlec.SetP.Annot.BitInstall
import Setlec.Verify.EnvWF

/-!
# The direct structure's readings (task #175 W4c, P3 module 2)

The P install of a direct structure reads its four stored types (the
former's, the constructor's, the recursor's, each entry's) at the
stage environments, and peels the Π-prefixes into the binder data the
tower leaves are built over.  Two syntactic facts carry the module:

* **The unmentioned leaf** (`denoteP_acvalWith_unmentioned`): a term
  whose constants all resolve in the pre-block environment reads the
  same under any leaf at the block's name.  The type former's
  parameter domains and the constructor's field domains are such
  terms (`checkConstantVal` at `env₀`, resp. the constructor stage's
  `constsResolve env₀` re-check), so their readings — the leaves'
  ingredients — are fixed before the leaves are, which is what lets
  the former's leaf mention them without circularity.

* **The reading peel** (`denoteP_openPis`): `denoteP` opens a Π-prefix
  with the very `fvar`s `openPisAtFvars` does, so a type's reading
  strips (`stripPisAV`) to the per-binder readings of the opened
  variables' annotations, each at its own depth.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec Setlec.Semantics Setlec.TTVerify Setlec.SetModel

/-! ## The unmentioned leaf -/

/-- Reading a term that resolves in `env₀` never consults the leaf at
a name `env₀` lacks: every `.const` the reading looks up resolves in
`env₀`, and the literal spines' support constants are part of
`constsResolve`'s literal clauses.  Stated as an equation — the two
runs are `none` together. -/
theorem denoteP_acvalWith_unmentioned
    {acval : Name → (Name → Nat) → AVExpr} {T : Name}
    {A : (Name → Nat) → AVExpr} {env₀ env : Env} {φ : Name → Nat}
    (hfresh : env₀.find? T = none) :
    ∀ (d : Nat) (e : Expr), Expr.constsResolve env₀ e = true →
      denoteP (acvalWith acval T A) env φ d e
        = denoteP acval env φ d e := by
  have hne : ∀ n, (env₀.find? n).isSome = true → n ≠ T := by
    intro n hn h
    rw [h, hfresh] at hn
    exact nomatch hn
  intro d e
  induction d, e using denoteP.induct (env := env) with
  | case1 d u => intro _; rw [denoteP, denoteP]
  | case2 d idx nm ty => intro _; rw [denoteP, denoteP]
  | case3 d n us ci hf hlen =>
    intro hcr
    rw [denoteP, denoteP, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen,
      acvalWith_ne (hne n (by simpa [Expr.constsResolve] using hcr))]
  | case4 d n us ci hf hlen =>
    intro _
    rw [denoteP, denoteP, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => intro _; rw [denoteP, denoteP, hf]
  | case6 d n ty body m ihty ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteP, denoteP, ihty hcr.1,
      ihbody (Expr.constsResolve_instantiate1 hcr.1 0 hcr.2)]
  | case7 d n ty body m ihty ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteP, denoteP, ihty hcr.1,
      ihbody (Expr.constsResolve_instantiate1 hcr.1 0 hcr.2)]
  | case8 d f a ihf iha =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteP, denoteP, ihf hcr.1, iha hcr.2]
  | case9 d n ty val body ihty ihval ihbody =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteP, denoteP, ihty hcr.1.1, ihval hcr.1.2,
      ihbody (Expr.constsResolve_instantiate1 hcr.1.1 0 hcr.2)]
  | case10 d sn i e ihe =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteP, denoteP, ihe hcr.2]
  | case11 d n hsup =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    rw [denoteP, denoteP, if_pos hsup, if_pos hsup,
      acvalWith_ne (hne natZeroName hcr.1.2),
      acvalWith_ne (hne natSuccName hcr.2)]
  | case12 d n hsup =>
    intro _
    rw [denoteP, denoteP, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    intro hcr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hZ⟩, hS⟩, -⟩, hO⟩, -⟩, hN⟩, hC⟩, hH⟩, hF⟩ := hcr
    rw [denoteP, denoteP, if_pos hsup, if_pos hsup,
      acvalWith_ne (hne stringOfListName hO),
      acvalWith_ne (hne listNilName hN),
      acvalWith_ne (hne listConsName hC),
      acvalWith_ne (hne charName hH),
      acvalWith_ne (hne charOfNatName hF),
      acvalWith_ne (hne natZeroName hZ),
      acvalWith_ne (hne natSuccName hS)]
  | case14 d s hsup =>
    intro _
    rw [denoteP, denoteP, if_neg hsup, if_neg hsup]
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

/-- Two leaves at the block's name read a pre-block term alike. -/
theorem denoteP_acvalWith_unmentioned₂
    {acval : Name → (Name → Nat) → AVExpr} {T : Name}
    {A₁ A₂ : (Name → Nat) → AVExpr} {env₀ env : Env} {φ : Name → Nat}
    (hfresh : env₀.find? T = none)
    (d : Nat) (e : Expr) (hcr : Expr.constsResolve env₀ e = true) :
    denoteP (acvalWith acval T A₁) env φ d e
      = denoteP (acvalWith acval T A₂) env φ d e := by
  rw [denoteP_acvalWith_unmentioned hfresh d e hcr,
    denoteP_acvalWith_unmentioned hfresh d e hcr]

/-! ## The reading peel -/

/-- **The peel.**  A Π-prefix opened at `fvar`s reads to a
`stripPisAV`-strippable reading whose binder data are the opened
variables' annotation readings at their own depths (domain sort
numeral `0`, the codomain bit the binder's own), and whose residual is
the opened body's reading at the full depth. -/
theorem denoteP_openPis {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
      {ea : AVExpr},
      openPisAtFvars n e d = some (fvs, o) →
      denoteP acval env φ d e = some ea →
      ∃ (pps : List (Nat × Nat × AVExpr)) (b : AVExpr),
        stripPisAV n ea = some (pps, b) ∧
        denoteP acval env φ (d + n) o = some b ∧
        pps.length = n ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          ∃ p, pps[i]? = some p ∧ p.1 = 0 ∧
            denoteP acval env φ (d + i) x.fvarTypeD = some p.2.2
  | 0, d, e, fvs, o, ea, hop, hden => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨[], ea, rfl, by simpa using hden, rfl,
      fun i x hx => by simp at hx⟩
  | n + 1, d, e, fvs, o, ea, hop, hden => by
    match e, hop with
    | .forallE nm dom body mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteP_forallE_inv hden
        obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteP_openPis n hop' hba
        refine ⟨(0, pwBit φ mb.pw, ta) :: pps, b, ?_, ?_, ?_, ?_⟩
        · simp only [stripPisAV, hst, Option.map_some]
        · rw [show d + (n + 1) = d + 1 + n from by omega]; exact hb
        · simp [hlen]
        · intro i x hx
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            subst hx
            exact ⟨(0, pwBit φ mb.pw, ta), rfl, rfl,
              by rw [Nat.add_zero]; exact hta⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hx
            obtain ⟨p, hp, hp1, hpd⟩ := hbind i x hx
            exact ⟨p, by simpa using hp, hp1,
              by rw [show d + (i + 1) = d + 1 + i from by omega]; exact hpd⟩
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _ _, hop | .sort _, hop | .const _ _, hop
    | .app _ _, hop | .lam _ _ _ _, hop | .letE _ _ _ _, hop | .lit _, hop
    | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

end Setlec.SetP
